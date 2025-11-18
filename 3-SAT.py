# ============================================================
# 0. 基础环境：安装 Kissat（现代 CDCL 求解器）
# ============================================================

!apt-get -y install git build-essential >/dev/null

# 获取 kissat 源码并编译（只做一次即可）
!git clone https://github.com/arminbiere/kissat.git >/dev/null
!cd kissat && ./configure >/dev/null && make -j4 >/dev/null

KISSAT_BIN = "/content/kissat/build/kissat"
print("Kissat binary at:", KISSAT_BIN)

# ============================================================
# 1. Python 侧：生成随机 3-SAT、调用 solver、计算 λ_B
# ============================================================

import os
import time
import random
import zlib
import math
import csv
import subprocess
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

BASE_DIR = Path("/content/scct_cdcl_experiment")
CNF_DIR = BASE_DIR / "cnf"
LOG_DIR = BASE_DIR / "logs"
RESULT_CSV = BASE_DIR / "scct_cdcl_results.csv"

CNF_DIR.mkdir(parents=True, exist_ok=True)
LOG_DIR.mkdir(parents=True, exist_ok=True)
BASE_DIR.mkdir(parents=True, exist_ok=True)

random.seed(42)

# ---------- 1.1 生成随机 3-SAT 实例 ----------

def gen_random_3sat_cnf(n_vars: int, ratio: float = 4.2):
    """
    生成一个随机 3-SAT 实例 (n_vars, m=round(ratio*n)).
    返回 (clauses, n_vars, n_clauses)，
    其中 clauses 是由 3 literal 组成的列表，例如 [(1,-3,4), ...]
    """
    n_clauses = int(round(ratio * n_vars))
    clauses = []
    seen = set()
    for _ in range(n_clauses):
        # 随机选 3 个不同变量
        vars_ = random.sample(range(1, n_vars + 1), 3)
        lits = []
        for v in vars_:
            sign = random.choice([1, -1])
            lits.append(sign * v)
        key = tuple(sorted(lits))
        if key in seen:
            # 确保不完全重复，简单处理即可
            continue
        seen.add(key)
        clauses.append(tuple(lits))
    # 若因去重导致数量略少，就不强行补齐了，影响不大
    return clauses, n_vars, len(clauses)

def write_dimacs_cnf(filepath: Path, clauses, n_vars: int):
    """
    将 3-SAT 子句列表写成 DIMACS CNF。
    """
    n_clauses = len(clauses)
    with open(filepath, "w") as f:
        f.write(f"p cnf {n_vars} {n_clauses}\n")
        for clause in clauses:
            line = " ".join(str(l) for l in clause) + " 0\n"
            f.write(line)

# ---------- 1.2 压缩模型：Ct, λ_B ----------

def Ct_bytes(data: bytes, level: int = 9) -> int:
    return len(zlib.compress(data, level))

SEP_BYTES = b"||"
C_SEP = Ct_bytes(SEP_BYTES)

def compute_lambda_B(problem_bytes: bytes, trace_bytes: bytes):
    """
    按照你新论文里的定义：
      Cp = Ct(problem)
      Cjoint = Ct(problem || sep || trace)
      Ccond = max{Cjoint - Cp - Csep, 1}
      lambda_B = Ccond / (Cp + Ccond)
    """
    Cp = Ct_bytes(problem_bytes)
    Cjoint = Ct_bytes(problem_bytes + SEP_BYTES + trace_bytes)
    Ccond = max(Cjoint - Cp - C_SEP, 1)
    lambda_B = Ccond / (Cp + Ccond)
    return Cp, Ccond, lambda_B

# ---------- 1.3 调用 Kissat，记录 T 和 trace ----------

def solve_with_kissat(cnf_path: Path, log_path: Path, timeout_sec: int = 300):
    """
    调用 kissat 求解。我们让它输出较详细的 log。
    - kissat 默认 verbose 比较有限，可以加一些选项，简单版先用默认。
    - 将 stdout 写入 log_path，用作 trace。
    """
    cmd = [KISSAT_BIN, str(cnf_path)]
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,  # 都合并到 stdout
            timeout=timeout_sec,
            check=False,
        )
        end = time.perf_counter()
        T = end - start
        out_bytes = proc.stdout
        with open(log_path, "wb") as f:
            f.write(out_bytes)

        # 简单判断 sat/unsat：kissat 的输出里会写 SATISFIABLE / UNSATISFIABLE
        out_str = out_bytes.decode("utf-8", errors="ignore")
        if "UNSATISFIABLE" in out_str:
            sat = False
            solved = True
        elif "SATISFIABLE" in out_str:
            sat = True
            solved = True
        else:
            sat = None
            solved = False

        # 用 log 行数当作粗略 trace_len
        trace_len = out_str.count("\n")

        return {
            "T": T,
            "sat": sat,
            "solved": solved,
            "trace_len": trace_len,
            "raw_log": out_bytes,
        }
    except subprocess.TimeoutExpired:
        end = time.perf_counter()
        T = end - start
        return {
            "T": T,
            "sat": None,
            "solved": False,
            "trace_len": 0,
            "raw_log": b"",
        }

# ============================================================
# 2. 主实验循环
# ============================================================

# 注意：真正跑 n=1e4~1e6 之前，先用小一点的 n 调试！
N_VARS_LIST = [500, 1000, 2000]  # 调好后，你可以改成 [10_000, 20_000, 50_000, ...]
INSTANCES_PER_N = 5               # 每个 n 做多少样本；真大规模时可以 3~10 不等
RATIO = 4.2

records = []

for n_vars in N_VARS_LIST:
    for idx in range(INSTANCES_PER_N):
        inst_id = f"n{n_vars}_i{idx}"
        cnf_path = CNF_DIR / f"{inst_id}.cnf"
        log_path = LOG_DIR / f"{inst_id}.log"

        print(f"[GEN+SOLVE] n={n_vars}, instance={idx} ...")

        # 2.1 生成 CNF
        clauses, nv, nc = gen_random_3sat_cnf(n_vars=n_vars, ratio=RATIO)
        write_dimacs_cnf(cnf_path, clauses, n_vars=nv)

        # 2.2 编码 problem(x) 为 bytes（就是 DIMACS 文件内容）
        problem_bytes = cnf_path.read_bytes()

        # 2.3 调用 Kissat
        res = solve_with_kissat(cnf_path, log_path, timeout_sec=300)

        T = res["T"]
        sat = res["sat"]
        solved = res["solved"]
        trace_len = res["trace_len"]
        trace_bytes = res["raw_log"]

        # 2.4 计算 λ_B
        Cp, Ccond, lambda_B = compute_lambda_B(problem_bytes, trace_bytes)

        records.append({
            "inst_id": inst_id,
            "n_vars": nv,
            "n_clauses": nc,
            "ratio": nc / nv if nv > 0 else None,
            "T": T,
            "log2_T": math.log2(T) if T > 0 else None,
            "sat": sat,
            "solved": solved,
            "trace_len": trace_len,
            "log2_trace": math.log2(trace_len) if trace_len > 0 else None,
            "C_p": Cp,
            "C_cond": Ccond,
            "lambda_B": lambda_B,
        })

# 存成 CSV，方便之后再分析
BASE_DIR.mkdir(exist_ok=True, parents=True)
with open(RESULT_CSV, "w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=list(records[0].keys()))
    writer.writeheader()
    writer.writerows(records)

print("Saved results to:", RESULT_CSV)

# ============================================================
# 3. 回归：Structure–Time Law & Structure–Work Law
# ============================================================

df = pd.DataFrame(records)
print("\n=== 数据预览 ===")
print(df.head())

print("\n=== 描述统计 ===")
print(df.describe(include="all"))

# 过滤掉 timeout 或 log2 为空的
df_valid_T = df[(df["solved"] == True) & df["log2_T"].notnull()]
df_valid_W = df[(df["solved"] == True) & df["log2_trace"].notnull()]

print("\n=== 有效样本数（时间） ===", df_valid_T.shape)
print("=== 有效样本数（工作量） ===", df_valid_W.shape)

# 准备特征：X = [lambda_B, log2_n]
df_valid_T = df_valid_T.copy()
df_valid_W = df_valid_W.copy()

df_valid_T["log2_n"] = np.log2(df_valid_T["n_vars"])
df_valid_W["log2_n"] = np.log2(df_valid_W["n_vars"])

X_T = df_valid_T[["lambda_B", "log2_n"]].values
y_T = df_valid_T["log2_T"].values

X_W = df_valid_W[["lambda_B", "log2_n"]].values
y_W = df_valid_W["log2_trace"].values

# 线性回归
reg_T = LinearRegression().fit(X_T, y_T)
reg_W = LinearRegression().fit(X_W, y_W)

alpha_T, beta_T = reg_T.coef_
gamma_T = reg_T.intercept_
R2_T = reg_T.score(X_T, y_T)

alpha_W, beta_W = reg_W.coef_
gamma_W = reg_W.intercept_
R2_W = reg_W.score(X_W, y_W)

print("\n=== 结构–时间定律（Structure–Time Law, CDCL 版） ===")
print("模型：log2 T(x) ≈ α λ_B + β log2 n + γ")
print(f"α ≈ {alpha_T:8.3f}, β ≈ {beta_T:8.3f}, γ ≈ {gamma_T:8.3f}, R^2 ≈ {R2_T:6.3f}")
print("等价于：T(x) ≈ const · n^β · 2^(α λ_B)")
const_T = 2**gamma_T
print(f"const ≈ {const_T:.3e}")

print("\n=== 结构–工作量定律（Structure–Work Law, CDCL 版） ===")
print("模型：log2 |trace(x)| ≈ α' λ_B + β' log2 n + γ'")
print(f"α' ≈ {alpha_W:8.3f}, β' ≈ {beta_W:8.3f}, γ' ≈ {gamma_W:8.3f}, R^2 ≈ {R2_W:6.3f}")
print("等价于：|trace(x)| ≈ const' · n^{β'} · 2^{α' λ_B}")
const_W = 2**gamma_W
print(f"const' ≈ {const_W:.3e}")

# 简单画两个散点图（optional）
import matplotlib.pyplot as plt

# 预测 vs 实际（时间）
y_T_pred = reg_T.predict(X_T)
plt.figure()
plt.scatter(y_T, y_T_pred, s=10)
plt.xlabel("实际 log2 T")
plt.ylabel("预测 log2 T")
plt.title("Structure–Time Law: predicted vs actual")
plt.grid(True)
plt.show()

# 预测 vs 实际（工作量）
y_W_pred = reg_W.predict(X_W)
plt.figure()
plt.scatter(y_W, y_W_pred, s=10)
plt.xlabel("实际 log2 |trace|")
plt.ylabel("预测 log2 |trace|")
plt.title("Structure–Work Law: predicted vs actual")
plt.grid(True)
plt.show()
