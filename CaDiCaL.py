# ============================================================
# 0. 环境准备：安装 CaDiCaL + 常用库
# ============================================================

!git clone https://github.com/arminbiere/cadical.git
%cd cadical
!./configure
!make -j4
%cd /content

!pip install pandas scikit-learn

# ============================================================
# 1. 导入依赖
# ============================================================
import os
import subprocess
import time
import random
import math
import zlib
import pandas as pd
import numpy as np
from sklearn.linear_model import LinearRegression

# ============================================================
# 2. 配置参数 —— 在这里调样本量 / 尺寸 / 超时
# ============================================================

CADICAL_BIN = "/content/cadical/build/cadical"

# 要测试的 n 取值
N_VALUES = [500, 1000, 2000]

# 每个 n 生成多少个实例（100*3=300；改成 300 就是 900）
INSTANCES_PER_N = 100

# 子句密度
RATIO = 4.2

# 单实例超时（秒）
TIMEOUT_SEC = 60.0

# 输出目录
OUT_DIR = "/content/scct_cadical_experiment"
os.makedirs(OUT_DIR, exist_ok=True)

# 随机种子（可固定以复现）
random.seed(42)


# ============================================================
# 3. 工具函数：生成随机 3-SAT 实例（DIMACS CNF）
# ============================================================

def generate_random_3sat(n, ratio=4.2):
    """
    生成随机 3-SAT CNF 实例（DIMACS 字符串）。
    - n: 变量数
    - ratio: m/n 密度
    """
    m = int(round(ratio * n))
    clauses = []
    for _ in range(m):
        # 选三个不同变量
        vars_ = random.sample(range(1, n+1), 3)
        # 随机符号
        lits = []
        for v in vars_:
            if random.random() < 0.5:
                lits.append(str(v))
            else:
                lits.append("-" + str(v))
        clause = " ".join(lits) + " 0"
        clauses.append(clause)
    header = f"p cnf {n} {m}"
    dimacs = "c random 3-SAT\n" + header + "\n" + "\n".join(clauses) + "\n"
    return dimacs


# ============================================================
# 4. 结构压缩度量：C_t, lambda_B 等
# ============================================================

def Ct(data_bytes):
    """zlib level=9 压缩长度"""
    return len(zlib.compress(data_bytes, 9))

SEP = b"||"
C_SEP = Ct(SEP)

def compute_structural_features(dimacs_str, trace_str):
    """
    输入：DIMACS 文本、CaDiCaL 原始输出文本
    返回：C_p, C_cond, lambda_B, trace_len
    """
    dimacs_bytes = dimacs_str.encode("utf-8", errors="ignore")
    trace_bytes = trace_str.encode("utf-8", errors="ignore")

    Cp = Ct(dimacs_bytes)
    Cjoint = Ct(dimacs_bytes + SEP + trace_bytes)
    Ccond = max(Cjoint - Cp - C_SEP, 1)

    lambda_B = Ccond / (Cp + Ccond)

    # trace_len：简单用输出行数作为工作量 proxy
    trace_len = len(trace_str.strip().splitlines())

    return Cp, Ccond, lambda_B, trace_len


# ============================================================
# 5. 调用 CaDiCaL 求解单个实例
# ============================================================

def solve_with_cadical(dimacs_str, n, inst_id):
    """
    将 DIMACS 写入临时文件，用 CaDiCaL 求解，
    记录 T、solver stdout（trace）、C_p、C_cond、lambda_B 等。
    """
    cnf_path = os.path.join(OUT_DIR, f"{inst_id}.cnf")
    with open(cnf_path, "w") as f:
        f.write(dimacs_str)

    cmd = [CADICAL_BIN, cnf_path]
    start = time.perf_counter()
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=TIMEOUT_SEC
        )
        elapsed = time.perf_counter() - start
        stdout = result.stdout
        stderr = result.stderr

        solved = (result.returncode == 10) or (result.returncode == 20)
        sat = (result.returncode == 10)

    except subprocess.TimeoutExpired as e:
        elapsed = TIMEOUT_SEC
        stdout = e.stdout.decode("utf-8", errors="ignore") if e.stdout else ""
        stderr = e.stderr.decode("utf-8", errors="ignore") if e.stderr else ""
        solved = False
        sat = None

    Cp, Ccond, lambda_B, trace_len = compute_structural_features(dimacs_str, stdout)

    return {
        "inst_id": inst_id,
        "n_vars": n,
        "n_clauses": int(round(RATIO * n)),
        "ratio": RATIO,
        "T": elapsed,
        "log2_T": math.log2(elapsed) if elapsed > 0 else float("nan"),
        "sat": sat,
        "solved": solved,
        "trace_len": trace_len,
        "log2_trace": math.log2(trace_len) if trace_len > 0 else float("nan"),
        "C_p": Cp,
        "C_cond": Ccond,
        "lambda_B": lambda_B,
    }


# ============================================================
# 6. 主循环：生成 & 求解 & 收集数据
# ============================================================

all_records = []

for n in N_VALUES:
    for i in range(INSTANCES_PER_N):
        inst_id = f"n{n}_i{i}"
        print(f"[GEN+SOLVE] n={n}, instance={i} ...")
        dimacs_str = generate_random_3sat(n, RATIO)
        rec = solve_with_cadical(dimacs_str, n, inst_id)
        all_records.append(rec)

df = pd.DataFrame(all_records)

csv_path = os.path.join(OUT_DIR, "scct_cadical_results.csv")
df.to_csv(csv_path, index=False)
print(f"\nSaved results to: {csv_path}\n")

# ============================================================
# 7. 基本统计与预览
# ============================================================

print("=== 数据预览 ===")
print(df.head())

print("\n=== 描述统计 ===")
print(df.describe(include="all"))

# 只保留真正有用的样本：solved=True 且 log2_T、log2_trace 非 NaN
valid_time = df[df["solved"] & df["log2_T"].notna()].copy()
valid_work = df[df["solved"] & df["log2_trace"].notna()].copy()

print(f"\n=== 有效样本数（时间） === {valid_time.shape}")
print(f"=== 有效样本数（工作量） === {valid_work.shape}")


# ============================================================
# 8. 线性回归：Structure–Time & Structure–Work Laws
# ============================================================

def fit_linear_model(df_sub, y_col, label):
    """
    拟合 log2 T 或 log2 trace:
      y ≈ α λ_B + β log2 n + γ
    """
    X = np.column_stack([
        df_sub["lambda_B"].values,
        np.log2(df_sub["n_vars"].values)
    ])
    y = df_sub[y_col].values
    model = LinearRegression()
    model.fit(X, y)
    α, β = model.coef_
    γ = model.intercept_
    R2 = model.score(X, y)
    return α, β, γ, R2

# --- Structure–Time Law ---
alpha_T, beta_T, gamma_T, R2_T = fit_linear_model(valid_time, "log2_T", "Time")

print("\n=== 结构–时间定律（Structure–Time Law, CaDiCaL 版） ===")
print("模型：log2 T(x) ≈ α λ_B + β log2 n + γ")
print(f"α ≈ {alpha_T:8.3f}, β ≈ {beta_T:8.3f}, γ ≈ {gamma_T:8.3f}, R^2 ≈ {R2_T:6.3f}")

# const = 2^γ
const_T = 2 ** gamma_T
print("等价于：T(x) ≈ const · n^β · 2^(α λ_B)")
print(f"const ≈ {const_T:.3e}")

# --- Structure–Work Law ---
alpha_W, beta_W, gamma_W, R2_W = fit_linear_model(valid_work, "log2_trace", "Work")

print("\n=== 结构–工作量定律（Structure–Work Law, CaDiCaL 版） ===")
print("模型：log2 |trace(x)| ≈ α' λ_B + β' log2 n + γ'")
print(f"α' ≈ {alpha_W:8.3f}, β' ≈ {beta_W:8.3f}, γ' ≈ {gamma_W:8.3f}, R^2 ≈ {R2_W:6.3f}")

const_W = 2 ** gamma_W
print("等价于：|trace(x)| ≈ const' · n^{β'} · 2^{α' λ_B}")
print(f"const' ≈ {const_W:.3e}")
