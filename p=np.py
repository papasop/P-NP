# ===============================================
# Structural Action vs Complexity: P (MST) vs NP (TSP)
# 版本 B：修复版 - 正确的状态编码和结构作用量计算
# ===============================================

import time
import gzip
import json
import math
import random
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Tuple

import numpy as np
import pandas as pd
from tqdm.auto import tqdm
from sklearn.linear_model import LinearRegression
from scipy import stats

# ---------- RNG ----------
RANDOM_SEED = 42
random.seed(RANDOM_SEED)
np.random.seed(RANDOM_SEED)

# ---------- Compression helpers ----------
def compress_bytes(data: bytes) -> int:
    return len(gzip.compress(data))

def json_compress_len(obj: Any) -> int:
    s = json.dumps(obj, separators=(",", ":")).encode("utf-8")
    return compress_bytes(s)

def safe_log2(x: float) -> float:
    if x <= 0:
        return float("nan")
    return math.log2(x)

# ---------- Problem generator ----------
def generate_complete_graph(n: int, w_min: int = 1, w_max: int = 10) -> List[List[int]]:
    """Generate a symmetric complete graph with integer weights."""
    w = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            wij = random.randint(w_min, w_max)
            w[i][j] = wij
            w[j][i] = wij
    return w

# ---------- FIXED: Structural action machinery ----------
def compute_lambda_step_fixed(solver_state: Any, reference_state: Any = None) -> float:
    """
    修复版本：只压缩求解状态本身，不重复包含问题描述
    λ_K(t) = K_state / (K_reference + K_state)
    
    reference_state: 用于归一化的参考状态（如初始状态）
    """
    K_state = json_compress_len(solver_state)
    
    if reference_state is not None:
        K_ref = json_compress_len(reference_state)
    else:
        # 使用空状态作为参考
        K_ref = json_compress_len({})
    
    # 避免除零
    if K_ref + K_state == 0:
        return 0.0
    
    return K_state / (K_ref + K_state)

@dataclass
class RunResult:
    problem_type: str  # "MST" or "TSP"
    n: int
    instance_id: int
    T_sec: float
    steps: int
    action: float        # Σ λ_K(t)
    avg_lambda: float    # action / steps
    structural_density: float  # 新增：结构密度度量

# ---------- FIXED: MST (P problem) with proper state encoding ----------
def prim_mst_structural_fixed(w: List[List[int]], instance_id: int) -> RunResult:
    """
    Prim's MST algorithm with FIXED structural trace.
    只记录增量信息，避免状态爆炸。
    """
    n = len(w)
    
    # 初始参考状态
    initial_state = {"type": "initial", "n": n}
    
    in_tree = [False]*n
    in_tree[0] = True
    current_tree_size = 1

    steps = 0
    total_action = 0.0

    t0 = time.perf_counter()
    
    # n-1 edges
    for _ in range(n-1):
        best = None
        best_w = None
        
        # 寻找最小边
        for u in range(n):
            if not in_tree[u]:
                continue
            for v in range(n):
                if in_tree[v]:
                    continue
                if best is None or w[u][v] < best_w:
                    best = (u, v)
                    best_w = w[u][v]
        
        u, v = best
        in_tree[v] = True
        current_tree_size += 1

        # FIXED: 只记录增量状态信息
        solver_state = {
            "type": "mst_step",
            "added_vertex": v,
            "added_edge": (u, v),
            "edge_weight": best_w,
            "current_tree_size": current_tree_size,
            "remaining_vertices": n - current_tree_size
        }
        
        lam = compute_lambda_step_fixed(solver_state, initial_state)
        total_action += lam
        steps += 1

    t1 = time.perf_counter()
    T = t1 - t0
    avg_lambda = total_action / steps if steps > 0 else 0.0
    
    # 计算结构密度：平均每个步骤的信息含量
    structural_density = avg_lambda

    return RunResult(
        problem_type="MST",
        n=n,
        instance_id=instance_id,
        T_sec=T,
        steps=steps,
        action=total_action,
        avg_lambda=avg_lambda,
        structural_density=structural_density,
    )

# ---------- FIXED: TSP (NP-complete) with proper state encoding ----------
def tsp_bruteforce_structural_fixed(w: List[List[int]], instance_id: int) -> RunResult:
    """
    TSP solver with FIXED state encoding.
    只记录关键决策信息，避免完整路径历史。
    """
    n = len(w)
    
    # 初始参考状态
    initial_state = {"type": "initial", "n": n}

    best_cost = float("inf")
    best_path = None

    steps = 0
    total_action = 0.0

    t0 = time.perf_counter()

    def dfs(path: List[int], cost_so_far: int, visited: List[bool]):
        nonlocal best_cost, best_path, steps, total_action

        current_city = path[-1] if path else 0
        path_length = len(path)
        remaining = n - path_length
        
        # FIXED: 只记录关键状态信息
        solver_state = {
            "type": "tsp_step",
            "current_city": current_city,
            "path_length": path_length,
            "remaining_cities": remaining,
            "cost_so_far": cost_so_far,
            "is_pruned": cost_so_far >= best_cost,
            "is_complete": path_length == n
        }
        
        lam = compute_lambda_step_fixed(solver_state, initial_state)
        total_action += lam
        steps += 1

        # 剪枝
        if cost_so_far >= best_cost:
            return

        # 完整路径检查
        if len(path) == n:
            total_cost = cost_so_far + w[path[-1]][path[0]]
            if total_cost < best_cost:
                best_cost = total_cost
                best_path = path[:]
            return

        # 继续搜索
        last = path[-1]
        for nxt in range(n):
            if not visited[nxt]:
                visited[nxt] = True
                dfs(path + [nxt], cost_so_far + w[last][nxt], visited)
                visited[nxt] = False

    visited = [False]*n
    visited[0] = True
    dfs([0], 0, visited)

    t1 = time.perf_counter()
    T = t1 - t0
    avg_lambda = total_action / steps if steps > 0 else 0.0
    
    structural_density = avg_lambda

    return RunResult(
        problem_type="TSP",
        n=n,
        instance_id=instance_id,
        T_sec=T,
        steps=steps,
        action=total_action,
        avg_lambda=avg_lambda,
        structural_density=structural_density,
    )

# ---------- Enhanced TSP with heuristic (对比实验) ----------
def tsp_nearest_neighbor_structural(w: List[List[int]], instance_id: int) -> RunResult:
    """
    最近邻启发式TSP求解器，用于对比精确算法。
    """
    n = len(w)
    initial_state = {"type": "initial", "n": n}

    steps = 0
    total_action = 0.0

    t0 = time.perf_counter()

    # 最近邻算法
    visited = [False]*n
    path = [0]  # 从城市0开始
    visited[0] = True
    total_cost = 0

    while len(path) < n:
        current = path[-1]
        best_next = None
        best_dist = float('inf')
        
        # 寻找最近的未访问城市
        for next_city in range(n):
            if not visited[next_city] and w[current][next_city] < best_dist:
                best_next = next_city
                best_dist = w[current][next_city]
        
        path.append(best_next)
        visited[best_next] = True
        total_cost += best_dist
        
        # 记录状态
        solver_state = {
            "type": "nn_tsp_step", 
            "current_city": current,
            "next_city": best_next,
            "path_length": len(path),
            "remaining": n - len(path)
        }
        
        lam = compute_lambda_step_fixed(solver_state, initial_state)
        total_action += lam
        steps += 1

    # 回到起点
    total_cost += w[path[-1]][path[0]]

    t1 = time.perf_counter()
    T = t1 - t0
    avg_lambda = total_action / steps if steps > 0 else 0.0
    
    structural_density = avg_lambda

    return RunResult(
        problem_type="TSP_NN",  # 标记为启发式版本
        n=n,
        instance_id=instance_id,
        T_sec=T,
        steps=steps,
        action=total_action,
        avg_lambda=avg_lambda,
        structural_density=structural_density,
    )

# ---------- Sanity check functions ----------
def run_sanity_checks():
    """运行合理性检查"""
    print("=== 运行合理性检查 ===")
    
    # 测试1: 状态压缩的基本性质
    empty_state = {}
    simple_state = {"step": 1, "type": "test"}
    complex_state = {"step": 1, "data": list(range(100))}
    
    lam_empty = compute_lambda_step_fixed(empty_state)
    lam_simple = compute_lambda_step_fixed(simple_state) 
    lam_complex = compute_lambda_step_fixed(complex_state)
    
    print(f"空状态 λ_K: {lam_empty:.4f}")
    print(f"简单状态 λ_K: {lam_simple:.4f}")
    print(f"复杂状态 λ_K: {lam_complex:.4f}")
    
    # 应该满足: lam_empty < lam_simple < lam_complex
    assert lam_empty < lam_simple < lam_complex, "状态压缩逻辑错误！"
    print("✅ 状态压缩测试通过")
    
    # 测试2: 相同算法的可重复性
    test_graph = generate_complete_graph(5)
    result1 = prim_mst_structural_fixed(test_graph, 0)
    result2 = prim_mst_structural_fixed(test_graph, 0)
    
    # 作用量应该相近（允许微小差异）
    action_diff = abs(result1.action - result2.action)
    assert action_diff < 0.1, f"可重复性测试失败: {action_diff}"
    print("✅ 算法可重复性测试通过")

# ---------- Main experiment ----------
def main_experiment():
    """主实验"""
    N_LIST_P = [10, 15, 20, 25, 30]   # MST: 多项式时间
    N_LIST_NP = [6, 7, 8, 9]          # TSP: 精确算法
    N_LIST_NP_HEURISTIC = [10, 15, 20, 25]  # TSP: 启发式算法
    INSTANCES_PER_N = 5

    results: List[RunResult] = []

    print("\n=== P-side: MST (Prim) with FIXED structural action ===")
    for n in tqdm(N_LIST_P):
        for inst in range(INSTANCES_PER_N):
            g = generate_complete_graph(n)
            res = prim_mst_structural_fixed(g, instance_id=inst)
            results.append(res)

    print("\n=== NP-side: TSP (Exact DFS + B&B) with FIXED structural action ===")
    for n in tqdm(N_LIST_NP):
        for inst in range(INSTANCES_PER_N):
            g = generate_complete_graph(n)
            res = tsp_bruteforce_structural_fixed(g, instance_id=inst)
            results.append(res)

    print("\n=== NP-side: TSP (Nearest Neighbor Heuristic) with FIXED structural action ===")
    for n in tqdm(N_LIST_NP_HEURISTIC):
        for inst in range(INSTANCES_PER_N):
            g = generate_complete_graph(n)
            res = tsp_nearest_neighbor_structural(g, instance_id=inst)
            results.append(res)

    return results

# ---------- Analysis functions ----------
def analyze_results(results: List[RunResult]):
    """分析实验结果"""
    df = pd.DataFrame([asdict(r) for r in results])
    df["log2T"] = df["T_sec"].apply(safe_log2)
    df["log2n"] = np.log2(df["n"].astype(float))

    print("\n=== 修复后结果概览 ===")
    display(df.head(10))

    print("\n=== 按问题类型分组统计 ===")
    group_stats = df.groupby("problem_type")[["T_sec", "steps", "action", "avg_lambda", "structural_density", "log2T"]].agg(["mean", "std"])
    display(group_stats)

    # 统计检验：MST vs TSP精确算法
    mst_df = df[df["problem_type"] == "MST"]
    tsp_exact_df = df[df["problem_type"] == "TSP"]
    tsp_nn_df = df[df["problem_type"] == "TSP_NN"]

    print("\n=== 统计显著性检验: MST vs TSP (精确算法) ===")
    if len(mst_df) > 0 and len(tsp_exact_df) > 0:
        t_action, p_action = stats.ttest_ind(mst_df["action"], tsp_exact_df["action"], equal_var=False)
        t_density, p_density = stats.ttest_ind(mst_df["structural_density"], tsp_exact_df["structural_density"], equal_var=False)
        t_time, p_time = stats.ttest_ind(mst_df["log2T"], tsp_exact_df["log2T"], equal_var=False)
        
        print(f"结构作用量: t={t_action:.3f}, p={p_action:.3e}")
        print(f"结构密度: t={t_density:.3f}, p={p_density:.3e}") 
        print(f"运行时间: t={t_time:.3f}, p={p_time:.3e}")

    # 回归分析
    print("\n=== 回归分析: log2T ~ structural_density + log2n ===")
    mask = np.isfinite(df["log2T"]) & np.isfinite(df["structural_density"])
    df_reg = df[mask].copy()
    
    X = df_reg[["structural_density", "log2n"]]
    y = df_reg["log2T"]
    
    reg = LinearRegression().fit(X, y)
    r2 = reg.score(X, y)
    
    print(f"结构密度系数: {reg.coef_[0]:.4f}")
    print(f"问题规模系数: {reg.coef_[1]:.4f}")
    print(f"截距: {reg.intercept_:.4f}")
    print(f"R²: {r2:.4f}")

    # 分类型回归
    print("\n=== 分类型回归分析 ===")
    for ptype in df_reg["problem_type"].unique():
        df_type = df_reg[df_reg["problem_type"] == ptype]
        if len(df_type) < 3:
            continue
            
        X_type = df_type[["structural_density", "log2n"]]
        y_type = df_type["log2T"]
        
        reg_type = LinearRegression().fit(X_type, y_type)
        r2_type = reg_type.score(X_type, y_type)
        
        print(f"{ptype}: 密度系数={reg_type.coef_[0]:.4f}, 规模系数={reg_type.coef_[1]:.4f}, R²={r2_type:.4f}")

    return df

# ---------- Visualization ----------
def plot_results(df):
    """绘制结果图表"""
    import matplotlib.pyplot as plt
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    
    # 1. 结构作用量 vs 问题规模
    for ptype in df["problem_type"].unique():
        subset = df[df["problem_type"] == ptype]
        axes[0,0].scatter(subset["n"], subset["action"], label=ptype, alpha=0.6)
    axes[0,0].set_xlabel("Problem Size (n)")
    axes[0,0].set_ylabel("Structural Action")
    axes[0,0].legend()
    axes[0,0].set_title("Structural Action vs Problem Size")
    
    # 2. 结构密度 vs 问题规模
    for ptype in df["problem_type"].unique():
        subset = df[df["problem_type"] == ptype]
        axes[0,1].scatter(subset["n"], subset["structural_density"], label=ptype, alpha=0.6)
    axes[0,1].set_xlabel("Problem Size (n)")
    axes[0,1].set_ylabel("Structural Density")
    axes[0,1].legend()
    axes[0,1].set_title("Structural Density vs Problem Size")
    
    # 3. 运行时间 vs 结构作用量
    for ptype in df["problem_type"].unique():
        subset = df[df["problem_type"] == ptype]
        axes[0,2].scatter(subset["action"], subset["T_sec"], label=ptype, alpha=0.6)
    axes[0,2].set_xlabel("Structural Action")
    axes[0,2].set_ylabel("Time (sec)")
    axes[0,2].set_yscale('log')
    axes[0,2].legend()
    axes[0,2].set_title("Time vs Structural Action")
    
    # 4. 运行时间 vs 结构密度
    for ptype in df["problem_type"].unique():
        subset = df[df["problem_type"] == ptype]
        axes[1,0].scatter(subset["structural_density"], subset["T_sec"], label=ptype, alpha=0.6)
    axes[1,0].set_xlabel("Structural Density")
    axes[1,0].set_ylabel("Time (sec)")
    axes[1,0].set_yscale('log')
    axes[1,0].legend()
    axes[1,0].set_title("Time vs Structural Density")
    
    # 5. 步骤数对比
    problem_types = df["problem_type"].unique()
    steps_means = [df[df["problem_type"] == pt]["steps"].mean() for pt in problem_types]
    axes[1,1].bar(problem_types, steps_means)
    axes[1,1].set_ylabel("Average Steps")
    axes[1,1].set_title("Average Steps by Algorithm")
    
    # 6. 结构密度分布
    density_data = [df[df["problem_type"] == pt]["structural_density"] for pt in problem_types]
    axes[1,2].boxplot(density_data, labels=problem_types)
    axes[1,2].set_ylabel("Structural Density")
    axes[1,2].set_title("Structural Density Distribution")
    
    plt.tight_layout()
    plt.show()

# ---------- Main execution ----------
if __name__ == "__main__":
    # 1. 运行合理性检查
    run_sanity_checks()
    
    # 2. 运行主实验
    results = main_experiment()
    
    # 3. 分析结果
    df = analyze_results(results)
    
    # 4. 可视化
    plot_results(df)
    
    print("\n=== 实验完成 ===")

