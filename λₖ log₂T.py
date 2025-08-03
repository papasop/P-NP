import itertools, time, random, math, zlib
import matplotlib.pyplot as plt
import numpy as np
from io import BytesIO

# 结构压缩函数
def compress_size(obj):
    raw = str(obj).encode('utf-8')
    return len(zlib.compress(raw))

# TSP 距离矩阵生成
def generate_tsp_instance(n, seed=None):
    if seed: random.seed(seed)
    points = [(random.uniform(0, 100), random.uniform(0, 100)) for _ in range(n)]
    dist = [[math.hypot(px - qx, py - qy) for (qx, qy) in points] for (px, py) in points]
    return dist

# 暴力解 TSP（NP解法）
def tsp_brute_force(dist):
    n = len(dist)
    nodes = list(range(n))
    best_len = float('inf')
    best_path = None
    for perm in itertools.permutations(nodes[1:]):
        path = [0] + list(perm)
        length = sum(dist[path[i]][path[i+1]] for i in range(n - 1)) + dist[path[-1]][0]
        if length < best_len:
            best_len = length
            best_path = path
    return best_path, best_len

# 贪心近似解（P解法）
def tsp_greedy(dist):
    n = len(dist)
    visited = [False] * n
    path = [0]
    visited[0] = True
    total = 0
    current = 0
    for _ in range(n - 1):
        next_node = min((i for i in range(n) if not visited[i]), key=lambda x: dist[current][x])
        total += dist[current][next_node]
        visited[next_node] = True
        path.append(next_node)
        current = next_node
    total += dist[current][0]
    path.append(0)
    return path, total

# 指标计算
def evaluate(n, mode="brute"):
    dist = generate_tsp_instance(n)
    K_problem = compress_size(dist)

    start = time.time()
    if mode == "brute":
        path, cost = tsp_brute_force(dist)
    else:
        path, cost = tsp_greedy(dist)
    end = time.time()
    T = end - start

    K_solution = compress_size((path, cost))
    λ_k = (K_problem - K_solution) / K_problem
    log2T = math.log2(T) if T > 0 else float('-inf')
    Λ = λ_k * log2T

    print(f"n = {n}, mode = {mode}")
    print(f"T = {T:.6f} sec, log2T = {log2T:.6f}")
    print(f"λₖ = {λ_k:.6f}, K_problem = {K_problem}, K_solution = {K_solution}")
    print(f"Λ(x) = {Λ:.6f}\n")
    return λ_k, log2T, Λ

# 主循环：n = 6 to 10
brute_results = []
greedy_results = []
for n in range(6, 11):
    brute_results.append(evaluate(n, "brute"))
    greedy_results.append(evaluate(n, "greedy"))

# 拟合并绘图
def plot_fit(data, label, color):
    λk = np.array([x[0] for x in data])
    logT = np.array([x[1] for x in data])
    fit = np.polyfit(λk, logT, 2)
    curve = np.poly1d(fit)
    xfit = np.linspace(min(λk), max(λk), 100)
    plt.plot(xfit, curve(xfit), '--', color=color, label=f"{label} fit")
    plt.scatter(λk, logT, color=color, label=f"{label} data")
    print(f"{label} 回归：log₂T ≈ {fit[0]:.2e}·λ² + {fit[1]:.2e}·λ + {fit[2]:.2f}")

plt.figure(figsize=(8, 6))
plot_fit(brute_results, "Brute (NP)", "red")
plot_fit(greedy_results, "Greedy (P)", "green")
plt.xlabel("λₖ")
plt.ylabel("log₂ T(x)")
plt.title("拟合: log₂ T(x) vs λₖ")
plt.legend()
plt.grid(True)
plt.show()
