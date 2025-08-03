# ✅ 安装依赖
import time, math, zlib, random, json
import matplotlib.pyplot as plt
from itertools import permutations
import numpy as np

# ✅ λₖ 计算函数
def compute_lambda_k(problem_data, solution_data):
    def compress(obj):
        raw = json.dumps(obj, sort_keys=True).encode()
        return len(zlib.compress(raw))
    K_problem = compress(problem_data)
    K_solution = compress(solution_data)
    λ_k = (K_problem - K_solution) / K_problem if K_problem != 0 else 0
    return λ_k, K_problem, K_solution

# ✅ 生成 TSP 问题
def generate_tsp_instance(n):
    return [(random.uniform(0, 100), random.uniform(0, 100)) for _ in range(n)]

def tsp_distance(city1, city2):
    return math.hypot(city1[0] - city2[0], city1[1] - city2[1])

def total_distance(route, cities):
    return sum(tsp_distance(cities[route[i]], cities[route[(i+1)%len(route)]]) for i in range(len(route)))

# ✅ 暴力 TSP 解法（NP类）
def brute_force_tsp(cities):
    n = len(cities)
    routes = permutations(range(n))
    best_route = None
    min_dist = float('inf')
    for route in routes:
        dist = total_distance(route, cities)
        if dist < min_dist:
            min_dist = dist
            best_route = route
    return list(best_route), min_dist

# ✅ 贪心 TSP 解法（P类近似）
def greedy_tsp(cities):
    n = len(cities)
    unvisited = set(range(n))
    route = [unvisited.pop()]
    while unvisited:
        last = route[-1]
        next_city = min(unvisited, key=lambda c: tsp_distance(cities[last], cities[c]))
        route.append(next_city)
        unvisited.remove(next_city)
    return route, total_distance(route, cities)

# ✅ 主测试函数
def run_experiment(n, mode="brute", verbose=True):
    cities = generate_tsp_instance(n)
    
    start = time.time()
    if mode == "brute":
        solution, dist = brute_force_tsp(cities)
    else:
        solution, dist = greedy_tsp(cities)
    end = time.time()

    T = end - start
    log2T = math.log2(T + 1e-10)
    λ_k, Kp, Ks = compute_lambda_k(cities, solution)
    Λ = λ_k * log2T

    if verbose:
        print(f"n = {n}, mode = {mode}")
        print(f"T = {T:.6f} sec, log2T = {log2T:.6f}")
        print(f"λₖ = {λ_k:.6f}, K_problem = {Kp}, K_solution = {Ks}")
        print(f"Λ(x) = {Λ:.6f}\n")

    return {
        "n": n, "T": T, "log2T": log2T,
        "λ_k": λ_k, "Λ": Λ,
        "Kp": Kp, "Ks": Ks,
        "mode": mode
    }

# ✅ 批量实验
results = []
for n in [6, 7, 8, 9, 10]:  # 可调整为更大 n（P类可支持 n=50+）
    results.append(run_experiment(n, mode="brute"))   # NP 类
    results.append(run_experiment(n, mode="greedy"))  # P 类近似

# ✅ 可视化
def plot_metric(metric):
    xs_brute = [r["n"] for r in results if r["mode"]=="brute"]
    ys_brute = [r[metric] for r in results if r["mode"]=="brute"]
    xs_greedy = [r["n"] for r in results if r["mode"]=="greedy"]
    ys_greedy = [r[metric] for r in results if r["mode"]=="greedy"]

    plt.figure(figsize=(8,5))
    plt.plot(xs_brute, ys_brute, 'o-r', label="NP (brute)")
    plt.plot(xs_greedy, ys_greedy, 'o-b', label="P (greedy)")
    plt.xlabel("Problem Size (n)")
    plt.ylabel(metric)
    plt.title(f"{metric} vs n")
    plt.legend()
    plt.grid(True)
    plt.show()

plot_metric("λ_k")
plot_metric("log2T")
plot_metric("Λ")
