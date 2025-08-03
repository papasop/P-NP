# === 安装依赖（Colab 通常自带）===
import random, time, zlib, json, math
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
import pandas as pd

# === 基础函数：结构压缩复杂度指标 λ_K ===
def compute_lambda_k(obj_problem, obj_solution):
    encoded_problem = json.dumps(obj_problem).encode()
    encoded_solution = json.dumps(obj_solution).encode()
    K_problem = len(zlib.compress(encoded_problem))
    K_solution = len(zlib.compress(encoded_solution))
    lambda_k = (K_problem - K_solution) / K_problem if K_problem > 0 else 0
    return lambda_k, K_problem, K_solution

# === 构造 TSP 问题实例（n 个城市）===
def generate_tsp_instance(n):
    return [(random.uniform(0, 100), random.uniform(0, 100)) for _ in range(n)]

def distance(p1, p2):
    return ((p1[0] - p2[0])**2 + (p1[1] - p2[1])**2)**0.5

def total_path_length(path, cities):
    return sum(distance(cities[path[i]], cities[path[(i+1)%len(path)]]) for i in range(len(path)))

# === 暴力解法（NP）：全排列尝试最短路径 ===
from itertools import permutations
def tsp_brute_force(cities):
    n = len(cities)
    best_path, best_cost = None, float('inf')
    for perm in permutations(range(n)):
        cost = total_path_length(perm, cities)
        if cost < best_cost:
            best_path, best_cost = perm, cost
    return best_path

# === 贪心解法（P）：每次选择最近城市 ===
def tsp_greedy(cities):
    n = len(cities)
    unvisited = set(range(1, n))
    path = [0]
    while unvisited:
        last = path[-1]
        next_city = min(unvisited, key=lambda i: distance(cities[last], cities[i]))
        path.append(next_city)
        unvisited.remove(next_city)
    return path

# === 实验核心 ===
def run_tsp_experiment(n_list, mode='brute', samples=1):
    records = []
    for n in n_list:
        for _ in range(samples):
            cities = generate_tsp_instance(n)
            t0 = time.time()
            if mode == 'brute':
                path = tsp_brute_force(cities)
            elif mode == 'greedy':
                path = tsp_greedy(cities)
            else:
                continue
            T = time.time() - t0
            log2T = math.log2(T) if T > 0 else -100
            λk, Kp, Ks = compute_lambda_k(cities, path)
            Λ = λk * log2T
            records.append({
                'n': n, 'mode': mode, 'T': T, 'log2T': log2T,
                'lambda_k': λk, 'K_problem': Kp, 'K_solution': Ks, 'Lambda': Λ
            })
    return pd.DataFrame(records)

# === 非线性拟合函数：二次、多项式、幂律 ===
def quadratic(x, a, b, c): return a * x**2 + b * x + c
def power_law(x, a, b, c): return a * np.power(x, b) + c

def fit_and_plot(df, mode='brute'):
    sub = df[df['mode'] == mode].sort_values('lambda_k')
    x = sub['lambda_k'].values
    y = sub['log2T'].values

    fig, ax = plt.subplots()
    ax.scatter(x, y, label='data', color='blue')

    # 拟合：二次曲线
    popt_quad, _ = curve_fit(quadratic, x, y)
    y_quad = quadratic(x, *popt_quad)
    ax.plot(x, y_quad, label=f'Quadratic: {popt_quad}', color='green')

    # 拟合：幂律
    popt_pow, _ = curve_fit(power_law, x, y, maxfev=10000)
    y_pow = power_law(x, *popt_pow)
    ax.plot(x, y_pow, label=f'Power: {popt_pow}', color='red')

    ax.set_title(f'{mode} fit: log2T vs lambda_k')
    ax.set_xlabel('lambda_k')
    ax.set_ylabel('log2(T)')
    ax.legend()
    plt.grid(True)
    plt.show()

    print(f"{mode.upper()} Quadratic Coefficients:", popt_quad)
    print(f"{mode.upper()} Power Law Coefficients:", popt_pow)

# === 执行测试 ===
n_list_small = [6, 7, 8, 9, 10]   # Brute 适用范围
n_list_greedy = list(range(6, 50, 5))  # Greedy 可扩展范围

df_brute = run_tsp_experiment(n_list_small, 'brute', samples=2)
df_greedy = run_tsp_experiment(n_list_greedy, 'greedy', samples=2)
df_all = pd.concat([df_brute, df_greedy]).reset_index(drop=True)

import pandas as pd
from IPython.display import display
display(df_all)

# === 拟合与绘图 ===
fit_and_plot(df_all, mode='brute')
fit_and_plot(df_all, mode='greedy')
