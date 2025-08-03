import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from sklearn.metrics import r2_score

# 示例数据（来自用户的结构数据，n=6~10，brute & greedy）
data = {
    "n": [6]*5 + [7]*5 + [8]*5 + [9]*5 + [10]*5,
    "mode": ["brute"]*25,
    "lambda_k": [
        0.717, 0.705, 0.720, 0.714, 0.720,
        0.736, 0.739, 0.741, 0.734, 0.743,
        0.766, 0.758, 0.763, 0.763, 0.765,
        0.780, 0.781, 0.778, 0.780, 0.778,
        0.795, 0.803, 0.801, 0.792, 0.799
    ],
    "log2T": [
        -11.95, -11.78, -11.81, -11.79, -12.01,
        -9.13, -9.20, -9.16, -9.16, -9.19,
        -6.27, -6.26, -6.34, -6.22, -6.27,
        -3.25, -2.99, -2.47, -3.20, -3.24,
        0.40, -0.08, 0.43, 0.10, 0.43
    ]
}
df_brute = pd.DataFrame(data)

# 模型1：指数模型 log2T = a + b·e^(c·λₖ)
def exp_model(lam, a, b, c):
    return a + b * np.exp(c * lam)

params_exp, _ = curve_fit(exp_model, df_brute["lambda_k"], df_brute["log2T"], maxfev=10000)
pred_exp = exp_model(df_brute["lambda_k"], *params_exp)
r2_exp = r2_score(df_brute["log2T"], pred_exp)

# 模型2：线性模型 log2T = a + b·n
params_lin = np.polyfit(df_brute["n"], df_brute["log2T"], 1)
pred_lin = np.polyval(params_lin, df_brute["n"])
r2_lin = r2_score(df_brute["log2T"], pred_lin)

# 生成可视化
plt.figure(figsize=(10, 5))

# 指数模型拟合图
plt.subplot(1, 2, 1)
plt.scatter(df_brute["lambda_k"], df_brute["log2T"], label="Data")
plt.plot(df_brute["lambda_k"], pred_exp, color="red", label="Exponential Fit")
plt.title(f"Exponential Fit: R² = {r2_exp:.4f}")
plt.xlabel("λₖ")
plt.ylabel("log₂T")
plt.legend()

# 线性模型拟合图（对 n）
plt.subplot(1, 2, 2)
plt.scatter(df_brute["n"], df_brute["log2T"], label="Data")
plt.plot(df_brute["n"], pred_lin, color="green", label="Linear Fit")
plt.title(f"Linear Fit (n): R² = {r2_lin:.4f}")
plt.xlabel("n")
plt.ylabel("log₂T")
plt.legend()

plt.tight_layout()
plt.show()

(params_exp, r2_exp), (params_lin, r2_lin)
