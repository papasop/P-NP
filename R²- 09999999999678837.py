import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from sklearn.linear_model import LinearRegression
from sklearn.metrics import r2_score

# 手动数据输入
data = {
    'n': [10, 15, 20, 25, 30, 35, 40, 45, 50],
    'lambda_k': [0.88]*9,
    'T_brute': [184.04, 414.08, 736.15, 1150.23, 1656.34, 2254.46, 2944.60, 3726.76, 4600.94],
}

df = pd.DataFrame(data)
df['log2T'] = np.log2(df['T_brute'])
df['log2n'] = np.log2(df['n'])

# 构建联合回归模型 log2T ~ lambda_k + log2n
X = df[['lambda_k', 'log2n']]
y = df['log2T']
reg = LinearRegression().fit(X, y)
df['log2T_pred'] = reg.predict(X)
r2 = r2_score(y, df['log2T_pred'])

# 打印结果
print("=== 回归结果 ===")
print(f"Intercept (γ): {reg.intercept_}")
print(f"Coefficients [λₖ, log2n]: {reg.coef_}")
print(f"R²: {r2}")

# 可视化
plt.figure(figsize=(8, 5))
plt.plot(df['n'], df['log2T'], 'o-', label='Actual')
plt.plot(df['n'], df['log2T_pred'], 's--', label='Predicted')
plt.xlabel('n')
plt.ylabel('log₂T')
plt.title('Log₂T vs n with λₖ=0.88')
plt.legend()
plt.grid(True)
plt.show()

# 可选：导出 CSV
df.to_csv("lambda_model_fit.csv", index=False)
