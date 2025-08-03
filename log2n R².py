import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from sklearn.linear_model import LinearRegression
from sklearn.metrics import r2_score

# 构造数据：手动录入 λₖ、n 和 T(x)
data = {
    'n': [10, 10, 15, 15, 20, 20, 25, 25, 30, 30, 35, 35, 40, 40, 45, 45, 50, 50],
    'lambda_k': [0.88, 0.76, 0.88, 0.75, 0.88, 0.77, 0.88, 0.76, 0.88, 0.75, 0.88, 0.77, 0.88, 0.76, 0.88, 0.75, 0.88, 0.77],
    'T': [184.04, 169.35, 414.08, 378.40, 736.15, 682.11, 1150.23, 1058.43,
          1656.34, 1513.61, 2254.46, 2088.96, 2944.60, 2709.58, 3726.76, 3405.63, 4600.94, 4263.17]
}

df = pd.DataFrame(data)
df['log2T'] = np.log2(df['T'])
df['log2n'] = np.log2(df['n'])

# 多元回归：log2T ~ lambda_k + log2n
X = df[['lambda_k', 'log2n']]
y = df['log2T']

model = LinearRegression()
model.fit(X, y)

# 预测和拟合指标
df['log2T_pred'] = model.predict(X)
r2 = r2_score(y, df['log2T_pred'])
coefficients = model.coef_
intercept = model.intercept_

# 打印结果
print("=== 回归结果 ===")
print(f"Intercept (γ): {intercept}")
print(f"Coefficients [λₖ, log2n]: {coefficients}")
print(f"R²: {r2}")

# 可视化对比
plt.figure(figsize=(8, 5))
plt.plot(df['log2T'], label='Actual log2T', marker='o')
plt.plot(df['log2T_pred'], label='Predicted log2T', marker='x')
plt.title("log₂T vs Prediction")
plt.xlabel("Sample Index")
plt.ylabel("log₂T")
plt.legend()
plt.grid(True)
plt.show()
