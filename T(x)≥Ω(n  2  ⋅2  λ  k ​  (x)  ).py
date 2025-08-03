import pandas as pd
from sklearn.metrics import r2_score
import numpy as np

# 示例数据（请根据你的实验数据替换）
df = pd.DataFrame({
    'n': [6, 7, 8, 9, 10],
    'lambda_k': [0.8, 0.83, 0.87, 0.89, 0.91],
    'log2T_brute': [-10.5, -9.2, -6.5, -3.0, 0.4],
    'log2T_greedy': [-15.0, -14.9, -14.7, -14.5, -14.3]
})

# Brute: Quadratic model
X_brute = np.column_stack([df['lambda_k']**2, df['lambda_k'], np.ones(len(df))])
coef_brute, _, _, _ = np.linalg.lstsq(X_brute, df['log2T_brute'], rcond=None)
pred_brute = X_brute @ coef_brute
r2_brute = r2_score(df['log2T_brute'], pred_brute)

# Greedy: Quadratic model
X_greedy = np.column_stack([df['lambda_k']**2, df['lambda_k'], np.ones(len(df))])
coef_greedy, _, _, _ = np.linalg.lstsq(X_greedy, df['log2T_greedy'], rcond=None)
pred_greedy = X_greedy @ coef_greedy
r2_greedy = r2_score(df['log2T_greedy'], pred_greedy)

# 显示拟合结果
df['log2T_brute_pred'] = pred_brute
df['log2T_greedy_pred'] = pred_greedy
import matplotlib.pyplot as plt

plt.figure()
plt.scatter(df['lambda_k'], df['log2T_brute'], label="Brute (True)", marker='o')
plt.plot(df['lambda_k'], df['log2T_brute_pred'], label="Brute (Fit)", linestyle='--')
plt.scatter(df['lambda_k'], df['log2T_greedy'], label="Greedy (True)", marker='x')
plt.plot(df['lambda_k'], df['log2T_greedy_pred'], label="Greedy (Fit)", linestyle=':')
plt.xlabel("λₖ")
plt.ylabel("log₂T")
plt.legend()
plt.title("Quadratic Fit: log₂T vs λₖ")
plt.grid(True)
plt.show()

df[['n', 'lambda_k', 'log2T_brute', 'log2T_brute_pred', 'log2T_greedy', 'log2T_greedy_pred']], coef_brute, r2_brute, coef_greedy, r2_greedy
