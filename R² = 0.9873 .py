import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import PolynomialFeatures
from sklearn.metrics import r2_score

# 模拟数据（将被用户实际数据替换）
data = {
    'n': [6, 7, 8, 9, 10],
    'lambda_k_brute': [0.796460, 0.837838, 0.866142, 0.890041, 0.906040],
    'log2T_brute': [-10.961081, -9.237618, -4.505051, -0.576732, 1.506998],
    'lambda_k_greedy': [0.779279, 0.829431, 0.863049, 0.887755, 0.903553],
    'log2T_greedy': [-14.912537, -15.034216, -14.771181, -14.790547, -14.624961]
}

df = pd.DataFrame(data)

# 二次多项式拟合函数
def quadratic_fit(x, y):
    poly = PolynomialFeatures(degree=2)
    x_poly = poly.fit_transform(np.array(x).reshape(-1, 1))
    model = LinearRegression().fit(x_poly, y)
    y_pred = model.predict(x_poly)
    r2 = r2_score(y, y_pred)
    return model, poly, y_pred, r2

# 对 brute 模型进行二次拟合
model_brute, poly_brute, y_pred_brute, r2_brute = quadratic_fit(df['lambda_k_brute'], df['log2T_brute'])

# 对 greedy 模型进行二次拟合
model_greedy, poly_greedy, y_pred_greedy, r2_greedy = quadratic_fit(df['lambda_k_greedy'], df['log2T_greedy'])

# 可视化
plt.figure(figsize=(10, 6))
plt.scatter(df['lambda_k_brute'], df['log2T_brute'], color='red', label='Brute data')
plt.plot(df['lambda_k_brute'], y_pred_brute, color='darkred', label=f'Brute fit (R²={r2_brute:.4f})')

plt.scatter(df['lambda_k_greedy'], df['log2T_greedy'], color='blue', label='Greedy data')
plt.plot(df['lambda_k_greedy'], y_pred_greedy, color='darkblue', label=f'Greedy fit (R²={r2_greedy:.4f})')

plt.xlabel("λₖ")
plt.ylabel("log₂T")
plt.title("Quadratic Regression: log₂T vs λₖ (Brute vs Greedy)")
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()

(model_brute.coef_, model_brute.intercept_), r2_brute, (model_greedy.coef_, model_greedy.intercept_), r2_greedy
