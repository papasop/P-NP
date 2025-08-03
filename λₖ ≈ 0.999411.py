import random, time, json, zlib, math
from ortools.constraint_solver import pywrapcp, routing_enums_pb2

# Step 1: 生成 n = 2000 的 TSP 实例
n = 2000
random.seed(42)
coords = [(random.uniform(0, 1000), random.uniform(0, 1000)) for _ in range(n)]
dist_matrix = [
    [int(((x1 - x2)**2 + (y1 - y2)**2)**0.5) for x2, y2 in coords]
    for x1, y1 in coords
]

# Step 2: 创建数据模型
def create_data_model():
    return {
        'distance_matrix': dist_matrix,
        'num_vehicles': 1,
        'depot': 0,
    }

data = create_data_model()

# Step 3: 设置 OR-Tools 路由模型
manager = pywrapcp.RoutingIndexManager(len(data['distance_matrix']),
                                       data['num_vehicles'], data['depot'])
routing = pywrapcp.RoutingModel(manager)

def distance_callback(from_index, to_index):
    return data['distance_matrix'][manager.IndexToNode(from_index)][manager.IndexToNode(to_index)]

transit_callback_index = routing.RegisterTransitCallback(distance_callback)
routing.SetArcCostEvaluatorOfAllVehicles(transit_callback_index)

# 使用 NP 难策略：GUIDED_LOCAL_SEARCH
search_params = pywrapcp.DefaultRoutingSearchParameters()
search_params.first_solution_strategy = (
    routing_enums_pb2.FirstSolutionStrategy.PATH_CHEAPEST_ARC)
search_params.local_search_metaheuristic = (
    routing_enums_pb2.LocalSearchMetaheuristic.GUIDED_LOCAL_SEARCH)
search_params.time_limit.seconds = 60

# Step 4: 求解 TSP 并计时
start = time.time()
solution = routing.SolveWithParameters(search_params)
end = time.time()
T = end - start

# Step 5: 构造解路径
def get_solution_path():
    index = routing.Start(0)
    path = []
    while not routing.IsEnd(index):
        path.append(manager.IndexToNode(index))
        index = solution.Value(routing.NextVar(index))
    return path

solution_path = get_solution_path()

# Step 6: λₖ + log₂T + Λ(x)
K_problem = len(zlib.compress(json.dumps(dist_matrix).encode()))
K_solution = len(zlib.compress(json.dumps(solution_path).encode()))
λ_k = (K_problem - K_solution) / K_problem
log2T = math.log2(T) if T > 0 else -100
Lambda = λ_k * log2T

# Step 7: 输出结果
print(f"T = {T:.6f} 秒")
print(f"log₂T = {log2T:.6f}")
print(f"λₖ = {λ_k:.6f}")
print(f"Λ(x) = {Lambda:.6f}")
print(f"K_problem = {K_problem}, K_solution = {K_solution}")
