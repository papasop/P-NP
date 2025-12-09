import Mathlib

open scoped BigOperators

namespace StructuralAction

/-! ### 1. 3-SAT 基础语法 -/

/-- 布尔赋值：`n` 个变量，对应 `Fin n → Bool` -/
abbrev Assignment (n : Nat) := Fin n → Bool

/-- 字面：变量索引 + 是否取反 -/
structure Literal (n : Nat) where
  var : Fin n
  neg : Bool
  deriving Repr

/-- 子句：3 个字面 -/
abbrev Clause (n : Nat) := Fin 3 → Literal n

/-- CNF 公式：子句列表 -/
abbrev CNF (n : Nat) := List (Clause n)

/-- 评价字面 -/
def literalEval {n : Nat} (σ : Assignment n) (ℓ : Literal n) : Bool :=
  let b := σ ℓ.var
  if ℓ.neg then !b else b

/-- 评价 3-子句 -/
def clauseEval {n : Nat} (σ : Assignment n) (C : Clause n) : Bool :=
  let ℓ0 := C ⟨0, by decide⟩
  let ℓ1 := C ⟨1, by decide⟩
  let ℓ2 := C ⟨2, by decide⟩
  literalEval σ ℓ0 || literalEval σ ℓ1 || literalEval σ ℓ2

/-- 评价 CNF：所有子句的合取（递归定义版本） -/
def cnfEval {n : Nat} (σ : Assignment n) : CNF n → Bool
  | []      => true
  | C :: Φ  => clauseEval σ C && cnfEval σ Φ

/-- 满足解集合 -/
def satSet {n : Nat} (Φ : CNF n) : Set (Assignment n) :=
  { σ | cnfEval σ Φ = true }


/-! ### 2. 能量函数 E：未满足子句个数（递归定义） -/

/-- 能量：未满足子句数量（递归版） -/
def energy {n : Nat} : CNF n → Assignment n → Nat
  | [],      _ => 0
  | C :: Φ,  σ => energy Φ σ + (if clauseEval σ C then 0 else 1)

/-- 辅助引理：`cnfEval = true` 当且仅当 `energy = 0`。 -/
lemma cnfEval_true_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
    cnfEval σ Φ = true ↔ energy Φ σ = 0 := by
  induction Φ with
  | nil =>
      simp [cnfEval, energy]
  | cons C Φ ih =>
      classical
      -- 对当前子句的布尔值分类
      cases hC : clauseEval σ C <;>
        simp [cnfEval, energy, hC, ih]

/-- 满足 ↔ 能量为 0（真正证明版） -/
lemma sat_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ energy Φ σ = 0 := by
  simpa [satSet] using (cnfEval_true_iff_energy_zero (Φ := Φ) (σ := σ))


/-! ### 3. 配置图（汉明距离 1） -/

/-- 汉明距离 1 的邻接关系 -/
def neighbor {n : Nat} (σ τ : Assignment n) : Prop :=
  (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card = 1

/-- 赋值空间上的简单图：边 = 汉明邻居 -/
def ConfigGraph (n : Nat) : SimpleGraph (Assignment n) where
  Adj σ τ := neighbor σ τ
  symm := by
    intro σ τ h
    dsimp [neighbor] at h ⊢
    have hset :
      (Finset.univ.filter fun i : Fin n => σ i ≠ τ i)
        =
      (Finset.univ.filter fun i : Fin n => τ i ≠ σ i) := by
      apply Finset.ext
      intro i
      simp [ne_comm]
    simpa [hset] using h
  loopless := by
    classical
    intro σ h
    dsimp [neighbor] at h
    have h0 :
      (Finset.univ.filter fun i : Fin n => σ i ≠ σ i).card = 0 := by
      simp
    have : 0 = 1 := by
      simpa [h0] using h
    exact Nat.zero_ne_one this


/-! ### 4. 抽象算法模型 & 轨迹 ψ -/

/-- 抽象算法模型：状态类型 + init + step + halting -/
structure AlgorithmModel (n : Nat) where
  StateType : Type
  init     : CNF n → StateType
  step     : CNF n → StateType → StateType
  halting  : CNF n → StateType → Prop

/-- 算法在公式 Φ 上的一条有限轨迹 ψ -/
structure ComputationPath {n : Nat} (A : AlgorithmModel n) (Φ : CNF n) where
  T      : Nat
  states : Fin (T+1) → A.StateType
  h_init :
    states ⟨0, Nat.succ_pos _⟩ = A.init Φ
  h_step :
    ∀ t : Fin T,
      states ⟨t.1.succ, Nat.succ_lt_succ t.2⟩
        = A.step Φ (states ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self _)⟩)
  h_halt :
    A.halting Φ (states ⟨T, Nat.lt_succ_self _⟩)


/-! ### 5. 抽象结构密度 λ 与作用量 A[ψ]（Nat 版本） -/

/-- 抽象的结构密度（λ），后面你可以换成 λₖ / 压缩长度。  
    这里先给一个常数 0 的占位。 -/
noncomputable
def structuralDensity {n : Nat} (A : AlgorithmModel n) :
    A.StateType → Nat :=
  fun _ => 0

/-- 结构作用量：A[ψ] = ∑ λ(s_t) （Nat 版本） -/
noncomputable
def action {n : Nat} {A : AlgorithmModel n} {Φ : CNF n}
    (ψ : ComputationPath A Φ) : Nat :=
  ∑ t : Fin (ψ.T + 1), structuralDensity A (ψ.states t)

/-- 时间步数：T -/
def time {n : Nat} {A : AlgorithmModel n} {Φ : CNF n}
    (ψ : ComputationPath A Φ) : Nat :=
  ψ.T


/-! ### 6. 能量子水平集 & 能量障碍（占位） -/

/-- 能量 ≤ k 的子水平集 -/
def sublevel {n : Nat} (Φ : CNF n) (k : Nat) : Set (Assignment n) :=
  { σ | energy Φ σ ≤ k }

/-- 能量障碍（占位版本）：真正版本会用路径 infimum 定义 -/
def energyBarrier {n : Nat} (_Φ : CNF n)
    (_S₀ : Set (Assignment n)) : Nat :=
  0


/-! ### 7. DPLL 状态与模型 -/

/-- DPLL 状态骨架 -/
structure DPLLState (n : Nat) where
  assign    : Assignment n
  undecided : Finset (Fin n)
  decisions : List (Fin n × Bool)
  formula   : CNF n
  conflict  : Bool

/-- DPLL 状态的能量 -/
def DPLLState.energy {n : Nat} (s : DPLLState n) : Nat :=
  StructuralAction.energy s.formula s.assign

/-- 当前赋值满足公式？ -/
def DPLLState.isSatisfied {n : Nat} (s : DPLLState n) : Prop :=
  cnfEval s.assign s.formula = true

/-- 当前赋值产生语义冲突？ -/
def DPLLState.hasConflict {n : Nat} (s : DPLLState n) : Prop :=
  cnfEval s.assign s.formula = false

/-- 所有变量都已决定？ -/
def DPLLState.isComplete {n : Nat} (s : DPLLState n) : Prop :=
  s.undecided = ∅

/-- DPLL 终止状态：要么 SAT，要么 complete+conflict -/
def DPLLState.isTerminal {n : Nat} (s : DPLLState n) : Prop :=
  s.isSatisfied ∨ (s.hasConflict ∧ s.isComplete)

namespace DPLL

open Classical

/-- DPLL 初始状态：所有变量未决定，赋值全 false -/
def initState {n : Nat} (Φ : CNF n) : DPLLState n :=
  { assign    := fun _ => false
  , undecided := Finset.univ
  , decisions := []
  , formula   := Φ
  , conflict  := false }

/-- 在状态 s 下评价子句是否为真（语义封装）。 -/
def clauseTrue {n : Nat} (s : DPLLState n) (C : Clause n) : Bool :=
  clauseEval s.assign C

/-- 在状态 s 下评价整个公式是否为真（语义封装）。 -/
def formulaTrue {n : Nat} (s : DPLLState n) : Bool :=
  cnfEval s.assign s.formula

/-- 当前状态中，变量 i 是否尚未决定？（命题版本） -/
def isUndecided {n : Nat} (s : DPLLState n) (i : Fin n) : Prop :=
  i ∈ s.undecided

/-- 更新赋值：把变量 i 设为 b，其他变量保持不变。 -/
def updateAssign {n : Nat} (s : DPLLState n) (i : Fin n) (b : Bool) :
    Assignment n :=
  fun j => if h : j = i then b else s.assign j

/--
一个非常简化的“单位传播/决策”原语：

- 在当前公式中，取第一个子句 C；
- 在 C 的三个字面中，找第一项变量尚未决定的字面 ℓ；
- 若找到，则返回 `(ℓ.var, !ℓ.neg)`，表示为了满足该字面，应将该变量赋为此布尔值；
- 若找不到（比如三个变量都已决定），返回 none。

> 注意：这不是完整、严格意义上的 unit propagation，仅作为骨架示例。
-/
noncomputable
def findUnitLiteral {n : Nat} (s : DPLLState n) : Option (Fin n × Bool) :=
  match s.formula with
  | []      => none
  | C :: _  =>
      let ℓ0 := C ⟨0, by decide⟩
      let ℓ1 := C ⟨1, by decide⟩
      let ℓ2 := C ⟨2, by decide⟩
      let mkVal (ℓ : Literal n) : Bool := !ℓ.neg
      if h0 : isUndecided s ℓ0.var then
        some (ℓ0.var, mkVal ℓ0)
      else if h1 : isUndecided s ℓ1.var then
        some (ℓ1.var, mkVal ℓ1)
      else if h2 : isUndecided s ℓ2.var then
        some (ℓ2.var, mkVal ℓ2)
      else
        none

/--
对状态 s 做一次“传播/决策”步：

- 若 `findUnitLiteral s = some (i, b)`：
  - 把变量 i 赋值为 b；
  - 从 undecided 中移除 i；
  - 把 (i, b) 记入 decisions；
  - 公式 formula 与 conflict 标志暂时保持不变（未来可以扩展为真正的冲突检测）。
- 若找不到可传播的字面，则保持状态不变。
-/
noncomputable
def unitPropOnce {n : Nat} (s : DPLLState n) : DPLLState n :=
  match findUnitLiteral s with
  | none => s
  | some (i, b) =>
      { assign    := updateAssign s i b
      , undecided := s.undecided.erase i
      , decisions := (i, b) :: s.decisions
      , formula   := s.formula
      , conflict  := s.conflict }

/-- DPLL 单步转移：目前实现为一轮简化版的“单位传播/决策”。 -/
noncomputable
def step {n : Nat} (_Φ : CNF n) (s : DPLLState n) : DPLLState n :=
  unitPropOnce s

/-- DPLL 停机条件 -/
def halting {n : Nat} (_Φ : CNF n) (s : DPLLState n) : Prop :=
  DPLLState.isTerminal s

end DPLL

/-- 把 DPLL 包装成 AlgorithmModel -/
noncomputable
def DPLLModel (n : Nat) : AlgorithmModel n :=
{ StateType := DPLLState n
, init     := fun Φ => DPLL.initState Φ
, step     := fun Φ s => DPLL.step Φ s
, halting  := fun Φ s => DPLL.halting Φ s }


/-! ### 8. CDCL 状态与模型 -/

/-- CDCL 状态骨架 -/
structure CDCLState (n : Nat) where
  assign      : Assignment n
  trail       : List (Fin n × Bool)
  decisionLvl : Nat
  formula     : CNF n
  learnt      : List (Clause n)
  conflicts   : Nat
  unsat       : Bool

/-- CDCL 状态能量 -/
def CDCLState.energy {n : Nat} (s : CDCLState n) : Nat :=
  StructuralAction.energy s.formula s.assign

/-- 当前赋值满足原公式？ -/
def CDCLState.isSatisfied {n : Nat} (s : CDCLState n) : Prop :=
  cnfEval s.assign s.formula = true

/-- 当前赋值语义冲突？ -/
def CDCLState.hasConflict {n : Nat} (s : CDCLState n) : Prop :=
  cnfEval s.assign s.formula = false

/-- SAT 停机：满足且未标记 unsat -/
def CDCLState.isSatTerminal {n : Nat} (s : CDCLState n) : Prop :=
  s.isSatisfied ∧ ¬ s.unsat

/-- UNSAT 停机：全局 unsat 标志为真 -/
def CDCLState.isUnsatTerminal {n : Nat} (s : CDCLState n) : Prop :=
  s.unsat

/-- CDCL 停机条件：SAT 或 UNSAT -/
def CDCLState.isTerminal {n : Nat} (s : CDCLState n) : Prop :=
  s.isSatTerminal ∨ s.isUnsatTerminal

/-- CDCL 初始状态骨架 -/
def CDCL.initState {n : Nat} (Φ : CNF n) : CDCLState n :=
  { assign      := fun _ => false
  , trail       := []
  , decisionLvl := 0
  , formula     := Φ
  , learnt      := []
  , conflicts   := 0
  , unsat       := false }

/-- CDCL 单步转移（目前占位实现：恒等） -/
def CDCL.step {n : Nat} (_Φ : CNF n) (s : CDCLState n) : CDCLState n :=
  s

/-- CDCL 停机条件 -/
def CDCL.halting {n : Nat} (_Φ : CNF n) (s : CDCLState n) : Prop :=
  CDCLState.isTerminal s

/-- 把 CDCL 包装成 AlgorithmModel -/
def CDCLModel (n : Nat) : AlgorithmModel n :=
{ StateType := CDCLState n
, init     := fun Φ => CDCL.initState Φ
, step     := fun Φ s => CDCL.step Φ s
, halting  := fun Φ s => CDCL.halting Φ s }


/-! ### 9. 给 DPLL / CDCL 一个“能量型”结构密度示例（Nat） -/

/-- DPLL：结构密度 = 能量（示例版） -/
noncomputable
def dpllStructuralDensity {n : Nat} (s : DPLLState n) : Nat :=
  s.energy

/-- CDCL：结构密度 = 能量（示例版） -/
noncomputable
def cdclStructuralDensity {n : Nat} (s : CDCLState n) : Nat :=
  s.energy


/-! ### 10. 把“满足”与“能量为 0”在状态层面连起来 -/

/-- 对 DPLL 状态：`isSatisfied` 等价于能量为 0。 -/
lemma DPLLState.isSatisfied_iff_energy_zero {n : Nat} (s : DPLLState n) :
    DPLLState.isSatisfied s ↔ DPLLState.energy s = 0 := by
  have h := sat_iff_energy_zero (Φ := s.formula) (σ := s.assign)
  simpa [DPLLState.isSatisfied, DPLLState.energy, satSet] using h

/-- 对 CDCL 状态：`isSatisfied` 等价于能量为 0。 -/
lemma CDCLState.isSatisfied_iff_energy_zero {n : Nat} (s : CDCLState n) :
    CDCLState.isSatisfied s ↔ CDCLState.energy s = 0 := by
  have h := sat_iff_energy_zero (Φ := s.formula) (σ := s.assign)
  simpa [CDCLState.isSatisfied, CDCLState.energy, satSet] using h


/-! ### 11. 方便记号：DPLLPath / CDCLPath -/

/-- DPLL 在公式 Φ 上的一条计算轨迹 -/
abbrev DPLLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (DPLLModel n) Φ

/-- CDCL 在公式 Φ 上的一条计算轨迹 -/
abbrev CDCLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (CDCLModel n) Φ


/-! ### 12. 一个 n = 1 的玩具 3-SAT 例子 -/

/-- 单变量的“正字面”子句：实际上就是 (x₀)。 -/
def exampleClause1 : Clause 1 :=
  fun _ => { var := ⟨0, by decide⟩, neg := false }

/-- 只包含一个子句 (x₀) 的 CNF：Φ(x) = (x₀)。 -/
def exampleCNF1 : CNF 1 :=
  [exampleClause1]

/-- 对 exampleCNF1 的 DPLL 初始状态 -/
def exampleDPLLInit : DPLLState 1 :=
  DPLL.initState exampleCNF1

/-- 在 exampleCNF1 上运行 DPLL 一步后的状态 -/
noncomputable
def exampleDPLLNext : DPLLState 1 :=
  DPLL.step exampleCNF1 exampleDPLLInit

/-- 对 exampleCNF1 的 CDCL 初始状态 -/
def exampleCDCLInit : CDCLState 1 :=
  CDCL.initState exampleCNF1

/-- 在 exampleCNF1 上运行 CDCL 一步后的状态 -/
def exampleCDCLNext : CDCLState 1 :=
  CDCL.step exampleCNF1 exampleCDCLInit


/-! ------------------------------------------------------------
### 13. 抽象离散作用量上界（Nat 版本）
------------------------------------------------------------ -/

section NatActionUpper

open Finset

/-- 离散结构作用量（自然数版本）：
    给定一个“密度”函数 `density : A.StateType → ℕ`，
    对一条路径 ψ 求和：A_nat[ψ] = ∑_{t=0}^T density(s_t)。 -/
def pathActionNat
    {n : ℕ} (A : AlgorithmModel n) (Φ : CNF n)
    (density : A.StateType → ℕ)
    (ψ : ComputationPath A Φ) : ℕ :=
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => density (ψ.states t))

/-- 抽象的“每步密度在非终止步上至少为 1 ⇒ 作用量下界时间步数”的定理。

设有算法模型 A、公式 Φ、一条轨迹 ψ 以及密度函数 density。
若在 ψ 的前 T 步（也就是索引 `t.val < ψ.T` 的那些状态）上，我们都有
`density (ψ.states t) ≥ 1`，则总时间步数 `ψ.T` 受到作用量的下界控制：

`ψ.T ≤ pathActionNat A Φ density ψ`.

这个引理是把“时间下界”搬运到“作用量下界”的关键桥梁。

> 当前版本仅给出精确的形式化接口，证明留作后续工作。
-/
lemma pathActionNat_ge_time
    {n : ℕ} (A : AlgorithmModel n) (Φ : CNF n)
    (density : A.StateType → ℕ)
    (ψ : ComputationPath A Φ)
    (hPos : ∀ t : Fin (ψ.T + 1),
      t.1 < ψ.T → 1 ≤ density (ψ.states t)) :
    ψ.T ≤ pathActionNat A Φ density ψ := by
  classical
  /-
  思路（将来可用于填充证明）：

  1. 记 `k := ψ.T`，并考虑函数
       f : Fin (k+1) → ℕ := fun t => density (ψ.states t)

  2. 在 Fin (k+1) 上，对所有满足 t.val < k 的索引，假设有：
       1 ≤ f t
     这是由 hPos 直接给出的。

  3. 证明一个纯组合引理：
       lemma sum_fin_ge_of_prefix_ge_one
         (k : ℕ) (f : Fin (k+1) → ℕ)
         (h : ∀ t, t.val < k → 1 ≤ f t) :
         k ≤ ∑ t, f t

     再把它套用到当前的 f 即可得到结论。

  4. 这个纯组合引理可以对 k 做归纳，用
       Fin.sum_univ_succ
     把 ∑ over Fin (k+2) 拆成 f 0 加上 ∑ over Fin (k+1) (with succ 索引)，
     再利用归纳假设和 hPos 对应的 1 ≤ f t。
  -/
  sorry

/-- 抽象的“每步能量有界 + 时间多项式有界 ⇒ 作用量多项式有界”定理（自然数版本）。 -/
lemma pathActionNat_polyUpper
    {n : ℕ} (A : AlgorithmModel n)
    (density : A.StateType → ℕ) (C : ℕ)
    (hC : ∀ (Φ : CNF n) (ψ : ComputationPath A Φ) (t : Fin (ψ.T + 1)),
      density (ψ.states t) ≤ C)
    (P : ℕ → ℕ)
    (hP : ∀ (Φ : CNF n) (ψ : ComputationPath A Φ), ψ.T ≤ P n) :
    ∀ (Φ : CNF n) (ψ : ComputationPath A Φ),
      pathActionNat A Φ density ψ ≤ (P n + 1) * C := by
  intro Φ ψ
  classical
  -- 每一步都有 density(s_t) ≤ C
  have h_each : ∀ t : Fin (ψ.T + 1), density (ψ.states t) ≤ C :=
    fun t => hC Φ ψ t

  /- ∑ density ≤ ∑ 常数 C -/
  have h_sum_le' :
    (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun t => density (ψ.states t))
      ≤
    (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun _ => C) := by
    refine Finset.sum_le_sum ?h
    intro t ht
    exact h_each t

  /- 常数和：∑_t C = (T+1) * C -/
  have h_sum_const :
    (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => C)
      =
    (ψ.T + 1) * C := by
    -- 先用 sum_const_nat 得到 card * C
    have h0 :
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => C)
        =
      (Finset.univ : Finset (Fin (ψ.T + 1))).card * C := by
      simpa using
        (Finset.sum_const_nat
          (s := (Finset.univ : Finset (Fin (ψ.T + 1))))
          (b := C))
    -- 再用 card_univ = ψ.T + 1
    have h_card :
      (Finset.univ : Finset (Fin (ψ.T + 1))).card = ψ.T + 1 := by
      simpa [Finset.card_univ, Fintype.card_fin]
    simpa [h_card] using h0

  -- 时间上界 ψ.T ≤ P n ⇒ ψ.T + 1 ≤ P n + 1
  have hT : ψ.T + 1 ≤ P n + 1 :=
    Nat.succ_le_succ (hP Φ ψ)

  have hT_mul : (ψ.T + 1) * C ≤ (P n + 1) * C :=
    Nat.mul_le_mul_right _ hT

  /- 最终 calc 链 -/
  calc
    pathActionNat A Φ density ψ
        = (Finset.univ : Finset (Fin (ψ.T + 1))).sum
            (fun t => density (ψ.states t)) := by rfl
    _ ≤ (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => C) := h_sum_le'
    _ = (ψ.T + 1) * C := h_sum_const
    _ ≤ (P n + 1) * C := hT_mul

/-- 通用版：给定任意密度函数，DPLL 的结构作用量。 -/
noncomputable
def dpllActionWith {n : Nat} (Φ : CNF n)
    (density : DPLLState n → Nat)
    (ψ : DPLLPath n Φ) : Nat :=
  pathActionNat (A := DPLLModel n) Φ density ψ

/-- 通用版：给定任意密度函数，CDCL 的结构作用量。 -/
noncomputable
def cdclActionWith {n : Nat} (Φ : CNF n)
    (density : CDCLState n → Nat)
    (ψ : CDCLPath n Φ) : Nat :=
  pathActionNat (A := CDCLModel n) Φ density ψ

/-- DPLL 的结构作用量（Nat）：用能量作为密度。 -/
noncomputable
def dpllAction {n : Nat} (Φ : CNF n)
    (ψ : DPLLPath n Φ) : Nat :=
  dpllActionWith Φ (fun s => dpllStructuralDensity s) ψ

/-- CDCL 的结构作用量（Nat）：用能量作为密度。 -/
noncomputable
def cdclAction {n : Nat} (Φ : CNF n)
    (ψ : CDCLPath n Φ) : Nat :=
  cdclActionWith Φ (fun s => cdclStructuralDensity s) ψ

/-- DPLL 版的多项式上界：  
    如果每步结构密度有界且时间 T 多项式有界，则 dpllAction 也多项式有界。 -/
lemma dpllAction_polyUpper
    {n : ℕ} (C : ℕ) (P : ℕ → ℕ)
    (hC : ∀ (Φ : CNF n) (ψ : DPLLPath n Φ) (t : Fin (ψ.T + 1)),
      dpllStructuralDensity (ψ.states t) ≤ C)
    (hP : ∀ (Φ : CNF n) (ψ : DPLLPath n Φ), ψ.T ≤ P n) :
    ∀ (Φ : CNF n) (ψ : DPLLPath n Φ),
      dpllAction Φ ψ ≤ (P n + 1) * C := by
  intro Φ ψ
  have h :=
    pathActionNat_polyUpper
      (A := DPLLModel n)
      (density := fun s => dpllStructuralDensity s)
      C
      (by
        intro Φ' ψ' t
        exact hC Φ' ψ' t)
      P
      (by
        intro Φ' ψ'
        exact hP Φ' ψ')
      Φ ψ
  simpa [dpllAction, dpllActionWith] using h

/-- CDCL 版的多项式上界：  
    如果每步结构密度有界且时间 T 多项式有界，则 cdclAction 也多项式有界。 -/
lemma cdclAction_polyUpper
    {n : ℕ} (C : ℕ) (P : ℕ → ℕ)
    (hC : ∀ (Φ : CNF n) (ψ : CDCLPath n Φ) (t : Fin (ψ.T + 1)),
      cdclStructuralDensity (ψ.states t) ≤ C)
    (hP : ∀ (Φ : CNF n) (ψ : CDCLPath n Φ), ψ.T ≤ P n) :
    ∀ (Φ : CNF n) (ψ : CDCLPath n Φ),
      cdclAction Φ ψ ≤ (P n + 1) * C := by
  intro Φ ψ
  have h :=
    pathActionNat_polyUpper
      (A := CDCLModel n)
      (density := fun s => cdclStructuralDensity s)
      C
      (by
        intro Φ' ψ' t
        exact hC Φ' ψ' t)
      P
      (by
        intro Φ' ψ'
        exact hP Φ' ψ')
      Φ ψ
  simpa [cdclAction, cdclActionWith] using h

end NatActionUpper


/-! ------------------------------------------------------------
### 14. 玩具版 “指数下界 + 多项式上界 ⇒ 矛盾” 定理 （完全无公理版）
使用 ℕ 上的 `2^n` 和 `n^2`。
------------------------------------------------------------ -/

/-- 玩具版：一个“结构作用量”序列 A : ℕ → ℕ -/
def ActionSeq := ℕ → ℕ

/-- 多项式上界：这里我们固定为 P(n) = n^2 作为玩具。 -/
def PolyUpper_n2 (A : ActionSeq) : Prop :=
  ∀ n : ℕ, A n ≤ n^2

/-- 指数下界：这里我们用 2^n 代替 “exp(n)”。 -/
def ExpLower_2pow (A : ActionSeq) : Prop :=
  ∀ n : ℕ, 2^n ≤ A n

/--
主玩具定理（完全形式化，无公理）：

> 如果同一个 A : ℕ → ℕ 同时满足
>  1. ∀n, A n ≥ 2^n
>  2. ∀n, A n ≤ n^2
> 那么矛盾。
-/
theorem toy_hardFamily_contradiction
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_n2 A) : False := by
  -- 在 n = 10 处抽象出不等式链：
  have h₁ : (2 : ℕ)^10 ≤ A 10 := hLower 10
  have h₂ : A 10 ≤ 10^2 := hUpper 10
  have h_le : (2 : ℕ)^10 ≤ 10^2 := le_trans h₁ h₂

  -- 但实际上 10^2 < 2^10，这是一个可计算事实。
  have h_lt : 10^2 < (2 : ℕ)^10 := by
    norm_num  -- 100 < 1024

  -- 合并得到 2^10 < 2^10，矛盾。
  have h_absurd : (2 : ℕ)^10 < (2 : ℕ)^10 :=
    lt_of_le_of_lt h_le h_lt
  exact lt_irrefl _ h_absurd


/-! ------------------------------------------------------------
### 15. “抽象 PolyUpper_general + ExpLower_2pow ⇒ 矛盾” schema
（条件版，不再引入额外公理）
------------------------------------------------------------ -/

/-- 抽象版本的“多项式上界”：
    这里为了复用 toy 定理，仍然选用 n² 作为统一的上界形状。 -/
def PolyUpper_general (A : ActionSeq) : Prop :=
  ∀ n : ℕ, A n ≤ n^2

/-- 一般形式：ExpLower_2pow A 与 PolyUpper_general A 不能同时成立。 -/
theorem expLower_2pow_not_PolyUpper_general
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_general A) : False := by
  exact toy_hardFamily_contradiction A hLower (by intro n; exact hUpper n)

/-- 语义化名称版本：
    “如果某个作用量族 A 同时满足指数下界和多项式上界，就矛盾。” -/
theorem no_polyTime_on_family
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_general A) :
    False :=
  expLower_2pow_not_PolyUpper_general A hLower hUpper

end StructuralAction




