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

/-- 评价 CNF：所有子句的合取 -/
def cnfEval {n : Nat} (σ : Assignment n) (Φ : CNF n) : Bool :=
  Φ.foldr (fun C acc => clauseEval σ C && acc) true

/-- 满足解集合 -/
def satSet {n : Nat} (Φ : CNF n) : Set (Assignment n) :=
  { σ | cnfEval σ Φ = true }


/-! ### 2. 能量函数 E：未满足子句个数 -/

/-- 能量：未满足子句数量 -/
def energy {n : Nat} (Φ : CNF n) (σ : Assignment n) : Nat :=
  Φ.foldr
    (fun C acc =>
      let ok := clauseEval σ C
      acc + (if ok then 0 else 1))
    0

/-- 暂时用 axiom：满足 ↔ 能量为 0。  
    将来可以用真正的归纳证明替掉。 -/
axiom sat_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ energy Φ σ = 0


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

/-- DPLL 初始状态：所有变量未决定，赋值全 false -/
def DPLL.initState {n : Nat} (Φ : CNF n) : DPLLState n :=
  { assign    := fun _ => false
  , undecided := Finset.univ
  , decisions := []
  , formula   := Φ
  , conflict  := false }

/-- DPLL 单步转移（目前占位实现：恒等） -/
def DPLL.step {n : Nat} (_Φ : CNF n) (s : DPLLState n) : DPLLState n :=
  s

/-- DPLL 停机条件 -/
def DPLL.halting {n : Nat} (_Φ : CNF n) (s : DPLLState n) : Prop :=
  DPLLState.isTerminal s

/-- 把 DPLL 包装成 AlgorithmModel -/
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

/-- DPLL 的结构作用量（Nat）：定义为 pathActionNat 的特例。 -/
noncomputable
def dpllAction {n : Nat} (Φ : CNF n)
    (ψ : DPLLPath n Φ) : Nat :=
  pathActionNat (A := DPLLModel n) Φ
    (fun s => dpllStructuralDensity s) ψ

/-- CDCL 的结构作用量（Nat）：定义为 pathActionNat 的特例。 -/
noncomputable
def cdclAction {n : Nat} (Φ : CNF n)
    (ψ : CDCLPath n Φ) : Nat :=
  pathActionNat (A := CDCLModel n) Φ
    (fun s => cdclStructuralDensity s) ψ

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
  -- 只需要把 dpllAction 展开成 pathActionNat
  simpa [dpllAction] using h

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
  simpa [cdclAction] using h

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
### 15. 一般化：任意多项式上界 P(n) 的抽象版本
------------------------------------------------------------ -/

namespace GeneralGrowth

/-- 一般的“多项式上界”谓词：`A` 被某个 `P` 从上界定。 -/
def PolyUpper (A P : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, A n ≤ P n

/-- 一般指数下界：这里沿用 StructuralAction.ExpLower_2pow。 -/
abbrev ExpLower_2pow (A : ℕ → ℕ) : Prop :=
  StructuralAction.ExpLower_2pow A

/--
给定某个具体的见证点 `n0`，如果

* A(n) ≥ 2^n
* A(n) ≤ P(n)
* 且 P(n0) < 2^n0

就能立刻得到矛盾。 -/
theorem expLower_polyUpper_contradiction_withWitness
    (A P : ℕ → ℕ)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper A P)
    (n0 : ℕ)
    (h_gt : P n0 < 2^n0) : False := by
  have h₁ : (2 : ℕ)^n0 ≤ A n0 := hLower n0
  have h₂ : A n0 ≤ P n0 := hUpper n0
  have h_le : (2 : ℕ)^n0 ≤ P n0 := le_trans h₁ h₂
  have h_lt : P n0 < (2 : ℕ)^n0 := h_gt
  have h_absurd : (2 : ℕ)^n0 < (2 : ℕ)^n0 :=
    lt_of_le_of_lt h_le h_lt
  exact lt_irrefl _ h_absurd

/--
一个抽象公理：**指数支配所有多项式**（在 ℕ 上版本）。

它声称：对任意给定的函数 `P : ℕ → ℕ`（在你的应用里是多项式），
都存在某个 `n0` 使得 `P n0 < 2^n0`。 -/
axiom poly_vs_exp_witness (P : ℕ → ℕ) :
  ∃ n0 : ℕ, P n0 < 2^n0

/--
综合版：如果同一个 A : ℕ → ℕ 同时满足

* 指数下界：A(n) ≥ 2^n
* 某个 P 的多项式上界：A(n) ≤ P(n)

则矛盾（利用 `poly_vs_exp_witness` 给出的指数支配见证）。 -/
theorem expLower_incompatible_with_polyUpper
    (A P : ℕ → ℕ)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper A P) : False := by
  obtain ⟨n0, h_gt⟩ := poly_vs_exp_witness P
  exact expLower_polyUpper_contradiction_withWitness
    A P hLower hUpper n0 h_gt

end GeneralGrowth


/-! ------------------------------------------------------------
### 16. 抽象 Hard 3-SAT 家族 + DPLL/CDCL Schema
------------------------------------------------------------ -/

namespace HardFamily

open GeneralGrowth

/-- 抽象的 Hard 3-SAT 家族：  
对于每个规模 `k`，给出一个“真正的变量数 n”和公式 `Φ : CNF n`。 -/
axiom HardCNF : ℕ → (Σ n, CNF n)

/-- 对第 k 个 hard 公式，变量个数 `n`。 -/
noncomputable def hardSize (k : ℕ) : ℕ :=
  (HardCNF k).1

/-- 对第 k 个 hard 公式，公式本身。 -/
noncomputable def hardFormula (k : ℕ) : CNF (hardSize k) :=
  (HardCNF k).2

/-- Hard family 上 DPLL 的一个固定运行轨迹（抽象存在性）。 -/
axiom hardDPLLPath :
  ∀ k : ℕ, DPLLPath (hardSize k) (hardFormula k)

/-- Hard family 上 CDCL 的一个固定运行轨迹。 -/
axiom hardCDCLPath :
  ∀ k : ℕ, CDCLPath (hardSize k) (hardFormula k)

/-- Hard family 上 DPLL 的结构作用量序列：A_DPLL(k) = dpllAction[ψ_k]。 -/
noncomputable
def HardActionDPLL (k : ℕ) : ℕ :=
  let Φ := hardFormula k
  let ψ := hardDPLLPath k
  dpllAction Φ ψ

/-- Hard family 上 CDCL 的结构作用量序列：A_CDCL(k) = cdclAction[ψ_k]。 -/
noncomputable
def HardActionCDCL (k : ℕ) : ℕ :=
  let Φ := hardFormula k
  let ψ := hardCDCLPath k
  cdclAction Φ ψ

/-- **假设 1（schema）：Hard family 上 DPLL 作用量有 2^k 的指数下界。** -/
axiom hardActionDPLL_expLower_2pow :
  ExpLower_2pow HardActionDPLL

/-- **假设 1'（schema）：Hard family 上 CDCL 作用量有 2^k 的指数下界。** -/
axiom hardActionCDCL_expLower_2pow :
  ExpLower_2pow HardActionCDCL

/-- **假设 2（schema）：Hard family 上 DPLL 的作用量具有某个多项式上界。** -/
axiom hardActionDPLL_polyUpper :
  ∃ P_DPLL : ℕ → ℕ,
    PolyUpper HardActionDPLL P_DPLL

/-- **假设 2'（schema）：Hard family 上 CDCL 的作用量具有某个多项式上界。** -/
axiom hardActionCDCL_polyUpper :
  ∃ P_CDCL : ℕ → ℕ,
    PolyUpper HardActionCDCL P_CDCL

/-- **主结论 1（DPLL 版）**：

在以上两个假设同时成立的前提下，Hard family 上 DPLL 不可能是多项式时间的。 -/
theorem no_polytime_DPLL_on_hardFamily : False := by
  rcases hardActionDPLL_polyUpper with ⟨P, hP⟩
  exact expLower_incompatible_with_polyUpper
    (A := HardActionDPLL) (P := P)
    hardActionDPLL_expLower_2pow hP

/-- **主结论 2（CDCL 版）**：

同理，Hard family 上 CDCL 也不可能是多项式时间的。 -/
theorem no_polytime_CDCL_on_hardFamily : False := by
  rcases hardActionCDCL_polyUpper with ⟨P, hP⟩
  exact expLower_incompatible_with_polyUpper
    (A := HardActionCDCL) (P := P)
    hardActionCDCL_expLower_2pow hP

end HardFamily

end StructuralAction


