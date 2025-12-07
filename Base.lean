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

/-- 这里暂时用 axiom：满足 <-> 能量为 0。  
    将来你可以用真正的归纳证明替掉。 -/
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
    intro σ h
    dsimp [neighbor] at h
    have hEmpty :
      (Finset.univ.filter fun i : Fin n => σ i ≠ σ i)
      = (∅ : Finset (Fin n)) := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      simp at hi
    have hCard :
      (Finset.univ.filter fun i : Fin n => σ i ≠ σ i).card = 0 := by
      simpa [hEmpty] using (Finset.card_empty : (∅ : Finset (Fin n)).card = 0)
    have : 0 = 1 := by
      simpa [hCard] using h
    exact zero_ne_one this


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
        = A.step Φ (states t)
  h_halt :
    A.halting Φ (states ⟨T, Nat.lt_succ_self _⟩)


/-! ### 5. 结构密度 λ 与作用量 A[ψ] -/

/-- 抽象的结构密度（λ），后面你可以换成 λₖ / 压缩长度 -/
noncomputable
def structuralDensity {n : Nat} (A : AlgorithmModel n) :
    A.StateType → Real :=
  fun _ => 0

/-- 结构作用量：A[ψ] = ∑ λ(s_t) -/
noncomputable
def action {n : Nat} {A : AlgorithmModel n} {Φ : CNF n}
    (ψ : ComputationPath A Φ) : Real :=
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


/-! ### 7. 结构作用量与时间的 schema 定理（axiom 占位） -/

/-- 假设：存在多项式界 P，使得 A[ψ] ≤ P(n) * time(ψ) -/
axiom action_bounds_time
  {n : Nat} (A : AlgorithmModel n) :
  ∃ (P : Nat → Nat),
    ∀ (Φ : CNF n) (ψ : ComputationPath A Φ),
      action ψ ≤ (P n : Real) * (time ψ)

/-- 假设：对某些公式族，所有 ψ 都有指数级结构作用量下界 -/
axiom exponential_action_lower_bound
  {n : Nat} (A : AlgorithmModel n) (Φ : CNF n) :
  ∃ (γ : Real), γ > 0 ∧
    ∀ (ψ : ComputationPath A Φ),
      action ψ ≥ Real.exp (γ * (n : Real))

/-- 示意性的结论占位：真正版本可以改成时间下界不等式 -/
theorem exponential_time_lower_bound_schematic
  {n : Nat} (_A : AlgorithmModel n) (_Φ : CNF n) :
  True := by
  trivial


/-! ### 8. DPLL 状态与模型 -/

/-- DPLL 状态骨架 -/
structure DPLLState (n : Nat) where
  assign    : Assignment n
  undecided : Finset (Fin n)
  decisions : List (Fin n × Bool)
  formula   : CNF n
  conflict  : Bool

/-- DPLL 状态的能量 -/
def DPLLState.energy {n : Nat} (s : DPLLState n) : Nat :=
  energy s.formula s.assign

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

/-- DPLL 单步转移（占位实现） -/
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


/-! ### 9. CDCL 状态与模型 -/

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
  energy s.formula s.assign

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

/-- CDCL 单步转移（占位实现） -/
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


/-! ### 10. 给 DPLL / CDCL 一个“能量型”结构密度示例 -/

/-- CDCL：结构密度 = 能量（示例版） -/
noncomputable
def cdclStructuralDensity {n : Nat} :
    (CDCLModel n).StateType → Real :=
  fun s => (CDCLState.energy s : Real)

/-- DPLL：结构密度 = 能量（示例版） -/
noncomputable
def dpllStructuralDensity {n : Nat} :
    (DPLLModel n).StateType → Real :=
  fun s => (DPLLState.energy s : Real)

end StructuralAction
namespace StructuralAction

/-! ## 下一步 1：给 DPLL.step 加一些基础引理 -/

/-- DPLL 的一步不会改动 formula（公式本身保持不变）。 -/
lemma DPLL.step_preserves_formula {n : Nat} (Φ : CNF n) (s : DPLLState n) :
    (DPLL.step Φ s).formula = s.formula := by
  -- 展开定义
  unfold DPLL.step
  by_cases hterm : DPLLState.isTerminal s
  · -- 已终止：step = id
    simp [hterm]
  · -- 未终止：分情况讨论 nextVar
    simp [hterm]

/-- DPLL 的一步不会增加 undecided 集合（要么不变，要么删掉一个变量）。 -/
lemma DPLL.step_undecided_subset {n : Nat} (Φ : CNF n) (s : DPLLState n) :
    (DPLL.step Φ s).undecided ⊆ s.undecided := by
  -- 展开 step
  unfold DPLL.step
  by_cases hterm : DPLLState.isTerminal s
  · -- 已终止：undecided 不变
    intro x hx
    simpa [hterm] using hx
  · -- 未终止：看有没有 nextVar
    simp [hterm] -- 得到 match 结构
    -- 两种情况：none / some v
    intro x hx
    cases hnv : DPLL.nextVar s with
    | none =>
        -- nextVar = none：step 只是改 conflict，undecided 不变
        simp [DPLL.nextVar, hnv] at hx ⊢
        exact hx
    | some v =>
        -- nextVar = some v：undecided 被 erase 掉 v
        simp [DPLL.nextVar, hnv] at hx ⊢
        -- hx : x ∈ s.undecided.erase v
        -- 利用 Finset.mem_erase 拿到 x ∈ s.undecided
        rcases Finset.mem_erase.mp hx with ⟨hx_ne, hx_mem⟩
        exact hx_mem

/-! ## 下一步 2：专门给 DPLL 定义结构作用量 dpllAction -/

/--（前面已经定义过）
    dpllStructuralDensity : DPLL 状态的结构密度，这里用能量作为示例。
    noncomputable
    def dpllStructuralDensity {n : Nat} :
        (DPLLModel n).StateType → Real :=
      fun s => (DPLLState.energy s : Real)
-/

/-- 针对 DPLLModel 的专用结构作用量：
    A_DPLL[ψ] = ∑ λ_DPLL(s_t)，其中 λ_DPLL = 能量型结构密度。 -/
noncomputable
def dpllAction {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (DPLLModel n) Φ) : Real :=
  ∑ t : Fin (ψ.T + 1), dpllStructuralDensity (ψ.states t)

/-- dpllAction 总是非负（因为每一步的能量 ≥ 0）。 -/
lemma dpllAction_nonneg {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (DPLLModel n) Φ) :
    0 ≤ dpllAction Φ ψ := by
  unfold dpllAction
  -- 每一项都是 Nat 转为 Real，因此非负
  have hterm_nonneg :
      ∀ t : Fin (ψ.T + 1),
        0 ≤ dpllStructuralDensity (ψ.states t) := by
    intro t
    -- dpllStructuralDensity = energy (Nat) cast 为 Real
    unfold dpllStructuralDensity
    simp
  -- 用 sum_nonneg
  exact Finset.sum_nonneg (fun t _ => hterm_nonneg t)

end StructuralAction
namespace StructuralAction

/-! ## 继续加强 DPLL：基础行为引理 -/

/-- 若状态已终止，则 DPLL.step 是恒等映射。 -/
lemma DPLL.step_terminal_id {n : Nat} (Φ : CNF n)
    {s : DPLLState n} (h : DPLLState.isTerminal s) :
    DPLL.step Φ s = s := by
  unfold DPLL.step
  simp [h]

/-- 若未终止且 `nextVar = none`，则一步 DPLL 会把 conflict 设为 `true`。 -/
lemma DPLL.step_conflict_when_no_nextVar {n : Nat} (Φ : CNF n)
    (s : DPLLState n)
    (h_not_term : ¬ DPLLState.isTerminal s)
    (h_none : DPLL.nextVar s = none) :
    (DPLL.step Φ s).conflict = true := by
  unfold DPLL.step
  simp [h_not_term, h_none]

/-- 若未终止且 `nextVar = some v`，则 v 不再出现在 undecided 里。 -/
lemma DPLL.step_removes_chosen_var {n : Nat} (Φ : CNF n)
    (s : DPLLState n)
    (h_not_term : ¬ DPLLState.isTerminal s)
    {v : Fin n} (h_some : DPLL.nextVar s = some v) :
    v ∉ (DPLL.step Φ s).undecided := by
  unfold DPLL.step
  simp [h_not_term, h_some]



/-! ## 给 CDCL 定义专用结构作用量 cdclAction -/

/-- 针对 CDCLModel 的专用结构作用量：
    A_CDCL[ψ] = ∑ λ_CDCL(s_t)，其中 λ_CDCL = 能量型结构密度。 -/
noncomputable
def cdclAction {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (CDCLModel n) Φ) : Real :=
  ∑ t : Fin (ψ.T + 1), cdclStructuralDensity (ψ.states t)

/-- cdclAction 总是非负（每一步的能量 ≥ 0）。 -/
lemma cdclAction_nonneg {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (CDCLModel n) Φ) :
    0 ≤ cdclAction Φ ψ := by
  unfold cdclAction
  have hterm_nonneg :
      ∀ t : Fin (ψ.T + 1),
        0 ≤ cdclStructuralDensity (ψ.states t) := by
    intro t
    unfold cdclStructuralDensity
    simp   -- Nat → Real，显然 ≥ 0
  exact Finset.sum_nonneg (by
    intro t ht
    exact hterm_nonneg t)
namespace StructuralAction

/-! ## 11. 方便记号：DPLLPath / CDCLPath -/

/-- DPLL 在公式 Φ 上的一条计算轨迹 -/
abbrev DPLLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (DPLLModel n) Φ

/-- CDCL 在公式 Φ 上的一条计算轨迹 -/
abbrev CDCLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (CDCLModel n) Φ


/-! ## 12. 一个 n = 1 的玩具 3-SAT 例子 -/

/--
单变量的“正字面”子句：实际上就是 (x₀)。
这里由于是 3-SAT 的骨架，我们用 3 个相同的字面填满子句位。
-/
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

end StructuralAction

end StructuralAction
