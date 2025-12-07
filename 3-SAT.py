import Mathlib

open scoped BigOperators

namespace StructuralAction

/-! # 1. 3-SAT 基础语法 -/

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


/-! # 2. 能量函数：未满足子句个数 (避免和状态的 `energy` 投影冲突，命名为 `cnfEnergy`) -/

/-- CNF 能量：未满足子句数量 -/
def cnfEnergy {n : Nat} (Φ : CNF n) (σ : Assignment n) : Nat :=
  Φ.foldr
    (fun C acc =>
      let ok := clauseEval σ C
      acc + (if ok then 0 else 1))
    0

/-- 这里暂时用 axiom：满足 ↔ 能量为 0。  
    将来你可以用真正的归纳证明替掉。 -/
axiom sat_iff_cnfEnergy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ cnfEnergy Φ σ = 0


/-! # 3. 配置图（汉明距离 1） -/

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
      -- 这里用老名字 eq_empty_iff_forall_not_mem，兼容旧版 mathlib
      apply Finset.eq_empty_iff_forall_not_mem.2
      intro i hi
      simp at hi
    have hCard :
      (Finset.univ.filter fun i : Fin n => σ i ≠ σ i).card = 0 := by
      simpa [hEmpty] using (Finset.card_empty : (∅ : Finset (Fin n)).card = 0)
    have : 0 = 1 := by
      simpa [hCard] using h
    exact zero_ne_one this


/-! # 4. 抽象算法模型 & 轨迹 ψ -/

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
      -- 把 `Fin T` 安全嵌入到 `Fin (T+1)` 里
      states ⟨t.1.succ, Nat.succ_lt_succ t.2⟩
        = A.step Φ (states ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self _)⟩)
  h_halt :
    A.halting Φ (states ⟨T, Nat.lt_succ_self _⟩)


/-! # 5. 抽象结构密度 λ 与作用量 A[ψ]（取值在 Nat，避免 Real 问题） -/

/-- 抽象的结构密度（λ），目前简单取 0，将来你可以换成 λₖ / 压缩长度。 -/
def structuralDensity {n : Nat} (A : AlgorithmModel n) :
    A.StateType → Nat :=
  fun _ => 0

/-- 通用结构作用量（Nat 版）：A[ψ] = ∑ λ(s_t) -/
def action {n : Nat} {A : AlgorithmModel n} {Φ : CNF n}
    (ψ : ComputationPath A Φ) : Nat :=
  -- 明确用 Finset.sum，避免 `∑ t in` 语法问题
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => structuralDensity A (ψ.states t))

/-- 时间步数：T -/
def time {n : Nat} {A : AlgorithmModel n} {Φ : CNF n}
    (ψ : ComputationPath A Φ) : Nat :=
  ψ.T


/-! # 6. 能量子水平集 & 能量障碍（占位） -/

/-- 能量 ≤ k 的子水平集中，使用 `cnfEnergy` -/
def sublevel {n : Nat} (Φ : CNF n) (k : Nat) : Set (Assignment n) :=
  { σ | cnfEnergy Φ σ ≤ k }

/-- 能量障碍（占位版本）：真正版本会用路径 infimum 定义 -/
def energyBarrier {n : Nat} (_Φ : CNF n)
    (_S₀ : Set (Assignment n)) : Nat :=
  0


/-! # 7. DPLL 状态与模型 -/

/-- DPLL 状态骨架 -/
structure DPLLState (n : Nat) where
  assign    : Assignment n
  undecided : Finset (Fin n)
  decisions : List (Fin n × Bool)
  formula   : CNF n
  conflict  : Bool

/-- DPLL 状态的能量（使用 `cnfEnergy`，避免与全局名冲突） -/
def DPLLState.energy {n : Nat} (s : DPLLState n) : Nat :=
  cnfEnergy s.formula s.assign

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


/-! # 8. CDCL 状态与模型 -/

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
  cnfEnergy s.formula s.assign

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


/-! # 9. DPLL / CDCL 专用结构作用量（能量型 λ，取值在 Nat） -/

/-- DPLL：结构密度 = 能量（Nat 版） -/
def dpllStructuralDensity {n : Nat} :
    DPLLState n → Nat :=
  fun s => s.energy

/-- CDCL：结构密度 = 能量（Nat 版） -/
def cdclStructuralDensity {n : Nat} :
    CDCLState n → Nat :=
  fun s => s.energy

/-- 针对 DPLLModel 的专用结构作用量：
    A_DPLL[ψ] = ∑ λ_DPLL(s_t)，其中 λ_DPLL = 能量型结构密度。 -/
def dpllAction {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (DPLLModel n) Φ) : Nat :=
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => dpllStructuralDensity (ψ.states t))

/-- 针对 CDCLModel 的专用结构作用量：
    A_CDCL[ψ] = ∑ λ_CDCL(s_t)，其中 λ_CDCL = 能量型结构密度。 -/
def cdclAction {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (CDCLModel n) Φ) : Nat :=
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => cdclStructuralDensity (ψ.states t))

/-- dpllAction 总是非负（Nat 中永远 ≥ 0）。 -/
lemma dpllAction_nonneg {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (DPLLModel n) Φ) :
    0 ≤ dpllAction Φ ψ := by
  -- 直接用 Nat 的性质，非负是自动的
  exact Nat.zero_le _

/-- cdclAction 总是非负（Nat 中永远 ≥ 0）。 -/
lemma cdclAction_nonneg {n : Nat} (Φ : CNF n)
    (ψ : ComputationPath (CDCLModel n) Φ) :
    0 ≤ cdclAction Φ ψ := by
  exact Nat.zero_le _


/-! # 10. 把“满足”与“能量为 0”在状态层面连起来 -/

/-- 对 DPLL 状态：`isSatisfied` 等价于能量为 0。 -/
lemma DPLLState.isSatisfied_iff_energy_zero {n : Nat} (s : DPLLState n) :
    DPLLState.isSatisfied s ↔ s.energy = 0 := by
  have h := sat_iff_cnfEnergy_zero (Φ := s.formula) (σ := s.assign)
  -- 直接用 `simpa` 展开定义
  simpa [DPLLState.isSatisfied, DPLLState.energy, satSet] using h

/-- 对 CDCL 状态：`isSatisfied` 等价于能量为 0。 -/
lemma CDCLState.isSatisfied_iff_energy_zero {n : Nat} (s : CDCLState n) :
    CDCLState.isSatisfied s ↔ s.energy = 0 := by
  have h := sat_iff_cnfEnergy_zero (Φ := s.formula) (σ := s.assign)
  simpa [CDCLState.isSatisfied, CDCLState.energy, satSet] using h


/-! # 11. 方便记号：DPLLPath / CDCLPath -/

/-- DPLL 在公式 Φ 上的一条计算轨迹 -/
abbrev DPLLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (DPLLModel n) Φ

/-- CDCL 在公式 Φ 上的一条计算轨迹 -/
abbrev CDCLPath (n : Nat) (Φ : CNF n) :=
  ComputationPath (CDCLModel n) Φ


/-! # 12. 一个 n = 1 的玩具 3-SAT 例子 -/

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


/-! # 13. 抽象层：多项式上界 vs “指数型”下界 (Nat 版 schema) -/

/-- 多项式参数：`C * n^k + C` 这样的简单 upper bound 形式（Nat 版）。 -/
structure PolyParam where
  C : Nat
  k : Nat
  hC_pos : 0 < C

/-- 函数 `f : ℕ → ℕ` “多项式有界”的抽象定义：

`∃ C,k, ∀ n, f n ≤ C * n^k + C`。 -/
def PolyBound (f : Nat → Nat) : Prop :=
  ∃ p : PolyParam, ∀ n : Nat, f n ≤ p.C * n ^ p.k + p.C

/-- `G` 对所有多项式上界函数 `P` 都有最终支配性：

对任意 `P`，如果 `P` 是多项式有界，
则 ∃ N，∀ n ≥ N, P n < G n。 -/
def GrowthDominatesPoly (G : Nat → Nat) : Prop :=
  ∀ (P : Nat → Nat), PolyBound P →
    ∃ N : Nat, ∀ {n : Nat}, n ≥ N → P n < G n

/-- 抽象 schema 定理的 Nat 版：

Hard landscape + correctness ⇒ 存在某个增长函数 `G`，
且 `G` 支配所有多项式；同时，PolyTime + 能量多项式有界
⇒ 结构作用量有多项式上界 `P`。
于是，在足够大的 n 上得到

`G n ≤ actionOn A F n ≤ P n < G n` 的矛盾。 -/
theorem main_schema_contradictionNat
  (SatFamily    : Type)                      -- 公式家族类型
  (AlgorithmFam : Type)                      -- 算法家族类型
  (actionOn     : AlgorithmFam → SatFamily → Nat → Nat)
  (SolvesFamily    : AlgorithmFam → SatFamily → Prop)
  (PolyTimeOnFamily : AlgorithmFam → SatFamily → Prop)
  (EnergyBoundOnFamily : AlgorithmFam → SatFamily → Prop)
  (HardEnergyLandscape  : SatFamily → Prop)
  -- Hard landscape + correctness ⇒ 存在一个 G，对所有多项式 P 有 GrowthDominatesPoly，
  -- 且 G n ≤ actionOn A F n （作用量下界）
  (HardLandscapeLowerBound :
     ∀ {F : SatFamily} {A : AlgorithmFam},
       HardEnergyLandscape F →
       SolvesFamily A F →
       ∃ (G : Nat → Nat),
         GrowthDominatesPoly G ∧
         ∀ n : Nat, G n ≤ actionOn A F n)
  -- PolyTime + 能量多项式有界 ⇒ 存在多项式上界 P，
  -- 对所有 n 有 actionOn A F n ≤ P n
  (ActionPolyUpperBound :
     ∀ {F : SatFamily} {A : AlgorithmFam},
       PolyTimeOnFamily A F →
       EnergyBoundOnFamily A F →
       ∃ (P : Nat → Nat),
         PolyBound P ∧
         ∀ n : Nat, actionOn A F n ≤ P n) :
  -- 结论：在 hard landscape 上，不存在同时满足 Solves + PolyTime + EnergyBound 的算法族。
  ∀ (F : SatFamily) (A : AlgorithmFam),
    HardEnergyLandscape F →
    SolvesFamily A F →
    PolyTimeOnFamily A F →
    EnergyBoundOnFamily A F →
    False := by
  intro F A hHard hSolve hPoly hEnergy
  classical

  -- 1. 从 hard landscape + correctness 得到增长函数 G 与作用量下界
  obtain ⟨G, hG_dom, hG_le_action⟩ :=
    HardLandscapeLowerBound (F := F) (A := A) hHard hSolve

  -- 2. 从 PolyTime + 能量多项式有界得到多项式上界 P
  obtain ⟨P, hPpoly, h_action_le_P⟩ :=
    ActionPolyUpperBound (F := F) (A := A) hPoly hEnergy

  -- 3. 利用 G 对多项式的支配性
  obtain ⟨N, hN⟩ :=
    hG_dom P hPpoly

  -- 4. 在 n = N 处比较：得到 G N ≤ action ≤ P N < G N 的矛盾
  have hDom : P N < G N :=
    hN (n := N) (le_rfl)

  have hUp  : actionOn A F N ≤ P N :=
    h_action_le_P N

  have hLow : G N ≤ actionOn A F N :=
    hG_le_action N

  -- 组合：G N ≤ action ≤ P N < G N
  have : G N < G N :=
    lt_of_le_of_lt (le_trans hLow hUp) hDom

  exact Nat.lt_irrefl _ this

end StructuralAction
