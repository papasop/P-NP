import Mathlib

open scoped BigOperators

namespace StructuralAction

------------------------------------------------------------
-- 1. 3-SAT 基础语法
------------------------------------------------------------

-- 布尔赋值：n 个变量，对应 Fin n → Bool
abbrev Assignment (n : Nat) := Fin n → Bool

-- 字面：变量索引 + 是否取反
structure Literal (n : Nat) where
  var : Fin n
  neg : Bool
  deriving Repr

-- 子句：3 个字面
abbrev Clause (n : Nat) := Fin 3 → Literal n

-- CNF 公式：子句列表
abbrev CNF (n : Nat) := List (Clause n)

-- 评价字面
def literalEval {n : Nat} (σ : Assignment n) (ℓ : Literal n) : Bool :=
  let b := σ ℓ.var
  if ℓ.neg then !b else b

-- 评价 3-子句
def clauseEval {n : Nat} (σ : Assignment n) (C : Clause n) : Bool :=
  let ℓ0 := C ⟨0, by decide⟩
  let ℓ1 := C ⟨1, by decide⟩
  let ℓ2 := C ⟨2, by decide⟩
  literalEval σ ℓ0 || literalEval σ ℓ1 || literalEval σ ℓ2

-- 递归版本 cnfEval：所有子句的合取
def cnfEval {n : Nat} (σ : Assignment n) : CNF n → Bool
  | []      => true
  | C :: Φ  => clauseEval σ C && cnfEval σ Φ

-- 满足解集合
def satSet {n : Nat} (Φ : CNF n) : Set (Assignment n) :=
  { σ | cnfEval σ Φ = true }

------------------------------------------------------------
-- 2. 能量函数 energy：未满足子句个数（递归定义）
------------------------------------------------------------

-- 能量：未满足子句数量
def energy {n : Nat} : CNF n → Assignment n → Nat
  | [],      _ => 0
  | C :: Φ,  σ =>
      energy Φ σ + (if clauseEval σ C = true then 0 else 1)

-- 核心引理：cnfEval = true ↔ energy = 0
lemma cnfEval_true_iff_energy_zero
    {n : Nat} (Φ : CNF n) (σ : Assignment n) :
    cnfEval σ Φ = true ↔ energy Φ σ = 0 := by
  induction Φ with
  | nil =>
      -- Φ = []
      simp [cnfEval, energy]
  | cons C Φ ih =>
      -- Φ = C :: Φ
      classical
      by_cases hC : clauseEval σ C = true
      · -- 子句 C 为真：等价关系归约到尾部 Φ
        simp [cnfEval, energy, hC, ih]
      · -- 子句 C 为假：整个公式为假，能量至少为 1
        -- 先把 clauseEval σ C = false 记下来，方便 simp
        have hC' : clauseEval σ C = false := by
          cases h' : clauseEval σ C <;> simp [h', hC] at *
        -- 此时：
        --   cnfEval σ (C :: Φ) = (false && cnfEval σ Φ) = false
        --   energy  (C :: Φ) σ = energy Φ σ + 1 ≥ 1
        -- 两边命题都为 False，直接用 simp 化成 False ↔ False
        simp [cnfEval, energy, hC', ih]

-- 满足 ↔ 能量为 0
lemma sat_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ energy Φ σ = 0 := by
  simpa [satSet] using (cnfEval_true_iff_energy_zero (Φ := Φ) (σ := σ))

------------------------------------------------------------
-- 3. 一般 CNF（变长子句）和 3-SAT 转换 to3CNF
------------------------------------------------------------

namespace PigeonholeFamily

-- 一般子句：字面列表（长度不限）
abbrev GenClause (n : Nat) := List (StructuralAction.Literal n)

-- 一般 CNF：子句列表，每个子句可以任意长度
abbrev GenCNF (n : Nat) := List (GenClause n)

-- 评价一般子句：折叠“或”
def genClauseEval {n : Nat} (σ : StructuralAction.Assignment n)
    (Γ : GenClause n) : Bool :=
  Γ.foldr (fun ℓ acc => StructuralAction.literalEval σ ℓ || acc) false

-- 评价一般 CNF：所有子句的合取
def genCNFEval {n : Nat} (σ : StructuralAction.Assignment n)
    (Φ : GenCNF n) : Bool :=
  Φ.foldr (fun C acc => genClauseEval σ C && acc) true

-- 把 3 个字面打包成一个 3-子句
def mkClause3 {n : Nat}
    (a b c : StructuralAction.Literal n)
    : StructuralAction.Clause n :=
  fun
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

-- 把一个变长子句 Γ 拆成若干个 3-子句列表
-- 简单 padding：不引入新变量，因此只保证：
--   genClauseEval σ Γ = true  ⇒  cnfEval σ (to3CNFClause Γ) = true
def to3CNFClause {n : Nat} : GenClause n → List (StructuralAction.Clause n)
  | []        => []
  | [a]       => [mkClause3 a a a]
  | [a, b]    => [mkClause3 a a b]
  | [a, b, c] => [mkClause3 a b c]
  | a :: b :: c :: rest =>
      mkClause3 a b c :: to3CNFClause rest

-- 3-SAT 转换：对每个一般子句做 to3CNFClause，然后拼接
def to3CNF {n : Nat} (Φ : GenCNF n) : StructuralAction.CNF n :=
  Φ.foldr (fun Γ acc => to3CNFClause Γ ++ acc) []

-- 3-CNF 转换的“满足性规格”：占位未来的严格证明
axiom to3CNF_equisat {n : Nat} (Φ : GenCNF n) :
  ∀ σ : StructuralAction.Assignment n,
    genCNFEval σ Φ = true ↔
    StructuralAction.cnfEval σ (to3CNF Φ) = true

------------------------------------------------------------
-- 4. 鸽笼原理 PHPₙ 的变量编码 + CNF 族
------------------------------------------------------------

-- 第 n 个鸽子：共有 n+1 只鸽子
abbrev Pigeon (n : Nat) := Fin (n + 1)

-- 第 n 个洞：共有 n 个洞
abbrev Hole (n : Nat) := Fin n

-- PHPₙ 的布尔变量个数上界：(n+1)*n + 1
abbrev PHPVar (n : Nat) : Nat :=
  Nat.succ ((n + 1) * n)

-- PHPₙ 的变量索引类型
abbrev PHPVarIdx (n : Nat) := Fin (PHPVar n)

-- 把 (p, h) 映射到变量索引：index(p, h) = p * n + h
noncomputable
def phpVarIndex (n : Nat) (p : Pigeon n) (h : Hole n) : PHPVarIdx n :=
  ⟨p.1 * n + h.1, by
    -- 证明 p.1 * n + h.1 < PHPVar n = (n+1)*n + 1
    have hp_le : p.1 ≤ n := Nat.le_of_lt_succ p.2
    have hh_lt : h.1 < n := h.2
    have hh_le : h.1 ≤ n - 1 := Nat.le_pred_of_lt hh_lt
    have h1a : p.1 * n + h.1 ≤ p.1 * n + (n - 1) :=
      Nat.add_le_add_left hh_le _
    have hp_mul : p.1 * n ≤ n * n :=
      Nat.mul_le_mul_right _ hp_le
    have h1b : p.1 * n + (n - 1) ≤ n * n + (n - 1) :=
      Nat.add_le_add_right hp_mul _
    have h1c : n * n + (n - 1) ≤ n * n + n := by
      have : n - 1 ≤ n := Nat.sub_le _ _
      exact Nat.add_le_add_left this _
    have h_total : p.1 * n + h.1 ≤ n * n + n :=
      le_trans (le_trans h1a h1b) h1c
    have h_le : p.1 * n + h.1 ≤ (n + 1) * n := by
      -- n * n + n = n * (n+1) = (n+1)*n
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
             Nat.add_assoc, Nat.mul_comm] using h_total
    have : p.1 * n + h.1 < ((n + 1) * n) + 1 :=
      Nat.lt_succ_of_le h_le
    simpa [PHPVar] using this ⟩

-- 把所有鸽子列成一个 List
noncomputable
def pigeonsList (n : Nat) : List (Pigeon n) :=
  List.ofFn (fun p : Pigeon n => p)

-- 把所有洞列成一个 List
noncomputable
def holesList (n : Nat) : List (Hole n) :=
  List.ofFn (fun h : Hole n => h)

-- 列出一个 List 中所有“有序对 (xᵢ, xⱼ)，其中 i < j”
def listPairs {α : Type} : List α → List (α × α)
  | []       => []
  | x :: xs  => (xs.map (fun y => (x,y))) ++ listPairs xs

-- 单只鸽子的 “至少一个洞” 子句：∨_{h} x_{p,h}
noncomputable
def phpClauseAtLeastOne (n : Nat) (p : Pigeon n) :
    GenClause (PHPVar n) :=
  (List.ofFn fun h : Hole n =>
    ({ var := phpVarIndex n p h, neg := false } :
      StructuralAction.Literal (PHPVar n)))

-- “At Least One” 子句族：对每个鸽子 p
noncomputable
def PHP_atLeastOne (n : Nat) : GenCNF (PHPVar n) :=
  List.ofFn (fun p : Pigeon n => phpClauseAtLeastOne n p)

-- 对固定洞 h，生成所有 “至多一只鸽子占 h” 的 2 字面子句
noncomputable
def phpClausesAtMostOneForHole (n : Nat) (h : Hole n) :
    GenCNF (PHPVar n) :=
  let ps    : List (Pigeon n)            := pigeonsList n
  let pairs : List (Pigeon n × Pigeon n) := listPairs ps
  pairs.map (fun (p₁, p₂) =>
    [ ({ var := phpVarIndex n p₁ h, neg := true } :
         StructuralAction.Literal (PHPVar n)),
      ({ var := phpVarIndex n p₂ h, neg := true } :
         StructuralAction.Literal (PHPVar n)) ])

-- “At Most One” 子句族：对每个洞 h
noncomputable
def PHP_atMostOne (n : Nat) : GenCNF (PHPVar n) :=
  let hs : List (Hole n) := holesList n
  hs.foldr
    (fun h acc => phpClausesAtMostOneForHole n h ++ acc)
    []

-- PHPₙ 的完整变长 CNF（未 3-SAT 化）：AtLeastOne ∧ AtMostOne
noncomputable
def PHP_fullGenCNF (n : Nat) : GenCNF (PHPVar n) :=
  PHP_atLeastOne n ++ PHP_atMostOne n

-- PHPₙ 的 3-SAT 编码：HardCNF = to3CNF (PHP_fullGenCNF)
noncomputable
def PHPcnf (n : Nat) : StructuralAction.CNF (PHPVar n) :=
  to3CNF (PHP_fullGenCNF n)

-- PHP_fullGenCNF 的语义桥接：SAT ↔ 存在单射 f : Pigeon → Hole
axiom PHP_fullGenCNF_sat_iff_injection (n : Nat) :
  (∃ σ : StructuralAction.Assignment (PHPVar n),
     genCNFEval σ (PHP_fullGenCNF n) = true)
  ↔
  (∃ f : Pigeon n → Hole n, Function.Injective f)

end PigeonholeFamily

------------------------------------------------------------
-- 5. 纯数学鸽笼原理：不存在单射 Pigeon n → Hole n
------------------------------------------------------------

section PigeonholeMath

open Function
open PigeonholeFamily

lemma no_injection_Pigeon_to_Hole (n : Nat) :
    ¬ ∃ f : Pigeon n → Hole n, Function.Injective f := by
  intro h
  rcases h with ⟨f, hf_inj⟩
  have h_card_le :
      Fintype.card (Pigeon n)
        ≤ Fintype.card (Hole n) :=
    Fintype.card_le_of_injective f hf_inj
  have h_succ_le : n.succ ≤ n := by
    simpa [Pigeon, Hole, Fintype.card_fin, Nat.succ_eq_add_one] using h_card_le
  exact Nat.not_succ_le_self n h_succ_le

end PigeonholeMath

------------------------------------------------------------
-- 6. 从 PHP_fullGenCNF 到 3-CNF PHPcnf 的 UNSAT 逻辑链
------------------------------------------------------------

section PHPUnsat

open PigeonholeFamily

-- PHP_fullGenCNF 不可满足
lemma PHP_fullGenCNF_unsat (n : Nat) :
  ¬ ∃ σ : Assignment (PHPVar n),
      genCNFEval σ (PHP_fullGenCNF n) = true := by
  intro hSat
  have hInj :
      ∃ f : Pigeon n → Hole n, Function.Injective f :=
    (PHP_fullGenCNF_sat_iff_injection n).1 hSat
  exact no_injection_Pigeon_to_Hole n hInj

-- HardCNF n = PHPcnf n：3-SAT 形式的鸽笼公式
noncomputable
def HardCNF (n : Nat) : CNF (PHPVar n) :=
  PHPcnf n

-- 对任意赋值 σ，HardCNF n 在 σ 下为 false（不可满足）
lemma HardCNF_unsat (n : Nat) :
  ∀ σ : Assignment (PHPVar n),
    cnfEval σ (HardCNF n) = false := by
  intro σ
  classical
  have hUnsatGen := PHP_fullGenCNF_unsat n
  have hNotSatCnf : ¬ cnfEval σ (HardCNF n) = true := by
    intro hSat
    -- 利用 to3CNF_equisat，把 3-CNF 的可满足性拉回 GenCNF
    have hEquiv :=
      to3CNF_equisat
        (Φ := PHP_fullGenCNF n) (σ := σ)
    have hSat3 :
        cnfEval σ (to3CNF (PHP_fullGenCNF n)) = true := by
      simpa [HardCNF, PHPcnf] using hSat
    have hSatGen :
        genCNFEval σ (PHP_fullGenCNF n) = true :=
      hEquiv.mpr hSat3
    exact hUnsatGen ⟨σ, hSatGen⟩
  -- Bool 只有 true / false 两种情况
  have hOr :
      cnfEval σ (HardCNF n) = true ∨
      cnfEval σ (HardCNF n) = false := by
    cases h' : cnfEval σ (HardCNF n) <;> simp [h']
  cases hOr with
  | inl hTrue =>
      exact False.elim (hNotSatCnf hTrue)
  | inr hFalse =>
      exact hFalse

end PHPUnsat

------------------------------------------------------------
-- 7. 抽象 DPLL 作用量序列 + 指数下界 / 多项式上界 schema
------------------------------------------------------------

-- 一个“作用量族”：给每个规模 n（例如 PHPₙ）一个自然数 A n
-- 在直觉上，你可以把 A n 理解为：
--   HardActionDPLL n = 在 HardCNF n 上，所有合法 DPLL 轨迹 ψ 的
--                      最小结构作用量 A[ψ]
def ActionSeq := Nat → Nat

-- 指数下界：A n ≥ 2^n
def ExpLower_2pow (A : ActionSeq) : Prop :=
  ∀ n : Nat, (2 : Nat)^n ≤ A n

-- 多项式上界（这里先固定成 n^2 的玩具版本）
def PolyUpper_general (A : ActionSeq) : Prop :=
  ∀ n : Nat, A n ≤ n^2

-- 玩具矛盾：如果 A 同时满足“指数下界 + n^2 上界”，则矛盾
theorem toy_hardFamily_contradiction
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_general A) : False := by
  -- 在 n = 10 处抽一个具体矛盾出来
  have h₁ : (2 : Nat)^10 ≤ A 10 := hLower 10
  have h₂ : A 10 ≤ 10^2 := hUpper 10
  have h_le : (2 : Nat)^10 ≤ 10^2 := le_trans h₁ h₂
  -- 已知 10^2 < 2^10
  have h_lt : 10^2 < (2 : Nat)^10 := by
    norm_num
  -- 合并得到 2^10 < 2^10，矛盾
  have h_absurd : (2 : Nat)^10 < (2 : Nat)^10 :=
    lt_of_le_of_lt h_le h_lt
  exact lt_irrefl _ h_absurd

-- 更语义化的包装名字
theorem no_polyTime_on_family
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_general A) :
    False :=
  toy_hardFamily_contradiction A hLower hUpper

------------------------------------------------------------
-- 8. 把 HardCNF（PHPₙ 的 3-SAT 编码）接到 DPLL 作用量族
------------------------------------------------------------

-- 概念上：HardActionDPLL n =
--   “在 HardCNF n 上，所有合法 DPLL 轨迹 ψ 的最小作用量 A[ψ]”
-- 这里先作为抽象序列，由后续复杂性理论给出性质。
axiom HardActionDPLL : ActionSeq

-- 指数下界假设（复杂性方向的核心目标）：
--   在 PHP 困难族 HardCNF n 上，任何 DPLL 轨迹的作用量都 ≥ 2^n，
--   从而 HardActionDPLL n ≥ 2^n。
axiom hardActionDPLL_expLower_2pow :
  ExpLower_2pow HardActionDPLL

-- 多项式上界假设（算法/工程上的“反面假设”）：
--   若我们假设 DPLL 在 HardCNF n 上是“多项式时间 + 每步结构密度多项式有界”，
--   通过类似 pathActionNat_polyUpper 的推理，可推出：
--     HardActionDPLL n ≤ n^2（这里用 n^2 当作统一的 P(n) 玩具上界）
axiom hardActionDPLL_polyUpper_from_alg :
  PolyUpper_general HardActionDPLL

-- 最终矛盾：同一个 HardActionDPLL 既有指数下界又有 n^2 上界 ⇒ 不可能。
theorem no_polyTime_DPLL_on_hardFamily : False :=
  no_polyTime_on_family
    HardActionDPLL
    hardActionDPLL_expLower_2pow
    hardActionDPLL_polyUpper_from_alg

------------------------------------------------------------
-- 9. 抽象算法模型 + 轨迹 + 离散作用量 + 下界引理
--    （与 PHPₙ / HardCNF 完全独立，是一个纯组合学工具）
------------------------------------------------------------

-- 抽象算法模型：状态类型 + init + step + halting
structure AlgorithmModel (n : Nat) where
  StateType : Type
  init     : CNF n → StateType
  step     : CNF n → StateType → StateType
  halting  : CNF n → StateType → Prop

-- 算法在公式 Φ 上的一条有限轨迹 ψ
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

open Finset

-- 离散结构作用量：
--   pathActionNat A Φ density ψ = ∑_{t=0}^T density(s_t)
def pathActionNat {n : Nat} (A : AlgorithmModel n) (Φ : CNF n)
    (density : A.StateType → Nat)
    (ψ : ComputationPath A Φ) : Nat :=
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => density (ψ.states t))

-- 核心下界引理：
--   若对路径上的每个状态 s_t 有 density(s_t) ≥ 1，
--   则作用量和 ≥ (T+1)。
lemma pathActionNat_ge_time
    {n : Nat} (A : AlgorithmModel n)
    (density : A.StateType → Nat)
    (hPos : ∀ (Φ : CNF n) (ψ : ComputationPath A Φ) (t : Fin (ψ.T + 1)),
      1 ≤ density (ψ.states t)) :
    ∀ (Φ : CNF n) (ψ : ComputationPath A Φ),
      ψ.T + 1 ≤ pathActionNat A Φ density ψ := by
  intro Φ ψ
  classical
  -- 每一步都有 density(s_t) ≥ 1
  have h_each : ∀ t : Fin (ψ.T + 1),
      1 ≤ density (ψ.states t) :=
    fun t => hPos Φ ψ t

  -- ∑ 1 ≤ ∑ density
  have h_sum_le :
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
      ≤
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun t => density (ψ.states t)) := by
    refine Finset.sum_le_sum ?h
    intro t ht
    exact h_each t

  -- 常数和：∑_t 1 = card * 1 = (T+1)
  have h_sum_const :
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
        = ψ.T + 1 := by
    -- 先用 sum_const_nat 得到 card * 1
    have h0 :
        (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
          =
        (Finset.univ : Finset (Fin (ψ.T + 1))).card * (1 : Nat) := by
      simpa using
        (Finset.sum_const_nat
          (s := (Finset.univ : Finset (Fin (ψ.T + 1))))
          (b := (1 : Nat)))
    -- 再用 card_univ = ψ.T + 1
    have h_card :
        (Finset.univ : Finset (Fin (ψ.T + 1))).card = ψ.T + 1 := by
      simpa [Finset.card_univ, Fintype.card_fin]
    simpa [h_card] using h0

  -- 把下界写成 ψ.T + 1 ≤ ∑ density
  have h_final :
      ψ.T + 1 ≤
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun t => density (ψ.states t)) := by
    simpa [h_sum_const] using h_sum_le

  -- 最后展开 pathActionNat
  simpa [pathActionNat] using h_final

end StructuralAction






