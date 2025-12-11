import Mathlib

open scoped BigOperators

namespace StructuralAction

------------------------------------------------------------
-- 1. 3-SAT 基础语法
------------------------------------------------------------

-- 布尔赋值：n 个变量，对应 Fin n → Bool
abbrev Assignment (n : Nat) := Fin n → Bool

-- [RESTRICT] 从扩展赋值 (n + aux) 投影回前 n 个变量
def restrictAssignment {n aux : Nat}
    (σ' : Assignment (n + aux)) : Assignment n :=
  fun i =>
    σ' ⟨i.1, by
      have hi : i.1 < n := i.2
      have hle : n ≤ n + aux := Nat.le_add_right _ _
      exact Nat.lt_of_lt_of_le hi hle⟩

-- 字面：变量索引 + 是否取反
structure Literal (n : Nat) where
  var : Fin n
  neg : Bool
  deriving Repr, DecidableEq   -- 后面 Resolution / DPLL 需要

-- 子句：3 个字面（仅用于 3-SAT 部分）
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
      simp [cnfEval, energy]
  | cons C Φ ih =>
      classical
      by_cases hC : clauseEval σ C = true
      · simp [cnfEval, energy, hC, ih]
      ·
        have hC' : clauseEval σ C = false := by
          cases h' : clauseEval σ C <;> simp [h', hC] at *
        simp [cnfEval, energy, hC', ih]

-- 满足 ↔ 能量为 0
lemma sat_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ energy Φ σ = 0 := by
  simpa [satSet] using (cnfEval_true_iff_energy_zero (Φ := Φ) (σ := σ))

------------------------------------------------------------
-- 3. 一般 CNF（变长子句）和评估
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

------------------------------------------------------------
-- 3'. 旧版 padding to3CNF（保留做对比，不再用在主证明链上）
------------------------------------------------------------

-- 把 3 个字面打包成一个 3-子句
def mkClause3 {n : Nat}
    (a b c : StructuralAction.Literal n)
    : StructuralAction.Clause n :=
  fun
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

-- 演示版：长度 ≥ 4 时只是简单分块，不保证等价
def to3CNFClause {n : Nat} : GenClause n → List (StructuralAction.Clause n)
  | []        => []
  | [a]       => [mkClause3 a a a]
  | [a, b]    => [mkClause3 a a b]
  | [a, b, c] => [mkClause3 a b c]
  | a :: b :: c :: rest =>
      mkClause3 a b c :: to3CNFClause rest

def to3CNF {n : Nat} (Φ : GenCNF n) : StructuralAction.CNF n :=
  Φ.foldr (fun Γ acc => to3CNFClause Γ ++ acc) []

------------------------------------------------------------
-- [TSEITIN CORE] 真正用于 3-CNF 的 Tseitin 转换接口（构造性版本）
------------------------------------------------------------

/-- Tseitin 转换的结果：
    * 原公式有 n 个变量；
    * Tseitin 转换后有 n + auxVars 个变量；
    * 输出一个真正的 3-CNF：StructuralAction.CNF (n + auxVars)。 -/
structure TseitinResult (n : Nat) where
  auxVars : Nat
  cnf     : StructuralAction.CNF (n + auxVars)

/-- 真正的 Tseitin 转换：
    这里先只给出“接口”，具体构造+证明是后续大工程，
    所以目前仍用 axiom 占位。 -/
axiom tseitinOfGenCNF {n : Nat} (Φ : GenCNF n) : TseitinResult n

/-- Tseitin 方向 1：GenCNF SAT ⇒ Tseitin CNF SAT（函数式版本）。

    给定原始赋值 σ，使 genCNFEval σ Φ = true，
    产生扩展赋值 σ' 使 Tseitin CNF 也为 true。 -/
axiom tseitin_sat_of_genSat {n : Nat} (Φ : GenCNF n) :
  ∀ (σ : StructuralAction.Assignment n),
    genCNFEval σ Φ = true →
    ∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true

/-- Tseitin 方向 2：Tseitin CNF SAT ⇒ GenCNF SAT（函数式版本）。

    给定扩展赋值 σ'，若 Tseitin CNF 满足，则
    原 CNF 在 restrictAssignment σ' 上也满足。 -/
axiom genSat_of_tseitin_sat {n : Nat} (Φ : GenCNF n) :
  ∀ (σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars)),
    StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true →
    genCNFEval (StructuralAction.restrictAssignment σ') Φ = true

/-- 方便使用的“存在性版本”：GenCNF SAT ⇒ Tseitin SAT。 -/
lemma tseitin_sat_of_genSat_exists {n : Nat} (Φ : GenCNF n) :
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true)
  →
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) := by
  intro h
  rcases h with ⟨σ, hσ⟩
  exact tseitin_sat_of_genSat (Φ := Φ) σ hσ

/-- 方便使用的“存在性版本”：Tseitin SAT ⇒ GenCNF SAT。 -/
lemma genSat_of_tseitin_sat_exists {n : Nat} (Φ : GenCNF n) :
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true)
  →
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true) := by
  intro h
  rcases h with ⟨σ', hσ'⟩
  refine ⟨StructuralAction.restrictAssignment σ', ?_⟩
  exact genSat_of_tseitin_sat (Φ := Φ) σ' hσ'

end PigeonholeFamily

------------------------------------------------------------
-- 4. [PHP FIX] 鸽笼原理 PHPₙ 的变量编码 + CNF 族
------------------------------------------------------------

open PigeonholeFamily

-- 第 n 个鸽子：共有 n+1 只鸽子
abbrev Pigeon (n : Nat) := Fin (n + 1)

-- 第 n 个洞：共有 n 个洞
abbrev Hole (n : Nat) := Fin n

/-- PHPₙ 的布尔变量个数：精确为 (n+1)*n 个。 -/
abbrev PHPVar (n : Nat) : Nat :=
  (n + 1) * n

/-- PHPₙ 的变量索引类型。 -/
abbrev PHPVarIdx (n : Nat) := Fin (PHPVar n)

/-- 把 (p, h) 映射到变量索引：index(p, h) = p * n + h。

    证明思路：
    * 因为 h < n，所以 p*n + h < p*n + n = (p+1)*n；
    * 又因为 p ≤ n，所以 (p+1)*n ≤ (n+1)*n = PHPVar n；
    * 合起来得到 p*n + h < PHPVar n。 -/
noncomputable
def phpVarIndex (n : Nat) (p : Pigeon n) (h : Hole n) : PHPVarIdx n :=
  ⟨p.1 * n + h.1, by
    have hp_lt : p.1 < n + 1 := p.2
    have hp_le : p.1 ≤ n := Nat.le_of_lt_succ hp_lt
    have hh_lt : h.1 < n := h.2

    -- 1. p * n + h < (p+1) * n
    have h_lt_step : p.1 * n + h.1 < p.1 * n + n := by
      exact Nat.add_lt_add_left hh_lt (p.1 * n)

    have h_eq : p.1 * n + n = (p.1 + 1) * n := by
      ring

    have h_lt_p1n : p.1 * n + h.1 < (p.1 + 1) * n := by
      simpa [h_eq] using h_lt_step

    -- 2. (p+1) ≤ (n+1) ⇒ (p+1)*n ≤ (n+1)*n
    have hp1_le : p.1 + 1 ≤ n + 1 :=
      Nat.succ_le_succ hp_le
    have hp1n_le : (p.1 + 1) * n ≤ (n + 1) * n :=
      Nat.mul_le_mul_right _ hp1_le

    -- 3. 链一下：p*n + h < (p+1)*n ≤ (n+1)*n
    have h_final :
        p.1 * n + h.1 < (n + 1) * n :=
      lt_of_lt_of_le h_lt_p1n hp1n_le

    -- 4. 最后改写成 PHPVar n
    simpa [PHPVar] using h_final ⟩

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

------------------------------------------------------------
-- 5. 纯数学鸽笼原理：不存在单射 Pigeon n → Hole n
------------------------------------------------------------

section PigeonholeMath

open Function

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
-- 6. 从 PHP_fullGenCNF 到 Tseitin 3-CNF 的 UNSAT 逻辑链
------------------------------------------------------------

section PHPUnsatTseitin

open PigeonholeFamily
open Function

/-- PHP_fullGenCNF 的语义桥接：
    SAT ↔ 存在单射 f : Pigeon n → Hole n。 -/
axiom PHP_fullGenCNF_sat_iff_injection (n : Nat) :
  (∃ σ : StructuralAction.Assignment (PHPVar n),
     genCNFEval σ (PHP_fullGenCNF n) = true)
  ↔
  (∃ f : Pigeon n → Hole n, Function.Injective f)

/-- PHP_fullGenCNF 不可满足。 -/
lemma PHP_fullGenCNF_unsat (n : Nat) :
  ¬ ∃ σ : Assignment (PHPVar n),
      genCNFEval σ (PHP_fullGenCNF n) = true := by
  intro hSat
  have hInj :
      ∃ f : Pigeon n → Hole n, Function.Injective f :=
    (PHP_fullGenCNF_sat_iff_injection n).1 hSat
  exact no_injection_Pigeon_to_Hole n hInj

/-- Tseitin 之后 PHPₙ 的变量总数：
    原始 PHPVar n 个变量 + Tseitin 引入的辅助变量个数。 -/
noncomputable
def HardVarT (n : Nat) : Nat :=
  PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars

/-- Tseitin 版困难族公式：对 PHP_fullGenCNF 做 Tseitin 3-CNF 转换。 -/
noncomputable
def HardCNF_T (n : Nat) : CNF (HardVarT n) :=
  (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf

/-- [HARD_T FIX] Tseitin 版困难族公式不可满足，
    使用了“函数式 + restrictAssignment”的 Tseitin 规格。 -/
lemma HardCNF_T_unsat (n : Nat) :
  ∀ σ' : Assignment (HardVarT n),
    cnfEval σ' (HardCNF_T n) = false := by
  intro σ'
  classical
  have hUnsatGen := PHP_fullGenCNF_unsat n
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n) = true := by
    intro hSat
    -- 1. 把 σ' 看成 Tseitin CNF 的满足赋值
    have hSatExist :
        ∃ σ'' : Assignment (PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars),
          cnfEval σ'' (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf = true := by
      refine ⟨σ', ?_⟩
      simpa [HardCNF_T, HardVarT] using hSat
    -- 2. 用“存在性版本”的 Tseitin 方向 2 得到原公式可满足
    have hGenSat :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      PigeonholeFamily.genSat_of_tseitin_sat_exists
        (Φ := PHP_fullGenCNF n)
        hSatExist
    -- 3. 与 PHP_fullGenCNF_unsat 矛盾
    exact hUnsatGen hGenSat
  have hOr :
      cnfEval σ' (HardCNF_T n) = true ∨
      cnfEval σ' (HardCNF_T n) = false := by
    cases h : cnfEval σ' (HardCNF_T n) <;> simp [h]
  cases hOr with
  | inl hTrue =>
      exact False.elim (hNotSat hTrue)
  | inr hFalse =>
      exact hFalse

end PHPUnsatTseitin

------------------------------------------------------------
-- 7. 抽象 DPLL 作用量序列 + 指数下界 / 多项式上界 schema
------------------------------------------------------------

-- 一个“作用量族”：给每个规模 n（例如 PHPₙ）一个自然数 A n
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
  have h₁ : (2 : Nat)^10 ≤ A 10 := hLower 10
  have h₂ : A 10 ≤ 10^2 := hUpper 10
  have h_le : (2 : Nat)^10 ≤ 10^2 := le_trans h₁ h₂
  have h_lt : 10^2 < (2 : Nat)^10 := by
    norm_num
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
-- 8. 一个“占位版”的 HardActionDPLL（目前只是 0）
------------------------------------------------------------

def HardActionDPLL : ActionSeq := fun _ => 0

------------------------------------------------------------
-- 9. 抽象算法模型 + 轨迹 + 离散作用量 + 下界引理
------------------------------------------------------------

structure AlgorithmModel (n : Nat) where
  StateType : Type
  init     : CNF n → StateType
  step     : CNF n → StateType → StateType
  halting  : CNF n → StateType → Prop

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

def pathActionNat {n : Nat} (A : AlgorithmModel n) (Φ : CNF n)
    (density : A.StateType → Nat)
    (ψ : ComputationPath A Φ) : Nat :=
  (Finset.univ : Finset (Fin (ψ.T + 1))).sum
    (fun t => density (ψ.states t))

lemma pathActionNat_ge_time
    {n : Nat} (A : AlgorithmModel n)
    (density : A.StateType → Nat)
    (hPos : ∀ (Φ : CNF n) (ψ : ComputationPath A Φ) (t : Fin (ψ.T + 1)),
      1 ≤ density (ψ.states t)) :
    ∀ (Φ : CNF n) (ψ : ComputationPath A Φ),
      ψ.T + 1 ≤ pathActionNat A Φ density ψ := by
  intro Φ ψ
  classical
  have h_each : ∀ t : Fin (ψ.T + 1),
      1 ≤ density (ψ.states t) :=
    fun t => hPos Φ ψ t
  have h_sum_le :
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
      ≤
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun t => density (ψ.states t)) := by
    refine Finset.sum_le_sum ?h
    intro t ht
    exact h_each t
  have h_sum_const :
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
        = ψ.T + 1 := by
    have h0 :
        (Finset.univ : Finset (Fin (ψ.T + 1))).sum (fun _ => (1 : Nat))
          =
        (Finset.univ : Finset (Fin (ψ.T + 1))).card * (1 : Nat) := by
      simpa using
        (Finset.sum_const_nat
          (s := (Finset.univ : Finset (Fin (ψ.T + 1))))
          (b := (1 : Nat)))
    have h_card :
        (Finset.univ : Finset (Fin (ψ.T + 1))).card = ψ.T + 1 := by
      simpa [Finset.card_univ, Fintype.card_fin]
    simpa [h_card] using h0
  have h_final :
      ψ.T + 1 ≤
      (Finset.univ : Finset (Fin (ψ.T + 1))).sum
        (fun t => density (ψ.states t)) := by
    simpa [h_sum_const] using h_sum_le
  simpa [pathActionNat] using h_final

------------------------------------------------------------
-- 10. Resolution 系统（RClause = List (Literal n)）
------------------------------------------------------------

namespace Resolution

open StructuralAction

/-- Resolution 子句：任意长度的字面列表（可以是空子句）。 -/
abbrev RClause (n : Nat) := List (Literal n)

/-- Resolution 公式：子句列表。 -/
abbrev RCNF (n : Nat) := List (RClause n)

/-- 字面取反：只翻转 neg 位，变量索引不变。 -/
def litNeg {n : Nat} (ℓ : Literal n) : Literal n :=
  { var := ℓ.var, neg := !ℓ.neg }

/-- 合并两个子句（集合视角：C ∪ D）。目前简单实现为列表拼接，再做去重。 -/
def merge {n : Nat} (C D : RClause n) : RClause n :=
  (C ++ D).eraseDups

/-- 判断两个字面是否互补：变量相同，极性相反。 -/
def isComplement {n : Nat} (ℓ₁ ℓ₂ : Literal n) : Bool :=
  decide (ℓ₁.var = ℓ₂.var ∧ ℓ₁.neg ≠ ℓ₂.neg)

/-- 简单规范化子句：
    * 去重；
    * 若存在互补对，则返回空子句（视作永真子句，可在 ConflictAnalyze 时忽略）。 -/
def simplify {n : Nat} (C : RClause n) : RClause n :=
  let C₁ := C.eraseDups
  if h : ∃ ℓ₁ ∈ C₁, ∃ ℓ₂ ∈ C₁, isComplement ℓ₁ ℓ₂ = true then
    []
  else
    C₁

/-- 单步 Resolution：从 (ℓ :: C) 和 (¬ℓ :: D) 推出 C ∪ D，
    并做一次简化（去重 / 互补检查）。 -/
def resolveOneStep {n : Nat}
    (ℓ : Literal n)
    (C D : RClause n) : RClause n :=
  let C' := C.filter (fun x => x ≠ ℓ)
  let D' := D.filter (fun x => x ≠ litNeg ℓ)
  simplify (merge C' D')

/-- Resolution 推导关系。 -/
inductive Derives {n : Nat} (Φ : RCNF n) : RClause n → Type where
  | axiom (C : RClause n) (hC : C ∈ Φ) :
      Derives Φ C
  | weaken (C C' : RClause n)
      (hSub : ∀ ℓ, ℓ ∈ C' → ℓ ∈ C)
      (hC' : Derives Φ C') :
      Derives Φ C
  | resolve (C D : RClause n) (ℓ : Literal n)
      (hC : Derives Φ (ℓ :: C))
      (hD : Derives Φ (litNeg ℓ :: D)) :
      Derives Φ (C ++ D)

/-- 一个反驳：导出了空子句 []。 -/
def Refutes {n : Nat} (Φ : RCNF n) : Type :=
  Derives Φ ([] : RClause n)

/-- 单个 Resolution 推导树的“长度”（节点数）。 -/
def derivationLength {n : Nat} {Φ : RCNF n} {C : RClause n}
    (h : Derives Φ C) : Nat :=
  match h with
  | Derives.axiom _ _           => 1
  | Derives.weaken _ _ _ h'     => derivationLength h'
  | Derives.resolve _ _ _ h₁ h₂ =>
      derivationLength h₁ + derivationLength h₂ + 1

/-- 一个反驳的长度：就是其内部导出证明的长度。 -/
def proofLength {n : Nat} {Φ : RCNF n}
    (π : Refutes Φ) : Nat :=
  derivationLength π

/-- （抽象形态）Resolution 对某些公式族的指数下界占位公理。 -/
axiom resolutionRefutation_expLower_2pow :
  ∃ (Len : StructuralAction.ActionSeq),
    StructuralAction.ExpLower_2pow Len

end Resolution

------------------------------------------------------------
-- 11. AbstractDPLL：带 decisionLevel / antecedent / resSteps
--     的状态 + UnitProp / ConflictAnalyze / Backtrack
------------------------------------------------------------

namespace AbstractDPLL

open StructuralAction
open Resolution

--------------------------------------------------
-- 11.1 从 3-SAT CNF 转成 Resolution CNF
--------------------------------------------------

/-- 把一个 3-子句变成 Resolution 子句（3 个字面组成的 List）。 -/
def clauseToRClause {n : Nat} (C : Clause n) : RClause n :=
  [ C ⟨0, by decide⟩,
    C ⟨1, by decide⟩,
    C ⟨2, by decide⟩ ]

/-- 把 3-SAT CNF（Clause 列表）转成 Resolution CNF（RClause 列表）。 -/
def cnfToRCNF {n : Nat} (Φ : CNF n) : RCNF n :=
  Φ.map clauseToRClause

--------------------------------------------------
-- 11.2 Trail / State：加入 decisionLevel / antecedent / resSteps
--------------------------------------------------

/-- Trail 中的一个条目：包含字面、决策层级以及产生它的前因子句。 -/
structure TrailEntry (n : Nat) where
  lit        : Literal n
  level      : Nat
  antecedent : Option (RClause n)

/-- 决策/传播轨迹：一串已经赋为 True 的字面（附带层级和前因）。 -/
abbrev Trail (n : Nat) := List (TrailEntry n)

/-- 抽象 DPLL 状态。 -/
structure State (n : Nat) where
  trail         : Trail n
  decisionLevel : Nat
  learnt        : RCNF n
  pending       : RCNF n
  conflict      : Option (RClause n)
  resSteps      : Nat

--------------------------------------------------
-- 11.3 Trail 相关辅助：真假判断 / level / antecedent
--------------------------------------------------

/-- 字面 ℓ 是否在 trail 中被赋为 True。 -/
def litIsTrue {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = ℓ)

/-- 字面 ℓ 是否在 trail 下为 False（存在其取反）。 -/
def litIsFalse {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = litNeg ℓ)

/-- 在给定 trail 下，从子句 C 里收集“未赋值的字面”。 -/
def unassignedLits {n : Nat} (τ : Trail n) (C : RClause n) :
    List (Literal n) :=
  C.filter (fun ℓ => !litIsTrue τ ℓ && !litIsFalse τ ℓ)

/-- 在 Trail 上查找某个字面的 antecedent 子句（若存在）。 -/
def findAntecedent {n : Nat} (τ : Trail n) (ℓ : Literal n) :
    Option (RClause n) :=
  match τ.find? (fun e => e.lit = ℓ) with
  | none      => none
  | some ent  => ent.antecedent

/-- Trail 中给定字面的决策层级（若未出现在 trail 中，则为 none）。 -/
def litLevel {n : Nat} (τ : Trail n) (ℓ : Literal n) : Option Nat :=
  match τ.find? (fun e => e.lit = ℓ) with
  | none     => none
  | some ent => some ent.level

/-- 带缺省值版本：若字面不在 trail 中，则视为层级 0。 -/
def litLevelDflt {n : Nat} (τ : Trail n) (ℓ : Literal n) : Nat :=
  match litLevel τ ℓ with
  | some l => l
  | none   => 0

--------------------------------------------------
-- 11.4 Unit Propagation
--------------------------------------------------

/-- Unit Propagation 的递归辅助函数。 -/
def unitPropagateAux {n : Nat}
    (τ : Trail n) (s : State n) :
    List (RClause n) → State n
  | [] => s
  | C :: Cs =>
      if C.any (fun ℓ => litIsTrue τ ℓ) then
        unitPropagateAux τ s Cs
      else
        let unassigned := unassignedLits τ C
        match unassigned with
        | [] =>
            { s with conflict := some C }
        | [ℓ] =>
            let entry : TrailEntry n :=
              { lit        := ℓ
                level      := s.decisionLevel
                antecedent := some C }
            { s with trail := entry :: s.trail }
        | _ =>
            unitPropagateAux τ s Cs

/-- Unit Propagation 顶层。 -/
def unitPropagate {n : Nat} (ΦR : RCNF n) (s : State n) : State n :=
  if h : s.conflict ≠ none then
    s
  else
    let clauses : List (RClause n) := ΦR ++ s.learnt ++ s.pending
    let τ := s.trail
    unitPropagateAux τ s clauses

--------------------------------------------------
-- 11.5 冲突分析：计数 / 选择 / 递归 resolve
--------------------------------------------------

/-- 统计一个子句中，在给定 decisionLevel 下出现的文字个数。 -/
def countLitsAtLevel {n : Nat}
    (τ : Trail n) (C : RClause n) (lvl : Nat) : Nat :=
  C.foldl
    (fun acc ℓ =>
      match litLevel τ ℓ with
      | some l =>
          if l = lvl then acc.succ else acc
      | none   => acc)
    0

/-- 从子句中挑出一个位于给定 decisionLevel 的文字（若存在）。 -/
def pickLitAtLevel? {n : Nat}
    (τ : Trail n) (C : RClause n) (lvl : Nat) :
    Option (Literal n) :=
  C.find? (fun ℓ =>
    match litLevel τ ℓ with
    | some l => l = lvl
    | none   => False)

/-- 冲突分析返回结果。 -/
structure AnalyzeResult (n : Nat) where
  learnt   : RClause n
  resSteps : Nat

/-- 冲突分析核心递归（简化版 UIP/backjump）： -/
def analyzeConflictCore {n : Nat}
    (τ : Trail n) (C₀ : RClause n) (lvl fuel : Nat) :
    AnalyzeResult n :=
  match fuel with
  | 0 =>
      { learnt   := Resolution.simplify C₀
        resSteps := 0 }
  | Nat.succ fuel' =>
      let cnt := countLitsAtLevel τ C₀ lvl
      if hcnt : cnt ≤ 1 then
        { learnt   := Resolution.simplify C₀
          resSteps := 0 }
      else
        match pickLitAtLevel? τ C₀ lvl with
        | none =>
            { learnt   := Resolution.simplify C₀
              resSteps := 0 }
        | some ℓ =>
            match findAntecedent τ ℓ with
            | none =>
                { learnt   := Resolution.simplify C₀
                  resSteps := 0 }
            | some C_ant =>
                let C_next := Resolution.resolveOneStep ℓ C₀ C_ant
                let resNext := analyzeConflictCore τ C_next lvl fuel'
                { learnt   := resNext.learnt
                  resSteps := resNext.resSteps.succ }

--------------------------------------------------
-- 11.6 Backjump 辅助
--------------------------------------------------

/-- 计算一个子句在当前 trail 下出现的最大决策层级（缺省 0）。 -/
def maxLevelInClause {n : Nat} (τ : Trail n) (C : RClause n) : Nat :=
  C.foldl (fun acc ℓ => Nat.max acc (litLevelDflt τ ℓ)) 0

/-- 给定目标决策层级 lvl，把 trail 裁剪为只保留 level ≤ lvl 的条目。 -/
def backtrackTrail {n : Nat} (τ : Trail n) (lvl : Nat) : Trail n :=
  τ.filter (fun e => e.level ≤ lvl)

--------------------------------------------------
-- 11.7 ConflictAnalyze / Backtrack / Decide
--------------------------------------------------

/-- Conflict Analyze。 -/
def conflictAnalyze {n : Nat} (ΦR : RCNF n) (s : State n) : State n :=
  match s.conflict with
  | none => s
  | some C_conf =>
      let lvl  := s.decisionLevel
      let τ    := s.trail
      let fuel :=
        τ.length + ΦR.length + s.learnt.length + s.pending.length + 1
      let res := analyzeConflictCore τ C_conf lvl fuel
      let C_learnt := Resolution.simplify res.learnt
      { s with
        learnt   := C_learnt :: s.learnt,
        conflict := none,
        resSteps := s.resSteps + res.resSteps }

/-- Backtrack / Backjump。 -/
def backtrack {n : Nat} (s : State n) : State n :=
  match s.learnt with
  | [] => s
  | C_learnt :: _ =>
      let τ       := s.trail
      let Lmax    := maxLevelInClause τ C_learnt
      let newLvl  := Lmax
      let τ'      := backtrackTrail τ newLvl
      { trail         := τ'
        decisionLevel := newLvl
        learnt        := s.learnt
        pending       := s.pending
        conflict      := s.conflict
        resSteps      := s.resSteps }

/-- Decide：在没有 unit / 冲突时，选择一个未赋值的变量做决策。 -/
def decide {n : Nat} (s : State n) : State n :=
  match s.pending with
  | [] => s
  | C :: _ =>
      match C with
      | [] => s
      | lit :: _ =>
          let newLevel := s.decisionLevel.succ
          let newEntry : TrailEntry n :=
            { lit        := lit
              level      := newLevel
              antecedent := none }
          { trail         := newEntry :: s.trail
            decisionLevel := newLevel
            learnt        := s.learnt
            pending       := s.pending
            conflict      := s.conflict
            resSteps      := s.resSteps }

--------------------------------------------------
-- 11.8 抽象 DPLL 模型：init / step / halting
--------------------------------------------------

/-- 初始状态。 -/
def initState {n : Nat} (Φ : CNF n) : State n :=
  { trail         := []
    decisionLevel := 0
    learnt        := []
    pending       := cnfToRCNF Φ
    conflict      := none
    resSteps      := 0 }

/-- 抽象 DPLL 模型。 -/
noncomputable
def Model (n : Nat) : AlgorithmModel n :=
  { StateType := State n
    init := fun Φ => initState Φ
    step := fun Φ s =>
      let ΦR := cnfToRCNF Φ
      let s₁ := unitPropagate ΦR s
      let s₂ := conflictAnalyze ΦR s₁
      let s₃ := backtrack s₂
      let s₄ := decide s₃
      s₄
    halting := fun _ s =>
      s.pending = [] ∨ s.conflict ≠ none }

--------------------------------------------------
-- 11.9 结构密度 λ'：每一步至少付出 1 单位 Action + resSteps
--------------------------------------------------

/-- 密度：至少 1，并叠加 resSteps。 -/
def density (n : Nat) (s : State n) : Nat :=
  s.resSteps.succ

/-- 对 DPLL 模型的 density，任意状态的 cost 至少为 1。 -/
lemma density_pos (n : Nat)
    (Φ : CNF n) (ψ : ComputationPath (Model n) Φ)
    (t : Fin (ψ.T + 1)) :
    1 ≤ density n (ψ.states t) := by
  simp [density]

/-- 专门版下界：在 DPLL 模型中，路径的 Action 至少等于时间步数 ψ.T + 1。 -/
lemma dpll_pathActionNat_ge_steps (n : Nat)
    (Φ : CNF n) (ψ : ComputationPath (Model n) Φ) :
    ψ.T + 1 ≤ pathActionNat (Model n) Φ (density n) ψ := by
  have hPos :
      ∀ (Φ' : CNF n) (ψ' : ComputationPath (Model n) Φ')
        (t : Fin (ψ'.T + 1)),
        1 ≤ density n (ψ'.states t) := by
    intro Φ' ψ' t
    simpa using (density_pos n Φ' ψ' t)
  have h :=
    StructuralAction.pathActionNat_ge_time
      (A := Model n)
      (density := density n)
      (Φ := Φ)
      (ψ := ψ)
      hPos
  exact h

--------------------------------------------------
-- 11.10 Resolution → DPLLPath 的“模拟骨架”（仍为公理）
--------------------------------------------------

/-- 一个“模拟记录”：给定 CNF Φ 及其 Resolution 反驳 π，
    构造 DPLL 计算路径 ψ，并证明
      pathActionNat ≥ proofLength π。 -/
structure Simulation {n : Nat} (Φ : CNF n)
    (π : Refutes (cnfToRCNF Φ)) where
  ψ  : ComputationPath (Model n) Φ
  hA : pathActionNat (Model n) Φ (density n) ψ
        ≥ proofLength π

/-- 存在模拟（未来目标：把它从 axiom 提升为 theorem）。 -/
axiom exists_simulation {n : Nat} (Φ : CNF n)
  (π : Refutes (cnfToRCNF Φ)) :
  Simulation (Φ := Φ) (π := π)

end AbstractDPLL

------------------------------------------------------------
-- 12. Resolution-hard family → DPLL-hard action family
------------------------------------------------------------

section HardFamilySchema

open Resolution
open AbstractDPLL

/-- 一个抽象的 “Resolution 困难族”。 -/
structure HardFamily where
  m : Nat → Nat
  F : ∀ n, CNF (m n)
  π : ∀ n, Resolution.Refutes (AbstractDPLL.cnfToRCNF (F n))

/-- 把每个 n 的 Resolution 反驳长度视为一个作用量族。 -/
def resLengthSeq (H : HardFamily) : ActionSeq :=
  fun n => Resolution.proofLength (H.π n)

/-- 从一个 Resolution 困难族 H 构造对应的 DPLL 作用量族。 -/
noncomputable
def hardActionFromFamily (H : HardFamily) : ActionSeq :=
  fun n =>
    let sim :=
      AbstractDPLL.exists_simulation
        (Φ := H.F n)
        (π := H.π n)
    pathActionNat
      (AbstractDPLL.Model (H.m n))
      (H.F n)
      (AbstractDPLL.density (H.m n))
      sim.ψ

/-- 对每个 n，DPLL 作用量 ≥ 对应的 Resolution 反驳长度。 -/
lemma hardActionFromFamily_ge_resLength (H : HardFamily) :
  ∀ n, resLengthSeq H n ≤ hardActionFromFamily H n := by
  intro n
  classical
  let sim :=
    AbstractDPLL.exists_simulation
      (Φ := H.F n)
      (π := H.π n)
  change
    Resolution.proofLength (H.π n)
      ≤
    pathActionNat
      (AbstractDPLL.Model (H.m n))
      (H.F n)
      (AbstractDPLL.density (H.m n))
      sim.ψ
  exact sim.hA

/-- 若某个 HardFamily 的 Resolution 反驳族存在指数下界，
    则对应的 DPLL 作用量族也存在指数下界。 -/
lemma expLower_lift_from_res_to_dpll
    (H : HardFamily)
    (hRes : ExpLower_2pow (resLengthSeq H)) :
    ExpLower_2pow (hardActionFromFamily H) := by
  intro n
  have h1 : (2 : Nat)^n ≤ resLengthSeq H n := hRes n
  have h2 : resLengthSeq H n ≤ hardActionFromFamily H n :=
    hardActionFromFamily_ge_resLength H n
  exact le_trans h1 h2

/-- 把 “Resolution 困难族在证明长度上有指数下界”
    和 “对应的 DPLL 作用量族有多项式上界” 拼在一起，
    得到矛盾。 -/
theorem no_polyTime_DPLL_on_HardFamily
    (H : HardFamily)
    (hRes : ExpLower_2pow (resLengthSeq H))
    (hUpper : PolyUpper_general (hardActionFromFamily H)) :
    False :=
  by
    have hLowerDPLL : ExpLower_2pow (hardActionFromFamily H) :=
      expLower_lift_from_res_to_dpll H hRes
    exact
      no_polyTime_on_family
        (A      := hardActionFromFamily H)
        (hLower := hLowerDPLL)
        (hUpper := hUpper)

end HardFamilySchema

end StructuralAction













































