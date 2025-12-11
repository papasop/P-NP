import Mathlib

open scoped BigOperators

namespace StructuralAction

------------------------------------------------------------
-- 1. 3-SAT 基础语法
------------------------------------------------------------

-- 布尔赋值：n 个变量，对应 Fin n → Bool
abbrev Assignment (n : Nat) := Fin n → Bool

-- 从扩展赋值 (n + aux) 投影回前 n 个变量
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
  deriving Repr, DecidableEq

-- 3-子句
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
-- 2. 能量函数：未满足子句个数
------------------------------------------------------------

def energy {n : Nat} : CNF n → Assignment n → Nat
  | [],      _ => 0
  | C :: Φ,  σ =>
      energy Φ σ + (if clauseEval σ C = true then 0 else 1)

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

lemma sat_iff_energy_zero {n : Nat} (Φ : CNF n) (σ : Assignment n) :
  σ ∈ satSet Φ ↔ energy Φ σ = 0 := by
  simpa [satSet] using (cnfEval_true_iff_energy_zero (Φ := Φ) (σ := σ))

------------------------------------------------------------
-- 3. 一般 CNF（变长子句）及评估 + Tseitin 接口
------------------------------------------------------------

namespace PigeonholeFamily

-- 一般子句：字面列表
abbrev GenClause (n : Nat) := List (StructuralAction.Literal n)
-- 一般 CNF
abbrev GenCNF (n : Nat) := List (GenClause n)

-- 一般子句的“或”
def genClauseEval {n : Nat} (σ : StructuralAction.Assignment n)
    (Γ : GenClause n) : Bool :=
  Γ.foldr (fun ℓ acc => StructuralAction.literalEval σ ℓ || acc) false

-- 一般 CNF 的“且”
def genCNFEval {n : Nat} (σ : StructuralAction.Assignment n)
    (Φ : GenCNF n) : Bool :=
  Φ.foldr (fun C acc => genClauseEval σ C && acc) true

------------------------------------------------------------
-- 3'. 演示用 padding 3-SAT 转换（不再用于主证明链）
------------------------------------------------------------

def mkClause3 {n : Nat}
    (a b c : StructuralAction.Literal n)
    : StructuralAction.Clause n :=
  fun
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

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
-- Tseitin 真正接口：引入辅助变量 + 3-CNF
------------------------------------------------------------

structure TseitinResult (n : Nat) where
  auxVars : Nat
  cnf     : StructuralAction.CNF (n + auxVars)

/-- Tseitin 转换：占位 axiom，接口是正确的。 -/
axiom tseitinOfGenCNF {n : Nat} (Φ : GenCNF n) : TseitinResult n

/-- Tseitin 方向 1：GenCNF SAT ⇒ Tseitin CNF SAT（函数式版本）。 -/
axiom tseitin_sat_of_genSat {n : Nat} (Φ : GenCNF n) :
  ∀ (σ : StructuralAction.Assignment n),
    genCNFEval σ Φ = true →
    ∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true

/-- Tseitin 方向 2：Tseitin CNF SAT ⇒ GenCNF SAT（函数式版本）。 -/
axiom genSat_of_tseitin_sat {n : Nat} (Φ : GenCNF n) :
  ∀ (σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars)),
    StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true →
    genCNFEval (StructuralAction.restrictAssignment σ') Φ = true

/-- 存在性版本：GenCNF SAT ⇒ Tseitin SAT。 -/
lemma tseitin_sat_of_genSat_exists {n : Nat} (Φ : GenCNF n) :
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true)
  →
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) := by
  intro h
  rcases h with ⟨σ, hσ⟩
  exact tseitin_sat_of_genSat (Φ := Φ) σ hσ

/-- 存在性版本：Tseitin SAT ⇒ GenCNF SAT。 -/
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
-- 4. PHP 编码（修正变量个数）
------------------------------------------------------------

open PigeonholeFamily

abbrev Pigeon (n : Nat) := Fin (n + 1)
abbrev Hole (n : Nat) := Fin n

/-- PHPₙ 的变量总数：精确为 (n+1)*n 个。 -/
abbrev PHPVar (n : Nat) : Nat :=
  (n + 1) * n

abbrev PHPVarIdx (n : Nat) := Fin (PHPVar n)

/-- 把 (p, h) 映射到 index = p * n + h。 -/
noncomputable
def phpVarIndex (n : Nat) (p : Pigeon n) (h : Hole n) : PHPVarIdx n :=
  ⟨p.1 * n + h.1, by
    have hp_lt : p.1 < n + 1 := p.2
    have hp_le : p.1 ≤ n := Nat.le_of_lt_succ hp_lt
    have hh_lt : h.1 < n := h.2

    -- p*n + h < (p+1)*n
    have h_lt_step : p.1 * n + h.1 < p.1 * n + n := by
      exact Nat.add_lt_add_left hh_lt (p.1 * n)
    have h_eq : p.1 * n + n = (p.1 + 1) * n := by
      ring
    have h_lt_p1n : p.1 * n + h.1 < (p.1 + 1) * n := by
      simpa [h_eq] using h_lt_step

    -- (p+1)*n ≤ (n+1)*n
    have hp1_le : p.1 + 1 ≤ n + 1 :=
      Nat.succ_le_succ hp_le
    have hp1n_le : (p.1 + 1) * n ≤ (n + 1) * n :=
      Nat.mul_le_mul_right _ hp1_le

    have h_final :
        p.1 * n + h.1 < (n + 1) * n :=
      lt_of_lt_of_le h_lt_p1n hp1n_le

    simpa [PHPVar] using h_final ⟩

noncomputable
def pigeonsList (n : Nat) : List (Pigeon n) :=
  List.ofFn (fun p : Pigeon n => p)

noncomputable
def holesList (n : Nat) : List (Hole n) :=
  List.ofFn (fun h : Hole n => h)

def listPairs {α : Type} : List α → List (α × α)
  | []       => []
  | x :: xs  => (xs.map (fun y => (x,y))) ++ listPairs xs

noncomputable
def phpClauseAtLeastOne (n : Nat) (p : Pigeon n) :
    GenClause (PHPVar n) :=
  (List.ofFn fun h : Hole n =>
    ({ var := phpVarIndex n p h, neg := false } :
      StructuralAction.Literal (PHPVar n)))

noncomputable
def PHP_atLeastOne (n : Nat) : GenCNF (PHPVar n) :=
  List.ofFn (fun p : Pigeon n => phpClauseAtLeastOne n p)

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

noncomputable
def PHP_atMostOne (n : Nat) : GenCNF (PHPVar n) :=
  let hs : List (Hole n) := holesList n
  hs.foldr
    (fun h acc => phpClausesAtMostOneForHole n h ++ acc)
    []

noncomputable
def PHP_fullGenCNF (n : Nat) : GenCNF (PHPVar n) :=
  PHP_atLeastOne n ++ PHP_atMostOne n

------------------------------------------------------------
-- 5. 纯数学鸽笼原理
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
-- 6. PHP_fullGenCNF UNSAT + Tseitin 版 HardCNF_T
------------------------------------------------------------

section PHPUnsatTseitin

open Function
open PigeonholeFamily

/-- PHP_fullGenCNF 的语义桥接：SAT ↔ 存在单射。 -/
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

/-- Tseitin 之后 PHPₙ 的变量总数：原始变量 + auxVars。 -/
noncomputable
def HardVarT (n : Nat) : Nat :=
  PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars

/-- Tseitin 版困难公式：PHP_fullGenCNF 经 Tseitin 3-CNF。 -/
noncomputable
def HardCNF_T (n : Nat) : CNF (HardVarT n) :=
  (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf

/-- Tseitin 版困难族公式不可满足。 -/
lemma HardCNF_T_unsat (n : Nat) :
  ∀ σ' : Assignment (HardVarT n),
    cnfEval σ' (HardCNF_T n) = false := by
  intro σ'
  classical
  have hUnsatGen := PHP_fullGenCNF_unsat n
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n) = true := by
    intro hSat
    -- 把 σ' 看成 Tseitin CNF 的满足赋值
    have hSatExist :
        ∃ σ'' : Assignment (PHPVar n +
          (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars),
          cnfEval σ'' (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf = true := by
      -- 利用 HardVarT 的定义展开即可 defeq
      refine ⟨σ', ?_⟩
      simpa [HardCNF_T, HardVarT] using hSat
    -- Tseitin SAT ⇒ GenCNF SAT
    have hGenSat :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      PigeonholeFamily.genSat_of_tseitin_sat_exists
        (Φ := PHP_fullGenCNF n)
        hSatExist
    -- 与 PHP_fullGenCNF_unsat 矛盾
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
-- 7. 抽象作用量族 + 上下界
------------------------------------------------------------

def ActionSeq := Nat → Nat

def ExpLower_2pow (A : ActionSeq) : Prop :=
  ∀ n : Nat, (2 : Nat)^n ≤ A n

def PolyUpper_general (A : ActionSeq) : Prop :=
  ∀ n : Nat, A n ≤ n^2

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

theorem no_polyTime_on_family
    (A : ActionSeq)
    (hLower : ExpLower_2pow A)
    (hUpper : PolyUpper_general A) :
    False :=
  toy_hardFamily_contradiction A hLower hUpper

------------------------------------------------------------
-- 8. 抽象算法模型 + 轨迹 + pathAction
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
-- 9. Resolution 系统
------------------------------------------------------------

namespace Resolution

open StructuralAction

abbrev RClause (n : Nat) := List (Literal n)
abbrev RCNF (n : Nat) := List (RClause n)

def litNeg {n : Nat} (ℓ : Literal n) : Literal n :=
  { var := ℓ.var, neg := !ℓ.neg }

def merge {n : Nat} (C D : RClause n) : RClause n :=
  (C ++ D).eraseDups

def isComplement {n : Nat} (ℓ₁ ℓ₂ : Literal n) : Bool :=
  decide (ℓ₁.var = ℓ₂.var ∧ ℓ₁.neg ≠ ℓ₂.neg)

def simplify {n : Nat} (C : RClause n) : RClause n :=
  let C₁ := C.eraseDups
  if h : ∃ ℓ₁ ∈ C₁, ∃ ℓ₂ ∈ C₁, isComplement ℓ₁ ℓ₂ = true then
    []
  else
    C₁

def resolveOneStep {n : Nat}
    (ℓ : Literal n)
    (C D : RClause n) : RClause n :=
  let C' := C.filter (fun x => x ≠ ℓ)
  let D' := D.filter (fun x => x ≠ litNeg ℓ)
  simplify (merge C' D')

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

def Refutes {n : Nat} (Φ : RCNF n) : Type :=
  Derives Φ ([] : RClause n)

def derivationLength {n : Nat} {Φ : RCNF n} {C : RClause n}
    (h : Derives Φ C) : Nat :=
  match h with
  | Derives.axiom _ _           => 1
  | Derives.weaken _ _ _ h'     => derivationLength h'
  | Derives.resolve _ _ _ h₁ h₂ =>
      derivationLength h₁ + derivationLength h₂ + 1

def proofLength {n : Nat} {Φ : RCNF n}
    (π : Refutes Φ) : Nat :=
  derivationLength π

end Resolution

------------------------------------------------------------
-- 10. AbstractDPLL：DPLL 状态 + UnitProp + ConflictAnalyze + Backtrack
------------------------------------------------------------

namespace AbstractDPLL

open StructuralAction
open Resolution

/-- 3-SAT CNF → Resolution CNF。 -/
def clauseToRClause {n : Nat} (C : Clause n) : RClause n :=
  [ C ⟨0, by decide⟩,
    C ⟨1, by decide⟩,
    C ⟨2, by decide⟩ ]

def cnfToRCNF {n : Nat} (Φ : CNF n) : RCNF n :=
  Φ.map clauseToRClause

structure TrailEntry (n : Nat) where
  lit        : Literal n
  level      : Nat
  antecedent : Option (RClause n)

abbrev Trail (n : Nat) := List (TrailEntry n)

structure State (n : Nat) where
  trail         : Trail n
  decisionLevel : Nat
  learnt        : RCNF n
  pending       : RCNF n
  conflict      : Option (RClause n)
  resSteps      : Nat

def litIsTrue {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = ℓ)

def litIsFalse {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = litNeg ℓ)

def unassignedLits {n : Nat} (τ : Trail n) (C : RClause n) :
    List (Literal n) :=
  C.filter (fun ℓ => !litIsTrue τ ℓ && !litIsFalse τ ℓ)

def findAntecedent {n : Nat} (τ : Trail n) (ℓ : Literal n) :
    Option (RClause n) :=
  match τ.find? (fun e => e.lit = ℓ) with
  | none      => none
  | some ent  => ent.antecedent

def litLevel {n : Nat} (τ : Trail n) (ℓ : Literal n) : Option Nat :=
  match τ.find? (fun e => e.lit = ℓ) with
  | none     => none
  | some ent => some ent.level

def litLevelDflt {n : Nat} (τ : Trail n) (ℓ : Literal n) : Nat :=
  match litLevel τ ℓ with
  | some l => l
  | none   => 0

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

def unitPropagate {n : Nat} (ΦR : RCNF n) (s : State n) : State n :=
  if h : s.conflict ≠ none then
    s
  else
    let clauses : List (RClause n) := ΦR ++ s.learnt ++ s.pending
    let τ := s.trail
    unitPropagateAux τ s clauses

def countLitsAtLevel {n : Nat}
    (τ : Trail n) (C : RClause n) (lvl : Nat) : Nat :=
  C.foldl
    (fun acc ℓ =>
      match litLevel τ ℓ with
      | some l =>
          if l = lvl then acc.succ else acc
      | none   => acc)
    0

def pickLitAtLevel? {n : Nat}
    (τ : Trail n) (C : RClause n) (lvl : Nat) :
    Option (Literal n) :=
  C.find? (fun ℓ =>
    match litLevel τ ℓ with
    | some l => l = lvl
    | none   => False)

structure AnalyzeResult (n : Nat) where
  learnt   : RClause n
  resSteps : Nat

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

def maxLevelInClause {n : Nat} (τ : Trail n) (C : RClause n) : Nat :=
  C.foldl (fun acc ℓ => Nat.max acc (litLevelDflt τ ℓ)) 0

def backtrackTrail {n : Nat} (τ : Trail n) (lvl : Nat) : Trail n :=
  τ.filter (fun e => e.level ≤ lvl)

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

def initState {n : Nat} (Φ : CNF n) : State n :=
  { trail         := []
    decisionLevel := 0
    learnt        := []
    pending       := cnfToRCNF Φ
    conflict      := none
    resSteps      := 0 }

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

def density (n : Nat) (s : State n) : Nat :=
  s.resSteps.succ

lemma density_pos (n : Nat)
    (Φ : CNF n) (ψ : ComputationPath (Model n) Φ)
    (t : Fin (ψ.T + 1)) :
    1 ≤ density n (ψ.states t) := by
  simp [density]

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

/-- 模拟记录：给定 Φ 和其 Resolution 反驳 π，构造 DPLL 轨迹 ψ，
    且 pathActionNat ≥ proofLength π。 -/
structure Simulation {n : Nat} (Φ : CNF n)
    (π : Resolution.Refutes (cnfToRCNF Φ)) where
  ψ  : ComputationPath (Model n) Φ
  hA : pathActionNat (Model n) Φ (density n) ψ
        ≥ Resolution.proofLength π

/-- 核心大猜想：存在这样的模拟（当前仍为 axiom）。 -/
axiom exists_simulation {n : Nat} (Φ : CNF n)
  (π : Resolution.Refutes (cnfToRCNF Φ)) :
  Simulation (Φ := Φ) (π := π)

end AbstractDPLL

------------------------------------------------------------
-- 11. HardFamily：Resolution-hard → DPLL-hard
------------------------------------------------------------

section HardFamilySchema

open Resolution
open AbstractDPLL

structure HardFamily where
  m : Nat → Nat
  F : ∀ n, CNF (m n)
  π : ∀ n, Resolution.Refutes (AbstractDPLL.cnfToRCNF (F n))

def resLengthSeq (H : HardFamily) : ActionSeq :=
  fun n => Resolution.proofLength (H.π n)

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

lemma expLower_lift_from_res_to_dpll
    (H : HardFamily)
    (hRes : ExpLower_2pow (resLengthSeq H)) :
    ExpLower_2pow (hardActionFromFamily H) := by
  intro n
  have h1 : (2 : Nat)^n ≤ resLengthSeq H n := hRes n
  have h2 : resLengthSeq H n ≤ hardActionFromFamily H n :=
    hardActionFromFamily_ge_resLength H n
  exact le_trans h1 h2

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

------------------------------------------------------------
-- 11.1 PHP 具体困难族实例 + 指数下界公理
------------------------------------------------------------

/-- 公理：对每个 n，PHP Tseitin 公式存在 Resolution 反驳。 -/
axiom PHP_resolution_refutation (n : Nat) :
  Resolution.Refutes (AbstractDPLL.cnfToRCNF (HardCNF_T n))

/-- PHP 对应的 HardFamily 实例。 -/
noncomputable
def PHP_HardFamily : HardFamily :=
  { m := HardVarT
    F := fun n => HardCNF_T n
    π := fun n => PHP_resolution_refutation n }

/-- 公理：PHP_HardFamily 的 Resolution 反驳长度族有指数下界。 -/
axiom PHP_resolution_expLower_2pow :
  ExpLower_2pow (resLengthSeq PHP_HardFamily)

/-- 主结论形式（针对 PHP 困难族）：DPLL 不可能在多项式作用量内解决。 -/
theorem no_polyTime_DPLL_on_PHP
    (hUpper : PolyUpper_general (hardActionFromFamily PHP_HardFamily)) :
    False :=
  no_polyTime_DPLL_on_HardFamily
    (H := PHP_HardFamily)
    (hRes := PHP_resolution_expLower_2pow)
    (hUpper := hUpper)

end HardFamilySchema

end StructuralAction








































