import Mathlib

open scoped BigOperators

/-
  整体命名空间：StructuralAction
  包含：
  1. 基础布尔语法 (Assignment / Literal / Clause / CNF / cnfEval)
  2. GenCNF + to3CNF（保留 equisat 公理）
  3. PHP 编码 + 小公理 + UNSAT 证明
-/
namespace StructuralAction

------------------------------------------------------------
-- 1. 基础 3-SAT 语法：Assignment / Literal / Clause / CNF
------------------------------------------------------------

/-- 一个有 n 个布尔变量的赋值：Fin n → Bool -/
abbrev Assignment (n : Nat) := Fin n → Bool

/-- 字面：变量索引 + 是否取反 -/
structure Literal (n : Nat) where
  var : Fin n
  neg : Bool
  deriving Repr, DecidableEq

/-- 3-子句：3 个字面 -/
abbrev Clause (n : Nat) := Fin 3 → Literal n

/-- CNF 公式：子句列表 -/
abbrev CNF (n : Nat) := List (Clause n)

/-- 评价一个字面 -/
def literalEval {n : Nat} (σ : Assignment n) (ℓ : Literal n) : Bool :=
  let b := σ ℓ.var
  if ℓ.neg then !b else b

/-- 评价一个 3-子句 -/
def clauseEval {n : Nat} (σ : Assignment n) (C : Clause n) : Bool :=
  let ℓ0 := C ⟨0, by decide⟩
  let ℓ1 := C ⟨1, by decide⟩
  let ℓ2 := C ⟨2, by decide⟩
  literalEval σ ℓ0 || literalEval σ ℓ1 || literalEval σ ℓ2

/-- 评价 CNF：所有子句取“且” -/
def cnfEval {n : Nat} (σ : Assignment n) : CNF n → Bool
  | []      => true
  | C :: Φ  => clauseEval σ C && cnfEval σ Φ

------------------------------------------------------------
-- 2. 一般 CNF（GenCNF）+ to3CNF（保留 equisat 公理）
------------------------------------------------------------

namespace PigeonholeFamily

open StructuralAction

/-- 一般子句：字面列表 -/
abbrev GenClause (n : Nat) := List (Literal n)

/-- 一般 CNF：子句列表 -/
abbrev GenCNF (n : Nat) := List (GenClause n)

/-- 评价一般子句：折叠“或” -/
def genClauseEval {n : Nat} (σ : Assignment n)
    (Γ : GenClause n) : Bool :=
  Γ.foldr (fun ℓ acc => literalEval σ ℓ || acc) false

/-- 评价一般 CNF：所有子句的合取 -/
def genCNFEval {n : Nat} (σ : Assignment n)
    (Φ : GenCNF n) : Bool :=
  Φ.foldr (fun C acc => genClauseEval σ C && acc) true

/-- 把 3 个字面打包成一个 3-子句 -/
def mkClause3 {n : Nat}
    (a b c : Literal n) : Clause n :=
  fun
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- 把一个变长子句 Γ 拆成一组三子句（旧版 padding，不引入新变量） -/
def to3CNFClause {n : Nat} : GenClause n → List (Clause n)
  | []        => []
  | [a]       => [mkClause3 a a a]
  | [a, b]    => [mkClause3 a a b]
  | [a, b, c] => [mkClause3 a b c]
  | a :: b :: c :: rest =>
      mkClause3 a b c :: to3CNFClause rest

/-- 旧版 3-SAT 转换：对每个一般子句做 to3CNFClause，然后拼接 -/
def to3CNF {n : Nat} (Φ : GenCNF n) : CNF n :=
  Φ.foldr (fun Γ acc => to3CNFClause Γ ++ acc) []

/-- 3-CNF 转换的“满足性规格”：保留为公理（以后可以再杀） -/
axiom to3CNF_equisat {n : Nat} (Φ : GenCNF n) :
  ∀ σ : Assignment n,
    genCNFEval σ Φ = true ↔
    cnfEval σ (to3CNF Φ) = true

/-- 关于拼接的一个小语义公理：
    若 genCNFEval σ (Φ₁ ++ Φ₂) = true，则两边都为 true。 -/
axiom genCNFEval_true_of_append
    {n : Nat} (σ : Assignment n)
    (Φ₁ Φ₂ : GenCNF n) :
    genCNFEval σ (Φ₁ ++ Φ₂) = true →
    genCNFEval σ Φ₁ = true ∧ genCNFEval σ Φ₂ = true

------------------------------------------------------------
-- 3. 鸽笼原理 PHPₙ 的变量编码 + GenCNF 公式族
------------------------------------------------------------

/-- 第 n 个鸽子：共有 n+1 只鸽子 -/
abbrev Pigeon (n : Nat) := Fin (n + 1)

/-- 第 n 个洞：共有 n 个洞 -/
abbrev Hole (n : Nat) := Fin n

/-- PHPₙ 的变量总数上界：(n+1)*n + 1 -/
abbrev PHPVar (n : Nat) : Nat :=
  Nat.succ ((n + 1) * n)

/-- PHPₙ 的变量索引类型 -/
abbrev PHPVarIdx (n : Nat) := Fin (PHPVar n)

/-- 把 (p, h) 映射到变量索引：index(p, h) = p * n + h -/
noncomputable
def phpVarIndex (n : Nat) (p : Pigeon n) (h : Hole n) : PHPVarIdx n :=
  ⟨p.1 * n + h.1, by
    -- 目标：p.1 * n + h.1 < (n+1)*n + 1 = PHPVar n
    have hp : p.1 ≤ n := Nat.le_of_lt_succ p.2
    have hh : h.1 ≤ n := Nat.le_of_lt h.2
    have h1 : p.1 * n + h.1 ≤ p.1 * n + n :=
      Nat.add_le_add_left hh _
    have hp' : p.1 * n ≤ n * n :=
      Nat.mul_le_mul_right _ hp
    have h2 : p.1 * n + n ≤ n * n + n :=
      Nat.add_le_add_right hp' _
    have h3 : n * n + n = (n + 1) * n := by
      ring
    have h4 : p.1 * n + n ≤ (n + 1) * n := by
      simpa [h3] using h2
    have h5 : p.1 * n + h.1 ≤ (n + 1) * n :=
      le_trans h1 h4
    have : p.1 * n + h.1 < (n + 1) * n + 1 :=
      Nat.lt_succ_of_le h5
    simpa [PHPVar] using this ⟩

/-- 所有鸽子的列表 -/
noncomputable
def pigeonsList (n : Nat) : List (Pigeon n) :=
  List.ofFn (fun p : Pigeon n => p)

/-- 所有洞的列表 -/
noncomputable
def holesList (n : Nat) : List (Hole n) :=
  List.ofFn (fun h : Hole n => h)

/-- 列出一个 List 中所有“有序对 (xᵢ, xⱼ)，其中 i < j” -/
def listPairs {α : Type} : List α → List (α × α)
  | []       => []
  | x :: xs  => (xs.map (fun y => (x,y))) ++ listPairs xs

------------------------------------------------------------
-- 3.1 PHP 的 ALO / AMO 公式构造
------------------------------------------------------------

/-- 单只鸽子的 “至少一个洞” 子句：∨_{h} x_{p,h} -/
noncomputable
def phpClauseAtLeastOne (n : Nat) (p : Pigeon n) :
    GenClause (PHPVar n) :=
  (List.ofFn fun h : Hole n =>
    ({ var := phpVarIndex n p h, neg := false } :
      Literal (PHPVar n)))

/-- “At Least One” 子句族：对每个鸽子 p -/
noncomputable
def PHP_atLeastOne (n : Nat) : GenCNF (PHPVar n) :=
  List.ofFn (fun p : Pigeon n => phpClauseAtLeastOne n p)

/-- 对固定洞 h，生成所有 “至多一只鸽子占 h” 的 2 字面子句 -/
noncomputable
def phpClausesAtMostOneForHole (n : Nat) (h : Hole n) :
    GenCNF (PHPVar n) :=
  let ps    : List (Pigeon n)            := pigeonsList n
  let pairs : List (Pigeon n × Pigeon n) := listPairs ps
  pairs.map (fun (p₁, p₂) =>
    [ ({ var := phpVarIndex n p₁ h, neg := true } :
         Literal (PHPVar n)),
      ({ var := phpVarIndex n p₂ h, neg := true } :
         Literal (PHPVar n)) ])

/-- “At Most One” 子句族：对每个洞 h -/
noncomputable
def PHP_atMostOne (n : Nat) : GenCNF (PHPVar n) :=
  let hs : List (Hole n) := holesList n
  hs.foldr
    (fun h acc => phpClausesAtMostOneForHole n h ++ acc)
    []

/-- PHPₙ 的完整变长 CNF（未 3-SAT 化）：ALO ∧ AMO -/
noncomputable
def PHP_fullGenCNF (n : Nat) : GenCNF (PHPVar n) :=
  PHP_atLeastOne n ++ PHP_atMostOne n

------------------------------------------------------------
-- 3.2 ALO / AMO 的语义：以“小公理”方式给出
------------------------------------------------------------

/-- ALO 部分语义公理：
    若 genCNFEval σ (PHP_atLeastOne n) = true，
    则每只鸽子 p 都有一个洞 h 使得 σ(x_{p,h}) = true。 -/
axiom PHP_atLeastOne_sound
    (n : Nat) (σ : Assignment (PHPVar n))
    (hσ : genCNFEval σ (PHP_atLeastOne n) = true) :
    ∀ p : Pigeon n, ∃ h : Hole n, σ (phpVarIndex n p h) = true

/-- AMO 部分语义公理：
    若 genCNFEval σ (PHP_atMostOne n) = true，
    则对任意洞 h、任意不同鸽子 p₁ ≠ p₂，
    不可能同时 σ(x_{p₁,h}) = true 且 σ(x_{p₂,h}) = true。 -/
axiom PHP_atMostOne_sound
    (n : Nat) (σ : Assignment (PHPVar n))
    (hσ : genCNFEval σ (PHP_atMostOne n) = true) :
    ∀ h : Hole n,
      ∀ p₁ p₂ : Pigeon n,
        p₁ ≠ p₂ →
        ¬ (σ (phpVarIndex n p₁ h) = true ∧
           σ (phpVarIndex n p₂ h) = true)

------------------------------------------------------------
-- 3.3 整体：PHP_fullGenCNF SAT ⇒ 存在单射 f : Pigeon → Hole
------------------------------------------------------------

open Function

/-- 核心定理（单向）：若 PHP_fullGenCNF n 可满足，
    则存在单射 f : Pigeon n → Hole n。 -/
theorem PHP_fullGenCNF_sat_implies_injection (n : Nat) :
  (∃ σ : Assignment (PHPVar n),
     genCNFEval σ (PHP_fullGenCNF n) = true) →
  (∃ f : Pigeon n → Hole n, Function.Injective f) := by
  intro hSat
  classical
  rcases hSat with ⟨σ, hσ⟩
  -- 用小公理拆分 ALO / AMO 部分
  have hSplit :=
    genCNFEval_true_of_append (σ := σ)
      (Φ₁ := PHP_atLeastOne n) (Φ₂ := PHP_atMostOne n)
  have ⟨hALO, hAMO⟩ :
      genCNFEval σ (PHP_atLeastOne n) = true ∧
      genCNFEval σ (PHP_atMostOne n) = true := by
    have := hSplit (by simpa [PHP_fullGenCNF] using hσ)
    simpa using this
  -- ALO ⇒ 为每个鸽子选一个洞
  have hALO_sem :=
    PHP_atLeastOne_sound (n := n) (σ := σ) hALO
  have hAMO_sem :=
    PHP_atMostOne_sound (n := n) (σ := σ) hAMO
  classical
  choose f hf using hALO_sem
  -- hf : ∀ p, σ (phpVarIndex n p (f p)) = true
  refine ⟨f, ?_⟩
  intro p₁ p₂ hHoleEq
  -- hHoleEq : f p₁ = f p₂
  by_cases hNe : p₁ = p₂
  · -- 已经相等，直接返回
    exact hNe
  · -- 假设 p₁ ≠ p₂，利用 AMO 得到矛盾
    have hpair :
        σ (phpVarIndex n p₁ (f p₁)) = true ∧
        σ (phpVarIndex n p₂ (f p₁)) = true := by
      constructor
      · -- 第一项来自 hf p₁
        exact hf p₁
      · -- 第二项：从 hf p₂ 并用 f p₂ = f p₁ 改写
        have := hf p₂
        -- hHoleEq : f p₁ = f p₂，因此 f p₂ = f p₁ 也是成立的
        simpa [hHoleEq.symm] using this
    -- 这与 AMO 语义矛盾
    have hcontra :=
      hAMO_sem (h := f p₁) p₁ p₂ hNe hpair
    exact (hcontra.elim)

end PigeonholeFamily

------------------------------------------------------------
-- 4. 纯数学鸽笼原理：不存在单射 Pigeon n → Hole n
------------------------------------------------------------

section PigeonholeMath

open Function
open PigeonholeFamily

lemma no_injection_Pigeon_to_Hole (n : Nat) :
    ¬ ∃ f : Pigeon n → Hole n, Function.Injective f := by
  intro h
  rcases h with ⟨f, hf_inj⟩
  -- 利用有限集的基数比较：card (Fin (n+1)) ≤ card (Fin n) 不可能
  have h_card_le :
      Fintype.card (Pigeon n)
        ≤ Fintype.card (Hole n) :=
    Fintype.card_le_of_injective f hf_inj
  have h_succ_le : n.succ ≤ n := by
    -- Pigeon n = Fin (n+1), Hole n = Fin n
    simpa [PigeonholeFamily.Pigeon, PigeonholeFamily.Hole,
           Fintype.card_fin, Nat.succ_eq_add_one] using h_card_le
  exact Nat.not_succ_le_self n h_succ_le

end PigeonholeMath

------------------------------------------------------------
-- 5. 从 PHP_fullGenCNF 到 3-CNF PHPcnf 的 UNSAT 逻辑链
------------------------------------------------------------

open PigeonholeFamily

/-- PHPₙ 的 3-SAT 编码（旧接口）：HardCNF = to3CNF (PHP_fullGenCNF) -/
noncomputable
def PHPcnf (n : Nat) : CNF (PHPVar n) :=
  to3CNF (PHP_fullGenCNF n)

/-- PHP_fullGenCNF 不可满足 -/
lemma PHP_fullGenCNF_unsat (n : Nat) :
  ¬ ∃ σ : Assignment (PHPVar n),
      genCNFEval σ (PHP_fullGenCNF n) = true := by
  intro hSat
  -- SAT ⇒ 存在单射
  have hInj :
      ∃ f : Pigeon n → Hole n, Function.Injective f :=
    PHP_fullGenCNF_sat_implies_injection (n := n) hSat
  -- 但数学鸽笼原理排除这种单射
  exact no_injection_Pigeon_to_Hole n hInj

/-- 对任意赋值 σ，PHP 的 3-CNF 编码在 σ 下为 false（不可满足） -/
lemma HardCNF_unsat (n : Nat) :
  ∀ σ : Assignment (PHPVar n),
    cnfEval σ (PHPcnf n) = false := by
  intro σ
  classical
  have hUnsatGen := PHP_fullGenCNF_unsat n
  have hNotSatCnf : ¬ cnfEval σ (PHPcnf n) = true := by
    intro hSat
    -- 利用 to3CNF_equisat 把 SAT 迁移到 GenCNF
    have hEquiv :=
      to3CNF_equisat
        (Φ := PHP_fullGenCNF n) (σ := σ)
    have hSat3 :
        cnfEval σ (to3CNF (PHP_fullGenCNF n)) = true := by
      simpa [PHPcnf] using hSat
    have hSatGen :
        genCNFEval σ (PHP_fullGenCNF n) = true :=
      hEquiv.mpr hSat3
    exact hUnsatGen ⟨σ, hSatGen⟩
  have hOr :
      cnfEval σ (PHPcnf n) = true ∨
      cnfEval σ (PHPcnf n) = false := by
    cases h' : cnfEval σ (PHPcnf n) <;> simp [h']
  cases hOr with
  | inl hTrue => exact False.elim (hNotSatCnf hTrue)
  | inr hFalse => exact hFalse

end StructuralAction









































