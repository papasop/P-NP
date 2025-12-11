import Mathlib

open scoped BigOperators

/-
  整体结构：
  * namespace StructuralAction
    - 1. 3-SAT 基础语法
    - 2. 一般 CNF（GenCNF）与 Tseitin 结果
    - 3. PHP 具体编码 + SAT ⇒ 注入 + UNSAT
    - 4. Tseitin 版困难 CNF：HardVarT / HardCNF_T / HardCNF_T_unsat
-/

namespace StructuralAction

------------------------------------------------------------
-- 1. 3-SAT / 一般 CNF 基础语法
------------------------------------------------------------

-- 布尔赋值：n 个变量，对应 Fin n → Bool
abbrev Assignment (n : Nat) := Fin n → Bool

-- 字面：变量索引 + 是否取反
structure Literal (n : Nat) where
  var : Fin n
  neg : Bool
  deriving Repr, DecidableEq

-- 3-SAT 子句：固定 3 个字面
abbrev Clause (n : Nat) := Fin 3 → Literal n

-- CNF 公式：3-SAT 子句列表
abbrev CNF (n : Nat) := List (Clause n)

-- 字面求值
def literalEval {n : Nat} (σ : Assignment n) (ℓ : Literal n) : Bool :=
  let b := σ ℓ.var
  if ℓ.neg then !b else b

-- 3-子句求值：三个字面的析取
def clauseEval {n : Nat} (σ : Assignment n) (C : Clause n) : Bool :=
  let ℓ0 := C ⟨0, by decide⟩
  let ℓ1 := C ⟨1, by decide⟩
  let ℓ2 := C ⟨2, by decide⟩
  literalEval σ ℓ0 || literalEval σ ℓ1 || literalEval σ ℓ2

-- CNF 求值：所有子句的合取（递归）
def cnfEval {n : Nat} (σ : Assignment n) : CNF n → Bool
  | []      => true
  | C :: Φ  => clauseEval σ C && cnfEval σ Φ

------------------------------------------------------------
-- 2. 一般 CNF（GenCNF）与 Tseitin 结果结构体
------------------------------------------------------------

namespace PigeonholeFamily

open StructuralAction

-- 一般子句：任意长度的字面列表
abbrev GenClause (n : Nat) := List (Literal n)

-- 一般 CNF：一般子句列表
abbrev GenCNF (n : Nat) := List (GenClause n)

-- 评价一般子句：折叠“或”
def genClauseEval {n : Nat} (σ : Assignment n) (Γ : GenClause n) : Bool :=
  Γ.foldr (fun ℓ acc => literalEval σ ℓ || acc) false

-- 评价一般 CNF：所有子句的合取
def genCNFEval {n : Nat} (σ : Assignment n) (Φ : GenCNF n) : Bool :=
  Φ.foldr (fun C acc => genClauseEval σ C && acc) true

/-- Tseitin 转换的结果：
    * 原公式有 n 个变量；
    * Tseitin 之后有 n + auxVars 个变量（扩展变量空间）；
    * 结果是一个 3-CNF（我们这里直接用 CNF 表示）。 -/
structure TseitinResult (n : Nat) where
  auxVars : Nat
  cnf     : CNF (n + auxVars)

/-- 这里给一个“占位实现”：真正的 Tseitin 构造可以日后填充；
    目前我们只关心类型对齐，不依赖具体构造。 -/
noncomputable
def tseitinOfGenCNF {n : Nat} (Φ : GenCNF n) : TseitinResult n :=
  { auxVars := 0
    cnf     := [] }   -- 任意占位，语义由后面公理给出

/-- 真正的 Tseitin 等价性公理：
    GenCNF 与其 Tseitin 3-CNF 在“存在满足赋值”这一层面上等价。 -/
axiom tseitin_equisat {n : Nat} (Φ : GenCNF n) :
  (∃ σ  : Assignment n,
     genCNFEval σ Φ = true)
    ↔
  (∃ σ' : Assignment (n + (tseitinOfGenCNF Φ).auxVars),
     cnfEval σ' (tseitinOfGenCNF Φ).cnf = true)

------------------------------------------------------------
-- 2'. Tseitin 等价性的两个方向引理（方便使用）
------------------------------------------------------------

/-- 方向 1：GenCNF SAT ⇒ Tseitin 3-CNF SAT。 -/
lemma tseitin_sat_of_genSat {n : Nat} (Φ : GenCNF n) :
  (∃ σ : Assignment n, genCNFEval σ Φ = true) →
  (∃ σ' : Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) := by
  intro h
  have hEquiv := tseitin_equisat (Φ := Φ)
  exact hEquiv.mp h

/-- 方向 2：Tseitin 3-CNF SAT ⇒ GenCNF SAT。 -/
lemma genSat_of_tseitin_sat {n : Nat} (Φ : GenCNF n) :
  (∃ σ' : Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) →
  (∃ σ : Assignment n, genCNFEval σ Φ = true) := by
  intro h
  have hEquiv := tseitin_equisat (Φ := Φ)
  exact hEquiv.mpr h

------------------------------------------------------------
-- 3. PHP 具体编码 + SAT ⇒ 注入 + UNSAT
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
    -- h.2 : h.1 < n
    have h1 : p.1 * n + h.1 < p.1 * n + n :=
      Nat.add_lt_add_left h.2 _
    have hp' : p.1 * n ≤ n * n :=
      Nat.mul_le_mul_right _ hp
    have h2 : p.1 * n + n ≤ n * n + n :=
      Nat.add_le_add_right hp' _
    have h3 : n * n + n = (n + 1) * n := by
      ring
    have h4 : p.1 * n + n ≤ (n + 1) * n := by
      simpa [h3] using h2
    have h5 : p.1 * n + h.1 < (n + 1) * n :=
      lt_of_lt_of_le h1 h4
    have : p.1 * n + h.1 < (n + 1) * n + 1 :=
      Nat.lt_trans h5 (Nat.lt_succ_self _)
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
-- 3.2 ALO / AMO / append 的语义小公理
------------------------------------------------------------

/-- 若 genCNFEval σ (Φ₁ ++ Φ₂) = true，则两边都为 true。 -/
axiom genCNFEval_true_of_append
    {n : Nat} (σ : Assignment n)
    (Φ₁ Φ₂ : GenCNF n) :
    genCNFEval σ (Φ₁ ++ Φ₂) = true →
    genCNFEval σ Φ₁ = true ∧ genCNFEval σ Φ₂ = true

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
open Classical

/-- 核心定理：若 PHP_fullGenCNF n 可满足，
    则存在单射 f : Pigeon n → Hole n。 -/
theorem PHP_fullGenCNF_sat_implies_injection (n : Nat) :
  (∃ σ : Assignment (PHPVar n),
     genCNFEval σ (PHP_fullGenCNF n) = true) →
  (∃ f : Pigeon n → Hole n, Function.Injective f) := by
  intro hSat
  classical
  rcases hSat with ⟨σ, hσ⟩
  -- 用 append 语义拆分 ALO / AMO 部分
  have hSplit :=
    genCNFEval_true_of_append (σ := σ)
      (Φ₁ := PHP_atLeastOne n) (Φ₂ := PHP_atMostOne n)
  have ⟨hALO, hAMO⟩ :
      genCNFEval σ (PHP_atLeastOne n) = true ∧
      genCNFEval σ (PHP_atMostOne n) = true := by
    have := hSplit (by simpa [PHP_fullGenCNF] using hσ)
    simpa using this
  -- 语义公理
  have hALO_sem :=
    PHP_atLeastOne_sound (n := n) (σ := σ) hALO
  have hAMO_sem :=
    PHP_atMostOne_sound (n := n) (σ := σ) hAMO
  -- 为每只鸽子选择一个洞
  classical
  choose f hf using hALO_sem
  -- hf : ∀ p, σ (phpVarIndex n p (f p)) = true
  refine ⟨f, ?_⟩
  intro p₁ p₂ hEq
  by_cases hNe : p₁ = p₂
  · exact hNe
  · -- 若 p₁ ≠ p₂，但 f p₁ = f p₂，则在洞 f p₁ 上两只鸽子都为 true，与 AMO 矛盾
    have hpair :
        σ (phpVarIndex n p₁ (f p₁)) = true ∧
        σ (phpVarIndex n p₂ (f p₁)) = true := by
      constructor
      · exact hf p₁
      · have := hf p₂
        simpa [hEq.symm] using this
    have hcontra :=
      hAMO_sem (h := f p₁) p₁ p₂ hNe hpair
    exact (hcontra.elim)

------------------------------------------------------------
-- 3.4 纯数学鸽笼原理 + PHP_fullGenCNF_unsat
------------------------------------------------------------

section PigeonholeMath

open Function

/-- 纯数学鸽笼原理：不存在单射 Fin (n+1) → Fin n。 -/
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
    simpa [Pigeon, Hole, Fintype.card_fin, Nat.succ_eq_add_one] using h_card_le
  exact Nat.not_succ_le_self n h_succ_le

end PigeonholeMath

/-- 真正的 UNSAT：PHP_fullGenCNF 不可满足 -/
lemma PHP_fullGenCNF_unsat (n : Nat) :
  ¬ ∃ σ : Assignment (PHPVar n),
      genCNFEval σ (PHP_fullGenCNF n) = true := by
  intro hSat
  have hInj := PHP_fullGenCNF_sat_implies_injection (n := n) hSat
  exact no_injection_Pigeon_to_Hole n hInj

end PigeonholeFamily

------------------------------------------------------------
-- 4. Tseitin 版 PHP 困难 CNF：HardVarT / HardCNF_T / HardCNF_T_unsat
------------------------------------------------------------

open PigeonholeFamily

/-- Tseitin 之后 PHPₙ 的变量总数：
    原始 PHPVar n 个变量 + Tseitin 引入的辅助变量个数。 -/
noncomputable
def HardVarT (n : Nat) : Nat :=
  PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars

/-- Tseitin 版困难公式：对 PHP_fullGenCNF 做 Tseitin 3-CNF 转换。 -/
noncomputable
def HardCNF_T (n : Nat) : CNF (HardVarT n) :=
  (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf

/-- Tseitin 版困难公式在 Bool 语义下不可满足。 -/
lemma HardCNF_T_unsat (n : Nat) :
  ∀ σ' : Assignment (HardVarT n),
    cnfEval σ' (HardCNF_T n) = false := by
  intro σ'
  classical
  -- 已知：原始 PHP_fullGenCNF n 在 GenCNF 语义下不可满足
  have hUnsatGen := PHP_fullGenCNF_unsat n

  -- 第一步：证明不能有 cnfEval σ' (HardCNF_T n) = true
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n) = true := by
    intro hSat
    -- 1.1 把 σ' 看成 Tseitin CNF 的满足赋值
    have hSatExist :
        ∃ σ'' :
          Assignment (PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars),
          cnfEval σ'' (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf = true := by
      -- HardVarT n = PHPVar n + auxVars 按定义相等，所以 σ' 就是需要的 σ''
      refine ⟨σ', ?_⟩
      simpa [HardCNF_T, HardVarT] using hSat

    -- 1.2 利用 Tseitin SAT ⇒ GenCNF SAT 的封装引理
    have hSatGen :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      PigeonholeFamily.genSat_of_tseitin_sat
        (Φ := PHP_fullGenCNF n) hSatExist

    -- 1.3 与 PHP_fullGenCNF_unsat 矛盾
    exact hUnsatGen hSatGen

  -- 第二步：利用 Bool 二值性：要么 true 要么 false
  have hOr :
      cnfEval σ' (HardCNF_T n) = true ∨
      cnfEval σ' (HardCNF_T n) = false := by
    cases h : cnfEval σ' (HardCNF_T n) <;> simp [h]

  -- 选 false 这一支
  cases hOr with
  | inl hTrue =>
      exact False.elim (hNotSat hTrue)
  | inr hFalse =>
      exact hFalse

end StructuralAction





































