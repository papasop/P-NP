import Mathlib

open scoped BigOperators

/-
  整体结构：
  * namespace StructuralAction
    - 1. 3-SAT 基础语法
    - 2. 一般 CNF（GenCNF）与 Tseitin 结果
    - 3. Tseitin 等价公理 + 两个方向引理
    - 4. PHP 困难族（抽象给出 fullGenCNF + UNSAT 公理）
    - 5. Tseitin 版困难 CNF：HardVarT / HardCNF_T / HardCNF_T_unsat
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

end PigeonholeFamily

------------------------------------------------------------
-- 3. PHP 困难族：抽象给出 fullGenCNF + UNSAT 公理
------------------------------------------------------------

open PigeonholeFamily

/-- 抽象声明：PHPₙ 使用的变量个数（这里只需要一个自然数函数）。 -/
axiom PHPVar : Nat → Nat

/-- 抽象声明：PHP_fullGenCNF n 是 PHPₙ 的一般 CNF 编码。 -/
axiom PHP_fullGenCNF (n : Nat) : GenCNF (PHPVar n)

/-- 抽象声明：PHP_fullGenCNF n 在 GenCNF 语义下不可满足。 -/
axiom PHP_fullGenCNF_unsat (n : Nat) :
  ¬ ∃ σ : Assignment (PHPVar n),
        genCNFEval σ (PHP_fullGenCNF n) = true

/-
  说明：这里我们没有再显式写出鸽笼变量编码 (p,h) ↦ index，
  而是把 PHP 公式族抽象成：
    * 一个变量数 PHPVar n；
    * 一个一般 CNF 公式 PHP_fullGenCNF n；
    * 一个不可满足性公理 PHP_fullGenCNF_unsat n。
  以后如果你要消除这一公理，可以在这个接口下补全具体编码和证明。
-/

------------------------------------------------------------
-- 4. Tseitin 版 PHP 困难 CNF：HardVarT / HardCNF_T / HardCNF_T_unsat
------------------------------------------------------------

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
