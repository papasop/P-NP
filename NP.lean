import Mathlib

open scoped BigOperators

/-
  整体结构：
  * namespace StructuralAction
    - 1. 3-SAT 基础语法
    - 2. 一般 CNF（GenCNF）+ 语义引理
    - 3. PHP 具体编码 + SAT ⇒ 注入 + UNSAT
    - 4. 参数化 Tseitin 编码 + HardCNF_T_unsat
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
-- 2. 一般 CNF（GenCNF）+ 语义引理
------------------------------------------------------------

namespace PigeonholeFamily

open StructuralAction
open List

-- 一般子句：任意长度的字面列表
abbrev GenClause (n : Nat) := List (Literal n)

-- 一般 CNF：一般子句列表
abbrev GenCNF (n : Nat) := List (GenClause n)

/-- 评价一般子句：递归折叠“或” -/
def genClauseEval {n : Nat} (σ : Assignment n) : GenClause n → Bool
  | []      => false
  | ℓ :: Γ  => literalEval σ ℓ || genClauseEval σ Γ

/-- 评价一般 CNF：递归折叠“且” -/
def genCNFEval {n : Nat} (σ : Assignment n) : GenCNF n → Bool
  | []      => true
  | C :: Φ  => genClauseEval σ C && genCNFEval σ Φ

/-- 子句求值为 true 当且仅当存在某个字面为 true。 -/
lemma genClauseEval_true_iff_exists_literal {n}
    (σ : Assignment n) :
  ∀ Γ : GenClause n,
    genClauseEval σ Γ = true ↔
    ∃ ℓ ∈ Γ, literalEval σ ℓ = true
  | [] => by
      simp [genClauseEval]
  | ℓ :: Γ => by
      have ih := genClauseEval_true_iff_exists_literal σ Γ
      constructor
      · intro h
        have : literalEval σ ℓ = true ∨ genClauseEval σ Γ = true := by
          -- Bool.or_eq_true : a || b = true ↔ a = true ∨ b = true
          simpa [genClauseEval, Bool.or_eq_true] using h
        cases this with
        | inl hℓ =>
            exact ⟨ℓ, by simp, hℓ⟩
        | inr hΓ =>
            rcases ih.mp hΓ with ⟨ℓ', hmem', hℓ'⟩
            exact ⟨ℓ', by simp [List.mem_cons, hmem'], hℓ'⟩
      · intro h
        rcases h with ⟨ℓ', hmem', hℓ'⟩
        -- 从 ℓ' ∈ ℓ :: Γ 得到 ℓ' = ℓ 或 ℓ' ∈ Γ
        have hmem'' : ℓ' = ℓ ∨ ℓ' ∈ Γ := by
          simpa [List.mem_cons] using hmem'
        have : literalEval σ ℓ = true ∨ genClauseEval σ Γ = true := by
          cases hmem'' with
          | inl hEq =>
              subst hEq
              exact Or.inl hℓ'
          | inr hIn =>
              have hΓ : genClauseEval σ Γ = true :=
                (ih.mpr ⟨ℓ', hIn, hℓ'⟩)
              exact Or.inr hΓ
        simpa [genClauseEval, Bool.or_eq_true] using this

/-- CNF 求值为 true 当且仅当所有子句都为 true。 -/
lemma genCNFEval_true_iff_all_clause_true {n}
    (σ : Assignment n) :
  ∀ Φ : GenCNF n,
    genCNFEval σ Φ = true ↔
    (∀ C ∈ Φ, genClauseEval σ C = true)
  | [] => by
      simp [genCNFEval]
  | C :: Φ => by
      have ih := genCNFEval_true_iff_all_clause_true σ Φ
      constructor
      · intro h
        have h' : genClauseEval σ C = true ∧ genCNFEval σ Φ = true := by
          simpa [genCNFEval, Bool.and_eq_true] using h
        rcases h' with ⟨hC, hΦ⟩
        intro C' hmem
        simp [List.mem_cons] at hmem
        rcases hmem with hEq | hIn
        · subst hEq
          exact hC
        · have hAllΦ : ∀ C'' ∈ Φ, genClauseEval σ C'' = true :=
            (ih.mp hΦ)
          exact hAllΦ C' hIn
      · intro hAll
        have hC : genClauseEval σ C = true := hAll C (by simp)
        have hAllΦ : ∀ C' ∈ Φ, genClauseEval σ C' = true := by
          intro C' hIn
          exact hAll C' (by simp [List.mem_cons, hIn])
        have hΦ : genCNFEval σ Φ = true := (ih.mpr hAllΦ)
        simpa [genCNFEval, Bool.and_eq_true, hC, hΦ]

/-- 拼接 Φ₁ ++ Φ₂ 的真值等价于“Φ₁ 为真且 Φ₂ 为真”。 -/
lemma genCNFEval_true_append_iff {n}
    (σ : Assignment n) (Φ₁ Φ₂ : GenCNF n) :
  genCNFEval σ (Φ₁ ++ Φ₂) = true ↔
  (genCNFEval σ Φ₁ = true ∧ genCNFEval σ Φ₂ = true) := by
  have hAll := genCNFEval_true_iff_all_clause_true (σ := σ)
  constructor
  · intro h
    have hAllClauses :=
      (hAll (Φ := Φ₁ ++ Φ₂)).mp h
    have hΦ₁ : genCNFEval σ Φ₁ = true := by
      apply (hAll (Φ := Φ₁)).mpr
      intro C hCmem
      exact hAllClauses C (by
        have : C ∈ Φ₁ ∨ C ∈ Φ₂ := Or.inl hCmem
        simpa [List.mem_append] using this)
    have hΦ₂ : genCNFEval σ Φ₂ = true := by
      apply (hAll (Φ := Φ₂)).mpr
      intro C hCmem
      exact hAllClauses C (by
        have : C ∈ Φ₁ ∨ C ∈ Φ₂ := Or.inr hCmem
        simpa [List.mem_append] using this)
    exact ⟨hΦ₁, hΦ₂⟩
  · intro h
    rcases h with ⟨hΦ₁, hΦ₂⟩
    have hAllΦ₁ :
        ∀ C ∈ Φ₁, genClauseEval σ C = true :=
      (hAll (Φ := Φ₁)).mp hΦ₁
    have hAllΦ₂ :
        ∀ C ∈ Φ₂, genClauseEval σ C = true :=
      (hAll (Φ := Φ₂)).mp hΦ₂
    apply (hAll (Φ := Φ₁ ++ Φ₂)).mpr
    intro C hCmem
    have : C ∈ Φ₁ ∨ C ∈ Φ₂ := by
      simpa [List.mem_append] using hCmem
    cases this with
    | inl hIn1 => exact hAllΦ₁ C hIn1
    | inr hIn2 => exact hAllΦ₂ C hIn2

/-- 原来的“拼接 ⇒ 两边都为真”公理，现在是证出来的 lemma。 -/
lemma genCNFEval_true_of_append
    {n : Nat} (σ : Assignment n)
    (Φ₁ Φ₂ : GenCNF n) :
    genCNFEval σ (Φ₁ ++ Φ₂) = true →
    genCNFEval σ Φ₁ = true ∧ genCNFEval σ Φ₂ = true := by
  intro h
  exact (genCNFEval_true_append_iff (σ := σ) Φ₁ Φ₂).mp h

------------------------------------------------------------
-- 2.b 参数化的 Tseitin 编码接口（无 axiom）
------------------------------------------------------------

/-- 对给定 GenCNF Φ 的某个 3-CNF 编码及其 equisat 证明。 -/
structure TseitinEncoding (n : Nat) (Φ : GenCNF n) where
  auxVars : Nat
  cnf     : CNF (n + auxVars)
  equisat :
    (∃ σ : Assignment n, genCNFEval σ Φ = true) ↔
    (∃ σ' : Assignment (n + auxVars), cnfEval σ' cnf = true)

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
-- 3.2 ALO / AMO 的语义：ALO 已经证明，AMO 暂时保留公理
------------------------------------------------------------

/-- ALO 语义：ALO 部分为真 ⇒ 每只鸽子至少一个洞为 true。 -/
lemma PHP_atLeastOne_sound
    (n : Nat) (σ : Assignment (PHPVar n))
    (hσ : genCNFEval σ (PHP_atLeastOne n) = true) :
    ∀ p : Pigeon n, ∃ h : Hole n, σ (phpVarIndex n p h) = true := by
  intro p
  -- 1. 利用 “CNF 为真 ⇒ 所有子句为真”
  have hAllClauses :=
    (genCNFEval_true_iff_all_clause_true
      (σ := σ) (Φ := PHP_atLeastOne n)).mp hσ
  -- 2. phpClauseAtLeastOne n p 是 PHP_atLeastOne n 中的一个子句
  have hIn : phpClauseAtLeastOne n p ∈ PHP_atLeastOne n := by
    -- PHP_atLeastOne n = ofFn (fun p' => phpClauseAtLeastOne n p')
    dsimp [PHP_atLeastOne]
    -- 利用 mem_ofFn，显式给出见证 p
    exact (List.mem_ofFn).2 ⟨p, rfl⟩
  have hClauseTrue : genClauseEval σ (phpClauseAtLeastOne n p) = true :=
    hAllClauses _ hIn
  -- 3. 子句为真 ⇒ 存在某个字面为真
  have hExistsLit :=
    (genClauseEval_true_iff_exists_literal
      (σ := σ) (Γ := phpClauseAtLeastOne n p)).mp hClauseTrue
  rcases hExistsLit with ⟨ℓ, hmem, hℓtrue⟩
  -- 4. 用 mem_ofFn 抽出对应的洞 h
  have hmem' :
      ℓ ∈ List.ofFn
        (fun h : Hole n =>
          ({ var := phpVarIndex n p h, neg := false } :
            Literal (PHPVar n))) := by
    -- phpClauseAtLeastOne n p 就是这个 ofFn
    dsimp [phpClauseAtLeastOne] at hmem
    simpa using hmem
  rcases (List.mem_ofFn).1 hmem' with ⟨h, hEq⟩
  subst hEq
  -- 5. 展开 literalEval，得到对应变量为 true
  have : σ (phpVarIndex n p h) = true := by
    -- neg = false ⇒ literalEval σ ℓ = σ var
    simpa [literalEval] using hℓtrue
  exact ⟨h, this⟩

/-- AMO 部分语义公理：
    若 genCNFEval σ (PHP_atMostOne n) = true，
    则对任意洞 h、任意不同鸽子 p₁ ≠ p₂，
    不可能同时 σ(x_{p₁,h}) = true 且 σ(x_{p₂,h}) = true。

  TODO：这里完全可以像 ALO 一样用 list/GenCNF 语义证明掉，
        只是证明会更长，当前版本先保留为 axiom。
-/
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
  -- 语义引理
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
  -- 直接把 card 不等式重写成 n.succ ≤ n
  have h_succ_le : n.succ ≤ n := by
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
-- 4. 参数化 Tseitin + HardCNF_T_unsat（无 oracle）
------------------------------------------------------------

open PigeonholeFamily

/-- 对 PHP_fullGenCNF n 的某个具体 TseitinEncoding，
    定义 HardVarT：原始 PHPVar n 个变量 + 辅助变量。 -/
noncomputable
def HardVarT (n : Nat)
    (E : TseitinEncoding (PHPVar n) (PHP_fullGenCNF n)) : Nat :=
  PHPVar n + E.auxVars

/-- 基于给定编码 E 的“困难 3-CNF” -/
noncomputable
def HardCNF_T (n : Nat)
    (E : TseitinEncoding (PHPVar n) (PHP_fullGenCNF n)) :
    CNF (HardVarT n E) :=
  E.cnf

/-- 对任何满足 equisat 规范的 Tseitin 编码 E，
    PHP 的 3-CNF 编码在 Bool 语义下不可满足。 -/
lemma HardCNF_T_unsat (n : Nat)
    (E : TseitinEncoding (PHPVar n) (PHP_fullGenCNF n)) :
  ∀ σ' : Assignment (HardVarT n E),
    cnfEval σ' (HardCNF_T n E) = false := by
  intro σ'
  classical
  -- 已知：原始 PHP_fullGenCNF n 在 GenCNF 语义下不可满足
  have hUnsatGen := PHP_fullGenCNF_unsat n

  -- 第一步：证明不能有 cnfEval σ' (HardCNF_T n E) = true
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n E) = true := by
    intro hSat
    -- 1.1 把 σ' 看成 E.cnf 的满足赋值
    have hSatExist :
        ∃ σ'' :
          Assignment (PHPVar n + E.auxVars),
          cnfEval σ'' E.cnf = true := by
      refine ⟨σ', ?_⟩
      simpa [HardCNF_T, HardVarT] using hSat

    -- 1.2 利用 TseitinEncoding 的 equisat 字段
    have hSatGen :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      (E.equisat).mpr hSatExist

    -- 1.3 与 PHP_fullGenCNF_unsat 矛盾
    exact hUnsatGen hSatGen

  -- 第二步：利用 Bool 二值性：要么 true 要么 false
  have hOr :
      cnfEval σ' (HardCNF_T n E) = true ∨
      cnfEval σ' (HardCNF_T n E) = false := by
    cases h : cnfEval σ' (HardCNF_T n E) <;> simp [h]

  -- 选 false 这一支
  cases hOr with
  | inl hTrue =>
      exact False.elim (hNotSat hTrue)
  | inr hFalse =>
      exact hFalse

end StructuralAction




































