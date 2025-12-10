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
  deriving Repr, DecidableEq   -- ★ 加上 DecidableEq，后面 Resolution / DPLL 需要

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
-- 3. 一般 CNF（变长子句）和 3-SAT 转换 to3CNF（旧版 padding）
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

-- 把一个变长子句 Γ 拆成若干个 3-子句列表（旧版 padding，不引入新变量）
def to3CNFClause {n : Nat} : GenClause n → List (StructuralAction.Clause n)
  | []        => []
  | [a]       => [mkClause3 a a a]
  | [a, b]    => [mkClause3 a a b]
  | [a, b, c] => [mkClause3 a b c]
  | a :: b :: c :: rest =>
      mkClause3 a b c :: to3CNFClause rest

------------------------------------------------------------
-- 3a. 单个子句的 3-SAT 转换：soundness（非空子句）
------------------------------------------------------------

lemma to3CNFClause_sound_nonempty
    {n : Nat} (σ : StructuralAction.Assignment n) :
  ∀ Γ : GenClause n,
    Γ ≠ [] →
    StructuralAction.cnfEval σ (to3CNFClause Γ) = true →
    genClauseEval σ Γ = true := by
  classical
  intro Γ hne h
  cases Γ with
  | nil =>
      cases hne rfl
  | cons a tail =>
      cases tail with
      | nil =>
          -- Γ = [a]
          have hTriple :
              StructuralAction.clauseEval σ (mkClause3 a a a) = true := by
            simpa [to3CNFClause, StructuralAction.cnfEval] using h
          have hLit :
              StructuralAction.literalEval σ a = true := by
            simpa [StructuralAction.clauseEval, mkClause3] using hTriple
          simpa [genClauseEval, hLit]
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              -- Γ = [a, b]
              have hTriple :
                  StructuralAction.clauseEval σ (mkClause3 a a b) = true := by
                simpa [to3CNFClause, StructuralAction.cnfEval] using h
              have hOr :
                  (StructuralAction.literalEval σ a
                    || StructuralAction.literalEval σ b) = true := by
                simpa [StructuralAction.clauseEval, mkClause3,
                       Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                  using hTriple
              simpa [genClauseEval,
                     Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                using hOr
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  -- Γ = [a, b, c]
                  have hTriple :
                      StructuralAction.clauseEval σ (mkClause3 a b c) = true := by
                    simpa [to3CNFClause, StructuralAction.cnfEval] using h
                  have hOr :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c) = true := by
                    simpa [StructuralAction.clauseEval, mkClause3] using hTriple
                  simpa [genClauseEval,
                         Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                    using hOr
              | cons d rest =>
                  -- Γ = a :: b :: c :: d :: rest  （长度 ≥ 4）
                  have hTriple :
                      StructuralAction.clauseEval σ (mkClause3 a b c) = true := by
                    have h' := h
                    simp [to3CNFClause, StructuralAction.cnfEval] at h'
                    exact h'.1
                  have hOr3 :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c) = true := by
                    simpa [StructuralAction.clauseEval, mkClause3,
                           Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                      using hTriple
                  have hOr4 :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c
                        || genClauseEval σ (d :: rest)) = true := by
                    have := congrArg
                      (fun b =>
                        b || genClauseEval σ (d :: rest)) hOr3
                    simpa [Bool.true_or, Bool.or_assoc] using this
                  have hShape :
                      genClauseEval σ (a :: b :: c :: d :: rest)
                        =
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c
                        || genClauseEval σ (d :: rest)) := by
                    simp [genClauseEval,
                          Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                  have := hOr4
                  simpa [hShape] using this

-- 旧版 3-SAT 转换：对每个一般子句做 to3CNFClause，然后拼接
def to3CNF {n : Nat} (Φ : GenCNF n) : StructuralAction.CNF n :=
  Φ.foldr (fun Γ acc => to3CNFClause Γ ++ acc) []

-- 3-CNF 转换的“满足性规格”：占位未来的严格证明（旧接口）
axiom to3CNF_equisat {n : Nat} (Φ : GenCNF n) :
  ∀ σ : StructuralAction.Assignment n,
    genCNFEval σ Φ = true ↔
    StructuralAction.cnfEval σ (to3CNF Φ) = true

------------------------------------------------------------
-- 3b. Tseitin 转换骨架 + Equisatisfiability 证明（骨架版）
------------------------------------------------------------

section Tseitin

-- Tseitin 转换的结果：
--   原公式有 n 个变量，Tseitin 之后有 n + auxVars 个变量，
--   并给出一个 3-CNF。
structure TseitinResult (n : Nat) where
  auxVars : Nat
  cnf     : StructuralAction.CNF (n + auxVars)

-- 把 Fin n 提升到 Fin (n + aux)
def liftFin {n aux : Nat} (i : Fin n) : Fin (n + aux) :=
  ⟨i.1, by
     have hi : i.1 < n := i.2
     have hle : n ≤ n + aux := Nat.le_add_right _ _
     exact Nat.lt_of_lt_of_le hi hle⟩

-- 把 Literal n 提升到 Literal (n + aux)
def liftLiteral {n aux : Nat}
    (ℓ : StructuralAction.Literal n) :
    StructuralAction.Literal (n + aux) :=
  { var := liftFin (n := n) (aux := aux) ℓ.var
  , neg := ℓ.neg }

-- 把 GenClause n 提升为 GenClause (n + aux)
def liftGenClause {n aux : Nat}
    (Γ : GenClause n) : GenClause (n + aux) :=
  Γ.map (fun ℓ => liftLiteral (n := n) (aux := aux) ℓ)

/- 真正的 Tseitin 会引入 fresh 变量。这里仍然用骨架占位： -/
noncomputable
def tseitinOfGenClause {n : Nat}
    (Γ : GenClause n) : TseitinResult n :=
  { auxVars := 0
  , cnf     := to3CNFClause Γ }

noncomputable
def tseitinOfGenCNF {n : Nat}
    (Φ : GenCNF n) : TseitinResult n :=
  { auxVars := 0
  , cnf     := to3CNF Φ }

/-- Tseitin 方向 1：GenCNF SAT ⇒ Tseitin CNF SAT -/
lemma tseitin_sat_of_genSat {n : Nat} (Φ : GenCNF n) :
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true)
  →
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) := by
  intro h
  classical
  rcases h with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  have hCnf : StructuralAction.cnfEval σ (to3CNF Φ) = true :=
    (to3CNF_equisat (Φ := Φ) (σ := σ)).mp hσ
  simpa [tseitinOfGenCNF] using hCnf

/-- Tseitin 方向 2：Tseitin CNF SAT ⇒ GenCNF SAT -/
lemma genSat_of_tseitin_sat {n : Nat} (Φ : GenCNF n) :
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true)
  →
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true) := by
  intro h
  classical
  rcases h with ⟨σ', hσ'⟩
  refine ⟨σ', ?_⟩
  have hGen : genCNFEval σ' Φ = true :=
    (to3CNF_equisat (Φ := Φ) (σ := σ')).mpr
      (by simpa [tseitinOfGenCNF] using hσ')
  exact hGen

end Tseitin

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

-- PHPₙ 的 3-SAT 编码（旧接口）：HardCNF = to3CNF (PHP_fullGenCNF)
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
-- 6'. 使用 Tseitin 版本的 HardCNF_T：PHP_fullGenCNF 经 Tseitin 的 3-CNF
------------------------------------------------------------

section PHPUnsatTseitin

open PigeonholeFamily

/-- Tseitin 之后 PHPₙ 的变量总数：
    原始 PHPVar n 个变量 + Tseitin 引入的辅助变量个数。 -/
noncomputable
def HardVarT (n : Nat) : Nat :=
  PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars

/-- Tseitin 版困难族公式：对 PHP_fullGenCNF 做 Tseitin 3-CNF 转换。 -/
noncomputable
def HardCNF_T (n : Nat) : CNF (HardVarT n) :=
  (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf

/-- Tseitin 版困难族公式不可满足： -/
lemma HardCNF_T_unsat (n : Nat) :
  ∀ σ' : Assignment (HardVarT n),
    cnfEval σ' (HardCNF_T n) = false := by
  intro σ'
  classical
  have hUnsatGen := PHP_fullGenCNF_unsat n
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n) = true := by
    intro hSat
    have hSatExist :
        ∃ σ'' : Assignment (PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars),
          cnfEval σ'' (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf = true := by
      refine ⟨σ', ?_⟩
      simpa [HardCNF_T, HardVarT] using hSat
    have hGenSat :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      genSat_of_tseitin_sat (Φ := PHP_fullGenCNF n) hSatExist
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
-- 7.5 提前声明：Resolution 系统的指数下界公理
------------------------------------------------------------

namespace Resolution

/-- （抽象形态）Resolution 对某些公式族的指数下界占位公理。 -/
axiom resolutionRefutation_expLower_2pow :
  ∃ (Len : StructuralAction.ActionSeq),
    StructuralAction.ExpLower_2pow Len

end Resolution

------------------------------------------------------------
-- 8. HardActionDPLL：从 Resolution 下界公理中“择取”出来的困难族作用量
------------------------------------------------------------

noncomputable
def HardActionDPLL : ActionSeq :=
  Classical.choose Resolution.resolutionRefutation_expLower_2pow

lemma HardActionDPLL_expLower_2pow :
  ExpLower_2pow HardActionDPLL :=
  Classical.choose_spec Resolution.resolutionRefutation_expLower_2pow

/-- 来自某个（未显式给出）DPLL / CDCL 算法的多项式上界：
    这里仍然是公理，占位你后续真正的“算法→多项式复杂度”证明。 -/
axiom HardActionDPLL_polyUpper_from_alg :
  PolyUpper_general HardActionDPLL

/-- 把指数下界 + 多项式上界拼在一起得到的“无多项式时间”矛盾。 -/
theorem no_polyTime_DPLL_on_hardFamily : False :=
  no_polyTime_on_family
    HardActionDPLL
    HardActionDPLL_expLower_2pow
    HardActionDPLL_polyUpper_from_alg

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
-- 10. Resolution 系统（修正版：RClause = List (Literal n)）
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

/-- Resolution 推导关系：
    注意返回值在 `Type` 中，这样我们可以在上面做一般递归
    （例如定义长度）。 -/
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

end Resolution

------------------------------------------------------------
-- 11. AbstractDPLL：带 decisionLevel / antecedent 的状态 + UnitProp 语义骨架
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
-- 11.2 Trail / State：加入 decisionLevel 与 antecedent
--------------------------------------------------

/-- Trail 中的一个条目：包含字面、决策层级以及产生它的前因子句。 -/
structure TrailEntry (n : Nat) where
  lit        : Literal n
  level      : Nat
  antecedent : Option (RClause n)

/-- 决策/传播轨迹：一串已经赋为 True 的字面（附带层级和前因）。 -/
abbrev Trail (n : Nat) := List (TrailEntry n)

/-- 抽象 DPLL 状态：
    * trail          : 当前决策 / 传播得到的字面轨迹
    * decisionLevel  : 当前决策层级
    * learnt         : 已学习子句（Resolution 视角下的派生子句）
    * pending        : 尚未处理 / 还在原公式里的子句
    * conflict       : 如果当前发现冲突，则存一个冲突子句（或 `[]`） -/
structure State (n : Nat) where
  trail         : Trail n
  decisionLevel : Nat
  learnt        : RCNF n
  pending       : RCNF n
  conflict      : Option (RClause n)

--------------------------------------------------
-- 11.3 辅助函数：在 trail 下判断字面真假 + unit 子句检测
--------------------------------------------------

/-- 字面 ℓ 是否在 trail 中被赋为 True（即 trail 里就有这个字面）。 -/
def litIsTrue {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = ℓ)

/-- 字面 ℓ 是否在 trail 下为 False（即 trail 中有它的否定）。 -/
def litIsFalse {n : Nat} (τ : Trail n) (ℓ : Literal n) : Bool :=
  τ.any (fun e => e.lit = litNeg ℓ)

/-- 在给定 trail 下，从子句 C 里收集“未赋值的字面”。 -/
def unassignedLits {n : Nat} (τ : Trail n) (C : RClause n) : List (Literal n) :=
  C.filter (fun ℓ => !litIsTrue τ ℓ && !litIsFalse τ ℓ)

--------------------------------------------------
-- 11.4 Unit Propagation：递归辅助 + 顶层函数
--------------------------------------------------

/-- Unit Propagation 的递归辅助函数：
    给定 trail τ、固定的状态 s 和一串子句列表，尝试做一次：
    * 如果发现某个子句在 τ 下：
      - 已满足：跳过；
      - 成为空子句（所有字面都为 False）：产生 conflict；
      - 是 unit 子句（恰好一个未赋值字面）：把该字面以 antecedent = 该子句 推入 trail；
      - 否则：继续看后面的子句。

    注意：这个版本最多执行一次“有效动作”（产生 conflict 或推一个 unit），
    找到第一个触发的子句就停下。 -/
def unitPropagateAux {n : Nat}
    (τ : Trail n) (s : State n) :
    List (RClause n) → State n
  | [] => s
  | C :: Cs =>
      -- 若 C 已在当前 trail 下满足，则忽略它
      if C.any (fun ℓ => litIsTrue τ ℓ) then
        unitPropagateAux τ s Cs
      else
        -- 否则，算出 C 中未赋值的字面集合
        let unassigned := unassignedLits τ C
        match unassigned with
        | [] =>
            -- 所有字面都为 False：产生一个 conflict 子句
            { s with conflict := some C }
        | [ℓ] =>
            -- 恰好一个未赋值字面：做一次 unit propagate
            let entry : TrailEntry n :=
              { lit        := ℓ
                level      := s.decisionLevel     -- 传播不提升决策层
                antecedent := some C }            -- 记录这个子句作为前因
            { s with trail := entry :: s.trail }
        | _ =>
            -- 还有多个未赋值字面，C 既不是冲突也不是 unit，继续扫后面的子句
            unitPropagateAux τ s Cs

/-- Unit Propagation：
    * 如果已经在 conflict 状态，则保持不变；
    * 否则，在 ΦR ∪ learnt ∪ pending 中做一次 unit propagation 探测。 -/
def unitPropagate {n : Nat} (ΦR : RCNF n) (s : State n) : State n :=
  if h : s.conflict ≠ none then
    -- 已经有 conflict，就不再做新的传播
    s
  else
    let clauses : List (RClause n) := ΦR ++ s.learnt ++ s.pending
    let τ := s.trail
    unitPropagateAux τ s clauses

--------------------------------------------------
-- 11.5 ConflictAnalyze / backtrack / decide
--------------------------------------------------

/-- Conflict Analyze：
    * 目标：当 conflict ≠ none 时，利用 Resolution 分析冲突，生成 learnt 子句；
    * 当前骨架：暂时不改变状态，只是占位。 -/
def conflictAnalyze {n : Nat} (ΦR : RCNF n) (s : State n) : State n :=
  -- TODO：若 s.conflict = some C，则在 trail 上做 UIP 分析，
  --       通过 Resolution 生成新的 learnt 子句，并清空 conflict 或做 backjump。
  s

/-- Backtrack：
    * 目标：根据冲突分析的结果回溯 trail（CDCL 的 backjump）；
    * 当前骨架：暂时直接返回原状态。 -/
def backtrack {n : Nat} (s : State n) : State n :=
  -- TODO：根据 learnt 子句中的决策层级，裁剪 trail 并调整 decisionLevel。
  s

/-- Decide：
    * 目标：在没有 unit / 冲突时，选择一个未赋值的变量做决策；
    * 实现：如果 pending 非空且其中首子句非空，取该子句的首字面为决策；
      提升 decisionLevel 并把决策写入 trail；
      否则保持不变。
    ★ 不再使用 `⟨0, by decide⟩`，避免出现 `0 < n` 的自由变量目标。 -/
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
            conflict      := s.conflict }

--------------------------------------------------
-- 11.6 抽象 DPLL 模型：用上述四个操作组合成一步 step
--------------------------------------------------

/-- 初始状态：trail 为空；决策层级 0；learnt 为空；pending = 原公式的 RCNF ；无冲突。 -/
def initState {n : Nat} (Φ : CNF n) : State n :=
  { trail         := []
    decisionLevel := 0
    learnt        := []
    pending       := cnfToRCNF Φ
    conflict      := none }

/-- 抽象 DPLL 模型：
    * init : 建立 initState；
    * step : unitPropagate → conflictAnalyze → backtrack → decide 的组合；
    * halting :
        - 要么 pending = []（公式“解决完了”）
        - 要么 conflict ≠ none（找到了冲突 / 反驳）。 -/
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
-- 11.7 结构密度 λ'：每一步至少付出 1 单位 Action
--------------------------------------------------

/-- 最简骨架版结构密度：
    * 每个状态的 cost = 1；
    * 未来可以升级为：
        - unitProp / resolve 步单独计价；
        - 让 Action 精确界面到 Resolution.proofLength。 -/
def density (n : Nat) (s : State n) : Nat := 1

--------------------------------------------------
-- 11.8 Resolution → DPLLPath 的“模拟骨架”（依赖指定 π）
--------------------------------------------------

/-- 一个“模拟记录”：给定 CNF Φ 及其 Resolution 反驳 π，
    构造 DPLL 计算路径 ψ，并证明
      pathActionNat ≥ proofLength π。 -/
structure Simulation {n : Nat} (Φ : CNF n)
    (π : Refutes (cnfToRCNF Φ)) where
  ψ  : ComputationPath (Model n) Φ
  hA : pathActionNat (Model n) Φ (density n) ψ
        ≥ proofLength π

/-- 存在模拟：Resolution 反驳 ⇒ 存在一条 DPLL 轨迹 ψ，
    使得 Action(ψ) ≥ proofLength(π)。

    ⭐ 当前仍然是公理（axiom），
       未来你的目标是把它变成真正的 theorem。 -/
axiom exists_simulation {n : Nat} (Φ : CNF n)
  (π : Refutes (cnfToRCNF Φ)) :
  Simulation (Φ := Φ) (π := π)

/-- 从给定的 Resolution 反驳 π 出发，构造一条对应的 DPLL 路径。 -/
noncomputable
def buildPathFromRefutation {n : Nat} (Φ : CNF n)
    (π : Refutes (cnfToRCNF Φ)) :
    ComputationPath (Model n) Φ :=
  (exists_simulation (Φ := Φ) (π := π)).ψ

/-- 关键不等式：沿着由 π 生成的路径，DPLL 的离散作用量
    至少等于该 Resolution 反驳的长度。 -/
lemma buildPathFromRefutation_action_ge_proofLength
    {n : Nat} (Φ : CNF n) (π : Refutes (cnfToRCNF Φ)) :
    proofLength π ≤
      pathActionNat (Model n) Φ (density n)
        (buildPathFromRefutation (Φ := Φ) (π := π)) := by
  have hA := (exists_simulation (Φ := Φ) (π := π)).hA
  simpa [buildPathFromRefutation] using hA

end AbstractDPLL

------------------------------------------------------------
-- 12. Resolution 生成的困难族 HardFamily → DPLL 作用量指数下界
------------------------------------------------------------

namespace ResolutionToDPLL

open StructuralAction
open Resolution
open AbstractDPLL

/-- 一个抽象的困难公式族：
    * m : 每个规模参数 n 对应的变量个数；
    * F n : 一个 CNF 公式，具有 m n 个变量；
    * π n : 对 cnfToRCNF (F n) 的 Resolution 反驳；
    * hExp : 反驳长度满足指数下界 2^n。 -/
structure HardFamily where
  m    : Nat → Nat
  F    : ∀ n : Nat, CNF (m n)
  π    : ∀ n : Nat, Refutes (cnfToRCNF (F n))
  hExp : ∀ n : Nat, (2 : Nat)^n ≤ proofLength (π n)

/-- 给定一个困难族 HardFamily，把对应的 DPLL 作用量
    定义成：在模型 Model (m n) 上，沿 buildPathFromRefutation 得到的路径的 Action。 -/
noncomputable
def hardActionFromFamily (H : HardFamily) : ActionSeq :=
  fun n =>
    let m := H.m n
    let Φ := H.F n
    let πn := H.π n
    let ψ := buildPathFromRefutation (Φ := Φ) (π := πn)
    pathActionNat (Model m) Φ (density m) ψ

lemma hardActionFromFamily_expLower_2pow (H : HardFamily) :
  ExpLower_2pow (hardActionFromFamily H) := by
  intro n
  -- 缩写一些符号
  let m := H.m n
  let Φ := H.F n
  let πn := H.π n
  have hExp' : (2 : Nat)^n ≤ proofLength πn := H.hExp n
  have hSim :
      proofLength πn ≤
        pathActionNat (Model m) Φ (density m)
          (buildPathFromRefutation (Φ := Φ) (π := πn)) :=
    buildPathFromRefutation_action_ge_proofLength
      (Φ := Φ) (π := πn)
  exact le_trans hExp' hSim

end ResolutionToDPLL

------------------------------------------------------------
-- 13. 把 HardFamily 具体化为：PHPₙ 的 Tseitin 3-CNF 困难族
------------------------------------------------------------

namespace PHPResolutionHard

open StructuralAction
open PigeonholeFamily
open Resolution
open AbstractDPLL
open ResolutionToDPLL

/-- 公理：PHPₙ 的 Tseitin 3-CNF HardCNF_T n 在 Resolution 系统中
    具有指数长的反驳（proofLength ≥ 2^n）。

    * 这里我们直接对每个 n 提供一个相应的反驳 π n，
      并要求其长度满足 2^n 下界。
    * 未来你如果真的构造出了这些反驳，可以把这个 axiom
      替换成真正的 theorem。 -/
axiom PHP_resolutionRefutation_expLower :
  ∀ n : Nat,
    ∃ π : Refutes (cnfToRCNF (HardCNF_T n)),
      (2 : Nat)^n ≤ proofLength π

/-- 利用上面的公理构造一个具体的 HardFamily，
    其中：
      * m n   = HardVarT n        （PHPₙ Tseitin 后的变量个数）
      * F n   = HardCNF_T n       （PHPₙ Tseitin 3-CNF）
      * π n   = 对 cnfToRCNF (HardCNF_T n) 的 Resolution 反驳
      * hExp  = proofLength (π n) ≥ 2^n。 -/
noncomputable
def PHPHardFamily : HardFamily :=
  { m    := HardVarT
    F    := fun n => HardCNF_T n
    π    := fun n => Classical.choose (PHP_resolutionRefutation_expLower n)
    hExp := by
      intro n
      have h := Classical.choose_spec (PHP_resolutionRefutation_expLower n)
      -- h : (2 : Nat)^n ≤ proofLength (Classical.choose (PHP_resolutionRefutation_expLower n))
      simpa using h }

/-- 对 PHPₙ 这族困难公式（HardCNF_T n），
    把 Resolution 指数 refutation 通过 Simulation
    提升为一个 DPLL 作用量的指数困难族。 -/
noncomputable
def HardActionDPLL_PHP : ActionSeq :=
  hardActionFromFamily PHPHardFamily

lemma HardActionDPLL_PHP_expLower_2pow :
  ExpLower_2pow HardActionDPLL_PHP :=
  hardActionFromFamily_expLower_2pow PHPHardFamily

end PHPResolutionHard

end StructuralAction





















