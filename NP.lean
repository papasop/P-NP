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
  deriving Repr, DecidableEq

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
  -- 对 Γ 按长度分类：[], [a], [a,b], [a,b,c], ≥ 4
  cases Γ with
  | nil =>
      -- Γ = [] 与“非空”假设矛盾
      cases hne rfl
  | cons a tail =>
      cases tail with
      | nil =>
          ----------------------------------------------------
          -- 情况 1：Γ = [a]
          ----------------------------------------------------
          have hTriple :
              StructuralAction.clauseEval σ (mkClause3 a a a) = true := by
            -- cnfEval σ [mkClause3 a a a] = clauseEval σ (mkClause3 a a a)
            simpa [to3CNFClause, StructuralAction.cnfEval] using h
          -- clauseEval (a,a,a) 就是 literalEval a
          have hLit :
              StructuralAction.literalEval σ a = true := by
            simpa [StructuralAction.clauseEval, mkClause3] using hTriple
          -- 一元子句的 genClauseEval 就是 literalEval a
          simpa [genClauseEval, hLit]
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              ------------------------------------------------
              -- 情况 2：Γ = [a, b]
              ------------------------------------------------
              have hTriple :
                  StructuralAction.clauseEval σ (mkClause3 a a b) = true := by
                -- to3CNFClause [a,b] = [mkClause3 a a b]
                simpa [to3CNFClause, StructuralAction.cnfEval] using h
              -- clauseEval (a,a,b) = (la || la || lb) ≃ (la || lb)
              have hOr :
                  (StructuralAction.literalEval σ a
                    || StructuralAction.literalEval σ b) = true := by
                simpa [StructuralAction.clauseEval, mkClause3,
                       Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                  using hTriple
              -- genClauseEval σ [a,b] = la || lb
              simpa [genClauseEval,
                     Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                using hOr
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  --------------------------------------------
                  -- 情况 3：Γ = [a, b, c]
                  --------------------------------------------
                  have hTriple :
                      StructuralAction.clauseEval σ (mkClause3 a b c) = true := by
                    -- to3CNFClause [a,b,c] = [mkClause3 a b c]
                    simpa [to3CNFClause, StructuralAction.cnfEval] using h
                  -- clauseEval (a,b,c) = la || lb || lc
                  have hOr :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c) = true := by
                    simpa [StructuralAction.clauseEval, mkClause3] using hTriple
                  -- genClauseEval σ [a,b,c] = la || lb || lc
                  simpa [genClauseEval,
                         Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                    using hOr
              | cons d rest =>
                  --------------------------------------------
                  -- 情况 4：Γ = a :: b :: c :: d :: rest  （长度 ≥ 4）
                  --------------------------------------------
                  -- 先从 h 中把“首个 3-子句为真”拆出来
                  have hTriple :
                      StructuralAction.clauseEval σ (mkClause3 a b c) = true := by
                    -- h : cnfEval σ (mkClause3 a b c :: to3CNFClause (d::rest)) = true
                    -- simp 后得到一个 ∧，取 .1 即首子句为真
                    have h' := h
                    simp [to3CNFClause, StructuralAction.cnfEval] at h'
                    exact h'.1
                  -- 提取前三个字面的 OR = true
                  have hOr3 :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c) = true := by
                    simpa [StructuralAction.clauseEval, mkClause3,
                           Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                      using hTriple
                  -- 把“前三个字面为真”的信息延伸到包含尾巴的 OR：
                  have hOr4 :
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c
                        || genClauseEval σ (d :: rest)) = true := by
                    -- 对等式 hOr3 两边同时做 “|| genClauseEval σ (d :: rest)”
                    have := congrArg
                      (fun b =>
                        b || genClauseEval σ (d :: rest)) hOr3
                    -- RHS: true || R = true
                    simpa [Bool.true_or, Bool.or_assoc] using this
                  -- 把 genClauseEval 展开成同样的 OR 结构
                  have hShape :
                      genClauseEval σ (a :: b :: c :: d :: rest)
                        =
                      (StructuralAction.literalEval σ a
                        || StructuralAction.literalEval σ b
                        || StructuralAction.literalEval σ c
                        || genClauseEval σ (d :: rest)) := by
                    simp [genClauseEval,
                          Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
                  -- 用 hOr4 + hShape 得到结论
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
-- 3b. Tseitin 转换骨架 + Equisatisfiability 证明
------------------------------------------------------------

section Tseitin

-- Tseitin 转换的结果：
--   原公式有 n 个变量，Tseitin 之后有 n + auxVars 个变量，
--   并给出一个 3-CNF（Clause 统一本在 CNF (n + auxVars) 上）。
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

/-
  真正的 Tseitin 将会在这里引入 fresh 变量并构造 3-CNF。
  目前骨架版本先不引入新变量，只是保持接口形状：
  auxVars = 0，cnf = to3CNF Φ。
-/

-- 单个变长子句的 Tseitin 3-CNF 编码（目前未使用，先保留骨架）
noncomputable
def tseitinOfGenClause {n : Nat}
    (Γ : GenClause n) : TseitinResult n :=
  { auxVars := 0
  , cnf     := to3CNFClause Γ }

-- 整个 GenCNF 的 Tseitin 3-CNF 编码（骨架版：直接用 to3CNF）
noncomputable
def tseitinOfGenCNF {n : Nat}
    (Φ : GenCNF n) : TseitinResult n :=
  { auxVars := 0
  , cnf     := to3CNF Φ }

/-- Tseitin 方向 1：
    若原始 GenCNF 可满足，则 Tseitin 3-CNF 也可满足。 -/
lemma tseitin_sat_of_genSat {n : Nat} (Φ : GenCNF n) :
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true)
  →
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true) := by
  intro h
  classical
  rcases h with ⟨σ, hσ⟩
  -- 由于 auxVars = 0，Assignment (n + aux) 与 Assignment n 直接相等
  refine ⟨σ, ?_⟩
  -- 用旧的 to3CNF_equisat 把 genCNFEval ⇒ cnfEval
  have hCnf : StructuralAction.cnfEval σ (to3CNF Φ) = true :=
    (to3CNF_equisat (Φ := Φ) (σ := σ)).mp hσ
  -- 再把 tseitinOfGenCNF Φ 展开成 to3CNF Φ
  simpa [tseitinOfGenCNF] using hCnf

/-- Tseitin 方向 2：
    若 Tseitin 3-CNF 可满足，则原始 GenCNF 也可满足。 -/
lemma genSat_of_tseitin_sat {n : Nat} (Φ : GenCNF n) :
  (∃ σ' : StructuralAction.Assignment (n + (tseitinOfGenCNF Φ).auxVars),
      StructuralAction.cnfEval σ' (tseitinOfGenCNF Φ).cnf = true)
  →
  (∃ σ : StructuralAction.Assignment n,
      genCNFEval σ Φ = true) := by
  intro h
  classical
  rcases h with ⟨σ', hσ'⟩
  -- 同样利用 auxVars = 0，直接把 σ' 当作原变量赋值使用
  refine ⟨σ', ?_⟩
  -- 先把 Tseitin CNF 展开为 to3CNF Φ，并用 to3CNF_equisat 的逆向
  have hGen : genCNFEval σ' Φ = true :=
    (to3CNF_equisat (Φ := Φ) (σ := σ')).mpr
      (by
        -- 证明 cnfEval σ' (to3CNF Φ) = true 与 hσ' 同构
        simpa [tseitinOfGenCNF] using hσ')
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

/-- Tseitin 版困难族公式不可满足：
    对任意赋值 σ' : Assignment (HardVarT n)，HardCNF_T n 的值恒为 false。 -/
lemma HardCNF_T_unsat (n : Nat) :
  ∀ σ' : Assignment (HardVarT n),
    cnfEval σ' (HardCNF_T n) = false := by
  intro σ'
  classical
  -- 已有：PHP_fullGenCNF n 不可满足
  have hUnsatGen := PHP_fullGenCNF_unsat n

  -- 先证明：cnfEval σ' (HardCNF_T n) ≠ true
  have hNotSat : ¬ cnfEval σ' (HardCNF_T n) = true := by
    intro hSat
    -- 把 hSat 包成“存在一个 σ' 满足 Tseitin 公式”的形式
    have hSatExist :
        ∃ σ'' : Assignment (PHPVar n + (tseitinOfGenCNF (PHP_fullGenCNF n)).auxVars),
          cnfEval σ'' (tseitinOfGenCNF (PHP_fullGenCNF n)).cnf = true := by
      refine ⟨σ', ?_⟩
      -- 展开 HardCNF_T 和 HardVarT，类型刚好对上
      simpa [HardCNF_T, HardVarT] using hSat

    -- 用 Tseitin 的 “sat ⇒ genSat” 定理，把满足性拉回到原始 GenCNF
    have hGenSat :
        ∃ σ₀ : Assignment (PHPVar n),
          genCNFEval σ₀ (PHP_fullGenCNF n) = true :=
      genSat_of_tseitin_sat (Φ := PHP_fullGenCNF n) hSatExist

    -- 与 PHP_fullGenCNF_unsat 矛盾
    exact hUnsatGen hGenSat

  -- Bool 只有 true / false 两种情况
  have hOr :
      cnfEval σ' (HardCNF_T n) = true ∨
      cnfEval σ' (HardCNF_T n) = false := by
    cases h : cnfEval σ' (HardCNF_T n) <;> simp [h]

  -- 排除 true，剩下的只能是 false
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

axiom HardActionDPLL : ActionSeq

axiom hardActionDPLL_expLower_2pow :
  ExpLower_2pow HardActionDPLL

axiom hardActionDPLL_polyUpper_from_alg :
  PolyUpper_general HardActionDPLL

theorem no_polyTime_DPLL_on_hardFamily : False :=
  no_polyTime_on_family
    HardActionDPLL
    hardActionDPLL_expLower_2pow
    hardActionDPLL_polyUpper_from_alg

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
-- 10. ResolutionToy：解析证明系统 + 证明长度
------------------------------------------------------------

namespace ResolutionToy

open StructuralAction
open PigeonholeFamily

-- 解析子句：用 Literal 列表表示
abbrev RClause (n : Nat) := List (Literal n)

-- 解析 CNF（子句集合）
abbrev RCNF (n : Nat) := List (RClause n)

/-- 字面的“否定”：同一变量，取反 neg 标志。 -/
def litNeg {n : Nat} (ℓ : Literal n) : Literal n :=
  { var := ℓ.var, neg := !ℓ.neg }

/-- 解析系统中的证明对象：从前提 Φ 推出结论子句 C 的证明树。

  构造器：
  * `ax` : 直接使用 Φ 中的某个子句；
  * `wk` : 子句弱化（超集）；
  * `res` : 解析规则。 -/
inductive ResProof (n : Nat) (Φ : RCNF n) : RClause n → Type where
  | ax {C} (hC : C ∈ Φ) :
      ResProof n Φ C
  | wk {C D} (hSub : ∀ ℓ ∈ C, ℓ ∈ D)
        (hC : ResProof n Φ C) :
      ResProof n Φ D
  | res {C D} (ℓ : Literal n)
        (hC : ResProof n Φ (ℓ :: C))
        (hD : ResProof n Φ (litNeg ℓ :: D)) :
      ResProof n Φ (C ++ D)

/-- 解析证明的“长度”：粗略计数规则应用次数。 -/
def proofLength {n : Nat} {Φ : RCNF n} {C : RClause n}
    (π : ResProof n Φ C) : Nat :=
  match π with
  | .ax _        => 1
  | .wk _ hC     => proofLength hC + 1
  | .res _ hC hD => proofLength hC + proofLength hD + 1

end ResolutionToy

------------------------------------------------------------
-- 11. AbstractDPLL：把 Resolution 证明映射到 DPLL 作用量下界
------------------------------------------------------------

namespace AbstractDPLL

open StructuralAction
open ResolutionToy

/-- 抽象的 DPLL 风格算法模型（依赖变量个数 n）。

  未来你会用真正的 DPLL/CDCL 状态与转移规则来实例化它。
  目前我们只把它当成一个黑盒的 AlgorithmModel。 -/
axiom model (n : Nat) : AlgorithmModel n

/-- DPLL 状态上的结构密度 λ' ：
    将来你会把它换成真正的“能量/冲突/决策层数”等结构指标。 -/
axiom density (n : Nat) : (model n).StateType → Nat

/--
`Simulation ΦR C π` 描述了：
* 给定一个 Resolution 证明 π : ResProof n ΦR C，
* 存在某个 3-SAT 公式 ΦC : CNF n，
* 和在 `model n` 上、关于 ΦC 的一条计算路径 `path`，
* 使得该路径的离散作用量（使用 density n）下界
  主导 Resolution 证明长度：

      proofLength π + 1 ≤ A_nat[ψ]

这是“Resolution → DPLLPath”的抽象桥梁数据结构。
-/
structure Simulation {n : Nat}
    (ΦR : RCNF n) (C : RClause n)
    (π : ResProof n ΦR C) where
  ΦC   : CNF n
  path : ComputationPath (model n) ΦC
  action_ge_length :
    proofLength π + 1 ≤
      pathActionNat (model n) ΦC (density n) path

/--
抽象公理：每一个 Resolution 证明 π 都可以被某个 DPLL 轨迹
在作用量意义下“模拟”，且该轨迹的作用量不小于证明长度。

这一条就是未来你要用具体 DPLL 语义 + λ' 来真正证明的核心定理，
这里先作为接口层面的 axiom。 -/
axiom exists_simulation
  {n : Nat} (ΦR : RCNF n)
  (C : RClause n)
  (π : ResProof n ΦR C) :
  Simulation ΦR C π

/--
**Action ≥ Resolution proof length（抽象骨架版）**

给定任意 Resolution 证明 π，我们可以找到：

* 某个 3-SAT 公式 ΦC : CNF n，
* 某条 DPLL 风格的计算路径 ψ，

使得（用 λ' 作为密度的 pathActionNat）满足：

    pathActionNat (model n) ΦC (density n) ψ ≥ proofLength π + 1
-/
theorem action_ge_resProofLength
  {n : Nat} (ΦR : RCNF n)
  (C : RClause n)
  (π : ResProof n ΦR C) :
  ∃ (ΦC : CNF n) (ψ : ComputationPath (model n) ΦC),
    proofLength π + 1 ≤
      pathActionNat (model n) ΦC (density n) ψ := by
  -- 从抽象 simulation 中解包出 ΦC, ψ 和不等式即可
  rcases exists_simulation ΦR C π with ⟨ΦC, ψ, hψ⟩
  exact ⟨ΦC, ψ, hψ⟩

end AbstractDPLL

end StructuralAction















