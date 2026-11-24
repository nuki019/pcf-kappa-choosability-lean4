/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposals
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# 课题 3 基础引擎：`IsC5`、`MadLt` 核心子图度数和与 `PCF`-代表系统（`Basic`）

本模块不修改 `LeanResearch.Proposals` 中的任何已审计定义，提供以下零 `sorry` 基础工具：
1. `IsC5`、`kappa_mono` 与 `MadLt` 的诱导子图遗传性、单调性及核心子图 `K` 上的度数和上界 `mad_core_sum_lt`；
2. `exists_pcfRep`（Lu–Ying–Song Lemma 2.1 的充分方向 `(2) → (1)`）：纯 `Finset` 版 `PCF`-代表系统判定。

（`C_5` 的 `4`-列表性质、`MinimalCounterexample` 与通用容许染色延拓框架见 `LeanResearch.Proposal3.Admissible`。）
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. `IsC5`、`MadLt` 遗传性与核心子图度数和 -/

/-- 有限连通 2-正则 5 阶简单图（即同构于 `C_5`）。 -/
def IsC5 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2

lemma kappa_mono {a b : ℕ} (h : a ≤ b) :
    (if a = 2 then 4 else a + 1) ≤ (if b = 2 then 4 else b + 1) := by
  split_ifs <;> omega

/-- `MadLt` 在任意诱导子图上的遗传性。 -/
lemma MadLt.induce {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p q : ℕ}
    (hmad : MadLt G p q) (T : Finset V) :
    MadLt (G.induce (T : Set V)) p q := by
  intro S hS
  let S' : Finset V := S.image Subtype.val
  have hS' : S'.Nonempty := hS.image _
  have hcard : S'.card = S.card :=
    Finset.card_image_of_injective S Subtype.val_injective
  have hfilter :
      ((S ×ˢ S).filter (fun e => (G.induce (T : Set V)).Adj e.1 e.2)).card =
      ((S' ×ˢ S').filter (fun e => G.Adj e.1 e.2)).card := by
    apply Finset.card_bij (fun e _ => (e.1.val, e.2.val))
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.induce_adj] at he ⊢
      exact ⟨⟨Finset.mem_image_of_mem _ he.1.1, Finset.mem_image_of_mem _ he.1.2⟩, he.2⟩
    · intro e₁ _ e₂ _ h
      ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · rintro ⟨e₁, e₂⟩ he
      simp only [Finset.mem_filter, Finset.mem_product, S', Finset.mem_image] at he
      rcases he.1.1 with ⟨a, ha, rfl⟩
      rcases he.1.2 with ⟨b, hb, rfl⟩
      refine ⟨(a, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.induce_adj]
      exact ⟨⟨ha, hb⟩, he.2⟩
  rw [hfilter, ← hcard]
  exact hmad S' hS'

/-- 子集 `S` 内顶点诱导度数之和等于 `S ×ˢ S` 中有序相邻对数。 -/
lemma sum_inter_neighborFinset_eq_card_adj_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ u ∈ S, (G.neighborFinset u ∩ S).card =
      ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card := by
  have hbij :
      ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card =
      (S.sigma (fun u => G.neighborFinset u ∩ S)).card := by
    apply Finset.card_bij (fun e _ => ⟨e.1, e.2⟩)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_product] at he
      simp only [Finset.mem_sigma, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨he.1.1, he.2, he.1.2⟩
    · intro e₁ _ e₂ _ h
      cases e₁; cases e₂
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      exact Prod.ext h.1 h.2
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx
      refine ⟨(x.1, x.2), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx.1, hx.2.2⟩, hx.2.1⟩
  rw [hbij, Finset.card_sigma]

/-- 零辅助图核心子图不等式：若 `MadLt G p q`，则对任意非空核心顶点集 `S`，
有 `q * ∑ u ∈ S, |N_G(u) ∩ S| < p * |S|`。 -/
lemma mad_core_sum_lt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p q : ℕ}
    (hmad : MadLt G p q) {S : Finset V} (hS : S.Nonempty) :
    q * (∑ u ∈ S, (G.neighborFinset u ∩ S).card) < p * S.card := by
  rw [sum_inter_neighborFinset_eq_card_adj_pairs]
  exact hmad S hS

/-- 若 `MadLt G p q` 且 `0 < q'`、`p * q' ≤ p' * q`，则 `MadLt G p' q'`。 -/
lemma MadLt.mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p q p' q' : ℕ}
    (hmad : MadLt G p q) (hq' : 0 < q') (hle : p * q' ≤ p' * q) :
    MadLt G p' q' := by
  intro S hS
  have h1 := hmad S hS
  have hmul : q * (q' * ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card) <
      q * (p' * S.card) := by
    calc q * (q' * ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card)
        = q' * (q * ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card) := by ring
      _ < q' * (p * S.card) := Nat.mul_lt_mul_of_pos_left h1 hq'
      _ = (p * q') * S.card := by ring
      _ ≤ (p' * q) * S.card := Nat.mul_le_mul_right _ hle
      _ = q * (p' * S.card) := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## 2. 颜色多重度与 `PCF`-代表系统（Lemma 2.1 充分条件） -/

/-- 列表 `B` 存在恰好出现一次的唯一颜色。 -/
def HasUniqueColor (B : List ℕ) : Prop :=
  ∃ c : ℕ, B.count c = 1

/-- 若索引集 `I` 上的选色 `a : ι → ℕ` 与固定背景颜色列表 `B` 拼合后存在唯一颜色。 -/
def IsPCFRep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset ℕ) (B : List ℕ) (a : ι → ℕ) : Prop :=
  (∀ i, a i ∈ A i) ∧
  ∃ c : ℕ, (Finset.univ.filter (fun i => a i = c)).card + B.count c = 1

/-- Lemma 2.1 的充分方向 `(2) → (1)`（纯 `Finset` 版，零索引偏移噪音）：
设每个集合 `A i` 非空，`q` 是满足 `|A i| = 1` 的索引数，`s` 是 `B` 中恰好出现一次的颜色数，
`r` 是 `B` 中出现至少两次的颜色数。若满足：
- 情形 1：`q < s`；或
- 情形 2：`q ≥ s` 且存在某个 `j` 使得 `r + s + (q - s) / 2 < (A j).card`，
则必然存在 `PCF`-代表系统 `a : ι → ℕ`。 -/
theorem exists_pcfRep {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ι → Finset ℕ) (hne : ∀ i, (A i).Nonempty) (B : List ℕ) :
    let sing := Finset.univ.filter (fun i => (A i).card = 1)
    let uniqB := B.toFinset.filter (fun c => B.count c = 1)
    let multB := B.toFinset.filter (fun c => 2 ≤ B.count c)
    (sing.card < uniqB.card ∨
      ∃ j : ι, multB.card + uniqB.card + (sing.card - uniqB.card) / 2 < (A j).card) →
    ∃ a : ι → ℕ, IsPCFRep A B a := by
  intro sing uniqB multB hcond
  -- 先为每个单点索引 `i ∈ sing` 取其唯一元素（对其余索引也先任取一个占位元素）
  have hpick : ∀ i : ι, ∃ x, x ∈ A i := fun i => hne i
  choose a₀ ha₀ using hpick
  -- 统计 `a₀` 在 `sing` 上的多重度函数
  let cntS : ℕ → ℕ := fun c => (sing.filter (fun i => a₀ i = c)).card
  -- 情形 A：存在颜色 `γ` 在 `sing` 选色 + `B` 中恰好出现一次
  by_cases huniq : ∃ γ : ℕ, cntS γ + B.count γ = 1
  · rcases huniq with ⟨γ, hγ⟩
    -- 对每个 `i ∉ sing`，`|A i| ≥ 2`，故可选 `a i ∈ A i \ {γ}`
    have hge2 : ∀ i, i ∉ sing → ∃ x ∈ A i, x ≠ γ := by
      intro i hi
      have hcard : 2 ≤ (A i).card := by
        have hpos : 1 ≤ (A i).card := (hne i).card_pos
        have hne1 : (A i).card ≠ 1 := by
          simpa [sing] using hi
        omega
      have hnonempty : (A i \ {γ}).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_inter (A i) {γ}
        have hle : (A i ∩ {γ}).card ≤ 1 :=
          le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp)
        omega
      rcases hnonempty with ⟨x, hx⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
      exact ⟨x, hx.1, hx.2⟩
    let a : ι → ℕ := fun i =>
      if h : i ∈ sing then a₀ i else (hge2 i h).choose
    refine ⟨a, ?_, γ, ?_⟩
    · intro i
      dsimp only [a]
      split_ifs with h
      · exact ha₀ i
      · exact (hge2 i h).choose_spec.1
    · have hfilt : Finset.univ.filter (fun i => a i = γ) = sing.filter (fun i => a₀ i = γ) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
        split_ifs with h
        · simp [h]
        · exact ⟨fun heq => False.elim ((hge2 i h).choose_spec.2 heq),
            fun ⟨hi, _⟩ => False.elim (h hi)⟩
      rw [hfilt]
      exact hγ
  · -- 情形 B：`sing` 选色与 `B` 拼合后没有唯一颜色
    push Not at huniq
    -- 1. 每个 `γ ∈ uniqB` 必在 `sing` 的像中至少出现一次，否则 `cntS γ + 1 = 1`
    have hsub_uniq : uniqB ⊆ sing.image a₀ := by
      intro γ hγ
      have hB1 : B.count γ = 1 := (Finset.mem_filter.mp hγ).2
      have hne0 : cntS γ ≠ 0 := by
        intro h0
        exact huniq γ (by omega)
      have hpos : 0 < (sing.filter (fun i => a₀ i = γ)).card := Nat.pos_of_ne_zero hne0
      rcases Finset.card_pos.mp hpos with ⟨i, hi⟩
      rw [Finset.mem_filter] at hi
      exact Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩
    -- 于是 `uniqB.card ≤ sing.card`（排除条件 1：`sing.card < uniqB.card`）
    have hqs : uniqB.card ≤ sing.card :=
      le_trans (Finset.card_le_card hsub_uniq) Finset.card_image_le
    rcases hcond with hlt | ⟨j, hj⟩
    · omega
    -- 2. 定义 `X_supp = (sing.image a₀) ∪ B.toFinset`
    let suppB := B.toFinset
    let newCols := (sing.image a₀) \ suppB
    -- 对每个 `γ ∈ newCols`，`B.count γ = 0` 且 `cntS γ ≥ 1`，由 `huniq` 得 `cntS γ ≥ 2`
    have hnew_ge2 : ∀ γ ∈ newCols, 2 ≤ cntS γ := by
      intro γ hγ
      rw [Finset.mem_sdiff] at hγ
      have hB0 : B.count γ = 0 := by
        rw [List.count_eq_zero]
        simpa [suppB] using hγ.2
      rcases Finset.mem_image.mp hγ.1 with ⟨i, hi, rfl⟩
      have hge1 : 1 ≤ cntS (a₀ i) :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      have hne1 : cntS (a₀ i) + B.count (a₀ i) ≠ 1 := huniq (a₀ i)
      omega
    -- 对每个 `γ ∈ uniqB`，`1 ≤ cntS γ`
    have huniq_ge1 : ∀ γ ∈ uniqB, 1 ≤ cntS γ := by
      intro γ hγ
      rcases Finset.mem_image.mp (hsub_uniq hγ) with ⟨i, hi, rfl⟩
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    -- `uniqB` 与 `newCols` 不交
    have hdisj : Disjoint uniqB newCols := by
      rw [Finset.disjoint_left]
      intro γ h1 h2
      have hmemB : γ ∈ suppB := (Finset.mem_filter.mp h1).1
      exact (Finset.mem_sdiff.mp h2).2 hmemB
    -- 纤维和界：`uniqB.card + 2 * newCols.card ≤ sing.card`
    have hsum_bound : uniqB.card + 2 * newCols.card ≤ sing.card := by
      have h1 : uniqB.card ≤ ∑ γ ∈ uniqB, cntS γ := by
        calc uniqB.card = ∑ _γ ∈ uniqB, 1 := by simp
          _ ≤ ∑ γ ∈ uniqB, cntS γ := Finset.sum_le_sum huniq_ge1
      have h2 : 2 * newCols.card ≤ ∑ γ ∈ newCols, cntS γ := by
        calc 2 * newCols.card = ∑ _γ ∈ newCols, 2 := by simp [mul_comm]
          _ ≤ ∑ γ ∈ newCols, cntS γ := Finset.sum_le_sum hnew_ge2
      have h3 : ∑ γ ∈ uniqB ∪ newCols, cntS γ ≤ sing.card := by
        have hsub :
            (uniqB ∪ newCols).biUnion (fun γ => sing.filter (fun i => a₀ i = γ)) ⊆ sing := by
          intro i hi
          rw [Finset.mem_biUnion] at hi
          rcases hi with ⟨_, _, hi⟩
          exact (Finset.mem_filter.mp hi).1
        have hpw : (↑(uniqB ∪ newCols) : Set ℕ).PairwiseDisjoint
            (fun γ => sing.filter (fun i => a₀ i = γ)) := by
          intro x _ y _ hxy
          change Disjoint (sing.filter (fun i => a₀ i = x)) (sing.filter (fun i => a₀ i = y))
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          exact hxy ((Finset.mem_filter.mp hi1).2.symm.trans (Finset.mem_filter.mp hi2).2)
        have heq : ∑ γ ∈ uniqB ∪ newCols, cntS γ =
            ((uniqB ∪ newCols).biUnion (fun γ => sing.filter (fun i => a₀ i = γ))).card :=
          (Finset.card_biUnion hpw).symm
        rw [heq]
        exact Finset.card_le_card hsub
      rw [Finset.sum_union hdisj] at h3
      omega
    -- `suppB.card = multB.card + uniqB.card`
    have hsuppB : suppB.card = multB.card + uniqB.card := by
      have hdisjB : Disjoint multB uniqB := by
        rw [Finset.disjoint_left]
        intro γ h1 h2
        have := (Finset.mem_filter.mp h1).2
        have := (Finset.mem_filter.mp h2).2
        omega
      have hunionB : multB ∪ uniqB = suppB := by
        ext γ
        simp only [Finset.mem_union, multB, uniqB, Finset.mem_filter, suppB]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          have hpos : 0 < B.count γ := List.count_pos_iff.mpr (List.mem_toFinset.mp h)
          by_cases h1 : B.count γ = 1
          · exact Or.inr ⟨h, h1⟩
          · exact Or.inl ⟨h, by omega⟩
      rw [← hunionB, Finset.card_union_of_disjoint hdisjB]
    -- `((sing.image a₀) ∪ suppB).card ≤ multB.card + uniqB.card + (sing.card - uniqB.card) / 2`
    let Xsupp := (sing.image a₀) ∪ suppB
    have hXsupp : Xsupp.card ≤ multB.card + uniqB.card + (sing.card - uniqB.card) / 2 := by
      have hun : Xsupp = newCols ∪ suppB := by
        ext γ
        simp only [Xsupp, newCols, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hdisjX : Disjoint newCols suppB := Finset.sdiff_disjoint
      rw [hun, Finset.card_union_of_disjoint hdisjX, hsuppB]
      omega
    -- 故 `Xsupp.card < (A j).card`，存在 `α ∈ A j \ Xsupp`
    have hAj_lt : Xsupp.card < (A j).card := lt_of_le_of_lt hXsupp hj
    have hex_alpha : (A j \ Xsupp).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.card_sdiff_add_card_inter (A j) Xsupp
      have h2 : (A j ∩ Xsupp).card ≤ Xsupp.card := Finset.card_le_card Finset.inter_subset_right
      omega
    rcases hex_alpha with ⟨α, hα⟩
    rw [Finset.mem_sdiff] at hα
    -- 断言 `j ∉ sing`：否则 `a₀ j ∈ sing.image a₀ ⊆ Xsupp` 且 `A j = {a₀ j}`，与 `α ∈ A j \ Xsupp` 矛盾！
    have hj_not_sing : j ∉ sing := by
      intro hjs
      have hcard1 : (A j).card = 1 := (Finset.mem_filter.mp hjs).2
      rcases Finset.card_eq_one.mp hcard1 with ⟨z, hz⟩
      have h1 : α = z := by simpa [hz] using hα.1
      have h2 : a₀ j = z := by simpa [hz] using ha₀ j
      have hmem : α ∈ Xsupp := by
        rw [h1, ← h2]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem a₀ hjs)
      exact hα.2 hmem
    -- 对其余 `i ∉ sing`（且 `i ≠ j`），`|A i| ≥ 2`，故可选 `a i ∈ A i \ {α}`
    have hge2_other : ∀ i, i ∉ sing → ∃ x ∈ A i, x ≠ α := by
      intro i hi
      have hcard : 2 ≤ (A i).card := by
        have hpos : 1 ≤ (A i).card := (hne i).card_pos
        have hne1 : (A i).card ≠ 1 := by simpa [sing] using hi
        omega
      have hnonempty : (A i \ {α}).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_inter (A i) {α}
        have hle : (A i ∩ {α}).card ≤ 1 :=
          le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp)
        omega
      rcases hnonempty with ⟨x, hx⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
      exact ⟨x, hx.1, hx.2⟩
    let a : ι → ℕ := fun i =>
      if h : i = j then α
      else if hs : i ∈ sing then a₀ i
      else (hge2_other i hs).choose
    refine ⟨a, ?_, α, ?_⟩
    · intro i
      dsimp only [a]
      split_ifs with h1 h2
      · subst h1; exact hα.1
      · exact ha₀ i
      · exact (hge2_other i h2).choose_spec.1
    · have hB0 : B.count α = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact hα.2 (Finset.mem_union_right _ (List.mem_toFinset.mpr hmem))
      have hfilt : Finset.univ.filter (fun i => a i = α) = {j} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, a]
        split_ifs with h1 h2
        · simp [h1]
        · constructor
          · intro heq
            exfalso
            apply hα.2
            rw [← heq]
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem a₀ h2)
          · intro heq; exact False.elim (h1 heq)
        · constructor
          · intro heq; exact False.elim ((hge2_other i h2).choose_spec.2 heq)
          · intro heq; exact False.elim (h1 heq)
      rw [hfilt, hB0]
      simp

end LeanResearch.Proposal3
