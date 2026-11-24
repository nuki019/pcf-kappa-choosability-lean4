/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BeyondDefs

/-!
# 引理 A 核心与引理 E0：`3`-线串单点计数 `≤ 1`、定色延拓引擎与 `no_T3_adj_deg_three`（`ThreeThreadExt`）

本模块为突破 `mad(G) < 12/5 → 22/9` 形式化核心纯组合引擎及引理 E0：
1. 纯组合 `3`-线串可达色集 `threeThreadGoodCols`：证明其总非空，且单点集出现次数 `≤ 1`
   （`threeThreadGoodCols_card_one_le_one`），以及带 `c₃ ≠ α` 避色约束的 `≤ 3` 变体；
2. 纯组合定色延拓引擎：`t3_fixed_color_extension`、`t21_fixed_color_extension`、
   `s32_a2_fixed_color_extension`；
3. 引理 E0：`no_T3_adj_deg_three`（在 `2 * p ≤ 5 * q` 下，任意 `T3` 顶点无 `3`-度邻点）。

（基于本引擎的 `q4_three_thread_good_bound` 见 `Q4Ext`，其余 4 条 `T3` 邻接限制见 `T3Adjacency` 与 `T3Adjacency2`。）
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 纯组合 `3`-线串可达色集与定色延拓引擎 -/

/-- `3`-线串 `u - v₁ - v₂ - v₃ - z` 在给定 `u ↦ α` 与 `Z₃ ⊆ L₃ \ {φz}` 时，
`v₁` 的合法可达颜色集合。 -/
def threeThreadGoodCols (L₁ L₂ : Finset ℕ) (Z₃ : Finset ℕ) (φz α : ℕ) : Finset ℕ :=
  (L₁ \ {α}).filter (fun c₁ =>
    ∃ c₃ ∈ Z₃, c₃ ≠ c₁ ∧ ∃ c₂ ∈ L₂ \ {α, c₃, φz}, c₂ ≠ c₁)

/-- 若 `|L₁| = |L₂| = 4` 且 `Z₃` 非空，则 `threeThreadGoodCols L₁ L₂ Z₃ φz α` 非空。 -/
lemma threeThreadGoodCols_nonempty {L₁ L₂ Z₃ : Finset ℕ} {φz α : ℕ}
    (hL1 : L₁.card = 4) (hL2 : L₂.card = 4) (hZ3 : Z₃.Nonempty) :
    (threeThreadGoodCols L₁ L₂ Z₃ φz α).Nonempty := by
  rcases hZ3 with ⟨c₃, hc₃⟩
  have hB2 : (L₂ \ {α, c₃, φz}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := card_sdiff_ge L₂ {α, c₃, φz}
    have h2 := card_triple_le α c₃ φz
    omega
  rcases hB2 with ⟨c₂, hc₂⟩
  have hB1 : (L₁ \ {α, c₂, c₃}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := card_sdiff_ge L₁ {α, c₂, c₃}
    have h2 := card_triple_le α c₂ c₃
    omega
  rcases hB1 with ⟨c₁, hc₁⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc₁
  refine ⟨c₁, ?_⟩
  rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨⟨hc₁.1, hc₁.2.1⟩, c₃, hc₃, Ne.symm hc₁.2.2.2, c₂, hc₂, Ne.symm hc₁.2.2.1⟩

/-- 辅助：若 `|L| = 4` 且 `L \ {a, b, c} ⊆ {d}`，则 `L = {d, a, b, c}` 且四元素两两互异。 -/
private lemma four_set_eq_of_sdiff_triple_subset_singleton {L : Finset ℕ} {a b c d : ℕ}
    (hL : L.card = 4) (hsub : L \ {a, b, c} ⊆ {d}) :
    L = {d, a, b, c} ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hne : (L \ {a, b, c}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := card_sdiff_ge L {a, b, c}
    have h2 := card_triple_le a b c
    omega
  have heq1 : L \ {a, b, c} = {d} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; exact hne.card_pos)
  have hd_mem : d ∈ L \ {a, b, c} := by rw [heq1]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd_mem
  have hinter : (L ∩ {a, b, c}).card = 3 := by
    have h1 := Finset.card_sdiff_add_card_inter L {a, b, c}
    rw [heq1, Finset.card_singleton, hL] at h1; omega
  have htri3 : ({a, b, c} : Finset ℕ).card = 3 := by
    have h1 : (L ∩ {a, b, c}).card ≤ ({a, b, c} : Finset ℕ).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h2 := card_triple_le a b c; omega
  have htri_sub : ({a, b, c} : Finset ℕ) ⊆ L := by
    have hEqI : L ∩ {a, b, c} = {a, b, c} :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    rw [← hEqI]; exact Finset.inter_subset_left
  have hab : a ≠ b := by
    intro h; subst h
    have hsub2 : ({a, a, c} : Finset ℕ) ⊆ {a, c} := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto
    have := le_trans (Finset.card_le_card hsub2) (Finset.card_le_two (a := a) (b := c))
    omega
  have hac : a ≠ c := by
    intro h; subst h
    have hsub2 : ({a, b, a} : Finset ℕ) ⊆ {a, b} := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto
    have := le_trans (Finset.card_le_card hsub2) (Finset.card_le_two (a := a) (b := b))
    omega
  have hbc : b ≠ c := by
    intro h; subst h
    have hsub2 : ({a, b, b} : Finset ℕ) ⊆ {a, b} := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto
    have := le_trans (Finset.card_le_card hsub2) (Finset.card_le_two (a := a) (b := b))
    omega
  have hL_eq : L = {d, a, b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hd_mem.1
      · exact htri_sub (by simp)
      · exact htri_sub (by simp)
      · exact htri_sub (by simp)
    · rw [Finset.card_insert_of_notMem (by simp [hd_mem.2.1, hd_mem.2.2.1, hd_mem.2.2.2]),
          htri3, hL]
  exact ⟨hL_eq, hd_mem.2.1, hd_mem.2.2.1, hd_mem.2.2.2, hab, hac, hbc⟩

/-- 核心机制：若 `|Z₃| ≥ 2`（含互异 `ζ₁ ≠ ζ₂`）且 `|threeThreadGoodCols L₁ L₂ Z₃ φz α| = 1`，
则必有 `L₂ = {ζ₂, α, ζ₁, φz}`，从而 `L₂ \ {ζ₁, ζ₂, φz} = {α}`！ -/
lemma threeThreadGoodCols_eq_one_forces_L2 {L₁ L₂ Z₃ : Finset ℕ} {φz α ζ₁ ζ₂ : ℕ}
    (hL1 : L₁.card = 4) (hL2 : L₂.card = 4)
    (hζ1 : ζ₁ ∈ Z₃) (hζ2 : ζ₂ ∈ Z₃) (hζ12 : ζ₁ ≠ ζ₂)
    (hcard1 : (threeThreadGoodCols L₁ L₂ Z₃ φz α).card = 1) :
    L₂ \ {ζ₁, ζ₂, φz} = {α} := by
  rcases Finset.card_eq_one.mp hcard1 with ⟨d, hd_eq⟩
  have hsub_of : ∀ c₃ ∈ Z₃, ∀ c₂ ∈ L₂ \ {α, c₃, φz}, L₁ \ {α, c₂, c₃} ⊆ {d} := by
    intro c₃ hc₃ c₂ hc₂ c₁ hc₁
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc₁
    have hmem : c₁ ∈ threeThreadGoodCols L₁ L₂ Z₃ φz α := by
      rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨⟨hc₁.1, hc₁.2.1⟩, c₃, hc₃, Ne.symm hc₁.2.2.2, c₂, hc₂, Ne.symm hc₁.2.2.1⟩
    rw [hd_eq] at hmem; exact hmem
  -- 取 `c₂₂ ∈ L₂ \ {α, ζ₂, φz}`，得 `ζ₂ ∈ L₁` 且 `ζ₂ ≠ d, ζ₂ ≠ α`
  have hB22 : (L₂ \ {α, ζ₂, φz}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := card_sdiff_ge L₂ {α, ζ₂, φz}; have h2 := card_triple_le α ζ₂ φz; omega
  rcases hB22 with ⟨c₂₂, hc₂₂⟩
  rcases four_set_eq_of_sdiff_triple_subset_singleton hL1 (hsub_of ζ₂ hζ2 c₂₂ hc₂₂) with
    ⟨hL1_eq2, _, _, hdζ2, _, hαζ2, _⟩
  have hζ2_L1 : ζ₂ ∈ L₁ := by rw [hL1_eq2]; simp
  -- 对任意 `c₂₁ ∈ L₂ \ {α, ζ₁, φz}`，必有 `c₂₁ = ζ₂`
  have hB21_sub : L₂ \ {α, ζ₁, φz} ⊆ {ζ₂} := by
    intro c₂₁ hc₂₁
    rcases four_set_eq_of_sdiff_triple_subset_singleton hL1 (hsub_of ζ₁ hζ1 c₂₁ hc₂₁) with
      ⟨hL1_eq1, _, _, _, _, _, _⟩
    rw [hL1_eq1] at hζ2_L1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hζ2_L1 ⊢
    rcases hζ2_L1 with h | h | h | h
    · exact False.elim (hdζ2 h.symm)
    · exact False.elim (hαζ2 h.symm)
    · exact h.symm
    · exact False.elim (hζ12 h.symm)
  rcases four_set_eq_of_sdiff_triple_subset_singleton hL2 hB21_sub with
    ⟨hL2_eq, hζ2α, hζ2ζ1, hζ2φ, hαζ1, hαφ, hζ1φ⟩
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  rw [hL2_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, h1, h2, h3⟩
    · exact False.elim (h2 rfl)
    · rfl
    · exact False.elim (h1 rfl)
    · exact False.elim (h3 rfl)
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), hαζ1, Ne.symm hζ2α, hαφ⟩

/-- 引理 A 核心：`3`-线串可达色集 `threeThreadGoodCols L₁ L₂ Z₃ φz α`
对固定 `Z₃`（`|Z₃| ≥ 2`），至多对 **1** 个 `α ∈ C` 为单点集！ -/
lemma threeThreadGoodCols_card_one_le_one (C : Finset ℕ) {L₁ L₂ Z₃ : Finset ℕ} {φz : ℕ}
    (hL1 : L₁.card = 4) (hL2 : L₂.card = 4) (hZ3 : 2 ≤ Z₃.card) :
    (C.filter (fun α => (threeThreadGoodCols L₁ L₂ Z₃ φz α).card = 1)).card ≤ 1 := by
  rcases exists_two_of_card_ge_two hZ3 with ⟨ζ₁, hζ1, ζ₂, hζ2, hζ12⟩
  rw [Finset.card_le_one]
  intro α₁ h1 α₂ h2
  simp only [Finset.mem_filter] at h1 h2
  have heq1 := threeThreadGoodCols_eq_one_forces_L2 hL1 hL2 hζ1 hζ2 hζ12 h1.2
  have heq2 := threeThreadGoodCols_eq_one_forces_L2 hL1 hL2 hζ1 hζ2 hζ12 h2.2
  have hsing : ({α₁} : Finset ℕ) = {α₂} := heq1.symm.trans heq2
  exact Finset.singleton_injective hsing

/-- 变体（用于孤立邻点 `w` 处保证 `c₃ ≠ α`）：若 `|Z₃| ≥ 3`，则对每个 `α`，
`Z₃ \ {α}` 仍有大小 `≥ 2`，且 `threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α` 至多对 **3** 个 `α`
为单点集（因为每个这样的 `α` 都必属于 `L₂ \ {φz}`）！ -/
lemma threeThreadGoodCols_avoid_card_one_le_three (C : Finset ℕ)
    {L₁ L₂ Z₃ : Finset ℕ} {φz : ℕ}
    (hL1 : L₁.card = 4) (hL2 : L₂.card = 4) (hZ3 : 3 ≤ Z₃.card) :
    (C.filter (fun α => (threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α).card = 1)).card ≤ 3 := by
  by_cases hne :
      (C.filter (fun α => (threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α).card = 1)).Nonempty
  · rcases hne with ⟨α₀, hα₀⟩
    have hZα0 : 2 ≤ (Z₃ \ {α₀}).card := by
      have := card_sdiff_ge Z₃ {α₀}; simp only [Finset.card_singleton] at this; omega
    rcases exists_two_of_card_ge_two hZα0 with ⟨ζ₁, hζ1, ζ₂, hζ2, hζ12⟩
    have heq0 := threeThreadGoodCols_eq_one_forces_L2 hL1 hL2 hζ1 hζ2 hζ12
      (Finset.mem_filter.mp hα₀).2
    have hφL2 : φz ∈ L₂ := by
      have hcardI : (L₂ ∩ {ζ₁, ζ₂, φz}).card = 3 := by
        have h1 := Finset.card_sdiff_add_card_inter L₂ {ζ₁, ζ₂, φz}
        rw [heq0, Finset.card_singleton, hL2] at h1; omega
      have htri3 : ({ζ₁, ζ₂, φz} : Finset ℕ).card = 3 := by
        have h1 : (L₂ ∩ {ζ₁, ζ₂, φz}).card ≤ ({ζ₁, ζ₂, φz} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_right
        have h2 := card_triple_le ζ₁ ζ₂ φz; omega
      have hEqI : L₂ ∩ {ζ₁, ζ₂, φz} = {ζ₁, ζ₂, φz} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have : φz ∈ L₂ ∩ {ζ₁, ζ₂, φz} := by rw [hEqI]; simp
      exact (Finset.mem_inter.mp this).1
    have hsub : C.filter (fun α => (threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α).card = 1) ⊆
        L₂ \ {φz} := by
      intro α hα
      rw [Finset.mem_filter] at hα
      have hZα : 2 ≤ (Z₃ \ {α}).card := by
        have := card_sdiff_ge Z₃ {α}; simp only [Finset.card_singleton] at this; omega
      rcases exists_two_of_card_ge_two hZα with ⟨η₁, hη1, η₂, hη2, hη12⟩
      have heq := threeThreadGoodCols_eq_one_forces_L2 hL1 hL2 hη1 hη2 hη12 hα.2
      have hmem : α ∈ L₂ \ {η₁, η₂, φz} := by rw [heq]; simp
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hmem ⊢
      exact ⟨hmem.1, hmem.2.2.2⟩
    have hcard_le : (L₂ \ {φz}).card = 3 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hφL2),
          Finset.card_singleton, hL2]
    exact le_trans (Finset.card_le_card hsub) (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]; omega

/-- 超级定色延拓引理 `t3_fixed_color_extension`：
给定 `T3` 顶点的叶邻点集合 `Y`（`|Y| ≥ 1`）、`3`-线串列表 `L₁, L₂`（大小 4）及末端可用集 `Z₃`
（`|Z₃| ≥ 2`）、另一好邻点色 `φy`、待定好邻点色 `δ` 以及可用色集 `C_u`（`|C_u| ≥ |Y| + 1`），
总存在合法延拓使得 `u` 与 `3`-线串及全部叶点同时满足 PCF！ -/
lemma t3_fixed_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {L₁ L₂ Z₃ C_u : Finset ℕ} {φy φz δ : ℕ}
    (hY1 : 1 ≤ Y.card) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hL1 : L₁.card = 4) (hL2' : L₂.card = 4) (hZ3 : 2 ≤ Z₃.card)
    (hCu : Y.card + 1 ≤ C_u.card) :
    ∃ α ∈ C_u, ∃ c₁ ∈ threeThreadGoodCols L₁ L₂ Z₃ φz α,
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, φy, δ] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → Option {r : V // r ∈ Y} → Finset ℕ := fun α o =>
    match o with
    | none => threeThreadGoodCols L₁ L₂ Z₃ φz α
    | some r => L r.val \ {α}
  have hA_ne : ∀ α o, (A α o).Nonempty := by
    intro α o; cases o with
    | none => exact threeThreadGoodCols_nonempty hL1 hL2' (Finset.card_pos.mp (by omega))
    | some r =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}
      have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C_u, ¬ ∃ f, IsPCFRep (A α) [φy, δ] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (some ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr
      simp only [aY, hr, dite_true]
      have hm := hf_mem (some ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm
      exact hm
    have hcnt_eq : (Y.filter (fun r => aY r = γ)).card +
        ([f none, φy, δ] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ)).card =
          (if f none = γ then 1 else 0) + (Y.filter (fun r => aY r = γ)).card := by
        have hpart : Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ) =
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ)) ∪
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o.isSome ∧ f o = γ)) := by
          ext o; cases o <;> simp
        have hdisj : Disjoint
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ))
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o.isSome ∧ f o = γ)) := by
          rw [Finset.disjoint_left]; intro o h1 h2
          simp only [Finset.mem_filter] at h1 h2; rcases h1.2 with ⟨rfl, _⟩; simp at h2
        rw [hpart, Finset.card_union_of_disjoint hdisj]
        congr 1
        · by_cases hn : f none = γ
          · have hEq : Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ) =
                {none} := by ext o; cases o <;> simp [hn]
            rw [hEq, Finset.card_singleton]; simp only [hn, ite_true]
          · have hEq : Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ) =
                ∅ := by ext o; cases o <;> simp [hn]
            rw [hEq, Finset.card_empty]; simp only [hn, ite_false]
        · apply Finset.card_bij (fun o ho => (o.get (Finset.mem_filter.mp ho).2.1).val)
          · intro o ho
            rcases Finset.mem_filter.mp ho with ⟨_, his, hfo⟩
            cases o with
            | none => simp at his
            | some r =>
              simp only [Option.get_some, Finset.mem_filter, aY, r.property, dite_true, true_and]
              exact hfo
          · intro o₁ ho₁ o₂ ho₂ heq
            rcases Finset.mem_filter.mp ho₁ with ⟨_, his₁, _⟩
            rcases Finset.mem_filter.mp ho₂ with ⟨_, his₂, _⟩
            cases o₁ with
            | none => simp at his₁
            | some r₁ =>
              cases o₂ with
              | none => simp at his₂
              | some r₂ =>
                simp only [Option.get_some] at heq
                exact congrArg some (Subtype.ext heq)
          · intro r hr
            rcases Finset.mem_filter.mp hr with ⟨hrY, hfr⟩
            simp only [aY, hrY, dite_true] at hfr
            refine ⟨some ⟨r, hrY⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_some]
            exact hfr
      have hlist : ([f none, φy, δ] : List ℕ).count γ =
          (if f none = γ then 1 else 0) + ([φy, δ] : List ℕ).count γ := by
        simp only [List.count_cons, beq_iff_eq]; split_ifs <;> omega
      omega
    exact hno α hα (f none) (hf_mem none) aY haY γ hcnt_eq
  -- 双计数：`2 * (|Y| + 1) ≤ 2 * |C_u| ≤ ∑ q_α ≤ 1 + 2 * |Y|`！
  have hlower : 2 * C_u.card ≤
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card := by
    calc 2 * C_u.card = ∑ _α ∈ C_u, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        no_pcfRep_pair_ge_two (hA_ne α) (by rw [Fintype.card_option, Fintype.card_coe]; omega)
          (hno_rep α hα)
  have hupper :
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card ≤
        1 + 2 * Y.card := by
    rw [sum_filter_card_comm]
    have hsplit_sum :
        ∑ o : Option {r // r ∈ Y}, (C_u.filter (fun α => (A α o).card = 1)).card =
        (C_u.filter (fun α => (A α none).card = 1)).card +
        ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [Fintype.sum_option]
      congr 1
      rw [← Finset.sum_attach Y (fun r => (C_u.filter (fun α => (L r \ {α}).card = 1)).card)]
      rfl
    rw [hsplit_sum]
    have h1 := threeThreadGoodCols_card_one_le_one C_u (φz := φz) hL1 hL2' hZ3
    have h2 : ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card ≤ 2 * Y.card := by
      calc ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C_u (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    dsimp only [A] at *; omega
  omega

/-- `t3_fixed_color_extension` 的 `Z₃ \ {α}` 避色变体（需要 `|Z₃| ≥ 3` 与 `|C_u| ≥ |Y| + 2`）。 -/
lemma t3_fixed_color_extension_avoid {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {L₁ L₂ Z₃ C_u : Finset ℕ} {φy φz δ : ℕ}
    (hY1 : 1 ≤ Y.card) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hL1 : L₁.card = 4) (hL2' : L₂.card = 4) (hZ3 : 3 ≤ Z₃.card)
    (hCu : Y.card + 2 ≤ C_u.card) :
    ∃ α ∈ C_u, ∃ c₁ ∈ threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α,
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, φy, δ] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → Option {r : V // r ∈ Y} → Finset ℕ := fun α o =>
    match o with
    | none => threeThreadGoodCols L₁ L₂ (Z₃ \ {α}) φz α
    | some r => L r.val \ {α}
  have hA_ne : ∀ α o, (A α o).Nonempty := by
    intro α o; cases o with
    | none =>
      have hZα : 2 ≤ (Z₃ \ {α}).card := by
        have := card_sdiff_ge Z₃ {α}; simp only [Finset.card_singleton] at this; omega
      exact threeThreadGoodCols_nonempty hL1 hL2' (Finset.card_pos.mp (by omega))
    | some r =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}
      have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C_u, ¬ ∃ f, IsPCFRep (A α) [φy, δ] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (some ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr
      simp only [aY, hr, dite_true]
      have hm := hf_mem (some ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm
      exact hm
    have hcnt_eq : (Y.filter (fun r => aY r = γ)).card +
        ([f none, φy, δ] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ)).card =
          (if f none = γ then 1 else 0) + (Y.filter (fun r => aY r = γ)).card := by
        have hpart : Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ) =
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ)) ∪
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o.isSome ∧ f o = γ)) := by
          ext o; cases o <;> simp
        have hdisj : Disjoint
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ))
            (Finset.univ.filter (fun o : Option {r // r ∈ Y} => o.isSome ∧ f o = γ)) := by
          rw [Finset.disjoint_left]; intro o h1 h2
          simp only [Finset.mem_filter] at h1 h2; rcases h1.2 with ⟨rfl, _⟩; simp at h2
        rw [hpart, Finset.card_union_of_disjoint hdisj]
        congr 1
        · by_cases hn : f none = γ
          · have hEq : Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ) =
                {none} := by ext o; cases o <;> simp [hn]
            rw [hEq, Finset.card_singleton]; simp only [hn, ite_true]
          · have hEq : Finset.univ.filter (fun o : Option {r // r ∈ Y} => o = none ∧ f o = γ) =
                ∅ := by ext o; cases o <;> simp [hn]
            rw [hEq, Finset.card_empty]; simp only [hn, ite_false]
        · apply Finset.card_bij (fun o ho => (o.get (Finset.mem_filter.mp ho).2.1).val)
          · intro o ho
            rcases Finset.mem_filter.mp ho with ⟨_, his, hfo⟩
            cases o with
            | none => simp at his
            | some r =>
              simp only [Option.get_some, Finset.mem_filter, aY, r.property, dite_true, true_and]
              exact hfo
          · intro o₁ ho₁ o₂ ho₂ heq
            rcases Finset.mem_filter.mp ho₁ with ⟨_, his₁, _⟩
            rcases Finset.mem_filter.mp ho₂ with ⟨_, his₂, _⟩
            cases o₁ with
            | none => simp at his₁
            | some r₁ =>
              cases o₂ with
              | none => simp at his₂
              | some r₂ =>
                simp only [Option.get_some] at heq
                exact congrArg some (Subtype.ext heq)
          · intro r hr
            rcases Finset.mem_filter.mp hr with ⟨hrY, hfr⟩
            simp only [aY, hrY, dite_true] at hfr
            refine ⟨some ⟨r, hrY⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_some]
            exact hfr
      have hlist : ([f none, φy, δ] : List ℕ).count γ =
          (if f none = γ then 1 else 0) + ([φy, δ] : List ℕ).count γ := by
        simp only [List.count_cons, beq_iff_eq]; split_ifs <;> omega
      omega
    exact hno α hα (f none) (hf_mem none) aY haY γ hcnt_eq
  have hlower : 2 * C_u.card ≤
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card := by
    calc 2 * C_u.card = ∑ _α ∈ C_u, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        no_pcfRep_pair_ge_two (hA_ne α) (by rw [Fintype.card_option, Fintype.card_coe]; omega)
          (hno_rep α hα)
  have hupper :
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card ≤
        3 + 2 * Y.card := by
    rw [sum_filter_card_comm]
    have hsplit_sum :
        ∑ o : Option {r // r ∈ Y}, (C_u.filter (fun α => (A α o).card = 1)).card =
        (C_u.filter (fun α => (A α none).card = 1)).card +
        ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [Fintype.sum_option]
      congr 1
      rw [← Finset.sum_attach Y (fun r => (C_u.filter (fun α => (L r \ {α}).card = 1)).card)]
      rfl
    rw [hsplit_sum]
    have h1 := threeThreadGoodCols_avoid_card_one_le_three C_u (φz := φz) hL1 hL2' hZ3
    have h2 : ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card ≤ 2 * Y.card := by
      calc ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C_u (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    dsimp only [A] at *; omega
  omega

/-- 纯组合 `T21` 定色延拓引理（给定 `u₁ ↦ δ` 时，`T21` 总有合法 PCF 延拓，`3*3 = 9 ≤ 7` 矛盾）！ -/
lemma t21_fixed_color_extension {Ly Aa Lv C2 : Finset ℕ} (cFun : ℕ → ℕ) {φz δ : ℕ}
    (hLy : Ly.card = 2) (hAa : 2 ≤ Aa.card) (hLv : Lv.card = 4) (hC2 : 3 ≤ C2.card) :
    ∃ α ∈ C2, ∃ cy ∈ Ly \ {α}, ∃ ca ∈ Aa \ {α}, ∃ cv ∈ Lv \ {α, cFun α, φz},
    ∃ γ : ℕ, ([cy, ca, cv, δ] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → Fin 3 → Finset ℕ := fun α i =>
    match i with
    | ⟨0, _⟩ => Ly \ {α}
    | ⟨1, _⟩ => Aa \ {α}
    | ⟨2, _⟩ => Lv \ {α, cFun α, φz}
  have hA_ne : ∀ α i, (A α i).Nonempty := by
    intro α i; fin_cases i
    · dsimp only [A]; rw [← Finset.card_pos]; have := card_sdiff_ge Ly {α}; simp at this; omega
    · dsimp only [A]; rw [← Finset.card_pos]; have := card_sdiff_ge Aa {α}; simp at this; omega
    · dsimp only [A]; rw [← Finset.card_pos]; have := card_sdiff_ge Lv {α, cFun α, φz}
      have := card_triple_le α (cFun α) φz; omega
  have hno_rep : ∀ α ∈ C2, ¬ ∃ f : Fin 3 → ℕ, IsPCFRep (A α) [δ] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    have hcnt : ([f 0, f 1, f 2, δ] : List ℕ).count γ = 1 := by
      have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      have hcard_eq : (Finset.univ.filter (fun i : Fin 3 => f i = γ)).card =
          (if f 0 = γ then 1 else 0) + (if f 1 = γ then 1 else 0) +
          (if f 2 = γ then 1 else 0) := by
        rw [Finset.card_filter, hu3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_singleton]
        omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq] at hγ ⊢
      omega
    exact hno α hα (f 0) (hf_mem 0) (f 1) (hf_mem 1) (f 2) (hf_mem 2) γ hcnt
  have hlower : 3 * C2.card ≤
      ∑ α ∈ C2, (Finset.univ.filter (fun i : Fin 3 => (A α i).card = 1)).card := by
    calc 3 * C2.card = ∑ _α ∈ C2, 3 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        (no_pcfRep_single_bounds (hA_ne α) (hno_rep α hα)).2.2.1 (by simp)
  have hupper : ∑ α ∈ C2, (Finset.univ.filter (fun i : Fin 3 => (A α i).card = 1)).card ≤ 7 := by
    rw [sum_filter_card_comm]
    have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [hu3, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 := (card_filter_sdiff_singleton_eq_one_le C2 Ly (by omega)).1
    have h1 := (card_filter_sdiff_singleton_eq_one_le C2 Aa hAa).1
    have h2 := (card_filter_sdiff_triple_eq_one_le C2 Lv hLv cFun φz).1
    dsimp only [A]; omega
  omega

/-- 纯组合 `S3_2(a = 2, b = 0, h ≥ 1)` 定色延拓引理（给定 `u₁ ↦ δ ∉ C2` 时总有合法延拓）！ -/
lemma s32_a2_fixed_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {A₁ A₂ C2 : Finset ℕ} {δ : ℕ}
    (hY1 : 1 ≤ Y.card) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hA1 : 2 ≤ A₁.card) (hA2 : 2 ≤ A₂.card)
    (hC2 : Y.card + 1 ≤ C2.card) (hδC : δ ∉ C2) :
    ∃ α ∈ C2, ∃ c₁ ∈ A₁ \ {α}, ∃ c₂ ∈ A₂ \ {α},
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, c₂, δ] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → {r : V // r ∈ Y} ⊕ Fin 2 → Finset ℕ := fun α s =>
    match s with
    | Sum.inl r => L r.val \ {α}
    | Sum.inr ⟨0, _⟩ => A₁ \ {α}
    | Sum.inr ⟨1, _⟩ => A₂ \ {α}
  have hA_ne : ∀ α s, (A α s).Nonempty := by
    intro α s; rcases s with r | i
    · dsimp only [A]; rw [← Finset.card_pos]; have h1 := card_sdiff_ge (L r.val) {α}
      have h2 := hL2 r.val r.property; simp only [Finset.card_singleton] at h1; omega
    · fin_cases i
      · dsimp only [A]; rw [← Finset.card_pos]; have := card_sdiff_ge A₁ {α}; simp at this; omega
      · dsimp only [A]; rw [← Finset.card_pos]; have := card_sdiff_ge A₂ {α}; simp at this; omega
  have hno_rep : ∀ α ∈ C2, ¬ ∃ f, IsPCFRep (A α) [δ] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (Sum.inl ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (Sum.inl ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt : (Y.filter (fun r => aY r = γ)).card +
        ([f (Sum.inr 0), f (Sum.inr 1), δ] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 2 => f s = γ)).card =
          (Y.filter (fun r => aY r = γ)).card +
          (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) := by
        rw [Finset.card_filter, Fintype.sum_sum_type]
        have hu2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
        have hR : ∑ i : Fin 2, (if f (Sum.inr i) = γ then 1 else 0) =
            (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) := by
          rw [hu2, Finset.sum_insert (by decide), Finset.sum_singleton]
        have hL : ∑ r : {r // r ∈ Y}, (if f (Sum.inl r) = γ then 1 else 0) =
            (Y.filter (fun r => aY r = γ)).card := by
          rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
          apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
        rw [hL, hR]; omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq] at hγ ⊢
      omega
    exact hno α hα (f (Sum.inr 0)) (hf_mem (Sum.inr 0)) (f (Sum.inr 1)) (hf_mem (Sum.inr 1))
      aY haY γ hcnt
  have hlower : 3 * C2.card ≤
      ∑ α ∈ C2, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 2 => (A α s).card = 1)).card := by
    calc 3 * C2.card = ∑ _α ∈ C2, 3 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        (no_pcfRep_single_bounds (hA_ne α) (hno_rep α hα)).2.2.1
          (by rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]; omega)
  have hsum_split :
      ∑ α ∈ C2, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 2 => (A α s).card = 1)).card =
      (∑ r ∈ Y, (C2.filter (fun α => (L r \ {α}).card = 1)).card) +
      (C2.filter (fun α => (A₁ \ {α}).card = 1)).card +
      (C2.filter (fun α => (A₂ \ {α}).card = 1)).card := by
    rw [sum_filter_card_comm, Fintype.sum_sum_type]
    have hu2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    have hR : ∑ i : Fin 2, (C2.filter (fun α => (A α (Sum.inr i)).card = 1)).card =
        (C2.filter (fun α => (A₁ \ {α}).card = 1)).card +
        (C2.filter (fun α => (A₂ \ {α}).card = 1)).card := by
      rw [hu2, Finset.sum_insert (by decide), Finset.sum_singleton]
    have hL : ∑ r : {r // r ∈ Y}, (C2.filter (fun α => (A α (Sum.inl r)).card = 1)).card =
        ∑ r ∈ Y, (C2.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [← Finset.sum_attach Y (fun r => (C2.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
    rw [hL, hR]; omega
  have hY_le : ∑ r ∈ Y, (C2.filter (fun α => (L r \ {α}).card = 1)).card ≤ 2 * Y.card := by
    calc ∑ r ∈ Y, (C2.filter (fun α => (L r \ {α}).card = 1)).card
        ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
          (card_filter_sdiff_singleton_eq_one_le C2 (L r) (by have := hL2 r hr; omega)).1
      _ = 2 * Y.card := by simp [mul_comm]
  have hA1_le := (card_filter_sdiff_singleton_eq_one_le C2 A₁ hA1).1
  have hA2_le := (card_filter_sdiff_singleton_eq_one_le C2 A₂ hA2).1
  -- 于是必有 `Y.card = 1`, `C2.card = 2`，且 `A₁, A₂, L r` 全部是 `C2` 的子集，从而 `δ` 唯一！
  have hY_eq1 : Y.card = 1 := by omega
  have hC2_eq2 : C2.card = 2 := by omega
  have hA1_eq2 : (C2.filter (fun α => (A₁ \ {α}).card = 1)).card = 2 := by omega
  have hA2_eq2 : (C2.filter (fun α => (A₂ \ {α}).card = 1)).card = 2 := by omega
  have hY_eq2 : ∑ r ∈ Y, (C2.filter (fun α => (L r \ {α}).card = 1)).card = 2 := by omega
  have hA1_sub : A₁ ⊆ C2 := ((card_filter_sdiff_singleton_eq_one_le C2 A₁ hA1).2 hA1_eq2).2
  have hA2_sub : A₂ ⊆ C2 := ((card_filter_sdiff_singleton_eq_one_le C2 A₂ hA2).2 hA2_eq2).2
  rcases Finset.card_eq_one.mp hY_eq1 with ⟨y, hy_eq⟩
  have hy_Y : y ∈ Y := by rw [hy_eq]; simp
  have hLy_eq2 : (C2.filter (fun α => (L y \ {α}).card = 1)).card = 2 := by
    rw [hy_eq, Finset.sum_singleton] at hY_eq2; exact hY_eq2
  have hLy_sub : L y ⊆ C2 :=
    ((card_filter_sdiff_singleton_eq_one_le C2 (L y) (by have := hL2 y hy_Y; omega)).2 hLy_eq2).2
  rcases Finset.card_pos.mp (by omega : 0 < C2.card) with ⟨α₀, hα₀⟩
  apply hno_rep α₀ hα₀
  refine ⟨fun s => (hA_ne α₀ s).choose, fun s => (hA_ne α₀ s).choose_spec, δ, ?_⟩
  have hzero : (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 2 =>
      (hA_ne α₀ s).choose = δ)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _ heq
    have hmem := (hA_ne α₀ s).choose_spec
    rw [heq] at hmem
    rcases s with ⟨r, hr⟩ | i
    · have hry : r = y := by rw [hy_eq, Finset.mem_singleton] at hr; exact hr
      simp only [A, hry, Finset.mem_sdiff] at hmem; exact hδC (hLy_sub hmem.1)
    · fin_cases i
      · simp only [A, Finset.mem_sdiff] at hmem; exact hδC (hA1_sub hmem.1)
      · simp only [A, Finset.mem_sdiff] at hmem; exact hδC (hA2_sub hmem.1)
  rw [hzero]; simp

/-- 若某叶点 `r₀ ∈ Y` 满足 `Disjoint (L r₀) C_u`，则 `C_u.card ≥ Y.card` 即足以让 `T3` 延拓！ -/
lemma t3_fixed_color_extension_disj_leaf {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {L₁ L₂ Z₃ C_u : Finset ℕ} {φy φz δ : ℕ} {r₀ : V}
    (hr0 : r₀ ∈ Y) (hdisj : Disjoint (L r₀) C_u) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hL1 : L₁.card = 4) (hL2' : L₂.card = 4) (hZ3 : 2 ≤ Z₃.card)
    (hCu : Y.card ≤ C_u.card) :
    ∃ α ∈ C_u, ∃ c₁ ∈ threeThreadGoodCols L₁ L₂ Z₃ φz α,
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, φy, δ] : List ℕ).count γ = 1 := by
  classical
  have hY1 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨r₀, hr0⟩
  by_contra hno
  push Not at hno
  let A : ℕ → Option {r : V // r ∈ Y} → Finset ℕ := fun α o =>
    match o with
    | none => threeThreadGoodCols L₁ L₂ Z₃ φz α
    | some r => L r.val \ {α}
  have hA_ne : ∀ α o, (A α o).Nonempty := by
    intro α o; cases o with
    | none => exact threeThreadGoodCols_nonempty hL1 hL2' (Finset.card_pos.mp (by omega))
    | some r =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}; have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C_u, ¬ ∃ f, IsPCFRep (A α) [φy, δ] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (some ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (some ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt_eq : (Y.filter (fun r => aY r = γ)).card +
        ([f none, φy, δ] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ)).card =
          (if f none = γ then 1 else 0) + (Y.filter (fun r => aY r = γ)).card := by
        rw [Finset.card_filter, Fintype.sum_option]
        congr 1
        rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
        apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
      have hlist : ([f none, φy, δ] : List ℕ).count γ =
          (if f none = γ then 1 else 0) + ([φy, δ] : List ℕ).count γ := by
        simp only [List.count_cons, beq_iff_eq]; split_ifs <;> omega
      omega
    exact hno α hα (f none) (hf_mem none) aY haY γ hcnt_eq
  have hlower : 2 * C_u.card ≤
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card := by
    calc 2 * C_u.card = ∑ _α ∈ C_u, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        no_pcfRep_pair_ge_two (hA_ne α) (by rw [Fintype.card_option, Fintype.card_coe]; omega)
          (hno_rep α hα)
  have hr0_zero : (C_u.filter (fun α => (L r₀ \ {α}).card = 1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro α hα hcard1
    have hnot : α ∉ L r₀ := Finset.disjoint_right.mp hdisj hα
    have hEq : L r₀ \ {α} = L r₀ := by
      ext t; simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨And.left, fun ht => ⟨ht, fun h => hnot (h ▸ ht)⟩⟩
    rw [hEq, hL2 r₀ hr0] at hcard1; omega
  have hupper :
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card ≤
        1 + 2 * (Y.card - 1) := by
    rw [sum_filter_card_comm, Fintype.sum_option]
    have h1 := threeThreadGoodCols_card_one_le_one C_u (φz := φz) hL1 hL2' hZ3
    have hsumY : ∑ r : {r // r ∈ Y}, (C_u.filter (fun α => (A α (some r)).card = 1)).card =
        ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [← Finset.sum_attach Y (fun r => (C_u.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
    rw [hsumY]
    have hY_erase : ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card =
        (C_u.filter (fun α => (L r₀ \ {α}).card = 1)).card +
        ∑ r ∈ Y.erase r₀, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [← Finset.add_sum_erase _ _ hr0]
    have hrest : ∑ r ∈ Y.erase r₀, (C_u.filter (fun α => (L r \ {α}).card = 1)).card ≤
        2 * (Y.card - 1) := by
      calc ∑ r ∈ Y.erase r₀, (C_u.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y.erase r₀, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C_u (L r)
              (by have := hL2 r (Finset.mem_of_mem_erase hr); omega)).1
        _ = 2 * (Y.erase r₀).card := by simp [mul_comm]
        _ = 2 * (Y.card - 1) := by rw [Finset.card_erase_of_mem hr0]
    dsimp only [A] at *; omega
  omega

/-- 若 `|C| ≥ |Y| + 1` 且对所有 `r ∈ Y` 有 `|L r| = 2`，则存在 `c ∈ C` 使每个叶点都能避开 `{c, β}`！ -/
lemma exists_color_leaves_avoid {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {C : Finset ℕ} {β : ℕ}
    (hL2 : ∀ r ∈ Y, (L r).card = 2) (hC : Y.card + 1 ≤ C.card) :
    ∃ c ∈ C, ∀ r ∈ Y, ∃ a ∈ L r, a ≠ c ∧ a ≠ β := by
  classical
  have hbad_le : ∀ r ∈ Y, (C.filter (fun c => L r = {c, β})).card ≤ 1 := by
    intro r _
    rw [Finset.card_le_one]
    intro c₁ h1 c₂ h2
    simp only [Finset.mem_filter] at h1 h2
    have heq : ({c₁, β} : Finset ℕ) = {c₂, β} := h1.2.symm.trans h2.2
    by_cases h1β : c₁ = β
    · subst h1β
      have hc2 : c₂ ∈ ({c₁, c₁} : Finset ℕ) := by rw [heq]; simp
      exact (by simpa using hc2 : c₂ = c₁).symm
    · have hc1 : c₁ ∈ ({c₂, β} : Finset ℕ) := by rw [← heq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1
      exact hc1.resolve_right h1β
  have hbi_card : (Y.biUnion (fun r => C.filter (fun c => L r = {c, β}))).card ≤ Y.card := by
    calc (Y.biUnion (fun r => C.filter (fun c => L r = {c, β}))).card
        ≤ ∑ r ∈ Y, (C.filter (fun c => L r = {c, β})).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ Y, 1 := Finset.sum_le_sum hbad_le
      _ = Y.card := by simp
  rcases exists_mem_sdiff_of_lt (A := C)
      (B := Y.biUnion (fun r => C.filter (fun c => L r = {c, β}))) (by omega) with ⟨c, hcC, hcnot⟩
  refine ⟨c, hcC, fun r hr => ?_⟩
  have hne : L r ≠ {c, β} := fun h =>
    hcnot (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hcC, h⟩⟩)
  have hsub : ¬ L r ⊆ {c, β} := by
    intro hs
    have hcard : ({c, β} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    have hLr2 := hL2 r hr
    exact hne (Finset.eq_of_subset_of_card_le hs (by omega))
  rw [Finset.not_subset] at hsub
  rcases hsub with ⟨a, haL, hanot⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hanot
  exact ⟨a, haL, hanot.1, hanot.2⟩

/-! ## 2. 通用图论 PCF 校验与 `T3` 拆解引理 -/

/-- 若 `u` 的邻点恰为 `n₁, n₂, n₃`（两两互异）与叶集 `Y`（不交），且 `γ` 在其中总出现次数为 1，
则 `u` 满足 PCF！ -/
lemma pcf_from_leaf_and_three {V : Type*}
    {G : SimpleGraph V} {ψ aY : V → ℕ} {u n₁ n₂ n₃ : V} {Y : Finset V} {γ : ℕ}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (hn1Y : n₁ ∉ Y) (hn2Y : n₂ ∉ Y) (hn3Y : n₃ ∉ Y)
    (hYadj : ∀ r ∈ Y, G.Adj u r) (hYψ : ∀ r ∈ Y, ψ r = aY r)
    (hall : ∀ r, G.Adj u r → r = n₁ ∨ r = n₂ ∨ r = n₃ ∨ r ∈ Y)
    (hcnt : (Y.filter (fun r => aY r = γ)).card + ([ψ n₁, ψ n₂, ψ n₃] : List ℕ).count γ = 1) :
    ∃ w, G.Adj u w ∧ ∀ r, G.Adj u r → ψ r = ψ w → r = w := by
  classical
  by_cases h1γ : ψ n₁ = γ
  · have h2γ : ψ n₂ ≠ γ := by
      intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h, ite_true] at hcnt
      omega
    have h3γ : ψ n₃ ≠ γ := by
      intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h, ite_true] at hcnt
      omega
    have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
      simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ,
        ite_true, ite_false] at hcnt
      omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    refine ⟨n₁, h1, fun r hur hψ => ?_⟩
    rw [h1γ] at hψ
    rcases hall r hur with rfl | rfl | rfl | hrY
    · rfl
    · exact False.elim (h2γ hψ)
    · exact False.elim (h3γ hψ)
    · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
  · by_cases h2γ : ψ n₂ = γ
    · have h3γ : ψ n₃ ≠ γ := by
        intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h2γ, h, ite_true] at hcnt
        omega
      have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ,
          ite_true, ite_false] at hcnt
        omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
      refine ⟨n₂, h2, fun r hur hψ => ?_⟩
      rw [h2γ] at hψ
      rcases hall r hur with rfl | rfl | rfl | hrY
      · exact False.elim (h1γ hψ)
      · rfl
      · exact False.elim (h3γ hψ)
      · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
    · by_cases h3γ : ψ n₃ = γ
      · have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
          simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ,
            ite_true, ite_false] at hcnt
          omega
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
        refine ⟨n₃, h3, fun r hur hψ => ?_⟩
        rw [h3γ] at hψ
        rcases hall r hur with rfl | rfl | rfl | hrY
        · exact False.elim (h1γ hψ)
        · exact False.elim (h2γ hψ)
        · rfl
        · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
      · have hone : (Y.filter (fun r => aY r = γ)).card = 1 := by
          simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ,
            ite_false] at hcnt
          omega
        rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
        have hw₀_mem : w₀ ∈ Y.filter (fun r => aY r = γ) := by rw [hw₀_eq]; simp
        rw [Finset.mem_filter] at hw₀_mem
        refine ⟨w₀, hYadj w₀ hw₀_mem.1, fun r hur hψ => ?_⟩
        rw [hYψ w₀ hw₀_mem.1, hw₀_mem.2] at hψ
        rcases hall r hur with rfl | rfl | rfl | hrY
        · exact False.elim (h1γ hψ)
        · exact False.elim (h2γ hψ)
        · exact False.elim (h3γ hψ)
        · have : r ∈ Y.filter (fun t => aY t = γ) :=
            Finset.mem_filter.mpr ⟨hrY, (hYψ r hrY).symm.trans hψ⟩
          rw [hw₀_eq, Finset.mem_singleton] at this; exact this

/-- 若 4-度点 `u` 的四个邻点 `n₁, n₂, n₃, n₄` 中颜色 `γ` 恰好出现一次，则 `u` 满足 PCF！ -/
lemma pcf_from_four_list {V : Type*} {G : SimpleGraph V} {ψ : V → ℕ} {u n₁ n₂ n₃ n₄ : V} {γ : ℕ}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃) (h4 : G.Adj u n₄)
    (hall : ∀ r, G.Adj u r → r = n₁ ∨ r = n₂ ∨ r = n₃ ∨ r = n₄)
    (hcnt : ([ψ n₁, ψ n₂, ψ n₃, ψ n₄] : List ℕ).count γ = 1) :
    ∃ w, G.Adj u w ∧ ∀ r, G.Adj u r → ψ r = ψ w → r = w := by
  by_cases h1γ : ψ n₁ = γ
  · have h2γ : ψ n₂ ≠ γ := by
      intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h, ite_true] at hcnt
      omega
    have h3γ : ψ n₃ ≠ γ := by
      intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h, ite_true] at hcnt
      omega
    have h4γ : ψ n₄ ≠ γ := by
      intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h, ite_true] at hcnt
      omega
    refine ⟨n₁, h1, fun r hur hψ => ?_⟩; rw [h1γ] at hψ
    rcases hall r hur with rfl | rfl | rfl | rfl
    · rfl
    · exact False.elim (h2γ hψ)
    · exact False.elim (h3γ hψ)
    · exact False.elim (h4γ hψ)
  · by_cases h2γ : ψ n₂ = γ
    · have h3γ : ψ n₃ ≠ γ := by
        intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h2γ, h, ite_true] at hcnt
        omega
      have h4γ : ψ n₄ ≠ γ := by
        intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h2γ, h, ite_true] at hcnt
        omega
      refine ⟨n₂, h2, fun r hur hψ => ?_⟩; rw [h2γ] at hψ
      rcases hall r hur with rfl | rfl | rfl | rfl
      · exact False.elim (h1γ hψ)
      · rfl
      · exact False.elim (h3γ hψ)
      · exact False.elim (h4γ hψ)
    · by_cases h3γ : ψ n₃ = γ
      · have h4γ : ψ n₄ ≠ γ := by
          intro h
          simp only [List.count_cons, List.count_nil, beq_iff_eq, h3γ, h, ite_true] at hcnt
          omega
        refine ⟨n₃, h3, fun r hur hψ => ?_⟩; rw [h3γ] at hψ
        rcases hall r hur with rfl | rfl | rfl | rfl
        · exact False.elim (h1γ hψ)
        · exact False.elim (h2γ hψ)
        · rfl
        · exact False.elim (h4γ hψ)
      · have h4γ : ψ n₄ = γ := by
          by_contra h
          simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h,
            ite_false] at hcnt
          omega
        refine ⟨n₄, h4, fun r hur hψ => ?_⟩; rw [h4γ] at hψ
        rcases hall r hur with rfl | rfl | rfl | rfl
        · exact False.elim (h1γ hψ)
        · exact False.elim (h2γ hψ)
        · exact False.elim (h3γ hψ)
        · rfl

/-- `IsT3 G u` 的完整几何拆解：给出唯一 `3`-线串 `u - v₁ - v₂ - v₃ - z`（且 `4 ≤ d(z)`、`z ≠ u`）
与两个互异好邻点 `x ≠ y`。 -/
lemma isT3_unpack {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (hu : IsT3 G u) :
    ∃ v₁ v₂ v₃ z x y : V,
      G.Adj u v₁ ∧ G.degree v₁ = 2 ∧
      G.Adj v₁ v₂ ∧ v₂ ≠ u ∧ G.degree v₂ = 2 ∧
      G.Adj v₂ v₃ ∧ v₃ ≠ v₁ ∧ G.degree v₃ = 2 ∧
      G.Adj v₃ z ∧ z ≠ v₂ ∧ 4 ≤ G.degree z ∧ z ≠ u ∧
      x ∈ goodNbrs G u ∧ y ∈ goodNbrs G u ∧ x ≠ y ∧
      coreNbrs G u = {v₁, x, y} ∧
      1 ≤ (leafNbrs G u).card ∧ (leafNbrs G u).card = G.degree u - 3 ∧
      (∀ r, G.Adj u r → r = v₁ ∨ r = x ∨ r = y ∨ r ∈ leafNbrs G u) ∧
      (∀ r, G.Adj v₁ r → r = u ∨ r = v₂) ∧
      (∀ r, G.Adj v₂ r → r = v₁ ∨ r = v₃) ∧
      (∀ r, G.Adj v₃ r → r = v₂ ∨ r = z) := by
  classical
  have hst := isT3_structure hm hpq hu
  rcases hu with ⟨hc3, ⟨v₁, hv₁⟩⟩
  have hv1_3 := mem_threeThreadNbrs.mp hv₁
  rcases hv1_3 with ⟨huv₁, hdv₁, v₂, v₃, z, hv12, hv2u, hdv₂, hv23, hv31, hdv₃, hv3z, hzv2, hdz3⟩
  have hzu : z ≠ u := fun h =>
    no_three_thread_same_anchor hm (by omega) hdv₁ hdv₂ hdv₃ huv₁ hv12 hv23 (h ▸ hv3z) hv31.symm
  have hdz4 : 4 ≤ G.degree z := by
    have hv3long : v₃ ∈ longThreadNbrs G z := by
      unfold longThreadNbrs degTwoNbrs
      rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hv3z.symm, hdv₃⟩, hv3z.symm, hdv₃, v₂, hv23.symm, hzv2.symm, hdv₂⟩
    exact deg_ge_four_of_longThreadNbr hm hdz3 hv3long
  rcases Finset.card_eq_two.mp hst.2.2.2.2.2 with ⟨x, y, hxy, hgood_eq⟩
  have hx : x ∈ goodNbrs G u := by rw [hgood_eq]; simp
  have hy : y ∈ goodNbrs G u := by rw [hgood_eq]; simp
  have hdx3 : 3 ≤ G.degree x := deg_ge_three_of_isGood (mem_goodNbrs.mp hx).2
  have hdy3 : 3 ≤ G.degree y := deg_ge_three_of_isGood (mem_goodNbrs.mp hy).2
  have hv1x : v₁ ≠ x := fun h => by subst h; omega
  have hv1y : v₁ ≠ y := fun h => by subst h; omega
  have hcore_eq : coreNbrs G u = {v₁, x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv₁, by omega⟩
      · exact mem_coreNbrs.mpr ⟨(mem_goodNbrs.mp hx).1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨(mem_goodNbrs.mp hy).1, by omega⟩
    · rw [Finset.card_insert_of_notMem (by simp [hv1x, hv1y]), Finset.card_pair hxy]
      unfold coreDeg at hc3; omega
  have hleaf_eq : (leafNbrs G u).card = G.degree u - 3 := by
    have := coreDeg_add_leafNbrs hm u; omega
  have hall_u : ∀ r, G.Adj u r → r = v₁ ∨ r = x ∨ r = y ∨ r ∈ leafNbrs G u := by
    intro r hur
    have hr1 := degree_ge_one hm r
    by_cases hdr : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, hdr⟩)))
    · have hrc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_eq] at hrc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrc
      rcases hrc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  rcases exists_other_neighbor_of_deg_two hdv₁ huv₁.symm with ⟨w₁, _, _, hall1⟩
  have hall_v1 : ∀ r, G.Adj v₁ r → r = u ∨ r = v₂ := fun r hr => by
    rcases hall1 r hr with rfl | hrw
    · exact Or.inl rfl
    · exact Or.inr (hrw.trans ((hall1 v₂ hv12).resolve_left hv2u).symm)
  rcases exists_other_neighbor_of_deg_two hdv₂ hv12.symm with ⟨w₂, _, _, hall2⟩
  have hall_v2 : ∀ r, G.Adj v₂ r → r = v₁ ∨ r = v₃ := fun r hr => by
    rcases hall2 r hr with rfl | hrw
    · exact Or.inl rfl
    · exact Or.inr (hrw.trans ((hall2 v₃ hv23).resolve_left hv31).symm)
  rcases exists_other_neighbor_of_deg_two hdv₃ hv23.symm with ⟨w₃, _, _, hall3⟩
  have hall_v3 : ∀ r, G.Adj v₃ r → r = v₂ ∨ r = z := fun r hr => by
    rcases hall3 r hr with rfl | hrw
    · exact Or.inl rfl
    · exact Or.inr (hrw.trans ((hall3 z hv3z).resolve_left hzv2).symm)
  exact ⟨v₁, v₂, v₃, z, x, y, huv₁, hdv₁, hv12, hv2u, hdv₂, hv23, hv31, hdv₃, hv3z, hzv2, hdz4,
    hzu, hx, hy, hxy, hcore_eq, by omega, hleaf_eq, hall_u, hall_v1, hall_v2, hall_v3⟩

/-! ## 3. 引理 E0：`T3` 顶点没有 `3`-度邻点（消灭 `T3 -- G32` 等一切 `3`-度邻点） -/

/-- 引理 E0：`T3` 顶点不能与任何 `3`-度顶点相邻！ -/
lemma no_T3_adj_deg_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u x₀ : V}
    (hu : IsT3 G u) (hux₀ : G.Adj u x₀) (hdx₀ : G.degree x₀ = 3) : False := by
  classical
  rcases isT3_unpack hm hpq hu with
    ⟨v₁, v₂, v₃, z, x₁, y₁, huv₁, hdv₁, hv12, hv2u, hdv₂, hv23, hv31, hdv₃, hv3z, hzv2, hdz4,
      hzu, hx₁, hy₁, hxy₁, hcore_eq, hY1, hYcard, hall_u, hall_v1, hall_v2, hall_v3⟩
  -- 因 `d(x₀) = 3` 且 `x₀ ∈ coreNbrs G u = {v₁, x₁, y₁}`，故 `x₀ = x₁` 或 `x₀ = y₁`；令 `y` 为另一好邻点！
  have hx₀_core : x₀ ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hux₀, by omega⟩
  rw [hcore_eq] at hx₀_core
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₀_core
  have hx₀_ne_v1 : x₀ ≠ v₁ := fun h => by subst h; omega
  have hex_y : ∃ y : V, y ∈ goodNbrs G u ∧ y ≠ x₀ ∧
      ∀ r, G.Adj u r → r = v₁ ∨ r = x₀ ∨ r = y ∨ r ∈ leafNbrs G u := by
    rcases hx₀_core with h | rfl | rfl
    · exact False.elim (hx₀_ne_v1 h)
    · exact ⟨y₁, hy₁, hxy₁.symm, hall_u⟩
    · exact ⟨x₁, hx₁, hxy₁, fun r hr => by
        rcases hall_u r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y with ⟨y, hy, hyx₀, hu_all⟩
  have huy : G.Adj u y := (mem_goodNbrs.mp hy).1
  have hdy3 : 3 ≤ G.degree y := deg_ge_three_of_isGood (mem_goodNbrs.mp hy).2
  let Y := leafNbrs G u
  let S : Finset V := insert u (insert v₁ (insert v₂ (insert v₃ Y)))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hv3u : v₃ ≠ u := fun h => by subst h; have := coreDeg_le_degree G v₃; have := hu.1; omega
  have hv1_not_Y : v₁ ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hv2_not_Y : v₂ ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hv3_not_Y : v₃ ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hx₀_not_S : x₀ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨(G.ne_of_adj hux₀).symm, hx₀_ne_v1, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hy_not_S : y ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨(G.ne_of_adj huy).symm, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz_not_S : z ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hzu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hzx₀ : z ≠ x₀ := fun h => by subst h; omega
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = u ∧ (s = x₀ ∨ s = y)) ∨ (r = v₃ ∧ s = z) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | hrY
    · rcases hu_all s hsr.symm with rfl | rfl | rfl | hsY
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, Or.inl rfl⟩
      · exact Or.inl ⟨rfl, Or.inr rfl⟩
      · exact False.elim (hsS (by
          simp only [S, Y, Finset.mem_insert]; exact Or.inr (Or.inr (Or.inr (Or.inr hsY)))))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr ⟨rfl, rfl⟩
    · have hrL := mem_leafNbrs.mp hrY
      rcases exists_unique_neighbor_of_deg_one hrL.2 with ⟨t, _, huniq⟩
      have hsu : s = u := (huniq s hsr.symm).trans (huniq u hrL.1.symm).symm
      exact False.elim (hsS (hsu ▸ huS))
  -- `x₀` 在 `G - S` 中恰有两个外部邻点 `w₁ ≠ w₂`！
  rcases exists_two_other_neighbors_of_deg_three (x := u) hdx₀ with
    ⟨w₁, w₂, hw1u, hw2u, hw12, hx0w1, hx0w2⟩
  have hw_not_S : ∀ w, G.Adj x₀ w → w ≠ u → w ∉ S := by
    intro w hxw hwu hwS
    rcases hS_out x₀ hx₀_not_S w hwS hxw with ⟨rfl, _⟩ | ⟨_, hzx⟩
    · exact hwu rfl
    · exact hzx₀ hzx.symm
  have hw1_not_S : w₁ ∉ S := hw_not_S w₁ hx0w1 hw1u
  have hw2_not_S : w₂ ∉ S := hw_not_S w₂ hx0w2 hw2u
  -- 关键：`x₀` 在 `G - S` 中的连通分支不可能是 `C₅`（否则 `x₀` 关联 `2`-线串，矛盾！），故可取真 PCF 染色使 `w₁, w₂` 异色！
  let H := G.induce ((Sᶜ : Finset V) : Set V)
  have hx₀S' : x₀ ∈ (Sᶜ : Finset V) := Finset.mem_compl.mpr hx₀_not_S
  let C₀ := H.connectedComponentMk ⟨x₀, hx₀S'⟩
  let T := compFinset S C₀
  have hx₀T : x₀ ∈ T := (mem_compFinset S C₀ x₀).mpr ⟨hx₀S', rfl⟩
  have hTsub : T ⊆ Sᶜ := fun r hr => ((mem_compFinset S C₀ r).mp hr).1
  have hTclosed : ∀ a ∈ T, ∀ b, b ∉ S → G.Adj a b → b ∈ T := by
    intro a ha b hbS hab
    rcases (mem_compFinset S C₀ a).mp ha with ⟨haS, haC⟩
    have hbS' : b ∈ (Sᶜ : Finset V) := Finset.mem_compl.mpr hbS
    have hreach : H.Reachable ⟨a, haS⟩ ⟨b, hbS'⟩ :=
      SimpleGraph.Adj.reachable (show H.Adj ⟨a, haS⟩ ⟨b, hbS'⟩ from hab)
    exact (mem_compFinset S C₀ b).mpr
      ⟨hbS', (SimpleGraph.ConnectedComponent.sound hreach).symm.trans haC⟩
  have hw1T : w₁ ∈ T := hTclosed x₀ hx₀T w₁ hw1_not_S hx0w1
  have hw2T : w₂ ∈ T := hTclosed x₀ hx₀T w₂ hw2_not_S hx0w2
  let F := G.induce (T : Set V)
  have hTconn : F.Connected := induced_comp_connected S C₀
  have hTne_univ : T ≠ Finset.univ := fun heq =>
    (Finset.mem_compl.mp (hTsub (heq ▸ Finset.mem_univ u))) huS
  have hT_not_C5 : ¬ IsC5 F := by
    intro hC5
    rcases exists_c5_cycle hTconn hC5 ⟨x₀, hx₀T⟩ with
      ⟨c₁, c₂, c₃, c₄, _, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
        ha01, ha12, ha23, ha34, ha40⟩
    have hdeg_of_not_y : ∀ c : {r : V // r ∈ (T : Set V)},
        c.val ≠ x₀ → c.val ≠ y → G.degree c.val = 2 := by
      intro c hc0 hcy
      have hcS : c.val ∉ S := Finset.mem_compl.mp (hTsub c.property)
      have hnoS : ∀ s ∈ S, ¬ G.Adj c.val s := by
        intro s hsS hcs
        rcases hS_out c.val hcS s hsS hcs with ⟨_, hc0' | hcy'⟩ | ⟨_, hcz⟩
        · exact hc0 hc0'
        · exact hcy hcy'
        · have hsub : G.neighborFinset c.val ⊆
              (F.neighborFinset c).image Subtype.val ∪ {v₃} := by
            intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
            by_cases hrS : r ∈ S
            · rcases hS_out c.val hcS r hrS hr with ⟨_, hc0' | hcy'⟩ | ⟨hrv3, _⟩
              · exact False.elim (hc0 hc0')
              · exact False.elim (hcy hcy')
              · simp [hrv3]
            · have hrT : r ∈ T := hTclosed c.val c.property r hrS hr
              exact Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨⟨r, hrT⟩, (F.mem_neighborFinset c ⟨r, hrT⟩).mpr hr, rfl⟩)
          have hle := Finset.card_le_card hsub
          have hun := Finset.card_union_le ((F.neighborFinset c).image Subtype.val) {v₃}
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
              SimpleGraph.card_neighborFinset_eq_degree, hC5.2 c, Finset.card_singleton] at hun
          rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
          have hdz_c : 4 ≤ G.degree c.val := hcz ▸ hdz4
          omega
      have hEq : G.neighborFinset c.val = (F.neighborFinset c).image Subtype.val := by
        ext r; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
        constructor
        · intro hr
          have hrS : r ∉ S := fun h => hnoS r h hr
          have hrT : r ∈ T := hTclosed c.val c.property r hrS hr
          exact ⟨⟨r, hrT⟩, hr, rfl⟩
        · rintro ⟨w, hw, rfl⟩; exact hw
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hEq,
          Finset.card_image_of_injective _ Subtype.val_injective,
          SimpleGraph.card_neighborFinset_eq_degree, hC5.2 c]
    have hval_ne : ∀ {a b : {r : V // r ∈ (T : Set V)}}, a ≠ b → a.val ≠ b.val :=
      fun h hv => h (Subtype.ext hv)
    by_cases hy12 : c₁.val = y ∨ c₂.val = y
    · have h4ne : c₄.val ≠ y := fun h => by
        rcases hy12 with h1 | h2
        · exact hval_ne h14 (h1.trans h.symm)
        · exact hval_ne h24 (h2.trans h.symm)
      have h3ne : c₃.val ≠ y := fun h => by
        rcases hy12 with h1 | h2
        · exact hval_ne h13 (h1.trans h.symm)
        · exact hval_ne h23 (h2.trans h.symm)
      have hd4 := hdeg_of_not_y c₄ (hval_ne h04.symm) h4ne
      have hd3 := hdeg_of_not_y c₃ (hval_ne h03.symm) h3ne
      exact no_three_vertex_two_thread hm hdx₀ hd4 hd3 ha40.symm ha34.symm
    · push Not at hy12
      have hd1 := hdeg_of_not_y c₁ (hval_ne h01.symm) hy12.1
      have hd2 := hdeg_of_not_y c₂ (hval_ne h02.symm) hy12.2
      exact no_three_vertex_two_thread hm hdx₀ hd1 hd2 ha01 ha12
  have hLF : ∀ v : {r : V // r ∈ (T : Set V)}, kappa F v ≤ (L v.val).card := fun v => by
    rw [hm.list_card v.val]; exact kappa_mono (degree_induce_le G T v)
  rcases hm.minimal T ⟨x₀, hx₀T⟩ hTne_univ hTconn hT_not_C5 (fun v => L v.val) hLF with
    ⟨φF, ⟨hpropF, hpcfF⟩, hmemF⟩
  have hw_col_ne : φF ⟨w₁, hw1T⟩ ≠ φF ⟨w₂, hw2T⟩ := by
    rcases hpcfF ⟨x₀, hx₀T⟩ ⟨⟨w₁, hw1T⟩, hx0w1⟩ with ⟨⟨w, hwT⟩, hx0w, huniq⟩
    have hallx0 : ∀ r, G.Adj x₀ r → r = u ∨ r = w₁ ∨ r = w₂ := by
      have hsub : ({u, w₁, w₂} : Finset V) ⊆ G.neighborFinset x₀ := by
        intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rw [SimpleGraph.mem_neighborFinset]
        rcases hr with rfl | rfl | rfl
        · exact hux₀.symm
        · exact hx0w1
        · exact hx0w2
      have hEq : ({u, w₁, w₂} : Finset V) = G.neighborFinset x₀ :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [SimpleGraph.card_neighborFinset_eq_degree, hdx₀,
              Finset.card_insert_of_notMem (by simp [hw1u.symm, hw2u.symm]),
              Finset.card_pair hw12])
      intro r hr
      have : r ∈ ({u, w₁, w₂} : Finset V) := by rw [hEq, SimpleGraph.mem_neighborFinset]; exact hr
      simpa using this
    intro heq
    rcases hallx0 w hx0w with rfl | rfl | rfl
    · exact (Finset.mem_compl.mp (hTsub hwT)) huS
    · exact hw12.symm (congrArg Subtype.val (huniq ⟨w₂, hw2T⟩ hx0w2 heq.symm))
    · exact hw12 (congrArg Subtype.val (huniq ⟨w₁, hw1T⟩ hx0w1 heq))
  -- 在 `G - S` 的其余连通分支用 `exists_admissible_coloring`，在 `T` 上覆写为 `φF`！
  rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm0⟩
  have hφsF_ex : ∀ v : V, ∃ c : ℕ, ∀ (hv : v ∈ T), (∃ w ∈ T, G.Adj v w) →
      ∃ t, ∃ ht : t ∈ T, G.Adj v t ∧ φF ⟨t, ht⟩ = c ∧
        ∀ w, ∀ hw : w ∈ T, G.Adj v w → φF ⟨w, hw⟩ = c → w = t := by
    intro v
    by_cases hc : ∃ (hv : v ∈ T), ∃ w ∈ T, G.Adj v w
    · rcases hc with ⟨hv, w, hw, hvw⟩
      rcases hpcfF ⟨v, hv⟩ ⟨⟨w, hw⟩, hvw⟩ with ⟨⟨t, ht⟩, hvt, huniq⟩
      exact ⟨φF ⟨t, ht⟩, fun _ _ => ⟨t, ht, hvt, rfl, fun r hr hvr hφr =>
        congrArg Subtype.val (huniq ⟨r, hr⟩ hvr hφr)⟩⟩
    · exact ⟨0, fun hv hw => False.elim (hc ⟨hv, hw⟩)⟩
  choose φsF hφsF using hφsF_ex
  let adm : AdmissibleColoring G L S :=
    { φ := fun r => if hr : r ∈ T then φF ⟨r, hr⟩ else adm0.φ r
      φs := fun r => if r ∈ T then φsF r else adm0.φs r
      mem_list := fun r hrS => by
        by_cases hrT : r ∈ T
        · simp only [hrT, dite_true]; exact hmemF ⟨r, hrT⟩
        · simp only [hrT, dite_false]; exact adm0.mem_list r hrS
      proper := fun a b haS hbS hab => by
        by_cases haT : a ∈ T
        · have hbT : b ∈ T := hTclosed a haT b hbS hab
          simp only [haT, hbT, dite_true]; exact hpropF ⟨a, haT⟩ ⟨b, hbT⟩ hab
        · have hbT : b ∉ T := fun h => haT (hTclosed b h a haS hab.symm)
          simp only [haT, hbT, dite_false]; exact adm0.proper a b haS hbS hab
      pcf_preserve := fun ψ hagree r hrS hnoniso havoid => by
        by_cases hrT : r ∈ T
        · rcases hnoniso with ⟨w0, hw0S, hrw0⟩
          have hw0T : w0 ∈ T := hTclosed r hrT w0 hw0S hrw0
          rcases hφsF r hrT ⟨w0, hw0T, hrw0⟩ with ⟨t, htT, hrt, hφt, huniq⟩
          refine ⟨t, hrt, fun w hrw hψw => ?_⟩
          have htS : t ∉ S := Finset.mem_compl.mp (hTsub htT)
          have hψt : ψ t = φsF r := by rw [hagree t htS]; simp only [htT, dite_true]; exact hφt
          by_cases hwS : w ∈ S
          · have hav := havoid w hwS hrw
            simp only [hrT, ite_true] at hav
            exact False.elim (hav (hψw.trans hψt))
          · have hwT : w ∈ T := hTclosed r hrT w hwS hrw
            have hψw' : φF ⟨w, hwT⟩ = φsF r := by
              have := hagree w hwS; simp only [hwT, dite_true] at this
              rw [← this, hψw, hψt]
            exact huniq w hwT hrw hψw'
        · have hagree0 : ∀ x, x ∉ S → (if x ∈ T then adm0.φ x else ψ x) = adm0.φ x := by
            intro x hxS; split_ifs with hxT
            · rfl
            · rw [hagree x hxS]; simp only [hxT, dite_false]
          have hnon0 : ∃ w, w ∉ S ∧ G.Adj r w := hnoniso
          have hav0 : ∀ w ∈ S, G.Adj r w → (if w ∈ T then adm0.φ w else ψ w) ≠ adm0.φs r := by
            intro w hwS hrw
            have hwT : w ∉ T := fun h => (Finset.mem_compl.mp (hTsub h)) hwS
            simp only [hwT, ite_false]
            have hav := havoid w hwS hrw; simp only [hrT, ite_false] at hav; exact hav
          rcases adm0.pcf_preserve (fun x => if x ∈ T then adm0.φ x else ψ x)
              hagree0 r hrS hnon0 hav0 with ⟨t, hrt, huniq⟩
          have htT : t ∉ T := fun h => by
            have htS : t ∉ S := Finset.mem_compl.mp (hTsub h)
            exact hrT (hTclosed t h r hrS hrt.symm)
          refine ⟨t, hrt, fun w hrw hψw => ?_⟩
          have hwT : w ∉ T := fun h => by
            have hwS : w ∉ S := Finset.mem_compl.mp (hTsub h)
            exact hrT (hTclosed w h r hrS hrw.symm)
          exact huniq w hrw (by simp only [hwT, htT, ite_false]; exact hψw) }
  have hw_col_ne' : adm.φ w₁ ≠ adm.φ w₂ := by
    change (if h : w₁ ∈ T then φF ⟨w₁, h⟩ else adm0.φ w₁) ≠
      (if h : w₂ ∈ T then φF ⟨w₂, h⟩ else adm0.φ w₂)
    simp only [hw1T, hw2T, dite_true]; exact hw_col_ne
  -- `y` 与 `z` 在 `G - S` 中均不孤立（各自至多在 `S` 中有 2 个邻点 `u, v₃`，而度数 `≥ 3`）
  have hnoniso : ∀ s ∉ S, 3 ≤ G.degree s → ∃ r ∉ S, G.Adj s r := by
    intro s hsS hds3
    by_contra hiso; push Not at hiso
    have hsub : G.neighborFinset s ⊆ {u, v₃} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hiso r h hr
      rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have h1 := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
    have h2 := Finset.card_le_two (a := u) (b := v₃)
    omega
  -- 调用 `t3_fixed_color_extension`（`x₀` 无需避开 `adm.φs x₀`！）
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, (show G.degree u ≠ 2 by omega)]
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hY_L2 : ∀ r ∈ Y, (L r).card = 2 := by
    intro r hr; rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  let Z₃ : Finset ℕ := L v₃ \ {adm.φ z, adm.φs z}
  have hZ3 : 2 ≤ Z₃.card := by
    dsimp only [Z₃]; have := card_sdiff_ge (L v₃) {adm.φ z, adm.φs z}
    have := Finset.card_le_two (a := adm.φ z) (b := adm.φs z); omega
  let C_u : Finset ℕ := L u \ {adm.φ y, adm.φs y, adm.φ x₀}
  have hCu : Y.card + 1 ≤ C_u.card := by
    dsimp only [C_u, Y]; have := card_sdiff_ge (L u) {adm.φ y, adm.φs y, adm.φ x₀}
    have := card_triple_le (adm.φ y) (adm.φs y) (adm.φ x₀); omega
  rcases t3_fixed_color_extension (L := L) (Y := Y) (L₁ := L v₁) (L₂ := L v₂) (Z₃ := Z₃)
    (C_u := C_u) (φy := adm.φ y) (φz := adm.φ z) (δ := adm.φ x₀)
    hY1 hY_L2 hLv1 hLv2 hZ3 hCu with ⟨α, hαC, c₁, hc₁, aY, haY, γ, hγ⟩
  simp only [C_u, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
  rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁
  rcases hc₁ with ⟨⟨hc1L, hc1α⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
  simp only [Z₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2B
  -- 构造完整着色 `ψ` 并用 `adm.contradiction`（仅 `x₀` 处用 `pcf_at_deg_three_of_two_distinct`！）
  have huv1_ne : u ≠ v₁ := G.ne_of_adj huv₁
  have hv12_ne : v₁ ≠ v₂ := G.ne_of_adj hv12
  have hv23_ne : v₂ ≠ v₃ := G.ne_of_adj hv23
  let ψ : V → ℕ := fun r =>
    if r = u then α else if r = v₁ then c₁ else if r = v₂ then c₂ else if r = v₃ then c₃
    else if r ∈ Y then aY r else adm.φ r
  have hψu : ψ u = α := by simp [ψ]
  have hψv1 : ψ v₁ = c₁ := by simp [ψ, huv1_ne.symm]
  have hψv2 : ψ v₂ = c₂ := by simp [ψ, hv2u, hv12_ne.symm]
  have hψv3 : ψ v₃ = c₃ := by simp [ψ, hv3u, hv31, hv23_ne.symm]
  have hψY : ∀ r ∈ Y, ψ r = aY r := by
    intro r hr
    have hru : r ≠ u := fun h => G.ne_of_adj (mem_leafNbrs.mp hr).1 h.symm
    have hrv1 : r ≠ v₁ := fun h => hv1_not_Y (h ▸ hr)
    have hrv2 : r ≠ v₂ := fun h => hv2_not_Y (h ▸ hr)
    have hrv3 : r ≠ v₃ := fun h => hv3_not_Y (h ▸ hr)
    simp [ψ, hru, hrv1, hrv2, hrv3, hr]
  have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
    intro r hr; simp only [S, Finset.mem_insert, not_or] at hr
    simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
  -- 借助 `hm.not_colorable` 直接验证全图 `IsPCFColoring G ψ`！
  apply hm.not_colorable
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · -- 恰当性
    have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
      intro a' b' hab ha'
      simp only [S, Finset.mem_insert] at ha'
      rcases ha' with ha | ha | ha | ha | ha'Y
      · subst a'
        rcases hu_all b' hab with hb | hb | hb | hbY
        · rw [hb, hψu, hψv1]; exact Ne.symm hc1α
        · rw [hb, hψu, hψ_out x₀ hx₀_not_S]; exact hαC.2.2.2
        · rw [hb, hψu, hψ_out y hy_not_S]; exact hαC.2.1
        · rw [hψu, hψY b' hbY]; exact (haY b' hbY).2.symm
      · subst a'
        rcases hall_v1 b' hab with hb | hb
        · rw [hb, hψv1, hψu]; exact hc1α
        · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
      · subst a'
        rcases hall_v2 b' hab with hb | hb
        · rw [hb, hψv2, hψv1]; exact hc21
        · rw [hb, hψv2, hψv3]; exact hc2B.2.2.1
      · subst a'
        rcases hall_v3 b' hab with hb | hb
        · rw [hb, hψv3, hψv2]; exact Ne.symm hc2B.2.2.1
        · rw [hb, hψv3, hψ_out z hz_not_S]; exact hc3Z.2.1
      · have haL := mem_leafNbrs.mp ha'Y
        rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
        have hbu : b' = u := (huniq b' hab).trans (huniq u haL.1.symm).symm
        rw [hbu, hψY a' ha'Y, hψu]; exact (haY a' ha'Y).2
    intro r₁ r₂ h12
    by_cases h1 : r₁ ∈ S
    · exact hcase r₁ r₂ h12 h1
    · by_cases h2 : r₂ ∈ S
      · exact (hcase r₂ r₁ h12.symm h2).symm
      · rw [hψ_out r₁ h1, hψ_out r₂ h2]; exact adm.proper r₁ r₂ h1 h2 h12
  · -- 无冲突性（PCF）
    intro r _
    by_cases hrS : r ∈ S
    · simp only [S, Finset.mem_insert] at hrS
      rcases hrS with hr | hr | hr | hr | hrY
      · subst r
        exact pcf_from_leaf_and_three huv₁ huy hux₀ (fun h => by subst h; omega)
          hx₀_ne_v1.symm hyx₀ hv1_not_Y (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun t ht => (mem_leafNbrs.mp ht).1) hψY
          (fun t ht => by
            rcases hu_all t ht with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h)))
          (by rw [hψv1, hψ_out y hy_not_S, hψ_out x₀ hx₀_not_S]; exact hγ)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u.symm
          (by rw [hψu, hψv2]; exact Ne.symm hc2B.2.1)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
          (by rw [hψv1, hψv3]; exact Ne.symm hc31)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z hzv2.symm
          (by rw [hψv2, hψ_out z hz_not_S]; exact hc2B.2.2.2)
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
    · -- `r ∉ S`：若 `r = x₀` 直接用 `w₁, w₂` 异色；否则用 `adm.pcf_preserve`！
      by_cases hrx0 : r = x₀
      · subst r
        exact pcf_at_deg_three_of_two_distinct hdx₀ hx0w1 hx0w2 hw12
          (by rw [hψ_out w₁ hw1_not_S, hψ_out w₂ hw2_not_S]; exact hw_col_ne')
      · by_cases hhas : ∃ w ∉ S, G.Adj r w
        · apply adm.pcf_preserve ψ hψ_out r hrS hhas
          intro t htS hrt
          rcases hS_out r hrS t htS hrt with ⟨ht, hr | hr⟩ | ⟨ht, hr⟩
          · exact False.elim (hrx0 hr)
          · rw [ht, hr, hψu]; exact hαC.2.2.1
          · rw [ht, hr, hψv3]; exact hc3Z.2.2
        · push Not at hhas
          have hpos : 0 < (G.neighborFinset r).card := by
            rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree_ge_one hm r; omega
          rcases Finset.card_pos.mp hpos with ⟨t, ht⟩
          have hrt : G.Adj r t := (G.mem_neighborFinset r t).mp ht
          have htS : t ∈ S := by by_contra h; exact hhas t h hrt
          rcases hS_out r hrS t htS hrt with ⟨_, hr | hr⟩ | ⟨_, hr⟩
          · exact False.elim (hrx0 hr)
          · rcases hnoniso y hy_not_S hdy3 with ⟨w, hwS, hyw⟩
            exact False.elim (hhas w hwS (hr ▸ hyw))
          · rcases hnoniso z hz_not_S (by omega) with ⟨w, hwS, hzw⟩
            exact False.elim (hhas w hwS (hr ▸ hzw))
  · -- 列表合法性
    intro r
    by_cases hrS : r ∈ S
    · simp only [S, Finset.mem_insert] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | hrY
      · rw [hψu]; exact hαC.1
      · rw [hψv1]; exact hc1L
      · rw [hψv2]; exact hc2B.1
      · rw [hψv3]; exact hc3Z.1
      · rw [hψY r hrY]; exact (haY r hrY).1
    · rw [hψ_out r hrS]; exact adm.mem_list r hrS

end LeanResearch.Proposal3

