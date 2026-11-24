/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BeyondDefs

/-!
# 核心度为 `3` 且无好核心邻点与长线串的精细可约构型引理（`Core3Ext`）

本模块针对 `mad(G) < 5/2`（`2 * p ≤ 5 * q`）的极小反例，统一建立核心度 `3` 且无 `2⁺`-线串、
无好核心邻点顶点的可约性结果：
1. `no_leafy_coreDeg3_all_a_b_except_L4`：若 `coreDeg G u = 3`、`4 ≤ G.degree u`，且
   `twoThreadNbrs G u = ∅`、`threeThreadNbrs G u = ∅`、`goodNbrs G u = ∅`，则唯一不可单点约化的
   构型为 `G.degree u = 4 ∧ (oneThreadNbrs G u).card = 3 ∧ (badNbrs G u).card = 0`（即 `4_1_3` 点）；
2. `deg_three_no_good_at_most_one_bad`：若 `G.degree u = 3` 且 `goodNbrs G u = ∅`，则
   `(badNbrs G u).card ≤ 1`（彻底排除 `(a=1, b=2, g=0)` 与 `(a=0, b=3, g=0)`）。
-/

namespace LeanResearch.Proposal3

/-! ## 1. 列表计数、局部 `PCF` 验证与坏点三色自由度辅助引理 -/

private lemma count_singleton_eq (a c : ℕ) :
    ([a] : List ℕ).count c = if a = c then 1 else 0 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

private lemma count_pair_eq (a b c : ℕ) :
    ([a, b] : List ℕ).count c = (if a = c then 1 else 0) + (if b = c then 1 else 0) := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

/-- 若顶点 `v` 的全体邻点恰好由两个互异点 `x₁, x₂` 与不交有限集 `W` 构成，且颜色 `γ` 在其中恰出现一次，
则 `v` 满足 PCF 条件。 -/
private lemma pcf_of_pair_and_finset {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {v x₁ x₂ : V} {W : Finset V} {γ : ℕ}
    (hx1 : G.Adj v x₁) (hx2 : G.Adj v x₂)
    (hW_adj : ∀ p ∈ W, G.Adj v p)
    (hall : ∀ t, G.Adj v t → t = x₁ ∨ t = x₂ ∨ t ∈ W)
    (hcnt : (W.filter (fun p => ψ p = γ)).card + ([ψ x₁, ψ x₂] : List ℕ).count γ = 1) :
    ∃ y, G.Adj v y ∧ ∀ t, G.Adj v t → ψ t = ψ y → t = y := by
  classical
  rw [count_pair_eq] at hcnt
  by_cases h1 : ψ x₁ = γ
  · simp only [h1, ite_true] at hcnt
    have h2 : ψ x₂ ≠ γ := by
      intro h; simp only [h, ite_true] at hcnt; omega
    have hzero : (W.filter (fun p => ψ p = γ)).card = 0 := by
      simp only [h2, ite_false] at hcnt; omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    refine ⟨x₁, hx1, ?_⟩
    intro t hvt hψt
    rw [h1] at hψt
    rcases hall t hvt with rfl | rfl | htW
    · rfl
    · exact False.elim (h2 hψt)
    · exact False.elim (hzero htW hψt)
  · simp only [h1, ite_false] at hcnt
    by_cases h2 : ψ x₂ = γ
    · simp only [h2, ite_true] at hcnt
      have hzero : (W.filter (fun p => ψ p = γ)).card = 0 := by omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
      refine ⟨x₂, hx2, ?_⟩
      intro t hvt hψt
      rw [h2] at hψt
      rcases hall t hvt with rfl | rfl | htW
      · exact False.elim (h1 hψt)
      · rfl
      · exact False.elim (hzero htW hψt)
    · simp only [h2, ite_false] at hcnt
      have hone : (W.filter (fun p => ψ p = γ)).card = 1 := by omega
      rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
      have hw₀_mem : w₀ ∈ W.filter (fun p => ψ p = γ) := by rw [hw₀_eq]; simp
      rw [Finset.mem_filter] at hw₀_mem
      refine ⟨w₀, hW_adj w₀ hw₀_mem.1, ?_⟩
      intro t hvt hψt
      rw [hw₀_mem.2] at hψt
      rcases hall t hvt with rfl | rfl | htW
      · exact False.elim (h1 hψt)
      · exact False.elim (h2 hψt)
      · have hmem : t ∈ W.filter (fun p => ψ p = γ) := Finset.mem_filter.mpr ⟨htW, hψt⟩
        rw [hw₀_eq, Finset.mem_singleton] at hmem
        exact hmem

/-- 若顶点 `v` 的全体邻点恰好由单点 `x` 与有限集 `W` 构成，且颜色 `γ` 在其中恰出现一次，
则 `v` 满足 PCF 条件。 -/
private lemma pcf_of_single_and_finset {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {v x : V} {W : Finset V} {γ : ℕ}
    (hx : G.Adj v x) (hW_adj : ∀ p ∈ W, G.Adj v p)
    (hall : ∀ t, G.Adj v t → t = x ∨ t ∈ W)
    (hcnt : (W.filter (fun p => ψ p = γ)).card + ([ψ x] : List ℕ).count γ = 1) :
    ∃ y, G.Adj v y ∧ ∀ t, G.Adj v t → ψ t = ψ y → t = y := by
  classical
  rw [count_singleton_eq] at hcnt
  by_cases h1 : ψ x = γ
  · simp only [h1, ite_true] at hcnt
    have hzero : (W.filter (fun p => ψ p = γ)).card = 0 := by omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    refine ⟨x, hx, ?_⟩
    intro t hvt hψt
    rw [h1] at hψt
    rcases hall t hvt with rfl | htW
    · rfl
    · exact False.elim (hzero htW hψt)
  · simp only [h1, ite_false] at hcnt
    have hone : (W.filter (fun p => ψ p = γ)).card = 1 := by omega
    rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
    have hw₀_mem : w₀ ∈ W.filter (fun p => ψ p = γ) := by rw [hw₀_eq]; simp
    rw [Finset.mem_filter] at hw₀_mem
    refine ⟨w₀, hW_adj w₀ hw₀_mem.1, ?_⟩
    intro t hvt hψt
    rw [hw₀_mem.2] at hψt
    rcases hall t hvt with rfl | htW
    · exact False.elim (h1 hψt)
    · have hmem : t ∈ W.filter (fun p => ψ p = γ) := Finset.mem_filter.mpr ⟨htW, hψt⟩
      rw [hw₀_eq, Finset.mem_singleton] at hmem
      exact hmem

/-- 坏点三色自由度引理（供孤立外部 `3`-度点情形使用）：
当坏点 `b` 的可用集 `C` 满足 `|C| ≥ |Y| + 2` 且 `δ ∉ C` 时，存在大小为 `3` 的子集 `P ⊆ C`
及见证色 `lam`，使得对每个 `γ ∈ P` 都存在 `Y` 上的合法叶染色令 `lam` 在 `Y ∪ {h}` 中恰出现一次。 -/
private lemma bad_three_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {C : Finset ℕ} {δ : ℕ}
    (hY2 : 2 ≤ Y.card) (hL2 : ∀ p ∈ Y, (L p).card = 2)
    (hC : Y.card + 2 ≤ C.card) (hδC : δ ∉ C) :
    ∃ P : Finset ℕ, ∃ lam : ℕ, P ⊆ C ∧ P.card = 3 ∧
      ∀ γ ∈ P, ∃ a : V → ℕ, (∀ p ∈ Y, a p ∈ L p ∧ a p ≠ γ) ∧
        (Y.filter (fun p => a p = lam)).card + (if δ = lam then 1 else 0) = 1 := by
  classical
  let I := Y.filter (fun p => δ ∈ L p)
  have hη_ex : ∀ p : V, p ∈ I → ∃ η ∈ L p, η ≠ δ := by
    intro p hp
    have hpY : p ∈ Y := (Finset.mem_filter.mp hp).1
    rcases exists_mem_sdiff_of_lt (A := L p) (B := {δ}) (by simp [hL2 p hpY]) with ⟨η, hη, hηδ⟩
    rw [Finset.mem_singleton] at hηδ
    exact ⟨η, hη, hηδ⟩
  let η : V → ℕ := fun p => if hp : p ∈ I then (hη_ex p hp).choose else 0
  have hη_spec : ∀ p (hp : p ∈ I), η p ∈ L p ∧ η p ≠ δ := by
    intro p hp; simp only [η, hp, dite_true]; exact (hη_ex p hp).choose_spec
  let T : Finset ℕ := I.image η
  have hT_le : T.card ≤ Y.card :=
    le_trans Finset.card_image_le (Finset.card_le_card (Finset.filter_subset _ Y))
  by_cases hT_lt : T.card < Y.card
  · -- 情形 1：`|T| ≤ |Y| - 1`，故 `|C \ T| ≥ 3`，任取 3-元子集 `P ⊆ C \ T` 并令 `lam = δ`！
    have hCT : 3 ≤ (C \ T).card := by
      have := card_sdiff_ge C T; omega
    rcases Finset.exists_subset_card_eq hCT with ⟨P, hP_sub, hP_card⟩
    refine ⟨P, δ, hP_sub.trans Finset.sdiff_subset, hP_card, ?_⟩
    intro γ hγP
    have hγCT := Finset.mem_sdiff.mp (hP_sub hγP)
    have hpick : ∀ p, p ∈ Y → p ∉ I → ∃ c ∈ L p, c ≠ γ := by
      intro p hpY _
      rcases exists_mem_sdiff_of_lt (A := L p) (B := {γ}) (by simp [hL2 p hpY]) with ⟨c, hc, hcn⟩
      rw [Finset.mem_singleton] at hcn; exact ⟨c, hc, hcn⟩
    let a : V → ℕ := fun p =>
      if hp : p ∈ I then η p
      else if hpY : p ∈ Y then (hpick p hpY hp).choose else 0
    refine ⟨a, ?_, ?_⟩
    · intro p hpY
      by_cases hpI : p ∈ I
      · simp only [a, hpI, dite_true]
        exact ⟨(hη_spec p hpI).1, fun h => hγCT.2 (h ▸ Finset.mem_image_of_mem η hpI)⟩
      · simp only [a, hpI, dite_false, hpY, dite_true]
        exact (hpick p hpY hpI).choose_spec
    · have hzero : (Y.filter (fun p => a p = δ)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p hpY heq
        by_cases hpI : p ∈ I
        · simp only [a, hpI, dite_true] at heq; exact (hη_spec p hpI).2 heq
        · simp only [a, hpI, dite_false, hpY, dite_true] at heq
          have hcL : (hpick p hpY hpI).choose ∈ L p := (hpick p hpY hpI).choose_spec.1
          exact hpI (Finset.mem_filter.mpr ⟨hpY, heq ▸ hcL⟩)
      rw [hzero]; simp
  · -- 情形 2：`|T| = |Y|`，故 `I = Y`，取 `p₀ ∈ Y` 与 `lam = η p₀`，`|C \ {lam}| ≥ 3`！
    have hT_eq : T.card = Y.card := by omega
    have hI_eq : I = Y := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ Y)
      (by have := Finset.card_image_le (f := η) (s := I); dsimp only [T] at hT_eq; omega)
    rcases Finset.card_pos.mp (by omega : 0 < Y.card) with ⟨p₀, hp₀Y⟩
    have hp₀I : p₀ ∈ I := hI_eq ▸ hp₀Y
    let lam := η p₀
    have hlamδ : lam ≠ δ := (hη_spec p₀ hp₀I).2
    have hClam : 3 ≤ (C \ {lam}).card := by
      have := card_sdiff_ge C {lam}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.exists_subset_card_eq hClam with ⟨P, hP_sub, hP_card⟩
    let a : V → ℕ := fun p => if p = p₀ then lam else δ
    refine ⟨P, lam, hP_sub.trans Finset.sdiff_subset, hP_card, ?_⟩
    intro γ hγP
    have hγm := Finset.mem_sdiff.mp (hP_sub hγP)
    rw [Finset.mem_singleton] at hγm
    refine ⟨a, ?_, ?_⟩
    · intro p hpY
      by_cases hp0 : p = p₀
      · subst p; simp only [a, ite_true]
        exact ⟨(hη_spec p₀ hp₀I).1, Ne.symm hγm.2⟩
      · simp only [a, hp0, ite_false]
        have hpI : p ∈ I := hI_eq ▸ hpY
        exact ⟨(Finset.mem_filter.mp hpI).2, fun h => hδC (h ▸ hγm.1)⟩
    · have hEq : Y.filter (fun p => a p = lam) = {p₀} := by
        ext p; simp only [Finset.mem_filter, Finset.mem_singleton, a]
        constructor
        · rintro ⟨_, h⟩
          split_ifs at h with hp0
          · exact hp0
          · exact False.elim (hlamδ h.symm)
        · rintro rfl; exact ⟨hp₀Y, by simp⟩
      rw [hEq, Finset.card_singleton]; simp [hlamδ.symm]

/-- 将 `J` 上关于 `f` 的子类型过滤计数转化为 `Finset.filter` 计数。 -/
private lemma card_subtype_filter_eq {V : Type*}
    (J : Finset V) (P : V → Prop) [DecidablePred P]
    [DecidablePred (fun i : {r : V // r ∈ J} => P i.val)] :
    (Finset.univ.filter (fun i : {r : V // r ∈ J} => P i.val)).card =
      (J.filter P).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.property, hi⟩
  · intro i₁ _ i₂ _ h; exact Subtype.ext h
  · intro r hr; simp only [Finset.mem_filter] at hr
    exact ⟨⟨r, hr.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2⟩, rfl⟩

/-! ## 2. 统一核心度 `3` 局部构型记录（`Core3Setup`）与延拓矛盾引擎 -/

/-- 核心度 `3` 且无 `2⁺`-线串、无好核心邻点顶点 `u` 的统一局部结构数据包。 -/
private structure Core3Setup {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) (u : V) where
  Y : Finset V
  T1 : Finset V
  B : Finset V
  R : Finset V
  S : Finset V
  ext : V → V
  hY_def : Y = leafNbrs G u
  hT1_def : T1 = oneThreadNbrs G u
  hB_def : B = badNbrs G u
  hR_def : R = coreNbrs G u
  hS_def : S = insert u (G.neighborFinset u ∪ B.biUnion (leafNbrs G))
  hdu3 : 3 ≤ G.degree u
  hR_eq : R = T1 ∪ B
  hT1B_disj : Disjoint T1 B
  hR_card : R.card = 3
  hY_card : Y.card + 3 = G.degree u
  hN_eq : G.neighborFinset u = Y ∪ R
  hYR_disj : Disjoint Y R
  huS : u ∈ S
  hu_not_N : u ∉ G.neighborFinset u
  hN_disj_BL : Disjoint (G.neighborFinset u) (B.biUnion (leafNbrs G))
  hu_not_BL : u ∉ B.biUnion (leafNbrs G)
  hext_spec : ∀ r ∈ R, G.Adj r (ext r) ∧ ext r ≠ u ∧ 3 ≤ G.degree (ext r) ∧ ext r ∉ S
  hT1_deg : ∀ w ∈ T1, G.degree w = 2
  hT1_all : ∀ w ∈ T1, ∀ t, G.Adj w t → t = u ∨ t = ext w
  hB_bad : ∀ b ∈ B, IsBad G b
  hB_all : ∀ b ∈ B, ∀ t, G.Adj b t → t = u ∨ t = ext b ∨ t ∈ leafNbrs G b
  hB_leaf_card : ∀ b ∈ B, 2 ≤ (leafNbrs G b).card ∧ (leafNbrs G b).card + 2 = G.degree b
  hB_leaf_disj : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → Disjoint (leafNbrs G b₁) (leafNbrs G b₂)
  hS_out : ∀ v, v ∉ S → ∀ x ∈ S, G.Adj v x → x ∈ R ∧ v = ext x

/-- 从 `coreDeg G u = 3`、`twoThreadNbrs = ∅`、`threeThreadNbrs = ∅`、`goodNbrs = ∅`
构建统一数据包 `Core3Setup`。 -/
private noncomputable def mkCore3Setup {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (hc3 : coreDeg G u = 3)
    (hno2 : twoThreadNbrs G u = ∅) (hno3 : threeThreadNbrs G u = ∅)
    (hgood0 : goodNbrs G u = ∅) : Core3Setup hm hpq u := by
  classical
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hR_eq : coreNbrs G u = oneThreadNbrs G u ∪ badNbrs G u := by
    rw [coreNbrs_eq_degTwo_union_degThreePlus, degTwoNbrs_eq_one_union_long hm u,
        longThreadNbrs_eq_two_union_three hm u, hno2, hno3, Finset.empty_union, Finset.union_empty,
        degThreePlusNbrs_eq_bad_union_good hm hpq u, hgood0, Finset.union_empty]
  have hT1B_disj : Disjoint (oneThreadNbrs G u) (badNbrs G u) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    rw [mem_oneThreadNbrs] at h1; rw [mem_badNbrs] at h2
    have := h1.2.1; have := h2.2.1; omega
  have hN_eq : G.neighborFinset u = leafNbrs G u ∪ coreNbrs G u := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, mem_leafNbrs, mem_coreNbrs]
    constructor
    · intro huv
      have hdv1 := degree_ge_one hm v
      by_cases h1 : G.degree v = 1
      · exact Or.inl ⟨huv, h1⟩
      · exact Or.inr ⟨huv, by omega⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hYR_disj : Disjoint (leafNbrs G u) (coreNbrs G u) :=
    (coreNbrs_disjoint_leafNbrs G u).symm
  have hY_card : (leafNbrs G u).card + 3 = G.degree u := by
    have := coreDeg_add_leafNbrs hm u; omega
  let S : Finset V := insert u (G.neighborFinset u ∪ (badNbrs G u).biUnion (leafNbrs G))
  have hB_bad : ∀ b ∈ badNbrs G u, IsBad G b := fun b hb => (mem_badNbrs.mp hb).2
  have hT1_deg : ∀ w ∈ oneThreadNbrs G u, G.degree w = 2 := fun w hw =>
    (mem_oneThreadNbrs.mp hw).2.1
  -- 为每个 `r ∈ coreNbrs G u` 提取唯一的外部核心邻点 `ext r`
  have hext_ex : ∀ r, r ∈ coreNbrs G u →
      ∃ z : V, G.Adj r z ∧ z ≠ u ∧ 3 ≤ G.degree z ∧
        (r ∈ oneThreadNbrs G u → ∀ t, G.Adj r t → t = u ∨ t = z) ∧
        (r ∈ badNbrs G u → ∀ t, G.Adj r t → t = u ∨ t = z ∨ t ∈ leafNbrs G r) := by
    intro r hr
    rw [hR_eq, Finset.mem_union] at hr
    rcases hr with hr1 | hrB
    · have h1 := oneThreadNbr_other_endpoint hm hdu3 hr1
      rcases h1 with ⟨z, hrz, hzu, hdz, _, _⟩
      have hur : G.Adj u r := (mem_oneThreadNbrs.mp hr1).1
      have hdr : G.degree r = 2 := (mem_oneThreadNbrs.mp hr1).2.1
      have hNr := neighborFinset_eq_pair_of_deg_two hdr hur.symm hrz hzu.symm
      refine ⟨z, hrz, hzu, hdz, ?_, fun hB => False.elim (Finset.disjoint_left.mp hT1B_disj hr1 hB)⟩
      intro _ t hrt
      have : t ∈ ({u, z} : Finset V) := by rw [← hNr]; exact (G.mem_neighborFinset r t).mpr hrt
      simpa using this
    · have hbm := mem_badNbrs.mp hrB
      have hub : G.Adj u r := hbm.1
      have hbad : IsBad G r := hbm.2
      have hu_core : u ∈ coreNbrs G r := mem_coreNbrs.mpr ⟨hub.symm, by omega⟩
      have hcard1 : (coreNbrs G r \ {u}).card = 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu_core),
            Finset.card_singleton]
        have := hbad.2; unfold coreDeg at this; omega
      rcases Finset.card_eq_one.mp hcard1 with ⟨z, hz_eq⟩
      have hz_mem : z ∈ coreNbrs G r \ {u} := by rw [hz_eq]; simp
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hz_mem
      have hrz : G.Adj r z := (mem_coreNbrs.mp hz_mem.1).1
      have hzu : z ≠ u := hz_mem.2
      have hdz : 3 ≤ G.degree z := bad_coreNbrs_deg_ge_three hm hpq hbad hz_mem.1
      have hcore_r : coreNbrs G r = {u, z} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact hu_core
          · exact hz_mem.1
        · rw [Finset.card_pair hzu.symm]; have := hbad.2; unfold coreDeg at this; omega
      refine ⟨z, hrz, hzu, hdz, fun h1 => False.elim (Finset.disjoint_left.mp hT1B_disj h1 hrB), ?_⟩
      intro _ t hrt
      have hdt1 := degree_ge_one hm t
      by_cases h1 : G.degree t = 1
      · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hrt, h1⟩))
      · have htc : t ∈ coreNbrs G r := mem_coreNbrs.mpr ⟨hrt, by omega⟩
        rw [hcore_r, Finset.mem_insert, Finset.mem_singleton] at htc
        rcases htc with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  let ext : V → V := fun r => if hr : r ∈ coreNbrs G u then (hext_ex r hr).choose else u
  have hext_raw : ∀ r (hr : r ∈ coreNbrs G u),
      G.Adj r (ext r) ∧ ext r ≠ u ∧ 3 ≤ G.degree (ext r) ∧
      (r ∈ oneThreadNbrs G u → ∀ t, G.Adj r t → t = u ∨ t = ext r) ∧
      (r ∈ badNbrs G u → ∀ t, G.Adj r t → t = u ∨ t = ext r ∨ t ∈ leafNbrs G r) := by
    intro r hr
    have hext_eq : ext r = (hext_ex r hr).choose := by simp only [ext, hr, dite_true]
    rw [hext_eq]
    exact (hext_ex r hr).choose_spec
  have hB_leaf_disj : ∀ b₁ ∈ badNbrs G u, ∀ b₂ ∈ badNbrs G u, b₁ ≠ b₂ →
      Disjoint (leafNbrs G b₁) (leafNbrs G b₂) := by
    intro b₁ _ b₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := mem_leafNbrs.mp hp1; have h2 := mem_leafNbrs.mp hp2
    rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨w, _, huniq⟩
    exact hne ((huniq b₁ h1.1.symm).trans (huniq b₂ h2.1.symm).symm)
  have hN_disj_BL : Disjoint (G.neighborFinset u) ((badNbrs G u).biUnion (leafNbrs G)) := by
    rw [Finset.disjoint_left]
    intro x hxN hxBL
    rcases Finset.mem_biUnion.mp hxBL with ⟨b, hbB, hxb⟩
    have h1 := mem_leafNbrs.mp hxb
    rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨w, _, huniq⟩
    have hub : u = b := (huniq u ((G.mem_neighborFinset u x).mp hxN).symm).trans
      (huniq b h1.1.symm).symm
    exact G.ne_of_adj (mem_badNbrs.mp hbB).1 hub
  have hu_not_BL : u ∉ (badNbrs G u).biUnion (leafNbrs G) := by
    intro huBL
    rcases Finset.mem_biUnion.mp huBL with ⟨b, _, hub⟩
    have := (mem_leafNbrs.mp hub).2; omega
  have hext_not_S : ∀ r ∈ coreNbrs G u, ext r ∉ S := by
    intro r hr hmem
    rcases hext_raw r hr with ⟨hrz, hzu, hdz, _, _⟩
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hmem
    rcases hmem with h1 | h2 | ⟨b, _, hbL⟩
    · exact hzu h1
    · rw [hN_eq, hR_eq, Finset.mem_union, Finset.mem_union] at h2
      rcases h2 with hY | hT | hB
      · have := (mem_leafNbrs.mp hY).2; omega
      · have := (mem_oneThreadNbrs.mp hT).2.1; omega
      · have hbad_z : IsBad G (ext r) := (mem_badNbrs.mp hB).2
        rw [hR_eq, Finset.mem_union] at hr
        rcases hr with hr1 | hrB
        · have hur : G.Adj u r := (mem_oneThreadNbrs.mp hr1).1
          have hdr : G.degree r = 2 := (mem_oneThreadNbrs.mp hr1).2.1
          have hr_in : r ∈ oneThreadNbrs G (ext r) :=
            mem_oneThreadNbrs.mpr ⟨hrz.symm, hdr, u, hur.symm, hzu.symm, hdu3⟩
          rw [bad_no_one_thread hm hbad_z] at hr_in
          exact Finset.notMem_empty r hr_in
        · exact no_adjacent_bad hm hpq (hB_bad r hrB) hbad_z hrz
    · have := (mem_leafNbrs.mp hbL).2; omega
  have hS_out : ∀ v, v ∉ S → ∀ x ∈ S, G.Adj v x → x ∈ coreNbrs G u ∧ v = ext x := by
    intro v hvS x hxS hvx
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hxS
    rcases hxS with rfl | hxN | ⟨b, hbB, hxb⟩
    · exact False.elim (hvS (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ ((G.mem_neighborFinset x v).mpr hvx.symm))))
    · rw [hN_eq, Finset.mem_union] at hxN
      rcases hxN with hxY | hxR
      · have hL := mem_leafNbrs.mp hxY
        rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
        have hvu : v = u := (huniq v hvx.symm).trans (huniq u hL.1.symm).symm
        exact False.elim (hvS (hvu ▸ Finset.mem_insert_self u _))
      · refine ⟨hxR, ?_⟩
        have hxR' := hxR
        rw [hR_eq, Finset.mem_union] at hxR'
        rcases hxR' with hx1 | hxB
        · rcases (hext_raw x hxR).2.2.2.1 hx1 v hvx.symm with rfl | rfl
          · exact False.elim (hvS (Finset.mem_insert_self v _))
          · rfl
        · rcases (hext_raw x hxR).2.2.2.2 hxB v hvx.symm with rfl | rfl | hvL
          · exact False.elim (hvS (Finset.mem_insert_self v _))
          · rfl
          · exact False.elim (hvS (Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨x, hxB, hvL⟩))))
    · have hL := mem_leafNbrs.mp hxb
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
      have hvb : v = b := (huniq v hvx.symm).trans (huniq b hL.1.symm).symm
      have hbN : b ∈ G.neighborFinset u := (G.mem_neighborFinset u b).mpr (mem_badNbrs.mp hbB).1
      exact False.elim (hvS (hvb ▸ Finset.mem_insert_of_mem (Finset.mem_union_left _ hbN)))
  refine
    { Y := leafNbrs G u
      T1 := oneThreadNbrs G u
      B := badNbrs G u
      R := coreNbrs G u
      S := S
      ext := ext
      hY_def := rfl
      hT1_def := rfl
      hB_def := rfl
      hR_def := rfl
      hS_def := rfl
      hdu3 := hdu3
      hR_eq := hR_eq
      hT1B_disj := hT1B_disj
      hR_card := hc3
      hY_card := hY_card
      hN_eq := hN_eq
      hYR_disj := hYR_disj
      huS := Finset.mem_insert_self u _
      hu_not_N := fun h => G.ne_of_adj ((G.mem_neighborFinset u u).mp h) rfl
      hN_disj_BL := hN_disj_BL
      hu_not_BL := hu_not_BL
      hext_spec := fun r hr =>
        ⟨(hext_raw r hr).1, (hext_raw r hr).2.1, (hext_raw r hr).2.2.1, hext_not_S r hr⟩
      hT1_deg := hT1_deg
      hT1_all := fun w hw =>
        (hext_raw w (by rw [hR_eq]; exact Finset.mem_union_left _ hw)).2.2.2.1 hw
      hB_bad := hB_bad
      hB_all := fun b hb =>
        (hext_raw b (by rw [hR_eq]; exact Finset.mem_union_right _ hb)).2.2.2.2 hb
      hB_leaf_card := fun b hb => by
        have hbad := hB_bad b hb
        have h1 := coreDeg_add_leafNbrs hm b
        have h2 := hbad.1; have h3 := hbad.2; omega
      hB_leaf_disj := hB_leaf_disj
      hS_out := hS_out }

/-- 外部非孤立情形的统一矛盾延拓引擎：给出 `u`、`N_G(u)` 及各坏邻点叶子的合法配色与局部 PCF 见证，
一步触发 `adm.contradiction`。 -/
private lemma Core3Setup.contradiction_noniso {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    {hm : MinimalCounterexample p q G L} {hpq : 2 * p ≤ 5 * q} {u : V}
    (cfg : Core3Setup hm hpq u)
    (hnoniso : ∀ r ∈ cfg.R, ∃ w, w ∉ cfg.S ∧ G.Adj (cfg.ext r) w)
    (adm : AdmissibleColoring G L cfg.S)
    (α : ℕ) (hα : α ∈ L u) (f : V → ℕ)
    (hf_mem : ∀ r ∈ G.neighborFinset u, f r ∈ L r ∧ f r ≠ α)
    (hf_R : ∀ r ∈ cfg.R, f r ≠ adm.φ (cfg.ext r) ∧ f r ≠ adm.φs (cfg.ext r))
    (hT1_pcf : ∀ w ∈ cfg.T1, α ≠ adm.φ (cfg.ext w))
    (hB_ext : ∀ b ∈ cfg.B, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G b, a p ∈ L p ∧ a p ≠ f b) ∧
      ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => a p = γ)).card +
        ([α, adm.φ (cfg.ext b)] : List ℕ).count γ = 1)
    (hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y) :
    False := by
  classical
  let aB : V → V → ℕ := fun b => if hb : b ∈ cfg.B then (hB_ext b hb).choose else fun _ => 0
  have haB_spec : ∀ b (hb : b ∈ cfg.B),
      (∀ p ∈ leafNbrs G b, aB b p ∈ L p ∧ aB b p ≠ f b) ∧
      ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => aB b p = γ)).card +
        ([α, adm.φ (cfg.ext b)] : List ℕ).count γ = 1 := by
    intro b hb; simp only [aB, hb, dite_true]; exact (hB_ext b hb).choose_spec
  let BL : Finset V := cfg.B.biUnion (leafNbrs G)
  have howner : ∀ x, x ∈ BL → ∃ b ∈ cfg.B, x ∈ leafNbrs G b := fun x hx => Finset.mem_biUnion.mp hx
  let ψ : V → ℕ := fun x =>
    if x = u then α
    else if x ∈ G.neighborFinset u then f x
    else if hxL : x ∈ BL then aB (howner x hxL).choose x
    else adm.φ x
  have hψu : ψ u = α := by simp [ψ]
  have hψN : ∀ r ∈ G.neighborFinset u, ψ r = f r := by
    intro r hr
    have hru : r ≠ u := fun h => cfg.hu_not_N (h ▸ hr)
    simp only [ψ, hru, hr, ite_false, ite_true]
  have hψL : ∀ b ∈ cfg.B, ∀ p ∈ leafNbrs G b, ψ p = aB b p := by
    intro b hb p hp
    have hpBL : p ∈ BL := Finset.mem_biUnion.mpr ⟨b, hb, hp⟩
    have hpu : p ≠ u := fun h => cfg.hu_not_BL (h ▸ hpBL)
    have hpN : p ∉ G.neighborFinset u := fun h => Finset.disjoint_left.mp cfg.hN_disj_BL h hpBL
    have hch : (howner p hpBL).choose = b := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (cfg.hB_leaf_disj _ (howner p hpBL).choose_spec.1 b hb hne)
        (howner p hpBL).choose_spec.2 hp
    simp only [ψ, hpu, hpN, hpBL, ite_false, dite_true, hch]
  have hψ_out : ∀ x, x ∉ cfg.S → ψ x = adm.φ x := by
    intro x hx
    rw [cfg.hS_def] at hx
    simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx
    have hxBL : x ∉ BL := hx.2.2
    simp only [ψ, hx.1, hx.2.1, hxBL, ite_false, dite_false]
  have hR_subN : cfg.R ⊆ G.neighborFinset u := by rw [cfg.hN_eq]; exact Finset.subset_union_right
  have hT1_subR : cfg.T1 ⊆ cfg.R := by rw [cfg.hR_eq]; exact Finset.subset_union_left
  have hB_subR : cfg.B ⊆ cfg.R := by rw [cfg.hR_eq]; exact Finset.subset_union_right
  apply adm.contradiction hm ψ hψ_out
  · intro x hx
    rw [cfg.hS_def] at hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with rfl | hxN | ⟨b, hbB, hxb⟩
    · rw [hψu]; exact hα
    · rw [hψN x hxN]; exact (hf_mem x hxN).1
    · rw [hψL b hbB x hxb]; exact ((haB_spec b hbB).1 x hxb).1
  · intro x₁ x₂ h12 hor
    have hcase : ∀ x y, G.Adj x y → x ∈ cfg.S → ψ x ≠ ψ y := by
      intro x y hxy hx
      rw [cfg.hS_def] at hx
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hx
      rcases hx with rfl | hxN | ⟨b, hbB, hxb⟩
      · have hyN : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy
        rw [hψu, hψN y hyN]; exact (hf_mem y hyN).2.symm
      · have hxN' := hxN
        rw [cfg.hN_eq, cfg.hR_eq, Finset.mem_union, Finset.mem_union] at hxN'
        rcases hxN' with hxY | hxT1 | hxB
        · rw [cfg.hY_def] at hxY
          have hL := mem_leafNbrs.mp hxY
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
          have hyu : y = u := (huniq y hxy).trans (huniq u hL.1.symm).symm
          rw [hyu, hψN x hxN, hψu]; exact (hf_mem x hxN).2
        · rcases cfg.hT1_all x hxT1 y hxy with rfl | rfl
          · rw [hψN x hxN, hψu]; exact (hf_mem x hxN).2
          · have hxR := hT1_subR hxT1
            rw [hψN x hxN, hψ_out (cfg.ext x) (cfg.hext_spec x hxR).2.2.2]
            exact (hf_R x hxR).1
        · rcases cfg.hB_all x hxB y hxy with rfl | rfl | hyL
          · rw [hψN x hxN, hψu]; exact (hf_mem x hxN).2
          · have hxR := hB_subR hxB
            rw [hψN x hxN, hψ_out (cfg.ext x) (cfg.hext_spec x hxR).2.2.2]
            exact (hf_R x hxR).1
          · rw [hψN x hxN, hψL x hxB y hyL]; exact ((haB_spec x hxB).1 y hyL).2.symm
      · have hL := mem_leafNbrs.mp hxb
        rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
        have hyb : y = b := (huniq y hxy).trans (huniq b hL.1.symm).symm
        rw [hyb, hψL b hbB x hxb, hψN b (hR_subN (hB_subR hbB))]
        exact ((haB_spec b hbB).1 x hxb).2
    rcases hor with h1 | h2
    · exact hcase x₁ x₂ h12 h1
    · exact (hcase x₂ x₁ h12.symm h2).symm
  · intro v hvS _ x hxS hvx
    rcases cfg.hS_out v hvS x hxS hvx with ⟨hxR, rfl⟩
    rw [hψN x (hR_subN hxR)]
    exact (hf_R x hxR).2
  · intro v hvS hiso ⟨x, hvx⟩
    have hxS : x ∈ cfg.S := by by_contra h; exact hiso x h hvx
    rcases cfg.hS_out v hvS x hxS hvx with ⟨hxR, rfl⟩
    rcases hnoniso x hxR with ⟨w, hwS, hxw⟩
    exact False.elim (hiso w hwS hxw)
  · intro x hxS _
    rw [cfg.hS_def] at hxS
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hxS
    rcases hxS with rfl | hxN | ⟨b, _, hxb⟩
    · rcases hu_pcf with ⟨y, hyN, hy_uniq⟩
      refine ⟨y, (G.mem_neighborFinset x y).mp hyN, ?_⟩
      intro t hxt hψt
      have htN : t ∈ G.neighborFinset x := (G.mem_neighborFinset x t).mpr hxt
      rw [hψN t htN, hψN y hyN] at hψt
      exact hy_uniq t htN hψt
    · rw [cfg.hN_eq, cfg.hR_eq, Finset.mem_union, Finset.mem_union] at hxN
      rcases hxN with hxY | hxT1 | hxB
      · rw [cfg.hY_def] at hxY
        exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm
      · have hxR := hT1_subR hxT1
        have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (hR_subN hxR)
        exact pcf_at_of_two_distinct_neighbors (cfg.hT1_deg x hxT1) hux.symm
          (cfg.hext_spec x hxR).1 (cfg.hext_spec x hxR).2.1.symm
          (by rw [hψu, hψ_out (cfg.ext x) (cfg.hext_spec x hxR).2.2.2]; exact hT1_pcf x hxT1)
      · have hxR := hB_subR hxB
        have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (hR_subN hxR)
        rcases (haB_spec x hxB).2 with ⟨γ, hγ⟩
        have hfilt : (leafNbrs G x).filter (fun p => ψ p = γ) =
            (leafNbrs G x).filter (fun p => aB x p = γ) := by
          ext p; simp only [Finset.mem_filter]
          exact ⟨fun ⟨hp, h⟩ => ⟨hp, by rwa [hψL x hxB p hp] at h⟩,
            fun ⟨hp, h⟩ => ⟨hp, by rw [hψL x hxB p hp]; exact h⟩⟩
        exact pcf_of_pair_and_finset (ψ := ψ) (v := x) (x₁ := u) (x₂ := cfg.ext x)
          (W := leafNbrs G x) (γ := γ) hux.symm (cfg.hext_spec x hxR).1
          (fun p hp => (mem_leafNbrs.mp hp).1) (cfg.hB_all x hxB)
          (by rw [hfilt, hψu, hψ_out (cfg.ext x) (cfg.hext_spec x hxR).2.2.2]; exact hγ)
    · exact pcf_at_deg_one (mem_leafNbrs.mp hxb).2 (mem_leafNbrs.mp hxb).1.symm

/-- 孤立外部 `3`-度点情形的统一矛盾延拓引擎：当 `insert z cfg.S = Finset.univ` 时，
给出全图合法配色与局部 PCF 见证，一步触发 `hm.not_colorable`。 -/
private lemma Core3Setup.contradiction_isolated {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    {hm : MinimalCounterexample p q G L} {hpq : 2 * p ≤ 5 * q} {u : V}
    (cfg : Core3Setup hm hpq u)
    (z : V) (hzS : z ∉ cfg.S) (hdz : G.degree z = 3)
    (hNz : G.neighborFinset z = cfg.R)
    (hextz : ∀ r ∈ cfg.R, cfg.ext r = z)
    (hall : insert z cfg.S = Finset.univ)
    (δ : ℕ) (hδ : δ ∈ L z) (α : ℕ) (hα : α ∈ L u) (f : V → ℕ)
    (hf_mem : ∀ r ∈ G.neighborFinset u, f r ∈ L r ∧ f r ≠ α)
    (hf_R : ∀ r ∈ cfg.R, f r ≠ δ)
    (hT1_pcf : ∀ w ∈ cfg.T1, α ≠ δ)
    (hB_ext : ∀ b ∈ cfg.B, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G b, a p ∈ L p ∧ a p ≠ f b) ∧
      ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => a p = γ)).card +
        ([α, δ] : List ℕ).count γ = 1)
    (hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y)
    (hz_pcf : ∃ r₁ ∈ cfg.R, ∃ r₂ ∈ cfg.R, f r₁ ≠ f r₂) : False := by
  classical
  let aB : V → V → ℕ := fun b => if hb : b ∈ cfg.B then (hB_ext b hb).choose else fun _ => 0
  have haB_spec : ∀ b (hb : b ∈ cfg.B),
      (∀ p ∈ leafNbrs G b, aB b p ∈ L p ∧ aB b p ≠ f b) ∧
      ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => aB b p = γ)).card +
        ([α, δ] : List ℕ).count γ = 1 := by
    intro b hb; simp only [aB, hb, dite_true]; exact (hB_ext b hb).choose_spec
  let BL : Finset V := cfg.B.biUnion (leafNbrs G)
  have howner : ∀ x, x ∈ BL → ∃ b ∈ cfg.B, x ∈ leafNbrs G b := fun x hx => Finset.mem_biUnion.mp hx
  let ψ : V → ℕ := fun x =>
    if x = z then δ
    else if x = u then α
    else if x ∈ G.neighborFinset u then f x
    else if hxL : x ∈ BL then aB (howner x hxL).choose x
    else 0
  have hzu : z ≠ u := fun h => hzS (h ▸ cfg.huS)
  have hzN : z ∉ G.neighborFinset u := fun h =>
    hzS (by rw [cfg.hS_def]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
  have hzBL : z ∉ BL := fun h =>
    hzS (by rw [cfg.hS_def]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hψz : ψ z = δ := by simp [ψ]
  have hψu : ψ u = α := by simp [ψ, hzu.symm]
  have hψN : ∀ r ∈ G.neighborFinset u, ψ r = f r := by
    intro r hr
    have hrz : r ≠ z := fun h => hzN (h ▸ hr)
    have hru : r ≠ u := fun h => cfg.hu_not_N (h ▸ hr)
    simp only [ψ, hrz, hru, hr, ite_false, ite_true]
  have hψL : ∀ b ∈ cfg.B, ∀ p ∈ leafNbrs G b, ψ p = aB b p := by
    intro b hb p hp
    have hpBL : p ∈ BL := Finset.mem_biUnion.mpr ⟨b, hb, hp⟩
    have hpz : p ≠ z := fun h => hzBL (h ▸ hpBL)
    have hpu : p ≠ u := fun h => cfg.hu_not_BL (h ▸ hpBL)
    have hpN : p ∉ G.neighborFinset u := fun h => Finset.disjoint_left.mp cfg.hN_disj_BL h hpBL
    have hch : (howner p hpBL).choose = b := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (cfg.hB_leaf_disj _ (howner p hpBL).choose_spec.1 b hb hne)
        (howner p hpBL).choose_spec.2 hp
    simp only [ψ, hpz, hpu, hpN, hpBL, ite_false, dite_true, hch]
  have hR_subN : cfg.R ⊆ G.neighborFinset u := by rw [cfg.hN_eq]; exact Finset.subset_union_right
  have hT1_subR : cfg.T1 ⊆ cfg.R := by rw [cfg.hR_eq]; exact Finset.subset_union_left
  have hB_subR : cfg.B ⊆ cfg.R := by rw [cfg.hR_eq]; exact Finset.subset_union_right
  have hall_cases : ∀ x : V,
      x = z ∨ x = u ∨ x ∈ G.neighborFinset u ∨ ∃ b ∈ cfg.B, x ∈ leafNbrs G b := by
    intro x
    have hx : x ∈ insert z cfg.S := by rw [hall]; exact Finset.mem_univ x
    rw [cfg.hS_def] at hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hx
    tauto
  apply hm.not_colorable
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    rcases hall_cases x with rfl | rfl | hxN | ⟨b, hbB, hxb⟩
    · have hyR : y ∈ cfg.R := by rw [← hNz]; exact (G.mem_neighborFinset x y).mpr hxy
      rw [hψz, hψN y (hR_subN hyR)]; exact (hf_R y hyR).symm
    · have hyN : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy
      rw [hψu, hψN y hyN]; exact (hf_mem y hyN).2.symm
    · have hxN' := hxN
      rw [cfg.hN_eq, cfg.hR_eq, Finset.mem_union, Finset.mem_union] at hxN'
      rcases hxN' with hxY | hxT1 | hxB
      · rw [cfg.hY_def] at hxY
        have hL := mem_leafNbrs.mp hxY
        rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
        have hyu : y = u := (huniq y hxy).trans (huniq u hL.1.symm).symm
        rw [hyu, hψN x hxN, hψu]; exact (hf_mem x hxN).2
      · have hxR := hT1_subR hxT1
        rcases cfg.hT1_all x hxT1 y hxy with rfl | rfl
        · rw [hψN x hxN, hψu]; exact (hf_mem x hxN).2
        · rw [hextz x hxR, hψN x hxN, hψz]; exact hf_R x hxR
      · have hxR := hB_subR hxB
        rcases cfg.hB_all x hxB y hxy with rfl | rfl | hyL
        · rw [hψN x hxN, hψu]; exact (hf_mem x hxN).2
        · rw [hextz x hxR, hψN x hxN, hψz]; exact hf_R x hxR
        · rw [hψN x hxN, hψL x hxB y hyL]; exact ((haB_spec x hxB).1 y hyL).2.symm
    · have hL := mem_leafNbrs.mp hxb
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨w, _, huniq⟩
      have hyb : y = b := (huniq y hxy).trans (huniq b hL.1.symm).symm
      rw [hyb, hψL b hbB x hxb, hψN b (hR_subN (hB_subR hbB))]
      exact ((haB_spec b hbB).1 x hxb).2
  · intro x _
    rcases hall_cases x with rfl | rfl | hxN | ⟨b, _, hxb⟩
    · rcases hz_pcf with ⟨r₁, hr₁R, r₂, hr₂R, hcol12⟩
      have h12 : r₁ ≠ r₂ := fun h => hcol12 (h ▸ rfl)
      have hz1 : G.Adj x r₁ := (G.mem_neighborFinset x r₁).mp (hNz.symm ▸ hr₁R)
      have hz2 : G.Adj x r₂ := (G.mem_neighborFinset x r₂).mp (hNz.symm ▸ hr₂R)
      exact pcf_at_deg_three_of_two_distinct hdz hz1 hz2 h12
        (by rw [hψN r₁ (hR_subN hr₁R), hψN r₂ (hR_subN hr₂R)]; exact hcol12)
    · rcases hu_pcf with ⟨y, hyN, hy_uniq⟩
      refine ⟨y, (G.mem_neighborFinset x y).mp hyN, ?_⟩
      intro t hxt hψt
      have htN : t ∈ G.neighborFinset x := (G.mem_neighborFinset x t).mpr hxt
      rw [hψN t htN, hψN y hyN] at hψt
      exact hy_uniq t htN hψt
    · rw [cfg.hN_eq, cfg.hR_eq, Finset.mem_union, Finset.mem_union] at hxN
      rcases hxN with hxY | hxT1 | hxB
      · rw [cfg.hY_def] at hxY
        exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm
      · have hxR := hT1_subR hxT1
        have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (hR_subN hxR)
        exact pcf_at_of_two_distinct_neighbors (cfg.hT1_deg x hxT1) hux.symm
          (hextz x hxR ▸ (cfg.hext_spec x hxR).1) hzu.symm
          (by rw [hψu, hψz]; exact hT1_pcf x hxT1)
      · have hxR := hB_subR hxB
        have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (hR_subN hxR)
        rcases (haB_spec x hxB).2 with ⟨γ, hγ⟩
        have hfilt : (leafNbrs G x).filter (fun p => ψ p = γ) =
            (leafNbrs G x).filter (fun p => aB x p = γ) := by
          ext p; simp only [Finset.mem_filter]
          exact ⟨fun ⟨hp, h⟩ => ⟨hp, by rwa [hψL x hxB p hp] at h⟩,
            fun ⟨hp, h⟩ => ⟨hp, by rw [hψL x hxB p hp]; exact h⟩⟩
        exact pcf_of_pair_and_finset (ψ := ψ) (v := x) (x₁ := u) (x₂ := z)
          (W := leafNbrs G x) (γ := γ) hux.symm (hextz x hxR ▸ (cfg.hext_spec x hxR).1)
          (fun p hp => (mem_leafNbrs.mp hp).1)
          (fun t hxt => by
            have := cfg.hB_all x hxB t hxt
            rwa [hextz x hxR] at this)
          (by rw [hfilt, hψu, hψz]; exact hγ)
    · exact pcf_at_deg_one (mem_leafNbrs.mp hxb).2 (mem_leafNbrs.mp hxb).1.symm
  · intro x
    rcases hall_cases x with rfl | rfl | hxN | ⟨b, hbB, hxb⟩
    · rw [hψz]; exact hδ
    · rw [hψu]; exact hα
    · rw [hψN x hxN]; exact (hf_mem x hxN).1
    · rw [hψL b hbB x hxb]; exact ((haB_spec b hbB).1 x hxb).1

/-! ## 3. 统一排除孤立外部 `3`-度点（证明所有外部锚点在 `G - S` 中皆非孤立） -/

/-- 在 `Core3Setup` 中，每个 `r ∈ cfg.R` 的外部邻点 `cfg.ext r` 在 `G - cfg.S` 中皆非孤立。 -/
private lemma Core3Setup.all_ext_noniso {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    {hm : MinimalCounterexample p q G L} {hpq : 2 * p ≤ 5 * q} {u : V}
    (cfg : Core3Setup hm hpq u) :
    ∀ r ∈ cfg.R, ∃ w, w ∉ cfg.S ∧ G.Adj (cfg.ext r) w := by
  classical
  by_contra hno
  push Not at hno
  rcases hno with ⟨r₀, hr₀R, hiso⟩
  let z := cfg.ext r₀
  have hzS : z ∉ cfg.S := (cfg.hext_spec r₀ hr₀R).2.2.2
  have hdz3 : 3 ≤ G.degree z := (cfg.hext_spec r₀ hr₀R).2.2.1
  have hNz_sub : G.neighborFinset z ⊆ cfg.R := by
    intro x hx
    have hzx : G.Adj z x := (G.mem_neighborFinset z x).mp hx
    have hxS : x ∈ cfg.S := by by_contra h; exact hiso x h hzx
    exact (cfg.hS_out z hzS x hxS hzx).1
  have hNz : G.neighborFinset z = cfg.R :=
    Finset.eq_of_subset_of_card_le hNz_sub
      (by rw [SimpleGraph.card_neighborFinset_eq_degree, cfg.hR_card]; exact hdz3)
  have hdz : G.degree z = 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNz, cfg.hR_card]
  have hextz : ∀ r ∈ cfg.R, cfg.ext r = z := by
    intro r hrR
    have hzr : G.Adj z r := (G.mem_neighborFinset z r).mp (hNz.symm ▸ hrR)
    have hrS : r ∈ cfg.S := by
      rw [cfg.hS_def]; apply Finset.mem_insert_of_mem; apply Finset.mem_union_left
      rw [cfg.hN_eq]; exact Finset.mem_union_right _ hrR
    exact (cfg.hS_out z hzS r hrS hzr).2.symm
  have hall : insert z cfg.S = Finset.univ := by
    apply eq_univ_of_closed hm.conn (v₀ := u) (Finset.mem_insert_of_mem cfg.huS)
    intro a ha b hab
    simp only [Finset.mem_insert] at ha ⊢
    rcases ha with rfl | haS
    · have hbR : b ∈ cfg.R := by rw [← hNz]; exact (G.mem_neighborFinset z b).mpr hab
      right; rw [cfg.hS_def]; apply Finset.mem_insert_of_mem; apply Finset.mem_union_left
      rw [cfg.hN_eq]; exact Finset.mem_union_right _ hbR
    · by_cases hbS : b ∈ cfg.S
      · exact Or.inr hbS
      · rcases cfg.hS_out b hbS a haS hab.symm with ⟨haR, rfl⟩
        exact Or.inl (hextz a haR)
  -- 取 `δ ∈ L z`，用 `bad_three_color_extension` 为每个 `r ∈ cfg.R` 构造 `|P r| ≥ 3` 与 `ban r`！
  have hLz : (L z).card = 4 := by rw [hm.list_card z]; simp [kappa, hdz]
  rcases Finset.card_pos.mp (by omega : 0 < (L z).card) with ⟨δ, hδ⟩
  have hpkg_ex : ∀ r, r ∈ cfg.R →
      ∃ (Pr : Finset ℕ) (banr : ℕ), Pr ⊆ L r \ {δ} ∧ 3 ≤ Pr.card ∧
        (r ∈ cfg.T1 → banr = δ) ∧
        (r ∈ cfg.B → ∀ c ∈ Pr, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G r, a p ∈ L p ∧ a p ≠ c) ∧
          ((leafNbrs G r).filter (fun p => a p = banr)).card +
            (if δ = banr then 1 else 0) = 1) := by
    intro r hrR
    rw [cfg.hR_eq, Finset.mem_union] at hrR
    rcases hrR with hr1 | hrB
    · have hLr : (L r).card = 4 := by rw [hm.list_card r]; simp [kappa, cfg.hT1_deg r hr1]
      have hcard3 : 3 ≤ (L r \ {δ}).card := by
        have := card_sdiff_ge (L r) {δ}; simp only [Finset.card_singleton] at this; omega
      exact ⟨L r \ {δ}, δ, subset_rfl, hcard3, fun _ => rfl,
        fun hB => False.elim (Finset.disjoint_left.mp cfg.hT1B_disj hr1 hB)⟩
    · have hbad := cfg.hB_bad r hrB
      have hWcard := cfg.hB_leaf_card r hrB
      have hLr : (L r).card = G.degree r + 1 := by
        rw [hm.list_card r]; simp [kappa, show G.degree r ≠ 2 by have := hbad.1; omega]
      have hL2 : ∀ p ∈ leafNbrs G r, (L p).card = 2 := fun p hp => by
        rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2]
      have hCb : (leafNbrs G r).card + 2 ≤ (L r \ {δ}).card := by
        have := card_sdiff_ge (L r) {δ}; simp only [Finset.card_singleton] at this; omega
      rcases bad_three_color_extension (δ := δ) hWcard.1 hL2 hCb (by simp) with
        ⟨Pr, lam, hPr_sub, hPr3, hPr_ext⟩
      exact ⟨Pr, lam, hPr_sub, by omega,
        fun h1 => False.elim (Finset.disjoint_left.mp cfg.hT1B_disj h1 hrB),
        fun _ => hPr_ext⟩
  let P : V → Finset ℕ := fun r => if hr : r ∈ cfg.R then (hpkg_ex r hr).choose else ∅
  let ban : V → ℕ := fun r => if hr : r ∈ cfg.R then (hpkg_ex r hr).choose_spec.choose else 0
  have hP_spec : ∀ r (hr : r ∈ cfg.R),
      P r ⊆ L r \ {δ} ∧ 3 ≤ (P r).card ∧
      (r ∈ cfg.T1 → ban r = δ) ∧
      (r ∈ cfg.B → ∀ c ∈ P r, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G r, a p ∈ L p ∧ a p ≠ c) ∧
        ((leafNbrs G r).filter (fun p => a p = ban r)).card +
          (if δ = ban r then 1 else 0) = 1) := by
    intro r hr; simp only [P, ban, hr, dite_true]; exact (hpkg_ex r hr).choose_spec.choose_spec
  rcases Finset.card_eq_three.mp cfg.hR_card with ⟨r₁, r₂, r₃, h12, h13, h23, hR_tri⟩
  have hr₁R : r₁ ∈ cfg.R := by rw [hR_tri]; simp
  have hr₂R : r₂ ∈ cfg.R := by rw [hR_tri]; simp
  have hr₃R : r₃ ∈ cfg.R := by rw [hR_tri]; simp
  have hLu : (L u).card = cfg.Y.card + 4 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by have := cfg.hdu3; omega]
    have := cfg.hY_card; omega
  let C : Finset ℕ := L u \ cfg.R.image ban
  have hC : cfg.Y.card + 1 ≤ C.card := by
    dsimp only [C]
    have h1 := card_sdiff_ge (L u) (cfg.R.image ban)
    have h2 : (cfg.R.image ban).card ≤ cfg.R.card := Finset.card_image_le
    have := cfg.hR_card; omega
  have hP_sdiff2 : ∀ r ∈ cfg.R, ∀ α : ℕ, 2 ≤ (P r \ {α}).card := by
    intro r hr α
    have h1 := card_sdiff_ge (P r) {α}
    have h2 := (hP_spec r hr).2.1
    simp only [Finset.card_singleton] at h1; omega
  -- 构造公共的坏点延拓验证器
  have hmk_B_ext : ∀ (α : ℕ) (f : V → ℕ),
      α ∈ C → (∀ r ∈ cfg.R, f r ∈ P r) →
      ∀ b ∈ cfg.B, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G b, a p ∈ L p ∧ a p ≠ f b) ∧
        ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => a p = γ)).card +
          ([α, δ] : List ℕ).count γ = 1 := by
    intro α f hαC hfP b hbB
    have hbR : b ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hbB
    have hα_ban : α ≠ ban b := fun h =>
      (Finset.mem_sdiff.mp hαC).2 (h ▸ Finset.mem_image_of_mem ban hbR)
    rcases (hP_spec b hbR).2.2.2 hbB (f b) (hfP b hbR) with ⟨a, ha_mem, ha_u⟩
    refine ⟨a, ha_mem, ban b, ?_⟩
    rw [count_pair_eq]; simp only [hα_ban, ite_false, zero_add]
    exact ha_u
  have hmk_T1_pcf : ∀ α ∈ C, ∀ w ∈ cfg.T1, α ≠ δ := by
    intro α hαC w hw1
    have hwR : w ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_left _ hw1
    have hban := (hP_spec w hwR).2.2.1 hw1
    intro h
    rw [← hban] at h
    exact (Finset.mem_sdiff.mp hαC).2 (h ▸ Finset.mem_image_of_mem ban hwR)
  -- 分 `cfg.Y = ∅`（`d(u) = 3`）与 `cfg.Y.Nonempty`（`d(u) ≥ 4`）两步完成！
  by_cases hYe : cfg.Y = ∅
  · have hdu_eq3 : G.degree u = 3 := by
      have := cfg.hY_card; rw [hYe, Finset.card_empty] at this; omega
    rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α, hαC⟩
    rcases Finset.card_pos.mp (by have := hP_sdiff2 r₁ hr₁R α; omega : 0 < (P r₁ \ {α}).card)
      with ⟨c₁, hc₁⟩
    rcases exists_mem_sdiff_of_lt (A := P r₂ \ {α}) (B := {c₁})
      (by simp only [Finset.card_singleton]; have := hP_sdiff2 r₂ hr₂R α; omega)
      with ⟨c₂, hc₂, hc₂1⟩
    rcases Finset.card_pos.mp (by have := hP_sdiff2 r₃ hr₃R α; omega : 0 < (P r₃ \ {α}).card)
      with ⟨c₃, hc₃⟩
    rw [Finset.mem_singleton] at hc₂1
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hc₁ hc₂ hc₃
    let f : V → ℕ := fun x => if x = r₁ then c₁ else if x = r₂ then c₂ else c₃
    have hf1 : f r₁ = c₁ := by simp [f]
    have hf2 : f r₂ = c₂ := by simp [f, h12.symm]
    have hf3 : f r₃ = c₃ := by simp [f, h13.symm, h23.symm]
    have hfP : ∀ r ∈ cfg.R, f r ∈ P r := by
      intro r hr; rw [hR_tri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hf1]; exact hc₁.1
      · rw [hf2]; exact hc₂.1
      · rw [hf3]; exact hc₃.1
    have hf_ne_α : ∀ r ∈ cfg.R, f r ≠ α := by
      intro r hr; rw [hR_tri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hf1]; exact hc₁.2
      · rw [hf2]; exact hc₂.2
      · rw [hf3]; exact hc₃.2
    have hNR : G.neighborFinset u = cfg.R := by rw [cfg.hN_eq, hYe, Finset.empty_union]
    have hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y := by
      have hr1u : G.Adj u r₁ := (G.mem_neighborFinset u r₁).mp (hNR.symm ▸ hr₁R)
      have hr2u : G.Adj u r₂ := (G.mem_neighborFinset u r₂).mp (hNR.symm ▸ hr₂R)
      rcases pcf_at_deg_three_of_two_distinct (ψ := f) hdu_eq3 hr1u hr2u h12
        (by rw [hf1, hf2]; exact Ne.symm hc₂1) with ⟨y, huy, hy_u⟩
      exact ⟨y, (G.mem_neighborFinset u y).mpr huy,
        fun t ht hft => hy_u t ((G.mem_neighborFinset u t).mp ht) hft⟩
    exact cfg.contradiction_isolated z hzS hdz hNz hextz hall δ hδ α
      (Finset.mem_sdiff.mp hαC).1 f
      (fun r hr => by
        rw [hNR] at hr
        exact ⟨(Finset.mem_sdiff.mp ((hP_spec r hr).1 (hfP r hr))).1, hf_ne_α r hr⟩)
      (fun r hr => by
        have hm' := Finset.mem_sdiff.mp ((hP_spec r hr).1 (hfP r hr))
        rw [Finset.mem_singleton] at hm'; exact hm'.2)
      (hmk_T1_pcf α hαC) (hmk_B_ext α f hαC hfP) hu_pcf
      ⟨r₁, hr₁R, r₂, hr₂R, by rw [hf1, hf2]; exact Ne.symm hc₂1⟩
  · -- `cfg.Y` 非空：对每个 `α ∈ C` 固定 `c₁ ≠ c₂` 后在 `J' = insert r₃ cfg.Y` 上双计数！
    have hY_pos : 1 ≤ cfg.Y.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hYe)
    let J' : Finset V := insert r₃ cfg.Y
    have hr3_not_Y : r₃ ∉ cfg.Y := Finset.disjoint_right.mp cfg.hYR_disj hr₃R
    have hJ'_card : J'.card = cfg.Y.card + 1 := Finset.card_insert_of_notMem hr3_not_Y
    have hJ'_subN : J' ⊆ G.neighborFinset u := by
      intro r hr; rw [cfg.hN_eq]; simp only [J', Finset.mem_insert] at hr
      rcases hr with rfl | hrY
      · exact Finset.mem_union_right _ hr₃R
      · exact Finset.mem_union_left _ hrY
    have hr1_not_J' : r₁ ∉ J' := by
      simp only [J', Finset.mem_insert, not_or]
      exact ⟨h13, Finset.disjoint_right.mp cfg.hYR_disj hr₁R⟩
    have hr2_not_J' : r₂ ∉ J' := by
      simp only [J', Finset.mem_insert, not_or]
      exact ⟨h23, Finset.disjoint_right.mp cfg.hYR_disj hr₂R⟩
    have hN_part : ∀ r ∈ G.neighborFinset u, r = r₁ ∨ r = r₂ ∨ r ∈ J' := by
      intro r hr; rw [cfg.hN_eq, Finset.mem_union] at hr
      rcases hr with hrY | hrR
      · exact Or.inr (Or.inr (Finset.mem_insert_of_mem hrY))
      · rw [hR_tri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hrR
        rcases hrR with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (h3 ▸ Finset.mem_insert_self r₃ cfg.Y))
    have hY_L2 : ∀ y ∈ cfg.Y, (L y).card = 2 := fun y hy => by
      rw [cfg.hY_def] at hy; rw [hm.list_card y]; simp [kappa, (mem_leafNbrs.mp hy).2]
    let A : ℕ → V → Finset ℕ := fun α r => if r = r₃ then P r₃ \ {α} else L r \ {α}
    have hA_ne : ∀ α r (hr : r ∈ J'), (A α r).Nonempty := by
      intro α r hr; rw [← Finset.card_pos]
      dsimp only [A]; split_ifs with h3
      · have := hP_sdiff2 r₃ hr₃R α; omega
      · have hrY : r ∈ cfg.Y := (Finset.mem_insert.mp hr).resolve_left h3
        have := card_sdiff_ge (L r) {α}; have := hY_L2 r hrY
        simp only [Finset.card_singleton] at *; omega
    -- 对每个 `α ∈ C`，在 `cfg.Y` 中必有至少 `2` 个单点集！
    have hq_ge2 : ∀ α ∈ C, 2 ≤ (cfg.Y.filter (fun y => (L y \ {α}).card = 1)).card := by
      intro α hαC
      rcases Finset.card_pos.mp (by have := hP_sdiff2 r₁ hr₁R α; omega : 0 < (P r₁ \ {α}).card)
        with ⟨c₁, hc₁⟩
      rcases exists_mem_sdiff_of_lt (A := P r₂ \ {α}) (B := {c₁})
        (by simp only [Finset.card_singleton]; have := hP_sdiff2 r₂ hr₂R α; omega)
        with ⟨c₂, hc₂, hc₂1⟩
      rw [Finset.mem_singleton] at hc₂1
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hc₁ hc₂
      have hno_rep : ¬ ∃ a : {r : V // r ∈ J'} → ℕ, IsPCFRep (fun i => A α i.val) [c₁, c₂] a := by
        rintro ⟨a, ha_mem, γ, hγ⟩
        let f : V → ℕ := fun x =>
          if x = r₁ then c₁ else if x = r₂ then c₂
          else if hx : x ∈ J' then a ⟨x, hx⟩ else 0
        have hf1 : f r₁ = c₁ := by simp [f]
        have hf2 : f r₂ = c₂ := by simp [f, h12.symm]
        have hfJ' : ∀ r (hr : r ∈ J'), f r = a ⟨r, hr⟩ := by
          intro r hr
          have h1 : r ≠ r₁ := fun h => hr1_not_J' (h ▸ hr)
          have h2 : r ≠ r₂ := fun h => hr2_not_J' (h ▸ hr)
          simp only [f, h1, h2, hr, ite_false, dite_true]
        have hr3J' : r₃ ∈ J' := Finset.mem_insert_self r₃ cfg.Y
        have ha3 := ha_mem ⟨r₃, hr3J'⟩
        simp only [A, ite_true, Finset.mem_sdiff, Finset.mem_singleton] at ha3
        have hfP : ∀ r ∈ cfg.R, f r ∈ P r := by
          intro r hr; rw [hR_tri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with h1 | h2 | h3
          · rw [h1, hf1]; exact hc₁.1
          · rw [h2, hf2]; exact hc₂.1
          · rw [h3, hfJ' r₃ hr3J']; exact ha3.1
        have hfilt : (J'.filter (fun p => f p = γ)).card =
            (Finset.univ.filter (fun i : {r : V // r ∈ J'} => a i = γ)).card := by
          rw [← card_subtype_filter_eq]
          congr 1; ext i; simp only [Finset.mem_filter, hfJ' i.val i.property]
        have hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y := by
          have hr1u : G.Adj u r₁ := (G.mem_neighborFinset u r₁).mp
            (by rw [cfg.hN_eq]; exact Finset.mem_union_right _ hr₁R)
          have hr2u : G.Adj u r₂ := (G.mem_neighborFinset u r₂).mp
            (by rw [cfg.hN_eq]; exact Finset.mem_union_right _ hr₂R)
          rcases pcf_of_pair_and_finset (ψ := f) (v := u) (x₁ := r₁) (x₂ := r₂) (W := J') (γ := γ)
            hr1u hr2u (fun p hp => (G.mem_neighborFinset u p).mp (hJ'_subN hp))
            (fun t ht => hN_part t ((G.mem_neighborFinset u t).mpr ht))
            (by rw [hfilt, hf1, hf2]; exact hγ) with ⟨y, huy, hy_u⟩
          exact ⟨y, (G.mem_neighborFinset u y).mpr huy,
            fun t ht hft => hy_u t ((G.mem_neighborFinset u t).mp ht) hft⟩
        exact cfg.contradiction_isolated z hzS hdz hNz hextz hall δ hδ α
          (Finset.mem_sdiff.mp hαC).1 f
          (fun r hr => by
            rcases hN_part r hr with h1 | h2 | hrJ'
            · rw [h1, hf1]; exact ⟨(Finset.mem_sdiff.mp ((hP_spec r₁ hr₁R).1 hc₁.1)).1, hc₁.2⟩
            · rw [h2, hf2]; exact ⟨(Finset.mem_sdiff.mp ((hP_spec r₂ hr₂R).1 hc₂.1)).1, hc₂.2⟩
            · rw [hfJ' r hrJ']
              by_cases h3 : r = r₃
              · have ha3' : a ⟨r, hrJ'⟩ = a ⟨r₃, hr3J'⟩ := congrArg a (Subtype.ext h3)
                rw [ha3', h3]
                exact ⟨(Finset.mem_sdiff.mp ((hP_spec r₃ hr₃R).1 ha3.1)).1, ha3.2⟩
              · have hm' := ha_mem ⟨r, hrJ'⟩
                simp only [A, h3, ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
                exact hm')
          (fun r hr => by
            have hm' := Finset.mem_sdiff.mp ((hP_spec r hr).1 (hfP r hr))
            rw [Finset.mem_singleton] at hm'; exact hm'.2)
          (hmk_T1_pcf α hαC) (hmk_B_ext α f hαC hfP) hu_pcf
          ⟨r₁, hr₁R, r₂, hr₂R, by rw [hf1, hf2]; exact Ne.symm hc₂1⟩
      have : Nonempty {r : V // r ∈ J'} := ⟨⟨r₃, Finset.mem_insert_self r₃ cfg.Y⟩⟩
      have hq2 := no_pcfRep_pair_ge_two (fun i : {r // r ∈ J'} => hA_ne α i.val i.property)
        (by rw [Fintype.card_coe, hJ'_card]; omega) hno_rep
      rw [card_subtype_filter_eq J' (fun r => (A α r).card = 1)] at hq2
      have hfilt_eq : J'.filter (fun r => (A α r).card = 1) =
          cfg.Y.filter (fun y => (L y \ {α}).card = 1) := by
        ext r; simp only [J', Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h3 | hrY, h1⟩
          · rw [h3] at h1; simp only [A, ite_true] at h1; have := hP_sdiff2 r₃ hr₃R α; omega
          · have hne3 : r ≠ r₃ := fun h => hr3_not_Y (h ▸ hrY)
            simp only [A, hne3, ite_false] at h1; exact ⟨hrY, h1⟩
        · rintro ⟨hrY, h1⟩
          have hne3 : r ≠ r₃ := fun h => hr3_not_Y (h ▸ hrY)
          exact ⟨Or.inr hrY, by simp only [A, hne3, ite_false]; exact h1⟩
      rw [← hfilt_eq]; exact hq2
    -- 双计数：`2 * (|Y| + 1) ≤ 2 * |C| ≤ ∑_{α ∈ C} q_Y(α) ≤ 2 * |Y|`，立即矛盾！
    have hlower : 2 * C.card ≤
        ∑ α ∈ C, (cfg.Y.filter (fun y => (L y \ {α}).card = 1)).card := by
      calc 2 * C.card = ∑ _α ∈ C, 2 := by simp [mul_comm]
        _ ≤ ∑ α ∈ C, (cfg.Y.filter (fun y => (L y \ {α}).card = 1)).card :=
          Finset.sum_le_sum hq_ge2
    have hupper :
        ∑ α ∈ C, (cfg.Y.filter (fun y => (L y \ {α}).card = 1)).card ≤ 2 * cfg.Y.card := by
      rw [sum_filter_card_comm]
      calc ∑ y ∈ cfg.Y, (C.filter (fun α => (L y \ {α}).card = 1)).card
          ≤ ∑ _y ∈ cfg.Y, 2 := Finset.sum_le_sum (fun y hy =>
            (card_filter_sdiff_singleton_eq_one_le C (L y) (by have := hY_L2 y hy; omega)).1)
        _ = 2 * cfg.Y.card := by simp [mul_comm]
    omega

/-! ## 4. 容许染色下的双色自由度打包与坏点定色延拓接口 -/

/-- 在容许染色 `adm` 下，为每个核心邻点 `r ∈ cfg.R` 统一打包大小 `≥ 2` 的备选集 `P r` 与禁色 `ban r`。 -/
private lemma Core3Setup.exists_core_packages {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    {hm : MinimalCounterexample p q G L} {hpq : 2 * p ≤ 5 * q} {u : V}
    (cfg : Core3Setup hm hpq u) (adm : AdmissibleColoring G L cfg.S) :
    ∃ (P : V → Finset ℕ) (ban : V → ℕ),
      ∀ r ∈ cfg.R, 2 ≤ (P r).card ∧
        (∀ c ∈ P r, c ∈ L r ∧ c ≠ adm.φ (cfg.ext r) ∧ c ≠ adm.φs (cfg.ext r)) ∧
        (r ∈ cfg.T1 → ban r = adm.φ (cfg.ext r)) ∧
        (r ∈ cfg.B → ∀ c ∈ P r, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G r, a p ∈ L p ∧ a p ≠ c) ∧
          ((leafNbrs G r).filter (fun p => a p = ban r)).card +
            (if adm.φ (cfg.ext r) = ban r then 1 else 0) = 1) := by
  classical
  have hpkg : ∀ r, r ∈ cfg.R →
      ∃ (Pr : Finset ℕ) (banr : ℕ), 2 ≤ Pr.card ∧
        (∀ c ∈ Pr, c ∈ L r ∧ c ≠ adm.φ (cfg.ext r) ∧ c ≠ adm.φs (cfg.ext r)) ∧
        (r ∈ cfg.T1 → banr = adm.φ (cfg.ext r)) ∧
        (r ∈ cfg.B → ∀ c ∈ Pr, ∃ a : V → ℕ, (∀ p ∈ leafNbrs G r, a p ∈ L p ∧ a p ≠ c) ∧
          ((leafNbrs G r).filter (fun p => a p = banr)).card +
            (if adm.φ (cfg.ext r) = banr then 1 else 0) = 1) := by
    intro r hrR
    rw [cfg.hR_eq, Finset.mem_union] at hrR
    rcases hrR with hr1 | hrB
    · have hLr : (L r).card = 4 := by rw [hm.list_card r]; simp [kappa, cfg.hT1_deg r hr1]
      let Pr : Finset ℕ := L r \ {adm.φ (cfg.ext r), adm.φs (cfg.ext r)}
      have hPr2 : 2 ≤ Pr.card := by
        dsimp only [Pr]
        have := card_sdiff_ge (L r) {adm.φ (cfg.ext r), adm.φs (cfg.ext r)}
        have := Finset.card_le_two (a := adm.φ (cfg.ext r)) (b := adm.φs (cfg.ext r)); omega
      refine ⟨Pr, adm.φ (cfg.ext r), hPr2, ?_, fun _ => rfl,
        fun hB => False.elim (Finset.disjoint_left.mp cfg.hT1B_disj hr1 hB)⟩
      intro c hc
      simp only [Pr, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2⟩
    · have hbad := cfg.hB_bad r hrB
      have hWcard := cfg.hB_leaf_card r hrB
      have hLr : (L r).card = G.degree r + 1 := by
        rw [hm.list_card r]; simp [kappa, show G.degree r ≠ 2 by have := hbad.1; omega]
      have hL2 : ∀ p ∈ leafNbrs G r, (L p).card = 2 := fun p hp => by
        rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2]
      let Cb : Finset ℕ := L r \ {adm.φ (cfg.ext r), adm.φs (cfg.ext r)}
      have hCb : (leafNbrs G r).card + 1 ≤ Cb.card := by
        dsimp only [Cb]
        have := card_sdiff_ge (L r) {adm.φ (cfg.ext r), adm.φs (cfg.ext r)}
        have := Finset.card_le_two (a := adm.φ (cfg.ext r)) (b := adm.φs (cfg.ext r)); omega
      rcases bad_two_color_extension (δ := adm.φ (cfg.ext r)) hWcard.1 hL2 hCb (by simp [Cb]) with
        ⟨γ₁, γ₂, lam, hγ₁, hγ₂, hγ12, hE1, hE2⟩
      refine ⟨{γ₁, γ₂}, lam, by rw [Finset.card_pair hγ12], ?_,
        fun h1 => False.elim (Finset.disjoint_left.mp cfg.hT1B_disj h1 hrB), ?_⟩
      · intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        have hcCb : c ∈ Cb := by rcases hc with rfl | rfl <;> assumption
        simp only [Cb, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcCb
        exact ⟨hcCb.1, hcCb.2.1, hcCb.2.2⟩
      · intro _ c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact hE1
        · exact hE2
  refine ⟨fun r => if hr : r ∈ cfg.R then (hpkg r hr).choose else ∅,
    fun r => if hr : r ∈ cfg.R then (hpkg r hr).choose_spec.choose else 0, ?_⟩
  intro r hr; simp only [hr, dite_true]; exact (hpkg r hr).choose_spec.choose_spec

/-- 在容许染色 `adm` 下，给定 `u` 的任意颜色 `α`，单个坏邻点 `b ∈ cfg.B` 及其叶邻点总可延拓并避开 `φs`。 -/
private lemma Core3Setup.bad_fixed_ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    {hm : MinimalCounterexample p q G L} {hpq : 2 * p ≤ 5 * q} {u : V}
    (cfg : Core3Setup hm hpq u) (adm : AdmissibleColoring G L cfg.S)
    {b : V} (hb : b ∈ cfg.B) (α : ℕ) :
    ∃ c : ℕ, c ∈ L b ∧ c ≠ α ∧ c ≠ adm.φ (cfg.ext b) ∧ c ≠ adm.φs (cfg.ext b) ∧
      ∃ a : V → ℕ, (∀ p ∈ leafNbrs G b, a p ∈ L p ∧ a p ≠ c) ∧
        ∃ γ : ℕ, ((leafNbrs G b).filter (fun p => a p = γ)).card +
          ([α, adm.φ (cfg.ext b)] : List ℕ).count γ = 1 := by
  have hbad := cfg.hB_bad b hb
  have hWcard := cfg.hB_leaf_card b hb
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by have := hbad.1; omega]
  have hL2 : ∀ p ∈ leafNbrs G b, (L p).card = 2 := fun p hp => by
    rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2]
  let Rb : Finset ℕ := L b \ {α, adm.φ (cfg.ext b), adm.φs (cfg.ext b)}
  have hRb : (if α = adm.φ (cfg.ext b) then (leafNbrs G b).card + 1
      else (leafNbrs G b).card) ≤ Rb.card := by
    dsimp only [Rb]
    have hsd := card_sdiff_ge (L b) {α, adm.φ (cfg.ext b), adm.φs (cfg.ext b)}
    split_ifs with heq
    · have hpair : ({α, adm.φ (cfg.ext b), adm.φs (cfg.ext b)} : Finset ℕ) =
          {adm.φ (cfg.ext b), adm.φs (cfg.ext b)} := by
        rw [heq]; ext x; simp
      rw [hpair] at hsd ⊢
      have := Finset.card_le_two (a := adm.φ (cfg.ext b)) (b := adm.φs (cfg.ext b)); omega
    · have := card_triple_le α (adm.φ (cfg.ext b)) (adm.φs (cfg.ext b)); omega
  rcases bad_fixed_color_extension hWcard.1 hL2 (by simp [Rb]) hRb with ⟨c, hcRb, a, ha_mem, γ, hγ⟩
  simp only [Rb, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcRb
  exact ⟨c, hcRb.1, hcRb.2.1, hcRb.2.2.1, hcRb.2.2.2, a, ha_mem, γ, hγ⟩

end LeanResearch.Proposal3

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 5. 主定理 1：含叶核心度 `3` 且无长线串、无好核心邻点构型的精确分类 -/

/-- 若 `coreDeg G u = 3`、`4 ≤ G.degree u` 且无 `2`-线串、`3`-线串及好核心邻点，
则除 `G.degree u = 4 ∧ |oneThreadNbrs| = 3 ∧ |badNbrs| = 0`（`4_1_3` 顶点）外全部可约！ -/
lemma no_leafy_coreDeg3_all_a_b_except_L4 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (hc3 : coreDeg G u = 3) (hdu4 : 4 ≤ G.degree u)
    (hno2 : twoThreadNbrs G u = ∅) (hno3 : threeThreadNbrs G u = ∅)
    (hgood0 : goodNbrs G u = ∅) :
    G.degree u = 4 ∧ (oneThreadNbrs G u).card = 3 ∧ (badNbrs G u).card = 0 := by
  classical
  let cfg := mkCore3Setup hm hpq hc3 hno2 hno3 hgood0
  have hnoniso := cfg.all_ext_noniso
  rcases exists_admissible_coloring hm (S := cfg.S) ⟨u, cfg.huS⟩ with ⟨adm⟩
  rcases cfg.exists_core_packages adm with ⟨P, ban, hP_spec⟩
  let J : Finset V := G.neighborFinset u
  have hJ_card : J.card = G.degree u := SimpleGraph.card_neighborFinset_eq_degree G u
  let PFull : V → Finset ℕ := fun r => if r ∈ cfg.R then P r else L r
  have hPFull_card2 : ∀ r ∈ J, 2 ≤ (PFull r).card := by
    intro r hr
    dsimp only [PFull]; split_ifs with hrR
    · exact (hP_spec r hrR).1
    · have hrY : r ∈ cfg.Y := by
        dsimp only [J] at hr
        rw [cfg.hN_eq, Finset.mem_union] at hr; exact hr.resolve_right hrR
      rw [cfg.hY_def] at hrY
      rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  let C : Finset ℕ := L u \ cfg.R.image ban
  have hC_ge : G.degree u - 2 ≤ C.card := by
    dsimp only [C]
    have h1 := card_sdiff_ge (L u) (cfg.R.image ban)
    have h2 : (cfg.R.image ban).card ≤ cfg.R.card := Finset.card_image_le
    have := cfg.hR_card; omega
  -- 1. 对每个 `α ∈ C`，`PFull r \ {α}` 在 `J` 上无 `B = []` 的 `PCF`-代表系统！
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ a : {r : V // r ∈ J} → ℕ, IsPCFRep (fun i => PFull i.val \ {α}) [] a := by
    intro α hαC ⟨a, ha_mem, γ, hγ⟩
    let f : V → ℕ := fun r => if hr : r ∈ J then a ⟨r, hr⟩ else 0
    have hfJ : ∀ r (hr : r ∈ J), f r = a ⟨r, hr⟩ := fun r hr => by simp only [f, hr, dite_true]
    have hf_R_memP : ∀ r ∈ cfg.R, f r ∈ P r ∧ f r ≠ α := by
      intro r hrR
      have hrJ : r ∈ J := by dsimp only [J]; rw [cfg.hN_eq]; exact Finset.mem_union_right _ hrR
      have hm' := ha_mem ⟨r, hrJ⟩
      simp only [PFull, hrR, ite_true, Finset.mem_sdiff, Finset.mem_singleton] at hm'
      rw [hfJ r hrJ]; exact hm'
    have hu_pcf : ∃ y ∈ J, ∀ t ∈ J, f t = f y → t = y := by
      simp only [List.count_nil, add_zero] at hγ
      rcases Finset.card_eq_one.mp hγ with ⟨⟨y₀, hy₀⟩, hy₀_eq⟩
      have hy₀_col : a ⟨y₀, hy₀⟩ = γ := by
        have : (⟨y₀, hy₀⟩ : {r // r ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) := by
          rw [hy₀_eq]; simp
        exact (Finset.mem_filter.mp this).2
      refine ⟨y₀, hy₀, ?_⟩
      intro t ht hft
      rw [hfJ t ht, hfJ y₀ hy₀, hy₀_col] at hft
      have : (⟨t, ht⟩ : {r // r ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hft⟩
      rw [hy₀_eq, Finset.mem_singleton] at this
      exact congrArg Subtype.val this
    exact cfg.contradiction_noniso hnoniso adm α (Finset.mem_sdiff.mp hαC).1 f
      (fun r hrJ => by
        rw [hfJ r hrJ]
        have hm' := ha_mem ⟨r, hrJ⟩
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hm'
        by_cases hrR : r ∈ cfg.R
        · simp only [PFull, hrR, ite_true] at hm'
          exact ⟨((hP_spec r hrR).2.1 _ hm'.1).1, hm'.2⟩
        · simp only [PFull, hrR, ite_false] at hm'; exact hm')
      (fun r hrR => by
        have h1 := (hP_spec r hrR).2.1 (f r) (hf_R_memP r hrR).1
        exact ⟨h1.2.1, h1.2.2⟩)
      (fun w hw1 => by
        have hwR : w ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_left _ hw1
        rw [← (hP_spec w hwR).2.2.1 hw1]
        intro h; exact (Finset.mem_sdiff.mp hαC).2 (h ▸ Finset.mem_image_of_mem ban hwR))
      (fun b hbB => by
        have hbR : b ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hbB
        have hα_ban : α ≠ ban b := fun h =>
          (Finset.mem_sdiff.mp hαC).2 (h ▸ Finset.mem_image_of_mem ban hbR)
        rcases (hP_spec b hbR).2.2.2 hbB (f b) (hf_R_memP b hbR).1 with ⟨aW, haW_mem, haW_u⟩
        refine ⟨aW, haW_mem, ban b, ?_⟩
        rw [count_pair_eq]; simp only [hα_ban, ite_false, zero_add]
        exact haW_u)
      hu_pcf
  -- 2. 双计数：`4 * (d(u) - 2) ≤ 4 * |C| ≤ ∑_{α ∈ C} q_α ≤ 2 * d(u)` → 必有 `d(u) = 4` 且处处取等！
  have hlower : 4 * C.card ≤ ∑ α ∈ C, (J.filter (fun r => (PFull r \ {α}).card = 1)).card := by
    calc 4 * C.card = ∑ _α ∈ C, 4 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, (J.filter (fun r => (PFull r \ {α}).card = 1)).card := by
        apply Finset.sum_le_sum
        intro α hαC
        rcases Finset.card_pos.mp (by omega : 0 < J.card) with ⟨r₀, hr₀⟩
        have : Nonempty {r : V // r ∈ J} := ⟨⟨r₀, hr₀⟩⟩
        have hne : ∀ i : {r : V // r ∈ J}, (PFull i.val \ {α}).Nonempty := by
          intro i; rw [← Finset.card_pos]
          have h1 := card_sdiff_ge (PFull i.val) {α}
          have h2 := hPFull_card2 i.val i.property
          simp only [Finset.card_singleton] at h1; omega
        have hq4 := (no_pcfRep_nil_bounds hne (hno_rep α hαC)).2
          (by rw [Fintype.card_coe, hJ_card]; exact hdu4)
        rw [card_subtype_filter_eq J (fun r => (PFull r \ {α}).card = 1)] at hq4
        exact hq4
  have hterm : ∀ r ∈ J, (C.filter (fun α => (PFull r \ {α}).card = 1)).card ≤ 2 := fun r hr =>
    (card_filter_sdiff_singleton_eq_one_le C (PFull r) (hPFull_card2 r hr)).1
  have hupper : ∑ α ∈ C, (J.filter (fun r => (PFull r \ {α}).card = 1)).card ≤ 2 * J.card := by
    rw [sum_filter_card_comm]
    calc ∑ r ∈ J, (C.filter (fun α => (PFull r \ {α}).card = 1)).card
        ≤ ∑ _r ∈ J, 2 := Finset.sum_le_sum hterm
      _ = 2 * J.card := by simp [mul_comm]
  have hdu_eq4 : G.degree u = 4 := by omega
  have hC2 : C.card = 2 := by omega
  have hsum_eq : ∑ r ∈ J, (C.filter (fun α => (PFull r \ {α}).card = 1)).card = 2 * J.card := by
    rw [sum_filter_card_comm] at hlower hupper; omega
  -- 取等推出：`ban` 在 `cfg.R` 上单射且像集含于 `L u`，同时每个 `r ∈ J` 都有 `PFull r ⊆ C`！
  have him_card : (cfg.R.image ban).card = 3 := by
    have h1 := Finset.card_sdiff_add_card_inter (L u) (cfg.R.image ban)
    have h2 : (L u ∩ cfg.R.image ban).card ≤ (cfg.R.image ban).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h3 : (cfg.R.image ban).card ≤ cfg.R.card := Finset.card_image_le
    have := cfg.hR_card; dsimp only [C] at hC2; omega
  have him_sub_Lu : cfg.R.image ban ⊆ L u := by
    have h1 := Finset.card_sdiff_add_card_inter (L u) (cfg.R.image ban)
    have hEq : L u ∩ cfg.R.image ban = cfg.R.image ban :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by dsimp only [C] at hC2; omega)
    intro c hc; rw [← hEq] at hc; exact (Finset.mem_inter.mp hc).1
  have hban_inj : Set.InjOn ban cfg.R :=
    Finset.injOn_of_card_image_eq (by rw [him_card, cfg.hR_card])
  have hPFull_sub_C : ∀ r ∈ J, PFull r ⊆ C := by
    intro r hr
    have heq2 : (C.filter (fun α => (PFull r \ {α}).card = 1)).card = 2 := by
      by_contra hne2
      have hlt2 : (C.filter (fun α => (PFull r \ {α}).card = 1)).card < 2 := by
        have := hterm r hr; omega
      have hlt_sum : ∑ s ∈ J, (C.filter (fun α => (PFull s \ {α}).card = 1)).card < ∑ _s ∈ J, 2 :=
        Finset.sum_lt_sum hterm ⟨r, hr, hlt2⟩
      simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
    exact ((card_filter_sdiff_singleton_eq_one_le C (PFull r) (hPFull_card2 r hr)).2 heq2).2
  -- 3. 证明 `(badNbrs G u).card = 0`（从而自动得 `(oneThreadNbrs G u).card = 3`）！
  have hB0 : (badNbrs G u).card = 0 := by
    by_contra hBne
    rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hBne) with ⟨b₀, hb₀B⟩
    have hb₀B' : b₀ ∈ cfg.B := by rw [cfg.hB_def]; exact hb₀B
    have hb₀R : b₀ ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hb₀B'
    have hb₀J : b₀ ∈ J := by dsimp only [J]; rw [cfg.hN_eq]; exact Finset.mem_union_right _ hb₀R
    let α₀ := ban b₀
    have hα₀_im : α₀ ∈ cfg.R.image ban := Finset.mem_image_of_mem ban hb₀R
    have hα₀_Lu : α₀ ∈ L u := him_sub_Lu hα₀_im
    have hα₀_notC : α₀ ∉ C := fun h => (Finset.mem_sdiff.mp h).2 hα₀_im
    -- 对 `b₀` 调用定色延拓 `bad_fixed_ext` 得 `cb₀`！
    rcases cfg.bad_fixed_ext adm hb₀B' α₀ with
      ⟨cb₀, hcb₀L, hcb₀α, hcb₀φ, hcb₀φs, aW₀, haW₀_mem, γ₀, hγ₀⟩
    let J' : Finset V := J \ {b₀}
    have hJ'_card : J'.card = 3 := by
      dsimp only [J']
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hb₀J),
          Finset.card_singleton]; omega
    -- 对所有 `r ∈ J'`，`α₀ ∉ PFull r`，故 `|PFull r \ {α₀}| ≥ 2`（零个单点集！）
    have hcard_ge2 : ∀ r ∈ J', 2 ≤ (PFull r \ {α₀}).card := by
      intro r hrJ'
      have hrJ : r ∈ J := (Finset.mem_sdiff.mp hrJ').1
      have hα₀_notP : α₀ ∉ PFull r := fun h => hα₀_notC (hPFull_sub_C r hrJ h)
      have hEq : PFull r \ {α₀} = PFull r := by
        ext c; simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨And.left, fun hc => ⟨hc, fun h => hα₀_notP (h ▸ hc)⟩⟩
      rw [hEq]; exact hPFull_card2 r hrJ
    have hno_rep' : ¬ ∃ a : {r : V // r ∈ J'} → ℕ,
        IsPCFRep (fun i => PFull i.val \ {α₀}) [cb₀] a := by
      rintro ⟨a, ha_mem, γ, hγ⟩
      let f : V → ℕ := fun r => if r = b₀ then cb₀ else if hr : r ∈ J' then a ⟨r, hr⟩ else 0
      have hfb₀ : f b₀ = cb₀ := by simp [f]
      have hfJ' : ∀ r (hr : r ∈ J'), f r = a ⟨r, hr⟩ := by
        intro r hr
        have hne : r ≠ b₀ := by
          have := (Finset.mem_sdiff.mp hr).2; rwa [Finset.mem_singleton] at this
        simp only [f, hne, hr, ite_false, dite_true]
      have hfilt : (J'.filter (fun r => f r = γ)).card =
          (Finset.univ.filter (fun i : {r : V // r ∈ J'} => a i = γ)).card := by
        rw [← card_subtype_filter_eq]
        congr 1; ext i; simp only [Finset.mem_filter, hfJ' i.val i.property]
      have hu_pcf : ∃ y ∈ J, ∀ t ∈ J, f t = f y → t = y := by
        rcases pcf_of_single_and_finset (ψ := f) (v := u) (x := b₀) (W := J') (γ := γ)
          ((G.mem_neighborFinset u b₀).mp hb₀J)
          (fun p hp => (G.mem_neighborFinset u p).mp (Finset.mem_sdiff.mp hp).1)
          (fun t ht => by
            by_cases htb : t = b₀
            · exact Or.inl htb
            · exact Or.inr (Finset.mem_sdiff.mpr
                ⟨(G.mem_neighborFinset u t).mpr ht, by simp [htb]⟩))
          (by rw [hfilt, hfb₀]; exact hγ) with ⟨y, huy, hy_u⟩
        exact ⟨y, (G.mem_neighborFinset u y).mpr huy,
          fun t ht hft => hy_u t ((G.mem_neighborFinset u t).mp ht) hft⟩
      have hf_R_other : ∀ r ∈ cfg.R, r ≠ b₀ → f r ∈ P r ∧ f r ≠ α₀ := by
        intro r hrR hne
        have hrJ : r ∈ J := by dsimp only [J]; rw [cfg.hN_eq]; exact Finset.mem_union_right _ hrR
        have hrJ' : r ∈ J' := Finset.mem_sdiff.mpr ⟨hrJ, by simp [hne]⟩
        have hm' := ha_mem ⟨r, hrJ'⟩
        simp only [PFull, hrR, ite_true, Finset.mem_sdiff, Finset.mem_singleton] at hm'
        rw [hfJ' r hrJ']; exact hm'
      exact cfg.contradiction_noniso hnoniso adm α₀ hα₀_Lu f
        (fun r hrJ => by
          by_cases hrb : r = b₀
          · subst hrb; rw [hfb₀]; exact ⟨hcb₀L, hcb₀α⟩
          · have hrJ' : r ∈ J' := Finset.mem_sdiff.mpr ⟨hrJ, by simp [hrb]⟩
            rw [hfJ' r hrJ']
            have hm' := ha_mem ⟨r, hrJ'⟩
            rw [Finset.mem_sdiff, Finset.mem_singleton] at hm'
            by_cases hrR : r ∈ cfg.R
            · simp only [PFull, hrR, ite_true] at hm'
              exact ⟨((hP_spec r hrR).2.1 _ hm'.1).1, hm'.2⟩
            · simp only [PFull, hrR, ite_false] at hm'; exact hm')
        (fun r hrR => by
          by_cases hrb : r = b₀
          · subst hrb; rw [hfb₀]; exact ⟨hcb₀φ, hcb₀φs⟩
          · have h1 := (hP_spec r hrR).2.1 (f r) (hf_R_other r hrR hrb).1
            exact ⟨h1.2.1, h1.2.2⟩)
        (fun w hw1 => by
          have hwR : w ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_left _ hw1
          have hne : w ≠ b₀ := fun h => Finset.disjoint_left.mp cfg.hT1B_disj hw1 (h ▸ hb₀B')
          rw [← (hP_spec w hwR).2.2.1 hw1]
          exact fun h => hne (hban_inj hwR hb₀R h.symm))
        (fun b hbB => by
          by_cases hbb : b = b₀
          · subst hbb; rw [hfb₀]; exact ⟨aW₀, haW₀_mem, γ₀, hγ₀⟩
          · have hbR : b ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hbB
            have hα_ban : α₀ ≠ ban b := fun h => hbb (hban_inj hbR hb₀R h.symm)
            rcases (hP_spec b hbR).2.2.2 hbB (f b) (hf_R_other b hbR hbb).1 with
              ⟨aW, haW_mem, haW_u⟩
            refine ⟨aW, haW_mem, ban b, ?_⟩
            rw [count_pair_eq]; simp only [hα_ban, ite_false, zero_add]
            exact haW_u)
        hu_pcf
    rcases Finset.card_pos.mp (by omega : 0 < J'.card) with ⟨r₀, hr₀⟩
    have : Nonempty {r : V // r ∈ J'} := ⟨⟨r₀, hr₀⟩⟩
    have hne' : ∀ i : {r : V // r ∈ J'}, (PFull i.val \ {α₀}).Nonempty := fun i =>
      Finset.card_pos.mp (by have := hcard_ge2 i.val i.property; omega)
    have hq1 := (no_pcfRep_single_bounds hne' hno_rep').1
    rw [card_subtype_filter_eq J' (fun r => (PFull r \ {α₀}).card = 1)] at hq1
    have hzero : (J'.filter (fun r => (PFull r \ {α₀}).card = 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r hr; have := hcard_ge2 r hr; omega
    omega
  have hfive := coreDeg_eq_five_parts hm hpq u
  rw [hno2, hno3, hgood0, Finset.card_empty] at hfive
  exact ⟨hdu_eq4, by omega, hB0⟩

/-! ## 6. 主定理 2：`3`-度且无好核心邻点的顶点至多有 `1` 个坏核心邻点 -/

/-- 若 `G.degree u = 3` 且 `goodNbrs G u = ∅`，则 `(badNbrs G u).card ≤ 1`
（彻底排除 `(a=1, b=2, g=0)` 与 `(a=0, b=3, g=0)`）。 -/
lemma deg_three_no_good_at_most_one_bad {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (hdu3 : G.degree u = 3) (hgood0 : goodNbrs G u = ∅) :
    (badNbrs G u).card ≤ 1 := by
  classical
  by_contra hgt
  push Not at hgt
  have hB2 : 2 ≤ (badNbrs G u).card := by omega
  have hc3 : coreDeg G u = 3 := by
    rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdu3]
  have hlong0 : longThreadNbrs G u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have := deg_ge_four_of_longThreadNbr hm (by omega) hv
    omega
  have hno2 : twoThreadNbrs G u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have : v ∈ longThreadNbrs G u := by
      rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_left _ hv
    rw [hlong0] at this; exact Finset.notMem_empty v this
  have hno3 : threeThreadNbrs G u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have : v ∈ longThreadNbrs G u := by
      rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_right _ hv
    rw [hlong0] at this; exact Finset.notMem_empty v this
  let cfg := mkCore3Setup hm hpq hc3 hno2 hno3 hgood0
  have hnoniso := cfg.all_ext_noniso
  rcases exists_admissible_coloring hm (S := cfg.S) ⟨u, cfg.huS⟩ with ⟨adm⟩
  rcases cfg.exists_core_packages adm with ⟨P, ban, hP_spec⟩
  -- 取出两个互异坏邻点 `b₂ ≠ b₃ ∈ cfg.B` 与唯一第三个核心邻点 `r₁ ∈ cfg.R`
  rcases exists_two_of_card_ge_two (by rw [cfg.hB_def]; exact hB2 : 2 ≤ cfg.B.card) with
    ⟨b₂, hb₂B, b₃, hb₃B, h23⟩
  have hb₂R : b₂ ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hb₂B
  have hb₃R : b₃ ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hb₃B
  rcases exists_third_coreNbr (u := u) hc3 (by rw [← cfg.hR_def]; exact hb₂R)
      (by rw [← cfg.hR_def]; exact hb₃R) h23 with ⟨r₁, hr₁R', h12, h13, hR_tri⟩
  have hr₁R : r₁ ∈ cfg.R := by rw [cfg.hR_def]; exact hr₁R'
  have hR_eq3 : cfg.R = {b₂, b₃, r₁} := by rw [cfg.hR_def]; exact hR_tri
  have hY_empty : cfg.Y = ∅ := by
    rw [cfg.hY_def]; exact leafNbrs_eq_empty_of_deg_le_three hm (by omega)
  have hNR : G.neighborFinset u = cfg.R := by rw [cfg.hN_eq, hY_empty, Finset.empty_union]
  have hLu : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  -- 取 `α₀ ∈ L u \ cfg.R.image ban`（基数 ≥ 4 - 3 = 1）
  let C : Finset ℕ := L u \ cfg.R.image ban
  have hC1 : 1 ≤ C.card := by
    dsimp only [C]
    have h1 := card_sdiff_ge (L u) (cfg.R.image ban)
    have h2 : (cfg.R.image ban).card ≤ cfg.R.card := Finset.card_image_le
    have := cfg.hR_card; omega
  rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α₀, hα₀C⟩
  have hPr_ne : ∀ r ∈ cfg.R, (P r \ {α₀}).Nonempty := by
    intro r hrR; rw [← Finset.card_pos]
    have h1 := card_sdiff_ge (P r) {α₀}; have h2 := (hP_spec r hrR).1
    simp only [Finset.card_singleton] at h1; omega
  -- 若 `P r₁ \ {α₀}` 与 `P b₂ \ {α₀}` 能选出两个不同颜色，直接用 `α₀` 延拓矛盾！
  by_cases hdiff : ∃ cx ∈ P r₁ \ {α₀}, ∃ cy ∈ P b₂ \ {α₀}, cx ≠ cy
  · rcases hdiff with ⟨c₁, hc₁, c₂, hc₂, hc12⟩
    rcases hPr_ne b₃ hb₃R with ⟨c₃, hc₃⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hc₁ hc₂ hc₃
    let f : V → ℕ := fun x => if x = r₁ then c₁ else if x = b₂ then c₂ else c₃
    have hf1 : f r₁ = c₁ := by simp [f]
    have hf2 : f b₂ = c₂ := by simp [f, h12.symm]
    have hf3 : f b₃ = c₃ := by simp [f, h13.symm, h23.symm]
    have hfP : ∀ r ∈ cfg.R, f r ∈ P r ∧ f r ≠ α₀ := by
      intro r hr; rw [hR_eq3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hf2]; exact hc₂
      · rw [hf3]; exact hc₃
      · rw [hf1]; exact hc₁
    have hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y := by
      have hr1u : G.Adj u r₁ := (G.mem_neighborFinset u r₁).mp (hNR.symm ▸ hr₁R)
      have hb2u : G.Adj u b₂ := (G.mem_neighborFinset u b₂).mp (hNR.symm ▸ hb₂R)
      rcases pcf_at_deg_three_of_two_distinct (ψ := f) hdu3 hr1u hb2u h12
        (by rw [hf1, hf2]; exact hc12) with ⟨y, huy, hy_u⟩
      exact ⟨y, (G.mem_neighborFinset u y).mpr huy,
        fun t ht hft => hy_u t ((G.mem_neighborFinset u t).mp ht) hft⟩
    exact cfg.contradiction_noniso hnoniso adm α₀ (Finset.mem_sdiff.mp hα₀C).1 f
      (fun r hr => by
        rw [hNR] at hr
        exact ⟨((hP_spec r hr).2.1 (f r) (hfP r hr).1).1, (hfP r hr).2⟩)
      (fun r hr => by
        have h1 := (hP_spec r hr).2.1 (f r) (hfP r hr).1
        exact ⟨h1.2.1, h1.2.2⟩)
      (fun w hw1 => by
        have hwR : w ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_left _ hw1
        rw [← (hP_spec w hwR).2.2.1 hw1]
        intro h; exact (Finset.mem_sdiff.mp hα₀C).2 (h ▸ Finset.mem_image_of_mem ban hwR))
      (fun b hbB => by
        have hbR : b ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hbB
        have hα_ban : α₀ ≠ ban b := fun h =>
          (Finset.mem_sdiff.mp hα₀C).2 (h ▸ Finset.mem_image_of_mem ban hbR)
        rcases (hP_spec b hbR).2.2.2 hbB (f b) (hfP b hbR).1 with ⟨aW, haW_mem, haW_u⟩
        refine ⟨aW, haW_mem, ban b, ?_⟩
        rw [count_pair_eq]; simp only [hα_ban, ite_false, zero_add]
        exact haW_u)
      hu_pcf
  · -- 否则 `P r₁ \ {α₀}` 与 `P b₂ \ {α₀}` 塌缩为同一单点 `{c₀}`，故 `P r₁ ⊆ {α₀, c₀}`！
    push Not at hdiff
    rcases hPr_ne b₂ hb₂R with ⟨c₀, hc₀⟩
    have hPr1_sub : P r₁ ⊆ {α₀, c₀} := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hca : c = α₀
      · exact Or.inl hca
      · exact Or.inr (hdiff c (Finset.mem_sdiff.mpr ⟨hc, by simp [hca]⟩) c₀ hc₀)
    -- 任取 `α₁ ∈ L u \ {α₀, c₀, ban r₁}`（`|L u| = 4 > 3`）：`α₁ ∉ P r₁` 且 `α₁ ≠ ban r₁`！
    rcases exists_mem_sdiff_of_lt (A := L u) (B := {α₀, c₀, ban r₁})
      (by have := card_triple_le α₀ c₀ (ban r₁); omega) with ⟨α₁, hα₁Lu, hα₁n⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα₁n
    have hα₁_notPr1 : α₁ ∉ P r₁ := fun h => by
      have hm' := hPr1_sub h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with h1 | h2
      · exact hα₁n.1 h1
      · exact hα₁n.2.1 h2
    -- 对两个坏邻点 `b₂, b₃` 调用定色延拓 `bad_fixed_ext`，再选 `c₁ ∈ P r₁ \ {c₂}` 使 `u` 满足 PCF！
    rcases cfg.bad_fixed_ext adm hb₂B α₁ with
      ⟨c₂, hc₂L, hc₂α, hc₂φ, hc₂φs, aW₂, haW₂_mem, γ₂, hγ₂⟩
    rcases cfg.bad_fixed_ext adm hb₃B α₁ with
      ⟨c₃, hc₃L, hc₃α, hc₃φ, hc₃φs, aW₃, haW₃_mem, γ₃, hγ₃⟩
    rcases exists_mem_sdiff_of_lt (A := P r₁) (B := {c₂})
      (by simp only [Finset.card_singleton]; have := (hP_spec r₁ hr₁R).1; omega)
      with ⟨c₁, hc₁P, hc₁2⟩
    rw [Finset.mem_singleton] at hc₁2
    have hc₁α : c₁ ≠ α₁ := fun h => hα₁_notPr1 (h ▸ hc₁P)
    let f : V → ℕ := fun x => if x = r₁ then c₁ else if x = b₂ then c₂ else c₃
    have hf1 : f r₁ = c₁ := by simp [f]
    have hf2 : f b₂ = c₂ := by simp [f, h12.symm]
    have hf3 : f b₃ = c₃ := by simp [f, h13.symm, h23.symm]
    have hu_pcf : ∃ y ∈ G.neighborFinset u, ∀ t ∈ G.neighborFinset u, f t = f y → t = y := by
      have hr1u : G.Adj u r₁ := (G.mem_neighborFinset u r₁).mp (hNR.symm ▸ hr₁R)
      have hb2u : G.Adj u b₂ := (G.mem_neighborFinset u b₂).mp (hNR.symm ▸ hb₂R)
      rcases pcf_at_deg_three_of_two_distinct (ψ := f) hdu3 hr1u hb2u h12
        (by rw [hf1, hf2]; exact hc₁2) with ⟨y, huy, hy_u⟩
      exact ⟨y, (G.mem_neighborFinset u y).mpr huy,
        fun t ht hft => hy_u t ((G.mem_neighborFinset u t).mp ht) hft⟩
    exact cfg.contradiction_noniso hnoniso adm α₁ hα₁Lu f
      (fun r hr => by
        rw [hNR, hR_eq3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h2 | h3 | h1
        · rw [h2, hf2]; exact ⟨hc₂L, hc₂α⟩
        · rw [h3, hf3]; exact ⟨hc₃L, hc₃α⟩
        · rw [h1, hf1]; exact ⟨((hP_spec r₁ hr₁R).2.1 c₁ hc₁P).1, hc₁α⟩)
      (fun r hr => by
        rw [hR_eq3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h2 | h3 | h1
        · rw [h2, hf2]; exact ⟨hc₂φ, hc₂φs⟩
        · rw [h3, hf3]; exact ⟨hc₃φ, hc₃φs⟩
        · rw [h1, hf1]
          have h := (hP_spec r₁ hr₁R).2.1 c₁ hc₁P
          exact ⟨h.2.1, h.2.2⟩)
      (fun w hw1 => by
        have hwR : w ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_left _ hw1
        rw [hR_eq3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hwR
        rcases hwR with h2 | h3 | h1
        · exact False.elim (Finset.disjoint_left.mp cfg.hT1B_disj hw1 (h2.symm ▸ hb₂B))
        · exact False.elim (Finset.disjoint_left.mp cfg.hT1B_disj hw1 (h3.symm ▸ hb₃B))
        · rw [h1, ← (hP_spec r₁ hr₁R).2.2.1 (h1 ▸ hw1)]; exact hα₁n.2.2)
      (fun b hbB => by
        have hbR : b ∈ cfg.R := by rw [cfg.hR_eq]; exact Finset.mem_union_right _ hbB
        rw [hR_eq3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hbR
        rcases hbR with h2 | h3 | h1
        · rw [h2, hf2]; exact ⟨aW₂, haW₂_mem, γ₂, hγ₂⟩
        · rw [h3, hf3]; exact ⟨aW₃, haW₃_mem, γ₃, hγ₃⟩
        · rw [h1, hf1]
          rcases (hP_spec r₁ hr₁R).2.2.2 (h1 ▸ hbB) c₁ hc₁P with ⟨aW₁, haW₁_mem, haW₁_u⟩
          refine ⟨aW₁, haW₁_mem, ban r₁, ?_⟩
          rw [count_pair_eq]; simp only [hα₁n.2.2, ite_false, zero_add]
          exact haW₁_u)
      hu_pcf

end LeanResearch.Proposal3
