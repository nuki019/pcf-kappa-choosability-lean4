/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.ThreadDefs

/-!
# 坏核心点与长线串核心结构引理（`BadAndThreads1`：Lemmas 3.4–3.8）

本模块对任意满足 `0 < q ∧ 2 * p ≤ 5 * q`（即 `mad(G) < 5/2`，同时覆盖 `12/5` 与 `22/9`！）的极小反例，
证明以下零 `sorry` 可约构型引理：
1. `bad_has_core_three_plus_neighbor`（Lemma 3.4）：坏点不能有两个 `2`-度邻点；
2. `leaf_plus_long_thread_le`（Lemma 3.5，升级至全域 `mad < 5/2`）：
   任意 `3⁺`-度点满足 `n_1(u) + n_{2⁺-th}(u) + 2 ≤ d_G(u)`；
   推论：`coreDeg_ge_two_of_deg_ge_three`（所有 `3⁺`-度点非好即坏）、`bad_no_long_thread`；
3. `bad_no_one_thread`（Lemma 3.6）：坏点不关联 `1`-线串（故坏点的两个核心邻点均为 `3⁺`-度点）；
4. `bad_two_color_extension`（Lemma 3.7）：坏点的纯组合双色自由度引理；
5. `bad_fixed_color_extension`（核心复用的定色延拓引理）：给定一端核心邻点任意固定颜色，坏点及其叶邻点总可延拓；
6. `no_adjacent_bad`（Lemma 3.8）：任意两个坏核心点不相邻。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. Lemma 3.4：坏点至少有一个 `3⁺`-度核心邻点 -/

/-- Lemma 3.4：若 `u` 是坏核心点（`d_G(u) ≥ 4, d_K(u) = 2`），则 `u` 至少有一个 `3⁺`-度邻点
（即 `u` 不可能有两个 `2`-度邻点）。 -/
lemma bad_has_core_three_plus_neighbor {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hbad : IsBad G u) :
    ∃ x : V, G.Adj u x ∧ 3 ≤ G.degree x := by
  by_contra hno
  push Not at hno
  rcases hbad with ⟨hdu4, hcore2⟩
  -- `coreNbrs G u` 大小为 2，且其中每个顶点度数 = 2！
  have hsub2 : coreNbrs G u = degTwoNbrs G u := by
    ext v; simp only [mem_coreNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨huv, hdv2⟩; exact ⟨huv, by have := hno v huv; omega⟩
    · rintro ⟨huv, hdv2⟩; exact ⟨huv, by omega⟩
  have hcard2 : (degTwoNbrs G u).card = 2 := by rw [← hsub2]; exact hcore2
  rcases Finset.card_eq_two.mp hcard2 with ⟨x₁, x₂, hx12, hxset⟩
  have hx1_mem : x₁ ∈ degTwoNbrs G u := by rw [hxset]; simp
  have hx2_mem : x₂ ∈ degTwoNbrs G u := by rw [hxset]; simp
  simp only [degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx1_mem hx2_mem
  rcases hx1_mem with ⟨hux1, hdx1⟩
  rcases hx2_mem with ⟨hux2, hdx2⟩
  rcases exists_other_neighbor_of_deg_two hdx1 hux1.symm with ⟨y₁, hx1y1, hy1u, hx1_all⟩
  rcases exists_other_neighbor_of_deg_two hdx2 hux2.symm with ⟨y₂, hx2y2, hy2u, hx2_all⟩
  have hux1_ne : u ≠ x₁ := G.ne_of_adj hux1
  have hux2_ne : u ≠ x₂ := G.ne_of_adj hux2
  have hy1x1 : y₁ ≠ x₁ := (G.ne_of_adj hx1y1).symm
  have hy2x2 : y₂ ≠ x₂ := (G.ne_of_adj hx2y2).symm
  -- `y₁ ≠ x₂` 且 `y₂ ≠ x₁`（否则出现同锚点 `u` 的 `2`-线串 `u-x₁-x₂-u`）
  have hy1x2 : y₁ ≠ x₂ := by
    intro h; subst h
    exact no_two_thread_same_anchor hm (by omega) hdx1 hdx2 hux1 hx1y1 hux2.symm
  have hy2x1 : y₂ ≠ x₁ := by
    intro h; subst h
    exact no_two_thread_same_anchor hm (by omega) hdx1 hdx2 hux1 hx2y2.symm hux2.symm
  -- `y₁, y₂` 都不是 `1`-度点，故不在 `S = {u, x₁, x₂} ∪ leafNbrs G u` 中
  have hdy1_ge2 : 2 ≤ G.degree y₁ := by
    have h1 := degree_ge_one hm y₁
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree y₁ = 1) hx1y1.symm; omega
  have hdy2_ge2 : 2 ≤ G.degree y₂ := by
    have h1 := degree_ge_one hm y₂
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree y₂ = 1) hx2y2.symm; omega
  let S : Finset V := insert u (G.neighborFinset u)
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hS_nbr : ∀ z ∈ G.neighborFinset u, z = x₁ ∨ z = x₂ ∨ z ∈ leafNbrs G u := by
    intro z hz
    have hdz1 := degree_ge_one hm z
    by_cases h1 : G.degree z = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨(G.mem_neighborFinset u z).mp hz, h1⟩))
    · have hc : z ∈ coreNbrs G u :=
        mem_coreNbrs.mpr ⟨(G.mem_neighborFinset u z).mp hz, by omega⟩
      rw [hsub2, hxset, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hy1S : y₁ ∉ S := by
    intro h
    simp only [S, Finset.mem_insert] at h
    rcases h with rfl | h
    · exact hy1u rfl
    · rcases hS_nbr y₁ h with h' | h' | h'
      · exact hy1x1 h'
      · exact hy1x2 h'
      · rw [mem_leafNbrs] at h'; omega
  have hy2S : y₂ ∉ S := by
    intro h
    simp only [S, Finset.mem_insert] at h
    rcases h with rfl | h
    · exact hy2u rfl
    · rcases hS_nbr y₂ h with h' | h' | h'
      · exact hy2x1 h'
      · exact hy2x2 h'
      · rw [mem_leafNbrs] at h'; omega
  -- `S` 与外部 `G - S` 的所有边只能是 `(x₁, y₁)` 和 `(x₂, y₂)`！
  have hS_out : ∀ v, v ∉ S → ∀ z ∈ S, G.Adj v z → (z = x₁ ∧ v = y₁) ∨ (z = x₂ ∧ v = y₂) := by
    intro v hvS z hzS hvz
    simp only [S, Finset.mem_insert] at hzS
    rcases hzS with rfl | hzN
    · exact False.elim (hvS (Finset.mem_insert_of_mem ((G.mem_neighborFinset z v).mpr hvz.symm)))
    · rcases hS_nbr z hzN with rfl | rfl | hzL
      · rcases hx1_all v hvz.symm with rfl | rfl
        · exact False.elim (hvS huS)
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hx2_all v hvz.symm with rfl | rfl
        · exact False.elim (hvS huS)
        · exact Or.inr ⟨rfl, rfl⟩
      · rw [mem_leafNbrs] at hzL
        rcases exists_unique_neighbor_of_deg_one hzL.2 with ⟨w, _, huniq⟩
        have hvu : v = u := (huniq v hvz.symm).trans (huniq u hzL.1.symm).symm
        exact False.elim (hvS (hvu ▸ huS))
  -- 验证 `y₁` 与 `y₂` 在 `G - S` 中皆非孤立！
  have hnoniso_y1 : ∃ z, z ∉ S ∧ G.Adj y₁ z := by
    by_cases hy12 : y₁ = y₂
    · have hdy1_ge3 : 3 ≤ G.degree y₁ := by
        by_contra hlt; push Not at hlt
        exact no_three_thread_same_anchor hm (by omega) hdx1 (by omega : G.degree y₁ = 2) hdx2
          hux1 hx1y1 (hy12 ▸ hx2y2.symm) hux2.symm hx12
      have hlt : ({x₁, x₂} : Finset V).card < (G.neighborFinset y₁).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := x₁) (b := x₂); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_out y₁ hy1S z hzS hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hzn.1 rfl
      · exact hzn.2 rfl
    · have hlt : ({x₁} : Finset V).card < (G.neighborFinset y₁).card := by
        rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      rw [Finset.mem_singleton] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_out y₁ hy1S z hzS hz with ⟨rfl, _⟩ | ⟨rfl, hEq⟩
      · exact hzn rfl
      · exact hy12 hEq
  have hnoniso_y2 : ∃ z, z ∉ S ∧ G.Adj y₂ z := by
    by_cases hy12 : y₁ = y₂
    · rw [← hy12]; exact hnoniso_y1
    · have hlt : ({x₂} : Finset V).card < (G.neighborFinset y₂).card := by
        rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      rw [Finset.mem_singleton] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_out y₂ hy2S z hzS hz with ⟨rfl, hEq⟩ | ⟨rfl, _⟩
      · exact hy12 hEq.symm
      · exact hzn rfl
  -- 取 `G - S` 的容许染色并应用 `no_pcfRep_nil_bounds` 与双计数！
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  have hLx1 : (L x₁).card = 4 := by rw [hm.list_card x₁]; simp [kappa, hdx1]
  have hLx2 : (L x₂).card = 4 := by rw [hm.list_card x₂]; simp [kappa, hdx2]
  let C : Finset ℕ := L u \ {adm.φ y₁, adm.φ y₂}
  have hC : G.degree u - 1 ≤ C.card := by
    dsimp only [C]
    have := card_sdiff_ge (L u) {adm.φ y₁, adm.φ y₂}
    have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φ y₂); omega
  let P₁ : Finset ℕ := L x₁ \ {adm.φ y₁, adm.φs y₁}
  let P₂ : Finset ℕ := L x₂ \ {adm.φ y₂, adm.φs y₂}
  have hP1 : 2 ≤ P₁.card := by
    dsimp only [P₁]
    have := card_sdiff_ge (L x₁) {adm.φ y₁, adm.φs y₁}
    have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φs y₁); omega
  have hP2 : 2 ≤ P₂.card := by
    dsimp only [P₂]
    have := card_sdiff_ge (L x₂) {adm.φ y₂, adm.φs y₂}
    have := Finset.card_le_two (a := adm.φ y₂) (b := adm.φs y₂); omega
  let P : V → Finset ℕ := fun z =>
    if z = x₁ then P₁ else if z = x₂ then P₂ else L z
  have hP_card2 : ∀ z ∈ G.neighborFinset u, 2 ≤ (P z).card := by
    intro z hz
    rcases hS_nbr z hz with rfl | rfl | hzL
    · simp [P, hP1]
    · simp [P, hx12.symm, hP2]
    · have hzx1 : z ≠ x₁ := fun h => by rw [h] at hzL; rw [mem_leafNbrs] at hzL; omega
      have hzx2 : z ≠ x₂ := fun h => by rw [h] at hzL; rw [mem_leafNbrs] at hzL; omega
      simp only [P, hzx1, hzx2, ite_false]
      rw [hm.list_card z]; rw [mem_leafNbrs] at hzL; simp [kappa, hzL.2]
  -- 对任意 `α ∈ C`，`A_α(z) = P z \ {α}` 在 `N_G(u)` 上无 `B = []` 的 `PCF`-代表系统！
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ a : {z : V // z ∈ G.neighborFinset u} → ℕ,
          IsPCFRep (fun i => P i.val \ {α}) [] a := by
    intro α hα ⟨a, ha_mem, γ, hγ⟩
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    let ψ : V → ℕ := fun v =>
      if v = u then α
      else if hv : v ∈ G.neighborFinset u then a ⟨v, hv⟩
      else adm.φ v
    have hψu : ψ u = α := by simp [ψ]
    have hψN : ∀ z (hz : z ∈ G.neighborFinset u), ψ z = a ⟨z, hz⟩ := by
      intro z hz
      have hzu : z ≠ u := (G.ne_of_adj ((G.mem_neighborFinset u z).mp hz)).symm
      simp only [ψ, hzu, ite_false, hz, dite_true]
    have hψ_out : ∀ v, v ∉ S → ψ v = adm.φ v := by
      intro v hv; simp only [S, Finset.mem_insert, not_or] at hv
      simp only [ψ, hv.1, hv.2, ite_false, dite_false]
    have ha_ne_α : ∀ z (hz : z ∈ G.neighborFinset u), a ⟨z, hz⟩ ≠ α := fun z hz => by
      have h := ha_mem ⟨z, hz⟩; rw [Finset.mem_sdiff, Finset.mem_singleton] at h; exact h.2
    have ha_in_P : ∀ z (hz : z ∈ G.neighborFinset u), a ⟨z, hz⟩ ∈ P z := fun z hz =>
      (Finset.mem_sdiff.mp (ha_mem ⟨z, hz⟩)).1
    have hx1N : x₁ ∈ G.neighborFinset u := (G.mem_neighborFinset u x₁).mpr hux1
    have hx2N : x₂ ∈ G.neighborFinset u := (G.mem_neighborFinset u x₂).mpr hux2
    have hax1 : a ⟨x₁, hx1N⟩ ∈ P₁ := by simpa [P] using ha_in_P x₁ hx1N
    have hax2 : a ⟨x₂, hx2N⟩ ∈ P₂ := by simpa [P, hx12.symm] using ha_in_P x₂ hx2N
    simp only [P₁, P₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hax1 hax2
    apply adm.contradiction hm ψ hψ_out
    · intro z hz
      simp only [S, Finset.mem_insert] at hz
      rcases hz with rfl | hzN
      · rw [hψu]; exact hα.1
      · rw [hψN z hzN]
        rcases hS_nbr z hzN with rfl | rfl | hzL
        · exact hax1.1
        · exact hax2.1
        · have hzx1 : z ≠ x₁ := fun h => by rw [h] at hzL; rw [mem_leafNbrs] at hzL; omega
          have hzx2 : z ≠ x₂ := fun h => by rw [h] at hzL; rw [mem_leafNbrs] at hzL; omega
          simpa [P, hzx1, hzx2] using ha_in_P z hzN
    · intro v₁ v₂ h12 hor
      have hcase : ∀ p r, G.Adj p r → p ∈ S → ψ p ≠ ψ r := by
        intro p r hpr hp
        simp only [S, Finset.mem_insert] at hp
        rcases hp with rfl | hpN
        · have hrN : r ∈ G.neighborFinset p := (G.mem_neighborFinset p r).mpr hpr
          rw [hψu, hψN r hrN]; exact (ha_ne_α r hrN).symm
        · rcases hS_nbr p hpN with hp1 | hp2 | hpL
          · rcases hx1_all r (hp1 ▸ hpr) with hr | hr
            · rw [hp1, hr, hψN x₁ hx1N, hψu]; exact ha_ne_α x₁ hx1N
            · rw [hp1, hr, hψN x₁ hx1N, hψ_out y₁ hy1S]; exact hax1.2.1
          · rcases hx2_all r (hp2 ▸ hpr) with hr | hr
            · rw [hp2, hr, hψN x₂ hx2N, hψu]; exact ha_ne_α x₂ hx2N
            · rw [hp2, hr, hψN x₂ hx2N, hψ_out y₂ hy2S]; exact hax2.2.1
          · rw [mem_leafNbrs] at hpL
            rcases exists_unique_neighbor_of_deg_one hpL.2 with ⟨w, _, huniq⟩
            have hr : r = u := (huniq r hpr).trans (huniq u hpL.1.symm).symm
            rw [hr, hψN p hpN, hψu]; exact ha_ne_α p hpN
      rcases hor with h1 | h2
      · exact hcase v₁ v₂ h12 h1
      · exact (hcase v₂ v₁ h12.symm h2).symm
    · intro v hvS _ z hzS hvz
      rcases hS_out v hvS z hzS hvz with ⟨hz1, hv1⟩ | ⟨hz2, hv2⟩
      · rw [hz1, hv1, hψN x₁ hx1N]; exact hax1.2.2
      · rw [hz2, hv2, hψN x₂ hx2N]; exact hax2.2.2
    · intro v hvS hiso ⟨z, hvz⟩
      have hzS : z ∈ S := by by_contra h; exact hiso z h hvz
      rcases hS_out v hvS z hzS hvz with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rcases hnoniso_y1 with ⟨r, hrS, hr⟩; exact False.elim (hiso r hrS hr)
      · rcases hnoniso_y2 with ⟨r, hrS, hr⟩; exact False.elim (hiso r hrS hr)
    · intro v hvS _
      simp only [S, Finset.mem_insert] at hvS
      rcases hvS with hvu | hvN
      · subst v
        simp only [List.count_nil, add_zero] at hγ
        rcases Finset.card_eq_one.mp hγ with ⟨⟨z₀, hz₀⟩, hz₀_eq⟩
        have hz₀_col : a ⟨z₀, hz₀⟩ = γ := by
          have : (⟨z₀, hz₀⟩ : {z // z ∈ G.neighborFinset u}) ∈
              Finset.univ.filter (fun i => a i = γ) := by rw [hz₀_eq]; simp
          exact (Finset.mem_filter.mp this).2
        refine ⟨z₀, (G.mem_neighborFinset u z₀).mp hz₀, ?_⟩
        intro r hur hψr
        have hrN : r ∈ G.neighborFinset u := (G.mem_neighborFinset u r).mpr hur
        rw [hψN r hrN, hψN z₀ hz₀, hz₀_col] at hψr
        have : (⟨r, hrN⟩ : {z // z ∈ G.neighborFinset u}) ∈
            Finset.univ.filter (fun i => a i = γ) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψr⟩
        rw [hz₀_eq, Finset.mem_singleton] at this
        exact congrArg Subtype.val this
      · rcases hS_nbr v hvN with rfl | rfl | hvL
        · exact pcf_at_of_two_distinct_neighbors hdx1 hux1.symm hx1y1 hy1u.symm
            (by rw [hψu, hψ_out y₁ hy1S]; exact hα.2.1)
        · exact pcf_at_of_two_distinct_neighbors hdx2 hux2.symm hx2y2 hy2u.symm
            (by rw [hψu, hψ_out y₂ hy2S]; exact hα.2.2)
        · rw [mem_leafNbrs] at hvL
          exact pcf_at_deg_one hvL.2 hvL.1.symm
  -- 双计数：`4 * (k - 1) ≤ 4 * |C| ≤ ∑_{α ∈ C} q_α ≤ 2 * k`，与 `k ≥ 4` 矛盾！
  have hlower : 4 * C.card ≤
      ∑ α ∈ C, ((G.neighborFinset u).filter (fun z => (P z \ {α}).card = 1)).card := by
    calc 4 * C.card = ∑ _α ∈ C, 4 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, ((G.neighborFinset u).filter (fun z => (P z \ {α}).card = 1)).card := by
        apply Finset.sum_le_sum
        intro α hα
        have : Nonempty {z : V // z ∈ G.neighborFinset u} :=
          ⟨⟨x₁, (G.mem_neighborFinset u x₁).mpr hux1⟩⟩
        have hne : ∀ i : {z : V // z ∈ G.neighborFinset u}, (P i.val \ {α}).Nonempty := by
          intro i; rw [← Finset.card_pos]
          have h1 := card_sdiff_ge (P i.val) {α}
          have h2 := hP_card2 i.val i.property
          simp only [Finset.card_singleton] at h1; omega
        have h4 : 4 ≤ Fintype.card {z : V // z ∈ G.neighborFinset u} := by
          rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]; exact hdu4
        have hq4 := (no_pcfRep_nil_bounds hne (hno_rep α hα)).2 h4
        have hbij :
            (Finset.univ.filter (fun i : {z // z ∈ G.neighborFinset u} =>
              (P i.val \ {α}).card = 1)).card =
            ((G.neighborFinset u).filter (fun z => (P z \ {α}).card = 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact ⟨i.property, hi⟩
          · intro i₁ _ i₂ _ h; exact Subtype.ext h
          · intro z hz; simp only [Finset.mem_filter] at hz
            exact ⟨⟨z, hz.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.2⟩, rfl⟩
        rw [← hbij]; exact hq4
  have hupper :
      ∑ α ∈ C, ((G.neighborFinset u).filter (fun z => (P z \ {α}).card = 1)).card ≤
        2 * G.degree u := by
    rw [sum_filter_card_comm]
    calc ∑ z ∈ G.neighborFinset u, (C.filter (fun α => (P z \ {α}).card = 1)).card
        ≤ ∑ _z ∈ G.neighborFinset u, 2 :=
          Finset.sum_le_sum (fun z hz => (card_filter_sdiff_singleton_eq_one_le C (P z)
            (hP_card2 z hz)).1)
      _ = 2 * G.degree u := by
          simp [SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
  omega

/-! ## 2. Lemma 3.5（升级至全域 `mad < 5/2`）：`n_1(u) + n_{2⁺-th}(u) + 2 ≤ d_G(u)` -/

/-- 辅助引理（`ε = 0` 独立无 `mad` 染色证明）：极小反例中，若 `z`（`d(z) ≥ 4`）的全体邻点都是
来自同一顶点 `u` 的 `m = d(z)` 条 `2`-线串的末端 `w_i`（且 `¬ G.Adj u z`），则矛盾！ -/
private lemma no_isolated_two_thread_hub {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u z : V}
    (hdz4 : 4 ≤ G.degree z) (hnu : ¬ G.Adj u z) (huz : u ≠ z)
    {M : Finset V} {w : V → V}
    (hM_sub : M ⊆ G.neighborFinset u)
    (hM_deg : ∀ v ∈ M, G.degree v = 2 ∧ G.degree (w v) = 2 ∧ G.Adj v (w v) ∧ w v ≠ u ∧
      G.Adj (w v) z ∧ z ≠ v)
    (hM_inj : Set.InjOn w M)
    (hNz : G.neighborFinset z = M.image w) : False := by
  have hM_card : M.card = G.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNz, Finset.card_image_of_injOn hM_inj]
  have hM4 : 4 ≤ M.card := by omega
  have hLz : (L z).card = M.card + 1 := by
    rw [hm.list_card z]; simp only [kappa, ← hM_card, show M.card ≠ 2 by omega, ite_false]
  -- `w v ∉ M` 且 `w v ≠ z` 且 `w v ≠ u` 且 `z ∉ M`
  have hw_not_M : ∀ v ∈ M, w v ∉ M := by
    intro v hv hwM
    rcases hM_deg v hv with ⟨hdv, hdw, hvw, hwu, hwz, _⟩
    have huw : G.Adj u (w v) := (G.mem_neighborFinset u (w v)).mp (hM_sub hwM)
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hM_sub hv)
    have hdu3 : 3 ≤ G.degree u := by
      have hle : M.card ≤ G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]; exact Finset.card_le_card hM_sub
      omega
    exact no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw huw.symm
  have hz_not_M : z ∉ M := fun hzM => hnu ((G.mem_neighborFinset u z).mp (hM_sub hzM))
  have hu_not_M : u ∉ M := fun huM => G.ne_of_adj ((G.mem_neighborFinset u u).mp (hM_sub huM)) rfl
  let S' : Finset V := insert z (M ∪ M.image w)
  have huS' : u ∉ S' := by
    simp only [S', Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
      not_and]
    exact ⟨huz, hu_not_M, fun v hv h => (hM_deg v hv).2.2.2.1 h⟩
  have hS'_out : ∀ a, a ∉ S' → ∀ b ∈ S', G.Adj a b → a = u ∧ b ∈ M := by
    intro a haS' b hbS' hab
    simp only [S', Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hbS'
    rcases hbS' with hbz | hbM | ⟨v, hvM, rfl⟩
    · subst b
      have : a ∈ M.image w := by rw [← hNz]; exact (G.mem_neighborFinset z a).mpr hab.symm
      exact False.elim (haS' (by simp [S', this]))
    · rcases hM_deg b hbM with ⟨hdb, _, hbw, hwu, _, _⟩
      have hub : G.Adj u b := (G.mem_neighborFinset u b).mp (hM_sub hbM)
      have hNb := neighborFinset_eq_pair_of_deg_two hdb hub.symm hbw hwu.symm
      have ha_mem : a ∈ ({u, w b} : Finset V) := by
        rw [← hNb]; exact (G.mem_neighborFinset b a).mpr hab.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with rfl | rfl
      · exact ⟨rfl, hbM⟩
      · exact False.elim (haS' (by simp [S', Finset.mem_image_of_mem w hbM]))
    · rcases hM_deg v hvM with ⟨_, hdw, hvw, _, hwz, hzv⟩
      have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
      have ha_mem : a ∈ ({v, z} : Finset V) := by
        rw [← hNw]; exact (G.mem_neighborFinset (w v) a).mpr hab.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with rfl | rfl
      · exact False.elim (haS' (by simp [S', hvM]))
      · exact False.elim (haS' (by simp [S']))
  have hv_all : ∀ v ∈ M, ∀ x, G.Adj v x → x = u ∨ x = w v := by
    intro v hv x hvx
    rcases hM_deg v hv with ⟨hdv, _, hvw, hwu, _, _⟩
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hM_sub hv)
    have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : x ∈ ({u, w v} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v x).mpr hvx
    simpa using this
  have hw_all : ∀ v ∈ M, ∀ x, G.Adj (w v) x → x = v ∨ x = z := by
    intro v hv x hwx
    rcases hM_deg v hv with ⟨_, hdw, hvw, _, hwz, hzv⟩
    have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
    have : x ∈ ({v, z} : Finset V) := by rw [← hNw]; exact (G.mem_neighborFinset (w v) x).mpr hwx
    simpa using this
  -- 情形 1：`u` 在 `G - S'` 中非孤立
  by_cases hu_noniso : ∃ r, r ∉ S' ∧ G.Adj u r
  · rcases exists_admissible_coloring hm (S := S') ⟨z, by simp [S']⟩ with ⟨adm⟩
    -- 对每个 `β ∈ L z` 和 `v ∈ M`，先选 `a_v(β) ∈ L v \ {adm.φ u, adm.φs u, β}`
    have hpick : ∀ (β : ℕ) (v : V), v ∈ M →
        ∃ c ∈ L v, c ≠ adm.φ u ∧ c ≠ adm.φs u ∧ c ≠ β := by
      intro β v hv
      have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, (hM_deg v hv).1]
      rcases exists_mem_sdiff_of_lt (A := L v) (B := {adm.φ u, adm.φs u, β})
        (by have := card_triple_le (adm.φ u) (adm.φs u) β; omega) with ⟨c, hc, hcn⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
      exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
    let aFun : ℕ → V → ℕ := fun β v =>
      if hv : v ∈ M then (hpick β v hv).choose else 0
    have haFun_spec : ∀ β v (hv : v ∈ M),
        aFun β v ∈ L v ∧ aFun β v ≠ adm.φ u ∧ aFun β v ≠ adm.φs u ∧ aFun β v ≠ β := by
      intro β v hv; simp only [aFun, hv, dite_true]; exact (hpick β v hv).choose_spec
    -- 对每个 `β ∈ L z`，集合族 `A_β(v) = L (w v) \ {β, aFun β v, adm.φ u}` 在 `M` 上无 `B=[]` 代表系统！
    have hno_rep : ∀ β ∈ L z,
        ¬ ∃ b : {v : V // v ∈ M} → ℕ,
            IsPCFRep (fun i => L (w i.val) \ {β, aFun β i.val, adm.φ u}) [] b := by
      intro β hβ ⟨b, hb_mem, γ, hγ⟩
      have hwinv : ∀ x, x ∈ M.image w → ∃ v ∈ M, w v = x := fun x hx => Finset.mem_image.mp hx
      let ψ : V → ℕ := fun x =>
        if x = z then β
        else if hxM : x ∈ M then aFun β x
        else if hxW : x ∈ M.image w then b ⟨(hwinv x hxW).choose, (hwinv x hxW).choose_spec.1⟩
        else adm.φ x
      have hψz : ψ z = β := by simp [ψ]
      have hψM : ∀ v (hv : v ∈ M), ψ v = aFun β v := by
        intro v hv
        have hvz : v ≠ z := fun h => hz_not_M (h ▸ hv)
        simp [ψ, hvz, hv]
      have hψW : ∀ v (hv : v ∈ M), ψ (w v) = b ⟨v, hv⟩ := by
        intro v hv
        have hwz : w v ≠ z := G.ne_of_adj (hM_deg v hv).2.2.2.2.1
        have hwM : w v ∉ M := hw_not_M v hv
        have hwIm : w v ∈ M.image w := Finset.mem_image_of_mem w hv
        have hch : (hwinv (w v) hwIm).choose = v :=
          hM_inj (hwinv (w v) hwIm).choose_spec.1 hv (hwinv (w v) hwIm).choose_spec.2
        simp only [ψ, hwz, hwM, hwIm, ite_false, dite_false, dite_true]
        congr 1; exact Subtype.ext hch
      have hψ_out : ∀ x, x ∉ S' → ψ x = adm.φ x := by
        intro x hx; simp only [S', Finset.mem_insert, Finset.mem_union, not_or] at hx
        simp only [ψ, hx.1, hx.2.1, hx.2.2, ite_false, dite_false]
      apply adm.contradiction hm ψ hψ_out
      · intro x hx
        simp only [S', Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
        rcases hx with rfl | hxM | ⟨v, hvM, rfl⟩
        · rw [hψz]; exact hβ
        · rw [hψM x hxM]; exact (haFun_spec β x hxM).1
        · rw [hψW v hvM]; exact (Finset.mem_sdiff.mp (hb_mem ⟨v, hvM⟩)).1
      · intro x₁ x₂ h12 hor
        have hcase : ∀ p r, G.Adj p r → p ∈ S' → ψ p ≠ ψ r := by
          intro p r hpr hp
          simp only [S', Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with hpz | hpM | ⟨v, hvM, rfl⟩
          · subst p
            have hr : r ∈ M.image w := by rw [← hNz]; exact (G.mem_neighborFinset z r).mpr hpr
            rcases Finset.mem_image.mp hr with ⟨v, hvM, rfl⟩
            have hbm := hb_mem ⟨v, hvM⟩
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
            rw [hψz, hψW v hvM]; exact Ne.symm hbm.2.1
          · rcases hv_all p hpM r hpr with hr | hr
            · rw [hr, hψM p hpM, hψ_out u huS']; exact (haFun_spec β p hpM).2.1
            · have hbm := hb_mem ⟨p, hpM⟩
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
              rw [hr, hψM p hpM, hψW p hpM]; exact Ne.symm hbm.2.2.1
          · have hbm := hb_mem ⟨v, hvM⟩
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
            rcases hw_all v hvM r hpr with hr | hr
            · rw [hr, hψW v hvM, hψM v hvM]; exact hbm.2.2.1
            · rw [hr, hψW v hvM, hψz]; exact hbm.2.1
        rcases hor with h1 | h2
        · exact hcase x₁ x₂ h12 h1
        · exact (hcase x₂ x₁ h12.symm h2).symm
      · intro a haS' _ c hcS' hac
        rcases hS'_out a haS' c hcS' hac with ⟨rfl, hcM⟩
        rw [hψM c hcM]; exact (haFun_spec β c hcM).2.2.1
      · intro a haS' hiso ⟨c, hac⟩
        have hcS' : c ∈ S' := by by_contra h; exact hiso c h hac
        rcases hS'_out a haS' c hcS' hac with ⟨rfl, _⟩
        rcases hu_noniso with ⟨r, hrS', hur⟩; exact False.elim (hiso r hrS' hur)
      · intro x hxS' _
        simp only [S', Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hxS'
        rcases hxS' with hxz | hxM | ⟨v, hvM, rfl⟩
        · subst x
          simp only [List.count_nil, add_zero] at hγ
          rcases Finset.card_eq_one.mp hγ with ⟨⟨v₀, hv₀⟩, hv₀_eq⟩
          have hv₀_col : b ⟨v₀, hv₀⟩ = γ := by
            have : (⟨v₀, hv₀⟩ : {v // v ∈ M}) ∈ Finset.univ.filter (fun i => b i = γ) := by
              rw [hv₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          refine ⟨w v₀, (hM_deg v₀ hv₀).2.2.2.2.1.symm, ?_⟩
          intro r hzr hψr
          have hrIm : r ∈ M.image w := by rw [← hNz]; exact (G.mem_neighborFinset z r).mpr hzr
          rcases Finset.mem_image.mp hrIm with ⟨v, hvM, rfl⟩
          rw [hψW v hvM, hψW v₀ hv₀, hv₀_col] at hψr
          have : (⟨v, hvM⟩ : {v // v ∈ M}) ∈ Finset.univ.filter (fun i => b i = γ) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψr⟩
          rw [hv₀_eq, Finset.mem_singleton] at this
          exact congrArg w (congrArg Subtype.val this)
        · have hbm := hb_mem ⟨x, hxM⟩
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
          exact pcf_at_of_two_distinct_neighbors (hM_deg x hxM).1
            ((G.mem_neighborFinset u x).mp (hM_sub hxM)).symm (hM_deg x hxM).2.2.1
            (hM_deg x hxM).2.2.2.1.symm
            (by rw [hψ_out u huS', hψW x hxM]; exact Ne.symm hbm.2.2.2)
        · exact pcf_at_of_two_distinct_neighbors (hM_deg v hvM).2.1
            (hM_deg v hvM).2.2.1.symm (hM_deg v hvM).2.2.2.2.1 (hM_deg v hvM).2.2.2.2.2.symm
            (by rw [hψM v hvM, hψz]; exact (haFun_spec β v hvM).2.2.2)
    -- 双计数：`4 * (M.card + 1) ≤ ∑_{β ∈ L z} q_β ≤ 3 * M.card`，矛盾！
    have hlower : 4 * (L z).card ≤
        ∑ β ∈ L z, (M.filter (fun v => (L (w v) \ {β, aFun β v, adm.φ u}).card = 1)).card := by
      calc 4 * (L z).card = ∑ _β ∈ L z, 4 := by simp [mul_comm]
        _ ≤ ∑ β ∈ L z, (M.filter (fun v => (L (w v) \ {β, aFun β v, adm.φ u}).card = 1)).card := by
          apply Finset.sum_le_sum
          intro β hβ
          rcases Finset.card_pos.mp (by omega : 0 < M.card) with ⟨v₀, hv₀⟩
          have : Nonempty {v : V // v ∈ M} := ⟨⟨v₀, hv₀⟩⟩
          have hne : ∀ i : {v : V // v ∈ M},
              (L (w i.val) \ {β, aFun β i.val, adm.φ u}).Nonempty := by
            intro i; rw [← Finset.card_pos]
            have hLw : (L (w i.val)).card = 4 := by
              rw [hm.list_card (w i.val)]; simp [kappa, (hM_deg i.val i.property).2.1]
            have h1 := card_sdiff_ge (L (w i.val)) {β, aFun β i.val, adm.φ u}
            have h2 := card_triple_le β (aFun β i.val) (adm.φ u); omega
          have hq4 := (no_pcfRep_nil_bounds hne (hno_rep β hβ)).2
            (by rw [Fintype.card_coe]; exact hM4)
          have hbij :
              (Finset.univ.filter (fun i : {v // v ∈ M} =>
                (L (w i.val) \ {β, aFun β i.val, adm.φ u}).card = 1)).card =
              (M.filter (fun v => (L (w v) \ {β, aFun β v, adm.φ u}).card = 1)).card := by
            apply Finset.card_bij (fun i _ => i.val)
            · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact ⟨i.property, hi⟩
            · intro i₁ _ i₂ _ h; exact Subtype.ext h
            · intro v hv; simp only [Finset.mem_filter] at hv
              exact ⟨⟨v, hv.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩, rfl⟩
          rw [← hbij]; exact hq4
    have hupper :
        ∑ β ∈ L z, (M.filter (fun v => (L (w v) \ {β, aFun β v, adm.φ u}).card = 1)).card ≤
          3 * M.card := by
      rw [sum_filter_card_comm]
      calc ∑ v ∈ M, ((L z).filter (fun β => (L (w v) \ {β, aFun β v, adm.φ u}).card = 1)).card
          ≤ ∑ _v ∈ M, 3 := by
            apply Finset.sum_le_sum; intro v hv
            have hLw : (L (w v)).card = 4 := by
              rw [hm.list_card (w v)]; simp [kappa, (hM_deg v hv).2.1]
            exact (card_filter_sdiff_triple_eq_one_le (L z) (L (w v)) hLw
              (fun β => aFun β v) (adm.φ u)).1
        _ = 3 * M.card := by simp [mul_comm]
    omega
  · -- 情形 2：`u` 在 `G - S'` 中孤立（全图即 `Θ(3,...,3)` 恰有 `M.card ≥ 4` 条 `2`-线串！）
    push Not at hu_noniso
    have hNu : G.neighborFinset u = M := by
      ext r; simp only [SimpleGraph.mem_neighborFinset]
      constructor
      · intro hur
        have hrS' : r ∈ S' := by by_contra h; exact hu_noniso r h hur
        exact (hS'_out u huS' r hrS' hur).2
      · intro hrM; exact (G.mem_neighborFinset u r).mp (hM_sub hrM)
    have hall : insert u S' = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := u) (by simp)
      intro a ha b hab
      simp only [Finset.mem_insert] at ha ⊢
      rcases ha with rfl | haS'
      · have hbM : b ∈ M := by rw [← hNu]; exact (G.mem_neighborFinset a b).mpr hab
        exact Or.inr (by simp [S', hbM])
      · by_cases hbS' : b ∈ S'
        · exact Or.inr hbS'
        · exact Or.inl (hS'_out b hbS' a haS' hab.symm).1
    rcases Finset.card_pos.mp (by omega : 0 < M.card) with ⟨v₀, hv₀⟩
    have hLu_pos : 0 < (L u).card := by
      rw [hm.list_card u]; simp only [kappa]; split_ifs <;> omega
    rcases Finset.card_pos.mp hLu_pos with ⟨α, hαL⟩
    have hLv0 : (L v₀).card = 4 := by rw [hm.list_card v₀]; simp [kappa, (hM_deg v₀ hv₀).1]
    rcases exists_mem_sdiff_of_lt (A := L v₀) (B := {α}) (by simp [hLv0]) with ⟨c₀, hc₀, hc₀α⟩
    rw [Finset.mem_singleton] at hc₀α
    let Bz : Finset ℕ := L z \ {c₀}
    have hBz : M.card ≤ Bz.card := by
      dsimp only [Bz]
      have := card_sdiff_ge (L z) {c₀}; simp only [Finset.card_singleton] at this; omega
    have hpick : ∀ (β : ℕ) (v : V), v ∈ M → v ≠ v₀ →
        ∃ c ∈ L v, c ≠ α ∧ c ≠ c₀ ∧ c ≠ β := by
      intro β v hv _
      have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, (hM_deg v hv).1]
      rcases exists_mem_sdiff_of_lt (A := L v) (B := {α, c₀, β})
        (by have := card_triple_le α c₀ β; omega) with ⟨c, hc, hcn⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
      exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
    let aFun : ℕ → V → ℕ := fun β v =>
      if hv0 : v = v₀ then c₀
      else if hv : v ∈ M then (hpick β v hv hv0).choose
      else 0
    have haFun_v0 : ∀ β, aFun β v₀ = c₀ := fun β => by simp [aFun]
    have haFun_ne : ∀ β v (hv : v ∈ M) (hne : v ≠ v₀),
        aFun β v ∈ L v ∧ aFun β v ≠ α ∧ aFun β v ≠ c₀ ∧ aFun β v ≠ β := by
      intro β v hv hne; simp only [aFun, hne, dite_false, hv, dite_true]
      exact (hpick β v hv hne).choose_spec
    have hno_rep : ∀ β ∈ Bz,
        ¬ ∃ b : {v : V // v ∈ M} → ℕ,
            IsPCFRep (fun i => L (w i.val) \ {β, aFun β i.val, α}) [] b := by
      intro β hβ ⟨b, hb_mem, γ, hγ⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hβ
      have hwinv : ∀ x, x ∈ M.image w → ∃ v ∈ M, w v = x := fun x hx => Finset.mem_image.mp hx
      let ψ : V → ℕ := fun x =>
        if x = u then α
        else if x = z then β
        else if x ∈ M then aFun β x
        else if hxW : x ∈ M.image w then b ⟨(hwinv x hxW).choose, (hwinv x hxW).choose_spec.1⟩
        else 0
      have hψu : ψ u = α := by simp [ψ]
      have hψz : ψ z = β := by simp [ψ, huz.symm]
      have hψM : ∀ v (hv : v ∈ M), ψ v = aFun β v := by
        intro v hv
        have hvu : v ≠ u := fun h => hu_not_M (h ▸ hv)
        have hvz : v ≠ z := fun h => hz_not_M (h ▸ hv)
        simp [ψ, hvu, hvz, hv]
      have hψW : ∀ v (hv : v ∈ M), ψ (w v) = b ⟨v, hv⟩ := by
        intro v hv
        have hwu : w v ≠ u := (hM_deg v hv).2.2.2.1
        have hwz : w v ≠ z := G.ne_of_adj (hM_deg v hv).2.2.2.2.1
        have hwM : w v ∉ M := hw_not_M v hv
        have hwIm : w v ∈ M.image w := Finset.mem_image_of_mem w hv
        have hch : (hwinv (w v) hwIm).choose = v :=
          hM_inj (hwinv (w v) hwIm).choose_spec.1 hv (hwinv (w v) hwIm).choose_spec.2
        simp only [ψ, hwu, hwz, hwM, hwIm, ite_false, dite_true]
        congr 1; exact Subtype.ext hch
      have hmem_all : ∀ x : V, x = u ∨ x = z ∨ x ∈ M ∨ x ∈ M.image w := by
        intro x
        have hx : x ∈ insert u S' := by rw [hall]; exact Finset.mem_univ x
        simp only [S', Finset.mem_insert, Finset.mem_union] at hx
        tauto
      apply hm.not_colorable
      refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
      · intro x₁ x₂ h12
        rcases hmem_all x₁ with hx1u | hx1z | hx1M | hx1W
        · subst x₁
          have hx2M : x₂ ∈ M := by rw [← hNu]; exact (G.mem_neighborFinset u x₂).mpr h12
          rw [hψu, hψM x₂ hx2M]
          by_cases h0 : x₂ = v₀
          · rw [h0, haFun_v0]; exact Ne.symm hc₀α
          · exact (haFun_ne β x₂ hx2M h0).2.1.symm
        · subst x₁
          have hx2W : x₂ ∈ M.image w := by rw [← hNz]; exact (G.mem_neighborFinset z x₂).mpr h12
          rcases Finset.mem_image.mp hx2W with ⟨v, hvM, rfl⟩
          have hbm := hb_mem ⟨v, hvM⟩
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
          rw [hψz, hψW v hvM]; exact Ne.symm hbm.2.1
        · rcases hv_all x₁ hx1M x₂ h12 with hx2 | hx2
          · rw [hx2, hψM x₁ hx1M, hψu]
            by_cases h0 : x₁ = v₀
            · rw [h0, haFun_v0]; exact hc₀α
            · exact (haFun_ne β x₁ hx1M h0).2.1
          · have hbm := hb_mem ⟨x₁, hx1M⟩
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
            rw [hx2, hψM x₁ hx1M, hψW x₁ hx1M]; exact Ne.symm hbm.2.2.1
        · rcases Finset.mem_image.mp hx1W with ⟨v, hvM, rfl⟩
          have hbm := hb_mem ⟨v, hvM⟩
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
          rcases hw_all v hvM x₂ h12 with hx2 | hx2
          · rw [hx2, hψW v hvM, hψM v hvM]; exact hbm.2.2.1
          · rw [hx2, hψW v hvM, hψz]; exact hbm.2.1
      · intro x _
        rcases hmem_all x with hxu | hxz | hxM | hxW
        · subst x
          refine ⟨v₀, (G.mem_neighborFinset u v₀).mp (hM_sub hv₀), ?_⟩
          intro r hur hψr
          have hrM : r ∈ M := by rw [← hNu]; exact (G.mem_neighborFinset u r).mpr hur
          rw [hψM r hrM, hψM v₀ hv₀, haFun_v0] at hψr
          by_contra hne
          exact (haFun_ne β r hrM hne).2.2.1 hψr
        · subst x
          simp only [List.count_nil, add_zero] at hγ
          rcases Finset.card_eq_one.mp hγ with ⟨⟨v₁, hv₁⟩, hv₁_eq⟩
          have hv₁_col : b ⟨v₁, hv₁⟩ = γ := by
            have : (⟨v₁, hv₁⟩ : {v // v ∈ M}) ∈ Finset.univ.filter (fun i => b i = γ) := by
              rw [hv₁_eq]; simp
            exact (Finset.mem_filter.mp this).2
          refine ⟨w v₁, (hM_deg v₁ hv₁).2.2.2.2.1.symm, ?_⟩
          intro r hzr hψr
          have hrIm : r ∈ M.image w := by rw [← hNz]; exact (G.mem_neighborFinset z r).mpr hzr
          rcases Finset.mem_image.mp hrIm with ⟨v, hvM, rfl⟩
          rw [hψW v hvM, hψW v₁ hv₁, hv₁_col] at hψr
          have : (⟨v, hvM⟩ : {v // v ∈ M}) ∈ Finset.univ.filter (fun i => b i = γ) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψr⟩
          rw [hv₁_eq, Finset.mem_singleton] at this
          exact congrArg w (congrArg Subtype.val this)
        · have hbm := hb_mem ⟨x, hxM⟩
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hbm
          exact pcf_at_of_two_distinct_neighbors (hM_deg x hxM).1
            ((G.mem_neighborFinset u x).mp (hM_sub hxM)).symm (hM_deg x hxM).2.2.1
            (hM_deg x hxM).2.2.2.1.symm
            (by rw [hψu, hψW x hxM]; exact Ne.symm hbm.2.2.2)
        · rcases Finset.mem_image.mp hxW with ⟨v, hvM, rfl⟩
          exact pcf_at_of_two_distinct_neighbors (hM_deg v hvM).2.1
            (hM_deg v hvM).2.2.1.symm (hM_deg v hvM).2.2.2.2.1 (hM_deg v hvM).2.2.2.2.2.symm
            (by
              rw [hψM v hvM, hψz]
              by_cases h0 : v = v₀
              · rw [h0, haFun_v0]; exact Ne.symm hβ.2
              · exact (haFun_ne β v hvM h0).2.2.2)
      · intro x
        rcases hmem_all x with rfl | rfl | hxM | hxW
        · rw [hψu]; exact hαL
        · rw [hψz]; exact hβ.1
        · rw [hψM x hxM]
          by_cases h0 : x = v₀
          · rw [h0, haFun_v0]; exact hc₀
          · exact (haFun_ne β x hxM h0).1
        · rcases Finset.mem_image.mp hxW with ⟨v, hvM, rfl⟩
          rw [hψW v hvM]; exact (Finset.mem_sdiff.mp (hb_mem ⟨v, hvM⟩)).1
    -- 双计数：`4 * M.card ≤ 4 * |Bz| ≤ ∑_{β ∈ Bz} q_β ≤ 3 * M.card`，矛盾！
    have hlower : 4 * Bz.card ≤
        ∑ β ∈ Bz, (M.filter (fun v => (L (w v) \ {β, aFun β v, α}).card = 1)).card := by
      calc 4 * Bz.card = ∑ _β ∈ Bz, 4 := by simp [mul_comm]
        _ ≤ ∑ β ∈ Bz, (M.filter (fun v => (L (w v) \ {β, aFun β v, α}).card = 1)).card := by
          apply Finset.sum_le_sum
          intro β hβ
          have : Nonempty {v : V // v ∈ M} := ⟨⟨v₀, hv₀⟩⟩
          have hne : ∀ i : {v : V // v ∈ M},
              (L (w i.val) \ {β, aFun β i.val, α}).Nonempty := by
            intro i; rw [← Finset.card_pos]
            have hLw : (L (w i.val)).card = 4 := by
              rw [hm.list_card (w i.val)]; simp [kappa, (hM_deg i.val i.property).2.1]
            have h1 := card_sdiff_ge (L (w i.val)) {β, aFun β i.val, α}
            have h2 := card_triple_le β (aFun β i.val) α; omega
          have hq4 := (no_pcfRep_nil_bounds hne (hno_rep β hβ)).2
            (by rw [Fintype.card_coe]; exact hM4)
          have hbij :
              (Finset.univ.filter (fun i : {v // v ∈ M} =>
                (L (w i.val) \ {β, aFun β i.val, α}).card = 1)).card =
              (M.filter (fun v => (L (w v) \ {β, aFun β v, α}).card = 1)).card := by
            apply Finset.card_bij (fun i _ => i.val)
            · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact ⟨i.property, hi⟩
            · intro i₁ _ i₂ _ h; exact Subtype.ext h
            · intro v hv; simp only [Finset.mem_filter] at hv
              exact ⟨⟨v, hv.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩, rfl⟩
          rw [← hbij]; exact hq4
    have hupper :
        ∑ β ∈ Bz, (M.filter (fun v => (L (w v) \ {β, aFun β v, α}).card = 1)).card ≤
          3 * M.card := by
      rw [sum_filter_card_comm]
      calc ∑ v ∈ M, (Bz.filter (fun β => (L (w v) \ {β, aFun β v, α}).card = 1)).card
          ≤ ∑ _v ∈ M, 3 := by
            apply Finset.sum_le_sum; intro v hv
            have hLw : (L (w v)).card = 4 := by
              rw [hm.list_card (w v)]; simp [kappa, (hM_deg v hv).2.1]
            exact (card_filter_sdiff_triple_eq_one_le Bz (L (w v)) hLw (fun β => aFun β v) α).1
        _ = 3 * M.card := by simp [mul_comm]
    omega

/-- Lemma 3.5（对任意 `mad(G) < 5/2` 成立！）：极小反例中，任意 `3⁺`-度点 `u` 满足
`|leafNbrs G u| + |longThreadNbrs G u| + 2 ≤ G.degree u`。 -/
lemma leaf_plus_long_thread_le {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u : V} (hdu3 : 3 ≤ G.degree u) :
    (leafNbrs G u).card + (longThreadNbrs G u).card + 2 ≤ G.degree u := by
  classical
  by_cases hdu_eq3 : G.degree u = 3
  · -- `d(u) = 3`：无叶邻点且无 `2⁺`-线串！
    have hL0 : leafNbrs G u = ∅ := leafNbrs_eq_empty_of_deg_le_three hm (by omega)
    have hT0 : longThreadNbrs G u = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset] at hv
      rcases hv.2 with ⟨huv, hdv, w, hvw, _, hdw⟩
      exact no_three_vertex_two_thread hm hdu_eq3 hdv hdw huv hvw
    rw [hL0, hT0]; simp; omega
  have hdu4 : 4 ≤ G.degree u := by omega
  by_contra hgt; push Not at hgt
  -- `leafNbrs G u` 与 `longThreadNbrs G u` 不交且均含于 `G.neighborFinset u`
  have hdisj : Disjoint (leafNbrs G u) (longThreadNbrs G u) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [mem_leafNbrs] at h1
    simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter] at h2
    omega
  have hun_sub : leafNbrs G u ∪ longThreadNbrs G u ⊆ G.neighborFinset u := by
    intro v hv; simp only [Finset.mem_union] at hv
    rcases hv with h | h
    · exact (G.mem_neighborFinset u v).mpr (mem_leafNbrs.mp h).1
    · simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter] at h; exact h.1.1
  have hun_card : G.degree u - 1 ≤ (leafNbrs G u ∪ longThreadNbrs G u).card := by
    rw [Finset.card_union_of_disjoint hdisj]; omega
  -- 任取大小为 `d(u) - 1` 的子集 `J ⊆ leafNbrs G u ∪ longThreadNbrs G u`
  rcases Finset.exists_subset_card_eq hun_card with ⟨J, hJsub, hJcard⟩
  have hJ_subN : J ⊆ G.neighborFinset u := Finset.Subset.trans hJsub hun_sub
  have hdiff1 : (G.neighborFinset u \ J).card = 1 := by
    rw [Finset.card_sdiff_of_subset hJ_subN, SimpleGraph.card_neighborFinset_eq_degree, hJcard]
    omega
  rcases Finset.card_eq_one.mp hdiff1 with ⟨x, hx_eq⟩
  have hx_mem : x ∈ G.neighborFinset u \ J := by rw [hx_eq]; simp
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hx_mem
  rcases hx_mem with ⟨hux, hxnotJ⟩
  have hN_part : G.neighborFinset u = insert x J := by
    ext r; constructor
    · intro hr; by_cases hrJ : r ∈ J
      · exact Finset.mem_insert_of_mem hrJ
      · have : r ∈ G.neighborFinset u \ J := Finset.mem_sdiff.mpr ⟨hr, hrJ⟩
        rw [hx_eq, Finset.mem_singleton] at this; rw [this]; exact Finset.mem_insert_self x J
    · intro hr; simp only [Finset.mem_insert] at hr
      rcases hr with hrx | hrJ
      · rw [hrx]; exact (G.mem_neighborFinset u x).mpr hux
      · exact hJ_subN hrJ
  let I₁ : Finset V := J ∩ leafNbrs G u
  let Ith : Finset V := J ∩ longThreadNbrs G u
  have hI_disj : Disjoint I₁ Ith :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj
  have hI_un : I₁ ∪ Ith = J := by
    ext v; simp only [I₁, Ith, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hv; rcases Finset.mem_union.mp (hJsub hv) with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
  -- 对每个 `v ∈ Ith`，取出其唯一 `2`-度后继 `w(v)` 及 `w(v)` 的唯一后继 `z(v)`
  have hwz_ex : ∀ v : V, v ∈ Ith →
      ∃ w z : V, G.degree v = 2 ∧ G.degree w = 2 ∧ G.Adj v w ∧ w ≠ u ∧
        G.Adj w z ∧ z ≠ v := by
    intro v hv
    have hvth : v ∈ longThreadNbrs G u := (Finset.mem_inter.mp hv).2
    simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset] at hvth
    rcases hvth.2 with ⟨_, hdv, w, hvw, hwu, hdw⟩
    rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨z, hwz, hzv, _⟩
    exact ⟨w, z, hdv, hdw, hvw, hwu, hwz, hzv⟩
  let w : V → V := fun v => if hv : v ∈ Ith then (hwz_ex v hv).choose else u
  let z : V → V := fun v => if hv : v ∈ Ith then (hwz_ex v hv).choose_spec.choose else u
  have hwz_spec : ∀ v (hv : v ∈ Ith),
      G.degree v = 2 ∧ G.degree (w v) = 2 ∧ G.Adj v (w v) ∧ w v ≠ u ∧
        G.Adj (w v) (z v) ∧ z v ≠ v := by
    intro v hv
    have hwv : w v = (hwz_ex v hv).choose := by simp only [w, hv, dite_true]
    have hzv : z v = (hwz_ex v hv).choose_spec.choose := by simp only [z, hv, dite_true]
    rw [hwv, hzv]
    exact (hwz_ex v hv).choose_spec.choose_spec
  -- 基本不交与单射性质
  have hw_inj : Set.InjOn w Ith := by
    intro v₁ hv₁ v₂ hv₂ heq
    by_contra hne
    rcases hwz_spec v₁ hv₁ with ⟨hd1, hdw1, h1w, _, _, _⟩
    rcases hwz_spec v₂ hv₂ with ⟨hd2, _, h2w, _, _, _⟩
    have hu1 : G.Adj u v₁ := (G.mem_neighborFinset u v₁).mp (hJ_subN (Finset.mem_inter.mp hv₁).1)
    have hu2 : G.Adj u v₂ := (G.mem_neighborFinset u v₂).mp (hJ_subN (Finset.mem_inter.mp hv₂).1)
    exact no_three_thread_same_anchor hm hdu3 hd1 hdw1 hd2 hu1 h1w (heq ▸ h2w.symm) hu2.symm hne
  have hw_not_N : ∀ v ∈ Ith, w v ∉ G.neighborFinset u := by
    intro v hv hwN
    rcases hwz_spec v hv with ⟨hdv, hdw, hvw, _, _, _⟩
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hJ_subN (Finset.mem_inter.mp hv).1)
    have huw : G.Adj u (w v) := (G.mem_neighborFinset u (w v)).mp hwN
    exact no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw huw.symm
  have hz_not_u : ∀ v ∈ Ith, z v ≠ u := by
    intro v hv heq
    rcases hwz_spec v hv with ⟨hdv, hdw, hvw, _, hwz, _⟩
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hJ_subN (Finset.mem_inter.mp hv).1)
    exact no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw (heq ▸ hwz)
  have hz_not_J : ∀ v ∈ Ith, z v ∉ J := by
    intro v hv hzJ
    rcases hwz_spec v hv with ⟨hdv, hdw, hvw, hwu, hwz, hzv⟩
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hJ_subN (Finset.mem_inter.mp hv).1)
    rw [← hI_un, Finset.mem_union] at hzJ
    rcases hzJ with hzI1 | hzIth
    · have hzL := mem_leafNbrs.mp (Finset.mem_inter.mp hzI1).2
      rcases exists_unique_neighbor_of_deg_one hzL.2 with ⟨r, _, huniq⟩
      exact hwu ((huniq (w v) hwz.symm).trans (huniq u hzL.1.symm).symm)
    · have hdz2 := (hwz_spec (z v) hzIth).1
      have huz : G.Adj u (z v) :=
        (G.mem_neighborFinset u (z v)).mp (hJ_subN (Finset.mem_inter.mp hzIth).1)
      exact no_three_thread_same_anchor hm hdu3 hdv hdw hdz2 huv hvw hwz huz.symm hzv.symm
  have hz_not_W : ∀ v ∈ Ith, z v ∉ Ith.image w := by
    intro v hv hzW
    rcases Finset.mem_image.mp hzW with ⟨v', hv', hEq⟩
    rcases hwz_spec v hv with ⟨hdv, hdw, hvw, _, hwz, hzv⟩
    rcases hwz_spec v' hv' with ⟨hdv', hdw', hv'w', _, _, _⟩
    have hvv' : v ≠ v' := by
      intro h; subst h; exact G.ne_of_adj hwz hEq
    have hwvv' : w v ≠ v' := fun h => hw_not_N v hv (h ▸ hJ_subN (Finset.mem_inter.mp hv').1)
    have hvwv' : v ≠ w v' := fun h => hw_not_N v' hv' (h ▸ hJ_subN (Finset.mem_inter.mp hv).1)
    exact no_four_path_of_deg_two hm hdv hdw hdw' hdv' hvw (hEq ▸ hwz) hv'w'.symm hvwv' hvv' hwvv'
  let S : Finset V := insert u (J ∪ Ith.image w)
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hz_not_S : ∀ v ∈ Ith, z v ∉ S := by
    intro v hv hzS
    simp only [S, Finset.mem_insert, Finset.mem_union] at hzS
    rcases hzS with h | h | h
    · exact hz_not_u v hv h
    · exact hz_not_J v hv h
    · exact hz_not_W v hv h
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨(G.ne_of_adj hux).symm, hxnotJ, fun hxW => ?_⟩
    rcases Finset.mem_image.mp hxW with ⟨v, hv, rfl⟩
    exact hw_not_N v hv ((G.mem_neighborFinset u (w v)).mpr hux)
  have hv_all : ∀ v ∈ Ith, ∀ r, G.Adj v r → r = u ∨ r = w v := by
    intro v hv r hvr
    rcases hwz_spec v hv with ⟨hdv, _, hvw, hwu, _, _⟩
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hJ_subN (Finset.mem_inter.mp hv).1)
    have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : r ∈ ({u, w v} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v r).mpr hvr
    simpa using this
  have hw_all : ∀ v ∈ Ith, ∀ r, G.Adj (w v) r → r = v ∨ r = z v := by
    intro v hv r hwr
    rcases hwz_spec v hv with ⟨_, hdw, hvw, _, hwz, hzv⟩
    have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
    have : r ∈ ({v, z v} : Finset V) := by rw [← hNw]; exact (G.mem_neighborFinset (w v) r).mpr hwr
    simpa using this
  -- `S` 与 `G - S` 的所有跨边只能是 `(u, x)` 或 `(w v, z v)`！
  have hS_out : ∀ a, a ∉ S → ∀ b ∈ S, G.Adj a b →
      (b = u ∧ a = x) ∨ (∃ v ∈ Ith, b = w v ∧ a = z v) := by
    intro a haS b hbS hab
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hbS
    rcases hbS with rfl | hbJ | ⟨v, hv, rfl⟩
    · have haN : a ∈ G.neighborFinset b := (G.mem_neighborFinset b a).mpr hab.symm
      rw [hN_part, Finset.mem_insert] at haN
      rcases haN with rfl | haJ
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (haS (by simp [S, haJ]))
    · rw [← hI_un, Finset.mem_union] at hbJ
      rcases hbJ with hbI1 | hbIth
      · have hbL := mem_leafNbrs.mp (Finset.mem_inter.mp hbI1).2
        rcases exists_unique_neighbor_of_deg_one hbL.2 with ⟨r, _, huniq⟩
        have hau : a = u := (huniq a hab.symm).trans (huniq u hbL.1.symm).symm
        exact False.elim (haS (hau ▸ huS))
      · rcases hv_all b hbIth a hab.symm with rfl | rfl
        · exact False.elim (haS huS)
        · exact False.elim (haS (by simp [S, Finset.mem_image_of_mem w hbIth]))
    · rcases hw_all v hv a hab.symm with rfl | rfl
      · exact False.elim (haS (by simp [S, (Finset.mem_inter.mp hv).1]))
      · exact Or.inr ⟨v, hv, rfl, rfl⟩
  -- 关键验证：每个 `z v`（`v ∈ Ith`）在 `G - S` 中皆非孤立！
  have hz_noniso : ∀ v ∈ Ith, ∃ r, r ∉ S ∧ G.Adj (z v) r := by
    intro v hv
    rcases hwz_spec v hv with ⟨hdv, hdw, hvw, hwu, hwz, hzv⟩
    have hdz2 : 2 ≤ G.degree (z v) := by
      have h1 := degree_ge_one hm (z v)
      by_contra hlt; push Not at hlt
      have := leaf_neighbor_deg_ge_four hm (by omega : G.degree (z v) = 1) hwz.symm; omega
    by_cases hdz_eq2 : G.degree (z v) = 2
    · rcases exists_other_neighbor_of_deg_two hdz_eq2 hwz.symm with ⟨r, hzr, hrw, _⟩
      refine ⟨r, ?_, hzr⟩
      intro hrS
      rcases hS_out (z v) (hz_not_S v hv) r hrS hzr with ⟨hru, _⟩ | ⟨v', hv', rfl, hzEq⟩
      · subst r
        have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (hJ_subN (Finset.mem_inter.mp hv).1)
        exact no_three_thread_same_anchor hm hdu3 hdv hdw hdz_eq2 huv hvw hwz hzr hzv.symm
      · have hvv' : v' ≠ v := fun h => hrw (by rw [h])
        have hwv'v : w v' ≠ v := fun h => hw_not_N v' hv' (h ▸ hJ_subN (Finset.mem_inter.mp hv).1)
        exact no_four_path_of_deg_two hm hdv hdw hdz_eq2 (hwz_spec v' hv').2.1
          hvw hwz hzr hzv.symm hwv'v.symm hrw.symm
    · -- `3 ≤ G.degree (z v)`，故由 `no_three_vertex_two_thread` 得 `4 ≤ G.degree (z v)`！
      have hdz4 : 4 ≤ G.degree (z v) := by
        by_contra hlt; push Not at hlt
        exact no_three_vertex_two_thread hm (by omega) hdw hdv hwz.symm hvw.symm
      by_contra hiso; push Not at hiso
      let M : Finset V := Ith.filter (fun v' => z v' = z v)
      have hM_sub : M ⊆ G.neighborFinset u :=
        Finset.Subset.trans (Finset.filter_subset _ Ith)
          (Finset.Subset.trans Finset.inter_subset_left hJ_subN)
      have hM_inj : Set.InjOn w M := hw_inj.mono (Finset.filter_subset _ Ith)
      -- 断言 `G.neighborFinset (z v)` 只含 `M.image w`（及可能含 `u`）
      have hNz_sub : G.neighborFinset (z v) ⊆
          (if G.Adj u (z v) then insert u (M.image w) else M.image w) := by
        intro r hr
        rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hiso r h hr
        rcases hS_out (z v) (hz_not_S v hv) r hrS hr with ⟨rfl, _⟩ | ⟨v', hv', rfl, hzEq⟩
        · simp [hr.symm]
        · have hv'M : v' ∈ M := Finset.mem_filter.mpr ⟨hv', hzEq.symm⟩
          have hm : w v' ∈ M.image w := Finset.mem_image_of_mem w hv'M
          split_ifs <;> simp [hm]
      by_cases huz : G.Adj u (z v)
      · -- `ε = 1`：用 `mad_core_sum_lt` 配合 `2 * p ≤ 5 * q` 得 `6m + 2 < 5m + 5 → m ≤ 2 → d(z) ≤ 3` 矛盾！
        have hM_card_ge3 : 3 ≤ M.card := by
          have h1 : G.degree (z v) ≤ (insert u (M.image w)).card := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            exact Finset.card_le_card (by simpa [huz] using hNz_sub)
          have h2 : (insert u (M.image w)).card ≤ M.card + 1 := by
            calc (insert u (M.image w)).card ≤ (M.image w).card + 1 := Finset.card_insert_le _ _
              _ = M.card + 1 := by rw [Finset.card_image_of_injOn hM_inj]
          omega
        let T : Finset V := insert u (insert (z v) (M ∪ M.image w))
        have hM_disj_W : Disjoint M (M.image w) := by
          rw [Finset.disjoint_left]; intro a ha1 ha2
          rcases Finset.mem_image.mp ha2 with ⟨v', hv', rfl⟩
          exact hw_not_N v' (Finset.mem_filter.mp hv').1 (hM_sub ha1)
        have hzv_not_MW : z v ∉ M ∪ M.image w := by
          intro h; rcases Finset.mem_union.mp h with h1 | h2
          · exact hz_not_J v hv (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).1
          · exact hz_not_W v hv (Finset.image_subset_image (Finset.filter_subset _ Ith) h2)
        have hu_not_zMW : u ∉ insert (z v) (M ∪ M.image w) := by
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
            not_and]
          refine ⟨(hz_not_u v hv).symm, fun huM =>
            G.ne_of_adj ((G.mem_neighborFinset u u).mp (hM_sub huM)) rfl,
            fun v' hv' h => (hwz_spec v' (Finset.mem_filter.mp hv').1).2.2.2.1 h⟩
        have hT_card : T.card = 2 * M.card + 2 := by
          dsimp only [T]
          rw [Finset.card_insert_of_notMem hu_not_zMW, Finset.card_insert_of_notMem hzv_not_MW,
              Finset.card_union_of_disjoint hM_disj_W, Finset.card_image_of_injOn hM_inj]
          omega
        have hT_sum : 6 * M.card + 2 ≤ ∑ t ∈ T, (G.neighborFinset t ∩ T).card := by
          have hu_deg : M.card + 1 ≤ (G.neighborFinset u ∩ T).card := by
            have hsub : insert (z v) M ⊆ G.neighborFinset u ∩ T := by
              intro r hr; simp only [Finset.mem_insert] at hr
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
              rcases hr with rfl | hrM
              · exact ⟨huz, by simp [T]⟩
              · exact ⟨(G.mem_neighborFinset u r).mp (hM_sub hrM), by simp [T, hrM]⟩
            calc M.card + 1 = (insert (z v) M).card := by
                  rw [Finset.card_insert_of_notMem
                    (fun h => hzv_not_MW (Finset.mem_union_left _ h))]
              _ ≤ (G.neighborFinset u ∩ T).card := Finset.card_le_card hsub
          have hz_deg : M.card + 1 ≤ (G.neighborFinset (z v) ∩ T).card := by
            have hsub : insert u (M.image w) ⊆ G.neighborFinset (z v) ∩ T := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_image] at hr
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
              rcases hr with rfl | ⟨v', hv', rfl⟩
              · exact ⟨huz.symm, by simp [T]⟩
              · have hv'Ith := (Finset.mem_filter.mp hv').1
                have hzEq := (Finset.mem_filter.mp hv').2
                exact ⟨(hzEq ▸ (hwz_spec v' hv'Ith).2.2.2.2.1).symm,
                  by simp [T, Finset.mem_image_of_mem w hv']⟩
            have hu_not_im : u ∉ M.image w := fun h => hu_not_zMW (by simp [h])
            calc M.card + 1 = (insert u (M.image w)).card := by
                  rw [Finset.card_insert_of_notMem hu_not_im, Finset.card_image_of_injOn hM_inj]
              _ ≤ (G.neighborFinset (z v) ∩ T).card := Finset.card_le_card hsub
          have hM_deg : ∀ v' ∈ M, 2 ≤ (G.neighborFinset v' ∩ T).card := by
            intro v' hv'
            have hv'Ith := (Finset.mem_filter.mp hv').1
            have hsub : ({u, w v'} : Finset V) ⊆ G.neighborFinset v' ∩ T := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
              rcases hr with hru | hrw
              · rw [hru]; exact ⟨((G.mem_neighborFinset u v').mp (hM_sub hv')).symm, by simp [T]⟩
              · rw [hrw]
                exact ⟨(hwz_spec v' hv'Ith).2.2.1, by simp [T, Finset.mem_image_of_mem w hv']⟩
            calc 2 = ({u, w v'} : Finset V).card :=
                  (Finset.card_pair (hwz_spec v' hv'Ith).2.2.2.1.symm).symm
              _ ≤ (G.neighborFinset v' ∩ T).card := Finset.card_le_card hsub
          have hW_deg : ∀ r ∈ M.image w, 2 ≤ (G.neighborFinset r ∩ T).card := by
            intro r hr
            rcases Finset.mem_image.mp hr with ⟨v', hv', rfl⟩
            have hv'Ith := (Finset.mem_filter.mp hv').1
            have hzEq := (Finset.mem_filter.mp hv').2
            have hsub : ({v', z v} : Finset V) ⊆ G.neighborFinset (w v') ∩ T := by
              intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
              rcases ht with htv' | htzv
              · rw [htv']; exact ⟨(hwz_spec v' hv'Ith).2.2.1.symm, by simp [T, hv']⟩
              · rw [htzv]; exact ⟨hzEq ▸ (hwz_spec v' hv'Ith).2.2.2.2.1, by simp [T]⟩
            calc 2 = ({v', z v} : Finset V).card :=
                  (Finset.card_pair (hzEq ▸ (hwz_spec v' hv'Ith).2.2.2.2.2).symm).symm
              _ ≤ (G.neighborFinset (w v') ∩ T).card := Finset.card_le_card hsub
          have hsplit : ∑ t ∈ T, (G.neighborFinset t ∩ T).card =
              (G.neighborFinset u ∩ T).card + (G.neighborFinset (z v) ∩ T).card +
              ∑ t ∈ M, (G.neighborFinset t ∩ T).card +
              ∑ t ∈ M.image w, (G.neighborFinset t ∩ T).card := by
            have h1 : ∑ t ∈ T, (G.neighborFinset t ∩ T).card =
                ∑ t ∈ insert u (insert (z v) (M ∪ M.image w)), (G.neighborFinset t ∩ T).card := rfl
            rw [h1, Finset.sum_insert hu_not_zMW, Finset.sum_insert hzv_not_MW,
                Finset.sum_union hM_disj_W]
            omega
          have hsumM : 2 * M.card ≤ ∑ t ∈ M, (G.neighborFinset t ∩ T).card := by
            calc 2 * M.card = ∑ _t ∈ M, 2 := by simp [mul_comm]
              _ ≤ ∑ t ∈ M, (G.neighborFinset t ∩ T).card := Finset.sum_le_sum hM_deg
          have hsumW : 2 * M.card ≤ ∑ t ∈ M.image w, (G.neighborFinset t ∩ T).card := by
            calc 2 * M.card = ∑ _t ∈ M.image w, 2 := by
                  simp [Finset.card_image_of_injOn hM_inj, mul_comm]
              _ ≤ ∑ t ∈ M.image w, (G.neighborFinset t ∩ T).card := Finset.sum_le_sum hW_deg
          omega
        have hmad := mad_core_sum_lt hm.mad (S := T) ⟨u, by simp [T]⟩
        rw [hT_card] at hmad
        have hqmul : q * (6 * M.card + 2) ≤ q * ∑ t ∈ T, (G.neighborFinset t ∩ T).card :=
          Nat.mul_le_mul_left q hT_sum
        have hlt_pq : q * (6 * M.card + 2) < 5 * q * (M.card + 1) := by
          calc q * (6 * M.card + 2) < p * (2 * M.card + 2) := lt_of_le_of_lt hqmul hmad
            _ = (2 * p) * (M.card + 1) := by ring
            _ ≤ (5 * q) * (M.card + 1) := Nat.mul_le_mul_right _ hpq
        have hlt_q : q * (6 * M.card + 2) < q * (5 * M.card + 5) := by
          have : 5 * q * (M.card + 1) = q * (5 * M.card + 5) := by ring
          omega
        have := Nat.lt_of_mul_lt_mul_left hlt_q
        omega
      · -- `ε = 0`：调用无 `mad` 依赖的 `no_isolated_two_thread_hub` 直接矛盾！
        have hNz_eq : G.neighborFinset (z v) = M.image w := by
          apply Finset.Subset.antisymm (by simpa [huz] using hNz_sub)
          intro r hr; rcases Finset.mem_image.mp hr with ⟨v', hv', rfl⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ((Finset.mem_filter.mp hv').2 ▸
            (hwz_spec v' (Finset.mem_filter.mp hv').1).2.2.2.2.1).symm
        exact no_isolated_two_thread_hub hm hdz4 huz (hz_not_u v hv).symm hM_sub
          (fun v' hv' => by
            have hv'Ith := (Finset.mem_filter.mp hv').1
            have hzEq := (Finset.mem_filter.mp hv').2
            rcases hwz_spec v' hv'Ith with ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨h1, h2, h3, h4, hzEq ▸ h5, hzEq ▸ h6⟩)
          hM_inj hNz_eq
  -- 现在正式开始主双计数：取 `G - S` 的容许染色 `adm`！
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  let β := adm.φ x
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  let C : Finset ℕ :=
    if ∃ r, r ∉ S ∧ G.Adj x r then L u \ {β, adm.φs x} else L u \ {β}
  have hC : G.degree u - 1 ≤ C.card := by
    dsimp only [C]
    split_ifs
    · have := card_sdiff_ge (L u) {β, adm.φs x}
      have := Finset.card_le_two (a := β) (b := adm.φs x); omega
    · have := card_sdiff_ge (L u) {β}; simp only [Finset.card_singleton] at this; omega
  have hβ_not_C : β ∉ C := by
    dsimp only [C]; split_ifs <;> simp
  -- 对每个 `α ∈ C` 与 `v ∈ Ith`，选取 `cFun α v ∈ L (w v) \ {α, adm.φ (z v), adm.φs (z v)}`
  have hc_ex : ∀ (α : ℕ) (v : V), v ∈ Ith →
      ∃ c ∈ L (w v), c ≠ α ∧ c ≠ adm.φ (z v) ∧ c ≠ adm.φs (z v) := by
    intro α v hv
    have hLw : (L (w v)).card = 4 := by rw [hm.list_card (w v)]; simp [kappa, (hwz_spec v hv).2.1]
    rcases exists_mem_sdiff_of_lt (A := L (w v)) (B := {α, adm.φ (z v), adm.φs (z v)})
      (by have := card_triple_le α (adm.φ (z v)) (adm.φs (z v)); omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → V → ℕ := fun α v => if hv : v ∈ Ith then (hc_ex α v hv).choose else 0
  have hcFun_spec : ∀ α v (hv : v ∈ Ith),
      cFun α v ∈ L (w v) ∧ cFun α v ≠ α ∧ cFun α v ≠ adm.φ (z v) ∧ cFun α v ≠ adm.φs (z v) := by
    intro α v hv; simp only [cFun, hv, dite_true]; exact (hc_ex α v hv).choose_spec
  let A : ℕ → V → Finset ℕ := fun α v =>
    if v ∈ Ith then L v \ {α, cFun α v, adm.φ (z v)} else L v \ {α}
  have hA_ne : ∀ α v (hv : v ∈ J), (A α v).Nonempty := by
    intro α v hv; rw [← Finset.card_pos]
    dsimp only [A]; split_ifs with hvth
    · have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, (hwz_spec v hvth).1]
      have h1 := card_sdiff_ge (L v) {α, cFun α v, adm.φ (z v)}
      have h2 := card_triple_le α (cFun α v) (adm.φ (z v)); omega
    · have hvI1 : v ∈ I₁ := by
        rw [← hI_un, Finset.mem_union] at hv; exact hv.resolve_right hvth
      have hLv : (L v).card = 2 := by
        rw [hm.list_card v]; simp [kappa, (mem_leafNbrs.mp (Finset.mem_inter.mp hvI1).2).2]
      have h1 := card_sdiff_ge (L v) {α}; simp only [Finset.card_singleton] at h1; omega
  -- 断言：对每个 `α ∈ C`，`A α` 在 `J` 上无 `B = [β]` 的 `PCF`-代表系统！
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ a : {v : V // v ∈ J} → ℕ, IsPCFRep (fun i => A α i.val) [β] a := by
    intro α hα ⟨a, ha_mem, γ, hγ⟩
    have hαL : α ∈ L u := by
      dsimp only [C] at hα; split_ifs at hα <;> exact (Finset.mem_sdiff.mp hα).1
    have hαβ : α ≠ β := fun h => hβ_not_C (h ▸ hα)
    have hα_φsx : (∃ r, r ∉ S ∧ G.Adj x r) → α ≠ adm.φs x := by
      intro hnon; dsimp only [C] at hα; simp only [hnon, ite_true] at hα
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
      exact hα.2.2
    have hwinv : ∀ r, r ∈ Ith.image w → ∃ v ∈ Ith, w v = r := fun r hr => Finset.mem_image.mp hr
    let ψ : V → ℕ := fun r =>
      if r = u then α
      else if hrJ : r ∈ J then a ⟨r, hrJ⟩
      else if hrW : r ∈ Ith.image w then cFun α (hwinv r hrW).choose
      else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψJ : ∀ v (hv : v ∈ J), ψ v = a ⟨v, hv⟩ := by
      intro v hv
      have hvu : v ≠ u := (G.ne_of_adj ((G.mem_neighborFinset u v).mp (hJ_subN hv))).symm
      simp only [ψ, hvu, ite_false, hv, dite_true]
    have hψW : ∀ v (hv : v ∈ Ith), ψ (w v) = cFun α v := by
      intro v hv
      have hwu : w v ≠ u := (hwz_spec v hv).2.2.2.1
      have hwJ : w v ∉ J := fun h => hw_not_N v hv (hJ_subN h)
      have hwIm : w v ∈ Ith.image w := Finset.mem_image_of_mem w hv
      have hch : (hwinv (w v) hwIm).choose = v :=
        hw_inj (hwinv (w v) hwIm).choose_spec.1 hv (hwinv (w v) hwIm).choose_spec.2
      simp only [ψ, hwu, hwJ, hwIm, ite_false, dite_false, dite_true, hch]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp only [ψ, hr.1, hr.2.1, hr.2.2, ite_false, dite_false]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hr
      rcases hr with rfl | hrJ | ⟨v, hv, rfl⟩
      · rw [hψu]; exact hαL
      · rw [hψJ r hrJ]
        have hm' := ha_mem ⟨r, hrJ⟩; dsimp only [A] at hm'
        split_ifs at hm' <;> exact (Finset.mem_sdiff.mp hm').1
      · rw [hψW v hv]; exact (hcFun_spec α v hv).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at ha'
        rcases ha' with rfl | haJ | ⟨v, hv, rfl⟩
        · have hbN : b' ∈ G.neighborFinset a' := (G.mem_neighborFinset a' b').mpr hab
          rw [hN_part, Finset.mem_insert] at hbN
          rcases hbN with hbx | hbJ
          · rw [hbx, hψu, hψ_out x hx_not_S]; exact hαβ
          · rw [hψu, hψJ b' hbJ]
            have hm' := ha_mem ⟨b', hbJ⟩; dsimp only [A] at hm'
            split_ifs at hm'
            · simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
              exact Ne.symm hm'.2.1
            · simp only [Finset.mem_sdiff, Finset.mem_singleton] at hm'
              exact Ne.symm hm'.2
        · have hm' := ha_mem ⟨a', haJ⟩; dsimp only [A] at hm'
          by_cases haIth : a' ∈ Ith
          · simp only [haIth, ite_true] at hm'
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
            rcases hv_all a' haIth b' hab with hb | hb
            · rw [hb, hψJ a' haJ, hψu]; exact hm'.2.1
            · rw [hb, hψJ a' haJ, hψW a' haIth]; exact hm'.2.2.1
          · simp only [haIth, ite_false] at hm'
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at hm'
            have haI1 : a' ∈ I₁ := by
              rw [← hI_un, Finset.mem_union] at haJ; exact haJ.resolve_right haIth
            have haL := mem_leafNbrs.mp (Finset.mem_inter.mp haI1).2
            rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
            have hb : b' = u := (huniq b' hab).trans (huniq u haL.1.symm).symm
            rw [hb, hψJ a' haJ, hψu]; exact hm'.2
        · rcases hw_all v hv b' hab with hb | hb
          · have hvJ : v ∈ J := (Finset.mem_inter.mp hv).1
            have hm' := ha_mem ⟨v, hvJ⟩; dsimp only [A] at hm'; simp only [hv, ite_true] at hm'
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
            rw [hb, hψW v hv, hψJ v hvJ]; exact Ne.symm hm'.2.2.1
          · rw [hb, hψW v hv, hψ_out (z v) (hz_not_S v hv)]; exact (hcFun_spec α v hv).2.2.1
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro a' haS hnon b' hbS hab
      rcases hS_out a' haS b' hbS hab with ⟨rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
      · rw [hψu]; exact hα_φsx hnon
      · rw [hψW v hv]; exact (hcFun_spec α v hv).2.2.2
    · intro a' haS hiso ⟨b', hab⟩
      have hbS : b' ∈ S := by by_contra h; exact hiso b' h hab
      rcases hS_out a' haS b' hbS hab with ⟨hbu, hax⟩ | ⟨v, hv, rfl, rfl⟩
      · subst a'; subst b'
        refine ⟨u, hab, ?_⟩
        intro r hxr _
        have hrS : r ∈ S := by by_contra h; exact hiso r h hxr
        rcases hS_out x haS r hrS hxr with ⟨rfl, _⟩ | ⟨v, hv, rfl, hxEq⟩
        · rfl
        · rcases hz_noniso v hv with ⟨t, htS, hzt⟩
          exact False.elim (hiso t htS (hxEq ▸ hzt))
      · rcases hz_noniso v hv with ⟨t, htS, hzt⟩
        exact False.elim (hiso t htS hzt)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hrS
      rcases hrS with hru | hrJ | ⟨v, hv, rfl⟩
      · subst r
        by_cases hγβ : γ = β
        · subst hγβ
          have hcnt : ([β] : List ℕ).count β = 1 := by simp
          have hzero : (Finset.univ.filter (fun i : {v // v ∈ J} => a i = β)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨x, hux, ?_⟩
          intro t hut hψt
          have htN : t ∈ G.neighborFinset u := (G.mem_neighborFinset u t).mpr hut
          rw [hN_part, Finset.mem_insert] at htN
          rcases htN with htx | htJ
          · exact htx
          · rw [hψJ t htJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨t, htJ⟩) hψt)
        · have hcnt : ([β] : List ℕ).count γ = 0 := by
            rw [List.count_eq_zero]; simpa using hγβ
          have hone : (Finset.univ.filter (fun i : {v // v ∈ J} => a i = γ)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨⟨v₀, hv₀⟩, hv₀_eq⟩
          have hv₀_col : a ⟨v₀, hv₀⟩ = γ := by
            have : (⟨v₀, hv₀⟩ : {v // v ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) := by
              rw [hv₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          refine ⟨v₀, (G.mem_neighborFinset u v₀).mp (hJ_subN hv₀), ?_⟩
          intro t hut hψt
          have htN : t ∈ G.neighborFinset u := (G.mem_neighborFinset u t).mpr hut
          rw [hN_part, Finset.mem_insert] at htN
          rcases htN with htx | htJ
          · rw [htx, hψ_out x hx_not_S, hψJ v₀ hv₀, hv₀_col] at hψt
            exact False.elim (hγβ hψt.symm)
          · rw [hψJ t htJ, hψJ v₀ hv₀, hv₀_col] at hψt
            have : (⟨t, htJ⟩ : {v // v ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [hv₀_eq, Finset.mem_singleton] at this
            exact congrArg Subtype.val this
      · by_cases hrIth : r ∈ Ith
        · exact pcf_at_of_two_distinct_neighbors (hwz_spec r hrIth).1
            ((G.mem_neighborFinset u r).mp (hJ_subN hrJ)).symm (hwz_spec r hrIth).2.2.1
            (hwz_spec r hrIth).2.2.2.1.symm
            (by rw [hψu, hψW r hrIth]; exact (hcFun_spec α r hrIth).2.1.symm)
        · have hrI1 : r ∈ I₁ := by
            rw [← hI_un, Finset.mem_union] at hrJ; exact hrJ.resolve_right hrIth
          have hrL := mem_leafNbrs.mp (Finset.mem_inter.mp hrI1).2
          exact pcf_at_deg_one hrL.2 hrL.1.symm
      · have hvJ : v ∈ J := (Finset.mem_inter.mp hv).1
        have hm' := ha_mem ⟨v, hvJ⟩; dsimp only [A] at hm'; simp only [hv, ite_true] at hm'
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
        exact pcf_at_of_two_distinct_neighbors (hwz_spec v hv).2.1
          (hwz_spec v hv).2.2.1.symm (hwz_spec v hv).2.2.2.2.1 (hwz_spec v hv).2.2.2.2.2.symm
          (by rw [hψJ v hvJ, hψ_out (z v) (hz_not_S v hv)]; exact hm'.2.2.2)
  -- 双计数：`3 * |C| ≤ ∑_{α ∈ C} q_α ≤ 2 * |I₁| + 3 * |Ith| = 3 * (d(u) - 1) - |I₁|`！
  have hlower : 3 * C.card ≤ ∑ α ∈ C, (J.filter (fun v => (A α v).card = 1)).card := by
    calc 3 * C.card = ∑ _α ∈ C, 3 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, (J.filter (fun v => (A α v).card = 1)).card := by
        apply Finset.sum_le_sum
        intro α hα
        rcases Finset.card_pos.mp (by omega : 0 < J.card) with ⟨v₀, hv₀⟩
        have : Nonempty {v : V // v ∈ J} := ⟨⟨v₀, hv₀⟩⟩
        have hq3 := (no_pcfRep_single_bounds (fun i : {v // v ∈ J} => hA_ne α i.val i.property)
          (hno_rep α hα)).2.2.1 (by rw [Fintype.card_coe]; omega)
        have hbij :
            (Finset.univ.filter (fun i : {v // v ∈ J} => (A α i.val).card = 1)).card =
            (J.filter (fun v => (A α v).card = 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact ⟨i.property, hi⟩
          · intro i₁ _ i₂ _ h; exact Subtype.ext h
          · intro v hv; simp only [Finset.mem_filter] at hv
            exact ⟨⟨v, hv.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩, rfl⟩
        rw [← hbij]; exact hq3
  have hterm_I1 : ∀ v ∈ I₁, (C.filter (fun α => (A α v).card = 1)).card ≤ 2 := by
    intro v hv
    have hvnotIth : v ∉ Ith := Finset.disjoint_left.mp hI_disj hv
    have hLv : (L v).card = 2 := by
      rw [hm.list_card v]; simp [kappa, (mem_leafNbrs.mp (Finset.mem_inter.mp hv).2).2]
    have hEq : C.filter (fun α => (A α v).card = 1) =
        C.filter (fun α => (L v \ {α}).card = 1) := by
      congr 1; ext α; simp [A, hvnotIth]
    rw [hEq]
    exact (card_filter_sdiff_singleton_eq_one_le C (L v) (by omega)).1
  have hterm_Ith : ∀ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card ≤ 3 := by
    intro v hv
    have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, (hwz_spec v hv).1]
    have hEq : C.filter (fun α => (A α v).card = 1) =
        C.filter (fun α => (L v \ {α, cFun α v, adm.φ (z v)}).card = 1) := by
      congr 1; ext α; simp [A, hv]
    rw [hEq]
    exact (card_filter_sdiff_triple_eq_one_le C (L v) hLv (fun α => cFun α v) (adm.φ (z v))).1
  have hupper : ∑ α ∈ C, (J.filter (fun v => (A α v).card = 1)).card ≤
      2 * I₁.card + 3 * Ith.card := by
    rw [sum_filter_card_comm, ← hI_un, Finset.sum_union hI_disj]
    have h1 : ∑ v ∈ I₁, (C.filter (fun α => (A α v).card = 1)).card ≤ 2 * I₁.card := by
      calc ∑ v ∈ I₁, (C.filter (fun α => (A α v).card = 1)).card
          ≤ ∑ _v ∈ I₁, 2 := Finset.sum_le_sum hterm_I1
        _ = 2 * I₁.card := by simp [mul_comm]
    have h2 : ∑ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card ≤ 3 * Ith.card := by
      calc ∑ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card
          ≤ ∑ _v ∈ Ith, 3 := Finset.sum_le_sum hterm_Ith
        _ = 3 * Ith.card := by simp [mul_comm]
    omega
  have hI_sum : I₁.card + Ith.card = G.degree u - 1 := by
    rw [← Finset.card_union_of_disjoint hI_disj, hI_un, hJcard]
  -- 必须处处取等：`I₁ = ∅`, `Ith = J`, `|C| = d(u) - 1`, 且对每个 `v ∈ Ith` 恰有 3 个单点！
  have hI1_zero : I₁.card = 0 := by omega
  have hIth_eq_J : Ith = J := by
    have hI1e : I₁ = ∅ := Finset.card_eq_zero.mp hI1_zero
    rw [hI1e, Finset.empty_union] at hI_un; exact hI_un
  have hsum_eq : ∑ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card = 3 * Ith.card := by
    rw [sum_filter_card_comm, ← hI_un, Finset.sum_union hI_disj] at hlower
    have hI1e : I₁ = ∅ := Finset.card_eq_zero.mp hI1_zero
    rw [hI1e, Finset.sum_empty, zero_add] at hlower
    have h2 : ∑ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card ≤ 3 * Ith.card := by
      calc ∑ v ∈ Ith, (C.filter (fun α => (A α v).card = 1)).card
          ≤ ∑ _v ∈ Ith, 3 := Finset.sum_le_sum hterm_Ith
        _ = 3 * Ith.card := by simp [mul_comm]
    omega
  -- 因此对每个 `v ∈ Ith`，`A α v ⊆ L v \ {adm.φ (z v)} ⊆ C`（不含 `β`！），故任取代表即得 `β` 唯一！
  have hA_sub_C : ∀ α (v : V), v ∈ Ith → A α v ⊆ C := by
    intro α v hv
    have heq3 : (C.filter (fun γ => (A γ v).card = 1)).card = 3 := by
      by_contra hne3
      have hlt3 : (C.filter (fun γ => (A γ v).card = 1)).card < 3 := by
        have := hterm_Ith v hv; omega
      have hlt_sum : ∑ t ∈ Ith, (C.filter (fun γ => (A γ t).card = 1)).card <
          ∑ _t ∈ Ith, 3 :=
        Finset.sum_lt_sum hterm_Ith ⟨v, hv, hlt3⟩
      simp only [Finset.sum_const, smul_eq_mul] at hlt_sum
      omega
    have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, (hwz_spec v hv).1]
    have hEq : C.filter (fun γ => (A γ v).card = 1) =
        C.filter (fun γ => (L v \ {γ, cFun γ v, adm.φ (z v)}).card = 1) := by
      congr 1; ext γ; simp [A, hv]
    rw [hEq] at heq3
    have hsub := (card_filter_sdiff_triple_eq_one_le C (L v) hLv (fun γ => cFun γ v)
      (adm.φ (z v))).2 heq3
    intro c hc
    dsimp only [A] at hc; simp only [hv, ite_true] at hc
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    exact hsub.2 (Finset.mem_sdiff.mpr ⟨hc.1, by simp [hc.2.2.2]⟩)
  -- 任取 `α₀ ∈ C` 与任意代表 `a_i ∈ A α₀ i`：因所有 `a_i ∈ C` 而 `β ∉ C`，`β` 恰出现一次！
  rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α₀, hα₀⟩
  apply hno_rep α₀ hα₀
  refine ⟨fun i => (hA_ne α₀ i.val i.property).choose,
    fun i => (hA_ne α₀ i.val i.property).choose_spec, β, ?_⟩
  have hzero : (Finset.univ.filter (fun i : {v // v ∈ J} =>
      (hA_ne α₀ i.val i.property).choose = β)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ heq
    have hiIth : i.val ∈ Ith := by rw [hIth_eq_J]; exact i.property
    have hmem : (hA_ne α₀ i.val i.property).choose ∈ C :=
      hA_sub_C α₀ i.val hiIth (hA_ne α₀ i.val i.property).choose_spec
    exact hβ_not_C (heq ▸ hmem)
  rw [hzero]; simp

/-- Corollary 3.5(i)：在 `mad < 5/2` 的极小反例中，任意 `3⁺`-度点满足 `coreDeg G u ≥ 2`
（因此每个 `3⁺`-度点要么是好点 `IsGood`，要么是坏点 `IsBad`）。 -/
lemma coreDeg_ge_two_of_deg_ge_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u : V} (hdu : 3 ≤ G.degree u) :
    2 ≤ coreDeg G u := by
  have h1 := leaf_plus_long_thread_le hm hpq hdu
  have h2 := coreDeg_add_leafNbrs hm u
  omega

/-- Corollary 3.5(i')：任意 `3⁺`-度点要么是好点，要么是坏点。 -/
lemma good_or_bad_of_deg_ge_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u : V} (hdu : 3 ≤ G.degree u) :
    IsGood G u ∨ IsBad G u := by
  have hge2 := coreDeg_ge_two_of_deg_ge_three hm hpq hdu
  by_cases h2 : coreDeg G u = 2
  · right
    have hdu4 : 4 ≤ G.degree u := by
      by_contra hlt; push Not at hlt
      have := coreDeg_eq_degree_of_deg_le_three hm (by omega : G.degree u ≤ 3); omega
    exact ⟨hdu4, h2⟩
  · left; unfold IsGood; omega

/-- Corollary 3.5(ii)：若 `coreDeg G u = 3`，则 `u` 至多关联 `1` 条 `2⁺`-线串。 -/
lemma longThreadNbrs_card_le_one_of_coreDeg_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u : V} (hc3 : coreDeg G u = 3) :
    (longThreadNbrs G u).card ≤ 1 := by
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have h1 := leaf_plus_long_thread_le hm hpq hdu3
  have h2 := coreDeg_add_leafNbrs hm u
  omega

/-- Corollary 3.5(iii)：坏核心点不关联任何 `2⁺`-线串。 -/
lemma bad_no_long_thread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u : V} (hbad : IsBad G u) :
    longThreadNbrs G u = ∅ := by
  have hdu4 := hbad.1
  have h1 := leaf_plus_long_thread_le hm hpq (u := u) (by omega)
  have h2 := coreDeg_add_leafNbrs hm u
  rw [hbad.2] at h2
  exact Finset.card_eq_zero.mp (by omega)

/-! ## 3. Lemma 3.6：坏核心点不关联任何 `1`-线串 -/

/-- Lemma 3.6：极小反例中，坏核心点 `u` 不关联任何 `1`-线串。 -/
lemma bad_no_one_thread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hbad : IsBad G u) :
    oneThreadNbrs G u = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ht
  rcases ht.2 with ⟨hut, hdt, v, htv, hvu, hdv3⟩
  rcases hbad with ⟨hdu4, hcore2⟩
  -- 由 Lemma 3.4，`u` 必有一个 `3⁺`-度邻点 `x`；又 `coreDeg u = 2`，故 `coreNbrs G u = {t, x}`！
  rcases bad_has_core_three_plus_neighbor hm ⟨hdu4, hcore2⟩ with ⟨x, hux, hdx3⟩
  have htx : t ≠ x := fun h => by subst h; omega
  have hcore_eq : coreNbrs G u = {t, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact mem_coreNbrs.mpr ⟨hut, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hux, by omega⟩
    · rw [Finset.card_pair htx]; exact hcore2.le
  -- 这里允许 `x = v`！令 `S = {u, t} ∪ leafNbrs G u`
  let Y := leafNbrs G u
  have hY_card : Y.card = G.degree u - 2 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm u; omega
  let S : Finset V := insert u (insert t Y)
  have huS : u ∈ S := Finset.mem_insert_self u _
  have ht_not_Y : t ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hu_not_Y : u ∉ Y := fun h => G.ne_of_adj (mem_leafNbrs.mp h).1 rfl
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    refine ⟨(G.ne_of_adj hux).symm, htx.symm, fun h => ?_⟩
    rw [mem_leafNbrs] at h; omega
  have hv_not_S : v ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    refine ⟨hvu, (G.ne_of_adj htv).symm, fun h => ?_⟩
    rw [mem_leafNbrs] at h; omega
  have ht_all : ∀ r, G.Adj t r → r = u ∨ r = v := by
    intro r htr
    have hNt := neighborFinset_eq_pair_of_deg_two hdt hut.symm htv hvu.symm
    have : r ∈ ({u, v} : Finset V) := by rw [← hNt]; exact (G.mem_neighborFinset t r).mpr htr
    simpa using this
  have hu_all : ∀ r, G.Adj u r → r = x ∨ r = t ∨ r ∈ Y := by
    intro r hur
    have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, h1⟩))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  have hS_out : ∀ a, a ∉ S → ∀ b ∈ S, G.Adj a b → (b = u ∧ a = x) ∨ (b = t ∧ a = v) := by
    intro a haS b hbS hab
    simp only [S, Finset.mem_insert] at hbS
    rcases hbS with rfl | rfl | hbY
    · rcases hu_all a hab.symm with rfl | rfl | haY
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (haS (by simp [S]))
      · exact False.elim (haS (by simp [S, haY]))
    · rcases ht_all a hab.symm with rfl | rfl
      · exact False.elim (haS huS)
      · exact Or.inr ⟨rfl, rfl⟩
    · have hbL := mem_leafNbrs.mp hbY
      rcases exists_unique_neighbor_of_deg_one hbL.2 with ⟨r, _, huniq⟩
      have hau : a = u := (huniq a hab.symm).trans (huniq u hbL.1.symm).symm
      exact False.elim (haS (hau ▸ huS))
  -- `x` 和 `v`（即使 `x = v`！）在 `G - S` 中皆非孤立（因 `d(x), d(v) ≥ 3` 且在 `S` 中至多失 2 邻点 `{u, t}`）
  have hnoniso_x : ∃ r, r ∉ S ∧ G.Adj x r := by
    have hlt : ({u, t} : Finset V).card < (G.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := u) (b := t); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out x hx_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  have hnoniso_v : ∃ r, r ∉ S ∧ G.Adj v r := by
    have hlt : ({u, t} : Finset V).card < (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := u) (b := t); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out v hv_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  have hLt : (L t).card = 4 := by rw [hm.list_card t]; simp [kappa, hdt]
  let β := adm.φ x
  let η := adm.φ v
  let θ := adm.φs v
  let C : Finset ℕ := L u \ {β, η, adm.φs x}
  have hC : G.degree u - 2 ≤ C.card := by
    dsimp only [C]
    have := card_sdiff_ge (L u) {β, η, adm.φs x}
    have := card_triple_le β η (adm.φs x); omega
  let J : Finset V := insert t Y
  have hJ_card : J.card = G.degree u - 1 := by
    dsimp only [J]; rw [Finset.card_insert_of_notMem ht_not_Y, hY_card]; omega
  let A : ℕ → V → Finset ℕ := fun α r =>
    if r = t then L t \ {α, η, θ} else L r \ {α}
  have hA_ne : ∀ α r (hr : r ∈ J), (A α r).Nonempty := by
    intro α r hr; rw [← Finset.card_pos]
    dsimp only [A]; split_ifs with hrt
    · have h1 := card_sdiff_ge (L t) {α, η, θ}
      have h2 := card_triple_le α η θ; omega
    · have hrY : r ∈ Y := (Finset.mem_insert.mp hr).resolve_left hrt
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
      have h1 := card_sdiff_ge (L r) {α}; simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ a : {r : V // r ∈ J} → ℕ, IsPCFRep (fun i => A α i.val) [β] a := by
    intro α hα ⟨a, ha_mem, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    let ψ : V → ℕ := fun r =>
      if r = u then α else if hrJ : r ∈ J then a ⟨r, hrJ⟩ else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψJ : ∀ r (hr : r ∈ J), ψ r = a ⟨r, hr⟩ := by
      intro r hr
      have hru : r ≠ u := by
        simp only [J, Finset.mem_insert] at hr
        rcases hr with rfl | hrY
        · exact (G.ne_of_adj hut).symm
        · exact fun h => hu_not_Y (h ▸ hrY)
      simp [ψ, hru, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, not_or] at hr
      have hrJ : r ∉ J := by simp [J, hr.2.1, hr.2.2]
      simp only [ψ, hr.1, hrJ, ite_false, dite_false]
    have htJ : t ∈ J := Finset.mem_insert_self t Y
    have hat : a ⟨t, htJ⟩ ∈ L t \ {α, η, θ} := by simpa [A] using ha_mem ⟨t, htJ⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hat
    apply adm.contradiction hm ψ hψ_out
    · intro r hr
      simp only [S, Finset.mem_insert] at hr
      rcases hr with rfl | hr'
      · rw [hψu]; exact hα.1
      · have hrJ : r ∈ J := by simpa [J] using hr'
        rw [hψJ r hrJ]
        have hm' := ha_mem ⟨r, hrJ⟩; dsimp only [A] at hm'
        split_ifs at hm' with hrt
        · have hLrt : L r = L t := congrArg L hrt
          rw [hLrt]; exact (Finset.mem_sdiff.mp hm').1
        · exact (Finset.mem_sdiff.mp hm').1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert] at ha'
        rcases ha' with hau | hat' | haY
        · subst a'
          rcases hu_all b' hab with hbx | hbt | hbY
          · rw [hbx, hψu, hψ_out x hx_not_S]; exact hα.2.1
          · rw [hbt, hψu, hψJ t htJ]; exact Ne.symm hat.2.1
          · have hbJ : b' ∈ J := Finset.mem_insert_of_mem hbY
            have hbt : b' ≠ t := fun h => ht_not_Y (h ▸ hbY)
            have hm' := ha_mem ⟨b', hbJ⟩; dsimp only [A] at hm'; simp only [hbt, ite_false] at hm'
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at hm'
            rw [hψu, hψJ b' hbJ]; exact Ne.symm hm'.2
        · subst a'
          rcases ht_all b' hab with hb | hb
          · rw [hb, hψJ t htJ, hψu]; exact hat.2.1
          · rw [hb, hψJ t htJ, hψ_out v hv_not_S]; exact hat.2.2.1
        · have haL := mem_leafNbrs.mp haY
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨w', _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u haL.1.symm).symm
          have haJ : a' ∈ J := Finset.mem_insert_of_mem haY
          have hat' : a' ≠ t := fun h => ht_not_Y (h ▸ haY)
          have hm' := ha_mem ⟨a', haJ⟩; dsimp only [A] at hm'; simp only [hat', ite_false] at hm'
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hm'
          rw [hb, hψJ a' haJ, hψu]; exact hm'.2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro a' haS _ b' hbS hab
      rcases hS_out a' haS b' hbS hab with ⟨hbu, hax⟩ | ⟨hbt, hav⟩
      · rw [hbu, hax, hψu]; exact hα.2.2.2
      · rw [hbt, hav, hψJ t htJ]; exact hat.2.2.2
    · intro a' haS hiso ⟨b', hab⟩
      have hbS : b' ∈ S := by by_contra h; exact hiso b' h hab
      rcases hS_out a' haS b' hbS hab with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rcases hnoniso_x with ⟨r, hrS, hxr⟩; exact False.elim (hiso r hrS hxr)
      · rcases hnoniso_v with ⟨r, hrS, hvr⟩; exact False.elim (hiso r hrS hvr)
    · intro r hrS _
      simp only [S, Finset.mem_insert] at hrS
      rcases hrS with hru | hrt | hrY
      · subst r
        by_cases hγβ : γ = β
        · subst hγβ
          have hcnt : ([β] : List ℕ).count β = 1 := by simp
          have hzero : (Finset.univ.filter (fun i : {r // r ∈ J} => a i = β)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨x, hux, ?_⟩
          intro w' huw' hψw'
          rcases hu_all w' huw' with hw'x | hw't | hwY
          · exact hw'x
          · rw [hw't, hψJ t htJ, hψ_out x hx_not_S] at hψw'
            exact False.elim (hzero (Finset.mem_univ ⟨t, htJ⟩) hψw')
          · have hwJ : w' ∈ J := Finset.mem_insert_of_mem hwY
            rw [hψJ w' hwJ, hψ_out x hx_not_S] at hψw'
            exact False.elim (hzero (Finset.mem_univ ⟨w', hwJ⟩) hψw')
        · have hcnt : ([β] : List ℕ).count γ = 0 := by
            rw [List.count_eq_zero]; simpa using hγβ
          have hone : (Finset.univ.filter (fun i : {r // r ∈ J} => a i = γ)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨⟨w₀, hw₀⟩, hw₀_eq⟩
          have hw₀_col : a ⟨w₀, hw₀⟩ = γ := by
            have : (⟨w₀, hw₀⟩ : {r // r ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) := by
              rw [hw₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          have huw0 : G.Adj u w₀ := by
            simp only [J, Finset.mem_insert] at hw₀
            rcases hw₀ with rfl | hwY
            · exact hut
            · exact (mem_leafNbrs.mp hwY).1
          refine ⟨w₀, huw0, ?_⟩
          intro w' huw' hψw'
          rcases hu_all w' huw' with hw'x | hw't | hwY
          · rw [hw'x, hψ_out x hx_not_S, hψJ w₀ hw₀, hw₀_col] at hψw'
            exact False.elim (hγβ hψw'.symm)
          · rw [hw't, hψJ t htJ, hψJ w₀ hw₀, hw₀_col] at hψw'
            have : (⟨t, htJ⟩ : {r // r ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψw'⟩
            rw [hw₀_eq, Finset.mem_singleton] at this
            exact hw't.trans (congrArg Subtype.val this)
          · have hwJ : w' ∈ J := Finset.mem_insert_of_mem hwY
            rw [hψJ w' hwJ, hψJ w₀ hw₀, hw₀_col] at hψw'
            have : (⟨w', hwJ⟩ : {r // r ∈ J}) ∈ Finset.univ.filter (fun i => a i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψw'⟩
            rw [hw₀_eq, Finset.mem_singleton] at this
            exact congrArg Subtype.val this
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdt hut.symm htv hvu.symm
          (by rw [hψu, hψ_out v hv_not_S]; exact hα.2.2.1)
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
  -- 双计数：`3 * (k - 2) ≤ 3 * |C| ≤ ∑ q_α ≤ 2 * (k - 1)` → 强制 `k = 4` 且处处取等！
  have hlower : 3 * C.card ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
    calc 3 * C.card = ∑ _α ∈ C, 3 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
        apply Finset.sum_le_sum; intro α hα
        have : Nonempty {r : V // r ∈ J} := ⟨⟨t, Finset.mem_insert_self t Y⟩⟩
        have hq3 := (no_pcfRep_single_bounds (fun i : {r // r ∈ J} => hA_ne α i.val i.property)
          (hno_rep α hα)).2.2.1 (by rw [Fintype.card_coe]; omega)
        have hbij :
            (Finset.univ.filter (fun i : {r // r ∈ J} => (A α i.val).card = 1)).card =
            (J.filter (fun r => (A α r).card = 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact ⟨i.property, hi⟩
          · intro i₁ _ i₂ _ h; exact Subtype.ext h
          · intro r hr; simp only [Finset.mem_filter] at hr
            exact ⟨⟨r, hr.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2⟩, rfl⟩
        rw [← hbij]; exact hq3
  have hterm : ∀ r ∈ J, (C.filter (fun α => (A α r).card = 1)).card ≤ 2 := by
    intro r hr
    by_cases hrt : r = t
    · subst r
      have hEq : C.filter (fun α => (A α t).card = 1) =
          C.filter (fun α => (L t \ {α, η, θ}).card = 1) := by congr 1; ext α; simp [A]
      rw [hEq]
      exact (card_filter_sdiff_two_fixed_eq_one_le C (L t) hLt η θ).1
    · have hrY : r ∈ Y := (Finset.mem_insert.mp hr).resolve_left hrt
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
      have hEq : C.filter (fun α => (A α r).card = 1) =
          C.filter (fun α => (L r \ {α}).card = 1) := by congr 1; ext α; simp [A, hrt]
      rw [hEq]
      exact (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).1
  have hupper : ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card ≤ 2 * J.card := by
    rw [sum_filter_card_comm]
    calc ∑ r ∈ J, (C.filter (fun α => (A α r).card = 1)).card
        ≤ ∑ _r ∈ J, 2 := Finset.sum_le_sum hterm
      _ = 2 * J.card := by simp [mul_comm]
  -- 必须 `G.degree u = 4`, `C.card = 2`, 且每个 `r ∈ J` 恰取 2，故 `∀ r ∈ J, A α r ⊆ C`！
  have hC2 : C.card = 2 := by omega
  have hsum_eq : ∑ r ∈ J, (C.filter (fun α => (A α r).card = 1)).card = 2 * J.card := by
    rw [sum_filter_card_comm] at hlower hupper; omega
  have hA_sub_C : ∀ α (r : V), r ∈ J → A α r ⊆ C := by
    intro α r hr
    have heq2 : (C.filter (fun γ => (A γ r).card = 1)).card = 2 := by
      by_contra hne2
      have hlt2 : (C.filter (fun γ => (A γ r).card = 1)).card < 2 := by have := hterm r hr; omega
      have hlt_sum : ∑ s ∈ J, (C.filter (fun γ => (A γ s).card = 1)).card < ∑ _s ∈ J, 2 :=
        Finset.sum_lt_sum hterm ⟨r, hr, hlt2⟩
      simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
    by_cases hrt : r = t
    · subst r
      have hEq : C.filter (fun γ => (A γ t).card = 1) =
          C.filter (fun γ => (L t \ {γ, η, θ}).card = 1) := by congr 1; ext γ; simp [A]
      rw [hEq] at heq2
      have hsub := (card_filter_sdiff_two_fixed_eq_one_le C (L t) hLt η θ).2 heq2
      intro c hc; simp only [A, ite_true, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hc
      exact hsub.2.2.2 (Finset.mem_sdiff.mpr ⟨hc.1, by simp [hc.2.2.1, hc.2.2.2]⟩)
    · have hrY : r ∈ Y := (Finset.mem_insert.mp hr).resolve_left hrt
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
      have hEq : C.filter (fun γ => (A γ r).card = 1) =
          C.filter (fun γ => (L r \ {γ}).card = 1) := by congr 1; ext γ; simp [A, hrt]
      rw [hEq] at heq2
      have hsub := (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).2 heq2
      intro c hc; simp only [A, hrt, ite_false, Finset.mem_sdiff] at hc
      exact hsub.2 hc.1
  -- 任取 `α₀ ∈ C` 与任意代表 `a_i ∈ A α₀ i`：全部落在 `C` 中（不含 `β`！），故 `β` 唯一！
  rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α₀, hα₀⟩
  apply hno_rep α₀ hα₀
  refine ⟨fun i => (hA_ne α₀ i.val i.property).choose,
    fun i => (hA_ne α₀ i.val i.property).choose_spec, β, ?_⟩
  have hzero : (Finset.univ.filter (fun i : {r // r ∈ J} =>
      (hA_ne α₀ i.val i.property).choose = β)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ heq
    have hmem : (hA_ne α₀ i.val i.property).choose ∈ C :=
      hA_sub_C α₀ i.val i.property (hA_ne α₀ i.val i.property).choose_spec
    simp only [C, Finset.mem_sdiff, Finset.mem_insert] at hmem
    exact hmem.2 (Or.inl heq)
  rw [hzero]; simp

/-- 综合 Lemma 3.5(iii) 与 Lemma 3.6：坏核心点的两个核心邻点均无 `2`-度点（全为 `3⁺`-度点）！ -/
lemma bad_coreNbrs_deg_ge_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u v : V} (hbad : IsBad G u) (hv : v ∈ coreNbrs G u) :
    3 ≤ G.degree v := by
  have h2 : degTwoNbrs G u = ∅ := by
    rw [degTwoNbrs_eq_one_union_long hm u, bad_no_one_thread hm hbad,
        bad_no_long_thread hm hpq hbad, Finset.empty_union]
  rw [coreNbrs_eq_degTwo_union_degThreePlus, h2, Finset.empty_union] at hv
  exact (Finset.mem_filter.mp hv).2

/-! ## 4. Lemma 3.7（坏点双色延拓）与定色延拓引理（`bad_fixed_color_extension`） -/

/-- Lemma 3.7（纯组合版）：设 `Y` 为 `d - 2` 个各具 `2`-列表的顶点集（`d ≥ 4`），
`C` 为坏点 `b` 的可用颜色集（`|C| ≥ d - 1`），`δ` 为已染色邻点 `h` 的颜色。
则存在互异两色 `γ₁ ≠ γ₂ ∈ C` 及见证色 `λ`，使得对每个 `i ∈ {1, 2}`，存在 `Y` 上的合法选色
`a_i : Y → ℕ`（满足 `a_i p ∈ L p \ {γ_i}`），令 `λ` 在 `a_i(Y)` 与 `[δ]` 拼合中恰好出现一次！ -/
lemma bad_two_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {C : Finset ℕ} {δ : ℕ}
    (hY2 : 2 ≤ Y.card) (hL2 : ∀ p ∈ Y, (L p).card = 2)
    (hC : Y.card + 1 ≤ C.card) (hδC : δ ∉ C) :
    ∃ γ₁ γ₂ lam : ℕ, γ₁ ∈ C ∧ γ₂ ∈ C ∧ γ₁ ≠ γ₂ ∧
      (∃ a₁ : V → ℕ, (∀ p ∈ Y, a₁ p ∈ L p ∧ a₁ p ≠ γ₁) ∧
        (Y.filter (fun p => a₁ p = lam)).card + (if δ = lam then 1 else 0) = 1) ∧
      (∃ a₂ : V → ℕ, (∀ p ∈ Y, a₂ p ∈ L p ∧ a₂ p ≠ γ₂) ∧
        (Y.filter (fun p => a₂ p = lam)).card + (if δ = lam then 1 else 0) = 1) := by
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
  · -- 情形 1：`|T| ≤ d - 3`，故 `|C \ T| ≥ 2`，取互异 `γ₁, γ₂ ∈ C \ T` 并令 `lam = δ`！
    have hCT : 2 ≤ (C \ T).card := by
      have := card_sdiff_ge C T; omega
    rcases exists_two_of_card_ge_two hCT with ⟨γ₁, hγ₁, γ₂, hγ₂, hγ12⟩
    rw [Finset.mem_sdiff] at hγ₁ hγ₂
    have hbuild : ∀ γ, γ ∈ C → γ ∉ T →
        ∃ a : V → ℕ, (∀ p ∈ Y, a p ∈ L p ∧ a p ≠ γ) ∧
          (Y.filter (fun p => a p = δ)).card + (if δ = δ then 1 else 0) = 1 := by
      intro γ _ hγT
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
          exact ⟨(hη_spec p hpI).1, fun h => hγT (h ▸ Finset.mem_image_of_mem η hpI)⟩
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
    exact ⟨γ₁, γ₂, δ, hγ₁.1, hγ₂.1, hγ12, hbuild γ₁ hγ₁.1 hγ₁.2, hbuild γ₂ hγ₂.1 hγ₂.2⟩
  · -- 情形 2：`|T| = |Y|`，故 `I = Y` 且 `η` 在 `Y` 上单射！
    have hT_eq : T.card = Y.card := by omega
    have hI_eq : I = Y := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ Y)
      (by have := Finset.card_image_le (f := η) (s := I); dsimp only [T] at hT_eq; omega)
    have hCT1 : 1 ≤ (C \ T).card := by have := card_sdiff_ge C T; omega
    rcases Finset.card_pos.mp (by omega : 0 < (C \ T).card) with ⟨γ₁, hγ₁⟩
    rw [Finset.mem_sdiff] at hγ₁
    rcases Finset.card_pos.mp (by omega : 0 < Y.card) with ⟨p₀, hp₀Y⟩
    have hp₀I : p₀ ∈ I := hI_eq ▸ hp₀Y
    let lam := η p₀
    have hlamT : lam ∈ T := Finset.mem_image_of_mem η hp₀I
    have hlamδ : lam ≠ δ := (hη_spec p₀ hp₀I).2
    have hγ1lam : γ₁ ≠ lam := fun h => hγ₁.2 (h ▸ hlamT)
    -- `|C| ≥ |Y| + 1 ≥ 3`，故存在 `γ₂ ∈ C \ {γ₁, lam}`！
    rcases exists_mem_sdiff_of_lt (A := C) (B := {γ₁, lam})
      (by have := Finset.card_le_two (a := γ₁) (b := lam); omega) with ⟨γ₂, hγ₂, hγ2n⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ2n
    -- 对 `γ ∈ {γ₁, γ₂}`，统一构造 `a(p) = if p = p₀ then lam else δ`！
    let a : V → ℕ := fun p => if p = p₀ then lam else δ
    have hbuild : ∀ γ, γ ∈ C → γ ≠ lam →
        (∀ p ∈ Y, a p ∈ L p ∧ a p ≠ γ) ∧
        (Y.filter (fun p => a p = lam)).card + (if δ = lam then 1 else 0) = 1 := by
      intro γ hγC hγlam
      refine ⟨?_, ?_⟩
      · intro p hpY
        by_cases hp0 : p = p₀
        · subst p; simp only [a, ite_true]
          exact ⟨(hη_spec p₀ hp₀I).1, hγlam.symm⟩
        · simp only [a, hp0, ite_false]
          have hpI : p ∈ I := hI_eq ▸ hpY
          exact ⟨(Finset.mem_filter.mp hpI).2, fun h => hδC (h ▸ hγC)⟩
      · have hEq : Y.filter (fun p => a p = lam) = {p₀} := by
          ext p; simp only [Finset.mem_filter, Finset.mem_singleton, a]
          constructor
          · rintro ⟨_, h⟩; split_ifs at h with hp0
            · exact hp0
            · exact False.elim (hlamδ h.symm)
          · rintro rfl; exact ⟨hp₀Y, by simp⟩
        rw [hEq, Finset.card_singleton]; simp [hlamδ.symm]
    exact ⟨γ₁, γ₂, lam, hγ₁.1, hγ₂, Ne.symm hγ2n.1,
      ⟨a, hbuild γ₁ hγ₁.1 hγ1lam⟩, ⟨a, hbuild γ₂ hγ₂ hγ2n.2⟩⟩

/-- 定色延拓引理（抽离自 Lu–Ying–Song Lemma 3.10 末尾，并直接复用于 Milestone 2 的 Lemma B！）：
设 `Y` 为 `d - 2` 个各具 `2`-列表的顶点集（`d ≥ 4`），`ρ, δ` 为坏点 `b` 的两个核心邻点的固定颜色，
`R` 为 `b` 的可用颜色集（`ρ ∉ R`，且 `|R| ≥ (if ρ = δ then |Y| + 1 else |Y|)`）。
则存在 `c ∈ R` 与 `a : V → ℕ`（满足 `∀ p ∈ Y, a p ∈ L p \ {c}`），使得 `a(Y)` 与 `[ρ, δ]` 拼合后有唯一色！ -/
lemma bad_fixed_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {R : Finset ℕ} {ρ δ : ℕ}
    (hY2 : 2 ≤ Y.card) (hL2 : ∀ p ∈ Y, (L p).card = 2)
    (hρR : ρ ∉ R)
    (hR : (if ρ = δ then Y.card + 1 else Y.card) ≤ R.card) :
    ∃ c ∈ R, ∃ a : V → ℕ, (∀ p ∈ Y, a p ∈ L p ∧ a p ≠ c) ∧
      ∃ γ : ℕ, (Y.filter (fun p => a p = γ)).card + ([ρ, δ] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  -- 对任意 `c ∈ R`，`A_c(p) = L p \ {c}` 在 `Y` 上无 `B = [ρ, δ]` 的 `PCF`-代表系统！
  have hno_rep : ∀ c ∈ R,
      ¬ ∃ a : {p : V // p ∈ Y} → ℕ, IsPCFRep (fun i => L i.val \ {c}) [ρ, δ] a := by
    intro c hc ⟨a, ha_mem, γ, hγ⟩
    let aExt : V → ℕ := fun p => if hp : p ∈ Y then a ⟨p, hp⟩ else 0
    have hbij :
        (Finset.univ.filter (fun i : {p // p ∈ Y} => a i = γ)).card =
        (Y.filter (fun p => aExt p = γ)).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨i.property, by simp [aExt, i.property, hi]⟩
      · intro i₁ _ i₂ _ h; exact Subtype.ext h
      · intro p hp; simp only [Finset.mem_filter] at hp
        exact ⟨⟨p, hp.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [aExt, hp.1] using hp.2⟩, rfl⟩
    refine hno c hc aExt (fun p hp => ?_) γ (by rw [← hbij]; exact hγ)
    simp only [aExt, hp, dite_true]
    have hm := ha_mem ⟨p, hp⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hm
    exact hm
  -- 双计数：`2 * |R| ≤ ∑_{c ∈ R} q_c ≤ 2 * |Y|`！
  have hlower : 2 * R.card ≤ ∑ c ∈ R, (Y.filter (fun p => (L p \ {c}).card = 1)).card := by
    calc 2 * R.card = ∑ _c ∈ R, 2 := by simp [mul_comm]
      _ ≤ ∑ c ∈ R, (Y.filter (fun p => (L p \ {c}).card = 1)).card := by
        apply Finset.sum_le_sum; intro c hc
        rcases Finset.card_pos.mp (by omega : 0 < Y.card) with ⟨p₀, hp₀⟩
        have : Nonempty {p : V // p ∈ Y} := ⟨⟨p₀, hp₀⟩⟩
        have hne : ∀ i : {p : V // p ∈ Y}, (L i.val \ {c}).Nonempty := by
          intro i; rw [← Finset.card_pos]
          have := card_sdiff_ge (L i.val) {c}; have := hL2 i.val i.property
          simp only [Finset.card_singleton] at *; omega
        have hq2 := no_pcfRep_pair_ge_two hne (by rw [Fintype.card_coe]; exact hY2) (hno_rep c hc)
        have hbij :
            (Finset.univ.filter (fun i : {p // p ∈ Y} => (L i.val \ {c}).card = 1)).card =
            (Y.filter (fun p => (L p \ {c}).card = 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact ⟨i.property, hi⟩
          · intro i₁ _ i₂ _ h; exact Subtype.ext h
          · intro p hp; simp only [Finset.mem_filter] at hp
            exact ⟨⟨p, hp.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
        rw [← hbij]; exact hq2
  have hterm : ∀ p ∈ Y, (R.filter (fun c => (L p \ {c}).card = 1)).card ≤ 2 := fun p hp =>
    (card_filter_sdiff_singleton_eq_one_le R (L p) (by have := hL2 p hp; omega)).1
  have hupper : ∑ c ∈ R, (Y.filter (fun p => (L p \ {c}).card = 1)).card ≤ 2 * Y.card := by
    rw [sum_filter_card_comm]
    calc ∑ p ∈ Y, (R.filter (fun c => (L p \ {c}).card = 1)).card
        ≤ ∑ _p ∈ Y, 2 := Finset.sum_le_sum hterm
      _ = 2 * Y.card := by simp [mul_comm]
  -- 若 `ρ = δ`，则 `|R| ≥ |Y| + 1`，与 `2 * |R| ≤ 2 * |Y|` 矛盾！
  by_cases hρδ : ρ = δ
  · simp only [hρδ, ite_true] at hR; omega
  · -- 故 `ρ ≠ δ` 且处处取等：每个 `p ∈ Y` 满足 `L p ⊆ R`（不含 `ρ` 与 `δ`！），任取 `c ∈ R` 即可！
    simp only [hρδ, ite_false] at hR
    have hsum_eq : ∑ p ∈ Y, (R.filter (fun c => (L p \ {c}).card = 1)).card = 2 * Y.card := by
      rw [sum_filter_card_comm] at hlower hupper; omega
    have hL_sub_R : ∀ p ∈ Y, L p ⊆ R := by
      intro p hp
      have heq2 : (R.filter (fun c => (L p \ {c}).card = 1)).card = 2 := by
        by_contra hne2
        have hlt2 : (R.filter (fun c => (L p \ {c}).card = 1)).card < 2 := by
          have := hterm p hp; omega
        have hlt_sum : ∑ q ∈ Y, (R.filter (fun c => (L q \ {c}).card = 1)).card < ∑ _q ∈ Y, 2 :=
          Finset.sum_lt_sum hterm ⟨p, hp, hlt2⟩
        simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
      exact ((card_filter_sdiff_singleton_eq_one_le R (L p) (by have := hL2 p hp; omega)).2 heq2).2
    rcases Finset.card_pos.mp (by omega : 0 < R.card) with ⟨c₀, hc₀⟩
    have hpick : ∀ p : V, p ∈ Y → ∃ x ∈ L p, x ≠ c₀ := by
      intro p hp
      rcases exists_mem_sdiff_of_lt (A := L p) (B := {c₀}) (by simp [hL2 p hp]) with ⟨x, hx, hxn⟩
      rw [Finset.mem_singleton] at hxn; exact ⟨x, hx, hxn⟩
    let a : V → ℕ := fun p => if hp : p ∈ Y then (hpick p hp).choose else 0
    refine hno c₀ hc₀ a
      (fun p hp => by simp only [a, hp, dite_true]; exact (hpick p hp).choose_spec) ρ ?_
    have hzero : (Y.filter (fun p => a p = ρ)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq
      simp only [a, hp, dite_true] at heq
      exact hρR (hL_sub_R p hp (heq ▸ (hpick p hp).choose_spec.1))
    rw [hzero, zero_add]; simp [hρδ]

/-! ## 5. Lemma 3.8：任意两个坏核心点不相邻 -/

/-- Lemma 3.8：极小反例中，任意两个坏核心点 `u₁, u₂` 互不相邻！ -/
lemma no_adjacent_bad {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u₁ u₂ : V} (hb1 : IsBad G u₁) (hb2 : IsBad G u₂) (hadj : G.Adj u₁ u₂) : False := by
  classical
  have hu12 : u₁ ≠ u₂ := G.ne_of_adj hadj
  have hu2_core1 : u₂ ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨hadj, by have := hb2.1; omega⟩
  have hu1_core2 : u₁ ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨hadj.symm, by have := hb1.1; omega⟩
  -- 取出 `u₁` 除 `u₂` 外的唯一核心邻点 `x`，以及 `u₂` 除 `u₁` 外的唯一核心邻点 `y`（可能 `x = y`！）
  have h1_other : (coreNbrs G u₁ \ {u₂}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu2_core1),
        Finset.card_singleton]; exact by have := hb1.2; unfold coreDeg at this; omega
  have h2_other : (coreNbrs G u₂ \ {u₁}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu1_core2),
        Finset.card_singleton]; exact by have := hb2.2; unfold coreDeg at this; omega
  rcases Finset.card_eq_one.mp h1_other with ⟨x, hx_eq⟩
  rcases Finset.card_eq_one.mp h2_other with ⟨y, hy_eq⟩
  have hx_mem : x ∈ coreNbrs G u₁ \ {u₂} := by rw [hx_eq]; simp
  have hy_mem : y ∈ coreNbrs G u₂ \ {u₁} := by rw [hy_eq]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hx_mem hy_mem
  have hux : G.Adj u₁ x := (mem_coreNbrs.mp hx_mem.1).1
  have huy : G.Adj u₂ y := (mem_coreNbrs.mp hy_mem.1).1
  have hxu2 : x ≠ u₂ := hx_mem.2
  have hyu1 : y ≠ u₁ := hy_mem.2
  have hdx3 : 3 ≤ G.degree x := bad_coreNbrs_deg_ge_three hm hpq hb1 hx_mem.1
  have hdy3 : 3 ≤ G.degree y := bad_coreNbrs_deg_ge_three hm hpq hb2 hy_mem.1
  have hcore1 : coreNbrs G u₁ = {u₂, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hu2_core1
      · exact hx_mem.1
    · rw [Finset.card_pair hxu2.symm]; have := hb1.2; unfold coreDeg at this; omega
  have hcore2 : coreNbrs G u₂ = {u₁, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hu1_core2
      · exact hy_mem.1
    · rw [Finset.card_pair hyu1.symm]; have := hb2.2; unfold coreDeg at this; omega
  let W := leafNbrs G u₁
  let Z := leafNbrs G u₂
  have hW_card : W.card = G.degree u₁ - 2 := by
    dsimp only [W]; have := coreDeg_add_leafNbrs hm u₁; have := hb1.2; omega
  have hZ_card : Z.card = G.degree u₂ - 2 := by
    dsimp only [Z]; have := coreDeg_add_leafNbrs hm u₂; have := hb2.2; omega
  have hWZ_disj : Disjoint W Z := by
    rw [Finset.disjoint_left]; intro r hrW hrZ
    have h1 := mem_leafNbrs.mp hrW; have h2 := mem_leafNbrs.mp hrZ
    rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨t, _, huniq⟩
    exact hu12 ((huniq u₁ h1.1.symm).trans (huniq u₂ h2.1.symm).symm)
  let S : Finset V := insert u₁ (insert u₂ (W ∪ Z))
  have hu1S : u₁ ∈ S := Finset.mem_insert_self u₁ _
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨(G.ne_of_adj hux).symm, hxu2, fun h => ?_, fun h => ?_⟩
    · rw [mem_leafNbrs] at h; omega
    · rw [mem_leafNbrs] at h; omega
  have hy_not_S : y ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨hyu1, (G.ne_of_adj huy).symm, fun h => ?_, fun h => ?_⟩
    · rw [mem_leafNbrs] at h; omega
    · rw [mem_leafNbrs] at h; omega
  have hu1_all : ∀ r, G.Adj u₁ r → r = u₂ ∨ r = x ∨ r ∈ W := by
    intro r hr
    have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore1, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hu2_all : ∀ r, G.Adj u₂ r → r = u₁ ∨ r = y ∨ r ∈ Z := by
    intro r hr
    have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore2, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hS_out : ∀ a, a ∉ S → ∀ b ∈ S, G.Adj a b → (b = u₁ ∧ a = x) ∨ (b = u₂ ∧ a = y) := by
    intro a haS b hbS hab
    simp only [S, Finset.mem_insert, Finset.mem_union] at hbS
    rcases hbS with rfl | rfl | hbW | hbZ
    · rcases hu1_all a hab.symm with rfl | rfl | haW
      · exact False.elim (haS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (haS (by simp [S, haW]))
    · rcases hu2_all a hab.symm with rfl | rfl | haZ
      · exact False.elim (haS hu1S)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (haS (by simp [S, haZ]))
    · have hL := mem_leafNbrs.mp hbW
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (haS (((huniq a hab.symm).trans (huniq u₁ hL.1.symm).symm) ▸ hu1S))
    · have hL := mem_leafNbrs.mp hbZ
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (haS (((huniq a hab.symm).trans (huniq u₂ hL.1.symm).symm) ▸
        (by simp [S] : u₂ ∈ S)))
  -- 注意：`d(x) ≥ 3, d(y) ≥ 3` 且在 `S` 中至多邻 `{u₁, u₂}`，故 `x` 和 `y` 在 `G - S` 中皆非孤立！
  have hnoniso_x : ∃ r, r ∉ S ∧ G.Adj x r := by
    have hlt : ({u₁, u₂} : Finset V).card < (G.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := u₁) (b := u₂); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out x hx_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  have hnoniso_y : ∃ r, r ∉ S ∧ G.Adj y r := by
    have hlt : ({u₁, u₂} : Finset V).card < (G.neighborFinset y).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := u₁) (b := u₂); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out y hy_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u₁, hu1S⟩ with ⟨adm⟩
  have hLu1 : (L u₁).card = G.degree u₁ + 1 := by
    rw [hm.list_card u₁]; simp [kappa, show G.degree u₁ ≠ 2 by have := hb1.1; omega]
  have hLu2 : (L u₂).card = G.degree u₂ + 1 := by
    rw [hm.list_card u₂]; simp [kappa, show G.degree u₂ ≠ 2 by have := hb2.1; omega]
  -- 对 `u₁` 应用 Lemma 3.7（`bad_two_color_extension`）！
  let δ := adm.φ x
  let C : Finset ℕ := L u₁ \ {δ, adm.φs x}
  have hC : W.card + 1 ≤ C.card := by
    dsimp only [C]
    have := card_sdiff_ge (L u₁) {δ, adm.φs x}
    have := Finset.card_le_two (a := δ) (b := adm.φs x)
    have := hb1.1; omega
  have hW_L2 : ∀ r ∈ W, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hZ_L2 : ∀ r ∈ Z, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  rcases bad_two_color_extension (Y := W) (C := C) (δ := δ) (by have := hb1.1; omega) hW_L2 hC
      (by simp [C]) with ⟨β, γ, α, hβC, hγC, hβγ, ⟨aW1, haW1_mem, haW1_u⟩, ⟨aW2, haW2_mem, haW2_u⟩⟩
  -- 对 `u₂`，令 `F = L u₂ \ {α, η, φ* y}`（`|F| ≥ m - 2 = |Z|`）！
  let η := adm.φ y
  let F : Finset ℕ := L u₂ \ {α, η, adm.φs y}
  have hF : Z.card ≤ F.card := by
    dsimp only [F]
    have := card_sdiff_ge (L u₂) {α, η, adm.φs y}
    have := card_triple_le α η (adm.φs y); omega
  let J : Finset V := insert u₁ Z
  have hu1_not_Z : u₁ ∉ Z := fun h => by rw [mem_leafNbrs] at h; have := hb1.1; omega
  have hJ_card : J.card = Z.card + 1 := Finset.card_insert_of_notMem hu1_not_Z
  let A : ℕ → V → Finset ℕ := fun θ r => if r = u₁ then ({β, γ} : Finset ℕ) \ {θ} else L r \ {θ}
  have hA_ne : ∀ θ r (hr : r ∈ J), (A θ r).Nonempty := by
    intro θ r hr; rw [← Finset.card_pos]
    dsimp only [A]; split_ifs with hr1
    · have := card_sdiff_ge ({β, γ} : Finset ℕ) {θ}
      rw [Finset.card_pair hβγ, Finset.card_singleton] at this; omega
    · have hrZ : r ∈ Z := (Finset.mem_insert.mp hr).resolve_left hr1
      have := card_sdiff_ge (L r) {θ}; have := hZ_L2 r hrZ
      simp only [Finset.card_singleton] at *; omega
  -- 断言：对每个 `θ ∈ F`，`A θ` 在 `J` 上无 `B = [η]` 的 `PCF`-代表系统！
  have hno_rep : ∀ θ ∈ F,
      ¬ ∃ a : {r : V // r ∈ J} → ℕ, IsPCFRep (fun i => A θ i.val) [η] a := by
    intro θ hθ ⟨a, ha_mem, μ, hμ⟩
    simp only [F, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hθ
    have hu1J : u₁ ∈ J := Finset.mem_insert_self u₁ Z
    have hau1_raw : a ⟨u₁, hu1J⟩ ∈ ({β, γ} : Finset ℕ) \ {θ} := by simpa [A] using ha_mem ⟨u₁, hu1J⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hau1_raw
    let c1 := a ⟨u₁, hu1J⟩
    have hc1_cases : c1 = β ∨ c1 = γ := hau1_raw.1
    have hc1C : c1 ∈ C := by
      rcases hc1_cases with h | h
      · rw [h]; exact hβC
      · rw [h]; exact hγC
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1C
    let aW : V → ℕ := if c1 = β then aW1 else aW2
    have haW_mem : ∀ r ∈ W, aW r ∈ L r ∧ aW r ≠ c1 := by
      intro r hr; dsimp only [aW]; split_ifs with h
      · rw [h]; exact haW1_mem r hr
      · rw [hc1_cases.resolve_left h]; exact haW2_mem r hr
    have haW_u : (W.filter (fun r => aW r = α)).card + (if δ = α then 1 else 0) = 1 := by
      by_cases h : c1 = β
      · simp only [aW, h, ite_true]; exact haW1_u
      · simp only [aW, h, ite_false]; exact haW2_u
    let ψ : V → ℕ := fun r =>
      if r = u₁ then c1
      else if r = u₂ then θ
      else if r ∈ W then aW r
      else if hrZ : r ∈ Z then a ⟨r, Finset.mem_insert_of_mem hrZ⟩
      else adm.φ r
    have hψu1 : ψ u₁ = c1 := by simp [ψ]
    have hψu2 : ψ u₂ = θ := by simp [ψ, hu12.symm]
    have hψW : ∀ r ∈ W, ψ r = aW r := by
      intro r hr
      have hr1 : r ≠ u₁ := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; have := hb1.1; omega
      have hr2 : r ≠ u₂ := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; have := hb2.1; omega
      simp [ψ, hr1, hr2, hr]
    have hψZ : ∀ r (hr : r ∈ Z), ψ r = a ⟨r, Finset.mem_insert_of_mem hr⟩ := by
      intro r hr
      have hr1 : r ≠ u₁ := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; have := hb1.1; omega
      have hr2 : r ≠ u₂ := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; have := hb2.1; omega
      have hrW : r ∉ W := fun h => Finset.disjoint_left.mp hWZ_disj h hr
      simp [ψ, hr1, hr2, hrW, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr
      simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | hrW | hrZ
      · rw [hψu1]; exact hc1C.1
      · rw [hψu2]; exact hθ.1
      · rw [hψW r hrW]; exact (haW_mem r hrW).1
      · rw [hψZ r hrZ]
        have hr1 : r ≠ u₁ := fun h => hu1_not_Z (h ▸ hrZ)
        have hm' := ha_mem ⟨r, Finset.mem_insert_of_mem hrZ⟩
        simp only [A, hr1, ite_false, Finset.mem_sdiff] at hm'; exact hm'.1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with ha1 | ha2 | haW | haZ
        · subst a'
          rcases hu1_all b' hab with hb2 | hbx | hbW
          · rw [hb2, hψu1, hψu2]; exact hau1_raw.2
          · rw [hbx, hψu1, hψ_out x hx_not_S]; exact hc1C.2.1
          · rw [hψu1, hψW b' hbW]; exact (haW_mem b' hbW).2.symm
        · subst a'
          rcases hu2_all b' hab with hb1 | hby | hbZ
          · rw [hb1, hψu2, hψu1]; exact Ne.symm hau1_raw.2
          · rw [hby, hψu2, hψ_out y hy_not_S]; exact hθ.2.2.1
          · have hb1' : b' ≠ u₁ := fun h => hu1_not_Z (h ▸ hbZ)
            have hm' := ha_mem ⟨b', Finset.mem_insert_of_mem hbZ⟩
            simp only [A, hb1', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
            rw [hψu2, hψZ b' hbZ]; exact Ne.symm hm'.2
        · have haL := mem_leafNbrs.mp haW
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
          have hb : b' = u₁ := (huniq b' hab).trans (huniq u₁ haL.1.symm).symm
          rw [hb, hψW a' haW, hψu1]; exact (haW_mem a' haW).2
        · have haL := mem_leafNbrs.mp haZ
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
          have hb : b' = u₂ := (huniq b' hab).trans (huniq u₂ haL.1.symm).symm
          have ha1' : a' ≠ u₁ := fun h => hu1_not_Z (h ▸ haZ)
          have hm' := ha_mem ⟨a', Finset.mem_insert_of_mem haZ⟩
          simp only [A, ha1', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
          rw [hb, hψZ a' haZ, hψu2]; exact hm'.2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro a' haS _ b' hbS hab
      rcases hS_out a' haS b' hbS hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hψu1]; exact hc1C.2.2
      · rw [hψu2]; exact hθ.2.2.2
    · intro a' haS hiso ⟨b', hab⟩
      have hbS : b' ∈ S := by by_contra h; exact hiso b' h hab
      rcases hS_out a' haS b' hbS hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hnoniso_x with ⟨r, hrS, hxr⟩; exact False.elim (hiso r hrS hxr)
      · rcases hnoniso_y with ⟨r, hrS, hyr⟩; exact False.elim (hiso r hrS hyr)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with hr1 | hr2 | hrW | hrZ
      · subst r
        by_cases hδα : δ = α
        · simp only [hδα, ite_true] at haW_u
          have hzero : (W.filter (fun t => aW t = α)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨x, hux, ?_⟩
          intro t hut hψt
          rcases hu1_all t hut with ht2 | htx | htW
          · rw [ht2, hψu2, hψ_out x hx_not_S] at hψt
            exact False.elim (hθ.2.1 (hψt.trans hδα))
          · exact htx
          · rw [hψW t htW, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero htW (hψt.trans hδα))
        · simp only [hδα, ite_false] at haW_u
          have hone : (W.filter (fun t => aW t = α)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
          have hw₀_mem : w₀ ∈ W.filter (fun t => aW t = α) := by rw [hw₀_eq]; simp
          rw [Finset.mem_filter] at hw₀_mem
          refine ⟨w₀, (mem_leafNbrs.mp hw₀_mem.1).1, ?_⟩
          intro t hut hψt
          rcases hu1_all t hut with ht2 | htx | htW
          · rw [ht2, hψu2, hψW w₀ hw₀_mem.1, hw₀_mem.2] at hψt
            exact False.elim (hθ.2.1 hψt)
          · rw [htx, hψ_out x hx_not_S, hψW w₀ hw₀_mem.1, hw₀_mem.2] at hψt
            exact False.elim (hδα hψt)
          · rw [hψW t htW, hψW w₀ hw₀_mem.1, hw₀_mem.2] at hψt
            have : t ∈ W.filter (fun t => aW t = α) := Finset.mem_filter.mpr ⟨htW, hψt⟩
            rw [hw₀_eq, Finset.mem_singleton] at this; exact this
      · subst r
        by_cases hμη : μ = η
        · subst hμη
          have hcnt : ([η] : List ℕ).count η = 1 := by simp
          have hzero : (Finset.univ.filter (fun i : {t // t ∈ J} => a i = η)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨y, huy, ?_⟩
          intro t hut hψt
          rcases hu2_all t hut with ht1 | hty | htZ
          · rw [ht1, hψu1, hψ_out y hy_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨u₁, hu1J⟩) hψt)
          · exact hty
          · rw [hψZ t htZ, hψ_out y hy_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨t, Finset.mem_insert_of_mem htZ⟩) hψt)
        · have hcnt : ([η] : List ℕ).count μ = 0 := by
            rw [List.count_eq_zero]; simpa using hμη
          have hone : (Finset.univ.filter (fun i : {t // t ∈ J} => a i = μ)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨⟨z₀, hz₀⟩, hz₀_eq⟩
          have hz₀_col : a ⟨z₀, hz₀⟩ = μ := by
            have : (⟨z₀, hz₀⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => a i = μ) := by
              rw [hz₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          have hu2z0 : G.Adj u₂ z₀ := by
            simp only [J, Finset.mem_insert] at hz₀
            rcases hz₀ with rfl | hzZ
            · exact hadj.symm
            · exact (mem_leafNbrs.mp hzZ).1
          have hψz0 : ψ z₀ = μ := by
            simp only [J, Finset.mem_insert] at hz₀
            rcases hz₀ with rfl | hzZ
            · rw [hψu1]; exact hz₀_col
            · rw [hψZ z₀ hzZ]; exact hz₀_col
          refine ⟨z₀, hu2z0, ?_⟩
          intro t hut hψt
          rcases hu2_all t hut with ht1 | hty | htZ
          · rw [ht1, hψu1, hψz0] at hψt
            have : (⟨u₁, hu1J⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => a i = μ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [hz₀_eq, Finset.mem_singleton] at this; exact ht1.trans (congrArg Subtype.val this)
          · rw [hty, hψ_out y hy_not_S, hψz0] at hψt; exact False.elim (hμη hψt.symm)
          · rw [hψZ t htZ, hψz0] at hψt
            have : (⟨t, Finset.mem_insert_of_mem htZ⟩ : {t // t ∈ J}) ∈
                Finset.univ.filter (fun i => a i = μ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [hz₀_eq, Finset.mem_singleton] at this; exact congrArg Subtype.val this
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrW).2 (mem_leafNbrs.mp hrW).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrZ).2 (mem_leafNbrs.mp hrZ).1.symm
  -- 双计数：`3 * |F| ≤ ∑_{θ ∈ F} q_θ ≤ 2 * (|Z| + 1)` → 强制 `|Z| = 2, |F| = 2` 且 `∀ r ∈ J, A θ r ⊆ F`！
  have hlower : 3 * F.card ≤ ∑ θ ∈ F, (J.filter (fun r => (A θ r).card = 1)).card := by
    calc 3 * F.card = ∑ _θ ∈ F, 3 := by simp [mul_comm]
      _ ≤ ∑ θ ∈ F, (J.filter (fun r => (A θ r).card = 1)).card := by
        apply Finset.sum_le_sum; intro θ hθ
        have : Nonempty {r : V // r ∈ J} := ⟨⟨u₁, Finset.mem_insert_self u₁ Z⟩⟩
        have hq3 := (no_pcfRep_single_bounds (fun i : {r // r ∈ J} => hA_ne θ i.val i.property)
          (hno_rep θ hθ)).2.2.1 (by rw [Fintype.card_coe, hJ_card]; have := hb2.1; omega)
        have hbij :
            (Finset.univ.filter (fun i : {r // r ∈ J} => (A θ i.val).card = 1)).card =
            (J.filter (fun r => (A θ r).card = 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact ⟨i.property, hi⟩
          · intro i₁ _ i₂ _ h; exact Subtype.ext h
          · intro r hr; simp only [Finset.mem_filter] at hr
            exact ⟨⟨r, hr.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2⟩, rfl⟩
        rw [← hbij]; exact hq3
  have hterm : ∀ r ∈ J, (F.filter (fun θ => (A θ r).card = 1)).card ≤ 2 := by
    intro r hr
    by_cases hr1 : r = u₁
    · subst r
      have hEq : F.filter (fun θ => (A θ u₁).card = 1) =
          F.filter (fun θ => (({β, γ} : Finset ℕ) \ {θ}).card = 1) := by congr 1; ext θ; simp [A]
      rw [hEq]
      exact (card_filter_sdiff_singleton_eq_one_le F {β, γ} (by rw [Finset.card_pair hβγ])).1
    · have hrZ : r ∈ Z := (Finset.mem_insert.mp hr).resolve_left hr1
      have hEq : F.filter (fun θ => (A θ r).card = 1) =
          F.filter (fun θ => (L r \ {θ}).card = 1) := by congr 1; ext θ; simp [A, hr1]
      rw [hEq]
      exact (card_filter_sdiff_singleton_eq_one_le F (L r) (by have := hZ_L2 r hrZ; omega)).1
  have hupper : ∑ θ ∈ F, (J.filter (fun r => (A θ r).card = 1)).card ≤ 2 * J.card := by
    rw [sum_filter_card_comm]
    calc ∑ r ∈ J, (F.filter (fun θ => (A θ r).card = 1)).card
        ≤ ∑ _r ∈ J, 2 := Finset.sum_le_sum hterm
      _ = 2 * J.card := by simp [mul_comm]
  have hZ2 : Z.card = 2 := by have := hb2.1; omega
  have hF2 : F.card = 2 := by omega
  have hsum_eq : ∑ r ∈ J, (F.filter (fun θ => (A θ r).card = 1)).card = 2 * J.card := by
    rw [sum_filter_card_comm] at hlower hupper; omega
  -- 于是对每个 `r ∈ J`，所有备选颜色均落在 `F` 中（特别地 `η ∉ F`，故任取 `θ₀ ∈ F` 与任意代表即得 `η` 唯一！）
  have hA_sub_F : ∀ θ (r : V), r ∈ J → A θ r ⊆ F := by
    intro θ r hr
    have heq2 : (F.filter (fun c => (A c r).card = 1)).card = 2 := by
      by_contra hne2
      have hlt2 : (F.filter (fun c => (A c r).card = 1)).card < 2 := by have := hterm r hr; omega
      have hlt_sum : ∑ s ∈ J, (F.filter (fun c => (A c s).card = 1)).card < ∑ _s ∈ J, 2 :=
        Finset.sum_lt_sum hterm ⟨r, hr, hlt2⟩
      simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
    by_cases hr1 : r = u₁
    · subst r
      have hEq : F.filter (fun c => (A c u₁).card = 1) =
          F.filter (fun c => (({β, γ} : Finset ℕ) \ {c}).card = 1) := by congr 1; ext c; simp [A]
      rw [hEq] at heq2
      have hsub := (card_filter_sdiff_singleton_eq_one_le F {β, γ}
        (by rw [Finset.card_pair hβγ])).2 heq2
      intro c hc; simp only [A, ite_true, Finset.mem_sdiff] at hc; exact hsub.2 hc.1
    · have hrZ : r ∈ Z := (Finset.mem_insert.mp hr).resolve_left hr1
      have hEq : F.filter (fun c => (A c r).card = 1) =
          F.filter (fun c => (L r \ {c}).card = 1) := by congr 1; ext c; simp [A, hr1]
      rw [hEq] at heq2
      have hsub := (card_filter_sdiff_singleton_eq_one_le F (L r)
        (by have := hZ_L2 r hrZ; omega)).2 heq2
      intro c hc; simp only [A, hr1, ite_false, Finset.mem_sdiff] at hc; exact hsub.2 hc.1
  rcases Finset.card_pos.mp (by omega : 0 < F.card) with ⟨θ₀, hθ₀⟩
  apply hno_rep θ₀ hθ₀
  refine ⟨fun i => (hA_ne θ₀ i.val i.property).choose,
    fun i => (hA_ne θ₀ i.val i.property).choose_spec, η, ?_⟩
  have hzero : (Finset.univ.filter (fun i : {r // r ∈ J} =>
      (hA_ne θ₀ i.val i.property).choose = η)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ heq
    have hmem : (hA_ne θ₀ i.val i.property).choose ∈ F :=
      hA_sub_F θ₀ i.val i.property (hA_ne θ₀ i.val i.property).choose_spec
    simp only [F, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.2 (Or.inr (Or.inl heq))
  rw [hzero]; simp

end LeanResearch.Proposal3
