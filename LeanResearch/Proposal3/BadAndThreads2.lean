/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BadAndThreads1

/-!
# 好 `3`-核心度点与 `2⁺`-线串精细结构引理（`BadAndThreads2`：Lemmas 3.9–3.10 与 Corollary 3.11）

本模块对任意满足 `2 * p ≤ 5 * q`（`mad(G) < 5/2`）的极小反例，完成 Lu–Ying–Song 剩余结构引理的零 `sorry`
形式化证明：
1. `thread_reduction`（Lemma 3.9）：若 `coreDeg G u = 3` 且 `u` 同时关联 `2⁺`-线串 `v` 与 `1`-线串 `a`，
   则必有 `G.degree u = 4` 且 `v ∈ twoThreadNbrs G u`；
2. `one_thread_unique_of_two_thread` 与 `no_bad_nbr_of_two_and_one_thread`（Lemma 3.10a）：
   若 `G.degree u = 4, coreDeg G u = 3` 且 `u` 关联 `2`-线串与 `1`-线串，
   则 `u` 恰关联 `1` 条 `1`-线串且无坏核心邻点；
3. `no_one_thread_bad_neighbor`（Lemma 3.10b）：若 `coreDeg G u = 3`，`u` 关联 `2⁺`-线串且不关联
   `1`-线串，则 `u` 无坏核心邻点；
4. `good_coreDeg_three_long_thread_summary`（Corollary 3.11）：合并供 `12/5` 与 `22/9` 放电使用。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 0. 小型局部辅助引理 -/

/-- `u` 若有核心度 `3` 且含两个互异核心邻点 `v ≠ a`，则存在唯一第三个核心邻点 `x`。 -/
lemma exists_third_coreNbr {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v a : V}
    (hc3 : coreDeg G u = 3) (hv : v ∈ coreNbrs G u) (ha : a ∈ coreNbrs G u) (hva : v ≠ a) :
    ∃ x : V, x ∈ coreNbrs G u ∧ x ≠ v ∧ x ≠ a ∧ coreNbrs G u = {v, a, x} := by
  have hsub : ({v, a} : Finset V) ⊆ coreNbrs G u := by
    intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hv
    · exact ha
  have hcard1 : (coreNbrs G u \ {v, a}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hva]
    unfold coreDeg at hc3; omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨x, hx_eq⟩
  have hx_mem : x ∈ coreNbrs G u \ {v, a} := by rw [hx_eq]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx_mem
  refine ⟨x, hx_mem.1, hx_mem.2.1, hx_mem.2.2, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hv
    · exact ha
    · exact hx_mem.1
  · rw [Finset.card_insert_of_notMem (by simp [hva, Ne.symm hx_mem.2.1]),
        Finset.card_pair (Ne.symm hx_mem.2.2)]
    unfold coreDeg at hc3; omega

/-- 极小反例中，若 `v` 是 `u` 关联的长线串起点，则 `4 ≤ G.degree u`。 -/
lemma deg_ge_four_of_longThreadNbr {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v : V} (hdu3 : 3 ≤ G.degree u)
    (hv : v ∈ longThreadNbrs G u) : 4 ≤ G.degree u := by
  by_contra hlt; push Not at hlt
  have hdu3' : G.degree u = 3 := by omega
  simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hv
  rcases hv.2 with ⟨huv, hdv, w, hvw, _, hdw⟩
  exact no_three_vertex_two_thread hm hdu3' hdv hdw huv hvw

/-- 若 4-度点 `u` 的四个邻点 `n₁, n₂, n₃, n₄` 中前三个颜色两两互异，则无论第四个邻点染何色，`u` 均满足 PCF！ -/
lemma pcf_at_deg_four_of_three_distinct {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {u n₁ n₂ n₃ n₄ : V}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂)
    (hall : ∀ r, G.Adj u r → r = n₁ ∨ r = n₂ ∨ r = n₃ ∨ r = n₄)
    (hc12 : ψ n₁ ≠ ψ n₂) (hc13 : ψ n₁ ≠ ψ n₃) (hc23 : ψ n₂ ≠ ψ n₃) :
    ∃ y, G.Adj u y ∧ ∀ r, G.Adj u r → ψ r = ψ y → r = y := by
  by_cases h41 : ψ n₄ = ψ n₁
  · -- `ψ n₂` 既不同于 `ψ n₁ = ψ n₄` 也不同于 `ψ n₃`，故 `n₂` 唯一！
    refine ⟨n₂, h2, ?_⟩
    intro r hur hψr
    rcases hall r hur with hr | hr | hr | hr
    · exact False.elim (hc12 (hr ▸ hψr))
    · exact hr
    · exact False.elim (hc23 (hr ▸ hψr).symm)
    · exact False.elim (hc12 (h41.symm.trans (hr ▸ hψr)))
  · -- `ψ n₁` 既不同于 `ψ n₂, ψ n₃` 也不同于 `ψ n₄`，故 `n₁` 唯一！
    refine ⟨n₁, h1, ?_⟩
    intro r hur hψr
    rcases hall r hur with hr | hr | hr | hr
    · exact hr
    · exact False.elim (hc12 (hr ▸ hψr).symm)
    · exact False.elim (hc13 (hr ▸ hψr).symm)
    · exact False.elim (h41 (hr ▸ hψr))

/-- 若 `4`-元集 `L` 满足 `L \ {c₁, ω₁, z} = {β}` 与 `L \ {c₂, ω₂, z} = {β}` 且 `c₁ ≠ c₂`、
`ω₁ ≠ c₁`、`ω₂ ≠ c₂`，则必有 `ω₁ = c₂`, `ω₂ = c₁`, `z ∈ L`, `β ∈ L`, 且 `c₁, c₂, z, β` 四色互异！ -/
lemma four_set_sdiff_eq_singleton_pair {L : Finset ℕ} {c₁ c₂ ω₁ ω₂ z β : ℕ}
    (hL4 : L.card = 4) (hc12 : c₁ ≠ c₂)
    (h1 : L \ {c₁, ω₁, z} = {β}) (h2 : L \ {c₂, ω₂, z} = {β}) :
    ω₁ = c₂ ∧ ω₂ = c₁ ∧ z ∈ L ∧ β ∈ L ∧
      c₁ ≠ z ∧ c₁ ≠ β ∧ c₂ ≠ z ∧ c₂ ≠ β ∧ z ≠ β := by
  have hsub : ∀ {a b : ℕ}, L \ {a, b, z} = {β} →
      a ∈ L ∧ b ∈ L ∧ z ∈ L ∧ β ∈ L ∧
      a ≠ b ∧ a ≠ z ∧ b ≠ z ∧ β ≠ a ∧ β ≠ b ∧ β ≠ z ∧ L = {a, b, z, β} := by
    intro a b hEq
    have hβ_mem : β ∈ L \ {a, b, z} := by rw [hEq]; simp
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hβ_mem
    have h1card : (L \ {a, b, z}).card = 1 := by rw [hEq, Finset.card_singleton]
    have h2card := Finset.card_sdiff_add_card_inter L {a, b, z}
    have hle1 : (L ∩ {a, b, z}).card ≤ ({a, b, z} : Finset ℕ).card :=
      Finset.card_le_card (Finset.inter_subset_right (s₁ := L))
    have hle2 := card_triple_le a b z
    have hcard_tri : ({a, b, z} : Finset ℕ).card = 3 := by omega
    have hEqI : L ∩ {a, b, z} = {a, b, z} :=
      Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := L)) (by omega)
    have h3sub : ({a, b, z} : Finset ℕ) ⊆ L := by
      intro t ht; rw [← hEqI] at ht; exact (Finset.mem_inter.mp ht).1
    have hab : a ≠ b := by
      intro h; subst h
      have : ({a, a, z} : Finset ℕ) = {a, z} := by ext t; simp
      rw [this] at hcard_tri; have := Finset.card_le_two (a := a) (b := z); omega
    have haz : a ≠ z := by
      intro h; subst h
      have : ({a, b, a} : Finset ℕ) = {a, b} := by ext t; simp; tauto
      rw [this] at hcard_tri; have := Finset.card_le_two (a := a) (b := b); omega
    have hbz : b ≠ z := by
      intro h; subst h
      have : ({a, b, b} : Finset ℕ) = {a, b} := by ext t; simp
      rw [this] at hcard_tri; have := Finset.card_le_two (a := a) (b := b); omega
    have hL_eq : L = {a, b, z, β} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact h3sub (by simp)
        · exact h3sub (by simp)
        · exact h3sub (by simp)
        · exact hβ_mem.1
      · rw [Finset.card_insert_of_notMem (by simp [hab, haz, Ne.symm hβ_mem.2.1]),
            Finset.card_insert_of_notMem (by simp [hbz, Ne.symm hβ_mem.2.2.1]),
            Finset.card_pair (Ne.symm hβ_mem.2.2.2)]
        omega
    exact ⟨h3sub (by simp), h3sub (by simp), h3sub (by simp), hβ_mem.1,
      hab, haz, hbz, hβ_mem.2.1, hβ_mem.2.2.1, hβ_mem.2.2.2, hL_eq⟩
  rcases hsub h1 with ⟨hc1L, hω1L, hzL, hβL, hc1ω1, hc1z, hω1z, hβc1, hβω1, hβz, hL1⟩
  rcases hsub h2 with ⟨hc2L, hω2L, _, _, hc2ω2, hc2z, hω2z, hβc2, hβω2, _, hL2⟩
  have hω1_eq : ω₁ = c₂ := by
    have hc2_in : c₂ ∈ ({c₁, ω₁, z, β} : Finset ℕ) := by rw [← hL1]; exact hc2L
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc2_in
    rcases hc2_in with h | h | h | h
    · exact False.elim (hc12 h.symm)
    · exact h.symm
    · exact False.elim (hc2z h)
    · exact False.elim (hβc2 h.symm)
  have hω2_eq : ω₂ = c₁ := by
    have hc1_in : c₁ ∈ ({c₂, ω₂, z, β} : Finset ℕ) := by rw [← hL2]; exact hc1L
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc1_in
    rcases hc1_in with h | h | h | h
    · exact False.elim (hc12 h)
    · exact h.symm
    · exact False.elim (hc1z h)
    · exact False.elim (hβc1 h.symm)
  exact ⟨hω1_eq, hω2_eq, hzL, hβL, hc1z, Ne.symm hβc1, hc2z, Ne.symm hβc2, Ne.symm hβz⟩

/-! ## 1. Lemma 3.9（`thread_reduction`）：两步证明（先证 `d(u) = 4`，再排除 `3`-线串） -/

/-- Lemma 3.9 第一步：若 `coreDeg G u = 3` 且 `u` 同时关联 `2⁺`-线串与 `1`-线串，则 `G.degree u = 4`！ -/
lemma thread_reduction_deg_four {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a : V}
    (hc3 : coreDeg G u = 3) (hv : v ∈ longThreadNbrs G u) (ha : a ∈ oneThreadNbrs G u) :
    G.degree u = 4 := by
  classical
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hdu4 : 4 ≤ G.degree u := deg_ge_four_of_longThreadNbr hm hdu3 hv
  by_contra hne4
  have hdu5 : 5 ≤ G.degree u := by omega
  simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ha
  rcases hv.2 with ⟨huv, hdv, w, hvw, hwu, hdw⟩
  rcases ha.2 with ⟨hua, hda, p0, hap, hpu, hdp3⟩
  rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨z, hwz, hzv, hw_all⟩
  have hva : v ≠ a := fun h => by
    subst h; exact not_oneThread_and_longThread ha.2 hv.2
  have hv_core : v ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨huv, by omega⟩
  have ha_core : a ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hua, by omega⟩
  rcases exists_third_coreNbr hc3 hv_core ha_core hva with ⟨x, hx_core, hxv, hxa, hcore_eq⟩
  have hux : G.Adj u x := (mem_coreNbrs.mp hx_core).1
  have hdx2 : 2 ≤ G.degree x := (mem_coreNbrs.mp hx_core).2
  -- 关键互异性质
  have hwu_ne : w ≠ u := hwu
  have hwa : w ≠ a := fun h => no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw (h ▸ hua.symm)
  have hwx : w ≠ x := fun h => no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw (h ▸ hux.symm)
  have hzu : z ≠ u := fun h => no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw (h ▸ hwz)
  have hza : z ≠ a := fun h =>
    no_three_thread_same_anchor hm hdu3 hdv hdw hda huv hvw (h ▸ hwz) hua.symm hva
  have hzv_ne : z ≠ v := hzv
  have hzw : z ≠ w := (G.ne_of_adj hwz).symm
  have hdz2 : 2 ≤ G.degree z := by
    have h1 := degree_ge_one hm z
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree z = 1) hwz.symm; omega
  have hpv : p0 ≠ v := fun h => by subst h; omega
  have hpw : p0 ≠ w := fun h => by subst h; omega
  have hpa : p0 ≠ a := (G.ne_of_adj hap).symm
  let Y := leafNbrs G u
  have hY_card : Y.card = G.degree u - 3 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm u; omega
  have hv_not_Y : v ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have ha_not_Y : a ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hw_not_Y : w ∉ Y := fun h => by rw [mem_leafNbrs] at h; omega
  have hu_not_Y : u ∉ Y := fun h => G.ne_of_adj (mem_leafNbrs.mp h).1 rfl
  let S : Finset V := insert u (insert v (insert w (insert a Y)))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    refine ⟨(G.ne_of_adj hux).symm, hxv, hwx.symm, hxa, fun h => ?_⟩
    rw [mem_leafNbrs] at h; omega
  have hp_not_S : p0 ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    refine ⟨hpu, hpv, hpw, hpa, fun h => ?_⟩
    rw [mem_leafNbrs] at h; omega
  have hz_not_S : z ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    refine ⟨hzu, hzv_ne, hzw, hza, fun h => ?_⟩
    rw [mem_leafNbrs] at h; omega
  have hv_all : ∀ r, G.Adj v r → r = u ∨ r = w := by
    intro r hvr
    have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : r ∈ ({u, w} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v r).mpr hvr
    simpa using this
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = p0 := by
    intro r har
    have hNa := neighborFinset_eq_pair_of_deg_two hda hua.symm hap hpu.symm
    have : r ∈ ({u, p0} : Finset V) := by rw [← hNa]; exact (G.mem_neighborFinset a r).mpr har
    simpa using this
  have hu_all : ∀ r, G.Adj u r → r = v ∨ r = a ∨ r = x ∨ r ∈ Y := by
    intro r hur
    have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, h1⟩)))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hS_out : ∀ q0, q0 ∉ S → ∀ b ∈ S, G.Adj q0 b →
      (b = u ∧ q0 = x) ∨ (b = w ∧ q0 = z) ∨ (b = a ∧ q0 = p0) := by
    intro q0 hqS b hbS hqb
    simp only [S, Finset.mem_insert] at hbS
    rcases hbS with rfl | rfl | rfl | rfl | hbY
    · rcases hu_all q0 hqb.symm with rfl | rfl | rfl | hqY
      · exact False.elim (hqS (by simp [S]))
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hqS (by simp [S, hqY]))
    · rcases hv_all q0 hqb.symm with rfl | rfl <;> exact False.elim (hqS (by simp [S]))
    · rcases hw_all q0 hqb.symm with rfl | rfl
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases ha_all q0 hqb.symm with rfl | rfl
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · have hL := mem_leafNbrs.mp hbY
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hqS (((huniq q0 hqb.symm).trans (huniq u hL.1.symm).symm) ▸ huS))
  -- 证明 `x, p0, z` 在 `G - S` 中全非孤立（即使它们重合！）
  have hnoniso_of_deg : ∀ q0, q0 ∉ S →
      (q0 = z → G.degree z = 2 → ∃ r, r ∉ S ∧ G.Adj z r) →
      (3 ≤ G.degree q0 → (q0 = z → 4 ≤ G.degree z) → ∃ r, r ∉ S ∧ G.Adj q0 r) := by
    intro q0 hqS _ hdq3 hqz4
    by_cases hqz : q0 = z
    · subst q0
      have hdz4 := hqz4 rfl
      have hlt : ({u, w, a} : Finset V).card < (G.neighborFinset z).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := card_triple_le u w a; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out z hqS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hrn.1 rfl
      · exact hrn.2.1 rfl
      · exact hrn.2.2 rfl
    · have hlt : ({u, a} : Finset V).card < (G.neighborFinset q0).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := u) (b := a); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out q0 hqS r hrS hr with ⟨rfl, _⟩ | ⟨_, hEq⟩ | ⟨rfl, _⟩
      · exact hrn.1 rfl
      · exact hqz hEq
      · exact hrn.2 rfl
  have hdz4_of_ge3 : 3 ≤ G.degree z → 4 ≤ G.degree z := by
    intro h3; by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega) hdw hdv hwz.symm hvw.symm
  have hnoniso_z : ∃ r, r ∉ S ∧ G.Adj z r := by
    by_cases hdz2' : G.degree z = 2
    · rcases exists_other_neighbor_of_deg_two hdz2' hwz.symm with ⟨r, hzr, hrw, _⟩
      refine ⟨r, ?_, hzr⟩
      intro hrS
      rcases hS_out z hz_not_S r hrS hzr with ⟨hru, _⟩ | ⟨hrw', _⟩ | ⟨hra, _⟩
      · subst r; exact no_three_thread_same_anchor hm hdu3 hdv hdw hdz2' huv hvw hwz hzr hzv.symm
      · exact hrw hrw'
      · subst r
        exact no_four_path_of_deg_two hm hdv hdw hdz2' hda hvw hwz hzr hzv.symm hva hwa
    · exact hnoniso_of_deg z hz_not_S (fun _ h => False.elim (hdz2' h)) (by omega)
        (fun _ => hdz4_of_ge3 (by omega))
  have hnoniso_p : ∃ r, r ∉ S ∧ G.Adj p0 r :=
    hnoniso_of_deg p0 hp_not_S (fun _ _ => hnoniso_z) hdp3
      (fun h => hdz4_of_ge3 (by rw [← h]; exact hdp3))
  have hnoniso_x : ∃ r, r ∉ S ∧ G.Adj x r := by
    by_cases hdx2' : G.degree x = 2
    · rcases exists_other_neighbor_of_deg_two hdx2' hux.symm with ⟨r, hxr, hru, _⟩
      refine ⟨r, ?_, hxr⟩
      intro hrS
      rcases hS_out x hx_not_S r hrS hxr with ⟨hru', _⟩ | ⟨hrw, hxz⟩ | ⟨hra, hxp⟩
      · exact hru hru'
      · subst r; exact no_three_thread_same_anchor hm hdu3 hdv hdw hdx2' huv hvw
          (hxz ▸ hwz) hux.symm hxv.symm
      · subst r; exact no_two_thread_same_anchor hm hdu3 hdx2' hda hux hxr hua.symm
    · exact hnoniso_of_deg x hx_not_S (fun _ _ => hnoniso_z) (by omega)
        (fun h => hdz4_of_ge3 (by rw [← h]; omega))
  -- 取 `G - S` 容许染色并展开 `k ≥ 5` 双计数！
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  have hLa : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  let β := adm.φ x
  let C : Finset ℕ := L u \ {β, adm.φs x, adm.φ p0}
  have hC : G.degree u - 2 ≤ C.card := by
    dsimp only [C]
    have := card_sdiff_ge (L u) {β, adm.φs x, adm.φ p0}
    have := card_triple_le β (adm.φs x) (adm.φ p0); omega
  have hβ_not_C : β ∉ C := by simp [C]
  have hc_ex : ∀ α : ℕ, ∃ c ∈ L w, c ≠ α ∧ c ≠ adm.φ z ∧ c ≠ adm.φs z := by
    intro α
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {α, adm.φ z, adm.φs z})
      (by have := card_triple_le α (adm.φ z) (adm.φs z); omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → ℕ := fun α => (hc_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w ∧ cFun α ≠ α ∧ cFun α ≠ adm.φ z ∧ cFun α ≠ adm.φs z :=
    fun α => (hc_ex α).choose_spec
  let J : Finset V := insert v (insert a Y)
  have hJ_card : J.card = G.degree u - 1 := by
    dsimp only [J]
    rw [Finset.card_insert_of_notMem (by simp [hva, hv_not_Y]),
        Finset.card_insert_of_notMem ha_not_Y, hY_card]
    omega
  let A : ℕ → V → Finset ℕ := fun α r =>
    if r = v then L v \ {α, cFun α, adm.φ z}
    else if r = a then L a \ {α, adm.φ p0, adm.φs p0}
    else L r \ {α}
  have hA_ne : ∀ α r (hr : r ∈ J), (A α r).Nonempty := by
    intro α r hr; rw [← Finset.card_pos]
    dsimp only [A]; split_ifs with hrv hra
    · have := card_sdiff_ge (L v) {α, cFun α, adm.φ z}
      have := card_triple_le α (cFun α) (adm.φ z); omega
    · have := card_sdiff_ge (L a) {α, adm.φ p0, adm.φs p0}
      have := card_triple_le α (adm.φ p0) (adm.φs p0); omega
    · have hrY : r ∈ Y := by
        simp only [J, Finset.mem_insert] at hr
        exact (hr.resolve_left hrv).resolve_left hra
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
      have := card_sdiff_ge (L r) {α}; simp only [Finset.card_singleton] at this; omega
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ f : {r : V // r ∈ J} → ℕ, IsPCFRep (fun i => A α i.val) [β] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    have hvJ : v ∈ J := Finset.mem_insert_self v _
    have haJ : a ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_self a Y)
    have hfv : f ⟨v, hvJ⟩ ∈ L v \ {α, cFun α, adm.φ z} := by simpa [A] using hf_mem ⟨v, hvJ⟩
    have hfa : f ⟨a, haJ⟩ ∈ L a \ {α, adm.φ p0, adm.φs p0} := by
      simpa [A, hva.symm] using hf_mem ⟨a, haJ⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hfv hfa
    let ψ : V → ℕ := fun r =>
      if r = u then α
      else if r = w then cFun α
      else if hrJ : r ∈ J then f ⟨r, hrJ⟩
      else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψw : ψ w = cFun α := by simp [ψ, hwu_ne]
    have hψJ : ∀ r (hr : r ∈ J), ψ r = f ⟨r, hr⟩ := by
      intro r hr
      have hru : r ≠ u := by
        simp only [J, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hrY
        · exact (G.ne_of_adj huv).symm
        · exact (G.ne_of_adj hua).symm
        · exact fun h => hu_not_Y (h ▸ hrY)
      have hrw : r ≠ w := by
        simp only [J, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hrY
        · exact G.ne_of_adj hvw
        · exact hwa.symm
        · exact fun h => hw_not_Y (h ▸ hrY)
      simp only [ψ, hru, hrw, ite_false, hr, dite_true]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, not_or] at hr
      have hrJ : r ∉ J := by simp [J, hr.2.1, hr.2.2.2.1, hr.2.2.2.2]
      simp only [ψ, hr.1, hr.2.2.1, hrJ, ite_false, dite_false]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr
      simp only [S, Finset.mem_insert] at hr
      rcases hr with rfl | hrv | rfl | hra | hrY
      · rw [hψu]; exact hα.1
      · rw [hrv, hψJ v hvJ]; exact hfv.1
      · rw [hψw]; exact (hcFun_spec α).1
      · rw [hra, hψJ a haJ]; exact hfa.1
      · have hrJ : r ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hrY)
        have hrv' : r ≠ v := fun h => hv_not_Y (h ▸ hrY)
        have hra' : r ≠ a := fun h => ha_not_Y (h ▸ hrY)
        have hm' := hf_mem ⟨r, hrJ⟩; simp only [A, hrv', hra', ite_false, Finset.mem_sdiff] at hm'
        rw [hψJ r hrJ]; exact hm'.1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert] at ha'
        rcases ha' with hau | hav | haw | haa | haY
        · subst a'
          rcases hu_all b' hab with hbv | hba | hbx | hbY
          · rw [hbv, hψu, hψJ v hvJ]; exact Ne.symm hfv.2.1
          · rw [hba, hψu, hψJ a haJ]; exact Ne.symm hfa.2.1
          · rw [hbx, hψu, hψ_out x hx_not_S]; exact hα.2.1
          · have hbJ : b' ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hbY)
            have hbv' : b' ≠ v := fun h => hv_not_Y (h ▸ hbY)
            have hba' : b' ≠ a := fun h => ha_not_Y (h ▸ hbY)
            have hm' := hf_mem ⟨b', hbJ⟩
            simp only [A, hbv', hba', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
            rw [hψu, hψJ b' hbJ]; exact Ne.symm hm'.2
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψJ v hvJ, hψu]; exact hfv.2.1
          · rw [hb, hψJ v hvJ, hψw]; exact hfv.2.2.1
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψJ v hvJ]; exact Ne.symm hfv.2.2.1
          · rw [hb, hψw, hψ_out z hz_not_S]; exact (hcFun_spec α).2.2.1
        · subst a'
          rcases ha_all b' hab with hb | hb
          · rw [hb, hψJ a haJ, hψu]; exact hfa.2.1
          · rw [hb, hψJ a haJ, hψ_out p0 hp_not_S]; exact hfa.2.2.1
        · have haL := mem_leafNbrs.mp haY
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u haL.1.symm).symm
          have haJ' : a' ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haY)
          have hav' : a' ≠ v := fun h => hv_not_Y (h ▸ haY)
          have haa' : a' ≠ a := fun h => ha_not_Y (h ▸ haY)
          have hm' := hf_mem ⟨a', haJ'⟩
          simp only [A, hav', haa', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
          rw [hb, hψJ a' haJ', hψu]; exact hm'.2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro q0 hqS _ b hbS hqb
      rcases hS_out q0 hqS b hbS hqb with ⟨hbu, hqx⟩ | ⟨hbw, hqz⟩ | ⟨hba, hqp⟩
      · rw [hbu, hqx, hψu]; exact hα.2.2.1
      · rw [hbw, hqz, hψw]; exact (hcFun_spec α).2.2.2
      · rw [hba, hqp, hψJ a haJ]; exact hfa.2.2.2
    · intro q0 hqS hiso ⟨b, hqb⟩
      have hbS : b ∈ S := by by_contra h; exact hiso b h hqb
      rcases hS_out q0 hqS b hbS hqb with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rcases hnoniso_x with ⟨r, hrS, hxr⟩; exact False.elim (hiso r hrS hxr)
      · rcases hnoniso_z with ⟨r, hrS, hzr⟩; exact False.elim (hiso r hrS hzr)
      · rcases hnoniso_p with ⟨r, hrS, hpr⟩; exact False.elim (hiso r hrS hpr)
    · intro r hrS _
      simp only [S, Finset.mem_insert] at hrS
      rcases hrS with hru | hrv | hrw | hra | hrY
      · subst r
        by_cases hγβ : γ = β
        · subst hγβ
          have hcnt : ([β] : List ℕ).count β = 1 := by simp
          have hzero : (Finset.univ.filter (fun i : {t // t ∈ J} => f i = β)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨x, hux, ?_⟩
          intro t hut hψt
          rcases hu_all t hut with htv | hta | htx | htY
          · rw [htv, hψJ v hvJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨v, hvJ⟩) hψt)
          · rw [hta, hψJ a haJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨a, haJ⟩) hψt)
          · exact htx
          · have htJ : t ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htY)
            rw [hψJ t htJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨t, htJ⟩) hψt)
        · have hcnt : ([β] : List ℕ).count γ = 0 := by
            rw [List.count_eq_zero]; simpa using hγβ
          have hone : (Finset.univ.filter (fun i : {t // t ∈ J} => f i = γ)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨⟨t₀, ht₀⟩, ht₀_eq⟩
          have ht₀_col : f ⟨t₀, ht₀⟩ = γ := by
            have : (⟨t₀, ht₀⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) := by
              rw [ht₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          have hut0 : G.Adj u t₀ := by
            simp only [J, Finset.mem_insert] at ht₀
            rcases ht₀ with rfl | rfl | htY
            · exact huv
            · exact hua
            · exact (mem_leafNbrs.mp htY).1
          refine ⟨t₀, hut0, ?_⟩
          intro t hut hψt
          rcases hu_all t hut with htv | hta | htx | htY
          · rw [htv, hψJ v hvJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨v, hvJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact htv.trans (congrArg Subtype.val this)
          · rw [hta, hψJ a haJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨a, haJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact hta.trans (congrArg Subtype.val this)
          · rw [htx, hψ_out x hx_not_S, hψJ t₀ ht₀, ht₀_col] at hψt
            exact False.elim (hγβ hψt.symm)
          · have htJ : t ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htY)
            rw [hψJ t htJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨t, htJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact congrArg Subtype.val this
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact (hcFun_spec α).2.1.symm)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψJ v hvJ, hψ_out z hz_not_S]; exact hfv.2.2.2)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hda hua.symm hap hpu.symm
          (by rw [hψu, hψ_out p0 hp_not_S]; exact hα.2.2.2)
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
  -- 双计数：`3 * (k - 2) ≤ 3 * |C| ≤ ∑ q_α ≤ 2 * (k - 3) + 2 + 3 = 2k - 1` → 强制 `k = 5` 且处处取等！
  have hlower : 3 * C.card ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
    calc 3 * C.card = ∑ _α ∈ C, 3 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
        apply Finset.sum_le_sum; intro α hα
        have : Nonempty {r : V // r ∈ J} := ⟨⟨v, Finset.mem_insert_self v _⟩⟩
        have hq3 := (no_pcfRep_single_bounds (fun i : {r // r ∈ J} => hA_ne α i.val i.property)
          (hno_rep α hα)).2.2.1 (by rw [Fintype.card_coe, hJ_card]; omega)
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
  have hterm_v : (C.filter (fun α => (A α v).card = 1)).card ≤ 3 := by
    have hEq : C.filter (fun α => (A α v).card = 1) =
        C.filter (fun α => (L v \ {α, cFun α, adm.φ z}).card = 1) := by congr 1; ext α; simp [A]
    rw [hEq]; exact (card_filter_sdiff_triple_eq_one_le C (L v) hLv cFun (adm.φ z)).1
  have hterm_a : (C.filter (fun α => (A α a).card = 1)).card ≤ 2 := by
    have hEq : C.filter (fun α => (A α a).card = 1) =
        C.filter (fun α => (L a \ {α, adm.φ p0, adm.φs p0}).card = 1) := by
      congr 1; ext α; simp [A, hva.symm]
    rw [hEq]; exact (card_filter_sdiff_two_fixed_eq_one_le C (L a) hLa (adm.φ p0) (adm.φs p0)).1
  have hterm_Y : ∀ r ∈ Y, (C.filter (fun α => (A α r).card = 1)).card ≤ 2 := by
    intro r hr
    have hrv : r ≠ v := fun h => hv_not_Y (h ▸ hr)
    have hra : r ≠ a := fun h => ha_not_Y (h ▸ hr)
    have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
    have hEq : C.filter (fun α => (A α r).card = 1) =
        C.filter (fun α => (L r \ {α}).card = 1) := by congr 1; ext α; simp [A, hrv, hra]
    rw [hEq]; exact (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).1
  have hsplit : ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card =
      (C.filter (fun α => (A α v).card = 1)).card +
      (C.filter (fun α => (A α a).card = 1)).card +
      ∑ r ∈ Y, (C.filter (fun α => (A α r).card = 1)).card := by
    rw [sum_filter_card_comm]
    dsimp only [J]
    rw [Finset.sum_insert (by simp [hva, hv_not_Y]), Finset.sum_insert ha_not_Y]
    omega
  have hsumY_le : ∑ r ∈ Y, (C.filter (fun α => (A α r).card = 1)).card ≤ 2 * Y.card := by
    calc ∑ r ∈ Y, (C.filter (fun α => (A α r).card = 1)).card
        ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum hterm_Y
      _ = 2 * Y.card := by simp [mul_comm]
  -- 必须 `G.degree u = 5`, `|C| = 3`, 且三项分别取等 `3, 2, 2 * |Y|`！
  have hv_eq3 : (C.filter (fun α => (A α v).card = 1)).card = 3 := by omega
  have ha_eq2 : (C.filter (fun α => (A α a).card = 1)).card = 2 := by omega
  have hY_eq : ∑ r ∈ Y, (C.filter (fun α => (A α r).card = 1)).card = 2 * Y.card := by omega
  -- 于是对每个 `r ∈ J`，`A α r ⊆ C`（不含 `β`！），任取 `α₀ ∈ C` 即得 `β` 唯一！
  have hA_sub_C : ∀ α (r : V), r ∈ J → A α r ⊆ C := by
    intro α r hr
    simp only [J, Finset.mem_insert] at hr
    rcases hr with hrv | hra | hrY
    · subst r
      have hEq : C.filter (fun γ => (A γ v).card = 1) =
          C.filter (fun γ => (L v \ {γ, cFun γ, adm.φ z}).card = 1) := by congr 1; ext γ; simp [A]
      rw [hEq] at hv_eq3
      have hsub := (card_filter_sdiff_triple_eq_one_le C (L v) hLv cFun (adm.φ z)).2 hv_eq3
      intro c hc; simp only [A, ite_true, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hc
      exact hsub.2 (Finset.mem_sdiff.mpr ⟨hc.1, by simp [hc.2.2.2]⟩)
    · subst r
      have hEq : C.filter (fun γ => (A γ a).card = 1) =
          C.filter (fun γ => (L a \ {γ, adm.φ p0, adm.φs p0}).card = 1) := by
        congr 1; ext γ; simp [A, hva.symm]
      rw [hEq] at ha_eq2
      have hsub :=
        (card_filter_sdiff_two_fixed_eq_one_le C (L a) hLa (adm.φ p0) (adm.φs p0)).2 ha_eq2
      intro c hc; simp only [A, hva.symm, ite_false, ite_true, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hc
      exact hsub.2.2.2 (Finset.mem_sdiff.mpr ⟨hc.1, by simp [hc.2.2.1, hc.2.2.2]⟩)
    · have hrv : r ≠ v := fun h => hv_not_Y (h ▸ hrY)
      have hra : r ≠ a := fun h => ha_not_Y (h ▸ hrY)
      have heq2 : (C.filter (fun γ => (A γ r).card = 1)).card = 2 := by
        by_contra hne2
        have hlt2 : (C.filter (fun γ => (A γ r).card = 1)).card < 2 := by
          have := hterm_Y r hrY; omega
        have hlt_sum : ∑ s ∈ Y, (C.filter (fun γ => (A γ s).card = 1)).card < ∑ _s ∈ Y, 2 :=
          Finset.sum_lt_sum hterm_Y ⟨r, hrY, hlt2⟩
        simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrY).2]
      have hEq : C.filter (fun γ => (A γ r).card = 1) =
          C.filter (fun γ => (L r \ {γ}).card = 1) := by congr 1; ext γ; simp [A, hrv, hra]
      rw [hEq] at heq2
      have hsub := (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).2 heq2
      intro c hc; simp only [A, hrv, hra, ite_false, Finset.mem_sdiff] at hc; exact hsub.2 hc.1
  rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α₀, hα₀⟩
  apply hno_rep α₀ hα₀
  refine ⟨fun i => (hA_ne α₀ i.val i.property).choose,
    fun i => (hA_ne α₀ i.val i.property).choose_spec, β, ?_⟩
  have hzero : (Finset.univ.filter (fun i : {r // r ∈ J} =>
      (hA_ne α₀ i.val i.property).choose = β)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ heq
    exact hβ_not_C (heq ▸ hA_sub_C α₀ i.val i.property (hA_ne α₀ i.val i.property).choose_spec)
  rw [hzero]; simp

/-- Lemma 3.9 第二步：若 `G.degree u = 4, coreDeg G u = 3` 且 `u` 关联 `1`-线串，则 `u` 不关联 `3`-线串！ -/
lemma thread_reduction_not_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a : V}
    (hdu4 : G.degree u = 4) (hc3 : coreDeg G u = 3)
    (hv : v ∈ threeThreadNbrs G u) (ha : a ∈ oneThreadNbrs G u) : False := by
  classical
  simp only [threeThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ha
  rcases hv.2 with ⟨huv, hdv, w, z, r0, hvw, hwu, hdw, hwz, hzv, hdz, hzr, hrw, hdr3⟩
  rcases ha.2 with ⟨hua, hda, p0, hap, hpu, hdp3⟩
  have hdr4 : 4 ≤ G.degree r0 := by
    by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega) hdz hdw hzr.symm hwz.symm
  have hY1 : (leafNbrs G u).card = 1 := by have := coreDeg_add_leafNbrs hm u; omega
  rcases Finset.card_eq_one.mp hY1 with ⟨y, hy_eq⟩
  have hy_mem : y ∈ leafNbrs G u := by rw [hy_eq]; simp
  rw [mem_leafNbrs] at hy_mem
  rcases hy_mem with ⟨huy, hdy⟩
  have hva : v ≠ a := fun h => by
    subst h
    exact not_oneThread_and_longThread ha.2 ⟨huv, hdv, w, hvw, hwu, hdw⟩
  have hv_core : v ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨huv, by omega⟩
  have ha_core : a ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hua, by omega⟩
  rcases exists_third_coreNbr hc3 hv_core ha_core hva with ⟨x, hx_core, hxv, hxa, hcore_eq⟩
  have hux : G.Adj u x := (mem_coreNbrs.mp hx_core).1
  have hdx2 : 2 ≤ G.degree x := (mem_coreNbrs.mp hx_core).2
  -- 6 个待删点 `{u, v, w, z, a, y}` 两两互异，且均异于 `{x, p0, r0}`！
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have hwa : w ≠ a := fun h =>
    no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hua.symm)
  have hwx : w ≠ x := fun h =>
    no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hux.symm)
  have hzu : z ≠ u := fun h => no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hwz)
  have hza : z ≠ a := fun h =>
    no_three_thread_same_anchor hm (by omega) hdv hdw hda huv hvw (h ▸ hwz) hua.symm hva
  have hzx : z ≠ x := fun h => by
    subst h
    exact no_three_thread_same_anchor hm (by omega) hdv hdw hdz huv hvw hwz hux.symm hxv.symm
  have hru : r0 ≠ u := fun h =>
    no_three_thread_same_anchor hm (by omega) hdv hdw hdz huv hvw hwz (h ▸ hzr) hzv.symm
  have hrv : r0 ≠ v := fun h => by subst h; omega
  have hra : r0 ≠ a := fun h => by subst h; omega
  have hpv : p0 ≠ v := fun h => by subst h; omega
  have hpw : p0 ≠ w := fun h => by subst h; omega
  have hpz : p0 ≠ z := fun h => by subst h; omega
  have hpa : p0 ≠ a := (G.ne_of_adj hap).symm
  have hvy : v ≠ y := fun h => by subst h; omega
  have hwy : w ≠ y := fun h => by subst h; omega
  have hzy : z ≠ y := fun h => by subst h; omega
  have hay : a ≠ y := fun h => by subst h; omega
  have huy_ne : u ≠ y := G.ne_of_adj huy
  have hxy : x ≠ y := fun h => by subst h; omega
  have hpy : p0 ≠ y := fun h => by subst h; omega
  have hry : r0 ≠ y := fun h => by subst h; omega
  have hvw_ne : v ≠ w := G.ne_of_adj hvw
  have hwz_ne : w ≠ z := G.ne_of_adj hwz
  have hzr_ne : z ≠ r0 := G.ne_of_adj hzr
  let S : Finset V := {u, v, w, z, a, y}
  have huS : u ∈ S := by simp [S]
  have hx_not_S : x ∉ S := by simp [S, (G.ne_of_adj hux).symm, hxv, hwx.symm, hzx.symm, hxa, hxy]
  have hp_not_S : p0 ∉ S := by simp [S, hpu, hpv, hpw, hpz, hpa, hpy]
  have hr_not_S : r0 ∉ S := by simp [S, hru, hrv, hrw, hzr_ne.symm, hra, hry]
  have hv_all : ∀ t, G.Adj v t → t = u ∨ t = w := by
    intro t ht; have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : t ∈ ({u, w} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v t).mpr ht
    simpa using this
  have hw_all : ∀ t, G.Adj w t → t = v ∨ t = z := by
    intro t ht; have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
    have : t ∈ ({v, z} : Finset V) := by rw [← hNw]; exact (G.mem_neighborFinset w t).mpr ht
    simpa using this
  have hz_all : ∀ t, G.Adj z t → t = w ∨ t = r0 := by
    intro t ht; have hNz := neighborFinset_eq_pair_of_deg_two hdz hwz.symm hzr hrw.symm
    have : t ∈ ({w, r0} : Finset V) := by rw [← hNz]; exact (G.mem_neighborFinset z t).mpr ht
    simpa using this
  have ha_all : ∀ t, G.Adj a t → t = u ∨ t = p0 := by
    intro t ht; have hNa := neighborFinset_eq_pair_of_deg_two hda hua.symm hap hpu.symm
    have : t ∈ ({u, p0} : Finset V) := by rw [← hNa]; exact (G.mem_neighborFinset a t).mpr ht
    simpa using this
  have hy_only : ∀ t, G.Adj y t → t = u := by
    rcases exists_unique_neighbor_of_deg_one hdy with ⟨t0, _, huniq⟩
    exact fun t ht => (huniq t ht).trans (huniq u huy.symm).symm
  have hu_all : ∀ t, G.Adj u t → t = v ∨ t = a ∨ t = x ∨ t = y := by
    intro t ht
    have hdt := degree_ge_one hm t
    by_cases h1 : G.degree t = 1
    · have : t ∈ ({y} : Finset V) := by rw [← hy_eq]; exact mem_leafNbrs.mpr ⟨ht, h1⟩
      exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp this)))
    · have hc : t ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨ht, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hS_out : ∀ q0, q0 ∉ S → ∀ b ∈ S, G.Adj q0 b →
      (b = u ∧ q0 = x) ∨ (b = z ∧ q0 = r0) ∨ (b = a ∧ q0 = p0) := by
    intro q0 hqS b hbS hqb
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hbS
    rcases hbS with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hu_all q0 hqb.symm with rfl | rfl | rfl | rfl
      · exact False.elim (hqS (by simp [S]))
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hqS (by simp [S]))
    · rcases hv_all q0 hqb.symm with rfl | rfl <;> exact False.elim (hqS (by simp [S]))
    · rcases hw_all q0 hqb.symm with rfl | rfl <;> exact False.elim (hqS (by simp [S]))
    · rcases hz_all q0 hqb.symm with rfl | rfl
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases ha_all q0 hqb.symm with rfl | rfl
      · exact False.elim (hqS (by simp [S]))
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact False.elim (hqS ((hy_only q0 hqb.symm) ▸ huS))
  -- 证明 `x, p0, r0` 在 `G - S` 中均非孤立！
  have hnoniso_r : ∃ t, t ∉ S ∧ G.Adj r0 t := by
    have hlt : ({u, z, a} : Finset V).card < (G.neighborFinset r0).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := card_triple_le u z a; omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨t, ht, htn⟩
    rw [SimpleGraph.mem_neighborFinset] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htn
    refine ⟨t, ?_, ht⟩
    intro htS
    rcases hS_out r0 hr_not_S t htS ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact htn.1 rfl
    · exact htn.2.1 rfl
    · exact htn.2.2 rfl
  have hnoniso_p : ∃ t, t ∉ S ∧ G.Adj p0 t := by
    by_cases hpr : p0 = r0
    · rw [hpr]; exact hnoniso_r
    · have hlt : ({u, a} : Finset V).card < (G.neighborFinset p0).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := u) (b := a); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨t, ht, htn⟩
      rw [SimpleGraph.mem_neighborFinset] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htn
      refine ⟨t, ?_, ht⟩
      intro htS
      rcases hS_out p0 hp_not_S t htS ht with ⟨rfl, _⟩ | ⟨_, hEq⟩ | ⟨rfl, _⟩
      · exact htn.1 rfl
      · exact hpr hEq
      · exact htn.2 rfl
  have hnoniso_x : ∃ t, t ∉ S ∧ G.Adj x t := by
    by_cases hxr : x = r0
    · rw [hxr]; exact hnoniso_r
    · by_cases hdx2' : G.degree x = 2
      · rcases exists_other_neighbor_of_deg_two hdx2' hux.symm with ⟨t, hxt, htu, _⟩
        refine ⟨t, ?_, hxt⟩
        intro htS
        rcases hS_out x hx_not_S t htS hxt with ⟨htu', _⟩ | ⟨_, hEq⟩ | ⟨hta, _⟩
        · exact htu htu'
        · exact hxr hEq
        · subst t; exact no_two_thread_same_anchor hm (by omega) hdx2' hda hux hxt hua.symm
      · have hlt : ({u, a} : Finset V).card < (G.neighborFinset x).card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          have := Finset.card_le_two (a := u) (b := a); omega
        rcases exists_mem_sdiff_of_lt hlt with ⟨t, ht, htn⟩
        rw [SimpleGraph.mem_neighborFinset] at ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htn
        refine ⟨t, ?_, ht⟩
        intro htS
        rcases hS_out x hx_not_S t htS ht with ⟨rfl, _⟩ | ⟨_, hEq⟩ | ⟨rfl, _⟩
        · exact htn.1 rfl
        · exact hxr hEq
        · exact htn.2 rfl
  -- 取 `G - S` 容许染色并固定临时颜色 `ζ ∈ L z \ {φ r0, φ* r0}`！
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  have hLz : (L z).card = 4 := by rw [hm.list_card z]; simp [kappa, hdz]
  have hLa : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLy : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  let ρ := adm.φ r0
  let τ := adm.φs r0
  let β := adm.φ x
  rcases exists_mem_sdiff_of_lt (A := L z) (B := {ρ, τ})
    (by have := Finset.card_le_two (a := ρ) (b := τ); omega) with ⟨ζ, hζL, hζn⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hζn
  -- 通用 6-点延拓构造器：给定 `(cu, cy, ca, cv, cw, cz)` 满足局部条件即得矛盾！
  have hcontra : ∀ (cu cy ca cv cw cz : ℕ),
      cu ∈ L u → cy ∈ L y → ca ∈ L a → cv ∈ L v → cw ∈ L w → cz ∈ L z →
      cu ≠ β → cu ≠ adm.φs x → cu ≠ adm.φ p0 →
      cy ≠ cu → ca ≠ cu → ca ≠ adm.φ p0 → ca ≠ adm.φs p0 →
      cv ≠ cu → cv ≠ cw → cw ≠ cu → cw ≠ cz → cw ≠ ρ →
      cz ≠ ρ → cz ≠ τ → cv ≠ cz →
      (∃ c : ℕ, ([cy, ca, cv, β] : List ℕ).count c = 1) → False := by
    intro cu cy ca cv cw cz hcu hcy hca hcv hcw hcz
      hcuβ hcuφx hcup hcyu hcau hcap hcaφp hcvu hcvw hcwu hcwz hcwρ hczρ hczτ hcvz ⟨γ, hγ⟩
    let ψ : V → ℕ := fun t =>
      if t = u then cu else if t = v then cv else if t = w then cw
      else if t = z then cz else if t = a then ca else if t = y then cy else adm.φ t
    have hψu : ψ u = cu := by simp [ψ]
    have hψv : ψ v = cv := by simp [ψ, huv_ne.symm]
    have hψw : ψ w = cw := by simp [ψ, hwu, hvw_ne.symm]
    have hψz : ψ z = cz := by simp [ψ, hzu, hzv, hwz_ne.symm]
    have hψa : ψ a = ca := by simp [ψ, (G.ne_of_adj hua).symm, hva.symm, hwa.symm, hza.symm]
    have hψy : ψ y = cy := by simp [ψ, huy_ne.symm, hvy.symm, hwy.symm, hzy.symm, hay.symm]
    have hψ_out : ∀ t, t ∉ S → ψ t = adm.φ t := by
      intro t ht; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      simp [ψ, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro t ht; simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hψu]; exact hcu
      · rw [hψv]; exact hcv
      · rw [hψw]; exact hcw
      · rw [hψz]; exact hcz
      · rw [hψa]; exact hca
      · rw [hψy]; exact hcy
    · intro t₁ t₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with h1 | h1 | h1 | h1 | h1 | h1
        · subst a'
          rcases hu_all b' hab with hb | hb | hb | hb
          · rw [hb, hψu, hψv]; exact hcvu.symm
          · rw [hb, hψu, hψa]; exact hcau.symm
          · rw [hb, hψu, hψ_out x hx_not_S]; exact hcuβ
          · rw [hb, hψu, hψy]; exact hcyu.symm
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψv, hψu]; exact hcvu
          · rw [hb, hψv, hψw]; exact hcvw
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψv]; exact hcvw.symm
          · rw [hb, hψw, hψz]; exact hcwz
        · subst a'
          rcases hz_all b' hab with hb | hb
          · rw [hb, hψz, hψw]; exact hcwz.symm
          · rw [hb, hψz, hψ_out r0 hr_not_S]; exact hczρ
        · subst a'
          rcases ha_all b' hab with hb | hb
          · rw [hb, hψa, hψu]; exact hcau
          · rw [hb, hψa, hψ_out p0 hp_not_S]; exact hcap
        · subst a'
          rw [hy_only b' hab, hψy, hψu]; exact hcyu
      rcases hor with h1 | h2
      · exact hcase t₁ t₂ h12 h1
      · exact (hcase t₂ t₁ h12.symm h2).symm
    · intro q0 hqS _ b hbS hqb
      rcases hS_out q0 hqS b hbS hqb with ⟨hbu, hqx⟩ | ⟨hbz, hqr⟩ | ⟨hba, hqp⟩
      · rw [hbu, hqx, hψu]; exact hcuφx
      · rw [hbz, hqr, hψz]; exact hczτ
      · rw [hba, hqp, hψa]; exact hcaφp
    · intro q0 hqS hiso ⟨b, hqb⟩
      have hbS : b ∈ S := by by_contra h; exact hiso b h hqb
      rcases hS_out q0 hqS b hbS hqb with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rcases hnoniso_x with ⟨t, htS, hxt⟩; exact False.elim (hiso t htS hxt)
      · rcases hnoniso_r with ⟨t, htS, hrt⟩; exact False.elim (hiso t htS hrt)
      · rcases hnoniso_p with ⟨t, htS, hpt⟩; exact False.elim (hiso t htS hpt)
    · intro t htS _
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at htS
      rcases htS with h1 | h1 | h1 | h1 | h1 | h1
      · subst t
        -- 利用 `[cy, ca, cv, β].count γ = 1` 找出 `u` 的唯一邻点！
        have hcnt : (if cy = γ then 1 else 0) + (if ca = γ then 1 else 0) +
            (if cv = γ then 1 else 0) + (if β = γ then 1 else 0) = 1 := by
          simp only [List.count_cons, List.count_nil, beq_iff_eq] at hγ
          omega
        by_cases hcyγ : cy = γ
        · have hcaγ : ca ≠ γ := by simp only [hcyγ, ite_true] at hcnt; split_ifs at hcnt <;> omega
          have hcvγ : cv ≠ γ := by simp only [hcyγ, ite_true] at hcnt; split_ifs at hcnt <;> omega
          have hβγ : β ≠ γ := by simp only [hcyγ, ite_true] at hcnt; split_ifs at hcnt <;> omega
          refine ⟨y, huy, ?_⟩
          intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψy, hcyγ] at hψs; exact False.elim (hcvγ hψs)
          · rw [hs, hψa, hψy, hcyγ] at hψs; exact False.elim (hcaγ hψs)
          · rw [hs, hψ_out x hx_not_S, hψy, hcyγ] at hψs; exact False.elim (hβγ hψs)
          · exact hs
        · by_cases hcaγ : ca = γ
          · have hcvγ : cv ≠ γ := by
              simp only [hcyγ, hcaγ, ite_true, ite_false] at hcnt; split_ifs at hcnt <;> omega
            have hβγ : β ≠ γ := by
              simp only [hcyγ, hcaγ, ite_true, ite_false] at hcnt; split_ifs at hcnt <;> omega
            refine ⟨a, hua, ?_⟩
            intro s hus hψs
            rcases hu_all s hus with hs | hs | hs | hs
            · rw [hs, hψv, hψa, hcaγ] at hψs; exact False.elim (hcvγ hψs)
            · exact hs
            · rw [hs, hψ_out x hx_not_S, hψa, hcaγ] at hψs; exact False.elim (hβγ hψs)
            · rw [hs, hψy, hψa, hcaγ] at hψs; exact False.elim (hcyγ hψs)
          · by_cases hcvγ : cv = γ
            · have hβγ : β ≠ γ := by
                simp only [hcyγ, hcaγ, hcvγ, ite_true, ite_false] at hcnt
                split_ifs at hcnt <;> omega
              refine ⟨v, huv, ?_⟩
              intro s hus hψs
              rcases hu_all s hus with hs | hs | hs | hs
              · exact hs
              · rw [hs, hψa, hψv, hcvγ] at hψs; exact False.elim (hcaγ hψs)
              · rw [hs, hψ_out x hx_not_S, hψv, hcvγ] at hψs; exact False.elim (hβγ hψs)
              · rw [hs, hψy, hψv, hcvγ] at hψs; exact False.elim (hcyγ hψs)
            · have hβγ : β = γ := by
                simp only [hcyγ, hcaγ, hcvγ, ite_false] at hcnt; split_ifs at hcnt <;> omega
              refine ⟨x, hux, ?_⟩
              intro s hus hψs
              rcases hu_all s hus with hs | hs | hs | hs
              · rw [hs, hψv, hψ_out x hx_not_S] at hψs; exact False.elim (hcvγ (hψs.trans hβγ))
              · rw [hs, hψa, hψ_out x hx_not_S] at hψs; exact False.elim (hcaγ (hψs.trans hβγ))
              · exact hs
              · rw [hs, hψy, hψ_out x hx_not_S] at hψs; exact False.elim (hcyγ (hψs.trans hβγ))
      · subst t
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact hcwu.symm)
      · subst t
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψv, hψz]; exact hcvz)
      · subst t
        exact pcf_at_of_two_distinct_neighbors hdz hwz.symm hzr hrw.symm
          (by rw [hψw, hψ_out r0 hr_not_S]; exact hcwρ)
      · subst t
        exact pcf_at_of_two_distinct_neighbors hda hua.symm hap hpu.symm
          (by rw [hψu, hψ_out p0 hp_not_S]; exact hcup)
      · subst t; exact pcf_at_deg_one hdy huy.symm
  -- 现在固定 `z ↦ ζ`，构造 `C = L u \ {β, φ* x, φ p0}` 与 3 元集族 `A α : Fin 3 → Finset ℕ`！
  let C : Finset ℕ := L u \ {β, adm.φs x, adm.φ p0}
  have hC : 2 ≤ C.card := by
    dsimp only [C]
    have := card_sdiff_ge (L u) {β, adm.φs x, adm.φ p0}
    have := card_triple_le β (adm.φs x) (adm.φ p0); omega
  have hcw_ex : ∀ α : ℕ, ∃ c ∈ L w, c ≠ α ∧ c ≠ ζ ∧ c ≠ ρ := by
    intro α
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {α, ζ, ρ})
      (by have := card_triple_le α ζ ρ; omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → ℕ := fun α => (hcw_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w ∧ cFun α ≠ α ∧ cFun α ≠ ζ ∧ cFun α ≠ ρ :=
    fun α => (hcw_ex α).choose_spec
  let A : ℕ → Fin 3 → Finset ℕ := fun α i =>
    match i with
    | ⟨0, _⟩ => L y \ {α}
    | ⟨1, _⟩ => L a \ {α, adm.φ p0, adm.φs p0}
    | ⟨2, _⟩ => L v \ {α, cFun α, ζ}
  have hA_ne : ∀ α (i : Fin 3), (A α i).Nonempty := by
    intro α i; fin_cases i
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L y) {α}
      simp only [Finset.card_singleton] at this; dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L a) {α, adm.φ p0, adm.φs p0}
      have := card_triple_le α (adm.φ p0) (adm.φs p0); dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L v) {α, cFun α, ζ}
      have := card_triple_le α (cFun α) ζ; dsimp only [A]; omega
  have hno_rep : ∀ α ∈ C, ¬ ∃ f : Fin 3 → ℕ, IsPCFRep (A α) [β] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    have h0 := hf_mem 0; have h1 := hf_mem 1; have h2 := hf_mem 2
    simp only [A, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h0 h1 h2
    apply hcontra α (f 0) (f 1) (f 2) (cFun α) ζ
      hα.1 h0.1 h1.1 h2.1 (hcFun_spec α).1 hζL
      hα.2.1 hα.2.2.1 hα.2.2.2 h0.2 h1.2.1 h1.2.2.1 h1.2.2.2
      h2.2.1 h2.2.2.1 (hcFun_spec α).2.1 (hcFun_spec α).2.2.1 (hcFun_spec α).2.2.2
      hζn.1 hζn.2 h2.2.2.2
    refine ⟨γ, ?_⟩
    have hfilt : (Finset.univ.filter (fun i : Fin 3 => f i = γ)).card =
        (if f 0 = γ then 1 else 0) + (if f 1 = γ then 1 else 0) + (if f 2 = γ then 1 else 0) := by
      have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [hu3, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
      split_ifs <;> simp
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hγ ⊢
    omega
  -- 对每个 `α ∈ C`，`no_pcfRep_single_bounds` 强制 `q_α = 3`，即 3 个集合全是单点！
  have hall_sing : ∀ α ∈ C, ∀ i : Fin 3, (A α i).card = 1 := by
    intro α hα i
    have hq3 := (no_pcfRep_single_bounds (hA_ne α) (hno_rep α hα)).2.2.1 (by simp)
    have hle3 : (Finset.univ.filter (fun j : Fin 3 => (A α j).card = 1)).card ≤ 3 :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have hEq : Finset.univ.filter (fun j : Fin 3 => (A α j).card = 1) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simp; omega)
    have : i ∈ Finset.univ.filter (fun j : Fin 3 => (A α j).card = 1) := by
      rw [hEq]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  -- 从而 `|C| = 2`（否则 `|C| ≥ 3` 时 `L y \ {α}` 单点次数 `≤ 2` 矛盾！）
  have hC2 : C.card = 2 := by
    have hle2 : C.card ≤ 2 := by
      have h1 := (card_filter_sdiff_singleton_eq_one_le C (L y) (by omega)).1
      have hEq : C.filter (fun α => (L y \ {α}).card = 1) = C :=
        Finset.filter_true_of_mem (fun α hα => hall_sing α hα 0)
      rw [hEq] at h1; exact h1
    omega
  rcases Finset.card_eq_two.mp hC2 with ⟨c₁, c₂, hc12, hC_eq⟩
  have hc1C : c₁ ∈ C := by rw [hC_eq]; simp
  have hc2C : c₂ ∈ C := by rw [hC_eq]; simp
  -- 推出 `L y = {c₁, c₂}` 与 `L a \ {φ p0, φ* p0} = {c₁, c₂}`！
  have hLy_eq : L y = {c₁, c₂} := by
    have hEq : C.filter (fun α => (L y \ {α}).card = 1) = C :=
      Finset.filter_true_of_mem (fun α hα => hall_sing α hα 0)
    have hsub := ((card_filter_sdiff_singleton_eq_one_le C (L y) (by omega)).2
      (by rw [hEq, hC2])).2
    rw [hC_eq] at hsub
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hc12, hLy])
  have hLa_eq : L a \ {adm.φ p0, adm.φs p0} = {c₁, c₂} := by
    have hEq : C.filter (fun α => (L a \ {α, adm.φ p0, adm.φs p0}).card = 1) = C :=
      Finset.filter_true_of_mem (fun α hα => hall_sing α hα 1)
    have hsub := ((card_filter_sdiff_two_fixed_eq_one_le C (L a) hLa (adm.φ p0) (adm.φs p0)).2
      (by rw [hEq, hC2])).2.2.2
    rw [hC_eq] at hsub
    have hge2 : 2 ≤ (L a \ {adm.φ p0, adm.φs p0}).card := by
      have := card_sdiff_ge (L a) {adm.φ p0, adm.φs p0}
      have := Finset.card_le_two (a := adm.φ p0) (b := adm.φs p0); omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hc12]; omega)
  -- 推出 `A c₁ 2 = {β}` 且 `A c₂ 2 = {β}`！
  have hAv_β : ∀ ci cj : ℕ, ci ∈ C → cj ∈ C → ci ≠ cj →
      ({ci, cj} : Finset ℕ) = C → L v \ {ci, cFun ci, ζ} = {β} := by
    intro ci cj hci hcj hne hpair
    rcases Finset.card_eq_one.mp (hall_sing ci hci 2) with ⟨d, hd⟩
    dsimp only [A] at hd
    have hd_eq : d = β := by
      by_contra hdβ
      apply hno_rep ci hci
      have hcj_Ly : cj ∈ L y \ {ci} := by
        rw [hLy_eq, ← hC_eq, ← hpair]; simp [hne.symm]
      have hcj_La : cj ∈ L a \ {ci, adm.φ p0, adm.φs p0} := by
        have h1 : cj ∈ L a \ {adm.φ p0, adm.φs p0} := by
          rw [hLa_eq, ← hC_eq, ← hpair]; simp
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h1 ⊢
        exact ⟨h1.1, hne.symm, h1.2.1, h1.2.2⟩
      have hd_Lv : d ∈ L v \ {ci, cFun ci, ζ} := by rw [hd]; simp
      have hcjβ : cj ≠ β := by
        simp only [C, Finset.mem_sdiff, Finset.mem_insert] at hcj
        exact fun h => hcj.2 (Or.inl h)
      let f : Fin 3 → ℕ := fun i => match i with | ⟨0, _⟩ => cj | ⟨1, _⟩ => cj | ⟨2, _⟩ => d
      refine ⟨f, ?_, β, ?_⟩
      · intro i; fin_cases i
        · exact hcj_Ly
        · exact hcj_La
        · exact hd_Lv
      · have hfilt : Finset.univ.filter (fun i : Fin 3 => f i = β) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _
          fin_cases i <;> simp [f, hcjβ, hdβ]
        rw [hfilt, Finset.card_empty]; simp
    rw [hd, hd_eq]
  have hAv1 := hAv_β c₁ c₂ hc1C hc2C hc12 hC_eq.symm
  have hAv2 := hAv_β c₂ c₁ hc2C hc1C hc12.symm (by rw [Finset.pair_comm, hC_eq])
  rcases four_set_sdiff_eq_singleton_pair hLv hc12 hAv1 hAv2 with
    ⟨hω1, hω2, hζLv, _, hc1ζ, hc1β, hc2ζ, hc2β, hζβ⟩
  -- 在 4-元集 `L z` 中，存在 `i ≠ j ∈ {c₁, c₂}` 与 `d ∈ L z \ {ζ, cj, ρ, τ}`！
  have hex_d : ∃ ci cj d : ℕ, ci ∈ C ∧ cj ∈ C ∧ ci ≠ cj ∧
      ({ci, cj} : Finset ℕ) = C ∧ d ∈ L z ∧ d ≠ ζ ∧ d ≠ cj ∧ d ≠ ρ ∧ d ≠ τ := by
    by_cases h1 : (L z \ {ζ, c₂, ρ, τ}).Nonempty
    · rcases h1 with ⟨d, hd⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd
      exact ⟨c₁, c₂, d, hc1C, hc2C, hc12, hC_eq.symm, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
        hd.2.2.2.2⟩
    · by_cases h2 : (L z \ {ζ, c₁, ρ, τ}).Nonempty
      · rcases h2 with ⟨d, hd⟩
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd
        exact ⟨c₂, c₁, d, hc2C, hc1C, hc12.symm, by rw [Finset.pair_comm, hC_eq],
          hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
      · exfalso
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h1 h2
        have hsub3 : L z ⊆ {ζ, ρ, τ} := by
          intro d hd
          have hm1 := h1 hd; have hm2 := h2 hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2 ⊢
          rcases hm1 with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · rcases hm2 with rfl | h | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (hc12 h.symm)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        have hle := le_trans (Finset.card_le_card hsub3) (card_triple_le ζ ρ τ)
        omega
  rcases hex_d with ⟨ci, cj, d, hciC, hcjC, hcij, hpair, hdL, hdζ, hdcj, hdρ, hdτ⟩
  have hci_spec := hciC
  simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hci_spec
  have hcj_Lw : cj ∈ L w ∧ cj ≠ ρ := by
    have hci_cases : ci = c₁ ∨ ci = c₂ := by rw [hC_eq] at hciC; simpa using hciC
    rcases hci_cases with h1 | h2
    · have hcj2 : cj = c₂ := by
        have : cj ∈ ({c₁, c₂} : Finset ℕ) := by rw [← hC_eq]; exact hcjC
        simpa [h1 ▸ hcij.symm] using this
      rw [hcj2, ← hω1]; exact ⟨(hcFun_spec c₁).1, (hcFun_spec c₁).2.2.2⟩
    · have hcj1 : cj = c₁ := by
        have : cj ∈ ({c₁, c₂} : Finset ℕ) := by rw [← hC_eq]; exact hcjC
        simpa [h2 ▸ hcij.symm] using this
      rw [hcj1, ← hω2]; exact ⟨(hcFun_spec c₂).1, (hcFun_spec c₂).2.2.2⟩
  have hcj_Ly : cj ∈ L y := by rw [hLy_eq, ← hC_eq, ← hpair]; simp
  have hcj_La : cj ∈ L a \ {adm.φ p0, adm.φs p0} := by rw [hLa_eq, ← hC_eq, ← hpair]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcj_La
  have hζ_ne_ci : ζ ≠ ci := by
    have : ci = c₁ ∨ ci = c₂ := by rw [hC_eq] at hciC; simpa using hciC
    rcases this with rfl | rfl
    · exact hc1ζ.symm
    · exact hc2ζ.symm
  have hζ_ne_cj : ζ ≠ cj := by
    have : cj = c₁ ∨ cj = c₂ := by rw [hC_eq] at hcjC; simpa using hcjC
    rcases this with rfl | rfl
    · exact hc1ζ.symm
    · exact hc2ζ.symm
  have hcj_ne_β : cj ≠ β := by
    simp only [C, Finset.mem_sdiff, Finset.mem_insert] at hcjC
    exact fun h => hcjC.2 (Or.inl h)
  -- 着色：`u ↦ ci, y ↦ cj, a ↦ cj, v ↦ ζ, w ↦ cj, z ↦ d`，`β` 在 `N(u)` 中唯一！
  apply hcontra ci cj cj ζ cj d
    hci_spec.1 hcj_Ly hcj_La.1 hζLv hcj_Lw.1 hdL
    hci_spec.2.1 hci_spec.2.2.1 hci_spec.2.2.2 hcij.symm hcij.symm hcj_La.2.1 hcj_La.2.2
    hζ_ne_ci hζ_ne_cj hcij.symm hdcj.symm hcj_Lw.2 hdρ hdτ hdζ.symm
  refine ⟨β, ?_⟩
  simp [hcj_ne_β, hζβ]

/-- Lemma 3.9（合并版）：若 `coreDeg G u = 3` 且 `u` 同时关联 `2⁺`-线串 `v` 与 `1`-线串 `a`，
则 `G.degree u = 4 ∧ v ∈ twoThreadNbrs G u`。 -/
lemma thread_reduction {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a : V}
    (hc3 : coreDeg G u = 3) (hv : v ∈ longThreadNbrs G u) (ha : a ∈ oneThreadNbrs G u) :
    G.degree u = 4 ∧ v ∈ twoThreadNbrs G u := by
  have hdu4 := thread_reduction_deg_four hm hc3 hv ha
  refine ⟨hdu4, ?_⟩
  rw [longThreadNbrs_eq_two_union_three hm u, Finset.mem_union] at hv
  rcases hv with h2 | h3
  · exact h2
  · exact False.elim (thread_reduction_not_three hm hdu4 hc3 h3 ha)

/-! ## 2. Lemma 3.10a（`one_thread_good_neighbor`）：`4`-度好点关联 `2`-线串与 `1`-线串 -/

/-- Lemma 3.10a 第一部分：`G.degree u = 4, coreDeg G u = 3` 且关联 `2`-线串与 `1`-线串时，
不能再关联第二条 `1`-线串！ -/
lemma one_thread_unique_of_two_thread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a t : V}
    (hdu4 : G.degree u = 4) (hc3 : coreDeg G u = 3)
    (hv : v ∈ twoThreadNbrs G u) (ha : a ∈ oneThreadNbrs G u) (ht : t ∈ oneThreadNbrs G u)
    (hat : a ≠ t) : False := by
  classical
  simp only [twoThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ha ht
  rcases hv.2 with ⟨huv, hdv, w, z, hvw, hwu, hdw, hwz, hzv, hdz3⟩
  rcases ha.2 with ⟨hua, hda, p0, hap, hpu, hdp3⟩
  rcases ht.2 with ⟨hut, hdt, q0, htq, hqu, hdq3⟩
  have hdz4 : 4 ≤ G.degree z := by
    by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega) hdw hdv hwz.symm hvw.symm
  have hY1 : (leafNbrs G u).card = 1 := by have := coreDeg_add_leafNbrs hm u; omega
  rcases Finset.card_eq_one.mp hY1 with ⟨y, hy_eq⟩
  have hy_mem : y ∈ leafNbrs G u := by rw [hy_eq]; simp
  rw [mem_leafNbrs] at hy_mem; rcases hy_mem with ⟨huy, hdy⟩
  have hva : v ≠ a := fun h => by
    subst h; exact not_oneThread_and_longThread ha.2 ⟨huv, hdv, w, hvw, hwu, hdw⟩
  have hvt : v ≠ t := fun h => by
    subst h; exact not_oneThread_and_longThread ht.2 ⟨huv, hdv, w, hvw, hwu, hdw⟩
  have hcore_eq : coreNbrs G u = {v, a, t} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hua, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hut, by omega⟩
    · rw [Finset.card_insert_of_notMem (by simp [hva, hvt]), Finset.card_pair hat]
      unfold coreDeg at hc3; omega
  have hwa : w ≠ a := fun h =>
    no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hua.symm)
  have hwt : w ≠ t := fun h =>
    no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hut.symm)
  have hzu : z ≠ u := fun h => no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hwz)
  let S : Finset V := {u, v, w, a, t, y}
  have huS : u ∈ S := by simp [S]
  have hz_not_S : z ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hzu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩
  have hp_not_S : p0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩
  have hq_not_S : q0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩
  have hv_all : ∀ r, G.Adj v r → r = u ∨ r = w := by
    intro r hr; have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : r ∈ ({u, w} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v r).mpr hr
    simpa using this
  have hw_all : ∀ r, G.Adj w r → r = v ∨ r = z := by
    intro r hr; have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
    have : r ∈ ({v, z} : Finset V) := by rw [← hNw]; exact (G.mem_neighborFinset w r).mpr hr
    simpa using this
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = p0 := by
    intro r hr; have hNa := neighborFinset_eq_pair_of_deg_two hda hua.symm hap hpu.symm
    have : r ∈ ({u, p0} : Finset V) := by rw [← hNa]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  have ht_all : ∀ r, G.Adj t r → r = u ∨ r = q0 := by
    intro r hr; have hNt := neighborFinset_eq_pair_of_deg_two hdt hut.symm htq hqu.symm
    have : r ∈ ({u, q0} : Finset V) := by rw [← hNt]; exact (G.mem_neighborFinset t r).mpr hr
    simpa using this
  have hy_only : ∀ r, G.Adj y r → r = u := by
    rcases exists_unique_neighbor_of_deg_one hdy with ⟨r0, _, huniq⟩
    exact fun r hr => (huniq r hr).trans (huniq u huy.symm).symm
  have hu_all : ∀ r, G.Adj u r → r = v ∨ r = a ∨ r = t ∨ r = y := by
    intro r hr
    have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · have : r ∈ ({y} : Finset V) := by rw [← hy_eq]; exact mem_leafNbrs.mpr ⟨hr, h1⟩
      exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp this)))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hS_out : ∀ s, s ∉ S → ∀ b ∈ S, G.Adj s b →
      (b = w ∧ s = z) ∨ (b = a ∧ s = p0) ∨ (b = t ∧ s = q0) := by
    intro s hsS b hbS hsb
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hbS
    rcases hbS with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hu_all s hsb.symm with rfl | rfl | rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hv_all s hsb.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hw_all s hsb.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases ha_all s hsb.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases ht_all s hsb.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact False.elim (hsS ((hy_only s hsb.symm) ▸ huS))
  -- `z, p0, q0` 在 `G - S` 中均非孤立！
  have hnoniso_z : ∃ r, r ∉ S ∧ G.Adj z r := by
    have hlt : ({w, a, t} : Finset V).card < (G.neighborFinset z).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := card_triple_le w a t; omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out z hz_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2.1 rfl
    · exact hrn.2.2 rfl
  have hnoniso_pq : ∀ s, s ∉ S → 3 ≤ G.degree s → ∃ r, r ∉ S ∧ G.Adj s r := by
    intro s hsS hds3
    by_cases hsz : s = z
    · rw [hsz]; exact hnoniso_z
    · have hlt : ({a, t} : Finset V).card < (G.neighborFinset s).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := a) (b := t); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out s hsS r hrS hr with ⟨_, hEq⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hsz hEq
      · exact hrn.1 rfl
      · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  have hLa : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLt : (L t).card = 4 := by rw [hm.list_card t]; simp [kappa, hdt]
  have hLy : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  let C₀ : Finset ℕ := L u \ {adm.φ p0, adm.φ q0}
  have hC0 : 3 ≤ C₀.card := by
    dsimp only [C₀]; have := card_sdiff_ge (L u) {adm.φ p0, adm.φ q0}
    have := Finset.card_le_two (a := adm.φ p0) (b := adm.φ q0); omega
  have hcw_ex : ∀ α : ℕ, ∃ c ∈ L w, c ≠ α ∧ c ≠ adm.φ z ∧ c ≠ adm.φs z := by
    intro α
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {α, adm.φ z, adm.φs z})
      (by have := card_triple_le α (adm.φ z) (adm.φs z); omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → ℕ := fun α => (hcw_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w ∧ cFun α ≠ α ∧ cFun α ≠ adm.φ z ∧ cFun α ≠ adm.φs z :=
    fun α => (hcw_ex α).choose_spec
  let A : ℕ → Fin 4 → Finset ℕ := fun α i =>
    match i with
    | ⟨0, _⟩ => L y \ {α}
    | ⟨1, _⟩ => L a \ {α, adm.φ p0, adm.φs p0}
    | ⟨2, _⟩ => L t \ {α, adm.φ q0, adm.φs q0}
    | ⟨3, _⟩ => L v \ {α, cFun α, adm.φ z}
  have hA_ne : ∀ α (i : Fin 4), (A α i).Nonempty := by
    intro α i; fin_cases i
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L y) {α}
      simp only [Finset.card_singleton] at this; dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L a) {α, adm.φ p0, adm.φs p0}
      have := card_triple_le α (adm.φ p0) (adm.φs p0); dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L t) {α, adm.φ q0, adm.φs q0}
      have := card_triple_le α (adm.φ q0) (adm.φs q0); dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L v) {α, cFun α, adm.φ z}
      have := card_triple_le α (cFun α) (adm.φ z); dsimp only [A]; omega
  have hno_rep : ∀ α ∈ C₀, ¬ ∃ f : Fin 4 → ℕ, IsPCFRep (A α) [] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    simp only [C₀, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    have h0 := hf_mem 0; have h1 := hf_mem 1; have h2 := hf_mem 2; have h3 := hf_mem 3
    simp only [A, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h0 h1 h2 h3
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have hvw_ne : v ≠ w := G.ne_of_adj hvw
    have huy_ne : u ≠ y := G.ne_of_adj huy
    have hvy : v ≠ y := fun h => by subst h; omega
    have hwy : w ≠ y := fun h => by subst h; omega
    have hay : a ≠ y := fun h => by subst h; omega
    have hty : t ≠ y := fun h => by subst h; omega
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v then f 3 else if r = w then cFun α
      else if r = a then f 1 else if r = t then f 2 else if r = y then f 0 else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψv : ψ v = f 3 := by simp [ψ, huv_ne.symm]
    have hψw : ψ w = cFun α := by simp [ψ, hwu, hvw_ne.symm]
    have hψa : ψ a = f 1 := by simp [ψ, (G.ne_of_adj hua).symm, hva.symm, hwa.symm]
    have hψt : ψ t = f 2 := by simp [ψ, (G.ne_of_adj hut).symm, hvt.symm, hwt.symm, hat.symm]
    have hψy : ψ y = f 0 := by simp [ψ, huy_ne.symm, hvy.symm, hwy.symm, hay.symm, hty.symm]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hψu]; exact hα.1
      · rw [hψv]; exact h3.1
      · rw [hψw]; exact (hcFun_spec α).1
      · rw [hψa]; exact h1.1
      · rw [hψt]; exact h2.1
      · rw [hψy]; exact h0.1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with h' | h' | h' | h' | h' | h'
        · subst a'
          rcases hu_all b' hab with hb | hb | hb | hb
          · rw [hb, hψu, hψv]; exact Ne.symm h3.2.1
          · rw [hb, hψu, hψa]; exact Ne.symm h1.2.1
          · rw [hb, hψu, hψt]; exact Ne.symm h2.2.1
          · rw [hb, hψu, hψy]; exact Ne.symm h0.2
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψv, hψu]; exact h3.2.1
          · rw [hb, hψv, hψw]; exact h3.2.2.1
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψv]; exact Ne.symm h3.2.2.1
          · rw [hb, hψw, hψ_out z hz_not_S]; exact (hcFun_spec α).2.2.1
        · subst a'
          rcases ha_all b' hab with hb | hb
          · rw [hb, hψa, hψu]; exact h1.2.1
          · rw [hb, hψa, hψ_out p0 hp_not_S]; exact h1.2.2.1
        · subst a'
          rcases ht_all b' hab with hb | hb
          · rw [hb, hψt, hψu]; exact h2.2.1
          · rw [hb, hψt, hψ_out q0 hq_not_S]; exact h2.2.2.1
        · subst a'
          rw [hy_only b' hab, hψy, hψu]; exact h0.2
      rcases hor with h' | h'
      · exact hcase r₁ r₂ h12 h'
      · exact (hcase r₂ r₁ h12.symm h').symm
    · intro s hsS _ b hbS hsb
      rcases hS_out s hsS b hbS hsb with ⟨hbw, hsz⟩ | ⟨hba, hsp⟩ | ⟨hbt, hsq⟩
      · rw [hbw, hsz, hψw]; exact (hcFun_spec α).2.2.2
      · rw [hba, hsp, hψa]; exact h1.2.2.2
      · rw [hbt, hsq, hψt]; exact h2.2.2.2
    · intro s hsS hiso ⟨b, hsb⟩
      have hbS : b ∈ S := by by_contra h; exact hiso b h hsb
      rcases hS_out s hsS b hbS hsb with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩
      · subst s; rcases hnoniso_z with ⟨r, hrS, hzr⟩; exact False.elim (hiso r hrS hzr)
      · subst s; rcases hnoniso_pq p0 hp_not_S hdp3 with ⟨r, hrS, hpr⟩
        exact False.elim (hiso r hrS hpr)
      · subst s; rcases hnoniso_pq q0 hq_not_S hdq3 with ⟨r, hrS, hqr⟩
        exact False.elim (hiso r hrS hqr)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hrS
      rcases hrS with h' | h' | h' | h' | h' | h'
      · subst r
        simp only [List.count_nil, add_zero] at hγ
        rcases Finset.card_eq_one.mp hγ with ⟨i₀, hi₀_eq⟩
        have hcol : ∀ i : Fin 4, f i = γ ↔ i = i₀ := by
          intro i
          have : i ∈ Finset.univ.filter (fun j : Fin 4 => f j = γ) ↔
              i ∈ ({i₀} : Finset (Fin 4)) := by
            rw [hi₀_eq]
          simpa using this
        fin_cases i₀
        · have hi0γ : f 0 = γ := (hcol 0).mpr rfl
          refine ⟨y, huy, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψy, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · rw [hs, hψa, hψy, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · rw [hs, hψt, hψy, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · exact hs
        · have hi0γ : f 1 = γ := (hcol 1).mpr rfl
          refine ⟨a, hua, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψa, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · exact hs
          · rw [hs, hψt, hψa, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · rw [hs, hψy, hψa, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
        · have hi0γ : f 2 = γ := (hcol 2).mpr rfl
          refine ⟨t, hut, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψt, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · rw [hs, hψa, hψt, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · exact hs
          · rw [hs, hψy, hψt, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
        · have hi0γ : f 3 = γ := (hcol 3).mpr rfl
          refine ⟨v, huv, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · exact hs
          · rw [hs, hψa, hψv, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · rw [hs, hψt, hψv, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · rw [hs, hψy, hψv, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact (hcFun_spec α).2.1.symm)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψv, hψ_out z hz_not_S]; exact h3.2.2.2)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hda hua.symm hap hpu.symm
          (by rw [hψu, hψ_out p0 hp_not_S]; exact hα.2.1)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdt hut.symm htq hqu.symm
          (by rw [hψu, hψ_out q0 hq_not_S]; exact hα.2.2)
      · subst r; exact pcf_at_deg_one hdy huy.symm
  -- 双计数：`4 * |C₀| ≤ 2 + 2 + 2 + 3 = 9`，与 `|C₀| ≥ 3` 矛盾！
  have hlower : 4 * C₀.card ≤
      ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card := by
    calc 4 * C₀.card = ∑ _α ∈ C₀, 4 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card := by
        apply Finset.sum_le_sum; intro α hα
        exact (no_pcfRep_nil_bounds (hA_ne α) (hno_rep α hα)).2 (by simp)
  have hupper : ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card ≤ 9 := by
    rw [sum_filter_card_comm]
    have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    rw [hu4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 := (card_filter_sdiff_singleton_eq_one_le C₀ (L y) (by omega)).1
    have h1 := (card_filter_sdiff_two_fixed_eq_one_le C₀ (L a) hLa (adm.φ p0) (adm.φs p0)).1
    have h2 := (card_filter_sdiff_two_fixed_eq_one_le C₀ (L t) hLt (adm.φ q0) (adm.φs q0)).1
    have h3 := (card_filter_sdiff_triple_eq_one_le C₀ (L v) hLv cFun (adm.φ z)).1
    dsimp only [A]; omega
  omega

/-- Lemma 3.10a 第二部分：`G.degree u = 4, coreDeg G u = 3` 且关联 `2`-线串与 `1`-线串时，
第三个核心邻点 `b` 不能是坏点！ -/
lemma no_bad_nbr_of_two_and_one_thread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a b : V}
    (hdu4 : G.degree u = 4) (hc3 : coreDeg G u = 3)
    (hv : v ∈ twoThreadNbrs G u) (ha : a ∈ oneThreadNbrs G u)
    (hb_adj : G.Adj u b) (hbad : IsBad G b) : False := by
  classical
  simp only [twoThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ha
  rcases hv.2 with ⟨huv, hdv, w, z, hvw, hwu, hdw, hwz, hzv, hdz3⟩
  rcases ha.2 with ⟨hua, hda, p0, hap, hpu, hdp3⟩
  have hdz4 : 4 ≤ G.degree z := by
    by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega) hdw hdv hwz.symm hvw.symm
  have hdb4 : 4 ≤ G.degree b := hbad.1
  have hY1 : (leafNbrs G u).card = 1 := by have := coreDeg_add_leafNbrs hm u; omega
  rcases Finset.card_eq_one.mp hY1 with ⟨y, hy_eq⟩
  have hy_mem : y ∈ leafNbrs G u := by rw [hy_eq]; simp
  rw [mem_leafNbrs] at hy_mem; rcases hy_mem with ⟨huy, hdy⟩
  have hva : v ≠ a := fun h => by
    subst h; exact not_oneThread_and_longThread ha.2 ⟨huv, hdv, w, hvw, hwu, hdw⟩
  have hvb : v ≠ b := fun h => by subst h; omega
  have hab_ne : a ≠ b := fun h => by subst h; omega
  have hub_ne : u ≠ b := G.ne_of_adj hb_adj
  have hcore_eq : coreNbrs G u = {v, a, b} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hua, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hb_adj, by omega⟩
    · rw [Finset.card_insert_of_notMem (by simp [hva, hvb]), Finset.card_pair hab_ne]
      unfold coreDeg at hc3; omega
  -- 取出坏点 `b` 除 `u` 外的唯一核心邻点 `h`（必为 `3⁺`-度点！）与叶邻点 `Pb`
  have hu_coreb : u ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hb_adj.symm, by omega⟩
  have hb_other : (coreNbrs G b \ {u}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu_coreb),
        Finset.card_singleton]; have := hbad.2; unfold coreDeg at this; omega
  rcases Finset.card_eq_one.mp hb_other with ⟨h0, hh_eq⟩
  have hh_mem : h0 ∈ coreNbrs G b \ {u} := by rw [hh_eq]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hh_mem
  have hbh : G.Adj b h0 := (mem_coreNbrs.mp hh_mem.1).1
  have hhu : h0 ≠ u := hh_mem.2
  have hdh3 : 3 ≤ G.degree h0 := bad_coreNbrs_deg_ge_three hm hpq hbad hh_mem.1
  have hcore_b : coreNbrs G b = {u, h0} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hu_coreb
      · exact hh_mem.1
    · rw [Finset.card_pair hhu.symm]; have := hbad.2; unfold coreDeg at this; omega
  let Pb := leafNbrs G b
  have hPb_card : Pb.card = G.degree b - 2 := by
    dsimp only [Pb]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  have hwa : w ≠ a := fun h =>
    no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hua.symm)
  have hwb : w ≠ b := fun h => by subst h; omega
  have hzu : z ≠ u := fun h => no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (h ▸ hwz)
  -- `z ≠ b`（因 `b` 是坏点不关联 `2⁺`-线串！）
  have hzb : z ≠ b := by
    intro h; subst h
    have hbw : w ∈ longThreadNbrs G z := by
      simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hwz.symm, hdw⟩, hwz.symm, hdw, v, hvw.symm, hzv.symm, hdv⟩
    rw [bad_no_long_thread hm hpq hbad] at hbw; exact Finset.notMem_empty w hbw
  -- `p0 ≠ b`（因 `b` 是坏点不关联 `1`-线串！）
  have hpb : p0 ≠ b := by
    intro h; subst h
    have hba : a ∈ oneThreadNbrs G p0 := by
      simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hap.symm, hda⟩, hap.symm, hda, u, hua.symm, hpu.symm, by omega⟩
    rw [bad_no_one_thread hm hbad] at hba; exact Finset.notMem_empty a hba
  have hy_not_Pb : y ∉ Pb := by
    intro h; have h1 := mem_leafNbrs.mp h
    rcases exists_unique_neighbor_of_deg_one hdy with ⟨r0, _, huniq⟩
    exact hub_ne ((huniq u huy.symm).trans (huniq b h1.1.symm).symm)
  let S : Finset V := insert u (insert v (insert w (insert a (insert b (insert y Pb)))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hz_not_S : z ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hzu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, hzb, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hp_not_S : p0 ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hpu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, hpb, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hh_not_S : h0 ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hhu, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, (G.ne_of_adj hbh).symm, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hv_all : ∀ r, G.Adj v r → r = u ∨ r = w := by
    intro r hr; have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : r ∈ ({u, w} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v r).mpr hr
    simpa using this
  have hw_all : ∀ r, G.Adj w r → r = v ∨ r = z := by
    intro r hr; have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
    have : r ∈ ({v, z} : Finset V) := by rw [← hNw]; exact (G.mem_neighborFinset w r).mpr hr
    simpa using this
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = p0 := by
    intro r hr; have hNa := neighborFinset_eq_pair_of_deg_two hda hua.symm hap hpu.symm
    have : r ∈ ({u, p0} : Finset V) := by rw [← hNa]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  have hy_only : ∀ r, G.Adj y r → r = u := by
    rcases exists_unique_neighbor_of_deg_one hdy with ⟨r0, _, huniq⟩
    exact fun r hr => (huniq r hr).trans (huniq u huy.symm).symm
  have hu_all : ∀ r, G.Adj u r → r = v ∨ r = a ∨ r = b ∨ r = y := by
    intro r hr; have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · have : r ∈ ({y} : Finset V) := by rw [← hy_eq]; exact mem_leafNbrs.mpr ⟨hr, h1⟩
      exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp this)))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hb_all : ∀ r, G.Adj b r → r = u ∨ r = h0 ∨ r ∈ Pb := by
    intro r hr; have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore_b, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hS_out : ∀ s, s ∉ S → ∀ q ∈ S, G.Adj s q →
      (q = w ∧ s = z) ∨ (q = a ∧ s = p0) ∨ (q = b ∧ s = h0) := by
    intro s hsS q hqS hsq
    simp only [S, Finset.mem_insert] at hqS
    rcases hqS with rfl | rfl | rfl | rfl | rfl | rfl | hqPb
    · rcases hu_all s hsq.symm with rfl | rfl | rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hv_all s hsq.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hw_all s hsq.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases ha_all s hsq.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hb_all s hsq.symm with rfl | rfl | hsPb
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact False.elim (hsS (by simp [S, hsPb]))
    · exact False.elim (hsS ((hy_only s hsq.symm) ▸ huS))
    · have hL := mem_leafNbrs.mp hqPb
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨r0, _, huniq⟩
      exact False.elim (hsS (((huniq s hsq.symm).trans (huniq b hL.1.symm).symm) ▸
        (by simp [S] : b ∈ S)))
  have hnoniso_z : ∃ r, r ∉ S ∧ G.Adj z r := by
    have hlt : ({w, a, b} : Finset V).card < (G.neighborFinset z).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := card_triple_le w a b; omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, ?_, hr⟩
    intro hrS
    rcases hS_out z hz_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2.1 rfl
    · exact hrn.2.2 rfl
  have hnoniso_ph : ∀ s, s ∉ S → 3 ≤ G.degree s → ∃ r, r ∉ S ∧ G.Adj s r := by
    intro s hsS hds3
    by_cases hsz : s = z
    · rw [hsz]; exact hnoniso_z
    · have hlt : ({a, b} : Finset V).card < (G.neighborFinset s).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := a) (b := b); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out s hsS r hrS hr with ⟨_, hEq⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hsz hEq
      · exact hrn.1 rfl
      · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  have hLa : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLy : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  -- 对坏点 `b` 应用 Lemma 3.7！
  let δ := adm.φ h0
  let Cb : Finset ℕ := L b \ {δ, adm.φs h0}
  have hCb : Pb.card + 1 ≤ Cb.card := by
    dsimp only [Cb]; have := card_sdiff_ge (L b) {δ, adm.φs h0}
    have := Finset.card_le_two (a := δ) (b := adm.φs h0); omega
  have hPb_L2 : ∀ r ∈ Pb, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  rcases bad_two_color_extension (Y := Pb) (C := Cb) (δ := δ) (by omega) hPb_L2 hCb (by simp [Cb])
    with ⟨γ₁, γ₂, lam, hγ1C, hγ2C, hγ12, ⟨aP1, haP1_mem, haP1_u⟩, ⟨aP2, haP2_mem, haP2_u⟩⟩
  let P : Finset ℕ := {γ₁, γ₂}
  let C₀ : Finset ℕ := L u \ {adm.φ p0, lam}
  have hC0 : 3 ≤ C₀.card := by
    dsimp only [C₀]; have := card_sdiff_ge (L u) {adm.φ p0, lam}
    have := Finset.card_le_two (a := adm.φ p0) (b := lam); omega
  have hcw_ex : ∀ α : ℕ, ∃ c ∈ L w, c ≠ α ∧ c ≠ adm.φ z ∧ c ≠ adm.φs z := by
    intro α
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {α, adm.φ z, adm.φs z})
      (by have := card_triple_le α (adm.φ z) (adm.φs z); omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → ℕ := fun α => (hcw_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w ∧ cFun α ≠ α ∧ cFun α ≠ adm.φ z ∧ cFun α ≠ adm.φs z :=
    fun α => (hcw_ex α).choose_spec
  let A : ℕ → Fin 4 → Finset ℕ := fun α i =>
    match i with
    | ⟨0, _⟩ => L y \ {α}
    | ⟨1, _⟩ => L a \ {α, adm.φ p0, adm.φs p0}
    | ⟨2, _⟩ => P \ {α}
    | ⟨3, _⟩ => L v \ {α, cFun α, adm.φ z}
  have hA_ne : ∀ α (i : Fin 4), (A α i).Nonempty := by
    intro α i; fin_cases i
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L y) {α}
      simp only [Finset.card_singleton] at this; dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L a) {α, adm.φ p0, adm.φs p0}
      have := card_triple_le α (adm.φ p0) (adm.φs p0); dsimp only [A]; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge P {α}
      dsimp only [A, P] at *; rw [Finset.card_pair hγ12, Finset.card_singleton] at this; omega
    · rw [← Finset.card_pos]; have := card_sdiff_ge (L v) {α, cFun α, adm.φ z}
      have := card_triple_le α (cFun α) (adm.φ z); dsimp only [A]; omega
  have hno_rep : ∀ α ∈ C₀, ¬ ∃ f : Fin 4 → ℕ, IsPCFRep (A α) [] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    simp only [C₀, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    have hf0 := hf_mem 0; have hf1 := hf_mem 1; have hf2 := hf_mem 2; have hf3 := hf_mem 3
    simp only [A, P, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hf0 hf1 hf2 hf3
    have hfbC : f 2 ∈ Cb := by
      rcases hf2.1 with h | h
      · rw [h]; exact hγ1C
      · rw [h]; exact hγ2C
    simp only [Cb, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hfbC
    let aP : V → ℕ := if f 2 = γ₁ then aP1 else aP2
    have haP_mem : ∀ r ∈ Pb, aP r ∈ L r ∧ aP r ≠ f 2 := by
      intro r hr; dsimp only [aP]; split_ifs with h
      · rw [h]; exact haP1_mem r hr
      · rw [hf2.1.resolve_left h]; exact haP2_mem r hr
    have haP_u : (Pb.filter (fun r => aP r = lam)).card + (if δ = lam then 1 else 0) = 1 := by
      by_cases h : f 2 = γ₁
      · simp only [aP, h, ite_true]; exact haP1_u
      · simp only [aP, h, ite_false]; exact haP2_u
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have hvw_ne : v ≠ w := G.ne_of_adj hvw
    have huy_ne : u ≠ y := G.ne_of_adj huy
    have hvy : v ≠ y := fun h => by subst h; omega
    have hwy : w ≠ y := fun h => by subst h; omega
    have hay : a ≠ y := fun h => by subst h; omega
    have hby : b ≠ y := fun h => by subst h; omega
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v then f 3 else if r = w then cFun α
      else if r = a then f 1 else if r = b then f 2 else if r = y then f 0
      else if r ∈ Pb then aP r else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψv : ψ v = f 3 := by simp [ψ, huv_ne.symm]
    have hψw : ψ w = cFun α := by simp [ψ, hwu, hvw_ne.symm]
    have hψa : ψ a = f 1 := by simp [ψ, (G.ne_of_adj hua).symm, hva.symm, hwa.symm]
    have hψb : ψ b = f 2 := by simp [ψ, hub_ne.symm, hvb.symm, hwb.symm, hab_ne.symm]
    have hψy : ψ y = f 0 := by simp [ψ, huy_ne.symm, hvy.symm, hwy.symm, hay.symm, hby.symm]
    have hψPb : ∀ r ∈ Pb, ψ r = aP r := by
      intro r hr
      have hru : r ≠ u := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrv : r ≠ v := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrw : r ≠ w := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hra : r ≠ a := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrb : r ≠ b := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hry : r ≠ y := fun h => hy_not_Pb (h ▸ hr)
      simp [ψ, hru, hrv, hrw, hra, hrb, hry, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | hrPb
      · rw [hψu]; exact hα.1
      · rw [hψv]; exact hf3.1
      · rw [hψw]; exact (hcFun_spec α).1
      · rw [hψa]; exact hf1.1
      · rw [hψb]; exact hfbC.1
      · rw [hψy]; exact hf0.1
      · rw [hψPb r hrPb]; exact (haP_mem r hrPb).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert] at ha'
        rcases ha' with h' | h' | h' | h' | h' | h' | haPb
        · subst a'
          rcases hu_all b' hab with hb | hb | hb | hb
          · rw [hb, hψu, hψv]; exact Ne.symm hf3.2.1
          · rw [hb, hψu, hψa]; exact Ne.symm hf1.2.1
          · rw [hb, hψu, hψb]; exact Ne.symm hf2.2
          · rw [hb, hψu, hψy]; exact Ne.symm hf0.2
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψv, hψu]; exact hf3.2.1
          · rw [hb, hψv, hψw]; exact hf3.2.2.1
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψv]; exact Ne.symm hf3.2.2.1
          · rw [hb, hψw, hψ_out z hz_not_S]; exact (hcFun_spec α).2.2.1
        · subst a'
          rcases ha_all b' hab with hb | hb
          · rw [hb, hψa, hψu]; exact hf1.2.1
          · rw [hb, hψa, hψ_out p0 hp_not_S]; exact hf1.2.2.1
        · subst a'
          rcases hb_all b' hab with hb | hb | hbPb
          · rw [hb, hψb, hψu]; exact hf2.2
          · rw [hb, hψb, hψ_out h0 hh_not_S]; exact hfbC.2.1
          · rw [hψb, hψPb b' hbPb]; exact (haP_mem b' hbPb).2.symm
        · subst a'
          rw [hy_only b' hab, hψy, hψu]; exact hf0.2
        · have haL := mem_leafNbrs.mp haPb
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨r0, _, huniq⟩
          have hb : b' = b := (huniq b' hab).trans (huniq b haL.1.symm).symm
          rw [hb, hψPb a' haPb, hψb]; exact (haP_mem a' haPb).2
      rcases hor with h' | h'
      · exact hcase r₁ r₂ h12 h'
      · exact (hcase r₂ r₁ h12.symm h').symm
    · intro s hsS _ q hqS hsq
      rcases hS_out s hsS q hqS hsq with ⟨hqw, hsz⟩ | ⟨hqa, hsp⟩ | ⟨hqb, hsh⟩
      · rw [hqw, hsz, hψw]; exact (hcFun_spec α).2.2.2
      · rw [hqa, hsp, hψa]; exact hf1.2.2.2
      · rw [hqb, hsh, hψb]; exact hfbC.2.2
    · intro s hsS hiso ⟨q, hsq⟩
      have hqS : q ∈ S := by by_contra h; exact hiso q h hsq
      rcases hS_out s hsS q hqS hsq with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩
      · subst s; rcases hnoniso_z with ⟨r, hrS, hzr⟩; exact False.elim (hiso r hrS hzr)
      · subst s; rcases hnoniso_ph p0 hp_not_S hdp3 with ⟨r, hrS, hpr⟩
        exact False.elim (hiso r hrS hpr)
      · subst s; rcases hnoniso_ph h0 hh_not_S hdh3 with ⟨r, hrS, hhr⟩
        exact False.elim (hiso r hrS hhr)
    · intro r hrS _
      simp only [S, Finset.mem_insert] at hrS
      rcases hrS with h' | h' | h' | h' | h' | h' | hrPb
      · subst r
        simp only [List.count_nil, add_zero] at hγ
        rcases Finset.card_eq_one.mp hγ with ⟨i₀, hi₀_eq⟩
        have hcol : ∀ i : Fin 4, f i = γ ↔ i = i₀ := by
          intro i
          have : i ∈ Finset.univ.filter (fun j : Fin 4 => f j = γ) ↔
              i ∈ ({i₀} : Finset (Fin 4)) := by rw [hi₀_eq]
          simpa using this
        fin_cases i₀
        · have hi0γ : f 0 = γ := (hcol 0).mpr rfl
          refine ⟨y, huy, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψy, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · rw [hs, hψa, hψy, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · rw [hs, hψb, hψy, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · exact hs
        · have hi0γ : f 1 = γ := (hcol 1).mpr rfl
          refine ⟨a, hua, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψa, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · exact hs
          · rw [hs, hψb, hψa, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · rw [hs, hψy, hψa, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
        · have hi0γ : f 2 = γ := (hcol 2).mpr rfl
          refine ⟨b, hb_adj, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · rw [hs, hψv, hψb, hi0γ] at hψs; exact absurd ((hcol 3).mp hψs) (by decide)
          · rw [hs, hψa, hψb, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · exact hs
          · rw [hs, hψy, hψb, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
        · have hi0γ : f 3 = γ := (hcol 3).mpr rfl
          refine ⟨v, huv, ?_⟩; intro s hus hψs
          rcases hu_all s hus with hs | hs | hs | hs
          · exact hs
          · rw [hs, hψa, hψv, hi0γ] at hψs; exact absurd ((hcol 1).mp hψs) (by decide)
          · rw [hs, hψb, hψv, hi0γ] at hψs; exact absurd ((hcol 2).mp hψs) (by decide)
          · rw [hs, hψy, hψv, hi0γ] at hψs; exact absurd ((hcol 0).mp hψs) (by decide)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact (hcFun_spec α).2.1.symm)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψv, hψ_out z hz_not_S]; exact hf3.2.2.2)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hda hua.symm hap hpu.symm
          (by rw [hψu, hψ_out p0 hp_not_S]; exact hα.2.1)
      · subst r
        -- `b` 由见证色 `lam`（不同于 `ψ u = α`！）满足 PCF！
        by_cases hδlam : δ = lam
        · simp only [hδlam, ite_true] at haP_u
          have hzero : (Pb.filter (fun s => aP s = lam)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨h0, hbh, ?_⟩
          intro s hbs hψs
          rcases hb_all s hbs with hs | hs | hsPb
          · rw [hs, hψu, hψ_out h0 hh_not_S] at hψs; exact False.elim (hα.2.2 (hψs.trans hδlam))
          · exact hs
          · rw [hψPb s hsPb, hψ_out h0 hh_not_S] at hψs
            exact False.elim (hzero hsPb (hψs.trans hδlam))
        · simp only [hδlam, ite_false] at haP_u
          have hone : (Pb.filter (fun s => aP s = lam)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
          have hw₀_mem : w₀ ∈ Pb.filter (fun s => aP s = lam) := by rw [hw₀_eq]; simp
          rw [Finset.mem_filter] at hw₀_mem
          refine ⟨w₀, (mem_leafNbrs.mp hw₀_mem.1).1, ?_⟩
          intro s hbs hψs
          rcases hb_all s hbs with hs | hs | hsPb
          · rw [hs, hψu, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs; exact False.elim (hα.2.2 hψs)
          · rw [hs, hψ_out h0 hh_not_S, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
            exact False.elim (hδlam hψs)
          · rw [hψPb s hsPb, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
            have : s ∈ Pb.filter (fun t => aP t = lam) := Finset.mem_filter.mpr ⟨hsPb, hψs⟩
            rw [hw₀_eq, Finset.mem_singleton] at this; exact this
      · subst r; exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrPb).2 (mem_leafNbrs.mp hrPb).1.symm
  -- 双计数：`4 * |C₀| ≤ 2 + 2 + 2 + 3 = 9`，与 `|C₀| ≥ 3` 矛盾！
  have hlower : 4 * C₀.card ≤
      ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card := by
    calc 4 * C₀.card = ∑ _α ∈ C₀, 4 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card := by
        apply Finset.sum_le_sum; intro α hα
        exact (no_pcfRep_nil_bounds (hA_ne α) (hno_rep α hα)).2 (by simp)
  have hupper : ∑ α ∈ C₀, (Finset.univ.filter (fun i : Fin 4 => (A α i).card = 1)).card ≤ 9 := by
    rw [sum_filter_card_comm]
    have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    rw [hu4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 := (card_filter_sdiff_singleton_eq_one_le C₀ (L y) (by omega)).1
    have h1 := (card_filter_sdiff_two_fixed_eq_one_le C₀ (L a) hLa (adm.φ p0) (adm.φs p0)).1
    have h2 := (card_filter_sdiff_singleton_eq_one_le C₀ P (by rw [Finset.card_pair hγ12])).1
    have h3 := (card_filter_sdiff_triple_eq_one_le C₀ (L v) hLv cFun (adm.φ z)).1
    dsimp only [A]; omega
  omega

/-! ## 3. Lemma 3.10b（`no_one_thread_bad_neighbor`）与 Corollary 3.11 -/

private lemma nat_sub_ge_of_le2 {d lb pb t r : ℕ} (hd : 4 ≤ d) (hlb : lb = d + 1)
    (hpb : pb = d - 2) (ht : t ≤ 2) (hr : lb - t ≤ r) : pb + 1 ≤ r := by omega

private lemma nat_sub_ge_of_le3 {d lb pb t r : ℕ} (hd : 4 ≤ d) (hlb : lb = d + 1)
    (hpb : pb = d - 2) (ht : t ≤ 3) (hr : lb - t ≤ r) : pb ≤ r := by omega

private lemma nat_sub_two_ge_two {d pb : ℕ} (hd : 4 ≤ d) (hpb : pb = d - 2) :
    2 ≤ pb := by omega

private lemma nat_add_two_ne_one {n : ℕ} (h : n + 2 = 1) : False := by omega

private lemma nat_add_one_eq_one {n : ℕ} (h : n + 1 = 1) : n = 0 := by omega

/-- Lemma 3.10b：若 `coreDeg G u = 3`、`u` 关联 `2⁺`-线串 `v` 且不关联任何 `1`-线串，
则 `u` 无坏核心邻点！ -/
lemma no_one_thread_bad_neighbor {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v b : V}
    (hc3 : coreDeg G u = 3) (hv : v ∈ longThreadNbrs G u) (hno1 : oneThreadNbrs G u = ∅)
    (hb_adj : G.Adj u b) (hbad : IsBad G b) : False := by
  classical
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hdu4 : 4 ≤ G.degree u := deg_ge_four_of_longThreadNbr hm hdu3 hv
  have hdb4 : 4 ≤ G.degree b := hbad.1
  have hlong_eq : longThreadNbrs G u = {v} := by
    have hle1 := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq hc3
    have hge1 : 1 ≤ (longThreadNbrs G u).card := Finset.card_pos.mpr ⟨v, hv⟩
    rcases Finset.card_eq_one.mp (by omega : (longThreadNbrs G u).card = 1) with ⟨v', hv'⟩
    have hv_eq : v = v' := by simpa [hv'] using hv
    rw [hv', hv_eq]
  simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
  rcases hv.2 with ⟨huv, hdv, w, hvw, hwu, hdw⟩
  rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨z, hwz, hzv, hw_all⟩
  have hvb : v ≠ b := fun h => by subst h; omega
  have hub_ne : u ≠ b := G.ne_of_adj hb_adj
  have hv_core : v ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨huv, by omega⟩
  have hb_core : b ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hb_adj, by omega⟩
  rcases exists_third_coreNbr hc3 hv_core hb_core hvb with ⟨x, hx_core, hxv, hxb, hcore_eq⟩
  have hux : G.Adj u x := (mem_coreNbrs.mp hx_core).1
  -- `x` 必为 `3⁺`-度点（因 `oneThreadNbrs = ∅` 且 `longThreadNbrs = {v}`！）
  have hdx3 : 3 ≤ G.degree x := by
    have hdx2 : 2 ≤ G.degree x := (mem_coreNbrs.mp hx_core).2
    by_contra hlt; push Not at hlt
    have hx2 : x ∈ degTwoNbrs G u := by
      simp only [degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨hux, by omega⟩
    rw [degTwoNbrs_eq_one_union_long hm u, hno1, hlong_eq, Finset.empty_union,
        Finset.mem_singleton] at hx2
    exact hxv hx2
  -- 取出坏点 `b` 除 `u` 外的唯一核心邻点 `h0`（`3⁺`-度点）与叶邻点 `Pb`
  have hu_coreb : u ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hb_adj.symm, by omega⟩
  have hb_other : (coreNbrs G b \ {u}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu_coreb),
        Finset.card_singleton]; have := hbad.2; unfold coreDeg at this; omega
  rcases Finset.card_eq_one.mp hb_other with ⟨h0, hh_eq⟩
  have hh_mem : h0 ∈ coreNbrs G b \ {u} := by rw [hh_eq]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hh_mem
  have hbh : G.Adj b h0 := (mem_coreNbrs.mp hh_mem.1).1
  have hhu : h0 ≠ u := hh_mem.2
  have hdh3 : 3 ≤ G.degree h0 := bad_coreNbrs_deg_ge_three hm hpq hbad hh_mem.1
  have hcore_b : coreNbrs G b = {u, h0} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hu_coreb
      · exact hh_mem.1
    · rw [Finset.card_pair hhu.symm]; have := hbad.2; unfold coreDeg at this; omega
  let Yu := leafNbrs G u
  let Pb := leafNbrs G b
  have hYu_card : Yu.card = G.degree u - 3 := by
    dsimp only [Yu]; have := coreDeg_add_leafNbrs hm u; omega
  have hPb_card : Pb.card = G.degree b - 2 := by
    dsimp only [Pb]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  have hYP_disj : Disjoint Yu Pb := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    have h1 := mem_leafNbrs.mp hr1; have h2 := mem_leafNbrs.mp hr2
    rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨t, _, huniq⟩
    exact hub_ne ((huniq u h1.1.symm).trans (huniq b h2.1.symm).symm)
  have hwb : w ≠ b := fun h => by subst h; omega
  have hwx : w ≠ x := fun h => by subst h; omega
  have hzu : z ≠ u := fun h => no_two_thread_same_anchor hm hdu3 hdv hdw huv hvw (h ▸ hwz)
  have hzb : z ≠ b := by
    intro h; subst h
    have hbw : w ∈ longThreadNbrs G z := by
      simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hwz.symm, hdw⟩, hwz.symm, hdw, v, hvw.symm, hzv.symm, hdv⟩
    rw [bad_no_long_thread hm hpq hbad] at hbw; exact Finset.notMem_empty w hbw
  have hdz2 : 2 ≤ G.degree z := by
    have h1 := degree_ge_one hm z
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree z = 1) hwz.symm; omega
  have hdz4_of_ge3 : 3 ≤ G.degree z → 4 ≤ G.degree z := by
    intro h3; by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega) hdw hdv hwz.symm hvw.symm
  let S : Finset V := insert u (insert v (insert w (insert b (Yu ∪ Pb))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨(G.ne_of_adj hux).symm, hxv, hwx.symm, hxb,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hh_not_S : h0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hhu, fun h => by subst h; omega, fun h => by subst h; omega, (G.ne_of_adj hbh).symm,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz_not_S : z ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hzu, hzv, (G.ne_of_adj hwz).symm, hzb,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hv_all : ∀ r, G.Adj v r → r = u ∨ r = w := by
    intro r hr; have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw hwu.symm
    have : r ∈ ({u, w} : Finset V) := by rw [← hNv]; exact (G.mem_neighborFinset v r).mpr hr
    simpa using this
  have hu_all : ∀ r, G.Adj u r → r = v ∨ r = b ∨ r = x ∨ r ∈ Yu := by
    intro r hr; have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩)))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hb_all : ∀ r, G.Adj b r → r = u ∨ r = h0 ∨ r ∈ Pb := by
    intro r hr; have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcore_b, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hS_out : ∀ s, s ∉ S → ∀ q ∈ S, G.Adj s q →
      (q = u ∧ s = x) ∨ (q = w ∧ s = z) ∨ (q = b ∧ s = h0) := by
    intro s hsS q hqS hsq
    simp only [S, Finset.mem_insert, Finset.mem_union] at hqS
    rcases hqS with rfl | rfl | rfl | rfl | hqYu | hqPb
    · rcases hu_all s hsq.symm with rfl | rfl | rfl | hsYu
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hsS (by simp [S, hsYu]))
    · rcases hv_all s hsq.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hw_all s hsq.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hb_all s hsq.symm with rfl | rfl | hsPb
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact False.elim (hsS (by simp [S, hsPb]))
    · have hL := mem_leafNbrs.mp hqYu
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨r0, _, huniq⟩
      exact False.elim (hsS (((huniq s hsq.symm).trans (huniq u hL.1.symm).symm) ▸ huS))
    · have hL := mem_leafNbrs.mp hqPb
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨r0, _, huniq⟩
      exact False.elim (hsS (((huniq s hsq.symm).trans (huniq b hL.1.symm).symm) ▸
        (by simp [S] : b ∈ S)))
  -- `x, h0, z` 在 `G - S` 中皆非孤立！
  have hnoniso_z : ∃ r, r ∉ S ∧ G.Adj z r := by
    by_cases hdz2' : G.degree z = 2
    · rcases exists_other_neighbor_of_deg_two hdz2' hwz.symm with ⟨r, hzr, hrw, _⟩
      refine ⟨r, ?_, hzr⟩
      intro hrS
      rcases hS_out z hz_not_S r hrS hzr with ⟨hru, _⟩ | ⟨hrw', _⟩ | ⟨hrb, _⟩
      · subst r; exact no_three_thread_same_anchor hm hdu3 hdv hdw hdz2' huv hvw hwz hzr hzv.symm
      · exact hrw hrw'
      · subst r
        have hbz : z ∈ longThreadNbrs G b := by
          simp only [longThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨⟨hzr.symm, hdz2'⟩, hzr.symm, hdz2', w, hwz.symm, hwb, hdw⟩
        rw [bad_no_long_thread hm hpq hbad] at hbz; exact Finset.notMem_empty z hbz
    · have hdz4 := hdz4_of_ge3 (by omega)
      have hlt : ({u, w, b} : Finset V).card < (G.neighborFinset z).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; have := card_triple_le u w b; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out z hz_not_S r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hrn.1 rfl
      · exact hrn.2.1 rfl
      · exact hrn.2.2 rfl
  have hnoniso_xh : ∀ s, s ∉ S → 3 ≤ G.degree s → ∃ r, r ∉ S ∧ G.Adj s r := by
    intro s hsS hds3
    by_cases hsz : s = z
    · rw [hsz]; exact hnoniso_z
    · have hlt : ({u, b} : Finset V).card < (G.neighborFinset s).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := u) (b := b); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨r, hr, hrn⟩
      rw [SimpleGraph.mem_neighborFinset] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
      refine ⟨r, ?_, hr⟩
      intro hrS
      rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨_, hEq⟩ | ⟨rfl, _⟩
      · exact hrn.1 rfl
      · exact hsz hEq
      · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, huS⟩ with ⟨adm⟩
  have hLu : (L u).card = G.degree u + 1 := by
    rw [hm.list_card u]; simp [kappa, show G.degree u ≠ 2 by omega]
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  have hPb_L2 : ∀ r ∈ Pb, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  -- 对坏点 `b` 应用 Lemma 3.7！
  let δ := adm.φ h0
  let Cb : Finset ℕ := L b \ {δ, adm.φs h0}
  have hCb : Pb.card + 1 ≤ Cb.card := by
    dsimp only [Cb]; have := card_sdiff_ge (L b) {δ, adm.φs h0}
    have := Finset.card_le_two (a := δ) (b := adm.φs h0); omega
  rcases bad_two_color_extension (Y := Pb) (C := Cb) (δ := δ) (by omega) hPb_L2 hCb (by simp [Cb])
    with ⟨γ₁, γ₂, lam, hγ1C, hγ2C, hγ12, ⟨aP1, haP1_mem, haP1_u⟩, ⟨aP2, haP2_mem, haP2_u⟩⟩
  let P : Finset ℕ := {γ₁, γ₂}
  let β := adm.φ x
  let C : Finset ℕ := L u \ {β, adm.φs x, lam}
  have hC : G.degree u - 2 ≤ C.card := by
    dsimp only [C]; have := card_sdiff_ge (L u) {β, adm.φs x, lam}
    have := card_triple_le β (adm.φs x) lam; omega
  have hβ_not_C : β ∉ C := by simp [C]
  have hcw_ex : ∀ α : ℕ, ∃ c ∈ L w, c ≠ α ∧ c ≠ adm.φ z ∧ c ≠ adm.φs z := by
    intro α
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {α, adm.φ z, adm.φs z})
      (by have := card_triple_le α (adm.φ z) (adm.φs z); omega) with ⟨c, hc, hcn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
    exact ⟨c, hc, hcn.1, hcn.2.1, hcn.2.2⟩
  let cFun : ℕ → ℕ := fun α => (hcw_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w ∧ cFun α ≠ α ∧ cFun α ≠ adm.φ z ∧ cFun α ≠ adm.φs z :=
    fun α => (hcw_ex α).choose_spec
  have hv_not_Yu : v ∉ Yu := fun h => by rw [mem_leafNbrs] at h; omega
  have hb_not_Yu : b ∉ Yu := fun h => by rw [mem_leafNbrs] at h; omega
  have hw_not_Yu : w ∉ Yu := fun h => by rw [mem_leafNbrs] at h; omega
  have hu_not_Yu : u ∉ Yu := fun h => G.ne_of_adj (mem_leafNbrs.mp h).1 rfl
  let J : Finset V := insert v (insert b Yu)
  have hJ_card : J.card = G.degree u - 1 := by
    dsimp only [J]
    rw [Finset.card_insert_of_notMem (by simp [hvb, hv_not_Yu]),
        Finset.card_insert_of_notMem hb_not_Yu, hYu_card]
    omega
  let A : ℕ → V → Finset ℕ := fun α r =>
    if r = v then L v \ {α, cFun α, adm.φ z}
    else if r = b then P \ {α}
    else L r \ {α}
  have hA_ne : ∀ α r (hr : r ∈ J), (A α r).Nonempty := by
    intro α r hr; rw [← Finset.card_pos]
    dsimp only [A]; split_ifs with hrv hrb
    · have := card_sdiff_ge (L v) {α, cFun α, adm.φ z}
      have := card_triple_le α (cFun α) (adm.φ z); omega
    · have := card_sdiff_ge P {α}
      dsimp only [P] at *; rw [Finset.card_pair hγ12, Finset.card_singleton] at this; omega
    · have hrYu : r ∈ Yu := by
        simp only [J, Finset.mem_insert] at hr; exact (hr.resolve_left hrv).resolve_left hrb
      have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrYu).2]
      have := card_sdiff_ge (L r) {α}; simp only [Finset.card_singleton] at this; omega
  have hno_rep : ∀ α ∈ C,
      ¬ ∃ f : {r : V // r ∈ J} → ℕ, IsPCFRep (fun i => A α i.val) [β] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    have hvJ : v ∈ J := Finset.mem_insert_self v _
    have hbJ : b ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_self b Yu)
    have hfv : f ⟨v, hvJ⟩ ∈ L v \ {α, cFun α, adm.φ z} := by simpa [A] using hf_mem ⟨v, hvJ⟩
    have hfb : f ⟨b, hbJ⟩ ∈ P \ {α} := by simpa [A, hvb.symm] using hf_mem ⟨b, hbJ⟩
    simp only [P, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hfv hfb
    have hfbC : f ⟨b, hbJ⟩ ∈ Cb := by
      rcases hfb.1 with h | h
      · rw [h]; exact hγ1C
      · rw [h]; exact hγ2C
    simp only [Cb, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hfbC
    let aP : V → ℕ := if f ⟨b, hbJ⟩ = γ₁ then aP1 else aP2
    have haP_mem : ∀ r ∈ Pb, aP r ∈ L r ∧ aP r ≠ f ⟨b, hbJ⟩ := by
      intro r hr; dsimp only [aP]; split_ifs with h
      · rw [h]; exact haP1_mem r hr
      · rw [hfb.1.resolve_left h]; exact haP2_mem r hr
    have haP_u : (Pb.filter (fun r => aP r = lam)).card + (if δ = lam then 1 else 0) = 1 := by
      by_cases h : f ⟨b, hbJ⟩ = γ₁
      · simp only [aP, h, ite_true]; exact haP1_u
      · simp only [aP, h, ite_false]; exact haP2_u
    let ψ : V → ℕ := fun r =>
      if r = u then α
      else if r = w then cFun α
      else if hrJ : r ∈ J then f ⟨r, hrJ⟩
      else if r ∈ Pb then aP r
      else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψw : ψ w = cFun α := by simp [ψ, hwu]
    have hψJ : ∀ r (hr : r ∈ J), ψ r = f ⟨r, hr⟩ := by
      intro r hr
      have hru : r ≠ u := by
        simp only [J, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hrYu
        · exact (G.ne_of_adj huv).symm
        · exact hub_ne.symm
        · exact fun h => hu_not_Yu (h ▸ hrYu)
      have hrw : r ≠ w := by
        simp only [J, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hrYu
        · exact G.ne_of_adj hvw
        · exact hwb.symm
        · exact fun h => hw_not_Yu (h ▸ hrYu)
      simp only [ψ, hru, hrw, ite_false, hr, dite_true]
    have hψPb : ∀ r ∈ Pb, ψ r = aP r := by
      intro r hr
      have hru : r ≠ u := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrw : r ≠ w := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrJ : r ∉ J := by
        simp only [J, Finset.mem_insert, not_or]
        exact ⟨fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega,
          fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega,
          fun h => Finset.disjoint_left.mp hYP_disj h hr⟩
      simp only [ψ, hru, hrw, hrJ, ite_false, dite_false, hr, ite_true]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      have hrJ : r ∉ J := by simp [J, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1]
      simp only [ψ, hr.1, hr.2.2.1, hrJ, hr.2.2.2.2.2, ite_false, dite_false]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with hr1 | hr2 | hr3 | hr4 | hrYu | hrPb
      · rw [hr1, hψu]; exact hα.1
      · rw [hr2, hψJ v hvJ]; exact hfv.1
      · rw [hr3, hψw]; exact (hcFun_spec α).1
      · rw [hr4, hψJ b hbJ]; exact hfbC.1
      · have hrJ : r ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hrYu)
        have hrv' : r ≠ v := fun h => hv_not_Yu (h ▸ hrYu)
        have hrb' : r ≠ b := fun h => hb_not_Yu (h ▸ hrYu)
        have hm' := hf_mem ⟨r, hrJ⟩; simp only [A, hrv', hrb', ite_false, Finset.mem_sdiff] at hm'
        rw [hψJ r hrJ]; exact hm'.1
      · rw [hψPb r hrPb]; exact (haP_mem r hrPb).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with h' | h' | h' | h' | haYu | haPb
        · subst a'
          rcases hu_all b' hab with hb | hb | hb | hbYu
          · rw [hb, hψu, hψJ v hvJ]; exact Ne.symm hfv.2.1
          · rw [hb, hψu, hψJ b hbJ]; exact Ne.symm hfb.2
          · rw [hb, hψu, hψ_out x hx_not_S]; exact hα.2.1
          · have hbJ' : b' ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hbYu)
            have hbv' : b' ≠ v := fun h => hv_not_Yu (h ▸ hbYu)
            have hbb' : b' ≠ b := fun h => hb_not_Yu (h ▸ hbYu)
            have hm' := hf_mem ⟨b', hbJ'⟩
            simp only [A, hbv', hbb', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
            rw [hψu, hψJ b' hbJ']; exact Ne.symm hm'.2
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψJ v hvJ, hψu]; exact hfv.2.1
          · rw [hb, hψJ v hvJ, hψw]; exact hfv.2.2.1
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψJ v hvJ]; exact Ne.symm hfv.2.2.1
          · rw [hb, hψw, hψ_out z hz_not_S]; exact (hcFun_spec α).2.2.1
        · subst a'
          rcases hb_all b' hab with hb | hb | hbPb
          · rw [hb, hψJ b hbJ, hψu]; exact hfb.2
          · rw [hb, hψJ b hbJ, hψ_out h0 hh_not_S]; exact hfbC.2.1
          · rw [hψJ b hbJ, hψPb b' hbPb]; exact (haP_mem b' hbPb).2.symm
        · have haL := mem_leafNbrs.mp haYu
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨r0, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u haL.1.symm).symm
          have haJ' : a' ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haYu)
          have hav' : a' ≠ v := fun h => hv_not_Yu (h ▸ haYu)
          have hab' : a' ≠ b := fun h => hb_not_Yu (h ▸ haYu)
          have hm' := hf_mem ⟨a', haJ'⟩
          simp only [A, hav', hab', ite_false, Finset.mem_sdiff, Finset.mem_singleton] at hm'
          rw [hb, hψJ a' haJ', hψu]; exact hm'.2
        · have haL := mem_leafNbrs.mp haPb
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨r0, _, huniq⟩
          have hb : b' = b := (huniq b' hab).trans (huniq b haL.1.symm).symm
          rw [hb, hψPb a' haPb, hψJ b hbJ]; exact (haP_mem a' haPb).2
      rcases hor with h' | h'
      · exact hcase r₁ r₂ h12 h'
      · exact (hcase r₂ r₁ h12.symm h').symm
    · intro s hsS _ q hqS hsq
      rcases hS_out s hsS q hqS hsq with ⟨hqu, hsx⟩ | ⟨hqw, hsz⟩ | ⟨hqb, hsh⟩
      · rw [hqu, hsx, hψu]; exact hα.2.2.1
      · rw [hqw, hsz, hψw]; exact (hcFun_spec α).2.2.2
      · rw [hqb, hsh, hψJ b hbJ]; exact hfbC.2.2
    · intro s hsS hiso ⟨q, hsq⟩
      have hqS : q ∈ S := by by_contra h; exact hiso q h hsq
      rcases hS_out s hsS q hqS hsq with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩
      · subst s; rcases hnoniso_xh x hx_not_S hdx3 with ⟨r, hrS, hxr⟩
        exact False.elim (hiso r hrS hxr)
      · subst s; rcases hnoniso_z with ⟨r, hrS, hzr⟩; exact False.elim (hiso r hrS hzr)
      · subst s; rcases hnoniso_xh h0 hh_not_S hdh3 with ⟨r, hrS, hhr⟩
        exact False.elim (hiso r hrS hhr)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with h' | h' | h' | h' | hrYu | hrPb
      · subst r
        by_cases hγβ : γ = β
        · subst hγβ
          have hcnt : ([β] : List ℕ).count β = 1 := by simp
          have hzero : (Finset.univ.filter (fun i : {t // t ∈ J} => f i = β)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨x, hux, ?_⟩
          intro t hut hψt
          rcases hu_all t hut with htv | htb | htx | htYu
          · rw [htv, hψJ v hvJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨v, hvJ⟩) hψt)
          · rw [htb, hψJ b hbJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨b, hbJ⟩) hψt)
          · exact htx
          · have htJ : t ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htYu)
            rw [hψJ t htJ, hψ_out x hx_not_S] at hψt
            exact False.elim (hzero (Finset.mem_univ ⟨t, htJ⟩) hψt)
        · have hcnt : ([β] : List ℕ).count γ = 0 := by
            rw [List.count_eq_zero]; simpa using hγβ
          have hone : (Finset.univ.filter (fun i : {t // t ∈ J} => f i = γ)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨⟨t₀, ht₀⟩, ht₀_eq⟩
          have ht₀_col : f ⟨t₀, ht₀⟩ = γ := by
            have : (⟨t₀, ht₀⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) := by
              rw [ht₀_eq]; simp
            exact (Finset.mem_filter.mp this).2
          have hut0 : G.Adj u t₀ := by
            simp only [J, Finset.mem_insert] at ht₀
            rcases ht₀ with rfl | rfl | htYu
            · exact huv
            · exact hb_adj
            · exact (mem_leafNbrs.mp htYu).1
          refine ⟨t₀, hut0, ?_⟩
          intro t hut hψt
          rcases hu_all t hut with htv | htb | htx | htYu
          · rw [htv, hψJ v hvJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨v, hvJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact htv.trans (congrArg Subtype.val this)
          · rw [htb, hψJ b hbJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨b, hbJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact htb.trans (congrArg Subtype.val this)
          · rw [htx, hψ_out x hx_not_S, hψJ t₀ ht₀, ht₀_col] at hψt
            exact False.elim (hγβ hψt.symm)
          · have htJ : t ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htYu)
            rw [hψJ t htJ, hψJ t₀ ht₀, ht₀_col] at hψt
            have : (⟨t, htJ⟩ : {t // t ∈ J}) ∈ Finset.univ.filter (fun i => f i = γ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψt⟩
            rw [ht₀_eq, Finset.mem_singleton] at this; exact congrArg Subtype.val this
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact (hcFun_spec α).2.1.symm)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψJ v hvJ, hψ_out z hz_not_S]; exact hfv.2.2.2)
      · subst r
        by_cases hδlam : δ = lam
        · simp only [hδlam, ite_true] at haP_u
          have hzero : (Pb.filter (fun s => aP s = lam)).card = 0 := by omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨h0, hbh, ?_⟩
          intro s hbs hψs
          rcases hb_all s hbs with hs | hs | hsPb
          · rw [hs, hψu, hψ_out h0 hh_not_S] at hψs; exact False.elim (hα.2.2.2 (hψs.trans hδlam))
          · exact hs
          · rw [hψPb s hsPb, hψ_out h0 hh_not_S] at hψs
            exact False.elim (hzero hsPb (hψs.trans hδlam))
        · simp only [hδlam, ite_false] at haP_u
          have hone : (Pb.filter (fun s => aP s = lam)).card = 1 := by omega
          rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
          have hw₀_mem : w₀ ∈ Pb.filter (fun s => aP s = lam) := by rw [hw₀_eq]; simp
          rw [Finset.mem_filter] at hw₀_mem
          refine ⟨w₀, (mem_leafNbrs.mp hw₀_mem.1).1, ?_⟩
          intro s hbs hψs
          rcases hb_all s hbs with hs | hs | hsPb
          · rw [hs, hψu, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs; exact False.elim (hα.2.2.2 hψs)
          · rw [hs, hψ_out h0 hh_not_S, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
            exact False.elim (hδlam hψs)
          · rw [hψPb s hsPb, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
            have : s ∈ Pb.filter (fun t => aP t = lam) := Finset.mem_filter.mpr ⟨hsPb, hψs⟩
            rw [hw₀_eq, Finset.mem_singleton] at this; exact this
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrYu).2 (mem_leafNbrs.mp hrYu).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrPb).2 (mem_leafNbrs.mp hrPb).1.symm
  -- 双计数：`3 * |C| ≤ ∑ q_α ≤ 3 + 2 + 2 * |Yu| = 2k - 1` → 排除 `k ≥ 6` 与 `k = 5`！
  have hlower : 3 * C.card ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
    calc 3 * C.card = ∑ _α ∈ C, 3 := by simp [mul_comm]
      _ ≤ ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card := by
        apply Finset.sum_le_sum; intro α hα
        have : Nonempty {r : V // r ∈ J} := ⟨⟨v, Finset.mem_insert_self v _⟩⟩
        have hq3 := (no_pcfRep_single_bounds (fun i : {r // r ∈ J} => hA_ne α i.val i.property)
          (hno_rep α hα)).2.2.1 (by rw [Fintype.card_coe, hJ_card]; omega)
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
  have hterm_v : (C.filter (fun α => (A α v).card = 1)).card ≤ 3 := by
    have hEq : C.filter (fun α => (A α v).card = 1) =
        C.filter (fun α => (L v \ {α, cFun α, adm.φ z}).card = 1) := by congr 1; ext α; simp [A]
    rw [hEq]; exact (card_filter_sdiff_triple_eq_one_le C (L v) hLv cFun (adm.φ z)).1
  have hterm_b : (C.filter (fun α => (A α b).card = 1)).card ≤ 2 := by
    have hEq : C.filter (fun α => (A α b).card = 1) =
        C.filter (fun α => (P \ {α}).card = 1) := by congr 1; ext α; simp [A, hvb.symm]
    rw [hEq]; exact (card_filter_sdiff_singleton_eq_one_le C P (by rw [Finset.card_pair hγ12])).1
  have hterm_Yu : ∀ r ∈ Yu, (C.filter (fun α => (A α r).card = 1)).card ≤ 2 := by
    intro r hr
    have hrv : r ≠ v := fun h => hv_not_Yu (h ▸ hr)
    have hrb : r ≠ b := fun h => hb_not_Yu (h ▸ hr)
    have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
    have hEq : C.filter (fun α => (A α r).card = 1) =
        C.filter (fun α => (L r \ {α}).card = 1) := by congr 1; ext α; simp [A, hrv, hrb]
    rw [hEq]; exact (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).1
  have hsplit : ∑ α ∈ C, (J.filter (fun r => (A α r).card = 1)).card =
      (C.filter (fun α => (A α v).card = 1)).card +
      (C.filter (fun α => (A α b).card = 1)).card +
      ∑ r ∈ Yu, (C.filter (fun α => (A α r).card = 1)).card := by
    rw [sum_filter_card_comm]
    dsimp only [J]
    rw [Finset.sum_insert (by simp [hvb, hv_not_Yu]), Finset.sum_insert hb_not_Yu]; omega
  have hsumY_le : ∑ r ∈ Yu, (C.filter (fun α => (A α r).card = 1)).card ≤ 2 * Yu.card := by
    calc ∑ r ∈ Yu, (C.filter (fun α => (A α r).card = 1)).card
        ≤ ∑ _r ∈ Yu, 2 := Finset.sum_le_sum hterm_Yu
      _ = 2 * Yu.card := by simp [mul_comm]
  have hdu_le5 : G.degree u ≤ 5 := by omega
  by_cases hdu5 : G.degree u = 5
  · -- `k = 5`：处处取等 → `∀ r ∈ J, A α r ⊆ C` → `β` 唯一矛盾！
    have hv_eq3 : (C.filter (fun α => (A α v).card = 1)).card = 3 := by omega
    have hb_eq2 : (C.filter (fun α => (A α b).card = 1)).card = 2 := by omega
    have hY_eq : ∑ r ∈ Yu, (C.filter (fun α => (A α r).card = 1)).card = 2 * Yu.card := by omega
    have hA_sub_C : ∀ α (r : V), r ∈ J → A α r ⊆ C := by
      intro α r hr; simp only [J, Finset.mem_insert] at hr
      rcases hr with hrv | hrb | hrYu
      · subst r
        have hEq : C.filter (fun γ => (A γ v).card = 1) =
            C.filter (fun γ => (L v \ {γ, cFun γ, adm.φ z}).card = 1) := by congr 1; ext γ; simp [A]
        rw [hEq] at hv_eq3
        have hsub := (card_filter_sdiff_triple_eq_one_le C (L v) hLv cFun (adm.φ z)).2 hv_eq3
        intro c hc; simp only [A, ite_true, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hc
        exact hsub.2 (Finset.mem_sdiff.mpr ⟨hc.1, by simp [hc.2.2.2]⟩)
      · subst r
        have hEq : C.filter (fun γ => (A γ b).card = 1) =
            C.filter (fun γ => (P \ {γ}).card = 1) := by congr 1; ext γ; simp [A, hvb.symm]
        rw [hEq] at hb_eq2
        have hsub := (card_filter_sdiff_singleton_eq_one_le C P
          (by rw [Finset.card_pair hγ12])).2 hb_eq2
        intro c hc; simp only [A, hvb.symm, ite_false, ite_true, Finset.mem_sdiff] at hc
        exact hsub.2 hc.1
      · have hrv : r ≠ v := fun h => hv_not_Yu (h ▸ hrYu)
        have hrb : r ≠ b := fun h => hb_not_Yu (h ▸ hrYu)
        have heq2 : (C.filter (fun γ => (A γ r).card = 1)).card = 2 := by
          by_contra hne2
          have hlt2 : (C.filter (fun γ => (A γ r).card = 1)).card < 2 := by
            have := hterm_Yu r hrYu; omega
          have hlt_sum : ∑ s ∈ Yu, (C.filter (fun γ => (A γ s).card = 1)).card < ∑ _s ∈ Yu, 2 :=
            Finset.sum_lt_sum hterm_Yu ⟨r, hrYu, hlt2⟩
          simp only [Finset.sum_const, smul_eq_mul] at hlt_sum; omega
        have hLr : (L r).card = 2 := by rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hrYu).2]
        have hEq : C.filter (fun γ => (A γ r).card = 1) =
            C.filter (fun γ => (L r \ {γ}).card = 1) := by congr 1; ext γ; simp [A, hrv, hrb]
        rw [hEq] at heq2
        have hsub := (card_filter_sdiff_singleton_eq_one_le C (L r) (by omega)).2 heq2
        intro c hc; simp only [A, hrv, hrb, ite_false, Finset.mem_sdiff] at hc; exact hsub.2 hc.1
    rcases Finset.card_pos.mp (by omega : 0 < C.card) with ⟨α₀, hα₀⟩
    apply hno_rep α₀ hα₀
    refine ⟨fun i => (hA_ne α₀ i.val i.property).choose,
      fun i => (hA_ne α₀ i.val i.property).choose_spec, β, ?_⟩
    have hzero : (Finset.univ.filter (fun i : {r // r ∈ J} =>
        (hA_ne α₀ i.val i.property).choose = β)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ heq
      exact hβ_not_C (heq ▸ hA_sub_C α₀ i.val i.property (hA_ne α₀ i.val i.property).choose_spec)
    rw [hzero]; simp
  · -- `k = 4`：`Yu = {y}`, `|J| = 3`, `|C| = 2`, 改染 `u ↦ lam, y ↦ c₁, w ↦ c₁, v ↦ c₂` 后对 `b` 用定色延拓！
    have hdu_eq4 : G.degree u = 4 := by omega
    have hYu1 : Yu.card = 1 := by omega
    rcases Finset.card_eq_one.mp hYu1 with ⟨y, hy_eq⟩
    have hy_Yu : y ∈ Yu := by rw [hy_eq]; simp
    have hy_mem := mem_leafNbrs.mp hy_Yu
    rcases hy_mem with ⟨huy, hdy⟩
    have hLy : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
    have hC2 : C.card = 2 := by omega
    rcases Finset.card_eq_two.mp hC2 with ⟨c₁, c₂, hc12, hC_eq⟩
    have hc1C : c₁ ∈ C := by rw [hC_eq]; simp
    have hc2C : c₂ ∈ C := by rw [hC_eq]; simp
    -- 对 `α ∈ C`，因 `|J| = 3` 且 `q_α ≥ 3`，故 `A α r` 全是单点集！
    have hall_sing : ∀ α ∈ C, ∀ r ∈ J, (A α r).card = 1 := by
      intro α hα r hr
      have : Nonempty {t : V // t ∈ J} := ⟨⟨v, Finset.mem_insert_self v _⟩⟩
      have hq3 := (no_pcfRep_single_bounds (fun i : {t // t ∈ J} => hA_ne α i.val i.property)
        (hno_rep α hα)).2.2.1 (by rw [Fintype.card_coe, hJ_card]; omega)
      have hbij :
          (Finset.univ.filter (fun i : {t // t ∈ J} => (A α i.val).card = 1)).card =
          (J.filter (fun t => (A α t).card = 1)).card := by
        apply Finset.card_bij (fun i _ => i.val)
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨i.property, hi⟩
        · intro i₁ _ i₂ _ h; exact Subtype.ext h
        · intro t ht; simp only [Finset.mem_filter] at ht
          exact ⟨⟨t, ht.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.2⟩, rfl⟩
      rw [hbij] at hq3
      have hEq : J.filter (fun t => (A α t).card = 1) = J :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ J) (by omega)
      have : r ∈ J.filter (fun t => (A α t).card = 1) := by rw [hEq]; exact hr
      exact (Finset.mem_filter.mp this).2
    have hLy_eq : L y = {c₁, c₂} := by
      have hEq : C.filter (fun α => (L y \ {α}).card = 1) = C := by
        apply Finset.filter_true_of_mem; intro α hα
        have hyJ : y ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy_Yu)
        have h1 := hall_sing α hα y hyJ
        have hyv : y ≠ v := fun h => hv_not_Yu (h ▸ hy_Yu)
        have hyb : y ≠ b := fun h => hb_not_Yu (h ▸ hy_Yu)
        simpa [A, hyv, hyb] using h1
      have hsub := ((card_filter_sdiff_singleton_eq_one_le C (L y) (by omega)).2
        (by rw [hEq, hC2])).2
      rw [hC_eq] at hsub
      exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hc12, hLy])
    have hP_eq : P = {c₁, c₂} := by
      have hEq : C.filter (fun α => (P \ {α}).card = 1) = C := by
        apply Finset.filter_true_of_mem; intro α hα
        have hbJ : b ∈ J := Finset.mem_insert_of_mem (Finset.mem_insert_self b Yu)
        have h1 := hall_sing α hα b hbJ
        simpa [A, hvb.symm] using h1
      have hsub := ((card_filter_sdiff_singleton_eq_one_le C P
        (by rw [Finset.card_pair hγ12])).2 (by rw [hEq, hC2])).2
      rw [hC_eq] at hsub
      exact Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_pair hc12, Finset.card_pair hγ12])
    -- 推出 `L v \ {c_i, cFun c_i, φ z} = {β}`！
    have hAv_β : ∀ ci cj : ℕ, ci ∈ C → cj ∈ C → ci ≠ cj →
        ({ci, cj} : Finset ℕ) = C → L v \ {ci, cFun ci, adm.φ z} = {β} := by
      intro ci cj hci hcj hne hpair
      have hvJ : v ∈ J := Finset.mem_insert_self v _
      have hs := hall_sing ci hci v hvJ
      simp only [A, ite_true] at hs
      rcases Finset.card_eq_one.mp hs with ⟨d, hd⟩
      have hd_eq : d = β := by
        by_contra hdβ
        apply hno_rep ci hci
        have hcj_Ly : cj ∈ L y \ {ci} := by rw [hLy_eq, ← hC_eq, ← hpair]; simp [hne.symm]
        have hcj_P : cj ∈ P \ {ci} := by rw [hP_eq, ← hC_eq, ← hpair]; simp [hne.symm]
        have hd_Lv : d ∈ L v \ {ci, cFun ci, adm.φ z} := by rw [hd]; simp
        have hcjβ : cj ≠ β := fun h => hβ_not_C (h ▸ hcj)
        let f : {t : V // t ∈ J} → ℕ := fun i => if i.val = v then d else cj
        refine ⟨f, ?_, β, ?_⟩
        · intro i; have hi := i.property; simp only [J, Finset.mem_insert] at hi
          rcases hi with h | h | hiYu
          · simp only [f, A, h, ite_true]; exact hd_Lv
          · simp only [f, A, h, hvb.symm, ite_false, ite_true]; exact hcj_P
          · have hiy : i.val = y :=
              Finset.mem_singleton.mp ((Finset.ext_iff.mp hy_eq i.val).mp hiYu)
            have hyv : y ≠ v := fun he => hv_not_Yu (he ▸ hy_Yu)
            have hyb : y ≠ b := fun he => hb_not_Yu (he ▸ hy_Yu)
            simp only [f, A, hiy, hyv, hyb, ite_false]; exact hcj_Ly
        · have hzero : (Finset.univ.filter (fun i : {t // t ∈ J} => f i = β)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i _; dsimp only [f]; split_ifs
            · exact hdβ
            · exact hcjβ
          rw [hzero]; simp
      rw [hd, hd_eq]
    have hAv1 := hAv_β c₁ c₂ hc1C hc2C hc12 hC_eq.symm
    have hAv2 := hAv_β c₂ c₁ hc2C hc1C hc12.symm (by rw [Finset.pair_comm, hC_eq])
    rcases four_set_sdiff_eq_singleton_pair hLv hc12 hAv1 hAv2 with
      ⟨hω1, hω2, _, _, hc1z, hc1β, hc2z, hc2β, _⟩
    -- 因为 `|L u| = 5` 且 `|L u \ {β, φ* x, lam}| = 2`，三色 `β, φ* x, lam` 互异且全在 `L u` 中！
    have hlam_spec : lam ∈ L u ∧ lam ≠ β ∧ lam ≠ adm.φs x := by
      have hcardI : (L u ∩ {β, adm.φs x, lam}).card = 3 := by
        have h1 := Finset.card_sdiff_add_card_inter (L u) {β, adm.φs x, lam}
        have h2 : (L u \ {β, adm.φs x, lam}).card = 2 := hC2
        have h3 : (L u ∩ {β, adm.φs x, lam}).card ≤ 3 :=
          le_trans (Finset.card_le_card (Finset.inter_subset_right (s₁ := L u)))
            (card_triple_le β (adm.φs x) lam)
        omega
      have htri3 : ({β, adm.φs x, lam} : Finset ℕ).card = 3 := by
        have h1 : (L u ∩ {β, adm.φs x, lam}).card ≤ ({β, adm.φs x, lam} : Finset ℕ).card :=
          Finset.card_le_card (Finset.inter_subset_right (s₁ := L u))
        have h2 := card_triple_le β (adm.φs x) lam; omega
      have hEqI : L u ∩ {β, adm.φs x, lam} = {β, adm.φs x, lam} :=
        Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := L u)) (by omega)
      have hlamLu : lam ∈ L u := by
        have : lam ∈ L u ∩ {β, adm.φs x, lam} := by rw [hEqI]; simp
        exact (Finset.mem_inter.mp this).1
      have hlamβ : lam ≠ β := by
        intro h; rw [h] at htri3
        have hsub : ({β, adm.φs x, β} : Finset ℕ) ⊆ {β, adm.φs x} := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inl rfl
        have := le_trans (Finset.card_le_card hsub) (Finset.card_le_two (a := β) (b := adm.φs x))
        omega
      have hlamφx : lam ≠ adm.φs x := by
        intro h; rw [h] at htri3
        have hsub : ({β, adm.φs x, adm.φs x} : Finset ℕ) ⊆ {β, adm.φs x} := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inr rfl
        have := le_trans (Finset.card_le_card hsub) (Finset.card_le_two (a := β) (b := adm.φs x))
        omega
      exact ⟨hlamLu, hlamβ, hlamφx⟩
    have hc1lam : c₁ ≠ lam := by
      simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1C
      exact hc1C.2.2.2
    have hc2lam : c₂ ≠ lam := by
      simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2C
      exact hc2C.2.2.2
    -- 对坏点 `b` 调用 `bad_fixed_color_extension`（给定 `u ↦ lam` 与 `h0 ↦ δ`）！
    let R : Finset ℕ := L b \ {lam, δ, adm.φs h0}
    have hR : (if lam = δ then Pb.card + 1 else Pb.card) ≤ R.card := by
      dsimp only [R]; split_ifs with h
      · have hsub : ({lam, δ, adm.φs h0} : Finset ℕ) ⊆ {lam, adm.φs h0} := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inl h.symm
          · exact Or.inr rfl
        have h1 := card_sdiff_ge (L b) {lam, δ, adm.φs h0}
        have h2 := le_trans (Finset.card_le_card hsub)
          (Finset.card_le_two (a := lam) (b := adm.φs h0))
        exact nat_sub_ge_of_le2 hdb4 hLb hPb_card h2 h1
      · have h1 := card_sdiff_ge (L b) {lam, δ, adm.φs h0}
        have h2 := card_triple_le lam δ (adm.φs h0)
        exact nat_sub_ge_of_le3 hdb4 hLb hPb_card h2 h1
    rcases bad_fixed_color_extension (Y := Pb) (R := R) (ρ := lam) (δ := δ)
      (nat_sub_two_ge_two hdb4 hPb_card)
      hPb_L2 (by simp [R]) hR with ⟨cb, hcbR, aP, haP_mem, γb, hγb⟩
    simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
    -- 构造完整着色：`u ↦ lam, y ↦ c₁, w ↦ c₁, v ↦ c₂, b ↦ cb, Pb ↦ aP`！
    have hc1_Lw : c₁ ∈ L w ∧ c₁ ≠ adm.φ z ∧ c₁ ≠ adm.φs z := by
      rw [← hω2]; exact ⟨(hcFun_spec c₂).1, (hcFun_spec c₂).2.2.1, (hcFun_spec c₂).2.2.2⟩
    have hc2_Lv : c₂ ∈ L v := by
      have : L v \ {c₁, c₂, adm.φ z} = {β} := hω1 ▸ hAv1
      have hcardI : (L v ∩ {c₁, c₂, adm.φ z}).card = 3 := by
        have h1 := Finset.card_sdiff_add_card_inter (L v) {c₁, c₂, adm.φ z}
        rw [this, Finset.card_singleton, hLv] at h1
        exact Nat.add_left_cancel (n := 1) h1
      have htri : ({c₁, c₂, adm.φ z} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hc12, hc1z]), Finset.card_pair hc2z]
      have hEqI : L v ∩ {c₁, c₂, adm.φ z} = {c₁, c₂, adm.φ z} :=
        Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := L v))
          (by rw [htri, hcardI])
      have : c₂ ∈ L v ∩ {c₁, c₂, adm.φ z} := by rw [hEqI]; simp
      exact (Finset.mem_inter.mp this).1
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have hvw_ne : v ≠ w := G.ne_of_adj hvw
    have huy_ne : u ≠ y := G.ne_of_adj huy
    have hvy : v ≠ y := fun h => hv_not_Yu (h ▸ hy_Yu)
    have hwy : w ≠ y := fun h => hw_not_Yu (h ▸ hy_Yu)
    have hby : b ≠ y := fun h => hb_not_Yu (h ▸ hy_Yu)
    have hy_not_Pb : y ∉ Pb := fun h => Finset.disjoint_left.mp hYP_disj hy_Yu h
    let ψ : V → ℕ := fun r =>
      if r = u then lam else if r = v then c₂ else if r = w then c₁
      else if r = b then cb else if r = y then c₁
      else if r ∈ Pb then aP r else adm.φ r
    have hψu : ψ u = lam := by simp [ψ]
    have hψv : ψ v = c₂ := by simp [ψ, huv_ne.symm]
    have hψw : ψ w = c₁ := by simp [ψ, hwu, hvw_ne.symm]
    have hψb : ψ b = cb := by simp [ψ, hub_ne.symm, hvb.symm, hwb.symm]
    have hψy : ψ y = c₁ := by simp [ψ, huy_ne.symm, hvy.symm, hwy.symm, hby.symm]
    have hψPb : ∀ r ∈ Pb, ψ r = aP r := by
      intro r hr
      have hru : r ≠ u := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrv : r ≠ v := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrw : r ≠ w := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hrb : r ≠ b := fun h => by rw [h] at hr; rw [mem_leafNbrs] at hr; omega
      have hry : r ≠ y := fun h => hy_not_Pb (h ▸ hr)
      simp [ψ, hru, hrv, hrw, hrb, hry, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      have hry : r ≠ y := fun h => hr.2.2.2.2.1 (h ▸ hy_Yu)
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hry, hr.2.2.2.2.2]
    have hy_only : ∀ r, G.Adj y r → r = u := by
      rcases exists_unique_neighbor_of_deg_one hdy with ⟨r0, _, huniq⟩
      exact fun r hr => (huniq r hr).trans (huniq u huy.symm).symm
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | rfl | rfl | hrYu | hrPb
      · rw [hψu]; exact hlam_spec.1
      · rw [hψv]; exact hc2_Lv
      · rw [hψw]; exact hc1_Lw.1
      · rw [hψb]; exact hcbR.1
      · have hry : r = y := by rw [hy_eq, Finset.mem_singleton] at hrYu; exact hrYu
        rw [hry, hψy, hLy_eq]; simp
      · rw [hψPb r hrPb]; exact (haP_mem r hrPb).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with h' | h' | h' | h' | haYu | haPb
        · subst a'
          rcases hu_all b' hab with hb | hb | hb | hbYu
          · rw [hb, hψu, hψv]; exact hc2lam.symm
          · rw [hb, hψu, hψb]; exact Ne.symm hcbR.2.1
          · rw [hb, hψu, hψ_out x hx_not_S]; exact hlam_spec.2.1
          · have hby' : b' = y := by rw [hy_eq, Finset.mem_singleton] at hbYu; exact hbYu
            rw [hby', hψu, hψy]; exact hc1lam.symm
        · subst a'
          rcases hv_all b' hab with hb | hb
          · rw [hb, hψv, hψu]; exact hc2lam
          · rw [hb, hψv, hψw]; exact hc12.symm
        · subst a'
          rcases hw_all b' hab with hb | hb
          · rw [hb, hψw, hψv]; exact hc12
          · rw [hb, hψw, hψ_out z hz_not_S]; exact hc1_Lw.2.1
        · subst a'
          rcases hb_all b' hab with hb | hb | hbPb
          · rw [hb, hψb, hψu]; exact hcbR.2.1
          · rw [hb, hψb, hψ_out h0 hh_not_S]; exact hcbR.2.2.1
          · rw [hψb, hψPb b' hbPb]; exact (haP_mem b' hbPb).2.symm
        · have hay : a' = y := by rw [hy_eq, Finset.mem_singleton] at haYu; exact haYu
          rw [hay, hy_only b' (hay ▸ hab), hψy, hψu]; exact hc1lam
        · have haL := mem_leafNbrs.mp haPb
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨r0, _, huniq⟩
          have hb : b' = b := (huniq b' hab).trans (huniq b haL.1.symm).symm
          rw [hb, hψPb a' haPb, hψb]; exact (haP_mem a' haPb).2
      rcases hor with h' | h'
      · exact hcase r₁ r₂ h12 h'
      · exact (hcase r₂ r₁ h12.symm h').symm
    · intro s hsS _ q hqS hsq
      rcases hS_out s hsS q hqS hsq with ⟨hqu, hsx⟩ | ⟨hqw, hsz⟩ | ⟨hqb, hsh⟩
      · rw [hqu, hsx, hψu]; exact hlam_spec.2.2
      · rw [hqw, hsz, hψw]; exact hc1_Lw.2.2
      · rw [hqb, hsh, hψb]; exact hcbR.2.2.2
    · intro s hsS hiso ⟨q, hsq⟩
      have hqS : q ∈ S := by by_contra h; exact hiso q h hsq
      rcases hS_out s hsS q hqS hsq with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩
      · subst s; rcases hnoniso_xh x hx_not_S hdx3 with ⟨r, hrS, hxr⟩
        exact False.elim (hiso r hrS hxr)
      · subst s; rcases hnoniso_z with ⟨r, hrS, hzr⟩; exact False.elim (hiso r hrS hzr)
      · subst s; rcases hnoniso_xh h0 hh_not_S hdh3 with ⟨r, hrS, hhr⟩
        exact False.elim (hiso r hrS hhr)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with h' | h' | h' | h' | hrYu | hrPb
      · subst r
        -- `u` 的四个邻点 `y (c₁), v (c₂), x (β), b (cb)` 前三色两两互异，自动满足 PCF！
        exact pcf_at_deg_four_of_three_distinct huy huv
          (fun t hut => by
            rcases hu_all t hut with h | h | h | htYu
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))
            · exact Or.inr (Or.inr (Or.inl h))
            · rw [hy_eq, Finset.mem_singleton] at htYu; exact Or.inl htYu)
          (by rw [hψy, hψv]; exact hc12)
          (by rw [hψy, hψ_out x hx_not_S]; exact hc1β)
          (by rw [hψv, hψ_out x hx_not_S]; exact hc2β)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw hwu.symm
          (by rw [hψu, hψw]; exact hc1lam.symm)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwz hzv.symm
          (by rw [hψv, hψ_out z hz_not_S]; exact hc2z)
      · subst r
        -- `b` 由 `bad_fixed_color_extension` 给出的唯一色 `γb` 满足 PCF！
        by_cases hγlam : γb = lam
        · rw [hγlam] at hγb
          have hlamδ : lam ≠ δ := by
            intro h; rw [h] at hγb
            have hcnt2 : ([δ, δ] : List ℕ).count δ = 2 := by simp
            rw [hcnt2] at hγb; exact nat_add_two_ne_one hγb
          have hcnt : ([lam, δ] : List ℕ).count lam = 1 := by simp [hlamδ]
          have hzero : (Pb.filter (fun s => aP s = lam)).card = 0 := by
            rw [hcnt] at hγb; exact nat_add_one_eq_one hγb
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨u, hb_adj.symm, ?_⟩
          intro s hbs hψs
          rcases hb_all s hbs with hs | hs | hsPb
          · exact hs
          · rw [hs, hψ_out h0 hh_not_S, hψu] at hψs; exact False.elim (hlamδ hψs.symm)
          · rw [hψPb s hsPb, hψu] at hψs; exact False.elim (hzero hsPb hψs)
        · by_cases hγδ : γb = δ
          · have hlamδ : lam ≠ δ := fun h => hγlam (hγδ.trans h.symm)
            rw [hγδ] at hγb
            have hcnt : ([lam, δ] : List ℕ).count δ = 1 := by simp [hlamδ]
            have hzero : (Pb.filter (fun s => aP s = δ)).card = 0 := by
              rw [hcnt] at hγb; exact nat_add_one_eq_one hγb
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
            refine ⟨h0, hbh, ?_⟩
            intro s hbs hψs
            rcases hb_all s hbs with hs | hs | hsPb
            · rw [hs, hψu, hψ_out h0 hh_not_S] at hψs; exact False.elim (hlamδ hψs)
            · exact hs
            · rw [hψPb s hsPb, hψ_out h0 hh_not_S] at hψs; exact False.elim (hzero hsPb hψs)
          · have hcnt : ([lam, δ] : List ℕ).count γb = 0 := by
              rw [List.count_eq_zero]; simp [hγlam, hγδ]
            have hone : (Pb.filter (fun s => aP s = γb)).card = 1 := by
              rw [hcnt, add_zero] at hγb; exact hγb
            rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
            have hw₀_mem : w₀ ∈ Pb.filter (fun s => aP s = γb) := by rw [hw₀_eq]; simp
            rw [Finset.mem_filter] at hw₀_mem
            refine ⟨w₀, (mem_leafNbrs.mp hw₀_mem.1).1, ?_⟩
            intro s hbs hψs
            rcases hb_all s hbs with hs | hs | hsPb
            · rw [hs, hψu, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs; exact False.elim (hγlam hψs.symm)
            · rw [hs, hψ_out h0 hh_not_S, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
              exact False.elim (hγδ hψs.symm)
            · rw [hψPb s hsPb, hψPb w₀ hw₀_mem.1, hw₀_mem.2] at hψs
              have : s ∈ Pb.filter (fun t => aP t = γb) := Finset.mem_filter.mpr ⟨hsPb, hψs⟩
              rw [hw₀_eq, Finset.mem_singleton] at this; exact this
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrYu).2 (mem_leafNbrs.mp hrYu).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrPb).2 (mem_leafNbrs.mp hrPb).1.symm

/-- Corollary 3.11（`good_coreDeg_three_long_thread_summary`）：合并 Lemmas 3.9–3.10，
供 `12/5` 基线放电与 `22/9` 突破放电直接调用！ -/
lemma good_coreDeg_three_long_thread_summary {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (hc3 : coreDeg G u = 3) :
    ((threeThreadNbrs G u).Nonempty →
      oneThreadNbrs G u = ∅ ∧ ∀ b ∈ coreNbrs G u, ¬ IsBad G b) ∧
    ((twoThreadNbrs G u).Nonempty →
      (oneThreadNbrs G u).card ≤ 1 ∧ ∀ b ∈ coreNbrs G u, ¬ IsBad G b) := by
  classical
  constructor
  · rintro ⟨v, hv3⟩
    have hvlong : v ∈ longThreadNbrs G u := by
      rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_right _ hv3
    have hno1 : oneThreadNbrs G u = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have h2 := (thread_reduction hm hc3 hvlong ha).2
      exact Finset.disjoint_left.mp (twoThreadNbrs_disjoint_threeThreadNbrs G u) h2 hv3
    refine ⟨hno1, fun b hb hbad => ?_⟩
    exact no_one_thread_bad_neighbor hm hpq hc3 hvlong hno1 (mem_coreNbrs.mp hb).1 hbad
  · rintro ⟨v, hv2⟩
    have hvlong : v ∈ longThreadNbrs G u := by
      rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_left _ hv2
    by_cases h1 : (oneThreadNbrs G u).Nonempty
    · rcases h1 with ⟨a, ha⟩
      have hdu4 := (thread_reduction hm hc3 hvlong ha).1
      refine ⟨?_, fun b hb hbad =>
        no_bad_nbr_of_two_and_one_thread hm hpq hdu4 hc3 hv2 ha (mem_coreNbrs.mp hb).1 hbad⟩
      have hsub : oneThreadNbrs G u ⊆ {a} := by
        intro t ht; rw [Finset.mem_singleton]
        by_contra hne
        exact one_thread_unique_of_two_thread hm hdu4 hc3 hv2 ha ht (Ne.symm hne)
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      refine ⟨by rw [h1]; simp, fun b hb hbad =>
        no_one_thread_bad_neighbor hm hpq hc3 hvlong h1 (mem_coreNbrs.mp hb).1 hbad⟩

end LeanResearch.Proposal3
