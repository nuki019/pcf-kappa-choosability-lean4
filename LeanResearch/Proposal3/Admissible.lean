/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.Basic

/-!
# `C_5` 列表刻画、极小反例与通用容许染色延拓引擎

本模块建立以下无 `sorry` 基础设施：
1. 基础有限集选色工具（`exists_mem_sdiff_of_lt`、`exists_two_of_card_ge_two` 等）；
2. `exists_c5_cycle`、`c5_pcf_colorable_of_ne`（Lemma 2.3）与 `c5_admissible_coloring`；
3. `MinimalCounterexample` 极小反例定义及强归纳归约引理；
4. `exists_admissible_coloring` 及带单点避色偏好版本：对任意非空真子集 `S` 构造 `G - S`
   上的容许染色 `(φ, φs)`，将所有例外 `C_5` 分支统一封装。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 通用有限集选色辅助引理 -/

lemma card_sdiff_ge {α : Type*} [DecidableEq α] (A B : Finset α) :
    A.card - B.card ≤ (A \ B).card := by
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  omega

lemma exists_mem_sdiff_of_lt {α : Type*} {A B : Finset α}
    (h : B.card < A.card) : ∃ x ∈ A, x ∉ B := by
  classical
  have hpos : 0 < (A \ B).card := by
    have := card_sdiff_ge A B
    omega
  rcases Finset.card_pos.mp hpos with ⟨x, hx⟩
  rw [Finset.mem_sdiff] at hx
  exact ⟨x, hx.1, hx.2⟩

lemma card_triple_le {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  le_trans (Finset.card_insert_le a {b, c}) (Nat.add_le_add_right (Finset.card_le_two) 1)

lemma card_quad_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 :=
  le_trans (Finset.card_insert_le a {b, c, d}) (Nat.add_le_add_right (card_triple_le b c d) 1)

lemma exists_two_of_card_ge_two {α : Type*} {A : Finset α}
    (h : 2 ≤ A.card) : ∃ x ∈ A, ∃ y ∈ A, x ≠ y := by
  classical
  have h1 : 0 < A.card := by omega
  rcases Finset.card_pos.mp h1 with ⟨x, hx⟩
  have h2 : ({x} : Finset α).card < A.card := by simp; omega
  rcases exists_mem_sdiff_of_lt h2 with ⟨y, hy, hyx⟩
  rw [Finset.mem_singleton] at hyx
  exact ⟨x, hx, y, hy, Ne.symm hyx⟩

lemma exists_four_of_card_eq_four {α : Type*} {A : Finset α}
    (h : A.card = 4) (a : α) :
    ∃ b c d : α, b ∈ A ∧ c ∈ A ∧ d ∈ A ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  have h1 : ({a} : Finset α).card < A.card := by simp [h]
  rcases exists_mem_sdiff_of_lt h1 with ⟨b, hb, hba⟩
  have h2 : ({a, b} : Finset α).card < A.card := by
    have := Finset.card_le_two (a := a) (b := b); omega
  rcases exists_mem_sdiff_of_lt h2 with ⟨c, hc, hcab⟩
  have h3 : ({a, b, c} : Finset α).card < A.card := by
    have := card_triple_le a b c; omega
  rcases exists_mem_sdiff_of_lt h3 with ⟨d, hd, hdabc⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hba hcab hdabc
  exact ⟨b, c, d, hb, hc, hd, Ne.symm hba, Ne.symm hcab.1, Ne.symm hdabc.1,
    Ne.symm hcab.2, Ne.symm hdabc.2.1, Ne.symm hdabc.2.2⟩

/-- 2-度点的两个邻点恰是某对不同顶点 `u, w`。 -/
lemma neighborFinset_eq_pair_of_deg_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v u w : V}
    (hd : G.degree v = 2) (hu : G.Adj v u) (hw : G.Adj v w) (hne : u ≠ w) :
    G.neighborFinset v = {u, w} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset v x).mpr hu
    · exact (G.mem_neighborFinset v x).mpr hw
  · rw [Finset.card_pair hne, SimpleGraph.card_neighborFinset_eq_degree, hd]

/-- 2-度点必有两个不同邻点。 -/
lemma exists_two_neighbors_of_deg_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} (hd : G.degree v = 2) :
    ∃ u w : V, G.Adj v u ∧ G.Adj v w ∧ u ≠ w ∧ ∀ z, G.Adj v z → z = u ∨ z = w := by
  classical
  have hc : (G.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd]
  rcases Finset.card_eq_two.mp hc with ⟨u, w, hne, hpair⟩
  have hu : G.Adj v u := (G.mem_neighborFinset v u).mp (by rw [hpair]; simp)
  have hw : G.Adj v w := (G.mem_neighborFinset v w).mp (by rw [hpair]; simp)
  refine ⟨u, w, hu, hw, hne, ?_⟩
  intro z hz
  have hz' : z ∈ ({u, w} : Finset V) := by
    rw [← hpair]; exact (G.mem_neighborFinset v z).mpr hz
  simpa using hz'

/-- 若 2-度点 `v` 的两个邻点异色，则 `v` 满足 PCF 条件。 -/
lemma pcf_at_of_two_distinct_neighbors {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {φ : V → ℕ} {v u w : V}
    (hd : G.degree v = 2) (hu : G.Adj v u) (hw : G.Adj v w) (hne : u ≠ w)
    (hcol : φ u ≠ φ w) :
    ∃ x, G.Adj v x ∧ ∀ y, G.Adj v y → φ y = φ x → y = x := by
  classical
  have hpair := neighborFinset_eq_pair_of_deg_two hd hu hw hne
  refine ⟨u, hu, ?_⟩
  intro y hy hφ
  have hy' : y ∈ ({u, w} : Finset V) := by
    rw [← hpair]; exact (G.mem_neighborFinset v y).mpr hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
  rcases hy' with rfl | rfl
  · rfl
  · exact False.elim (hcol hφ.symm)

/-! ## 2. `C_5` 的循环排序、`4`-列表刻画（Lemma 2.3）与容许染色 -/

/-- 连通图上无外连边的非空子集必为全集。 -/
lemma eq_univ_of_closed {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hconn : G.Connected) {T : Finset V} {v₀ : V}
    (hv₀ : v₀ ∈ T) (hcl : ∀ u ∈ T, ∀ w, G.Adj u w → w ∈ T) : T = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  rcases hconn v₀ x with ⟨p⟩
  have hwalk : ∀ {a b : V} (q : G.Walk a b), a ∈ T → b ∈ T := by
    intro a b q ha
    induction q with
    | nil => exact ha
    | @cons u v w huv _ ih => exact ih (hcl u ha v huv)
  exact hwalk p hv₀

/-- 连通 2-正则 5 阶简单图从任意顶点 `v₀` 出发存在循环排序 `v₀-v₁-v₂-v₃-v₄-v₀`。 -/
lemma exists_c5_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hc5 : IsC5 G) (v₀ : V) :
    ∃ v₁ v₂ v₃ v₄ : V,
      ({v₀, v₁, v₂, v₃, v₄} : Finset V) = Finset.univ ∧
      v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₀ ≠ v₄ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧
      v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ ∧
      G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₄ ∧ G.Adj v₄ v₀ := by
  rcases hc5 with ⟨hcard5, hdeg2⟩
  rcases exists_two_neighbors_of_deg_two (hdeg2 v₀) with ⟨v₁, v₄, h01, h04, h14, hN0⟩
  have h0_ne_1 : v₀ ≠ v₁ := G.ne_of_adj h01
  have h0_ne_4 : v₀ ≠ v₄ := G.ne_of_adj h04
  rcases exists_two_neighbors_of_deg_two (hdeg2 v₁) with ⟨a, b, h1a, h1b, hab, _⟩
  have hv₂_ex : ∃ v₂, G.Adj v₁ v₂ ∧ v₂ ≠ v₀ := by
    by_cases ha : a = v₀
    · exact ⟨b, h1b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, h1a, ha⟩
  rcases hv₂_ex with ⟨v₂, h12, h20⟩
  have h1_ne_2 : v₁ ≠ v₂ := G.ne_of_adj h12
  have h2_ne_4 : v₂ ≠ v₄ := by
    intro heq
    have h14' : G.Adj v₁ v₄ := heq ▸ h12
    have hN0' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₀) h01 h04 h14
    have hN1' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₁) h01.symm h14' h0_ne_4
    have hN4' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₄) h04.symm h14'.symm h0_ne_1
    have hall : ({v₀, v₁, v₄} : Finset V) = Finset.univ := by
      apply eq_univ_of_closed hconn (v₀ := v₀) (by simp)
      intro u hu w huw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl
      · have : w ∈ ({v₁, v₄} : Finset V) := by
          rw [← hN0']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ ({v₀, v₄} : Finset V) := by
          rw [← hN1']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ ({v₀, v₁} : Finset V) := by
          rw [← hN4']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
    have hle := card_triple_le v₀ v₁ v₄
    rw [hall, Finset.card_univ, hcard5] at hle
    omega
  rcases exists_two_neighbors_of_deg_two (hdeg2 v₂) with ⟨c, d, h2c, h2d, hcd, _⟩
  have hv₃_ex : ∃ v₃, G.Adj v₂ v₃ ∧ v₃ ≠ v₁ := by
    by_cases hc : c = v₁
    · exact ⟨d, h2d, fun hd => hcd (hc.trans hd.symm)⟩
    · exact ⟨c, h2c, hc⟩
  rcases hv₃_ex with ⟨v₃, h23, h31⟩
  have h2_ne_3 : v₂ ≠ v₃ := G.ne_of_adj h23
  have h3_ne_0 : v₃ ≠ v₀ := by
    intro heq
    have h02 : G.Adj v₀ v₂ := (heq ▸ h23).symm
    rcases hN0 v₂ h02 with h | h
    · exact h1_ne_2 h.symm
    · exact h2_ne_4 h
  have h3_ne_4 : v₃ ≠ v₄ := by
    intro heq
    have h24' : G.Adj v₂ v₄ := heq ▸ h23
    have hN0' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₀) h01 h04 h14
    have hN1' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₁) h01.symm h12 h20.symm
    have hN2' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₂) h12.symm h24' h14
    have hN4' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₄) h04.symm h24'.symm h20.symm
    have hall : ({v₀, v₁, v₂, v₄} : Finset V) = Finset.univ := by
      apply eq_univ_of_closed hconn (v₀ := v₀) (by simp)
      intro u hu w huw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl | rfl
      · have : w ∈ ({v₁, v₄} : Finset V) := by
          rw [← hN0']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ ({v₀, v₂} : Finset V) := by
          rw [← hN1']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ ({v₁, v₄} : Finset V) := by
          rw [← hN2']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ ({v₀, v₂} : Finset V) := by
          rw [← hN4']; exact (G.mem_neighborFinset u w).mpr huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
    have hle := card_quad_le v₀ v₁ v₂ v₄
    rw [hall, Finset.card_univ, hcard5] at hle
    omega
  have hall5 : ({v₀, v₁, v₂, v₃, v₄} : Finset V) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard5]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h3_ne_4]
    · simp [h2_ne_3, h2_ne_4]
    · simp [h1_ne_2, h31.symm, h14]
    · simp [h0_ne_1, h20.symm, h3_ne_0.symm, h0_ne_4]
  have h34 : G.Adj v₃ v₄ := by
    rcases exists_two_neighbors_of_deg_two (hdeg2 v₄) with ⟨p, q, h4p, h4q, hpq, _⟩
    have hz_ex : ∃ z, G.Adj v₄ z ∧ z ≠ v₀ := by
      by_cases hp : p = v₀
      · exact ⟨q, h4q, fun hq => hpq (hp.trans hq.symm)⟩
      · exact ⟨p, h4p, hp⟩
    rcases hz_ex with ⟨z, h4z, hz0⟩
    have hzmem : z ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with hz | hz | hz | hz | hz
    · exact False.elim (hz0 hz)
    · have h14' : G.Adj v₁ v₄ := (hz ▸ h4z).symm
      have hN1' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₁) h01.symm h12 h20.symm
      have : v₄ ∈ ({v₀, v₂} : Finset V) := by
        rw [← hN1']; exact (G.mem_neighborFinset v₁ v₄).mpr h14'
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact False.elim (h0_ne_4 h.symm)
      · exact False.elim (h2_ne_4 h.symm)
    · have h24' : G.Adj v₂ v₄ := (hz ▸ h4z).symm
      have hN2' := neighborFinset_eq_pair_of_deg_two (hdeg2 v₂) h12.symm h23 h31.symm
      have : v₄ ∈ ({v₁, v₃} : Finset V) := by
        rw [← hN2']; exact (G.mem_neighborFinset v₂ v₄).mpr h24'
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact False.elim (h14 h.symm)
      · exact False.elim (h3_ne_4 h.symm)
    · exact (hz ▸ h4z).symm
    · exact False.elim (G.ne_of_adj h4z hz.symm)
  exact ⟨v₁, v₂, v₃, v₄, hall5, h0_ne_1, h20.symm, h3_ne_0.symm, h0_ne_4,
    h1_ne_2, h31.symm, h14, h2_ne_3, h2_ne_4, h3_ne_4, h01, h12, h23, h34, h04.symm⟩

/-- 单射染色（任意两点异色）对任意简单图必是 PCF 染色。 -/
lemma isPCFColoring_of_injective {V : Type*} {G : SimpleGraph V} {φ : V → ℕ}
    (hinj : Function.Injective φ) : IsPCFColoring G φ := by
  refine ⟨fun u v huv heq => G.ne_of_adj huv (hinj heq), ?_⟩
  intro v ⟨u, hu⟩
  exact ⟨u, hu, fun w _ hφ => hinj hφ⟩

/-- Lemma 2.3（`C_5` 的 `4`-列表可染充分条件）：
若 `G` 连通且 `IsC5 G`，`∀ v, 4 ≤ (L v).card`，
且并非所有 5 个顶点的列表都等于同一个 4 元集，则 `G` 存在 PCF `L`-染色。 -/
lemma c5_pcf_colorable_of_ne {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hc5 : IsC5 G) (L : V → Finset ℕ)
    (hL : ∀ v, 4 ≤ (L v).card)
    (hnot_eq4 : ¬ ∃ A : Finset ℕ, A.card = 4 ∧ ∀ v, L v = A) :
    ∃ φ : V → ℕ, IsPCFColoring G φ ∧ ∀ v, φ v ∈ L v := by
  classical
  have hstart : ∃ v₀ : V, 5 ≤ (L v₀).card ∨ ∃ v₄ : V, G.Adj v₀ v₄ ∧ ∃ c ∈ L v₀, c ∉ L v₄ := by
    by_cases h5 : ∃ v, 5 ≤ (L v).card
    · rcases h5 with ⟨v, hv⟩; exact ⟨v, Or.inl hv⟩
    · push Not at h5
      have hall4 : ∀ v, (L v).card = 4 := fun v => by have := hL v; have := h5 v; omega
      have hex_ne : ∃ u w : V, G.Adj u w ∧ L u ≠ L w := by
        by_contra hsame
        push Not at hsame
        rcases hconn.nonempty with ⟨r⟩
        apply hnot_eq4
        refine ⟨L r, hall4 r, ?_⟩
        intro x
        rcases hconn r x with ⟨p⟩
        induction p with
        | nil => rfl
        | @cons a b c hab _ ih => exact ih.trans (hsame a b hab).symm
      rcases hex_ne with ⟨u, w, huw, hne⟩
      have hnsub : ¬ L u ⊆ L w := by
        intro hsub
        exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hall4 u, hall4 w]))
      rw [Finset.not_subset] at hnsub
      rcases hnsub with ⟨c, hcu, hcw⟩
      exact ⟨u, Or.inr ⟨w, huw, c, hcu, hcw⟩⟩
  rcases hstart with ⟨v₀, hcase⟩
  rcases exists_c5_cycle hconn hc5 v₀ with
    ⟨v₁, v₂, v₃, v₄, hall5, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n,
      h01, h12, h23, h34, h40⟩
  have h5cols : ∃ c₀ c₁ c₂ c₃ c₄ : ℕ,
      c₀ ∈ L v₀ ∧ c₁ ∈ L v₁ ∧ c₂ ∈ L v₂ ∧ c₃ ∈ L v₃ ∧ c₄ ∈ L v₄ ∧
      c₀ ≠ c₁ ∧ c₀ ≠ c₂ ∧ c₀ ≠ c₃ ∧ c₀ ≠ c₄ ∧
      c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₁ ≠ c₄ ∧
      c₂ ≠ c₃ ∧ c₂ ≠ c₄ ∧ c₃ ≠ c₄ := by
    rcases hcase with hcard5 | ⟨w, hw0, c₀, hc₀v₀, hc₀w⟩
    · have hpos1 : 0 < (L v₁).card := by have := hL v₁; omega
      rcases Finset.card_pos.mp hpos1 with ⟨c₁, hc₁⟩
      rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {c₁}) (by simp; have := hL v₂; omega) with
        ⟨c₂, hc₂, hc₂n⟩
      rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {c₁, c₂})
        (by have := Finset.card_le_two (a := c₁) (b := c₂); have := hL v₃; omega) with
        ⟨c₃, hc₃, hc₃n⟩
      rcases exists_mem_sdiff_of_lt (A := L v₄) (B := {c₁, c₂, c₃})
        (by have := card_triple_le c₁ c₂ c₃; have := hL v₄; omega) with ⟨c₄, hc₄, hc₄n⟩
      rcases exists_mem_sdiff_of_lt (A := L v₀) (B := {c₁, c₂, c₃, c₄})
        (by have := card_quad_le c₁ c₂ c₃ c₄; omega) with ⟨c₀, hc₀, hc₀n⟩
      rw [Finset.mem_singleton] at hc₂n
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₃n hc₄n hc₀n
      exact ⟨c₀, c₁, c₂, c₃, c₄, hc₀, hc₁, hc₂, hc₃, hc₄,
        hc₀n.1, hc₀n.2.1, hc₀n.2.2.1, hc₀n.2.2.2,
        Ne.symm hc₂n, Ne.symm hc₃n.1, Ne.symm hc₄n.1,
        Ne.symm hc₃n.2, Ne.symm hc₄n.2.1, Ne.symm hc₄n.2.2⟩
    · have hN0' := neighborFinset_eq_pair_of_deg_two (hc5.2 v₀) h01 h40.symm h14n
      have hwmem : w ∈ ({v₁, v₄} : Finset V) := by
        rw [← hN0']; exact (G.mem_neighborFinset v₀ w).mpr hw0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
      rcases hwmem with hw1 | hw4
      · have hc₀1 : c₀ ∉ L v₁ := hw1 ▸ hc₀w
        rcases exists_mem_sdiff_of_lt (A := L v₄) (B := {c₀})
          (by simp; have := hL v₄; omega) with ⟨c₄, hc₄, hc₄n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {c₀, c₄})
          (by have := Finset.card_le_two (a := c₀) (b := c₄); have := hL v₃; omega) with
          ⟨c₃, hc₃, hc₃n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {c₀, c₃, c₄})
          (by have := card_triple_le c₀ c₃ c₄; have := hL v₂; omega) with ⟨c₂, hc₂, hc₂n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₁) (B := {c₂, c₃, c₄})
          (by have := card_triple_le c₂ c₃ c₄; have := hL v₁; omega) with ⟨c₁, hc₁, hc₁n⟩
        have hc₀₁ : c₀ ≠ c₁ := fun h => hc₀1 (h ▸ hc₁)
        rw [Finset.mem_singleton] at hc₄n
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₃n hc₂n hc₁n
        exact ⟨c₀, c₁, c₂, c₃, c₄, hc₀v₀, hc₁, hc₂, hc₃, hc₄,
          hc₀₁, Ne.symm hc₂n.1, Ne.symm hc₃n.1, Ne.symm hc₄n,
          hc₁n.1, hc₁n.2.1, hc₁n.2.2,
          hc₂n.2.1, hc₂n.2.2, hc₃n.2⟩
      · have hc₀4 : c₀ ∉ L v₄ := hw4 ▸ hc₀w
        rcases exists_mem_sdiff_of_lt (A := L v₁) (B := {c₀})
          (by simp; have := hL v₁; omega) with ⟨c₁, hc₁, hc₁n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {c₀, c₁})
          (by have := Finset.card_le_two (a := c₀) (b := c₁); have := hL v₂; omega) with
          ⟨c₂, hc₂, hc₂n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {c₀, c₁, c₂})
          (by have := card_triple_le c₀ c₁ c₂; have := hL v₃; omega) with ⟨c₃, hc₃, hc₃n⟩
        rcases exists_mem_sdiff_of_lt (A := L v₄) (B := {c₁, c₂, c₃})
          (by have := card_triple_le c₁ c₂ c₃; have := hL v₄; omega) with ⟨c₄, hc₄, hc₄n⟩
        have hc₀₄ : c₀ ≠ c₄ := fun h => hc₀4 (h ▸ hc₄)
        rw [Finset.mem_singleton] at hc₁n
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₂n hc₃n hc₄n
        exact ⟨c₀, c₁, c₂, c₃, c₄, hc₀v₀, hc₁, hc₂, hc₃, hc₄,
          Ne.symm hc₁n, Ne.symm hc₂n.1, Ne.symm hc₃n.1, hc₀₄,
          Ne.symm hc₂n.2, Ne.symm hc₃n.2.1, Ne.symm hc₄n.1,
          Ne.symm hc₃n.2.2, Ne.symm hc₄n.2.1, Ne.symm hc₄n.2.2⟩
  rcases h5cols with ⟨c₀, c₁, c₂, c₃, c₄, hc₀, hc₁, hc₂, hc₃, hc₄,
    h01c, h02c, h03c, h04c, h12c, h13c, h14c, h23c, h24c, h34c⟩
  let φ : V → ℕ := fun v =>
    if v = v₀ then c₀
    else if v = v₁ then c₁
    else if v = v₂ then c₂
    else if v = v₃ then c₃
    else c₄
  have hφ0 : φ v₀ = c₀ := by simp [φ]
  have hφ1 : φ v₁ = c₁ := by simp [φ, h01n.symm]
  have hφ2 : φ v₂ = c₂ := by simp [φ, h02n.symm, h12n.symm]
  have hφ3 : φ v₃ = c₃ := by simp [φ, h03n.symm, h13n.symm, h23n.symm]
  have hφ4 : φ v₄ = c₄ := by simp [φ, h04n.symm, h14n.symm, h24n.symm, h34n.symm]
  refine ⟨φ, isPCFColoring_of_injective ?_, ?_⟩
  · intro x y hxy
    have hx : x ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ x
    have hy : y ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (rw [hφ0, hφ1] at hxy; exact False.elim (h01c hxy))
    | (rw [hφ0, hφ2] at hxy; exact False.elim (h02c hxy))
    | (rw [hφ0, hφ3] at hxy; exact False.elim (h03c hxy))
    | (rw [hφ0, hφ4] at hxy; exact False.elim (h04c hxy))
    | (rw [hφ1, hφ0] at hxy; exact False.elim (h01c hxy.symm))
    | (rw [hφ1, hφ2] at hxy; exact False.elim (h12c hxy))
    | (rw [hφ1, hφ3] at hxy; exact False.elim (h13c hxy))
    | (rw [hφ1, hφ4] at hxy; exact False.elim (h14c hxy))
    | (rw [hφ2, hφ0] at hxy; exact False.elim (h02c hxy.symm))
    | (rw [hφ2, hφ1] at hxy; exact False.elim (h12c hxy.symm))
    | (rw [hφ2, hφ3] at hxy; exact False.elim (h23c hxy))
    | (rw [hφ2, hφ4] at hxy; exact False.elim (h24c hxy))
    | (rw [hφ3, hφ0] at hxy; exact False.elim (h03c hxy.symm))
    | (rw [hφ3, hφ1] at hxy; exact False.elim (h13c hxy.symm))
    | (rw [hφ3, hφ2] at hxy; exact False.elim (h23c hxy.symm))
    | (rw [hφ3, hφ4] at hxy; exact False.elim (h34c hxy))
    | (rw [hφ4, hφ0] at hxy; exact False.elim (h04c hxy.symm))
    | (rw [hφ4, hφ1] at hxy; exact False.elim (h14c hxy.symm))
    | (rw [hφ4, hφ2] at hxy; exact False.elim (h24c hxy.symm))
    | (rw [hφ4, hφ3] at hxy; exact False.elim (h34c hxy.symm))
  · intro v
    have hv : v ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [hφ0]; exact hc₀
    · rw [hφ1]; exact hc₁
    · rw [hφ2]; exact hc₂
    · rw [hφ3]; exact hc₃
    · rw [hφ4]; exact hc₄

/-- 例外 `C_5` 的容许染色：指定特殊顶点 `x` 与特殊颜色 `α ∈ A`（`|A| = 4`），
构造恰当 `A`-染色使 `x` 的两个邻点都染 `α`，且其余 4 点各自邻域中两色不同。 -/
lemma c5_admissible_coloring {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hc5 : IsC5 G) (A : Finset ℕ) (hA : A.card = 4)
    (x : V) (α : ℕ) (hα : α ∈ A) :
    ∃ φ : V → ℕ,
      (∀ v, φ v ∈ A) ∧
      (∀ u v, G.Adj u v → φ u ≠ φ v) ∧
      (∀ u, G.Adj x u → φ u = α) ∧
      (∀ v, v ≠ x → ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → φ w = φ u → w = u) := by
  classical
  rcases exists_c5_cycle hconn hc5 x with
    ⟨v₁, v₂, v₃, v₄, hall5, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n,
      h01, h12, h23, h34, h40⟩
  rcases exists_four_of_card_eq_four hA α with
    ⟨β, γ, δ, hβ, hγ, hδ, hαβ, hαγ, hαδ, hβγ, hβδ, hγδ⟩
  let φ : V → ℕ := fun v =>
    if v = x then β
    else if v = v₁ then α
    else if v = v₂ then γ
    else if v = v₃ then δ
    else α
  have hφx : φ x = β := by simp [φ]
  have hφ1 : φ v₁ = α := by simp [φ, h01n.symm]
  have hφ2 : φ v₂ = γ := by simp [φ, h02n.symm, h12n.symm]
  have hφ3 : φ v₃ = δ := by simp [φ, h03n.symm, h13n.symm, h23n.symm]
  have hφ4 : φ v₄ = α := by simp [φ, h04n.symm, h14n.symm, h24n.symm, h34n.symm]
  have hNx := neighborFinset_eq_pair_of_deg_two (hc5.2 x) h01 h40.symm h14n
  have hN1 := neighborFinset_eq_pair_of_deg_two (hc5.2 v₁) h01.symm h12 h02n
  have hN2 := neighborFinset_eq_pair_of_deg_two (hc5.2 v₂) h12.symm h23 h13n
  have hN3 := neighborFinset_eq_pair_of_deg_two (hc5.2 v₃) h23.symm h34 h24n
  have hN4 := neighborFinset_eq_pair_of_deg_two (hc5.2 v₄) h34.symm h40 h03n.symm
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro v
    have hv : v ∈ ({x, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [hφx]; exact hβ
    · rw [hφ1]; exact hα
    · rw [hφ2]; exact hγ
    · rw [hφ3]; exact hδ
    · rw [hφ4]; exact hα
  · intro u v huv
    have hu : u ∈ ({x, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ u
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · have : v ∈ ({v₁, v₄} : Finset V) := by
        rw [← hNx]; exact (G.mem_neighborFinset u v).mpr huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · rw [hφx, hφ1]; exact hαβ.symm
      · rw [hφx, hφ4]; exact hαβ.symm
    · have : v ∈ ({x, v₂} : Finset V) := by
        rw [← hN1]; exact (G.mem_neighborFinset u v).mpr huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · rw [hφ1, hφx]; exact hαβ
      · rw [hφ1, hφ2]; exact hαγ
    · have : v ∈ ({v₁, v₃} : Finset V) := by
        rw [← hN2]; exact (G.mem_neighborFinset u v).mpr huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · rw [hφ2, hφ1]; exact hαγ.symm
      · rw [hφ2, hφ3]; exact hγδ
    · have : v ∈ ({v₂, v₄} : Finset V) := by
        rw [← hN3]; exact (G.mem_neighborFinset u v).mpr huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · rw [hφ3, hφ2]; exact hγδ.symm
      · rw [hφ3, hφ4]; exact hαδ.symm
    · have : v ∈ ({v₃, x} : Finset V) := by
        rw [← hN4]; exact (G.mem_neighborFinset u v).mpr huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · rw [hφ4, hφ3]; exact hαδ
      · rw [hφ4, hφx]; exact hαβ
  · intro u hu
    have : u ∈ ({v₁, v₄} : Finset V) := by
      rw [← hNx]; exact (G.mem_neighborFinset x u).mpr hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact hφ1
    · exact hφ4
  · intro v hvx
    have hv : v ∈ ({x, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall5]; exact Finset.mem_univ v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hvx rfl)
    · exact pcf_at_of_two_distinct_neighbors (hc5.2 v) h01.symm h12 h02n
        (by rw [hφx, hφ2]; exact hβγ)
    · exact pcf_at_of_two_distinct_neighbors (hc5.2 v) h12.symm h23 h13n
        (by rw [hφ1, hφ3]; exact hαδ)
    · exact pcf_at_of_two_distinct_neighbors (hc5.2 v) h23.symm h34 h24n
        (by rw [hφ2, hφ4]; exact hαγ.symm)
    · exact pcf_at_of_two_distinct_neighbors (hc5.2 v) h34.symm h40 h03n.symm
        (by rw [hφ3, hφx]; exact hβδ.symm)

/-! ## 3. 极小反例定义与通用容许染色延拓引擎 -/

/-- `MadLt G p q` 下 PCF `κ_G`-可选择性的阶数极小反例（已将列表缩至精确大小 `kappa G v`）。 -/
structure MinimalCounterexample (p q : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset ℕ) : Prop where
  conn : G.Connected
  neC5 : ¬ IsC5 G
  mad : MadLt G p q
  list_card : ∀ v, (L v).card = kappa G v
  not_colorable : ¬ ∃ φ : V → ℕ, IsPCFColoring G φ ∧ ∀ v, φ v ∈ L v
  minimal : ∀ (T : Finset V), T.Nonempty → T ≠ Finset.univ →
    (G.induce (T : Set V)).Connected → ¬ IsC5 (G.induce (T : Set V)) →
    IsPCFChoosable (G.induce (T : Set V)) (kappa (G.induce (T : Set V)))

/-- 通过强归纳，证明「对所有图成立」等价于「不存在任何 `MinimalCounterexample p q`」。 -/
lemma isPCFChoosable_of_no_minimal_counterexample.{u} (p q : ℕ)
    (hno : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (L : W → Finset ℕ),
      ¬ MinimalCounterexample p q H L)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hneC5 : ¬ IsC5 G) (hmad : MadLt G p q) :
    IsPCFChoosable G (kappa G) := by
  suffices h : ∀ (n : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = n → H.Connected → ¬ IsC5 H → MadLt H p q →
      IsPCFChoosable H (kappa H) by
    exact h (Fintype.card V) G rfl hconn hneC5 hmad
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W _ _ H _ hcard hHconn hHneC5 hHmad L₀ hL₀
    have hshrink : ∀ v, ∃ A ⊆ L₀ v, A.card = kappa H v :=
      fun v => Finset.exists_subset_card_eq (hL₀ v)
    choose L hLsub hLcard using hshrink
    by_contra hnot₀
    have hnot : ¬ ∃ φ : W → ℕ, IsPCFColoring H φ ∧ ∀ v, φ v ∈ L v := by
      rintro ⟨φ, hpcf, hmem⟩
      exact hnot₀ ⟨φ, hpcf, fun v => hLsub v (hmem v)⟩
    apply hno H L
    refine ⟨hHconn, hHneC5, hHmad, hLcard, hnot, ?_⟩
    intro T _ hTne hTconn hTneC5
    have hTcard : Fintype.card {x : W // x ∈ (T : Set W)} < n := by
      simp only [Finset.mem_coe, Fintype.card_coe]
      rw [← hcard]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hTne)
    exact ih _ hTcard (H.induce (T : Set W)) rfl hTconn hTneC5 (hHmad.induce T)

/-- 连通分支的顶点 `Finset`。 -/
noncomputable def compFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) (C : (G.induce ((Sᶜ : Finset V) : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ h : v ∈ (Sᶜ : Finset V),
    (G.induce ((Sᶜ : Finset V) : Set V)).connectedComponentMk ⟨v, h⟩ = C)

lemma mem_compFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) (C : (G.induce ((Sᶜ : Finset V) : Set V)).ConnectedComponent) (v : V) :
    v ∈ compFinset S C ↔ ∃ h : v ∈ (Sᶜ : Finset V),
      (G.induce ((Sᶜ : Finset V) : Set V)).connectedComponentMk ⟨v, h⟩ = C := by
  classical
  simp [compFinset]

/-- 诱导子图中任意顶点度数不超过原图度数。 -/
lemma degree_induce_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : {x : V // x ∈ (T : Set V)}) :
    (G.induce (T : Set V)).degree v ≤ G.degree v.val := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hinj : ((G.induce (T : Set V)).neighborFinset v).image Subtype.val ⊆
      G.neighborFinset v.val := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  exact Finset.card_le_card hinj

/-- 在 `G - S` 上，连通分支 `C` 的顶点集诱导的子图必连通。 -/
lemma induced_comp_connected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) (C : (G.induce ((Sᶜ : Finset V) : Set V)).ConnectedComponent) :
    (G.induce (compFinset S C : Set V)).Connected := by
  let H := G.induce ((Sᶜ : Finset V) : Set V)
  have hne : (compFinset S C).Nonempty := by
    rcases C.exists_rep with ⟨u, rfl⟩
    exact ⟨u.val, (mem_compFinset S _ u.val).mpr ⟨u.property, rfl⟩⟩
  have : Nonempty {x : V // x ∈ (compFinset S C : Set V)} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine ⟨?_⟩
  intro ⟨a, ha⟩ ⟨b, hb⟩
  rcases (mem_compFinset S C a).mp ha with ⟨haS, haC⟩
  rcases (mem_compFinset S C b).mp hb with ⟨hbS, hbC⟩
  have hreach : H.Reachable ⟨a, haS⟩ ⟨b, hbS⟩ :=
    SimpleGraph.ConnectedComponent.exact (haC.trans hbC.symm)
  rcases hreach with ⟨p⟩
  have hlift : ∀ {x y : {v : V // v ∈ (Sᶜ : Finset V)}} (q : H.Walk x y)
      (hxC : H.connectedComponentMk x = C),
      (G.induce (compFinset S C : Set V)).Reachable
        ⟨x.val, (mem_compFinset S C x.val).mpr ⟨x.property, hxC⟩⟩
        ⟨y.val, (mem_compFinset S C y.val).mpr ⟨y.property,
          (SimpleGraph.ConnectedComponent.sound (Nonempty.intro q)).symm.trans hxC⟩⟩ := by
    intro x y q hxC
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w huv q' ih =>
      have hvC : H.connectedComponentMk v = C :=
        (SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable huv)).symm.trans hxC
      have hadj : (G.induce (compFinset S C : Set V)).Adj
          ⟨u.val, (mem_compFinset S C u.val).mpr ⟨u.property, hxC⟩⟩
          ⟨v.val, (mem_compFinset S C v.val).mpr ⟨v.property, hvC⟩⟩ := huv
      exact (SimpleGraph.Adj.reachable hadj).trans (ih hvC)
  exact hlift p haC

/-- 通用容许染色延拓记录：删除非空真子集 `S` 后，在 `G - S` 上给出的染色 `φ` 与避色见证 `φs`。 -/
structure AdmissibleColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset ℕ) (S : Finset V) where
  φ : V → ℕ
  φs : V → ℕ
  mem_list : ∀ v, v ∉ S → φ v ∈ L v
  proper : ∀ u v, u ∉ S → v ∉ S → G.Adj u v → φ u ≠ φ v
  pcf_preserve : ∀ (ψ : V → ℕ), (∀ x, x ∉ S → ψ x = φ x) →
    ∀ v, v ∉ S → (∃ w, w ∉ S ∧ G.Adj v w) →
    (∀ y, y ∈ S → G.Adj v y → ψ y ≠ φs v) →
    ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → ψ w = ψ u → w = u

/-- 从 `AdmissibleColoring` 一步导出整图 `G` 的 PCF `L`-染色，从而与极小反例矛盾。 -/
lemma AdmissibleColoring.contradiction {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {S : Finset V}
    (adm : AdmissibleColoring G L S) (ψ : V → ℕ)
    (hagree : ∀ x, x ∉ S → ψ x = adm.φ x)
    (hmemS : ∀ v, v ∈ S → ψ v ∈ L v)
    (hpropS : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → ψ u ≠ ψ v)
    (havoid : ∀ v, v ∉ S → (∃ w, w ∉ S ∧ G.Adj v w) → ∀ y, y ∈ S → G.Adj v y → ψ y ≠ adm.φs v)
    (hiso : ∀ v, v ∉ S → (∀ w, w ∉ S → ¬ G.Adj v w) → (∃ u, G.Adj v u) →
      ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → ψ w = ψ u → w = u)
    (hpcfS : ∀ v, v ∈ S → (∃ u, G.Adj v u) →
      ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → ψ w = ψ u → w = u) : False := by
  apply hm.not_colorable
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · intro u v huv
    by_cases h : u ∈ S ∨ v ∈ S
    · exact hpropS u v huv h
    · push Not at h
      rw [hagree u h.1, hagree v h.2]
      exact adm.proper u v h.1 h.2 huv
  · intro v hv
    by_cases hvS : v ∈ S
    · exact hpcfS v hvS hv
    · by_cases hnoniso : ∃ w, w ∉ S ∧ G.Adj v w
      · exact adm.pcf_preserve ψ hagree v hvS hnoniso (havoid v hvS hnoniso)
      · push Not at hnoniso
        exact hiso v hvS hnoniso hv
  · intro v
    by_cases hvS : v ∈ S
    · exact hmemS v hvS
    · rw [hagree v hvS]
      exact adm.mem_list v hvS

/-- 主构造定理：对极小反例 `G` 和任意非空子集 `S`，存在容许染色 `AdmissibleColoring G L S`。
同时支持避色函数 `avoid : V → Finset ℕ`（`∀ v, (avoid v).card ≤ 3`）：
对每个在 `G - S` 中至少有 2 个邻点的顶点 `v ∉ S`，要么其在 `G - S` 中已有两异色邻点（延拓时无需避色），
要么 `v` 是某例外 `C_5` 分支的唯一边界点且满足 `φs v ∉ avoid v`。 -/
theorem exists_admissible_coloring_avoid {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {S : Finset V}
    (hSne : S.Nonempty) (avoid : V → Finset ℕ) (havoid_card : ∀ v, (avoid v).card ≤ 3) :
    ∃ adm : AdmissibleColoring G L S,
      ∀ v, v ∉ S → (∃ w₁ w₂, w₁ ∉ S ∧ w₂ ∉ S ∧ w₁ ≠ w₂ ∧ G.Adj v w₁ ∧ G.Adj v w₂) →
        (∃ w₁ w₂, w₁ ∉ S ∧ w₂ ∉ S ∧ G.Adj v w₁ ∧ G.Adj v w₂ ∧ adm.φ w₁ ≠ adm.φ w₂) ∨
        adm.φs v ∉ avoid v := by
  classical
  let H := G.induce ((Sᶜ : Finset V) : Set V)
  have hcomp : ∀ C : H.ConnectedComponent,
      ∃ (φC φsC : V → ℕ),
        (∀ v ∈ compFinset S C, φC v ∈ L v) ∧
        (∀ u ∈ compFinset S C, ∀ v ∈ compFinset S C, G.Adj u v → φC u ≠ φC v) ∧
        (∀ v ∈ compFinset S C, (∃ w ∈ compFinset S C, G.Adj v w) →
          ∀ (ψ : V → ℕ), (∀ x ∈ compFinset S C, ψ x = φC x) →
          (∀ y, y ∈ S → G.Adj v y → ψ y ≠ φsC v) →
          ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → ψ w = ψ u → w = u) ∧
        (∀ v ∈ compFinset S C,
          (∃ w₁ ∈ compFinset S C, ∃ w₂ ∈ compFinset S C, w₁ ≠ w₂ ∧ G.Adj v w₁ ∧ G.Adj v w₂) →
          (∃ w₁ ∈ compFinset S C, ∃ w₂ ∈ compFinset S C,
            G.Adj v w₁ ∧ G.Adj v w₂ ∧ φC w₁ ≠ φC w₂) ∨
          φsC v ∉ avoid v) := by
    intro C
    let T := compFinset S C
    let F := G.induce (T : Set V)
    have hTconn : F.Connected := induced_comp_connected S C
    have hTne : T.Nonempty := by
      rcases C.exists_rep with ⟨u, rfl⟩
      exact ⟨u.val, (mem_compFinset S _ u.val).mpr ⟨u.property, rfl⟩⟩
    have hTsub : T ⊆ Sᶜ := fun v hv => ((mem_compFinset S C v).mp hv).1
    have hTne_univ : T ≠ Finset.univ := by
      intro heq
      rcases hSne with ⟨s, hs⟩
      exact (Finset.mem_compl.mp (hTsub (heq ▸ Finset.mem_univ s))) hs
    have hTclosed : ∀ v ∈ T, ∀ w, w ∉ S → G.Adj v w → w ∈ T := by
      intro v hv w hwS hvw
      rcases (mem_compFinset S C v).mp hv with ⟨hvS, hvC⟩
      have hwS' : w ∈ Sᶜ := Finset.mem_compl.mpr hwS
      have hreach : H.Reachable ⟨v, hvS⟩ ⟨w, hwS'⟩ :=
        SimpleGraph.Adj.reachable (show H.Adj ⟨v, hvS⟩ ⟨w, hwS'⟩ from hvw)
      exact (mem_compFinset S C w).mpr
        ⟨hwS', (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hvC⟩
    have hLF : ∀ v : {x : V // x ∈ (T : Set V)}, kappa F v ≤ (L v.val).card := by
      intro v
      rw [hm.list_card v.val]
      exact kappa_mono (degree_induce_le G T v)
    by_cases hex_pcf : ∃ φF : {x : V // x ∈ (T : Set V)} → ℕ,
        IsPCFColoring F φF ∧ ∀ v, φF v ∈ L v.val
    · rcases hex_pcf with ⟨φF, ⟨hpropF, hpcfF⟩, hmemF⟩
      let φC : V → ℕ := fun v => if hv : v ∈ T then φF ⟨v, hv⟩ else 0
      have hφC_eq : ∀ (v : V) (hv : v ∈ T), φC v = φF ⟨v, hv⟩ := fun v hv => by simp [φC, hv]
      have huniq : ∀ v : V, ∃ c : ℕ, ∀ (hv : v ∈ T),
          (∃ w ∈ T, G.Adj v w) →
          ∃ u, ∃ hu : u ∈ T, G.Adj v u ∧ φF ⟨u, hu⟩ = c ∧
            ∀ w, ∀ hw : w ∈ T, G.Adj v w → φF ⟨w, hw⟩ = c → w = u := by
        intro v
        by_cases hcond : ∃ (hv : v ∈ T), ∃ w ∈ T, G.Adj v w
        · rcases hcond with ⟨hv, w, hw, hvw⟩
          rcases hpcfF ⟨v, hv⟩ ⟨⟨w, hw⟩, hvw⟩ with ⟨⟨u, hu⟩, hvu, hu_uniq⟩
          refine ⟨φF ⟨u, hu⟩, fun _ _ => ⟨u, hu, hvu, rfl, ?_⟩⟩
          intro z hz hvz hφz
          exact congrArg Subtype.val (hu_uniq ⟨z, hz⟩ hvz hφz)
        · refine ⟨0, fun hv hw => False.elim (hcond ⟨hv, hw⟩)⟩
      choose φsC hφsC using huniq
      refine ⟨φC, φsC, ?_, ?_, ?_, ?_⟩
      · intro v hv; rw [hφC_eq v hv]; exact hmemF ⟨v, hv⟩
      · intro u hu v hv huv; rw [hφC_eq u hu, hφC_eq v hv]; exact hpropF ⟨u, hu⟩ ⟨v, hv⟩ huv
      · intro v hv hnoniso ψ hagree havoid
        rcases hφsC v hv hnoniso with ⟨u, hu, hvu, hφu, hu_uniq⟩
        refine ⟨u, hvu, ?_⟩
        intro w hvw hψw
        have hψu : ψ u = φsC v := by rw [hagree u hu, hφC_eq u hu, hφu]
        by_cases hwS : w ∈ S
        · exact False.elim (havoid w hwS hvw (hψw.trans hψu))
        · have hwT : w ∈ T := hTclosed v hv w hwS hvw
          have hφw : φF ⟨w, hwT⟩ = φsC v := by
            rw [← hφC_eq w hwT, ← hagree w hwT, hψw, hψu]
          exact hu_uniq w hwT hvw hφw
      · intro v hv ⟨w₁, hw₁, w₂, hw₂, hne12, hvw₁, hvw₂⟩
        left
        rcases hφsC v hv ⟨w₁, hw₁, hvw₁⟩ with ⟨u, hu, hvu, hφu, hu_uniq⟩
        by_cases h1 : w₁ = u
        · refine ⟨u, hu, w₂, hw₂, hvu, hvw₂, ?_⟩
          rw [hφC_eq u hu, hφC_eq w₂ hw₂, hφu]
          intro hEq
          exact hne12 (h1.trans (hu_uniq w₂ hw₂ hvw₂ hEq.symm).symm)
        · refine ⟨u, hu, w₁, hw₁, hvu, hvw₁, ?_⟩
          rw [hφC_eq u hu, hφC_eq w₁ hw₁, hφu]
          intro hEq
          exact h1 (hu_uniq w₁ hw₁ hvw₁ hEq.symm)
    · have hFC5 : IsC5 F := by
        by_contra hneC5
        exact hex_pcf (hm.minimal T hTne hTne_univ hTconn hneC5 (fun v => L v.val) hLF)
      have hL4F : ∀ v : {x : V // x ∈ (T : Set V)}, 4 ≤ (L v.val).card := by
        intro v
        have h1 := hLF v
        have h2 : kappa F v = 4 := by simp [kappa, hFC5.2 v]
        omega
      have hall_eq4 :
          ∃ A : Finset ℕ, A.card = 4 ∧ ∀ v : {x : V // x ∈ (T : Set V)}, L v.val = A := by
        by_contra hnot
        exact hex_pcf (c5_pcf_colorable_of_ne hTconn hFC5 (fun v => L v.val) hL4F hnot)
      rcases hall_eq4 with ⟨A, hA4, hLA⟩
      have hbdry : ∃ x : {v : V // v ∈ (T : Set V)}, ∃ s ∈ S, G.Adj x.val s := by
        rcases hTne with ⟨t₀, ht₀⟩
        rcases hSne with ⟨s₀, hs₀⟩
        rcases hm.conn t₀ s₀ with ⟨p⟩
        have hfind : ∀ {a b : V} (q : G.Walk a b), a ∈ T → b ∉ T →
            ∃ x ∈ T, ∃ s ∉ T, G.Adj x s := by
          intro a b q ha hb
          induction q with
          | nil => exact False.elim (hb ha)
          | @cons u v w huv q' ih =>
            by_cases hvT : v ∈ T
            · exact ih hvT hb
            · exact ⟨u, ha, v, hvT, huv⟩
        have hs₀_notT : s₀ ∉ T := fun h => (Finset.mem_compl.mp (hTsub h)) hs₀
        rcases hfind p ht₀ hs₀_notT with ⟨x, hxT, s, hsT, hxs⟩
        have hsS : s ∈ S := by
          by_contra hsnotS
          exact hsT (hTclosed x hxT s hsnotS hxs)
        exact ⟨⟨x, hxT⟩, s, hsS, hxs⟩
      rcases hbdry with ⟨xF, s₀, hs₀S, hxFs₀⟩
      have hxF_deg3 : G.degree xF.val = 3 := by
        have hL4 : (L xF.val).card = 4 := by rw [hLA xF, hA4]
        have hkap : kappa G xF.val = 4 := by rw [← hm.list_card xF.val, hL4]
        have hge3 : 3 ≤ G.degree xF.val := by
          have h2 : F.degree xF = 2 := hFC5.2 xF
          have hsub : (F.neighborFinset xF).image Subtype.val ⊂ G.neighborFinset xF.val := by
            rw [Finset.ssubset_iff_of_subset]
            · refine ⟨s₀, (G.mem_neighborFinset xF.val s₀).mpr hxFs₀, ?_⟩
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨y, _, hy⟩
              exact (Finset.mem_compl.mp (hTsub (hy ▸ y.property))) hs₀S
            · intro w hw
              rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
              exact (G.mem_neighborFinset xF.val u.val).mpr ((F.mem_neighborFinset xF u).mp hu)
          have hlt := Finset.card_lt_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
              SimpleGraph.card_neighborFinset_eq_degree,
              SimpleGraph.card_neighborFinset_eq_degree, h2] at hlt
          omega
        simp only [kappa] at hkap
        split_ifs at hkap with h2 <;> omega
      have hxF_uniqS : ∀ y ∈ S, G.Adj xF.val y → y = s₀ := by
        intro y hyS hxFy
        by_contra hyne
        have hsub : ((F.neighborFinset xF).image Subtype.val) ∪ {s₀, y} ⊆
            G.neighborFinset xF.val := by
          intro w hw
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert,
            Finset.mem_singleton] at hw
          rcases hw with ⟨u, hu, rfl⟩ | rfl | rfl
          · exact (G.mem_neighborFinset xF.val u.val).mpr ((F.mem_neighborFinset xF u).mp hu)
          · exact (G.mem_neighborFinset xF.val w).mpr hxFs₀
          · exact (G.mem_neighborFinset xF.val w).mpr hxFy
        have hdisj : Disjoint ((F.neighborFinset xF).image Subtype.val) {s₀, y} := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          rcases Finset.mem_image.mp hw1 with ⟨u, _, rfl⟩
          have huS : u.val ∉ S := Finset.mem_compl.mp (hTsub u.property)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw2
          rcases hw2 with rfl | rfl
          · exact huS hs₀S
          · exact huS hyS
        have hle := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ Subtype.val_injective,
            Finset.card_pair (Ne.symm hyne),
            SimpleGraph.card_neighborFinset_eq_degree,
            SimpleGraph.card_neighborFinset_eq_degree, hFC5.2 xF, hxF_deg3] at hle
        omega
      rcases exists_mem_sdiff_of_lt (A := A) (B := avoid xF.val)
        (by have := havoid_card xF.val; omega) with ⟨α, hαA, hαavoid⟩
      rcases c5_admissible_coloring hTconn hFC5 A hA4 xF α hαA with
        ⟨φF, hmemF, hpropF, hnbxF, hpcfOther⟩
      let φC : V → ℕ := fun v => if hv : v ∈ T then φF ⟨v, hv⟩ else 0
      have hφC_eq : ∀ (v : V) (hv : v ∈ T), φC v = φF ⟨v, hv⟩ := fun v hv => by simp [φC, hv]
      have huniq : ∀ v : V, ∃ c : ℕ,
          (v = xF.val → c = α) ∧
          (∀ (hv : v ∈ T), v ≠ xF.val →
            ∃ u, ∃ hu : u ∈ T, G.Adj v u ∧ φF ⟨u, hu⟩ = c ∧
              ∀ w, ∀ hw : w ∈ T, G.Adj v w → φF ⟨w, hw⟩ = c → w = u) := by
        intro v
        by_cases hvx : v = xF.val
        · exact ⟨α, fun _ => rfl, fun _ hne => False.elim (hne hvx)⟩
        · by_cases hv : v ∈ T
          · have hne_sub : (⟨v, hv⟩ : {x : V // x ∈ (T : Set V)}) ≠ xF :=
              fun h => hvx (congrArg Subtype.val h)
            rcases hpcfOther ⟨v, hv⟩ hne_sub with ⟨⟨u, hu⟩, hvu, hu_uniq⟩
            refine ⟨φF ⟨u, hu⟩, fun h => False.elim (hvx h), fun _ _ => ⟨u, hu, hvu, rfl, ?_⟩⟩
            intro z hz hvz hφz
            exact congrArg Subtype.val (hu_uniq ⟨z, hz⟩ hvz hφz)
          · exact ⟨0, fun h => False.elim (hvx h), fun hv' _ => False.elim (hv hv')⟩
      choose φsC hφsC_x hφsC_other using huniq
      refine ⟨φC, φsC, ?_, ?_, ?_, ?_⟩
      · intro v hv; rw [hφC_eq v hv, hLA ⟨v, hv⟩]; exact hmemF ⟨v, hv⟩
      · intro u hu v hv huv; rw [hφC_eq u hu, hφC_eq v hv]; exact hpropF ⟨u, hu⟩ ⟨v, hv⟩ huv
      · intro v hv _ ψ hagree havoid
        by_cases hvx : v = xF.val
        · subst hvx
          have hαeq : φsC xF.val = α := hφsC_x xF.val rfl
          refine ⟨s₀, hxFs₀, ?_⟩
          intro w hxFw hψw
          by_cases hwS : w ∈ S
          · exact hxF_uniqS w hwS hxFw
          · have hwT : w ∈ T := hTclosed xF.val hv w hwS hxFw
            have hψw_eq : ψ w = α := by
              rw [hagree w hwT, hφC_eq w hwT]
              exact hnbxF ⟨w, hwT⟩ hxFw
            exact False.elim (havoid s₀ hs₀S hxFs₀ (by rw [hαeq, ← hψw_eq, hψw]))
        · rcases hφsC_other v hv hvx with ⟨u, hu, hvu, hφu, hu_uniq⟩
          refine ⟨u, hvu, ?_⟩
          intro w hvw hψw
          have hψu : ψ u = φsC v := by rw [hagree u hu, hφC_eq u hu, hφu]
          by_cases hwS : w ∈ S
          · exact False.elim (havoid w hwS hvw (hψw.trans hψu))
          · have hwT : w ∈ T := hTclosed v hv w hwS hvw
            have hφw : φF ⟨w, hwT⟩ = φsC v := by
              rw [← hφC_eq w hwT, ← hagree w hwT, hψw, hψu]
            exact hu_uniq w hwT hvw hφw
      · intro v hv ⟨w₁, hw₁, w₂, hw₂, hne12, hvw₁, hvw₂⟩
        by_cases hvx : v = xF.val
        · right; rw [hvx, hφsC_x xF.val rfl]; exact hαavoid
        · left
          rcases hφsC_other v hv hvx with ⟨u, hu, hvu, hφu, hu_uniq⟩
          by_cases h1 : w₁ = u
          · refine ⟨u, hu, w₂, hw₂, hvu, hvw₂, ?_⟩
            rw [hφC_eq u hu, hφC_eq w₂ hw₂, hφu]
            intro hEq
            exact hne12 (h1.trans (hu_uniq w₂ hw₂ hvw₂ hEq.symm).symm)
          · refine ⟨u, hu, w₁, hw₁, hvu, hvw₁, ?_⟩
            rw [hφC_eq u hu, hφC_eq w₁ hw₁, hφu]
            intro hEq
            exact h1 (hu_uniq w₁ hw₁ hvw₁ hEq.symm)
  choose φC φsC hCmem hCprop hCpcf hCtwo using hcomp
  let compOf : ∀ v, v ∉ S → H.ConnectedComponent :=
    fun v hv => H.connectedComponentMk ⟨v, Finset.mem_compl.mpr hv⟩
  let φ : V → ℕ := fun v => if hv : v ∉ S then φC (compOf v hv) v else 0
  let φs : V → ℕ := fun v => if hv : v ∉ S then φsC (compOf v hv) v else 0
  have hφ_eq : ∀ (v : V) (hv : v ∉ S), φ v = φC (compOf v hv) v := fun v hv => by simp [φ, hv]
  have hφs_eq : ∀ (v : V) (hv : v ∉ S), φs v = φsC (compOf v hv) v := fun v hv => by simp [φs, hv]
  refine ⟨⟨φ, φs, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [hφ_eq v hv]
    exact hCmem (compOf v hv) v ((mem_compFinset S _ v).mpr ⟨Finset.mem_compl.mpr hv, rfl⟩)
  · intro u v hu hv huv
    rw [hφ_eq u hu, hφ_eq v hv]
    have hsame : compOf u hu = compOf v hv :=
      SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Adj.reachable (show H.Adj ⟨u, Finset.mem_compl.mpr hu⟩
          ⟨v, Finset.mem_compl.mpr hv⟩ from huv))
    rw [hsame]
    exact hCprop (compOf v hv) u
      ((mem_compFinset S _ u).mpr ⟨Finset.mem_compl.mpr hu, hsame⟩)
      v ((mem_compFinset S _ v).mpr ⟨Finset.mem_compl.mpr hv, rfl⟩) huv
  · intro ψ hagree v hv ⟨w, hw, hvw⟩ havoid
    let C := compOf v hv
    have hvT : v ∈ compFinset S C := (mem_compFinset S C v).mpr ⟨Finset.mem_compl.mpr hv, rfl⟩
    have hsame : compOf w hw = C :=
      (SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Adj.reachable (show H.Adj ⟨v, Finset.mem_compl.mpr hv⟩
          ⟨w, Finset.mem_compl.mpr hw⟩ from hvw))).symm
    have hwT : w ∈ compFinset S C := (mem_compFinset S C w).mpr ⟨Finset.mem_compl.mpr hw, hsame⟩
    apply hCpcf C v hvT ⟨w, hwT, hvw⟩ ψ
    · intro x hx
      rcases (mem_compFinset S C x).mp hx with ⟨hxS, hxC⟩
      have hxnotS : x ∉ S := Finset.mem_compl.mp hxS
      rw [hagree x hxnotS, hφ_eq x hxnotS]
      have : compOf x hxnotS = C := hxC
      rw [this]
    · intro y hy hvy
      have := havoid y hy hvy
      rwa [hφs_eq v hv] at this
  · intro v hv ⟨w₁, w₂, hw₁, hw₂, hne12, hvw₁, hvw₂⟩
    let C := compOf v hv
    have hvT : v ∈ compFinset S C := (mem_compFinset S C v).mpr ⟨Finset.mem_compl.mpr hv, rfl⟩
    have hsame₁ : compOf w₁ hw₁ = C :=
      (SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Adj.reachable (show H.Adj ⟨v, Finset.mem_compl.mpr hv⟩
          ⟨w₁, Finset.mem_compl.mpr hw₁⟩ from hvw₁))).symm
    have hsame₂ : compOf w₂ hw₂ = C :=
      (SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Adj.reachable (show H.Adj ⟨v, Finset.mem_compl.mpr hv⟩
          ⟨w₂, Finset.mem_compl.mpr hw₂⟩ from hvw₂))).symm
    have hw₁T : w₁ ∈ compFinset S C :=
      (mem_compFinset S C w₁).mpr ⟨Finset.mem_compl.mpr hw₁, hsame₁⟩
    have hw₂T : w₂ ∈ compFinset S C :=
      (mem_compFinset S C w₂).mpr ⟨Finset.mem_compl.mpr hw₂, hsame₂⟩
    rcases hCtwo C v hvT ⟨w₁, hw₁T, w₂, hw₂T, hne12, hvw₁, hvw₂⟩ with
      ⟨u₁, hu₁, u₂, hu₂, hvu₁, hvu₂, hcol⟩ | hav
    · left
      rcases (mem_compFinset S C u₁).mp hu₁ with ⟨hu₁S, hu₁C⟩
      rcases (mem_compFinset S C u₂).mp hu₂ with ⟨hu₂S, hu₂C⟩
      have hu₁not : u₁ ∉ S := Finset.mem_compl.mp hu₁S
      have hu₂not : u₂ ∉ S := Finset.mem_compl.mp hu₂S
      refine ⟨u₁, u₂, hu₁not, hu₂not, hvu₁, hvu₂, ?_⟩
      dsimp only
      rw [hφ_eq u₁ hu₁not, hφ_eq u₂ hu₂not]
      have h1 : compOf u₁ hu₁not = C := hu₁C
      have h2 : compOf u₂ hu₂not = C := hu₂C
      rw [h1, h2]
      exact hcol
    · right
      dsimp only
      rw [hφs_eq v hv]
      exact hav

/-- 常用无参数版本：对极小反例 `G` 和任意非空子集 `S`，存在容许染色 `AdmissibleColoring G L S`。 -/
theorem exists_admissible_coloring {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {S : Finset V} (hSne : S.Nonempty) :
    Nonempty (AdmissibleColoring G L S) := by
  rcases exists_admissible_coloring_avoid hm hSne (fun _ => ∅) (fun _ => by simp) with ⟨adm, _⟩
  exact ⟨adm⟩

end LeanResearch.Proposal3
