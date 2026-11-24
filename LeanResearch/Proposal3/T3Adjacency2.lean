/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.T3Adjacency

/-!
# 引理 E（续）：`T3` 与 `T21` / `S3_2(a=2)` / `T20` 的邻接限制（`T3Adjacency2`）

本模块补全 `22/9` 放电所需的其余 3 条 `T3` 邻接限制：
1. `no_T3_adj_T21`：`T3` 顶点不与 `T21` 顶点相邻；
2. `no_T3_adj_S3_2_a2`：`T3` 顶点不与 `coreDeg = 3, |oneThreadNbrs| = 2` 顶点相邻；
3. `no_T3_T20_T3`：`T20` 顶点不能同时与两个不同的 `T3` 顶点相邻。
-/

@[expose] public section

namespace LeanResearch.Proposal3

private lemma unique_neighbor_of_deg_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v a b : V}
    (hd : G.degree v = 1) (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  rcases exists_unique_neighbor_of_deg_one hd with ⟨_, _, huniq⟩
  exact (huniq a ha).trans (huniq b hb).symm

private lemma ne_of_deg2_ge4 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (ha : G.degree a = 2) (hb : 4 ≤ G.degree b) : a ≠ b := by
  intro heq; rw [heq] at ha; omega

private lemma ne_of_deg1_ge4 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (ha : G.degree a = 1) (hb : 4 ≤ G.degree b) : a ≠ b := by
  intro heq; rw [heq] at ha; omega

private lemma ne_of_deg1_eq2 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (ha : G.degree a = 1) (hb : G.degree b = 2) : a ≠ b := by
  intro heq; rw [heq] at ha; omega

private lemma ne_of_deg2_ge3 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (ha : G.degree a = 2) (hb : 3 ≤ G.degree b) : a ≠ b := by
  intro heq; rw [heq] at ha; omega

private lemma not_mem_leafNbrs_of_deg_eq2 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V}
    (hx : G.degree x = 2) : x ∉ leafNbrs G u := by
  intro h; have := (mem_leafNbrs.mp h).2; omega

private lemma not_mem_leafNbrs_of_deg_ge3 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V}
    (hx : 3 ≤ G.degree x) : x ∉ leafNbrs G u := by
  intro h; have := (mem_leafNbrs.mp h).2; omega

private lemma not_mem_leafNbrs_of_deg_ge4 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V}
    (hx : 4 ≤ G.degree x) : x ∉ leafNbrs G u := by
  intro h; have := (mem_leafNbrs.mp h).2; omega

private lemma card_sdiff_one_pos {A : Finset ℕ} {a : ℕ} (h : A.card = 4) : (A \ {a}).Nonempty := by
  rw [← Finset.card_pos]; have := card_sdiff_ge A {a}
  simp only [Finset.card_singleton] at this; omega

private lemma card_sdiff_one_ge_three {A : Finset ℕ} {a : ℕ} (h : A.card = 4) :
    3 ≤ (A \ {a}).card := by
  have := card_sdiff_ge A {a}; simp only [Finset.card_singleton] at this; omega

private lemma card_sdiff_pair_ge_two {A : Finset ℕ} {a b : ℕ} (h : A.card = 4) :
    2 ≤ (A \ {a, b}).card := by
  have := card_sdiff_ge A {a, b}; have := Finset.card_le_two (a := a) (b := b); omega

private lemma card_sdiff_triple_pos {A : Finset ℕ} {a b c : ℕ} (h : A.card = 4) :
    (A \ {a, b, c}).Nonempty := by
  rw [← Finset.card_pos]; have := card_sdiff_ge A {a, b, c}
  have := card_triple_le a b c; omega

private lemma card_sdiff_triple_ge_add_one {A : Finset ℕ} {k a b c : ℕ} (h : A.card = k + 4) :
    k + 1 ≤ (A \ {a, b, c}).card := by
  have := card_sdiff_ge A {a, b, c}; have := card_triple_le a b c; omega

private lemma card_sdiff_pair_ge_add_two {A : Finset ℕ} {k a b : ℕ} (h : A.card = k + 4) :
    k + 2 ≤ (A \ {a, b}).card := by
  have := card_sdiff_ge A {a, b}; have := Finset.card_le_two (a := a) (b := b); omega

private lemma card_sdiff_one_ge_add_two {A : Finset ℕ} {k a : ℕ} (h : A.card = k + 4) :
    k + 2 ≤ (A \ {a}).card := by
  have := card_sdiff_ge A {a}; simp only [Finset.card_singleton] at this; omega

private lemma card_ge_add_two_of_eq_add_four {A : Finset ℕ} {k : ℕ} (h : A.card = k + 4) :
    k + 2 ≤ A.card := by omega

private lemma unpack_threeThreadGoodCols {L₁ L₂ Z₃ : Finset ℕ} {φz α c₁ : ℕ}
    (h : c₁ ∈ threeThreadGoodCols L₁ L₂ Z₃ φz α) :
    c₁ ∈ L₁ ∧ c₁ ≠ α ∧ ∃ c₂ ∈ L₂, c₂ ≠ α ∧ c₂ ≠ c₁ ∧ c₂ ≠ φz ∧
      ∃ c₃ ∈ Z₃, c₃ ≠ c₂ ∧ c₃ ≠ c₁ := by
  rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at h
  rcases h with ⟨⟨h1, h2⟩, c₃, h3, h31, c₂, h2B, h21⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h2B
  exact ⟨h1, h2, c₂, h2B.1, h2B.2.1, h21, h2B.2.2.2, c₃, h3, Ne.symm h2B.2.2.1, h31⟩

/-! ## 1. 引理 E2：`no_T3_adj_T21`（`T3` 与 `T21` 不相邻） -/

/-- 引理 E2：在 `9 * p ≤ 22 * q` 下，`T3` 顶点不能与 `T21` 顶点相邻！ -/
lemma no_T3_adj_T21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u₁ u₂ : V}
    (hu1 : IsT3 G u₁) (hu2 : IsT21 G u₂) (hadj : G.Adj u₁ u₂) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hu12 : u₁ ≠ u₂ := G.ne_of_adj hadj
  -- 拆解 `u₁` (`IsT3`)
  rcases isT3_unpack hm hpq25 hu1 with
    ⟨v₁, v₂, v₃, z₁, x₁, y₁', huv₁, hdv₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, hdz1,
      hz1u1, hx₁, hy₁', hxy₁, hcore1, hY1_pos, hY1_card, hall_u1', hall_v1, hall_v2, hall_v3⟩
  have hst1 := isT3_structure hm hpq25 hu1
  have hdu1 : 4 ≤ G.degree u₁ := hst1.1
  -- 拆解 `u₂` (`IsT21`)
  have hst2 := isT21_structure hm hpq25 hu2
  have hdu2 : G.degree u₂ = 4 := hst2.1
  rcases Finset.card_eq_one.mp hst2.2.1 with ⟨y₂, hleaf2_eq⟩
  have hy2_mem : y₂ ∈ leafNbrs G u₂ := by rw [hleaf2_eq]; simp
  have hu2y2 : G.Adj u₂ y₂ := (mem_leafNbrs.mp hy2_mem).1
  have hdy2 : G.degree y₂ = 1 := (mem_leafNbrs.mp hy2_mem).2
  rcases hu2.2.1 with ⟨w₁, hw1_mem⟩
  rcases twoThreadNbr_other_endpoint hm (by omega) hw1_mem with
    ⟨w₂, z₂, hu2w1, hdw1, hw12, hw2u2, hdw2, hw2z2, hz2w1, hu2z2, hdz2_3, _, haw1, haw2⟩
  have hdz2 : 4 ≤ G.degree z₂ := by
    have hw2long : w₂ ∈ longThreadNbrs G z₂ := by
      unfold longThreadNbrs degTwoNbrs
      rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hw2z2.symm, hdw2⟩, hw2z2.symm, hdw2, w₁, hw12.symm, hz2w1.symm, hdw1⟩
    exact deg_ge_four_of_longThreadNbr hm hdz2_3 hw2long
  rcases hu2.2.2 with ⟨a₂, ha2_mem⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) ha2_mem with
    ⟨p₂, ha2p2, hp2u2, hdp2, _, haa2⟩
  have hu2a2 : G.Adj u₂ a₂ := (mem_oneThreadNbrs.mp ha2_mem).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2_mem).2.1
  -- 确定 `u₁` 的另一好邻点 `y₁`
  have hu2_core1 : u₂ ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨hadj, by omega⟩
  rw [hcore1] at hu2_core1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu2_core1
  have hex_y1 : ∃ y₁ : V, y₁ ∈ goodNbrs G u₁ ∧ y₁ ≠ u₂ ∧
      ∀ r, G.Adj u₁ r → r = v₁ ∨ r = u₂ ∨ r = y₁ ∨ r ∈ leafNbrs G u₁ := by
    rcases hu2_core1 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu2; omega)
    · exact ⟨y₁', hy₁', hxy₁.symm, hall_u1'⟩
    · exact ⟨x₁, hx₁, hxy₁, fun r hr => by
        rcases hall_u1' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y1 with ⟨y₁, hy1_good, hy1u2, hall_u1⟩
  have hu1y1 : G.Adj u₁ y₁ := (mem_goodNbrs.mp hy1_good).1
  have hdy1 : 3 ≤ G.degree y₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy1_good).2
  -- 2-度点的邻点全枚举
  rcases exists_other_neighbor_of_deg_two hdw1 hu2w1.symm with ⟨tw1, _, _, hall_w1'⟩
  have hall_w1 : ∀ r, G.Adj w₁ r → r = u₂ ∨ r = w₂ := fun r hr => by
    rcases hall_w1' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_w1' w₂ hw12).resolve_left hw2u2).symm)
  rcases exists_other_neighbor_of_deg_two hdw2 hw12.symm with ⟨tw2, _, _, hall_w2'⟩
  have hall_w2 : ∀ r, G.Adj w₂ r → r = w₁ ∨ r = z₂ := fun r hr => by
    rcases hall_w2' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_w2' z₂ hw2z2).resolve_left hz2w1).symm)
  rcases exists_other_neighbor_of_deg_two hda2 hu2a2.symm with ⟨ta2, _, _, hall_a2'⟩
  have hall_a2 : ∀ r, G.Adj a₂ r → r = u₂ ∨ r = p₂ := fun r hr => by
    rcases hall_a2' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_a2' p₂ ha2p2).resolve_left hp2u2).symm)
  -- `u₂` 的 4 个邻点恰为 `u₁, w₁, a₂, y₂`
  have ha2_ne_w1 : a₂ ≠ w₁ := fun h => by
    have had : G.Adj a₂ w₂ := h ▸ hw12
    rcases hall_a2 w₂ had with hw | hw
    · exact hw2u2 hw
    · rw [hw] at hdw2; omega
  have ha2_ne_w2 : a₂ ≠ w₂ := fun h => by
    have had : G.Adj a₂ w₁ := h ▸ hw12.symm
    rcases hall_a2 w₁ had with hw | hw
    · exact (G.ne_of_adj hu2w1).symm hw
    · rw [hw] at hdw1; omega
  have hall_u2 : ∀ r, G.Adj u₂ r → r = u₁ ∨ r = w₁ ∨ r = a₂ ∨ r = y₂ := by
    have hsub : ({u₁, w₁, a₂, y₂} : Finset V) ⊆ G.neighborFinset u₂ := by
      intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rw [SimpleGraph.mem_neighborFinset]
      rcases hr with rfl | rfl | rfl | rfl
      · exact hadj.symm
      · exact hu2w1
      · exact hu2a2
      · exact hu2y2
    have h4 : ({u₁, w₁, a₂, y₂} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by subst h; omega, fun h => by subst h; omega,
              fun h => by subst h; omega⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨ha2_ne_w1.symm, fun h => by subst h; omega⟩),
          Finset.card_pair (fun h => by subst h; omega)]
    have heq : G.neighborFinset u₂ = {u₁, w₁, a₂, y₂} :=
      (Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hdu2, h4])).symm
    intro r hr
    have hrm : r ∈ ({u₁, w₁, a₂, y₂} : Finset V) := by
      rw [← heq, SimpleGraph.mem_neighborFinset]; exact hr
    simpa [Finset.mem_insert, Finset.mem_singleton] using hrm
  -- 零重合性：`z₁ ≠ u₂`、`z₂ ≠ u₁`、`p₂ ≠ u₁`
  have hz1u2 : z₁ ≠ u₂ := by
    intro h; subst z₁
    have hv3m : v₃ ∈ threeThreadNbrs G u₂ := by
      rw [mem_threeThreadNbrs]
      exact ⟨hv3z1.symm, hdv₃, v₂, v₁, u₁, hv23.symm, hzv2.symm, hdv₂, hv12.symm, hv31.symm,
        hdv₁, huv₁.symm, hv2u1.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨v₃, hv3m⟩; omega
  have hz2u1 : z₂ ≠ u₁ := by
    intro h; subst z₂
    have hw2m : w₂ ∈ twoThreadNbrs G u₁ := by
      rw [mem_twoThreadNbrs]
      exact ⟨hw2z2.symm, hdw2, w₁, u₂, hw12.symm, hz2w1.symm, hdw1, hu2w1.symm,
        hw2u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨w₂, hw2m⟩; omega
  have hp2u1 : p₂ ≠ u₁ := by
    intro h; subst p₂
    have ha2m : a₂ ∈ oneThreadNbrs G u₁ := by
      rw [mem_oneThreadNbrs]
      exact ⟨ha2p2.symm, hda2, u₂, hu2a2.symm, hp2u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨a₂, ha2m⟩; omega
  -- 线串两两不交
  have ha_v := threeThread_anchors_eq hm (by omega) (by omega) hz1u1.symm
    hdv₁ hdv₂ hdv₃ huv₁ hv12 hv2u1 hv23 hv31 hv3z1 hzv2
  have hv_ne_w : ∀ a ∈ ({v₁, v₂, v₃} : Finset V), ∀ b ∈ ({w₁, w₂, a₂} : Finset V), a ≠ b := by
    intro a ha b hb heq; subst heq
    have ha_anc : threadAnchors G a = {u₁, z₁} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact ha_v.1
      · exact ha_v.2.1
      · exact ha_v.2.2
    have hu1_in : u₁ ∈ threadAnchors G a := by rw [ha_anc]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · rw [haw1] at hu1_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_in
      exact hu1_in.elim hu12 hz2u1.symm
    · rw [haw2] at hu1_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_in
      exact hu1_in.elim hu12 hz2u1.symm
    · rw [haa2] at hu1_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_in
      exact hu1_in.elim hu12 hp2u1.symm
  -- 构造删除集 `S`
  let Y₁ := leafNbrs G u₁
  let S : Finset V :=
    insert u₁ (insert u₂ (insert v₁ (insert v₂ (insert v₃
      (insert w₁ (insert w₂ (insert a₂ (insert y₂ Y₁))))))))
  have hu1S : u₁ ∈ S := Finset.mem_insert_self u₁ _
  have hY1_subS : Y₁ ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))))
  have hy2_not_Y1 : y₂ ∉ Y₁ := fun h => by
    have h1 := (mem_leafNbrs.mp h).1
    exact hu12 (unique_neighbor_of_deg_one hdy2 h1.symm hu2y2.symm)
  have hy1_not_S : y₁ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨(G.ne_of_adj hu1y1).symm, hy1u2, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz1_not_S : z₁ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hz1u1, hz1u2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz2_not_S : z₂ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hz2u1, hu2z2.symm, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hp2_not_S : p₂ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hp2u1, hp2u2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  -- 刻画跨过 `S` 边界的 4 条边
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = u₁ ∧ s = y₁) ∨ (r = v₃ ∧ s = z₁) ∨ (r = w₂ ∧ s = z₂) ∨ (r = a₂ ∧ s = p₂) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1
    · rcases hall_u1 s hsr.symm with rfl | rfl | rfl | hsY1
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hsS (hY1_subS hsY1))
    · rcases hall_u2 s hsr.symm with rfl | rfl | rfl | rfl <;>
        exact False.elim (hsS (by simp [S]))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w2 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rcases hall_a2 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · have := unique_neighbor_of_deg_one hdy2 hsr.symm hu2y2.symm
      exact False.elim (hsS (by rw [this]; simp [S]))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hsr.symm
        (mem_leafNbrs.mp hrY1).1.symm
      exact False.elim (hsS (by rw [this]; exact hu1S))
  -- 证明 `S` 外无孤立邻点（唯一孤立 4-度点 `s` 导出 `|K| = 9, ∑ coreDeg = 22`，矛盾 `9p ≤ 22q`！）
  have hno_iso : ∀ s ∉ S, (∃ r ∈ S, G.Adj s r) → ∃ t ∉ S, G.Adj s t := by
    intro s hsS ⟨r₀, hr0S, hsr0⟩
    by_contra hiso; push Not at hiso
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ hr0S hsr0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hsub : G.neighborFinset s ⊆ {u₁, v₃, w₂, a₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hiso r h hr
      rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hds4 : 4 ≤ G.degree s := by
      by_cases h1 : G.Adj s v₃
      · rcases hS_out s hsS v₃ (by simp [S]) h1 with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact False.elim (by rw [h] at hdv₃; omega)
        · exact hdz1
        · exact False.elim (hv_ne_w v₃ (by simp) w₂ (by simp) h)
        · exact False.elim (hv_ne_w v₃ (by simp) a₂ (by simp) h)
      · by_cases h2 : G.Adj s w₂
        · rcases hS_out s hsS w₂ (by simp [S]) h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
          · exact False.elim (by rw [h] at hdw2; omega)
          · exact False.elim (hv_ne_w v₃ (by simp) w₂ (by simp) h.symm)
          · exact hdz2
          · exact False.elim (ha2_ne_w2 h.symm)
        · have hsub2 : G.neighborFinset s ⊆ {u₁, a₂} := by
            intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
            have hrS : r ∈ S := by by_contra h; exact hiso r h hr
            rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
            · simp
            · exact False.elim (h1 hr)
            · exact False.elim (h2 hr)
            · simp
          have hc := Finset.card_le_card hsub2
          rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := Finset.card_le_two (a := u₁) (b := a₂); omega
    have h4_le : ({u₁, v₃, w₂, a₂} : Finset V).card ≤ 4 := card_quad_le u₁ v₃ w₂ a₂
    have hcard_eq : G.neighborFinset s = {u₁, v₃, w₂, a₂} :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
    have hds_eq4 : G.degree s = 4 := by
      have hc := congrArg Finset.card hcard_eq
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc; omega
    have hs_y1 : s = y₁ := by
      have had : G.Adj s u₁ := (G.mem_neighborFinset s u₁).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS u₁ hu1S had with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (by rw [h] at hdu1; omega)
      · exact False.elim (by rw [h] at hdu1; omega)
      · exact False.elim (by rw [h] at hdu1; omega)
    have hs_z1 : s = z₁ := by
      have had : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS v₃ (by simp [S]) had with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (by rw [h] at hdv₃; omega)
      · exact h
      · exact False.elim (hv_ne_w v₃ (by simp) w₂ (by simp) h)
      · exact False.elim (hv_ne_w v₃ (by simp) a₂ (by simp) h)
    have hs_z2 : s = z₂ := by
      have had : G.Adj s w₂ := (G.mem_neighborFinset s w₂).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS w₂ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim (by rw [h] at hdw2; omega)
      · exact False.elim (hv_ne_w v₃ (by simp) w₂ (by simp) h.symm)
      · exact h
      · exact False.elim (ha2_ne_w2 h.symm)
    have hs_p2 : s = p₂ := by
      have had : G.Adj s a₂ := (G.mem_neighborFinset s a₂).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS a₂ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (by rw [h] at hda2; omega)
      · exact False.elim (hv_ne_w v₃ (by simp) a₂ (by simp) h.symm)
      · exact False.elim (ha2_ne_w2 h)
      · exact h
    have hall_univ : insert s S = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := s) (Finset.mem_insert_self s S)
      intro a ha b hab
      simp only [Finset.mem_insert] at ha ⊢
      rcases ha with rfl | haS
      · exact Or.inr (by by_contra hbS; exact hiso b hbS hab)
      · by_cases hbS : b ∈ S
        · exact Or.inr hbS
        · rcases hS_out b hbS a haS hab.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact Or.inl hs_y1.symm
          · exact Or.inl hs_z1.symm
          · exact Or.inl hs_z2.symm
          · exact Or.inl hs_p2.symm
    have hK_eq : coreVerts G = {s, u₁, u₂, v₁, v₂, v₃, w₁, w₂, a₂} := by
      ext r; simp only [mem_coreVerts, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hr2
        have hrU : r ∈ insert s S := by rw [hall_univ]; exact Finset.mem_univ r
        simp only [S, Finset.mem_insert] at hrU
        rcases hrU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hY1
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · exact False.elim (by omega)
        · exact False.elim (by rw [mem_leafNbrs] at hY1; omega)
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
    have hsu1 : s ≠ u₁ := fun h => hsS (h ▸ hu1S)
    have hsu2 : s ≠ u₂ := fun h => hsS (by rw [h]; simp [S])
    have hK9 : (coreVerts G).card = 9 := by
      rw [hK_eq]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsu1, hsu2, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hu12, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv12, hv31.symm, hv_ne_w v₁ (by simp) w₁ (by simp),
          hv_ne_w v₁ (by simp) w₂ (by simp), hv_ne_w v₁ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv23, hv_ne_w v₂ (by simp) w₁ (by simp),
          hv_ne_w v₂ (by simp) w₂ (by simp), hv_ne_w v₂ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_ne_w v₃ (by simp) w₁ (by simp), hv_ne_w v₃ (by simp) w₂ (by simp),
          hv_ne_w v₃ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hw12, ha2_ne_w1.symm⟩)]
      rw [Finset.card_pair ha2_ne_w2.symm]
    have hcs4 : coreDeg G s = 4 := by
      have hEq : coreNbrs G s = G.neighborFinset s := by
        ext r; simp only [mem_coreNbrs, SimpleGraph.mem_neighborFinset]
        exact ⟨And.left, fun hr => ⟨hr, by
          have : r ∈ ({u₁, v₃, w₂, a₂} : Finset V) := by
            rw [← hcard_eq, SimpleGraph.mem_neighborFinset]; exact hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl | rfl | rfl <;> omega⟩⟩
      rw [coreDeg, hEq, SimpleGraph.card_neighborFinset_eq_degree, hds_eq4]
    have hKsum : ∑ r ∈ coreVerts G, coreDeg G r = 22 := by
      rw [hK_eq]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsu1, hsu2, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hu12, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv12, hv31.symm, hv_ne_w v₁ (by simp) w₁ (by simp),
          hv_ne_w v₁ (by simp) w₂ (by simp), hv_ne_w v₁ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv23, hv_ne_w v₂ (by simp) w₁ (by simp),
          hv_ne_w v₂ (by simp) w₂ (by simp), hv_ne_w v₂ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_ne_w v₃ (by simp) w₁ (by simp), hv_ne_w v₃ (by simp) w₂ (by simp),
          hv_ne_w v₃ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hw12, ha2_ne_w1.symm⟩)]
      rw [Finset.sum_pair ha2_ne_w2.symm]
      have hc_v1 : coreDeg G v₁ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₁]
      have hc_v2 : coreDeg G v₂ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₂]
      have hc_v3 : coreDeg G v₃ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₃]
      have hc_w1 : coreDeg G w₁ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw1]
      have hc_w2 : coreDeg G w₂ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw2]
      have hc_a2 : coreDeg G a₂ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hda2]
      rw [hcs4, hu1.1, hu2.1, hc_v1, hc_v2, hc_v3, hc_w1, hc_w2, hc_a2]
      rfl
    exact mad_22_9_contra hm hpq hK9 hKsum (by omega)
  -- 主染色阶段：容许染色 + `t21_fixed_color_extension` + `t3_fun_color_extension`
  rcases exists_admissible_coloring hm ⟨u₁, hu1S⟩ with ⟨adm⟩
  have hLu1 : (L u₁).card = Y₁.card + 4 := by
    dsimp only [Y₁]; rw [hm.list_card u₁]; unfold kappa; split_ifs <;> omega
  have hLu2 : (L u₂).card = 5 := by rw [hm.list_card u₂]; simp [kappa, hdu2]
  have hLy2 : (L y₂).card = 2 := by rw [hm.list_card y₂]; simp [kappa, hdy2]
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw1]
  have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw2]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  have hY1_L2 : ∀ r ∈ Y₁, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  let Aa : Finset ℕ := L a₂ \ {adm.φ p₂, adm.φs p₂}
  have hAa : 2 ≤ Aa.card := by
    dsimp only [Aa]; have := card_sdiff_ge (L a₂) {adm.φ p₂, adm.φs p₂}
    have := Finset.card_le_two (a := adm.φ p₂) (b := adm.φs p₂); omega
  have hcw2_ex : ∀ α : ℕ, (L w₂ \ {adm.φ z₂, adm.φs z₂, α}).Nonempty := fun α => by
    rw [← Finset.card_pos]
    have := card_sdiff_ge (L w₂) {adm.φ z₂, adm.φs z₂, α}
    have := card_triple_le (adm.φ z₂) (adm.φs z₂) α; omega
  let cFun : ℕ → ℕ := fun α => (hcw2_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L w₂ ∧ cFun α ≠ adm.φ z₂ ∧ cFun α ≠ adm.φs z₂ ∧ cFun α ≠ α := by
    intro α
    have h := (hcw2_ex α).choose_spec
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have hu2_ext : ∀ α₁ : ℕ, ∃ α₂ ∈ L u₂ \ {α₁, adm.φ p₂},
      ∃ cy ∈ L y₂ \ {α₂}, ∃ ca ∈ Aa \ {α₂}, ∃ cw₁ ∈ L w₁ \ {α₂, cFun α₂, adm.φ z₂},
      ∃ γ₂ : ℕ, ([cy, ca, cw₁, α₁] : List ℕ).count γ₂ = 1 := by
    intro α₁
    have hC2 : 3 ≤ (L u₂ \ {α₁, adm.φ p₂}).card := by
      have := card_sdiff_ge (L u₂) {α₁, adm.φ p₂}
      have := Finset.card_le_two (a := α₁) (b := adm.φ p₂); omega
    exact t21_fixed_color_extension cFun hLy2 hAa hLw1 hC2
  let f₂ : ℕ → ℕ := fun α₁ => (hu2_ext α₁).choose
  let Z₁ : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
  have hZ1 : 2 ≤ Z₁.card := by
    dsimp only [Z₁]; have := card_sdiff_ge (L v₃) {adm.φ z₁, adm.φs z₁}
    have := Finset.card_le_two (a := adm.φ z₁) (b := adm.φs z₁); omega
  let C₁ : Finset ℕ := L u₁ \ {adm.φ y₁, adm.φs y₁}
  have hC1 : Y₁.card + 1 ≤ C₁.card := by
    dsimp only [C₁]; have := card_sdiff_ge (L u₁) {adm.φ y₁, adm.φs y₁}
    have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φs y₁); omega
  rcases t3_fun_color_extension (L := L) (Y := Y₁) (L₁ := L v₁) (L₂ := L v₂) (Z₃ := Z₁)
    (C_u := C₁) (φy := adm.φ y₁) (φz := adm.φ z₁) f₂ hY1_pos hY1_L2 hLv1 hLv2 hZ1 hC1 with
    ⟨α₁, hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
  let α₂ : ℕ := f₂ α₁
  have hα2_spec := (hu2_ext α₁).choose_spec
  change α₂ ∈ L u₂ \ {α₁, adm.φ p₂} ∧
      ∃ cy ∈ L y₂ \ {α₂}, ∃ ca ∈ Aa \ {α₂}, ∃ cw₁ ∈ L w₁ \ {α₂, cFun α₂, adm.φ z₂},
      ∃ γ₂ : ℕ, ([cy, ca, cw₁, α₁] : List ℕ).count γ₂ = 1 at hα2_spec
  rcases hα2_spec with ⟨hα2C, cy, hcy, ca, hca, cw₁, hcw1, γ₂, hγ₂⟩
  let cw₂ : ℕ := cFun α₂
  have hcw2 := hcFun_spec α₂
  rcases unpack_threeThreadGoodCols hc₁ with
    ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2z1, c₃, hc3Z, hc3c2, hc3c1⟩
  simp only [C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1C
  simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C hcy hcw1
  simp only [Aa, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca
  let ψ : V → ℕ := fun r =>
    if r = u₁ then α₁
    else if r = u₂ then α₂
    else if r = v₁ then c₁
    else if r = v₂ then c₂
    else if r = v₃ then c₃
    else if r = w₁ then cw₁
    else if r = w₂ then cw₂
    else if r = a₂ then ca
    else if r = y₂ then cy
    else if r ∈ Y₁ then aY₁ r
    else adm.φ r
  have hψ_u1 : ψ u₁ = α₁ := by simp [ψ]
  have hψ_u2 : ψ u₂ = α₂ := by simp [ψ, hu12.symm]
  have hψ_v1 : ψ v₁ = c₁ := by
    simp [ψ, (show v₁ ≠ u₁ by intro h; subst h; omega), (show v₁ ≠ u₂ by intro h; subst h; omega)]
  have hψ_v2 : ψ v₂ = c₂ := by
    simp [ψ, (show v₂ ≠ u₁ by intro h; subst h; omega), (show v₂ ≠ u₂ by intro h; subst h; omega),
      (G.ne_of_adj hv12).symm]
  have hψ_v3 : ψ v₃ = c₃ := by
    simp [ψ, (show v₃ ≠ u₁ by intro h; subst h; omega), (show v₃ ≠ u₂ by intro h; subst h; omega),
      hv31, (G.ne_of_adj hv23).symm]
  have hψ_w1 : ψ w₁ = cw₁ := by
    simp [ψ, (show w₁ ≠ u₁ by intro h; subst h; omega), (show w₁ ≠ u₂ by intro h; subst h; omega),
      (hv_ne_w v₁ (by simp) w₁ (by simp)).symm, (hv_ne_w v₂ (by simp) w₁ (by simp)).symm,
      (hv_ne_w v₃ (by simp) w₁ (by simp)).symm]
  have hψ_w2 : ψ w₂ = cw₂ := by
    simp [ψ, (show w₂ ≠ u₁ by intro h; subst h; omega), (show w₂ ≠ u₂ by intro h; subst h; omega),
      (hv_ne_w v₁ (by simp) w₂ (by simp)).symm, (hv_ne_w v₂ (by simp) w₂ (by simp)).symm,
      (hv_ne_w v₃ (by simp) w₂ (by simp)).symm, (G.ne_of_adj hw12).symm]
  have hψ_a2 : ψ a₂ = ca := by
    simp [ψ, (show a₂ ≠ u₁ by intro h; subst h; omega), (show a₂ ≠ u₂ by intro h; subst h; omega),
      (hv_ne_w v₁ (by simp) a₂ (by simp)).symm, (hv_ne_w v₂ (by simp) a₂ (by simp)).symm,
      (hv_ne_w v₃ (by simp) a₂ (by simp)).symm, ha2_ne_w1, ha2_ne_w2]
  have hψ_y2 : ψ y₂ = cy := by
    simp [ψ, (show y₂ ≠ u₁ by intro h; subst h; omega), (show y₂ ≠ u₂ by intro h; subst h; omega),
      (show y₂ ≠ v₁ by intro h; subst h; omega), (show y₂ ≠ v₂ by intro h; subst h; omega),
      (show y₂ ≠ v₃ by intro h; subst h; omega), (show y₂ ≠ w₁ by intro h; subst h; omega),
      (show y₂ ≠ w₂ by intro h; subst h; omega), (show y₂ ≠ a₂ by intro h; subst h; omega)]
  have hψ_Y1 : ∀ r ∈ Y₁, ψ r = aY₁ r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    have hne : r ≠ y₂ := fun h => hy2_not_Y1 (h ▸ hr)
    simp [ψ, hr, hne, (show r ≠ u₁ by intro h; subst h; omega),
      (show r ≠ u₂ by intro h; subst h; omega), (show r ≠ v₁ by intro h; subst h; omega),
      (show r ≠ v₂ by intro h; subst h; omega), (show r ≠ v₃ by intro h; subst h; omega),
      (show r ≠ w₁ by intro h; subst h; omega), (show r ≠ w₂ by intro h; subst h; omega),
      (show r ≠ a₂ by intro h; subst h; omega)]
  have hagree : ∀ x, x ∉ S → ψ x = adm.φ x := fun x hx => by
    simp only [S, Finset.mem_insert, not_or] at hx
    rcases hx with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    simp [ψ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  have hprop_S : ∀ r ∈ S, ∀ t, G.Adj r t → ψ r ≠ ψ t := by
    intro r hrS t hrt
    simp only [S, Finset.mem_insert] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1
    · rcases hall_u1 t hrt with ht | ht | ht | htY1
      · rw [ht, hψ_u1, hψ_v1]; exact Ne.symm hc1α1
      · rw [ht, hψ_u1, hψ_u2]; exact Ne.symm hα2C.2.1
      · rw [ht, hψ_u1, hagree y₁ hy1_not_S]; exact hα1C.2.1
      · rw [hψ_u1, hψ_Y1 t htY1]; exact Ne.symm (haY₁ t htY1).2
    · rcases hall_u2 t hrt with ht | ht | ht | ht
      · rw [ht, hψ_u2, hψ_u1]; exact hα2C.2.1
      · rw [ht, hψ_u2, hψ_w1]; exact Ne.symm hcw1.2.1
      · rw [ht, hψ_u2, hψ_a2]; exact Ne.symm hca.2
      · rw [ht, hψ_u2, hψ_y2]; exact Ne.symm hcy.2
    · rcases hall_v1 t hrt with ht | ht
      · rw [ht, hψ_v1, hψ_u1]; exact hc1α1
      · rw [ht, hψ_v1, hψ_v2]; exact Ne.symm hc2c1
    · rcases hall_v2 t hrt with ht | ht
      · rw [ht, hψ_v2, hψ_v1]; exact hc2c1
      · rw [ht, hψ_v2, hψ_v3]; exact Ne.symm hc3c2
    · rcases hall_v3 t hrt with ht | ht
      · rw [ht, hψ_v3, hψ_v2]; exact hc3c2
      · rw [ht, hψ_v3, hagree z₁ hz1_not_S]; exact hc3Z.2.1
    · rcases hall_w1 t hrt with ht | ht
      · rw [ht, hψ_w1, hψ_u2]; exact hcw1.2.1
      · rw [ht, hψ_w1, hψ_w2]; exact hcw1.2.2.1
    · rcases hall_w2 t hrt with ht | ht
      · rw [ht, hψ_w2, hψ_w1]; exact Ne.symm hcw1.2.2.1
      · rw [ht, hψ_w2, hagree z₂ hz2_not_S]; exact hcw2.2.1
    · rcases hall_a2 t hrt with ht | ht
      · rw [ht, hψ_a2, hψ_u2]; exact hca.2
      · rw [ht, hψ_a2, hagree p₂ hp2_not_S]; exact hca.1.2.1
    · have ht := unique_neighbor_of_deg_one hdy2 hrt hu2y2.symm
      rw [ht, hψ_y2, hψ_u2]; exact hcy.2
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hrt
        (mem_leafNbrs.mp hrY1).1.symm
      rw [ht, hψ_Y1 r hrY1, hψ_u1]; exact (haY₁ r hrY1).2
  apply adm.contradiction hm ψ hagree
  · intro r hrS
    simp only [S, Finset.mem_insert] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1
    · rw [hψ_u1]; exact hα1C.1
    · rw [hψ_u2]; exact hα2C.1
    · rw [hψ_v1]; exact hc1L
    · rw [hψ_v2]; exact hc2L
    · rw [hψ_v3]; exact hc3Z.1
    · rw [hψ_w1]; exact hcw1.1
    · rw [hψ_w2]; exact hcw2.1
    · rw [hψ_a2]; exact hca.1.1
    · rw [hψ_y2]; exact hcy.1
    · rw [hψ_Y1 r hrY1]; exact (haY₁ r hrY1).1
  · intro a b hab hor
    rcases hor with ha | hb
    · exact hprop_S a ha b hab
    · exact (hprop_S b hb a hab.symm).symm
  · intro s hsS _ r hrS hsr
    rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψ_u1]; exact hα1C.2.2
    · rw [hψ_v3]; exact hc3Z.2.2
    · rw [hψ_w2]; exact hcw2.2.2.1
    · rw [hψ_a2]; exact hca.1.2.2
  · intro s hsS hiso ⟨r, hsr⟩
    have hrS : r ∈ S := by by_contra h; exact hiso r h hsr
    rcases hno_iso s hsS ⟨r, hrS, hsr⟩ with ⟨t, htS, hst⟩
    exact False.elim (hiso t htS hst)
  · intro r hrS _
    simp only [S, Finset.mem_insert] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1
    · apply pcf_from_leaf_and_three (γ := γ₁) huv₁ hu1y1 hadj (fun h => by subst h; omega)
        (fun h => by subst h; omega) hy1u2 (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y1
        (fun t ht => by
          rcases hall_u1 t ht with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h)))
      rw [hψ_v1, hagree y₁ hy1_not_S, hψ_u2]; exact hγ₁
    · apply pcf_from_four_list (γ := γ₂) hu2y2 hu2a2 hu2w1 hadj.symm
        (fun t ht => by
          rcases hall_u2 t ht with h | h | h | h
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inl h)
      rw [hψ_y2, hψ_a2, hψ_w1, hψ_u1]; exact hγ₂
    · exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
        (by rw [hψ_u1, hψ_v2]; exact hc2α1.symm)
    · exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
        (by rw [hψ_v1, hψ_v3]; exact hc3c1.symm)
    · exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
        (by rw [hψ_v2, hagree z₁ hz1_not_S]; exact hc2z1)
    · exact pcf_at_of_two_distinct_neighbors hdw1 hu2w1.symm hw12 hw2u2.symm
        (by rw [hψ_u2, hψ_w2]; exact hcw2.2.2.2.symm)
    · exact pcf_at_of_two_distinct_neighbors hdw2 hw12.symm hw2z2 hz2w1.symm
        (by rw [hψ_w1, hagree z₂ hz2_not_S]; exact hcw1.2.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda2 hu2a2.symm ha2p2 hp2u2.symm
        (by rw [hψ_u2, hagree p₂ hp2_not_S]; exact hα2C.2.2)
    · exact ⟨u₂, hu2y2.symm, fun t ht _ => unique_neighbor_of_deg_one hdy2 ht hu2y2.symm⟩
    · exact ⟨u₁, (mem_leafNbrs.mp hrY1).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 ht (mem_leafNbrs.mp hrY1).1.symm⟩

/-! ## 2. 引理 E3：`no_T3_adj_S3_2_a2`（`T3` 不与 `coreDeg = 3, |oneThreadNbrs| = 2` 相邻） -/

/-- 引理 E3：在 `9 * p ≤ 22 * q` 下，`T3` 顶点不能与满足 `coreDeg = 3` 且有 2 条 `1`-线串的顶点相邻！ -/
lemma no_T3_adj_S3_2_a2 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u₁ u₂ : V}
    (hu1 : IsT3 G u₁) (hc3 : coreDeg G u₂ = 3) (h1 : (oneThreadNbrs G u₂).card = 2)
    (hadj : G.Adj u₁ u₂) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hu12 : u₁ ≠ u₂ := G.ne_of_adj hadj
  -- 拆解 `u₁` (`IsT3`)
  rcases isT3_unpack hm hpq25 hu1 with
    ⟨v₁, v₂, v₃, z₁, x₁, y₁', huv₁, hdv₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, hdz1,
      hz1u1, hx₁, hy₁', hxy₁, hcore1, hY1_pos, hY1_card, hall_u1', hall_v1, hall_v2, hall_v3⟩
  have hst1 := isT3_structure hm hpq25 hu1
  have hdu1 : 4 ≤ G.degree u₁ := hst1.1
  -- 由引理 E0，`u₂` 不可能是 `3`-度点，故 `4 ≤ G.degree u₂` 且 `1 ≤ |leafNbrs G u₂|`！
  have hdu2_3 : 3 ≤ G.degree u₂ := by have := coreDeg_le_degree G u₂; omega
  have hdu2 : 4 ≤ G.degree u₂ := by
    by_contra h
    exact no_T3_adj_deg_three hm hpq25 hu1 hadj (by omega)
  let Y₁ := leafNbrs G u₁
  let Y₂ := leafNbrs G u₂
  have hY2_card : Y₂.card = G.degree u₂ - 3 := by
    have := coreDeg_add_leafNbrs hm u₂; dsimp only [Y₂]; omega
  have hY2_pos : 1 ≤ Y₂.card := by omega
  -- 拆解 `u₂` 的两条 `1`-线串 `a₁, a₂`
  rcases Finset.card_eq_two.mp h1 with ⟨a₁, a₂, ha12, hone2_eq⟩
  have ha1_mem : a₁ ∈ oneThreadNbrs G u₂ := by rw [hone2_eq]; simp
  have ha2_mem : a₂ ∈ oneThreadNbrs G u₂ := by rw [hone2_eq]; simp
  rcases oneThreadNbr_other_endpoint hm hdu2_3 ha1_mem with ⟨p₁, ha1p1, hp1u2, hdp1, _, haa1⟩
  rcases oneThreadNbr_other_endpoint hm hdu2_3 ha2_mem with ⟨p₂, ha2p2, hp2u2, hdp2, _, haa2⟩
  have hu2a1 : G.Adj u₂ a₁ := (mem_oneThreadNbrs.mp ha1_mem).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1_mem).2.1
  have hu2a2 : G.Adj u₂ a₂ := (mem_oneThreadNbrs.mp ha2_mem).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2_mem).2.1
  rcases exists_other_neighbor_of_deg_two hda1 hu2a1.symm with ⟨ta1, _, _, hall_a1'⟩
  have hall_a1 : ∀ r, G.Adj a₁ r → r = u₂ ∨ r = p₁ := fun r hr => by
    rcases hall_a1' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_a1' p₁ ha1p1).resolve_left hp1u2).symm)
  rcases exists_other_neighbor_of_deg_two hda2 hu2a2.symm with ⟨ta2, _, _, hall_a2'⟩
  have hall_a2 : ∀ r, G.Adj a₂ r → r = u₂ ∨ r = p₂ := fun r hr => by
    rcases hall_a2' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_a2' p₂ ha2p2).resolve_left hp2u2).symm)
  -- `coreNbrs G u₂ = {u₁, a₁, a₂}` 与 `u₂` 的全部邻点枚举
  have hcore2 : coreNbrs G u₂ = {u₁, a₁, a₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨hadj.symm, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hu2a1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hu2a2, by omega⟩
    · rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩),
          Finset.card_pair ha12]
      unfold coreDeg at hc3; omega
  have hall_u2 : ∀ r, G.Adj u₂ r → r = u₁ ∨ r = a₁ ∨ r = a₂ ∨ r ∈ Y₂ := by
    intro r hur
    have hr1 := degree_ge_one hm r
    by_cases hdr : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, hdr⟩)))
    · have hrc : r ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore2] at hrc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrc
      rcases hrc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  -- 确定 `u₁` 的另一好邻点 `y₁`
  have hu2_core1 : u₂ ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨hadj, by omega⟩
  rw [hcore1] at hu2_core1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu2_core1
  have hex_y1 : ∃ y₁ : V, y₁ ∈ goodNbrs G u₁ ∧ y₁ ≠ u₂ ∧
      ∀ r, G.Adj u₁ r → r = v₁ ∨ r = u₂ ∨ r = y₁ ∨ r ∈ Y₁ := by
    rcases hu2_core1 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu2; omega)
    · exact ⟨y₁', hy₁', hxy₁.symm, hall_u1'⟩
    · exact ⟨x₁, hx₁, hxy₁, fun r hr => by
        rcases hall_u1' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y1 with ⟨y₁, hy1_good, hy1u2, hall_u1⟩
  have hu1y1 : G.Adj u₁ y₁ := (mem_goodNbrs.mp hy1_good).1
  have hdy1 : 3 ≤ G.degree y₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy1_good).2
  -- 零重合性：`p₁ ≠ u₁`、`p₂ ≠ u₁`、`z₁ ≠ u₂`、`{v₁, v₂, v₃}` 不交 `{a₁, a₂}`
  have hp1u1 : p₁ ≠ u₁ := by
    intro h; subst p₁
    have ha1m : a₁ ∈ oneThreadNbrs G u₁ := by
      rw [mem_oneThreadNbrs]
      exact ⟨ha1p1.symm, hda1, u₂, hu2a1.symm, hp1u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨a₁, ha1m⟩; omega
  have hp2u1 : p₂ ≠ u₁ := by
    intro h; subst p₂
    have ha2m : a₂ ∈ oneThreadNbrs G u₁ := by
      rw [mem_oneThreadNbrs]
      exact ⟨ha2p2.symm, hda2, u₂, hu2a2.symm, hp2u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨a₂, ha2m⟩; omega
  have hv_ne_a : ∀ x ∈ ({v₁, v₂, v₃} : Finset V), ∀ b ∈ ({a₁, a₂} : Finset V), x ≠ b := by
    intro x hx b hb heq; subst heq
    have hx_has2 : ∃ w, G.Adj x w ∧ G.degree w = 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨v₂, hv12, hdv₂⟩
      · exact ⟨v₁, hv12.symm, hdv₁⟩
      · exact ⟨v₂, hv23.symm, hdv₂⟩
    rcases hx_has2 with ⟨w, hxw, hdw2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · rcases hall_a1 w hxw with rfl | rfl <;> omega
    · rcases hall_a2 w hxw with rfl | rfl <;> omega
  have hz1u2 : z₁ ≠ u₂ := by
    intro h; subst z₁
    have hv3c : v₃ ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨hv3z1.symm, by omega⟩
    rw [hcore2] at hv3c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv3c
    rcases hv3c with h | h | h
    · rw [h] at hdv₃; omega
    · exact hv_ne_a v₃ (by simp) a₁ (by simp) h
    · exact hv_ne_a v₃ (by simp) a₂ (by simp) h
  have hY12_disj : Disjoint Y₁ Y₂ := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    exact hu12 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hr1).2
      (mem_leafNbrs.mp hr1).1.symm (mem_leafNbrs.mp hr2).1.symm)
  -- 构造删除集 `S`
  let S : Finset V :=
    insert u₁ (insert u₂ (insert v₁ (insert v₂ (insert v₃ (insert a₁ (insert a₂ (Y₁ ∪ Y₂)))))))
  have hu1S : u₁ ∈ S := Finset.mem_insert_self u₁ _
  have hY1_subS : Y₁ ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))))
  have hY2_subS : Y₂ ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))))
  have hy1_not_S : y₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨(G.ne_of_adj hu1y1).symm, hy1u2, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz1_not_S : z₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hz1u1, hz1u2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hp1_not_S : p₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hp1u1, hp1u2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hp2_not_S : p₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hp2u1, hp2u2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  -- 刻画跨过 `S` 边界的 4 条边
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = u₁ ∧ s = y₁) ∨ (r = v₃ ∧ s = z₁) ∨ (r = a₁ ∧ s = p₁) ∨ (r = a₂ ∧ s = p₂) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1 | hrY2
    · rcases hall_u1 s hsr.symm with rfl | rfl | rfl | hsY1
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hsS (hY1_subS hsY1))
    · rcases hall_u2 s hsr.symm with rfl | rfl | rfl | hsY2
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (hY2_subS hsY2))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hall_a1 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rcases hall_a2 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hsr.symm
        (mem_leafNbrs.mp hrY1).1.symm
      exact False.elim (hsS (by rw [this]; exact hu1S))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hsr.symm
        (mem_leafNbrs.mp hrY2).1.symm
      exact False.elim (hsS (by rw [this]; simp [S]))
  -- 证明 `S` 外无孤立邻点（唯一孤立 4-度点 `s` 导出 `|K| = 8, ∑ coreDeg = 20`，`176 ≤ 180` 矛盾！）
  have hno_iso : ∀ s ∉ S, (∃ r ∈ S, G.Adj s r) → ∃ t ∉ S, G.Adj s t := by
    intro s hsS ⟨r₀, hr0S, hsr0⟩
    by_contra hiso; push Not at hiso
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ hr0S hsr0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hsub : G.neighborFinset s ⊆ {u₁, v₃, a₁, a₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hiso r h hr
      rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hds4 : 4 ≤ G.degree s := by
      by_cases h1 : G.Adj s u₁
      · by_contra h4
        exact no_T3_adj_deg_three hm hpq25 hu1 h1.symm (by omega)
      · by_cases h2 : G.Adj s v₃
        · rcases hS_out s hsS v₃ (by simp [S]) h2 with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact hdz1
          · exact False.elim (hv_ne_a v₃ (by simp) a₁ (by simp) h)
          · exact False.elim (hv_ne_a v₃ (by simp) a₂ (by simp) h)
        · have hsub2 : G.neighborFinset s ⊆ {a₁, a₂} := by
            intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
            have hrS : r ∈ S := by by_contra h; exact hiso r h hr
            rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact False.elim (h1 hr)
            · exact False.elim (h2 hr)
            · simp
            · simp
          have hc := Finset.card_le_card hsub2
          rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := Finset.card_le_two (a := a₁) (b := a₂); omega
    have h4_le : ({u₁, v₃, a₁, a₂} : Finset V).card ≤ 4 := card_quad_le u₁ v₃ a₁ a₂
    have hcard_eq : G.neighborFinset s = {u₁, v₃, a₁, a₂} :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
    have hds_eq4 : G.degree s = 4 := by
      have hc := congrArg Finset.card hcard_eq
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc; omega
    have hs_y1 : s = y₁ := by
      have had : G.Adj s u₁ := (G.mem_neighborFinset s u₁).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS u₁ hu1S had with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (by rw [h] at hdu1; omega)
      · exact False.elim (by rw [h] at hdu1; omega)
      · exact False.elim (by rw [h] at hdu1; omega)
    have hs_z1 : s = z₁ := by
      have had : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS v₃ (by simp [S]) had with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (by rw [h] at hdv₃; omega)
      · exact h
      · exact False.elim (hv_ne_a v₃ (by simp) a₁ (by simp) h)
      · exact False.elim (hv_ne_a v₃ (by simp) a₂ (by simp) h)
    have hs_p1 : s = p₁ := by
      have had : G.Adj s a₁ := (G.mem_neighborFinset s a₁).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS a₁ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim (by rw [h] at hda1; omega)
      · exact False.elim (hv_ne_a v₃ (by simp) a₁ (by simp) h.symm)
      · exact h
      · exact False.elim (ha12 h)
    have hs_p2 : s = p₂ := by
      have had : G.Adj s a₂ := (G.mem_neighborFinset s a₂).mp (by rw [hcard_eq]; simp)
      rcases hS_out s hsS a₂ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (by rw [h] at hda2; omega)
      · exact False.elim (hv_ne_a v₃ (by simp) a₂ (by simp) h.symm)
      · exact False.elim (ha12 h.symm)
      · exact h
    have hall_univ : insert s S = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := s) (Finset.mem_insert_self s S)
      intro a ha b hab
      simp only [Finset.mem_insert] at ha ⊢
      rcases ha with rfl | haS
      · exact Or.inr (by by_contra hbS; exact hiso b hbS hab)
      · by_cases hbS : b ∈ S
        · exact Or.inr hbS
        · rcases hS_out b hbS a haS hab.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact Or.inl hs_y1.symm
          · exact Or.inl hs_z1.symm
          · exact Or.inl hs_p1.symm
          · exact Or.inl hs_p2.symm
    have hK_eq : coreVerts G = {s, u₁, u₂, v₁, v₂, v₃, a₁, a₂} := by
      ext r; simp only [mem_coreVerts, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hr2
        have hrU : r ∈ insert s S := by rw [hall_univ]; exact Finset.mem_univ r
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrU
        rcases hrU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hY1 | hY2
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · exact False.elim (by rw [mem_leafNbrs] at hY1; omega)
        · exact False.elim (by rw [mem_leafNbrs] at hY2; omega)
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
    have hsu1 : s ≠ u₁ := fun h => hsS (h ▸ hu1S)
    have hsu2 : s ≠ u₂ := fun h => hsS (by rw [h]; simp [S])
    have hK8 : (coreVerts G).card = 8 := by
      rw [hK_eq]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsu1, hsu2, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hu12, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv12, hv31.symm, hv_ne_a v₁ (by simp) a₁ (by simp),
          hv_ne_a v₁ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv23, hv_ne_a v₂ (by simp) a₁ (by simp),
          hv_ne_a v₂ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_ne_a v₃ (by simp) a₁ (by simp), hv_ne_a v₃ (by simp) a₂ (by simp)⟩)]
      rw [Finset.card_pair ha12]
    have hcs4 : coreDeg G s = 4 := by
      have hEq : coreNbrs G s = G.neighborFinset s := by
        ext r; simp only [mem_coreNbrs, SimpleGraph.mem_neighborFinset]
        exact ⟨And.left, fun hr => ⟨hr, by
          have : r ∈ ({u₁, v₃, a₁, a₂} : Finset V) := by
            rw [← hcard_eq, SimpleGraph.mem_neighborFinset]; exact hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl | rfl | rfl <;> omega⟩⟩
      rw [coreDeg, hEq, SimpleGraph.card_neighborFinset_eq_degree, hds_eq4]
    have hKsum : ∑ r ∈ coreVerts G, coreDeg G r = 20 := by
      rw [hK_eq]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsu1, hsu2, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hu12, fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => by subst h; omega, fun h => by subst h; omega,
          fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv12, hv31.symm, hv_ne_a v₁ (by simp) a₁ (by simp),
          hv_ne_a v₁ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hv23, hv_ne_a v₂ (by simp) a₁ (by simp),
          hv_ne_a v₂ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_ne_a v₃ (by simp) a₁ (by simp), hv_ne_a v₃ (by simp) a₂ (by simp)⟩)]
      rw [Finset.sum_pair ha12]
      have hc_v1 : coreDeg G v₁ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₁]
      have hc_v2 : coreDeg G v₂ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₂]
      have hc_v3 : coreDeg G v₃ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₃]
      have hc_a1 : coreDeg G a₁ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hda1]
      have hc_a2 : coreDeg G a₂ = 2 := by
        rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hda2]
      rw [hcs4, hu1.1, hc3, hc_v1, hc_v2, hc_v3, hc_a1, hc_a2]
      rfl
    exact mad_22_9_contra hm hpq hK8 hKsum (by omega)
  -- 主染色阶段：容许染色 + `s32_a2_fixed_color_extension` + `t3_fun_color_extension`
  rcases exists_admissible_coloring hm ⟨u₁, hu1S⟩ with ⟨adm⟩
  have hLu1 : (L u₁).card = Y₁.card + 4 := by
    dsimp only [Y₁]; rw [hm.list_card u₁]; unfold kappa; split_ifs <;> omega
  have hLu2 : (L u₂).card = Y₂.card + 4 := by
    rw [hm.list_card u₂]; unfold kappa; split_ifs <;> omega
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  have hY1_L2 : ∀ r ∈ Y₁, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY2_L2 : ∀ r ∈ Y₂, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  let A₁ : Finset ℕ := L a₁ \ {adm.φ p₁, adm.φs p₁}
  let A₂ : Finset ℕ := L a₂ \ {adm.φ p₂, adm.φs p₂}
  have hA1 : 2 ≤ A₁.card := by
    dsimp only [A₁]; have := card_sdiff_ge (L a₁) {adm.φ p₁, adm.φs p₁}
    have := Finset.card_le_two (a := adm.φ p₁) (b := adm.φs p₁); omega
  have hA2 : 2 ≤ A₂.card := by
    dsimp only [A₂]; have := card_sdiff_ge (L a₂) {adm.φ p₂, adm.φs p₂}
    have := Finset.card_le_two (a := adm.φ p₂) (b := adm.φs p₂); omega
  have hu2_ext : ∀ α₁ : ℕ, ∃ α₂ ∈ L u₂ \ {α₁, adm.φ p₁, adm.φ p₂},
      ∃ ca₁ ∈ A₁ \ {α₂}, ∃ ca₂ ∈ A₂ \ {α₂},
      ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
      ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
        ([ca₁, ca₂, α₁] : List ℕ).count γ₂ = 1 := by
    intro α₁
    have hC2 : Y₂.card + 1 ≤ (L u₂ \ {α₁, adm.φ p₁, adm.φ p₂}).card := by
      have := card_sdiff_ge (L u₂) {α₁, adm.φ p₁, adm.φ p₂}
      have := card_triple_le α₁ (adm.φ p₁) (adm.φ p₂); omega
    have hnot : α₁ ∉ L u₂ \ {α₁, adm.φ p₁, adm.φ p₂} := by simp
    exact s32_a2_fixed_color_extension hY2_pos hY2_L2 hA1 hA2 hC2 hnot
  let f₂ : ℕ → ℕ := fun α₁ => (hu2_ext α₁).choose
  let Z₁ : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
  have hZ1 : 2 ≤ Z₁.card := by
    dsimp only [Z₁]; have := card_sdiff_ge (L v₃) {adm.φ z₁, adm.φs z₁}
    have := Finset.card_le_two (a := adm.φ z₁) (b := adm.φs z₁); omega
  let C₁ : Finset ℕ := L u₁ \ {adm.φ y₁, adm.φs y₁}
  have hC1 : Y₁.card + 1 ≤ C₁.card := by
    dsimp only [C₁]; have := card_sdiff_ge (L u₁) {adm.φ y₁, adm.φs y₁}
    have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φs y₁); omega
  rcases t3_fun_color_extension (L := L) (Y := Y₁) (L₁ := L v₁) (L₂ := L v₂) (Z₃ := Z₁)
    (C_u := C₁) (φy := adm.φ y₁) (φz := adm.φ z₁) f₂ hY1_pos hY1_L2 hLv1 hLv2 hZ1 hC1 with
    ⟨α₁, hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
  let α₂ : ℕ := f₂ α₁
  have hα2_spec := (hu2_ext α₁).choose_spec
  change α₂ ∈ L u₂ \ {α₁, adm.φ p₁, adm.φ p₂} ∧
      ∃ ca₁ ∈ A₁ \ {α₂}, ∃ ca₂ ∈ A₂ \ {α₂},
      ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
      ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
        ([ca₁, ca₂, α₁] : List ℕ).count γ₂ = 1 at hα2_spec
  rcases hα2_spec with ⟨hα2C, ca₁, hca1, ca₂, hca2, aY₂, haY₂, γ₂, hγ₂⟩
  rcases unpack_threeThreadGoodCols hc₁ with
    ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2z1, c₃, hc3Z, hc3c2, hc3c1⟩
  simp only [C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1C
  simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
  simp only [A₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca1
  simp only [A₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca2
  let ψ : V → ℕ := fun r =>
    if r = u₁ then α₁
    else if r = u₂ then α₂
    else if r = v₁ then c₁
    else if r = v₂ then c₂
    else if r = v₃ then c₃
    else if r = a₁ then ca₁
    else if r = a₂ then ca₂
    else if r ∈ Y₁ then aY₁ r
    else if r ∈ Y₂ then aY₂ r
    else adm.φ r
  have hψ_u1 : ψ u₁ = α₁ := by simp [ψ]
  have hψ_u2 : ψ u₂ = α₂ := by simp [ψ, hu12.symm]
  have hψ_v1 : ψ v₁ = c₁ := by
    simp [ψ, (show v₁ ≠ u₁ by intro h; subst h; omega), (show v₁ ≠ u₂ by intro h; subst h; omega)]
  have hψ_v2 : ψ v₂ = c₂ := by
    simp [ψ, (show v₂ ≠ u₁ by intro h; subst h; omega), (show v₂ ≠ u₂ by intro h; subst h; omega),
      (G.ne_of_adj hv12).symm]
  have hψ_v3 : ψ v₃ = c₃ := by
    simp [ψ, (show v₃ ≠ u₁ by intro h; subst h; omega), (show v₃ ≠ u₂ by intro h; subst h; omega),
      hv31, (G.ne_of_adj hv23).symm]
  have hψ_a1 : ψ a₁ = ca₁ := by
    simp [ψ, (show a₁ ≠ u₁ by intro h; subst h; omega), (show a₁ ≠ u₂ by intro h; subst h; omega),
      (hv_ne_a v₁ (by simp) a₁ (by simp)).symm, (hv_ne_a v₂ (by simp) a₁ (by simp)).symm,
      (hv_ne_a v₃ (by simp) a₁ (by simp)).symm]
  have hψ_a2 : ψ a₂ = ca₂ := by
    simp [ψ, (show a₂ ≠ u₁ by intro h; subst h; omega), (show a₂ ≠ u₂ by intro h; subst h; omega),
      (hv_ne_a v₁ (by simp) a₂ (by simp)).symm, (hv_ne_a v₂ (by simp) a₂ (by simp)).symm,
      (hv_ne_a v₃ (by simp) a₂ (by simp)).symm, ha12.symm]
  have hψ_Y1 : ∀ r ∈ Y₁, ψ r = aY₁ r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    simp [ψ, hr, (show r ≠ u₁ by intro h; subst h; omega),
      (show r ≠ u₂ by intro h; subst h; omega), (show r ≠ v₁ by intro h; subst h; omega),
      (show r ≠ v₂ by intro h; subst h; omega), (show r ≠ v₃ by intro h; subst h; omega),
      (show r ≠ a₁ by intro h; subst h; omega), (show r ≠ a₂ by intro h; subst h; omega)]
  have hψ_Y2 : ∀ r ∈ Y₂, ψ r = aY₂ r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    have hnot1 : r ∉ Y₁ := Finset.disjoint_right.mp hY12_disj hr
    simp [ψ, hr, hnot1, (show r ≠ u₁ by intro h; subst h; omega),
      (show r ≠ u₂ by intro h; subst h; omega), (show r ≠ v₁ by intro h; subst h; omega),
      (show r ≠ v₂ by intro h; subst h; omega), (show r ≠ v₃ by intro h; subst h; omega),
      (show r ≠ a₁ by intro h; subst h; omega), (show r ≠ a₂ by intro h; subst h; omega)]
  have hagree : ∀ x, x ∉ S → ψ x = adm.φ x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hx
    rcases hx with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    simp [ψ, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have hprop_S : ∀ r ∈ S, ∀ t, G.Adj r t → ψ r ≠ ψ t := by
    intro r hrS t hrt
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1 | hrY2
    · rcases hall_u1 t hrt with ht | ht | ht | htY1
      · rw [ht, hψ_u1, hψ_v1]; exact Ne.symm hc1α1
      · rw [ht, hψ_u1, hψ_u2]; exact Ne.symm hα2C.2.1
      · rw [ht, hψ_u1, hagree y₁ hy1_not_S]; exact hα1C.2.1
      · rw [hψ_u1, hψ_Y1 t htY1]; exact Ne.symm (haY₁ t htY1).2
    · rcases hall_u2 t hrt with ht | ht | ht | htY2
      · rw [ht, hψ_u2, hψ_u1]; exact hα2C.2.1
      · rw [ht, hψ_u2, hψ_a1]; exact Ne.symm hca1.2
      · rw [ht, hψ_u2, hψ_a2]; exact Ne.symm hca2.2
      · rw [hψ_u2, hψ_Y2 t htY2]; exact Ne.symm (haY₂ t htY2).2
    · rcases hall_v1 t hrt with ht | ht
      · rw [ht, hψ_v1, hψ_u1]; exact hc1α1
      · rw [ht, hψ_v1, hψ_v2]; exact Ne.symm hc2c1
    · rcases hall_v2 t hrt with ht | ht
      · rw [ht, hψ_v2, hψ_v1]; exact hc2c1
      · rw [ht, hψ_v2, hψ_v3]; exact Ne.symm hc3c2
    · rcases hall_v3 t hrt with ht | ht
      · rw [ht, hψ_v3, hψ_v2]; exact hc3c2
      · rw [ht, hψ_v3, hagree z₁ hz1_not_S]; exact hc3Z.2.1
    · rcases hall_a1 t hrt with ht | ht
      · rw [ht, hψ_a1, hψ_u2]; exact hca1.2
      · rw [ht, hψ_a1, hagree p₁ hp1_not_S]; exact hca1.1.2.1
    · rcases hall_a2 t hrt with ht | ht
      · rw [ht, hψ_a2, hψ_u2]; exact hca2.2
      · rw [ht, hψ_a2, hagree p₂ hp2_not_S]; exact hca2.1.2.1
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hrt
        (mem_leafNbrs.mp hrY1).1.symm
      rw [ht, hψ_Y1 r hrY1, hψ_u1]; exact (haY₁ r hrY1).2
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hrt
        (mem_leafNbrs.mp hrY2).1.symm
      rw [ht, hψ_Y2 r hrY2, hψ_u2]; exact (haY₂ r hrY2).2
  apply adm.contradiction hm ψ hagree
  · intro r hrS
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1 | hrY2
    · rw [hψ_u1]; exact hα1C.1
    · rw [hψ_u2]; exact hα2C.1
    · rw [hψ_v1]; exact hc1L
    · rw [hψ_v2]; exact hc2L
    · rw [hψ_v3]; exact hc3Z.1
    · rw [hψ_a1]; exact hca1.1.1
    · rw [hψ_a2]; exact hca2.1.1
    · rw [hψ_Y1 r hrY1]; exact (haY₁ r hrY1).1
    · rw [hψ_Y2 r hrY2]; exact (haY₂ r hrY2).1
  · intro a b hab hor
    rcases hor with ha | hb
    · exact hprop_S a ha b hab
    · exact (hprop_S b hb a hab.symm).symm
  · intro s hsS _ r hrS hsr
    rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψ_u1]; exact hα1C.2.2
    · rw [hψ_v3]; exact hc3Z.2.2
    · rw [hψ_a1]; exact hca1.1.2.2
    · rw [hψ_a2]; exact hca2.1.2.2
  · intro s hsS hiso ⟨r, hsr⟩
    have hrS : r ∈ S := by by_contra h; exact hiso r h hsr
    rcases hno_iso s hsS ⟨r, hrS, hsr⟩ with ⟨t, htS, hst⟩
    exact False.elim (hiso t htS hst)
  · intro r hrS _
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY1 | hrY2
    · apply pcf_from_leaf_and_three (γ := γ₁) huv₁ hu1y1 hadj (fun h => by subst h; omega)
        (fun h => by subst h; omega) hy1u2 (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y1
        (fun t ht => by
          rcases hall_u1 t ht with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h)))
      rw [hψ_v1, hagree y₁ hy1_not_S, hψ_u2]; exact hγ₁
    · apply pcf_from_leaf_and_three (γ := γ₂) hu2a1 hu2a2 hadj.symm ha12
        (fun h => by subst h; omega)
        (fun h => by subst h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y2
        (fun t ht => by
          rcases hall_u2 t ht with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h)))
      rw [hψ_a1, hψ_a2, hψ_u1]; exact hγ₂
    · exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
        (by rw [hψ_u1, hψ_v2]; exact hc2α1.symm)
    · exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
        (by rw [hψ_v1, hψ_v3]; exact hc3c1.symm)
    · exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
        (by rw [hψ_v2, hagree z₁ hz1_not_S]; exact hc2z1)
    · exact pcf_at_of_two_distinct_neighbors hda1 hu2a1.symm ha1p1 hp1u2.symm
        (by rw [hψ_u2, hagree p₁ hp1_not_S]; exact hα2C.2.2.1)
    · exact pcf_at_of_two_distinct_neighbors hda2 hu2a2.symm ha2p2 hp2u2.symm
        (by rw [hψ_u2, hagree p₂ hp2_not_S]; exact hα2C.2.2.2)
    · exact ⟨u₁, (mem_leafNbrs.mp hrY1).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 ht (mem_leafNbrs.mp hrY1).1.symm⟩
    · exact ⟨u₂, (mem_leafNbrs.mp hrY2).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 ht (mem_leafNbrs.mp hrY2).1.symm⟩

/-! ## 3. 引理 E4：`no_T3_T20_T3`（`T20` 不能同时邻接两个不同的 `T3` 顶点） -/

private lemma no_T3_T20_T3_shared {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u u₁ u₂ : V}
    (hu : IsT20 G u) (hu1 : IsT3 G u₁) (hu2 : IsT3 G u₂)
    (h1 : G.Adj u u₁) (h2 : G.Adj u u₂) (h12 : u₁ ≠ u₂)
    (hsh : ∀ v ∈ threeThreadNbrs G u₁, u₂ ∈ threadAnchors G v) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have huu1 : u ≠ u₁ := G.ne_of_adj h1
  have huu2 : u ≠ u₂ := G.ne_of_adj h2
  -- 拆解 `u` (`IsT20`)
  have hst := isT20_structure hm hpq25 hu
  have hdu : 4 ≤ G.degree u := hst.1
  rcases hu.2.1 with ⟨xu, hxu_mem⟩
  rcases twoThreadNbr_other_endpoint hm (by omega) hxu_mem with
    ⟨yu, zu, huxu, hdxu, hxuyu, hyuu, hdyu, hyuzu, hzuxu, huzu, hdzu3, _, haxu, hayu⟩
  have hdzu : 4 ≤ G.degree zu := by
    have hyulong : yu ∈ longThreadNbrs G zu := by
      unfold longThreadNbrs degTwoNbrs
      rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hyuzu.symm, hdyu⟩, hyuzu.symm, hdyu, xu, hxuyu.symm, hzuxu.symm, hdxu⟩
    exact deg_ge_four_of_longThreadNbr hm hdzu3 hyulong
  rcases exists_other_neighbor_of_deg_two hdxu huxu.symm with ⟨txu, _, _, hall_xu'⟩
  have hall_xu : ∀ r, G.Adj xu r → r = u ∨ r = yu := fun r hr => by
    rcases hall_xu' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_xu' yu hxuyu).resolve_left hyuu).symm)
  rcases exists_other_neighbor_of_deg_two hdyu hxuyu.symm with ⟨tyu, _, _, hall_yu'⟩
  have hall_yu : ∀ r, G.Adj yu r → r = xu ∨ r = zu := fun r hr => by
    rcases hall_yu' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_yu' zu hyuzu).resolve_left hzuxu).symm)
  -- 拆解 `u₁`, `u₂` (`IsT3`)
  rcases isT3_unpack hm hpq25 hu1 with
    ⟨v₁, v₂, v₃, z₁, x₁, y₁', huv₁, hdv₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, hdz1,
      hz1u1, hx₁, hy₁', hxy₁, hcore1, hY1_pos, hY1_card, hall_u1', hall_v1, hall_v2, hall_v3⟩
  rcases isT3_unpack hm hpq25 hu2 with
    ⟨w₁, w₂, w₃, z₂, x₂, y₂', huw₁, hdw₁, hw12, hw2u2, hdw₂, hw23, hw31, hdw₃, hw3z2, hzw2, hdz2,
      hz2u2, hx₂, hy₂', hxy₂, hcore2, hY2_pos, hY2_card, hall_u2', hall_w1, hall_w2, hall_w3⟩
  have hst1 := isT3_structure hm hpq25 hu1
  have hst2 := isT3_structure hm hpq25 hu2
  have hdu1 : 4 ≤ G.degree u₁ := hst1.1
  have hdu2 : 4 ≤ G.degree u₂ := hst2.1
  let Yu := leafNbrs G u
  let Y₁ := leafNbrs G u₁
  let Y₂ := leafNbrs G u₂
  have hYu_card : Yu.card = G.degree u - 3 := by
    have := coreDeg_add_leafNbrs hm u; have := hu.1; dsimp only [Yu]; omega
  have hYu_pos : 1 ≤ Yu.card := by omega
  -- `u` 的全部核心邻点为 `{xu, u₁, u₂}`
  have hcore_u : coreNbrs G u = {xu, u₁, u₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huxu, by omega⟩
      · exact mem_coreNbrs.mpr ⟨h1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨h2, by omega⟩
    · rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩),
          Finset.card_pair h12]
      have := hu.1; unfold coreDeg at this; omega
  have hall_u : ∀ r, G.Adj u r → r = xu ∨ r = u₁ ∨ r = u₂ ∨ r ∈ Yu := by
    intro r hur
    have hr1 := degree_ge_one hm r
    by_cases hdr : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, hdr⟩)))
    · have hrc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_u] at hrc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrc
      rcases hrc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  -- 确定 `u₁`、`u₂` 各自除 `u` 之外的另一好邻点 `y₁, y₂`
  have hu_core1 : u ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨h1.symm, by omega⟩
  rw [hcore1] at hu_core1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_core1
  have hex_y1 : ∃ y₁ : V, y₁ ∈ goodNbrs G u₁ ∧ y₁ ≠ u ∧
      ∀ r, G.Adj u₁ r → r = v₁ ∨ r = u ∨ r = y₁ ∨ r ∈ Y₁ := by
    rcases hu_core1 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu; omega)
    · exact ⟨y₁', hy₁', hxy₁.symm, hall_u1'⟩
    · exact ⟨x₁, hx₁, hxy₁, fun r hr => by
        rcases hall_u1' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y1 with ⟨y₁, hy1_good, hy1u, hall_u1⟩
  have hu1y1 : G.Adj u₁ y₁ := (mem_goodNbrs.mp hy1_good).1
  have hdy1 : 3 ≤ G.degree y₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy1_good).2
  have hu_core2 : u ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨h2.symm, by omega⟩
  rw [hcore2] at hu_core2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_core2
  have hex_y2 : ∃ y₂ : V, y₂ ∈ goodNbrs G u₂ ∧ y₂ ≠ u ∧
      ∀ r, G.Adj u₂ r → r = w₁ ∨ r = u ∨ r = y₂ ∨ r ∈ Y₂ := by
    rcases hu_core2 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu; omega)
    · exact ⟨y₂', hy₂', hxy₂.symm, hall_u2'⟩
    · exact ⟨x₂, hx₂, hxy₂, fun r hr => by
        rcases hall_u2' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y2 with ⟨y₂, hy2_good, hy2u, hall_u2⟩
  have hu2y2 : G.Adj u₂ y₂ := (mem_goodNbrs.mp hy2_good).1
  have hdy2 : 3 ≤ G.degree y₂ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy2_good).2
  -- 由引理 E1，`¬ G.Adj u₁ u₂`，并排除所有跨顶点重合
  have hnadj12 : ¬ G.Adj u₁ u₂ := fun h => no_T3_adj_T3 hm hpq hu1 hu2 h
  have hy1u2 : y₁ ≠ u₂ := fun h => hnadj12 (h ▸ hu1y1)
  have hy2u1 : y₂ ≠ u₁ := fun h => hnadj12 (h ▸ hu2y2).symm
  have hzuu1 : zu ≠ u₁ := by
    intro h; subst zu
    have hyum : yu ∈ twoThreadNbrs G u₁ := by
      rw [mem_twoThreadNbrs]
      exact ⟨hyuzu.symm, hdyu, xu, u, hxuyu.symm, hzuxu.symm, hdxu, huxu.symm, hyuu.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨yu, hyum⟩; omega
  have hzuu2 : zu ≠ u₂ := by
    intro h; subst zu
    have hyum : yu ∈ twoThreadNbrs G u₂ := by
      rw [mem_twoThreadNbrs]
      exact ⟨hyuzu.symm, hdyu, xu, u, hxuyu.symm, hzuxu.symm, hdxu, huxu.symm, hyuu.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨yu, hyum⟩; omega
  have hz1u : z₁ ≠ u := by
    intro h; subst z₁
    have hv3m : v₃ ∈ threeThreadNbrs G u := by
      rw [mem_threeThreadNbrs]
      exact ⟨hv3z1.symm, hdv₃, v₂, v₁, u₁, hv23.symm, hzv2.symm, hdv₂, hv12.symm, hv31.symm,
        hdv₁, huv₁.symm, hv2u1.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨v₃, hv3m⟩; omega
  have hz2u : z₂ ≠ u := by
    intro h; subst z₂
    have hw3m : w₃ ∈ threeThreadNbrs G u := by
      rw [mem_threeThreadNbrs]
      exact ⟨hw3z2.symm, hdw₃, w₂, w₁, u₂, hw23.symm, hzw2.symm, hdw₂, hw12.symm, hw31.symm,
        hdw₁, huw₁.symm, hw2u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨w₃, hw3m⟩; omega
  -- 线串不交性与叶集两两不交
  have ha_v := threeThread_anchors_eq hm (by omega) (by omega) hz1u1.symm
    hdv₁ hdv₂ hdv₃ huv₁ hv12 hv2u1 hv23 hv31 hv3z1 hzv2
  have ha_w := threeThread_anchors_eq hm (by omega) (by omega) hz2u2.symm
    hdw₁ hdw₂ hdw₃ huw₁ hw12 hw2u2 hw23 hw31 hw3z2 hzw2
  have hx_ne_v : ∀ a ∈ ({xu, yu} : Finset V), ∀ b ∈ ({v₁, v₂, v₃} : Finset V), a ≠ b := by
    intro a ha b hb heq; subst heq
    have ha_anc : threadAnchors G a = {u, zu} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact haxu
      · exact hayu
    have hu_in : u ∈ threadAnchors G a := by rw [ha_anc]; simp
    have hb_anc : threadAnchors G a = {u₁, z₁} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ha_v.1
      · exact ha_v.2.1
      · exact ha_v.2.2
    rw [hb_anc] at hu_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in
    exact hu_in.elim huu1 hz1u.symm
  have hx_ne_w : ∀ a ∈ ({xu, yu} : Finset V), ∀ b ∈ ({w₁, w₂, w₃} : Finset V), a ≠ b := by
    intro a ha b hb heq; subst heq
    have ha_anc : threadAnchors G a = {u, zu} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact haxu
      · exact hayu
    have hu_in : u ∈ threadAnchors G a := by rw [ha_anc]; simp
    have hb_anc : threadAnchors G a = {u₂, z₂} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ha_w.1
      · exact ha_w.2.1
      · exact ha_w.2.2
    rw [hb_anc] at hu_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in
    exact hu_in.elim huu2 hz2u.symm
  have hYu1_disj : Disjoint Yu Y₁ := by
    rw [Finset.disjoint_left]; intro r hru hr1
    exact huu1 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hru).2
      (mem_leafNbrs.mp hru).1.symm (mem_leafNbrs.mp hr1).1.symm)
  have hYu2_disj : Disjoint Yu Y₂ := by
    rw [Finset.disjoint_left]; intro r hru hr2
    exact huu2 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hru).2
      (mem_leafNbrs.mp hru).1.symm (mem_leafNbrs.mp hr2).1.symm)
  have hY12_disj : Disjoint Y₁ Y₂ := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    exact h12 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hr1).2
      (mem_leafNbrs.mp hr1).1.symm (mem_leafNbrs.mp hr2).1.symm)
  -- 列表基数预备
  have hLu : (L u).card = Yu.card + 4 := by
    rw [hYu_card, hm.list_card u]; unfold kappa; split_ifs <;> omega
  have hLu1 : (L u₁).card = Y₁.card + 4 := by
    dsimp only [Y₁]; rw [hm.list_card u₁]; unfold kappa; split_ifs <;> omega
  have hLu2 : (L u₂).card = Y₂.card + 4 := by
    dsimp only [Y₂]; rw [hm.list_card u₂]; unfold kappa; split_ifs <;> omega
  have hLxu : (L xu).card = 4 := by rw [hm.list_card xu]; simp [kappa, hdxu]
  have hLyu : (L yu).card = 4 := by rw [hm.list_card yu]; simp [kappa, hdyu]
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw₁]
  have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw₂]
  have hLw3 : (L w₃).card = 4 := by rw [hm.list_card w₃]; simp [kappa, hdw₃]
  have hYu_L2 : ∀ r ∈ Yu, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY1_L2 : ∀ r ∈ Y₁, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY2_L2 : ∀ r ∈ Y₂, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  -- 分两种几何情形：`z₁ = u₂`（共享 `3`-线串）与 `z₁ ≠ u₂`（两条不交 `3`-线串）
  have hshared : z₁ = u₂ := by
    have hv1m : v₁ ∈ threeThreadNbrs G u₁ := by
      rw [mem_threeThreadNbrs]
      exact ⟨huv₁, hdv₁, v₂, v₃, z₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, by omega⟩
    have hin := hsh v₁ hv1m
    rw [ha_v.1] at hin; simp only [Finset.mem_insert, Finset.mem_singleton] at hin
    exact (hin.resolve_left h12.symm).symm
  subst z₁
  have hw1_eq_v3 : w₁ = v₃ := by
    have hv3_mem : v₃ ∈ threeThreadNbrs G u₂ := by
      rw [mem_threeThreadNbrs]
      exact ⟨hv3z1.symm, hdv₃, v₂, v₁, u₁, hv23.symm, hzv2.symm, hdv₂, hv12.symm, hv31.symm,
        hdv₁, huv₁.symm, hv2u1.symm, by omega⟩
    have hw1_mem : w₁ ∈ threeThreadNbrs G u₂ := by
      rw [mem_threeThreadNbrs]
      exact ⟨huw₁, hdw₁, w₂, w₃, z₂, hw12, hw2u2, hdw₂, hw23, hw31, hdw₃, hw3z2, hzw2, by omega⟩
    have hcard1 := hst2.2.1
    exact Finset.card_le_one.mp (by rw [hcard1]) w₁ hw1_mem v₃ hv3_mem
  rw [hw1_eq_v3] at hall_u2
  let S : Finset V :=
    insert u (insert u₁ (insert u₂ (insert xu (insert yu
      (insert v₁ (insert v₂ (insert v₃ (Yu ∪ (Y₁ ∪ Y₂)))))))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hYu_subS : Yu ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))))))
  have hY1_subS : Y₁ ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl hr)))))))))
  have hY2_subS : Y₂ ⊆ S := fun r hr => by
    simp only [S, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr hr)))))))))
  have hzu_not_S : zu ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨huzu.symm, hzuu1, hzuu2, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hy1_not_S : y₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hy1u, (G.ne_of_adj hu1y1).symm, hy1u2, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hy2_not_S : y₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hy2u, hy2u1, (G.ne_of_adj hu2y2).symm, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
      fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = yu ∧ s = zu) ∨ (r = u₁ ∧ s = y₁) ∨ (r = u₂ ∧ s = y₂) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrYu | hrY1 | hrY2
    · rcases hall_u s hsr.symm with rfl | rfl | rfl | hsYu
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (hYu_subS hsYu))
    · rcases hall_u1 s hsr.symm with rfl | rfl | rfl | hsY1
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact False.elim (hsS (hY1_subS hsY1))
    · rcases hall_u2 s hsr.symm with rfl | rfl | rfl | hsY2
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact False.elim (hsS (hY2_subS hsY2))
    · rcases hall_xu s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_yu s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 hsr.symm
        (mem_leafNbrs.mp hrYu).1.symm
      exact False.elim (hsS (by rw [this]; exact huS))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hsr.symm
        (mem_leafNbrs.mp hrY1).1.symm
      exact False.elim (hsS (by rw [this]; simp [S]))
    · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hsr.symm
        (mem_leafNbrs.mp hrY2).1.symm
      exact False.elim (hsS (by rw [this]; simp [S]))
  -- 情形 A 绝无孤立外部点（仅 3 条跨越边且 `4 ≤ d(zu)`）
  have hno_iso : ∀ s ∉ S, (∃ r ∈ S, G.Adj s r) → ∃ t ∉ S, G.Adj s t := by
    intro s hsS ⟨r₀, hr0S, hsr0⟩
    by_contra hiso; push Not at hiso
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ hr0S hsr0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    by_cases hyu : G.Adj s yu
    · have hds4 : 4 ≤ G.degree s := by
        rcases hS_out s hsS yu (by simp [S]) hyu with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hdzu
        · exact False.elim (by rw [h] at hdyu; omega)
        · exact False.elim (by rw [h] at hdyu; omega)
      have hsub : G.neighborFinset s ⊆ {yu, u₁, u₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hiso r h hr
        rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      have hc := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
      have := card_triple_le yu u₁ u₂; omega
    · have hsub2 : G.neighborFinset s ⊆ {u₁, u₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hiso r h hr
        rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact False.elim (hyu hr)
        · simp
        · simp
      have hc := Finset.card_le_card hsub2
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
      have := Finset.card_le_two (a := u₁) (b := u₂); omega
  -- 情形 A 染色：先定 `u₂` 使 `y₂` 成为唯一 PCF 色，再定 `u₁`，最后由 `t20_fun_color_extension` 封口！
  rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm⟩
  let C₂ : Finset ℕ := L u₂ \ {adm.φ y₂, adm.φs y₂}
  have hC2 : Y₂.card + 1 ≤ C₂.card := by
    dsimp only [C₂]; have := card_sdiff_ge (L u₂) {adm.φ y₂, adm.φs y₂}
    have := Finset.card_le_two (a := adm.φ y₂) (b := adm.φs y₂); omega
  rcases exists_color_leaves_avoid (β := adm.φ y₂) hY2_L2 hC2 with ⟨α₂, hα2C, haY2_ex⟩
  let aY₂ : V → ℕ := fun r => if hr : r ∈ Y₂ then (haY2_ex r hr).choose else 0
  have haY₂ : ∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂ ∧ aY₂ r ≠ adm.φ y₂ := fun r hr => by
    simp only [aY₂, hr, dite_true]; exact (haY2_ex r hr).choose_spec
  let Z₃ : Finset ℕ := L v₃ \ {α₂, adm.φ y₂}
  have hZ3 : 2 ≤ Z₃.card := by
    dsimp only [Z₃]; have := card_sdiff_ge (L v₃) {α₂, adm.φ y₂}
    have := Finset.card_le_two (a := α₂) (b := adm.φ y₂); omega
  have hu1_ext : ∀ α : ℕ, ∃ α₁ ∈ L u₁ \ {adm.φ y₁, adm.φs y₁, α},
      ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₃ α₂ α₁,
      ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
      ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
        ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 := by
    intro α
    have hC1 : Y₁.card + 1 ≤ (L u₁ \ {adm.φ y₁, adm.φs y₁, α}).card := by
      have := card_sdiff_ge (L u₁) {adm.φ y₁, adm.φs y₁, α}
      have := card_triple_le (adm.φ y₁) (adm.φs y₁) α; omega
    exact t3_fixed_color_extension hY1_pos hY1_L2 hLv1 hLv2 hZ3 hC1
  let f₁ : ℕ → ℕ := fun α => (hu1_ext α).choose
  have hcyu_ex : ∀ α : ℕ, (L yu \ {adm.φ zu, adm.φs zu, α}).Nonempty := fun α => by
    rw [← Finset.card_pos]
    have := card_sdiff_ge (L yu) {adm.φ zu, adm.φs zu, α}
    have := card_triple_le (adm.φ zu) (adm.φs zu) α; omega
  let cFun : ℕ → ℕ := fun α => (hcyu_ex α).choose
  have hcFun_spec : ∀ α, cFun α ∈ L yu ∧ cFun α ≠ adm.φ zu ∧ cFun α ≠ adm.φs zu ∧ cFun α ≠ α := by
    intro α
    have h := (hcyu_ex α).choose_spec
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  let C_u : Finset ℕ := L u \ {α₂, adm.φ y₂}
  have hCu : Yu.card + 2 ≤ C_u.card := by
    dsimp only [C_u]; have := card_sdiff_ge (L u) {α₂, adm.φ y₂}
    have := Finset.card_le_two (a := α₂) (b := adm.φ y₂); omega
  rcases t20_fun_color_extension (L := L) (Y := Yu) (Lv := L xu) (C_u := C_u)
    cFun f₁ (fun _ => α₂) (φz := adm.φ zu) hYu_pos hYu_L2 hLxu hCu with
    ⟨α, hαC, cxu, hcxu, aYu, haYu, γu, hγu⟩
  let α₁ : ℕ := f₁ α
  have hα1_spec := (hu1_ext α).choose_spec
  change α₁ ∈ L u₁ \ {adm.φ y₁, adm.φs y₁, α} ∧
      ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₃ α₂ α₁,
      ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
      ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
        ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 at hα1_spec
  rcases hα1_spec with ⟨hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
  rcases unpack_threeThreadGoodCols hc₁ with
    ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2α2, c₃, hc3Z, hc3c2, hc3c1⟩
  let cyu : ℕ := cFun α
  have hcyu := hcFun_spec α
  simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
  simp only [Z₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
  simp only [C_u, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1C hcxu
  let ψ : V → ℕ := fun r =>
    if r = u then α
    else if r = u₁ then α₁
    else if r = u₂ then α₂
    else if r = xu then cxu
    else if r = yu then cyu
    else if r = v₁ then c₁
    else if r = v₂ then c₂
    else if r = v₃ then c₃
    else if r ∈ Yu then aYu r
    else if r ∈ Y₁ then aY₁ r
    else if r ∈ Y₂ then aY₂ r
    else adm.φ r
  have hψ_u : ψ u = α := by simp [ψ]
  have hψ_u1 : ψ u₁ = α₁ := by simp [ψ, huu1.symm]
  have hψ_u2 : ψ u₂ = α₂ := by simp [ψ, huu2.symm, h12.symm]
  have hψ_xu : ψ xu = cxu := by
    simp [ψ, (show xu ≠ u by intro h; subst h; omega),
      (show xu ≠ u₁ by intro h; subst h; omega), (show xu ≠ u₂ by intro h; subst h; omega)]
  have hψ_yu : ψ yu = cyu := by
    simp [ψ, (show yu ≠ u by intro h; subst h; omega),
      (show yu ≠ u₁ by intro h; subst h; omega), (show yu ≠ u₂ by intro h; subst h; omega),
      (G.ne_of_adj hxuyu).symm]
  have hψ_v1 : ψ v₁ = c₁ := by
    simp [ψ, (show v₁ ≠ u by intro h; subst h; omega),
      (show v₁ ≠ u₁ by intro h; subst h; omega), (show v₁ ≠ u₂ by intro h; subst h; omega),
      (hx_ne_v xu (by simp) v₁ (by simp)).symm, (hx_ne_v yu (by simp) v₁ (by simp)).symm]
  have hψ_v2 : ψ v₂ = c₂ := by
    simp [ψ, (show v₂ ≠ u by intro h; subst h; omega),
      (show v₂ ≠ u₁ by intro h; subst h; omega), (show v₂ ≠ u₂ by intro h; subst h; omega),
      (hx_ne_v xu (by simp) v₂ (by simp)).symm, (hx_ne_v yu (by simp) v₂ (by simp)).symm,
      (G.ne_of_adj hv12).symm]
  have hψ_v3 : ψ v₃ = c₃ := by
    simp [ψ, (show v₃ ≠ u by intro h; subst h; omega),
      (show v₃ ≠ u₁ by intro h; subst h; omega), (show v₃ ≠ u₂ by intro h; subst h; omega),
      (hx_ne_v xu (by simp) v₃ (by simp)).symm, (hx_ne_v yu (by simp) v₃ (by simp)).symm,
      hv31, (G.ne_of_adj hv23).symm]
  have hψ_Yu : ∀ r ∈ Yu, ψ r = aYu r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    simp [ψ, hr, (show r ≠ u by intro h; subst h; omega),
      (show r ≠ u₁ by intro h; subst h; omega), (show r ≠ u₂ by intro h; subst h; omega),
      (show r ≠ xu by intro h; subst h; omega), (show r ≠ yu by intro h; subst h; omega),
      (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
      (show r ≠ v₃ by intro h; subst h; omega)]
  have hψ_Y1 : ∀ r ∈ Y₁, ψ r = aY₁ r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    have hnu : r ∉ Yu := Finset.disjoint_right.mp hYu1_disj hr
    simp [ψ, hr, hnu, (show r ≠ u by intro h; subst h; omega),
      (show r ≠ u₁ by intro h; subst h; omega), (show r ≠ u₂ by intro h; subst h; omega),
      (show r ≠ xu by intro h; subst h; omega), (show r ≠ yu by intro h; subst h; omega),
      (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
      (show r ≠ v₃ by intro h; subst h; omega)]
  have hψ_Y2 : ∀ r ∈ Y₂, ψ r = aY₂ r := fun r hr => by
    have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
    have hnu : r ∉ Yu := Finset.disjoint_right.mp hYu2_disj hr
    have hn1 : r ∉ Y₁ := Finset.disjoint_right.mp hY12_disj hr
    simp [ψ, hr, hnu, hn1, (show r ≠ u by intro h; subst h; omega),
      (show r ≠ u₁ by intro h; subst h; omega), (show r ≠ u₂ by intro h; subst h; omega),
      (show r ≠ xu by intro h; subst h; omega), (show r ≠ yu by intro h; subst h; omega),
      (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
      (show r ≠ v₃ by intro h; subst h; omega)]
  have hagree : ∀ x, x ∉ S → ψ x = adm.φ x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hx
    rcases hx with ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11'⟩
    simp [ψ, h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11']
  have hprop_S : ∀ r ∈ S, ∀ t, G.Adj r t → ψ r ≠ ψ t := by
    intro r hrS t hrt
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrYu | hrY1 | hrY2
    · rcases hall_u t hrt with ht | ht | ht | htYu
      · rw [ht, hψ_u, hψ_xu]; exact Ne.symm hcxu.2.1
      · rw [ht, hψ_u, hψ_u1]; exact Ne.symm hα1C.2.2.2
      · rw [ht, hψ_u, hψ_u2]; exact hαC.2.1
      · rw [hψ_u, hψ_Yu t htYu]; exact Ne.symm (haYu t htYu).2
    · rcases hall_u1 t hrt with ht | ht | ht | htY1
      · rw [ht, hψ_u1, hψ_v1]; exact Ne.symm hc1α1
      · rw [ht, hψ_u1, hψ_u]; exact hα1C.2.2.2
      · rw [ht, hψ_u1, hagree y₁ hy1_not_S]; exact hα1C.2.1
      · rw [hψ_u1, hψ_Y1 t htY1]; exact Ne.symm (haY₁ t htY1).2
    · rcases hall_u2 t hrt with ht | ht | ht | htY2
      · rw [ht, hψ_u2, hψ_v3]; exact Ne.symm hc3Z.2.1
      · rw [ht, hψ_u2, hψ_u]; exact Ne.symm hαC.2.1
      · rw [ht, hψ_u2, hagree y₂ hy2_not_S]; exact hα2C.2.1
      · rw [hψ_u2, hψ_Y2 t htY2]; exact Ne.symm (haY₂ t htY2).2.1
    · rcases hall_xu t hrt with ht | ht
      · rw [ht, hψ_xu, hψ_u]; exact hcxu.2.1
      · rw [ht, hψ_xu, hψ_yu]; exact hcxu.2.2.1
    · rcases hall_yu t hrt with ht | ht
      · rw [ht, hψ_yu, hψ_xu]; exact Ne.symm hcxu.2.2.1
      · rw [ht, hψ_yu, hagree zu hzu_not_S]; exact hcyu.2.1
    · rcases hall_v1 t hrt with ht | ht
      · rw [ht, hψ_v1, hψ_u1]; exact hc1α1
      · rw [ht, hψ_v1, hψ_v2]; exact Ne.symm hc2c1
    · rcases hall_v2 t hrt with ht | ht
      · rw [ht, hψ_v2, hψ_v1]; exact hc2c1
      · rw [ht, hψ_v2, hψ_v3]; exact Ne.symm hc3c2
    · rcases hall_v3 t hrt with ht | ht
      · rw [ht, hψ_v3, hψ_v2]; exact hc3c2
      · rw [ht, hψ_v3, hψ_u2]; exact hc3Z.2.1
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 hrt
        (mem_leafNbrs.mp hrYu).1.symm
      rw [ht, hψ_Yu r hrYu, hψ_u]; exact (haYu r hrYu).2
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hrt
        (mem_leafNbrs.mp hrY1).1.symm
      rw [ht, hψ_Y1 r hrY1, hψ_u1]; exact (haY₁ r hrY1).2
    · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hrt
        (mem_leafNbrs.mp hrY2).1.symm
      rw [ht, hψ_Y2 r hrY2, hψ_u2]; exact (haY₂ r hrY2).2.1
  apply adm.contradiction hm ψ hagree
  · intro r hrS
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrYu | hrY1 | hrY2
    · rw [hψ_u]; exact hαC.1
    · rw [hψ_u1]; exact hα1C.1
    · rw [hψ_u2]; exact hα2C.1
    · rw [hψ_xu]; exact hcxu.1
    · rw [hψ_yu]; exact hcyu.1
    · rw [hψ_v1]; exact hc1L
    · rw [hψ_v2]; exact hc2L
    · rw [hψ_v3]; exact hc3Z.1
    · rw [hψ_Yu r hrYu]; exact (haYu r hrYu).1
    · rw [hψ_Y1 r hrY1]; exact (haY₁ r hrY1).1
    · rw [hψ_Y2 r hrY2]; exact (haY₂ r hrY2).1
  · intro a b hab hor
    rcases hor with ha | hb
    · exact hprop_S a ha b hab
    · exact (hprop_S b hb a hab.symm).symm
  · intro s hsS _ r hrS hsr
    rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψ_yu]; exact hcyu.2.2.1
    · rw [hψ_u1]; exact hα1C.2.2.1
    · rw [hψ_u2]; exact hα2C.2.2
  · intro s hsS hiso ⟨r, hsr⟩
    have hrS : r ∈ S := by by_contra h; exact hiso r h hsr
    rcases hno_iso s hsS ⟨r, hrS, hsr⟩ with ⟨t, htS, hst⟩
    exact False.elim (hiso t htS hst)
  · intro r hrS _
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrYu | hrY1 | hrY2
    · apply pcf_from_leaf_and_three (γ := γu) huxu h1 h2 (fun h => by subst h; omega)
        (fun h => by subst h; omega) h12 (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Yu hall_u
      rw [hψ_xu, hψ_u1, hψ_u2]; exact hγu
    · apply pcf_from_leaf_and_three (γ := γ₁) huv₁ hu1y1 h1.symm (fun h => by subst h; omega)
        (fun h => by subst h; omega) hy1u (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
        (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y1
        (fun t ht => by
          rcases hall_u1 t ht with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h)))
      rw [hψ_v1, hagree y₁ hy1_not_S, hψ_u]; exact hγ₁
    · refine ⟨y₂, hu2y2, fun t ht hψt => ?_⟩
      rw [hagree y₂ hy2_not_S] at hψt
      rcases hall_u2 t ht with rfl | rfl | rfl | htY2
      · exact False.elim (hc3Z.2.2 (hψ_v3 ▸ hψt))
      · exact False.elim (hαC.2.2 (hψ_u ▸ hψt))
      · rfl
      · exact False.elim ((haY₂ t htY2).2.2 (hψ_Y2 t htY2 ▸ hψt))
    · exact pcf_at_of_two_distinct_neighbors hdxu huxu.symm hxuyu hyuu.symm
        (by rw [hψ_u, hψ_yu]; exact Ne.symm hcyu.2.2.2)
    · exact pcf_at_of_two_distinct_neighbors hdyu hxuyu.symm hyuzu hzuxu.symm
        (by rw [hψ_xu, hagree zu hzu_not_S]; exact hcxu.2.2.2)
    · exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
        (by rw [hψ_u1, hψ_v2]; exact Ne.symm hc2α1)
    · exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
        (by rw [hψ_v1, hψ_v3]; exact Ne.symm hc3c1)
    · exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
        (by rw [hψ_v2, hψ_u2]; exact hc2α2)
    · exact ⟨u, (mem_leafNbrs.mp hrYu).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 ht (mem_leafNbrs.mp hrYu).1.symm⟩
    · exact ⟨u₁, (mem_leafNbrs.mp hrY1).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 ht (mem_leafNbrs.mp hrY1).1.symm⟩
    · exact ⟨u₂, (mem_leafNbrs.mp hrY2).1.symm, fun t ht _ =>
        unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 ht (mem_leafNbrs.mp hrY2).1.symm⟩

/-- 引理 E4：在 `9 * p ≤ 22 * q` 下，`T20` 顶点不能同时与两个不同的 `T3` 顶点相邻！ -/
lemma no_T3_T20_T3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u u₁ u₂ : V}
    (hu : IsT20 G u) (hu1 : IsT3 G u₁) (hu2 : IsT3 G u₂)
    (h1 : G.Adj u u₁) (h2 : G.Adj u u₂) (h12 : u₁ ≠ u₂) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have huu1 : u ≠ u₁ := G.ne_of_adj h1
  have huu2 : u ≠ u₂ := G.ne_of_adj h2
  -- 拆解 `u` (`IsT20`)
  have hst := isT20_structure hm hpq25 hu
  have hdu : 4 ≤ G.degree u := hst.1
  rcases hu.2.1 with ⟨xu, hxu_mem⟩
  rcases twoThreadNbr_other_endpoint hm (by omega) hxu_mem with
    ⟨yu, zu, huxu, hdxu, hxuyu, hyuu, hdyu, hyuzu, hzuxu, huzu, hdzu3, _, haxu, hayu⟩
  have hdzu : 4 ≤ G.degree zu := by
    have hyulong : yu ∈ longThreadNbrs G zu := by
      unfold longThreadNbrs degTwoNbrs
      rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hyuzu.symm, hdyu⟩, hyuzu.symm, hdyu, xu, hxuyu.symm, hzuxu.symm, hdxu⟩
    exact deg_ge_four_of_longThreadNbr hm hdzu3 hyulong
  rcases exists_other_neighbor_of_deg_two hdxu huxu.symm with ⟨txu, _, _, hall_xu'⟩
  have hall_xu : ∀ r, G.Adj xu r → r = u ∨ r = yu := fun r hr => by
    rcases hall_xu' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_xu' yu hxuyu).resolve_left hyuu).symm)
  rcases exists_other_neighbor_of_deg_two hdyu hxuyu.symm with ⟨tyu, _, _, hall_yu'⟩
  have hall_yu : ∀ r, G.Adj yu r → r = xu ∨ r = zu := fun r hr => by
    rcases hall_yu' r hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h.trans ((hall_yu' zu hyuzu).resolve_left hzuxu).symm)
  -- 拆解 `u₁`, `u₂` (`IsT3`)
  rcases isT3_unpack hm hpq25 hu1 with
    ⟨v₁, v₂, v₃, z₁, x₁, y₁', huv₁, hdv₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, hdz1,
      hz1u1, hx₁, hy₁', hxy₁, hcore1, hY1_pos, hY1_card, hall_u1', hall_v1, hall_v2, hall_v3⟩
  rcases isT3_unpack hm hpq25 hu2 with
    ⟨w₁, w₂, w₃, z₂, x₂, y₂', huw₁, hdw₁, hw12, hw2u2, hdw₂, hw23, hw31, hdw₃, hw3z2, hzw2, hdz2,
      hz2u2, hx₂, hy₂', hxy₂, hcore2, hY2_pos, hY2_card, hall_u2', hall_w1, hall_w2, hall_w3⟩
  have hst1 := isT3_structure hm hpq25 hu1
  have hst2 := isT3_structure hm hpq25 hu2
  have hdu1 : 4 ≤ G.degree u₁ := hst1.1
  have hdu2 : 4 ≤ G.degree u₂ := hst2.1
  let Yu := leafNbrs G u
  let Y₁ := leafNbrs G u₁
  let Y₂ := leafNbrs G u₂
  have hYu_card : Yu.card = G.degree u - 3 := by
    have := coreDeg_add_leafNbrs hm u; have := hu.1; dsimp only [Yu]; omega
  have hYu_pos : 1 ≤ Yu.card := by omega
  -- `u` 的全部核心邻点为 `{xu, u₁, u₂}`
  have hcore_u : coreNbrs G u = {xu, u₁, u₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huxu, by omega⟩
      · exact mem_coreNbrs.mpr ⟨h1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨h2, by omega⟩
    · rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩),
          Finset.card_pair h12]
      have := hu.1; unfold coreDeg at this; omega
  have hall_u : ∀ r, G.Adj u r → r = xu ∨ r = u₁ ∨ r = u₂ ∨ r ∈ Yu := by
    intro r hur
    have hr1 := degree_ge_one hm r
    by_cases hdr : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, hdr⟩)))
    · have hrc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_u] at hrc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrc
      rcases hrc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  -- 确定 `u₁`、`u₂` 各自除 `u` 之外的另一好邻点 `y₁, y₂`
  have hu_core1 : u ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨h1.symm, by omega⟩
  rw [hcore1] at hu_core1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_core1
  have hex_y1 : ∃ y₁ : V, y₁ ∈ goodNbrs G u₁ ∧ y₁ ≠ u ∧
      ∀ r, G.Adj u₁ r → r = v₁ ∨ r = u ∨ r = y₁ ∨ r ∈ Y₁ := by
    rcases hu_core1 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu; omega)
    · exact ⟨y₁', hy₁', hxy₁.symm, hall_u1'⟩
    · exact ⟨x₁, hx₁, hxy₁, fun r hr => by
        rcases hall_u1' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y1 with ⟨y₁, hy1_good, hy1u, hall_u1⟩
  have hu1y1 : G.Adj u₁ y₁ := (mem_goodNbrs.mp hy1_good).1
  have hdy1 : 3 ≤ G.degree y₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy1_good).2
  have hu_core2 : u ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨h2.symm, by omega⟩
  rw [hcore2] at hu_core2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_core2
  have hex_y2 : ∃ y₂ : V, y₂ ∈ goodNbrs G u₂ ∧ y₂ ≠ u ∧
      ∀ r, G.Adj u₂ r → r = w₁ ∨ r = u ∨ r = y₂ ∨ r ∈ Y₂ := by
    rcases hu_core2 with h | rfl | rfl
    · exact False.elim (by rw [h] at hdu; omega)
    · exact ⟨y₂', hy₂', hxy₂.symm, hall_u2'⟩
    · exact ⟨x₂, hx₂, hxy₂, fun r hr => by
        rcases hall_u2' r hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))⟩
  rcases hex_y2 with ⟨y₂, hy2_good, hy2u, hall_u2⟩
  have hu2y2 : G.Adj u₂ y₂ := (mem_goodNbrs.mp hy2_good).1
  have hdy2 : 3 ≤ G.degree y₂ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy2_good).2
  -- 由引理 E1，`¬ G.Adj u₁ u₂`，并排除所有跨顶点重合
  have hnadj12 : ¬ G.Adj u₁ u₂ := fun h => no_T3_adj_T3 hm hpq hu1 hu2 h
  have hy1u2 : y₁ ≠ u₂ := fun h => hnadj12 (h ▸ hu1y1)
  have hy2u1 : y₂ ≠ u₁ := fun h => hnadj12 (h ▸ hu2y2).symm
  have hzuu1 : zu ≠ u₁ := by
    intro h; subst zu
    have hyum : yu ∈ twoThreadNbrs G u₁ := by
      rw [mem_twoThreadNbrs]
      exact ⟨hyuzu.symm, hdyu, xu, u, hxuyu.symm, hzuxu.symm, hdxu, huxu.symm, hyuu.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨yu, hyum⟩; omega
  have hzuu2 : zu ≠ u₂ := by
    intro h; subst zu
    have hyum : yu ∈ twoThreadNbrs G u₂ := by
      rw [mem_twoThreadNbrs]
      exact ⟨hyuzu.symm, hdyu, xu, u, hxuyu.symm, hzuxu.symm, hdxu, huxu.symm, hyuu.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨yu, hyum⟩; omega
  have hz1u : z₁ ≠ u := by
    intro h; subst z₁
    have hv3m : v₃ ∈ threeThreadNbrs G u := by
      rw [mem_threeThreadNbrs]
      exact ⟨hv3z1.symm, hdv₃, v₂, v₁, u₁, hv23.symm, hzv2.symm, hdv₂, hv12.symm, hv31.symm,
        hdv₁, huv₁.symm, hv2u1.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨v₃, hv3m⟩; omega
  have hz2u : z₂ ≠ u := by
    intro h; subst z₂
    have hw3m : w₃ ∈ threeThreadNbrs G u := by
      rw [mem_threeThreadNbrs]
      exact ⟨hw3z2.symm, hdw₃, w₂, w₁, u₂, hw23.symm, hzw2.symm, hdw₂, hw12.symm, hw31.symm,
        hdw₁, huw₁.symm, hw2u2.symm, by omega⟩
    have := Finset.card_pos.mpr ⟨w₃, hw3m⟩; omega
  -- 线串不交性与叶集两两不交
  have ha_v := threeThread_anchors_eq hm (by omega) (by omega) hz1u1.symm
    hdv₁ hdv₂ hdv₃ huv₁ hv12 hv2u1 hv23 hv31 hv3z1 hzv2
  have ha_w := threeThread_anchors_eq hm (by omega) (by omega) hz2u2.symm
    hdw₁ hdw₂ hdw₃ huw₁ hw12 hw2u2 hw23 hw31 hw3z2 hzw2
  have hx_ne_v : ∀ a ∈ ({xu, yu} : Finset V), ∀ b ∈ ({v₁, v₂, v₃} : Finset V), a ≠ b := by
    intro a ha b hb heq; subst heq
    have ha_anc : threadAnchors G a = {u, zu} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact haxu
      · exact hayu
    have hu_in : u ∈ threadAnchors G a := by rw [ha_anc]; simp
    have hb_anc : threadAnchors G a = {u₁, z₁} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ha_v.1
      · exact ha_v.2.1
      · exact ha_v.2.2
    rw [hb_anc] at hu_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in
    exact hu_in.elim huu1 hz1u.symm
  have hx_ne_w : ∀ a ∈ ({xu, yu} : Finset V), ∀ b ∈ ({w₁, w₂, w₃} : Finset V), a ≠ b := by
    intro a ha b hb heq; subst heq
    have ha_anc : threadAnchors G a = {u, zu} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact haxu
      · exact hayu
    have hu_in : u ∈ threadAnchors G a := by rw [ha_anc]; simp
    have hb_anc : threadAnchors G a = {u₂, z₂} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ha_w.1
      · exact ha_w.2.1
      · exact ha_w.2.2
    rw [hb_anc] at hu_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in
    exact hu_in.elim huu2 hz2u.symm
  have hYu1_disj : Disjoint Yu Y₁ := by
    rw [Finset.disjoint_left]; intro r hru hr1
    exact huu1 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hru).2
      (mem_leafNbrs.mp hru).1.symm (mem_leafNbrs.mp hr1).1.symm)
  have hYu2_disj : Disjoint Yu Y₂ := by
    rw [Finset.disjoint_left]; intro r hru hr2
    exact huu2 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hru).2
      (mem_leafNbrs.mp hru).1.symm (mem_leafNbrs.mp hr2).1.symm)
  have hY12_disj : Disjoint Y₁ Y₂ := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    exact h12 (unique_neighbor_of_deg_one (mem_leafNbrs.mp hr1).2
      (mem_leafNbrs.mp hr1).1.symm (mem_leafNbrs.mp hr2).1.symm)
  -- 列表基数预备
  have hLu : (L u).card = Yu.card + 4 := by
    rw [hYu_card, hm.list_card u]; unfold kappa; split_ifs <;> omega
  have hLu1 : (L u₁).card = Y₁.card + 4 := by
    dsimp only [Y₁]; rw [hm.list_card u₁]; unfold kappa; split_ifs <;> omega
  have hLu2 : (L u₂).card = Y₂.card + 4 := by
    dsimp only [Y₂]; rw [hm.list_card u₂]; unfold kappa; split_ifs <;> omega
  have hLxu : (L xu).card = 4 := by rw [hm.list_card xu]; simp [kappa, hdxu]
  have hLyu : (L yu).card = 4 := by rw [hm.list_card yu]; simp [kappa, hdyu]
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw₁]
  have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw₂]
  have hLw3 : (L w₃).card = 4 := by rw [hm.list_card w₃]; simp [kappa, hdw₃]
  have hYu_L2 : ∀ r ∈ Yu, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY1_L2 : ∀ r ∈ Y₁, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY2_L2 : ∀ r ∈ Y₂, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  -- 分两种几何情形：`z₁ = u₂`（共享 `3`-线串）与 `z₁ ≠ u₂`（两条不交 `3`-线串）
  by_cases hshared : z₁ = u₂
  · exact no_T3_T20_T3_shared hm hpq hu hu1 hu2 h1 h2 h12 (fun v hv => by
      have hv1m : v₁ ∈ threeThreadNbrs G u₁ := by
        rw [mem_threeThreadNbrs]
        exact ⟨huv₁, hdv₁, v₂, v₃, z₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, by omega⟩
      have heq : v = v₁ := Finset.card_le_one.mp (by rw [hst1.2.1]) v hv v₁ hv1m
      rw [heq, ha_v.1, hshared]; simp)
  · -- 情形 B：`z₁ ≠ u₂`，两条 `3`-线串完全不交！
    have hz2u1 : z₂ ≠ u₁ := by
      intro h; subst z₂
      have hw3_mem : w₃ ∈ threeThreadNbrs G u₁ := by
        rw [mem_threeThreadNbrs]
        exact ⟨hw3z2.symm, hdw₃, w₂, w₁, u₂, hw23.symm, hzw2.symm, hdw₂, hw12.symm, hw31.symm,
          hdw₁, huw₁.symm, hw2u2.symm, by omega⟩
      have hv1_mem : v₁ ∈ threeThreadNbrs G u₁ := by
        rw [mem_threeThreadNbrs]
        exact ⟨huv₁, hdv₁, v₂, v₃, z₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, by omega⟩
      have hcard1 := hst1.2.1
      have hw3_eq : w₃ = v₁ := Finset.card_le_one.mp (by rw [hcard1]) w₃ hw3_mem v₁ hv1_mem
      have h1_a := ha_v.1
      have h2_a := ha_w.2.2
      rw [hw3_eq] at h2_a
      have hpair : ({u₁, z₁} : Finset V) = {u₂, u₁} := h1_a.symm.trans h2_a
      have hz_in : z₁ ∈ ({u₂, u₁} : Finset V) := by rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz_in
      exact hz_in.elim hshared hz1u1
    have hv_ne_w : ∀ a ∈ ({v₁, v₂, v₃} : Finset V), ∀ b ∈ ({w₁, w₂, w₃} : Finset V), a ≠ b := by
      intro a ha b hb heq; subst heq
      have h1_a : threadAnchors G a = {u₁, z₁} := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact ha_v.1
        · exact ha_v.2.1
        · exact ha_v.2.2
      have h2_a : threadAnchors G a = {u₂, z₂} := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact ha_w.1
        · exact ha_w.2.1
        · exact ha_w.2.2
      have hu1_in : u₁ ∈ ({u₂, z₂} : Finset V) := by rw [← h2_a, h1_a]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_in
      exact hu1_in.elim h12 hz2u1.symm
    let S : Finset V :=
      insert u (insert u₁ (insert u₂ (insert xu (insert yu
        (insert v₁ (insert v₂ (insert v₃ (insert w₁ (insert w₂ (insert w₃
          (Yu ∪ (Y₁ ∪ Y₂))))))))))))
    have huS : u ∈ S := Finset.mem_insert_self u _
    have hYu_subS : Yu ⊆ S := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl hr)))))))))))
    have hY1_subS : Y₁ ⊆ S := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))))))))))
    have hY2_subS : Y₂ ⊆ S := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))))))))
    have hzu_not_S : zu ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨huzu.symm, hzuu1, hzuu2, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hy1_not_S : y₁ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨hy1u, (G.ne_of_adj hu1y1).symm, hy1u2, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hz1_not_S : z₁ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨hz1u, hz1u1, hshared, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hy2_not_S : y₂ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨hy2u, hy2u1, (G.ne_of_adj hu2y2).symm, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hz2_not_S : z₂ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨hz2u, hz2u1, hz2u2, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
        (r = yu ∧ s = zu) ∨ (r = u₁ ∧ s = y₁) ∨ (r = v₃ ∧ s = z₁) ∨
        (r = u₂ ∧ s = y₂) ∨ (r = w₃ ∧ s = z₂) := by
      intro s hsS r hrS hsr
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        hrYu | hrY1 | hrY2
      · rcases hall_u s hsr.symm with rfl | rfl | rfl | hsYu
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (hYu_subS hsYu))
      · rcases hall_u1 s hsr.symm with rfl | rfl | rfl | hsY1
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact False.elim (hsS (hY1_subS hsY1))
      · rcases hall_u2 s hsr.symm with rfl | rfl | rfl | hsY2
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        · exact False.elim (hsS (hY2_subS hsY2))
      · rcases hall_xu s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_yu s hsr.symm with rfl | rfl
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v3 s hsr.symm with rfl | rfl
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_w2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_w3 s hsr.symm with rfl | rfl
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 hsr.symm
          (mem_leafNbrs.mp hrYu).1.symm
        exact False.elim (hsS (by rw [this]; exact huS))
      · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hsr.symm
          (mem_leafNbrs.mp hrY1).1.symm
        exact False.elim (hsS (by rw [this]; simp [S]))
      · have := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hsr.symm
          (mem_leafNbrs.mp hrY2).1.symm
        exact False.elim (hsS (by rw [this]; simp [S]))
    -- 外部孤立点（若存在）必满足 `4 ≤ d(s)` 且全局唯一！
    have hiso_deg4 : ∀ s ∉ S, (∀ t ∉ S, ¬ G.Adj s t) → (∃ r ∈ S, G.Adj s r) →
        4 ≤ G.degree s := by
      intro s hsS hiso ⟨r₀, hr0S, hsr0⟩
      have hds3 : 3 ≤ G.degree s := by
        rcases hS_out s hsS r₀ hr0S hsr0 with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      by_cases hyu : G.Adj s yu
      · rcases hS_out s hsS yu (by simp [S]) hyu with
          ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hdzu
        · exact False.elim (by rw [h] at hdyu; omega)
        · exact False.elim (hx_ne_v yu (by simp) v₃ (by simp) h)
        · exact False.elim (by rw [h] at hdyu; omega)
        · exact False.elim (hx_ne_w yu (by simp) w₃ (by simp) h)
      · by_cases hv3 : G.Adj s v₃
        · rcases hS_out s hsS v₃ (by simp [S]) hv3 with
            ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact False.elim (hx_ne_v yu (by simp) v₃ (by simp) h.symm)
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact hdz1
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h)
        · by_cases hw3 : G.Adj s w₃
          · rcases hS_out s hsS w₃ (by simp [S]) hw3 with
              ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
            · exact False.elim (hx_ne_w yu (by simp) w₃ (by simp) h.symm)
            · exact False.elim (by rw [h] at hdw₃; omega)
            · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h.symm)
            · exact False.elim (by rw [h] at hdw₃; omega)
            · exact hdz2
          · have hsub2 : G.neighborFinset s ⊆ {u₁, u₂} := by
              intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
              have hrS : r ∈ S := by by_contra h; exact hiso r h hr
              rcases hS_out s hsS r hrS hr with
                ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
              · exact False.elim (hyu hr)
              · simp
              · exact False.elim (hv3 hr)
              · simp
              · exact False.elim (hw3 hr)
            have hc := Finset.card_le_card hsub2
            rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
            have := Finset.card_le_two (a := u₁) (b := u₂); omega
    have hiso_uniq : ∀ s₁ s₂, s₁ ∉ S → s₂ ∉ S →
        (∀ t ∉ S, ¬ G.Adj s₁ t) → (∀ t ∉ S, ¬ G.Adj s₂ t) →
        (∃ r ∈ S, G.Adj s₁ r) → (∃ r ∈ S, G.Adj s₂ r) → s₁ = s₂ := by
      intro s₁ s₂ hs1 hs2 hi1 hi2 hr1 hr2
      by_contra hne
      have hd1 := hiso_deg4 s₁ hs1 hi1 hr1
      have hd2 := hiso_deg4 s₂ hs2 hi2 hr2
      have hdisj : Disjoint (G.neighborFinset s₁) (G.neighborFinset s₂) := by
        rw [Finset.disjoint_left]; intro r h1m h2m
        rw [SimpleGraph.mem_neighborFinset] at h1m h2m
        have hrS : r ∈ S := by by_contra h; exact hi1 r h h1m
        rcases hS_out s₁ hs1 r hrS h1m with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hS_out s₂ hs2 r hrS h2m with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact hne rfl
          · exact False.elim (by rw [h] at hdyu; omega)
          · exact False.elim (hx_ne_v r (by simp) v₃ (by simp) h)
          · exact False.elim (by rw [h] at hdyu; omega)
          · exact False.elim (hx_ne_w r (by simp) w₃ (by simp) h)
        · rcases hS_out s₂ hs2 r hrS h2m with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact False.elim (by rw [h] at hdu1; omega)
          · exact hne rfl
          · exact False.elim (by rw [h] at hdu1; omega)
          · exact False.elim (h12 h)
          · exact False.elim (by rw [h] at hdu1; omega)
        · rcases hS_out s₂ hs2 r hrS h2m with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact False.elim (hx_ne_v yu (by simp) r (by simp) h.symm)
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact hne rfl
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact False.elim (hv_ne_w r (by simp) w₃ (by simp) h)
        · rcases hS_out s₂ hs2 r hrS h2m with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
          · exact False.elim (by rw [h] at hdu2; omega)
          · exact False.elim (h12 h.symm)
          · exact False.elim (by rw [h] at hdu2; omega)
          · exact hne rfl
          · exact False.elim (by rw [h] at hdu2; omega)
        · rcases hS_out s₂ hs2 r hrS h2m with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
          · exact False.elim (hx_ne_w yu (by simp) r (by simp) h.symm)
          · exact False.elim (by rw [h] at hdw₃; omega)
          · exact False.elim (hv_ne_w v₃ (by simp) r (by simp) h.symm)
          · exact False.elim (by rw [h] at hdw₃; omega)
          · exact hne rfl
      have hsub : G.neighborFinset s₁ ∪ G.neighborFinset s₂ ⊆ {yu, u₁, v₃, u₂, w₃} := by
        intro r hr; rw [Finset.mem_union, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset] at hr
        rcases hr with h1m | h2m
        · have hrS : r ∈ S := by by_contra h; exact hi1 r h h1m
          rcases hS_out s₁ hs1 r hrS h1m with
            ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
        · have hrS : r ∈ S := by by_contra h; exact hi2 r h h2m
          rcases hS_out s₂ hs2 r hrS h2m with
            ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree] at hcard
      have h5 : ({yu, u₁, v₃, u₂, w₃} : Finset V).card ≤ 5 := by
        have h4 := card_quad_le u₁ v₃ u₂ w₃
        have := Finset.card_insert_le yu ({u₁, v₃, u₂, w₃} : Finset V); omega
      omega
    -- 构造容许染色 `adm` 并提取情形 B 统一封口闭包 `hfinish_B`
    rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm⟩
    have hfinish_B :
        ∀ (α α₁ α₂ cxu cyu c₁ c₂ c₃ d₁ d₂ d₃ : ℕ) (aYu aY₁ aY₂ : V → ℕ),
          α ∈ L u → α₁ ∈ L u₁ → α₂ ∈ L u₂ → cxu ∈ L xu → cyu ∈ L yu →
          c₁ ∈ L v₁ → c₂ ∈ L v₂ → c₃ ∈ L v₃ → d₁ ∈ L w₁ → d₂ ∈ L w₂ → d₃ ∈ L w₃ →
          (∀ r ∈ Yu, aYu r ∈ L r ∧ aYu r ≠ α) →
          (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) →
          (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) →
          cxu ≠ α → cxu ≠ cyu → cxu ≠ adm.φ zu → cyu ≠ adm.φ zu → cyu ≠ α →
          α₁ ≠ α → α₁ ≠ adm.φ y₁ → c₁ ≠ α₁ → c₂ ≠ α₁ → c₂ ≠ c₁ → c₂ ≠ adm.φ z₁ →
          c₃ ≠ adm.φ z₁ → c₃ ≠ c₂ → c₃ ≠ c₁ →
          α₂ ≠ α → α₂ ≠ adm.φ y₂ → d₁ ≠ α₂ → d₂ ≠ α₂ → d₂ ≠ d₁ → d₂ ≠ adm.φ z₂ →
          d₃ ≠ adm.φ z₂ → d₃ ≠ d₂ → d₃ ≠ d₁ →
          (∃ γu, (Yu.filter (fun r => aYu r = γu)).card +
            ([cxu, α₁, α₂] : List ℕ).count γu = 1) →
          (∃ γ₁, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
            ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1) →
          (∃ γ₂, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
            ([d₁, adm.φ y₂, α] : List ℕ).count γ₂ = 1) →
          (∀ s ∉ S, (∃ t ∉ S, G.Adj s t) →
            (s = zu → cyu ≠ adm.φs s) ∧ (s = y₁ → α₁ ≠ adm.φs s) ∧
            (s = z₁ → c₃ ≠ adm.φs s) ∧ (s = y₂ → α₂ ≠ adm.φs s) ∧
            (s = z₂ → d₃ ≠ adm.φs s)) →
          (∀ s ∉ S, (∀ t ∉ S, ¬ G.Adj s t) → (∃ r ∈ S, G.Adj s r) →
            (G.Adj s yu ∧ (G.Adj s u₁ → α₁ ≠ cyu) ∧ (G.Adj s v₃ → c₃ ≠ cyu) ∧
              (G.Adj s u₂ → α₂ ≠ cyu) ∧ (G.Adj s w₃ → d₃ ≠ cyu)) ∨
            (G.Adj s u₁ ∧ ¬ G.Adj s yu ∧ c₃ ≠ α₁ ∧ α₂ ≠ α₁ ∧ d₃ ≠ α₁)) →
          False := by
      intro α α₁ α₂ cxu cyu c₁ c₂ c₃ d₁ d₂ d₃ aYu aY₁ aY₂
        hαL hα1L hα2L hcxuL hcyuL hc1L hc2L hc3L hd1L hd2L hd3L
        haYu haY₁ haY₂ hcxα hcxcy hcxz hcyz hcyα
        hα1α hα1y1 hc1α1 hc2α1 hc2c1 hc2z1 hc3z1 hc3c2 hc3c1
        hα2α hα2y2 hd1α2 hd2α2 hd2d1 hd2z2 hd3z2 hd3d2 hd3d1
        ⟨γu, hγu⟩ ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩ havoid_out hiso_out
      let ψ : V → ℕ := fun r =>
        if r = u then α
        else if r = u₁ then α₁
        else if r = u₂ then α₂
        else if r = xu then cxu
        else if r = yu then cyu
        else if r = v₁ then c₁
        else if r = v₂ then c₂
        else if r = v₃ then c₃
        else if r = w₁ then d₁
        else if r = w₂ then d₂
        else if r = w₃ then d₃
        else if r ∈ Yu then aYu r
        else if r ∈ Y₁ then aY₁ r
        else if r ∈ Y₂ then aY₂ r
        else adm.φ r
      have hψ_u : ψ u = α := by simp only [ψ, ite_true]
      have hψ_u1 : ψ u₁ = α₁ := by simp only [ψ, huu1.symm, ite_true, ite_false]
      have hψ_u2 : ψ u₂ = α₂ := by simp only [ψ, huu2.symm, h12.symm, ite_true, ite_false]
      have hψ_xu : ψ xu = cxu := by
        simp only [ψ, ne_of_deg2_ge4 hdxu hdu, ne_of_deg2_ge4 hdxu hdu1,
          ne_of_deg2_ge4 hdxu hdu2, ite_true, ite_false]
      have hψ_yu : ψ yu = cyu := by
        simp only [ψ, ne_of_deg2_ge4 hdyu hdu, ne_of_deg2_ge4 hdyu hdu1,
          ne_of_deg2_ge4 hdyu hdu2, (G.ne_of_adj hxuyu).symm, ite_true, ite_false]
      have hψ_v1 : ψ v₁ = c₁ := by
        simp only [ψ, ne_of_deg2_ge4 hdv₁ hdu, ne_of_deg2_ge4 hdv₁ hdu1,
          ne_of_deg2_ge4 hdv₁ hdu2, (hx_ne_v xu (by simp) v₁ (by simp)).symm,
          (hx_ne_v yu (by simp) v₁ (by simp)).symm, ite_true, ite_false]
      have hψ_v2 : ψ v₂ = c₂ := by
        simp only [ψ, ne_of_deg2_ge4 hdv₂ hdu, ne_of_deg2_ge4 hdv₂ hdu1,
          ne_of_deg2_ge4 hdv₂ hdu2, (hx_ne_v xu (by simp) v₂ (by simp)).symm,
          (hx_ne_v yu (by simp) v₂ (by simp)).symm, (G.ne_of_adj hv12).symm, ite_true, ite_false]
      have hψ_v3 : ψ v₃ = c₃ := by
        simp only [ψ, ne_of_deg2_ge4 hdv₃ hdu, ne_of_deg2_ge4 hdv₃ hdu1,
          ne_of_deg2_ge4 hdv₃ hdu2, (hx_ne_v xu (by simp) v₃ (by simp)).symm,
          (hx_ne_v yu (by simp) v₃ (by simp)).symm, hv31, (G.ne_of_adj hv23).symm,
          ite_true, ite_false]
      have hψ_w1 : ψ w₁ = d₁ := by
        simp only [ψ, ne_of_deg2_ge4 hdw₁ hdu, ne_of_deg2_ge4 hdw₁ hdu1,
          ne_of_deg2_ge4 hdw₁ hdu2, (hx_ne_w xu (by simp) w₁ (by simp)).symm,
          (hx_ne_w yu (by simp) w₁ (by simp)).symm, (hv_ne_w v₁ (by simp) w₁ (by simp)).symm,
          (hv_ne_w v₂ (by simp) w₁ (by simp)).symm, (hv_ne_w v₃ (by simp) w₁ (by simp)).symm,
          ite_true, ite_false]
      have hψ_w2 : ψ w₂ = d₂ := by
        simp only [ψ, ne_of_deg2_ge4 hdw₂ hdu, ne_of_deg2_ge4 hdw₂ hdu1,
          ne_of_deg2_ge4 hdw₂ hdu2, (hx_ne_w xu (by simp) w₂ (by simp)).symm,
          (hx_ne_w yu (by simp) w₂ (by simp)).symm, (hv_ne_w v₁ (by simp) w₂ (by simp)).symm,
          (hv_ne_w v₂ (by simp) w₂ (by simp)).symm, (hv_ne_w v₃ (by simp) w₂ (by simp)).symm,
          (G.ne_of_adj hw12).symm, ite_true, ite_false]
      have hψ_w3 : ψ w₃ = d₃ := by
        simp only [ψ, ne_of_deg2_ge4 hdw₃ hdu, ne_of_deg2_ge4 hdw₃ hdu1,
          ne_of_deg2_ge4 hdw₃ hdu2, (hx_ne_w xu (by simp) w₃ (by simp)).symm,
          (hx_ne_w yu (by simp) w₃ (by simp)).symm, (hv_ne_w v₁ (by simp) w₃ (by simp)).symm,
          (hv_ne_w v₂ (by simp) w₃ (by simp)).symm, (hv_ne_w v₃ (by simp) w₃ (by simp)).symm,
          hw31, (G.ne_of_adj hw23).symm, ite_true, ite_false]
      have hψ_Yu : ∀ r ∈ Yu, ψ r = aYu r := fun r hr => by
        have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
        simp only [ψ, hr, ne_of_deg1_ge4 hdr hdu, ne_of_deg1_ge4 hdr hdu1,
          ne_of_deg1_ge4 hdr hdu2, ne_of_deg1_eq2 hdr hdxu, ne_of_deg1_eq2 hdr hdyu,
          ne_of_deg1_eq2 hdr hdv₁, ne_of_deg1_eq2 hdr hdv₂, ne_of_deg1_eq2 hdr hdv₃,
          ne_of_deg1_eq2 hdr hdw₁, ne_of_deg1_eq2 hdr hdw₂, ne_of_deg1_eq2 hdr hdw₃,
          ite_true, ite_false]
      have hψ_Y1 : ∀ r ∈ Y₁, ψ r = aY₁ r := fun r hr => by
        have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
        have hnu : r ∉ Yu := Finset.disjoint_right.mp hYu1_disj hr
        simp only [ψ, hr, hnu, ne_of_deg1_ge4 hdr hdu, ne_of_deg1_ge4 hdr hdu1,
          ne_of_deg1_ge4 hdr hdu2, ne_of_deg1_eq2 hdr hdxu, ne_of_deg1_eq2 hdr hdyu,
          ne_of_deg1_eq2 hdr hdv₁, ne_of_deg1_eq2 hdr hdv₂, ne_of_deg1_eq2 hdr hdv₃,
          ne_of_deg1_eq2 hdr hdw₁, ne_of_deg1_eq2 hdr hdw₂, ne_of_deg1_eq2 hdr hdw₃,
          ite_true, ite_false]
      have hψ_Y2 : ∀ r ∈ Y₂, ψ r = aY₂ r := fun r hr => by
        have hdr : G.degree r = 1 := (mem_leafNbrs.mp hr).2
        have hnu : r ∉ Yu := Finset.disjoint_right.mp hYu2_disj hr
        have hn1 : r ∉ Y₁ := Finset.disjoint_right.mp hY12_disj hr
        simp only [ψ, hr, hnu, hn1, ne_of_deg1_ge4 hdr hdu, ne_of_deg1_ge4 hdr hdu1,
          ne_of_deg1_ge4 hdr hdu2, ne_of_deg1_eq2 hdr hdxu, ne_of_deg1_eq2 hdr hdyu,
          ne_of_deg1_eq2 hdr hdv₁, ne_of_deg1_eq2 hdr hdv₂, ne_of_deg1_eq2 hdr hdv₃,
          ne_of_deg1_eq2 hdr hdw₁, ne_of_deg1_eq2 hdr hdw₂, ne_of_deg1_eq2 hdr hdw₃,
          ite_true, ite_false]
      have hagree : ∀ x, x ∉ S → ψ x = adm.φ x := fun x hx => by
        simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hx
        rcases hx with ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩
        simp only [ψ, h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14',
          ite_false]
      have hprop_S : ∀ r ∈ S, ∀ t, G.Adj r t → ψ r ≠ ψ t := by
        intro r hrS t hrt
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr |
          hrYu | hrY1 | hrY2
        · rw [hr] at hrt ⊢
          rcases hall_u t hrt with ht | ht | ht | htYu
          · rw [ht, hψ_u, hψ_xu]; exact Ne.symm hcxα
          · rw [ht, hψ_u, hψ_u1]; exact Ne.symm hα1α
          · rw [ht, hψ_u, hψ_u2]; exact Ne.symm hα2α
          · rw [hψ_u, hψ_Yu t htYu]; exact Ne.symm (haYu t htYu).2
        · rw [hr] at hrt ⊢
          rcases hall_u1 t hrt with ht | ht | ht | htY1
          · rw [ht, hψ_u1, hψ_v1]; exact Ne.symm hc1α1
          · rw [ht, hψ_u1, hψ_u]; exact hα1α
          · rw [ht, hψ_u1, hagree y₁ hy1_not_S]; exact hα1y1
          · rw [hψ_u1, hψ_Y1 t htY1]; exact Ne.symm (haY₁ t htY1).2
        · rw [hr] at hrt ⊢
          rcases hall_u2 t hrt with ht | ht | ht | htY2
          · rw [ht, hψ_u2, hψ_w1]; exact Ne.symm hd1α2
          · rw [ht, hψ_u2, hψ_u]; exact hα2α
          · rw [ht, hψ_u2, hagree y₂ hy2_not_S]; exact hα2y2
          · rw [hψ_u2, hψ_Y2 t htY2]; exact Ne.symm (haY₂ t htY2).2
        · rw [hr] at hrt ⊢
          rcases hall_xu t hrt with ht | ht
          · rw [ht, hψ_xu, hψ_u]; exact hcxα
          · rw [ht, hψ_xu, hψ_yu]; exact hcxcy
        · rw [hr] at hrt ⊢
          rcases hall_yu t hrt with ht | ht
          · rw [ht, hψ_yu, hψ_xu]; exact Ne.symm hcxcy
          · rw [ht, hψ_yu, hagree zu hzu_not_S]; exact hcyz
        · rw [hr] at hrt ⊢
          rcases hall_v1 t hrt with ht | ht
          · rw [ht, hψ_v1, hψ_u1]; exact hc1α1
          · rw [ht, hψ_v1, hψ_v2]; exact Ne.symm hc2c1
        · rw [hr] at hrt ⊢
          rcases hall_v2 t hrt with ht | ht
          · rw [ht, hψ_v2, hψ_v1]; exact hc2c1
          · rw [ht, hψ_v2, hψ_v3]; exact Ne.symm hc3c2
        · rw [hr] at hrt ⊢
          rcases hall_v3 t hrt with ht | ht
          · rw [ht, hψ_v3, hψ_v2]; exact hc3c2
          · rw [ht, hψ_v3, hagree z₁ hz1_not_S]; exact hc3z1
        · rw [hr] at hrt ⊢
          rcases hall_w1 t hrt with ht | ht
          · rw [ht, hψ_w1, hψ_u2]; exact hd1α2
          · rw [ht, hψ_w1, hψ_w2]; exact Ne.symm hd2d1
        · rw [hr] at hrt ⊢
          rcases hall_w2 t hrt with ht | ht
          · rw [ht, hψ_w2, hψ_w1]; exact hd2d1
          · rw [ht, hψ_w2, hψ_w3]; exact Ne.symm hd3d2
        · rw [hr] at hrt ⊢
          rcases hall_w3 t hrt with ht | ht
          · rw [ht, hψ_w3, hψ_w2]; exact hd3d2
          · rw [ht, hψ_w3, hagree z₂ hz2_not_S]; exact hd3z2
        · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 hrt
            (mem_leafNbrs.mp hrYu).1.symm
          rw [ht, hψ_Yu r hrYu, hψ_u]; exact (haYu r hrYu).2
        · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 hrt
            (mem_leafNbrs.mp hrY1).1.symm
          rw [ht, hψ_Y1 r hrY1, hψ_u1]; exact (haY₁ r hrY1).2
        · have ht := unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 hrt
            (mem_leafNbrs.mp hrY2).1.symm
          rw [ht, hψ_Y2 r hrY2, hψ_u2]; exact (haY₂ r hrY2).2
      apply adm.contradiction hm ψ hagree
      · intro r hrS
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr |
          hrYu | hrY1 | hrY2
        · rw [hr, hψ_u]; exact hαL
        · rw [hr, hψ_u1]; exact hα1L
        · rw [hr, hψ_u2]; exact hα2L
        · rw [hr, hψ_xu]; exact hcxuL
        · rw [hr, hψ_yu]; exact hcyuL
        · rw [hr, hψ_v1]; exact hc1L
        · rw [hr, hψ_v2]; exact hc2L
        · rw [hr, hψ_v3]; exact hc3L
        · rw [hr, hψ_w1]; exact hd1L
        · rw [hr, hψ_w2]; exact hd2L
        · rw [hr, hψ_w3]; exact hd3L
        · rw [hψ_Yu r hrYu]; exact (haYu r hrYu).1
        · rw [hψ_Y1 r hrY1]; exact (haY₁ r hrY1).1
        · rw [hψ_Y2 r hrY2]; exact (haY₂ r hrY2).1
      · intro a b hab hor
        rcases hor with ha | hb
        · exact hprop_S a ha b hab
        · exact (hprop_S b hb a hab.symm).symm
      · intro s hsS hnoniso r hrS hsr
        have ha := havoid_out s hsS hnoniso
        rcases hS_out s hsS r hrS hsr with
          ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩
        · rw [hr, hψ_yu]; exact ha.1 hs
        · rw [hr, hψ_u1]; exact ha.2.1 hs
        · rw [hr, hψ_v3]; exact ha.2.2.1 hs
        · rw [hr, hψ_u2]; exact ha.2.2.2.1 hs
        · rw [hr, hψ_w3]; exact ha.2.2.2.2 hs
      · intro s hsS hiso ⟨r₀, hsr0⟩
        have hr0S : r₀ ∈ S := by by_contra h; exact hiso r₀ h hsr0
        rcases hiso_out s hsS hiso ⟨r₀, hr0S, hsr0⟩ with
          ⟨hsyu, h1ne, h2ne, h3ne, h4ne⟩ | ⟨hsu1, hnsyu, h2ne, h3ne, h4ne⟩
        · refine ⟨yu, hsyu, fun t hst hψt => ?_⟩
          have htS : t ∈ S := by by_contra h; exact hiso t h hst
          rw [hψ_yu] at hψt
          rcases hS_out s hsS t htS hst with
            ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
          · exact ht
          · rw [ht] at hst hψt; exact False.elim (h1ne hst (hψ_u1.symm.trans hψt))
          · rw [ht] at hst hψt; exact False.elim (h2ne hst (hψ_v3.symm.trans hψt))
          · rw [ht] at hst hψt; exact False.elim (h3ne hst (hψ_u2.symm.trans hψt))
          · rw [ht] at hst hψt; exact False.elim (h4ne hst (hψ_w3.symm.trans hψt))
        · refine ⟨u₁, hsu1, fun t hst hψt => ?_⟩
          have htS : t ∈ S := by by_contra h; exact hiso t h hst
          rw [hψ_u1] at hψt
          rcases hS_out s hsS t htS hst with
            ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
          · rw [ht] at hst; exact False.elim (hnsyu hst)
          · exact ht
          · rw [ht] at hψt; exact False.elim (h2ne (hψ_v3.symm.trans hψt))
          · rw [ht] at hψt; exact False.elim (h3ne (hψ_u2.symm.trans hψt))
          · rw [ht] at hψt; exact False.elim (h4ne (hψ_w3.symm.trans hψt))
      · intro r hrS _
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr |
          hrYu | hrY1 | hrY2
        · rw [hr]
          apply pcf_from_leaf_and_three (γ := γu) huxu h1 h2 (ne_of_deg2_ge4 hdxu hdu1)
            (ne_of_deg2_ge4 hdxu hdu2) h12 (not_mem_leafNbrs_of_deg_eq2 hdxu)
            (not_mem_leafNbrs_of_deg_ge4 hdu1) (not_mem_leafNbrs_of_deg_ge4 hdu2)
            (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Yu hall_u
          rw [hψ_xu, hψ_u1, hψ_u2]; exact hγu
        · rw [hr]
          apply pcf_from_leaf_and_three (γ := γ₁) huv₁ hu1y1 h1.symm (ne_of_deg2_ge3 hdv₁ hdy1)
            (ne_of_deg2_ge4 hdv₁ hdu) hy1u (not_mem_leafNbrs_of_deg_eq2 hdv₁)
            (not_mem_leafNbrs_of_deg_ge3 hdy1) (not_mem_leafNbrs_of_deg_ge4 hdu)
            (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y1
            (fun t ht => by
              rcases hall_u1 t ht with h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr h)))
          rw [hψ_v1, hagree y₁ hy1_not_S, hψ_u]; exact hγ₁
        · rw [hr]
          apply pcf_from_leaf_and_three (γ := γ₂) huw₁ hu2y2 h2.symm (ne_of_deg2_ge3 hdw₁ hdy2)
            (ne_of_deg2_ge4 hdw₁ hdu) hy2u (not_mem_leafNbrs_of_deg_eq2 hdw₁)
            (not_mem_leafNbrs_of_deg_ge3 hdy2) (not_mem_leafNbrs_of_deg_ge4 hdu)
            (fun t ht => (mem_leafNbrs.mp ht).1) hψ_Y2
            (fun t ht => by
              rcases hall_u2 t ht with h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr h)))
          rw [hψ_w1, hagree y₂ hy2_not_S, hψ_u]; exact hγ₂
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdxu huxu.symm hxuyu hyuu.symm
            (by rw [hψ_u, hψ_yu]; exact Ne.symm hcyα)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdyu hxuyu.symm hyuzu hzuxu.symm
            (by rw [hψ_xu, hagree zu hzu_not_S]; exact hcxz)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
            (by rw [hψ_u1, hψ_v2]; exact Ne.symm hc2α1)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
            (by rw [hψ_v1, hψ_v3]; exact Ne.symm hc3c1)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
            (by rw [hψ_v2, hagree z₁ hz1_not_S]; exact hc2z1)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdw₁ huw₁.symm hw12 hw2u2.symm
            (by rw [hψ_u2, hψ_w2]; exact Ne.symm hd2α2)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdw₂ hw12.symm hw23 hw31.symm
            (by rw [hψ_w1, hψ_w3]; exact Ne.symm hd3d1)
        · rw [hr]; exact pcf_at_of_two_distinct_neighbors hdw₃ hw23.symm hw3z2 hzw2.symm
            (by rw [hψ_w2, hagree z₂ hz2_not_S]; exact hd2z2)
        · exact ⟨u, (mem_leafNbrs.mp hrYu).1.symm, fun t ht _ =>
            unique_neighbor_of_deg_one (mem_leafNbrs.mp hrYu).2 ht (mem_leafNbrs.mp hrYu).1.symm⟩
        · exact ⟨u₁, (mem_leafNbrs.mp hrY1).1.symm, fun t ht _ =>
            unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY1).2 ht (mem_leafNbrs.mp hrY1).1.symm⟩
        · exact ⟨u₂, (mem_leafNbrs.mp hrY2).1.symm, fun t ht _ =>
            unique_neighbor_of_deg_one (mem_leafNbrs.mp hrY2).2 ht (mem_leafNbrs.mp hrY2).1.symm⟩
    -- 依是否存在外部孤立点分 B0 / B1 / B2 三分支！
    by_cases hiso_ex : ∃ s₀ ∉ S, (∀ t ∉ S, ¬ G.Adj s₀ t) ∧ ∃ r ∈ S, G.Adj s₀ r
    · rcases hiso_ex with ⟨s₀, hs0S, hs0_iso, hs0_nbr⟩
      by_cases hs0_zu : s₀ = zu
      · -- 分支 B1：唯一孤立点 `s₀ = zu`，先固定 `yu ↦ cyu` 并令其余端点避开 `φs' s₀ = cyu`！
        have hcyu_ne : (L yu \ {adm.φ zu}).Nonempty := card_sdiff_one_pos hLyu
        rcases hcyu_ne with ⟨cyu, hcyu_mem⟩
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hcyu_mem
        let φs' : V → ℕ := fun v => if v = s₀ then cyu else adm.φs v
        let Z₁ : Finset ℕ := L v₃ \ {adm.φ z₁, φs' z₁}
        let Z₂ : Finset ℕ := L w₃ \ {adm.φ z₂, φs' z₂}
        have hZ1 : 2 ≤ Z₁.card := card_sdiff_pair_ge_two hLv3
        have hZ2 : 2 ≤ Z₂.card := card_sdiff_pair_ge_two hLw3
        have hu1_ext : ∀ α : ℕ, ∃ α₁ ∈ L u₁ \ {adm.φ y₁, φs' y₁, α},
            ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₁ (adm.φ z₁) α₁,
            ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
            ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
              ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 := fun α =>
          t3_fixed_color_extension hY1_pos hY1_L2 hLv1 hLv2 hZ1
            (card_sdiff_triple_ge_add_one hLu1)
        have hu2_ext : ∀ α : ℕ, ∃ α₂ ∈ L u₂ \ {adm.φ y₂, φs' y₂, α},
            ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
            ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
            ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
              ([d₁, adm.φ y₂, α] : List ℕ).count γ₂ = 1 := fun α =>
          t3_fixed_color_extension hY2_pos hY2_L2 hLw1 hLw2 hZ2
            (card_sdiff_triple_ge_add_one hLu2)
        let f₁ : ℕ → ℕ := fun α => (hu1_ext α).choose
        let f₂ : ℕ → ℕ := fun α => (hu2_ext α).choose
        let C_u : Finset ℕ := L u \ {cyu}
        have hCu : Yu.card + 2 ≤ C_u.card := card_sdiff_one_ge_add_two hLu
        rcases t20_fun_color_extension (L := L) (Y := Yu) (Lv := L xu) (C_u := C_u)
          (fun _ => cyu) f₁ f₂ (φz := adm.φ zu) hYu_pos hYu_L2 hLxu hCu with
          ⟨α, hαC, cxu, hcxu, aYu, haYu, γu, hγu⟩
        let α₁ : ℕ := f₁ α
        have hα1_spec := (hu1_ext α).choose_spec
        change α₁ ∈ L u₁ \ {adm.φ y₁, φs' y₁, α} ∧
            ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₁ (adm.φ z₁) α₁,
            ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
            ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
              ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 at hα1_spec
        rcases hα1_spec with ⟨hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
        let α₂ : ℕ := f₂ α
        have hα2_spec := (hu2_ext α).choose_spec
        change α₂ ∈ L u₂ \ {adm.φ y₂, φs' y₂, α} ∧
            ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
            ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
            ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
              ([d₁, adm.φ y₂, α] : List ℕ).count γ₂ = 1 at hα2_spec
        rcases hα2_spec with ⟨hα2C, d₁, hd₁, aY₂, haY₂, γ₂, hγ₂⟩
        rcases unpack_threeThreadGoodCols hc₁ with
          ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2z1, c₃, hc3Z, hc3c2, hc3c1⟩
        rcases unpack_threeThreadGoodCols hd₁ with
          ⟨hd1L, hd1α2, d₂, hd2L, hd2α2, hd2d1, hd2z2, d₃, hd3Z, hd3d2, hd3d1⟩
        simp only [C_u, Finset.mem_sdiff, Finset.mem_singleton] at hαC
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcxu hα1C
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
        simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
        simp only [Z₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd3Z
        apply hfinish_B α α₁ α₂ cxu cyu c₁ c₂ c₃ d₁ d₂ d₃ aYu aY₁ aY₂
          hαC.1 hα1C.1 hα2C.1 hcxu.1 hcyu_mem.1 hc1L hc2L hc3Z.1 hd1L hd2L hd3Z.1
          haYu haY₁ haY₂ hcxu.2.1 hcxu.2.2.1 hcxu.2.2.2 hcyu_mem.2 (Ne.symm hαC.2)
          hα1C.2.2.2 hα1C.2.1 hc1α1 hc2α1 hc2c1 hc2z1 hc3Z.2.1 hc3c2 hc3c1
          hα2C.2.2.2 hα2C.2.1 hd1α2 hd2α2 hd2d1 hd2z2 hd3Z.2.1 hd3d2 hd3d1
          ⟨γu, hγu⟩ ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
        · intro s _ ⟨t, htS, hst⟩
          have hne0 : s ≠ s₀ := fun h => hs0_iso t htS (h ▸ hst)
          refine ⟨fun h => False.elim (hne0 (h.trans hs0_zu.symm)), ?_, ?_, ?_, ?_⟩
          · intro h; have := hα1C.2.2.1; rw [← h] at this; simpa [φs', hne0] using this
          · intro h; have := hc3Z.2.2; rw [← h] at this; simpa [φs', hne0] using this
          · intro h; have := hα2C.2.2.1; rw [← h] at this; simpa [φs', hne0] using this
          · intro h; have := hd3Z.2.2; rw [← h] at this; simpa [φs', hne0] using this
        · intro s hsS hiso hnbr
          have hseq : s = s₀ := hiso_uniq s s₀ hsS hs0S hiso hs0_iso hnbr hs0_nbr
          subst hseq
          left
          refine ⟨hs0_zu ▸ hyuzu.symm, ?_, ?_, ?_, ?_⟩
          · intro h
            have hy1eq : s = y₁ := by
              rcases hS_out s hsS u₁ (by simp [S]) h with
                ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
              · exact False.elim (by rw [h'] at hdu1; omega)
              · exact h'
              · exact False.elim (by rw [h'] at hdu1; omega)
              · exact False.elim (h12 h')
              · exact False.elim (by rw [h'] at hdu1; omega)
            have := hα1C.2.2.1; rw [← hy1eq] at this; simpa [φs'] using this
          · intro h
            have hz1eq : s = z₁ := by
              rcases hS_out s hsS v₃ (by simp [S]) h with
                ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩ | ⟨h', _⟩
              · exact False.elim (hx_ne_v yu (by simp) v₃ (by simp) h'.symm)
              · exact False.elim (by rw [h'] at hdv₃; omega)
              · exact h'
              · exact False.elim (by rw [h'] at hdv₃; omega)
              · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h')
            have := hc3Z.2.2; rw [← hz1eq] at this; simpa [φs'] using this
          · intro h
            have hy2eq : s = y₂ := by
              rcases hS_out s hsS u₂ (by simp [S]) h with
                ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩
              · exact False.elim (by rw [h'] at hdu2; omega)
              · exact False.elim (h12 h'.symm)
              · exact False.elim (by rw [h'] at hdu2; omega)
              · exact h'
              · exact False.elim (by rw [h'] at hdu2; omega)
            have := hα2C.2.2.1; rw [← hy2eq] at this; simpa [φs'] using this
          · intro h
            have hz2eq : s = z₂ := by
              rcases hS_out s hsS w₃ (by simp [S]) h with
                ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩
              · exact False.elim (hx_ne_w yu (by simp) w₃ (by simp) h'.symm)
              · exact False.elim (by rw [h'] at hdw₃; omega)
              · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h'.symm)
              · exact False.elim (by rw [h'] at hdw₃; omega)
              · exact h'
            have := hd3Z.2.2; rw [← hz2eq] at this; simpa [φs'] using this
      · -- 分支 B2：唯一孤立点 `s₀ ≠ zu`，则 `N(s₀) = {u₁, v₃, u₂, w₃}` 且 `s₀ = y₁ = z₁ = y₂ = z₂`！
        have hns0_yu : ¬ G.Adj s₀ yu := by
          intro h
          rcases hS_out s₀ hs0S yu (by simp [S]) h with
            ⟨_, heq⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
          · exact hs0_zu heq
          · exact False.elim (by rw [h'] at hdyu; omega)
          · exact False.elim (hx_ne_v yu (by simp) v₃ (by simp) h')
          · exact False.elim (by rw [h'] at hdyu; omega)
          · exact False.elim (hx_ne_w yu (by simp) w₃ (by simp) h')
        have hsub4 : G.neighborFinset s₀ ⊆ {u₁, v₃, u₂, w₃} := by
          intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
          have hrS : r ∈ S := by by_contra h; exact hs0_iso r h hr
          rcases hS_out s₀ hs0S r hrS hr with
            ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact False.elim (hns0_yu hr)
          · simp
          · simp
          · simp
          · simp
        have hd4 := hiso_deg4 s₀ hs0S hs0_iso hs0_nbr
        have h4le := card_quad_le u₁ v₃ u₂ w₃
        have hcard_eq : G.neighborFinset s₀ = {u₁, v₃, u₂, w₃} :=
          Finset.eq_of_subset_of_card_le hsub4 (by
            rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
        have hs0_y1 : s₀ = y₁ := by
          have had : G.Adj s₀ u₁ := (G.mem_neighborFinset s₀ u₁).mp (by rw [hcard_eq]; simp)
          rcases hS_out s₀ hs0S u₁ (by simp [S]) had with
            ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
          · exact False.elim (by rw [h'] at hdu1; omega)
          · exact h'
          · exact False.elim (by rw [h'] at hdu1; omega)
          · exact False.elim (h12 h')
          · exact False.elim (by rw [h'] at hdu1; omega)
        have hs0_z1 : s₀ = z₁ := by
          have had : G.Adj s₀ v₃ := (G.mem_neighborFinset s₀ v₃).mp (by rw [hcard_eq]; simp)
          rcases hS_out s₀ hs0S v₃ (by simp [S]) had with
            ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩ | ⟨h', _⟩
          · exact False.elim (hx_ne_v yu (by simp) v₃ (by simp) h'.symm)
          · exact False.elim (by rw [h'] at hdv₃; omega)
          · exact h'
          · exact False.elim (by rw [h'] at hdv₃; omega)
          · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h')
        have hs0_y2 : s₀ = y₂ := by
          have had : G.Adj s₀ u₂ := (G.mem_neighborFinset s₀ u₂).mp (by rw [hcard_eq]; simp)
          rcases hS_out s₀ hs0S u₂ (by simp [S]) had with
            ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩ | ⟨h', _⟩
          · exact False.elim (by rw [h'] at hdu2; omega)
          · exact False.elim (h12 h'.symm)
          · exact False.elim (by rw [h'] at hdu2; omega)
          · exact h'
          · exact False.elim (by rw [h'] at hdu2; omega)
        have hs0_z2 : s₀ = z₂ := by
          have had : G.Adj s₀ w₃ := (G.mem_neighborFinset s₀ w₃).mp (by rw [hcard_eq]; simp)
          rcases hS_out s₀ hs0S w₃ (by simp [S]) had with
            ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩
          · exact False.elim (hx_ne_w yu (by simp) w₃ (by simp) h'.symm)
          · exact False.elim (by rw [h'] at hdw₃; omega)
          · exact False.elim (hv_ne_w v₃ (by simp) w₃ (by simp) h'.symm)
          · exact False.elim (by rw [h'] at hdw₃; omega)
          · exact h'
        -- 用 `t3_fixed_color_extension_avoid` 选 `α₁`（`c₃ ≠ α₁`），再选 `α₂, d₃` 避开 `α₁`！
        let Z₁ : Finset ℕ := L v₃ \ {adm.φ s₀}
        have hZ1 : 3 ≤ Z₁.card := card_sdiff_one_ge_three hLv3
        have hu1_ext : ∀ α : ℕ, ∃ α₁ ∈ L u₁ \ {adm.φ s₀, α},
            ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) (Z₁ \ {α₁}) (adm.φ s₀) α₁,
            ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
            ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
              ([c₁, adm.φ s₀, α] : List ℕ).count γ₁ = 1 := fun α =>
          t3_fixed_color_extension_avoid hY1_pos hY1_L2 hLv1 hLv2 hZ1
            (card_sdiff_pair_ge_add_two hLu1)
        let f₁ : ℕ → ℕ := fun α => (hu1_ext α).choose
        have hu2_ext : ∀ α : ℕ, ∃ α₂ ∈ L u₂ \ {adm.φ s₀, f₁ α, α},
            ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) (L w₃ \ {adm.φ s₀, f₁ α}) (adm.φ s₀) α₂,
            ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
            ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
              ([d₁, adm.φ s₀, α] : List ℕ).count γ₂ = 1 := fun α =>
          t3_fixed_color_extension hY2_pos hY2_L2 hLw1 hLw2
            (card_sdiff_pair_ge_two hLw3) (card_sdiff_triple_ge_add_one hLu2)
        let f₂ : ℕ → ℕ := fun α => (hu2_ext α).choose
        have hcyu_ex : ∀ α : ℕ, (L yu \ {adm.φ zu, adm.φs zu, α}).Nonempty := fun _ =>
          card_sdiff_triple_pos hLyu
        let cFun : ℕ → ℕ := fun α => (hcyu_ex α).choose
        have hcFun_spec : ∀ α, cFun α ∈ L yu ∧ cFun α ≠ adm.φ zu ∧
            cFun α ≠ adm.φs zu ∧ cFun α ≠ α := fun α => by
          have h := (hcyu_ex α).choose_spec
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h
          exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
        rcases t20_fun_color_extension (L := L) (Y := Yu) (Lv := L xu) (C_u := L u)
          cFun f₁ f₂ (φz := adm.φ zu) hYu_pos hYu_L2 hLxu
          (card_ge_add_two_of_eq_add_four hLu) with
          ⟨α, hαL, cxu, hcxu, aYu, haYu, γu, hγu⟩
        let α₁ : ℕ := f₁ α
        have hα1_spec := (hu1_ext α).choose_spec
        change α₁ ∈ L u₁ \ {adm.φ s₀, α} ∧
            ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) (Z₁ \ {α₁}) (adm.φ s₀) α₁,
            ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
            ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
              ([c₁, adm.φ s₀, α] : List ℕ).count γ₁ = 1 at hα1_spec
        rcases hα1_spec with ⟨hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
        let α₂ : ℕ := f₂ α
        have hα2_spec := (hu2_ext α).choose_spec
        change α₂ ∈ L u₂ \ {adm.φ s₀, α₁, α} ∧
            ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) (L w₃ \ {adm.φ s₀, α₁}) (adm.φ s₀) α₂,
            ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
            ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
              ([d₁, adm.φ s₀, α] : List ℕ).count γ₂ = 1 at hα2_spec
        rcases hα2_spec with ⟨hα2C, d₁, hd₁, aY₂, haY₂, γ₂, hγ₂⟩
        rcases unpack_threeThreadGoodCols hc₁ with
          ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2z1, c₃, hc3Z, hc3c2, hc3c1⟩
        rcases unpack_threeThreadGoodCols hd₁ with
          ⟨hd1L, hd1α2, d₂, hd2L, hd2α2, hd2d1, hd2z2, d₃, hd3Z, hd3d2, hd3d1⟩
        let cyu : ℕ := cFun α
        have hcyu := hcFun_spec α
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcxu hα1C
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C hd3Z
        simp only [Z₁, Finset.mem_sdiff, Finset.mem_singleton] at hc3Z
        apply hfinish_B α α₁ α₂ cxu cyu c₁ c₂ c₃ d₁ d₂ d₃ aYu aY₁ aY₂
          hαL hα1C.1 hα2C.1 hcxu.1 hcyu.1 hc1L hc2L hc3Z.1.1 hd1L hd2L hd3Z.1
          haYu haY₁ haY₂ hcxu.2.1 hcxu.2.2.1 hcxu.2.2.2 hcyu.2.1 hcyu.2.2.2
          hα1C.2.2 (hs0_y1 ▸ hα1C.2.1) hc1α1 hc2α1 hc2c1 (hs0_z1 ▸ hc2z1)
          (hs0_z1 ▸ hc3Z.1.2) hc3c2 hc3c1
          hα2C.2.2.2 (hs0_y2 ▸ hα2C.2.1) hd1α2 hd2α2 hd2d1 (hs0_z2 ▸ hd2z2)
          (hs0_z2 ▸ hd3Z.2.1) hd3d2 hd3d1
          ⟨γu, hγu⟩ ⟨γ₁, hs0_y1 ▸ hγ₁⟩ ⟨γ₂, hs0_y2 ▸ hγ₂⟩
        · intro s _ ⟨t, htS, hst⟩
          have hne0 : s ≠ s₀ := fun h => hs0_iso t htS (h ▸ hst)
          refine ⟨fun h => h ▸ hcyu.2.2.1,
            fun h => False.elim (hne0 (h.trans hs0_y1.symm)),
            fun h => False.elim (hne0 (h.trans hs0_z1.symm)),
            fun h => False.elim (hne0 (h.trans hs0_y2.symm)),
            fun h => False.elim (hne0 (h.trans hs0_z2.symm))⟩
        · intro s hsS hiso hnbr
          have hseq : s = s₀ := hiso_uniq s s₀ hsS hs0S hiso hs0_iso hnbr hs0_nbr
          subst hseq
          right
          exact ⟨(G.mem_neighborFinset s u₁).mp (by rw [hcard_eq]; simp),
            hns0_yu, hc3Z.2, hα2C.2.2.1, hd3Z.2.2⟩
    · -- 分支 B0：无任何外部孤立点！
      let Z₁ : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
      let Z₂ : Finset ℕ := L w₃ \ {adm.φ z₂, adm.φs z₂}
      have hZ1 : 2 ≤ Z₁.card := card_sdiff_pair_ge_two hLv3
      have hZ2 : 2 ≤ Z₂.card := card_sdiff_pair_ge_two hLw3
      have hu1_ext : ∀ α : ℕ, ∃ α₁ ∈ L u₁ \ {adm.φ y₁, adm.φs y₁, α},
          ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₁ (adm.φ z₁) α₁,
          ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
          ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
            ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 := fun α =>
        t3_fixed_color_extension hY1_pos hY1_L2 hLv1 hLv2 hZ1
          (card_sdiff_triple_ge_add_one hLu1)
      have hu2_ext : ∀ α : ℕ, ∃ α₂ ∈ L u₂ \ {adm.φ y₂, adm.φs y₂, α},
          ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
          ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
          ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
            ([d₁, adm.φ y₂, α] : List ℕ).count γ₂ = 1 := fun α =>
        t3_fixed_color_extension hY2_pos hY2_L2 hLw1 hLw2 hZ2
          (card_sdiff_triple_ge_add_one hLu2)
      let f₁ : ℕ → ℕ := fun α => (hu1_ext α).choose
      let f₂ : ℕ → ℕ := fun α => (hu2_ext α).choose
      have hcyu_ex : ∀ α : ℕ, (L yu \ {adm.φ zu, adm.φs zu, α}).Nonempty := fun _ =>
        card_sdiff_triple_pos hLyu
      let cFun : ℕ → ℕ := fun α => (hcyu_ex α).choose
      have hcFun_spec : ∀ α, cFun α ∈ L yu ∧ cFun α ≠ adm.φ zu ∧
          cFun α ≠ adm.φs zu ∧ cFun α ≠ α := fun α => by
        have h := (hcyu_ex α).choose_spec
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      rcases t20_fun_color_extension (L := L) (Y := Yu) (Lv := L xu) (C_u := L u)
        cFun f₁ f₂ (φz := adm.φ zu) hYu_pos hYu_L2 hLxu
        (card_ge_add_two_of_eq_add_four hLu) with
        ⟨α, hαL, cxu, hcxu, aYu, haYu, γu, hγu⟩
      let α₁ : ℕ := f₁ α
      have hα1_spec := (hu1_ext α).choose_spec
      change α₁ ∈ L u₁ \ {adm.φ y₁, adm.φs y₁, α} ∧
          ∃ c₁ ∈ threeThreadGoodCols (L v₁) (L v₂) Z₁ (adm.φ z₁) α₁,
          ∃ aY₁ : V → ℕ, (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) ∧
          ∃ γ₁ : ℕ, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
            ([c₁, adm.φ y₁, α] : List ℕ).count γ₁ = 1 at hα1_spec
      rcases hα1_spec with ⟨hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
      let α₂ : ℕ := f₂ α
      have hα2_spec := (hu2_ext α).choose_spec
      change α₂ ∈ L u₂ \ {adm.φ y₂, adm.φs y₂, α} ∧
          ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
          ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
          ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
            ([d₁, adm.φ y₂, α] : List ℕ).count γ₂ = 1 at hα2_spec
      rcases hα2_spec with ⟨hα2C, d₁, hd₁, aY₂, haY₂, γ₂, hγ₂⟩
      rcases unpack_threeThreadGoodCols hc₁ with
        ⟨hc1L, hc1α1, c₂, hc2L, hc2α1, hc2c1, hc2z1, c₃, hc3Z, hc3c2, hc3c1⟩
      rcases unpack_threeThreadGoodCols hd₁ with
        ⟨hd1L, hd1α2, d₂, hd2L, hd2α2, hd2d1, hd2z2, d₃, hd3Z, hd3d2, hd3d1⟩
      let cyu : ℕ := cFun α
      have hcyu := hcFun_spec α
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcxu hα1C
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
      simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
      simp only [Z₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd3Z
      apply hfinish_B α α₁ α₂ cxu cyu c₁ c₂ c₃ d₁ d₂ d₃ aYu aY₁ aY₂
        hαL hα1C.1 hα2C.1 hcxu.1 hcyu.1 hc1L hc2L hc3Z.1 hd1L hd2L hd3Z.1
        haYu haY₁ haY₂ hcxu.2.1 hcxu.2.2.1 hcxu.2.2.2 hcyu.2.1 hcyu.2.2.2
        hα1C.2.2.2 hα1C.2.1 hc1α1 hc2α1 hc2c1 hc2z1 hc3Z.2.1 hc3c2 hc3c1
        hα2C.2.2.2 hα2C.2.1 hd1α2 hd2α2 hd2d1 hd2z2 hd3Z.2.1 hd3d2 hd3d1
        ⟨γu, hγu⟩ ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
      · intro s _ _
        exact ⟨fun h => h ▸ hcyu.2.2.1, fun h => h ▸ hα1C.2.2.1, fun h => h ▸ hc3Z.2.2,
          fun h => h ▸ hα2C.2.2.1, fun h => h ▸ hd3Z.2.2⟩
      · intro s hsS hiso hnbr
        exact False.elim (hiso_ex ⟨s, hsS, hiso, hnbr⟩)

end LeanResearch.Proposal3
