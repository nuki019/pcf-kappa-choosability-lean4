/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BeyondDefs

/-!
# `22/9` 放电桥接与弱点邻接禁用构型（`BridgeExt`）

本模块引入第四类弱 `1`-线串顶点 `IsL4`（`d_G = 4, coreDeg = 3`, `1` 叶 + `3` 条 `1`-线串）
及扩展弱点集 `IsPoor1Ext = {L3, B3, T21, L4}`，在 `2 * p ≤ 5 * q`（`mad < 5/2`）下
零 `sorry` 证明五个核心桥接可约构型引理：
1. `L3_at_most_one_L3_nbr`：每个 `L3` 至多通过 `1`-线串连 `1` 个 `L3`；
2. `no_B3_one_thread_Poor1Ext`：`B3` 不能通过 `1`-线串连接任意 `IsPoor1Ext` 顶点；
3. `no_T21_one_thread_Poor1Ext`：`T21` 不能通过 `1`-线串连接任意 `IsPoor1Ext` 顶点；
4. `no_L4_one_thread_Poor1Ext`：`L4` 不能通过 `1`-线串连接任意 `IsPoor1Ext` 顶点；
5. `no_T21_two_thread_T21`：两个 `T21` 不能通过 `2`-线串相连。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. `IsL4`、`IsPoor1Ext` 定义与结构刻画 -/

/-- `L4` 顶点（即 `4_1_3`）：`d_G = 4`、`coreDeg = 3`、`1` 个叶点 + `3` 条 `1`-线串。 -/
def IsL4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  G.degree u = 4 ∧ coreDeg G u = 3 ∧ (oneThreadNbrs G u).card = 3

/-- 扩展的 `Poor1` 顶点集合 `{L3, B3, T21, L4}`。 -/
def IsPoor1Ext {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  IsL3 G u ∨ IsB3 G u ∨ IsT21 G u ∨ IsL4 G u

private lemma ne_of_deg_eq_ne {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} {m n : ℕ} (ha : G.degree a = m) (hb : G.degree b = n) (hne : m ≠ n) : a ≠ b :=
  fun h => hne (by rw [← ha, h, hb])

private lemma ne_of_deg_ge_lt {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} {m n : ℕ} (ha : m ≤ G.degree a) (hb : G.degree b = n) (hlt : n < m) : a ≠ b :=
  fun h => by rw [h, hb] at ha; omega

lemma hasOneThreadBetween_symm {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : HasOneThreadBetween G u v) : HasOneThreadBetween G v u := by
  rcases h with ⟨a, hua, hda, hav, huv⟩
  exact ⟨a, hav.symm, hda, hua.symm, huv.symm⟩

lemma hasTwoThreadBetween_symm {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : HasTwoThreadBetween G u v) : HasTwoThreadBetween G v u := by
  rcases h with ⟨x, y, hux, hdx, hxy, hyu, hdy, hyv, hvx, huv⟩
  exact ⟨y, x, hyv.symm, hdy, hxy.symm, hvx.symm, hdx, hux.symm, hyu.symm, huv.symm⟩

lemma isL3_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (h : IsL3 G u) :
    G.degree u = 3 ∧ coreDeg G u = 3 ∧ leafNbrs G u = ∅ ∧
      G.neighborFinset u = oneThreadNbrs G u ∧ twoThreadNbrs G u = ∅ ∧ badNbrs G u = ∅ := by
  classical
  rcases h with ⟨hdu3, h1c⟩
  have hc3 : coreDeg G u = 3 := by
    rw [coreDeg_eq_degree_of_deg_le_three hm (by omega : G.degree u ≤ 3), hdu3]
  have hleaf : leafNbrs G u = ∅ :=
    leafNbrs_eq_empty_of_deg_le_three hm (by omega : G.degree u ≤ 3)
  have hsub : oneThreadNbrs G u ⊆ G.neighborFinset u := fun x hx =>
    (G.mem_neighborFinset u x).mpr (mem_oneThreadNbrs.mp hx).1
  have hN : G.neighborFinset u = oneThreadNbrs G u := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdu3, h1c])
  have ht2 : twoThreadNbrs G u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hx1 : x ∈ oneThreadNbrs G u := by
      rw [← hN]; exact (G.mem_neighborFinset u x).mpr (mem_twoThreadNbrs.mp hx).1
    exact not_oneThread_and_longThread (mem_oneThreadNbrs.mp hx1)
      (by rcases mem_twoThreadNbrs.mp hx with ⟨h1, h2, y, _, h3, h4, h5, _⟩
          exact ⟨h1, h2, y, h3, h4, h5⟩)
  have hbad : badNbrs G u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hx1 : x ∈ oneThreadNbrs G u := by
      rw [← hN]; exact (G.mem_neighborFinset u x).mpr (mem_badNbrs.mp hx).1
    have hdx2 : G.degree x = 2 := (mem_oneThreadNbrs.mp hx1).2.1
    have hdx4 : 4 ≤ G.degree x := (mem_badNbrs.mp hx).2.1
    omega
  exact ⟨hdu3, hc3, hleaf, hN, ht2, hbad⟩

lemma isB3_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (h : IsB3 G u) :
    G.degree u = 3 ∧ coreDeg G u = 3 ∧ leafNbrs G u = ∅ ∧
      (oneThreadNbrs G u).card = 2 ∧ (badNbrs G u).card = 1 ∧
      twoThreadNbrs G u = ∅ ∧ goodNbrs G u = ∅ ∧
      G.neighborFinset u = oneThreadNbrs G u ∪ badNbrs G u := by
  classical
  rcases h with ⟨hdu3, h1c, hbc⟩
  have hc3 : coreDeg G u = 3 := by
    rw [coreDeg_eq_degree_of_deg_le_three hm (by omega : G.degree u ≤ 3), hdu3]
  have hleaf : leafNbrs G u = ∅ :=
    leafNbrs_eq_empty_of_deg_le_three hm (by omega : G.degree u ≤ 3)
  have hfive := coreDeg_eq_five_parts hm hpq u
  have ht2 : twoThreadNbrs G u = ∅ := Finset.card_eq_zero.mp (by omega)
  have hgood : goodNbrs G u = ∅ := Finset.card_eq_zero.mp (by omega)
  have hdisj : Disjoint (oneThreadNbrs G u) (badNbrs G u) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have hd2 : G.degree x = 2 := (mem_oneThreadNbrs.mp h1).2.1
    have hd4 : 4 ≤ G.degree x := (mem_badNbrs.mp h2).2.1
    omega
  have hsub : oneThreadNbrs G u ∪ badNbrs G u ⊆ G.neighborFinset u := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact (G.mem_neighborFinset u x).mpr (mem_oneThreadNbrs.mp hx).1
    · exact (G.mem_neighborFinset u x).mpr (mem_badNbrs.mp hx).1
  have hN : G.neighborFinset u = oneThreadNbrs G u ∪ badNbrs G u := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
          hdu3, h1c, hbc])
  exact ⟨hdu3, hc3, hleaf, h1c, hbc, ht2, hgood, hN⟩

lemma isL4_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (h : IsL4 G u) :
    G.degree u = 4 ∧ coreDeg G u = 3 ∧ (leafNbrs G u).card = 1 ∧
      (oneThreadNbrs G u).card = 3 ∧ twoThreadNbrs G u = ∅ ∧
      badNbrs G u = ∅ ∧ goodNbrs G u = ∅ ∧
      coreNbrs G u = oneThreadNbrs G u ∧
      G.neighborFinset u = oneThreadNbrs G u ∪ leafNbrs G u := by
  classical
  rcases h with ⟨hdu4, hc3, h1c⟩
  have hleaf_add := coreDeg_add_leafNbrs hm u
  have hleaf : (leafNbrs G u).card = 1 := by omega
  have hfive := coreDeg_eq_five_parts hm hpq u
  have ht2 : twoThreadNbrs G u = ∅ := Finset.card_eq_zero.mp (by omega)
  have hbad : badNbrs G u = ∅ := Finset.card_eq_zero.mp (by omega)
  have hgood : goodNbrs G u = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsub_core : oneThreadNbrs G u ⊆ coreNbrs G u := fun x hx =>
    mem_coreNbrs.mpr ⟨(mem_oneThreadNbrs.mp hx).1, by have := (mem_oneThreadNbrs.mp hx).2.1; omega⟩
  have hcore : coreNbrs G u = oneThreadNbrs G u := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub_core (by unfold coreDeg at hc3; omega)
  have hdisj : Disjoint (oneThreadNbrs G u) (leafNbrs G u) := by
    rw [← hcore]; exact coreNbrs_disjoint_leafNbrs G u
  have hsub_N : oneThreadNbrs G u ∪ leafNbrs G u ⊆ G.neighborFinset u := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact (G.mem_neighborFinset u x).mpr (mem_oneThreadNbrs.mp hx).1
    · exact (G.mem_neighborFinset u x).mpr (mem_leafNbrs.mp hx).1
  have hN : G.neighborFinset u = oneThreadNbrs G u ∪ leafNbrs G u := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub_N (by
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
          hdu4, h1c, hleaf])
  exact ⟨hdu4, hc3, hleaf, h1c, ht2, hbad, hgood, hcore, hN⟩

lemma coreDeg_eq_three_of_isPoor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (h : IsPoor1Ext G u) :
    coreDeg G u = 3 := by
  rcases h with h | h | h | h
  · exact (isL3_structure hm h).2.1
  · have hdu3 := h.1
    rw [coreDeg_eq_degree_of_deg_le_three hm (by omega : G.degree u ≤ 3), hdu3]
  · exact h.1
  · exact h.2.1

lemma deg_ge_three_of_isPoor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (h : IsPoor1Ext G u) :
    3 ≤ G.degree u := by
  have h1 := coreDeg_eq_three_of_isPoor1Ext hm h
  have h2 := coreDeg_le_degree G u
  omega

lemma not_isBad_of_isPoor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (h : IsPoor1Ext G u) :
    ¬ IsBad G u := by
  intro hb
  have h1 := coreDeg_eq_three_of_isPoor1Ext hm h
  have h2 := hb.2
  omega

lemma twoThreadNbrs_eq_empty_of_not_isT21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (h : IsPoor1Ext G u) (hn : ¬ IsT21 G u) :
    twoThreadNbrs G u = ∅ := by
  rcases h with h | h | h | h
  · exact (isL3_structure hm h).2.2.2.2.1
  · exact (isB3_structure hm hpq h).2.2.2.2.2.1
  · exact False.elim (hn h)
  · exact (isL4_structure hm hpq h).2.2.2.2.1

lemma adj_isPoor1Ext_implies_both_T21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v : V}
    (hu : IsPoor1Ext G u) (hv : IsPoor1Ext G v) (hadj : G.Adj u v) :
    IsT21 G u ∧ IsT21 G v := by
  have hside : ∀ {x y : V}, IsPoor1Ext G x → IsPoor1Ext G y → G.Adj x y → IsT21 G x := by
    intro x y hx hy hxy
    have hdy3 := deg_ge_three_of_isPoor1Ext hm hy
    have hnybad := not_isBad_of_isPoor1Ext hm hy
    rcases hx with hx | hx | hx | hx
    · have hN := (isL3_structure hm hx).2.2.2.1
      have hy1 : y ∈ oneThreadNbrs G x := by rw [← hN]; exact (G.mem_neighborFinset x y).mpr hxy
      have := (mem_oneThreadNbrs.mp hy1).2.1; omega
    · have hN := (isB3_structure hm hpq hx).2.2.2.2.2.2.2
      have hyN : y ∈ oneThreadNbrs G x ∪ badNbrs G x := by
        rw [← hN]; exact (G.mem_neighborFinset x y).mpr hxy
      rw [Finset.mem_union] at hyN
      rcases hyN with hy1 | hyb
      · have := (mem_oneThreadNbrs.mp hy1).2.1; omega
      · exact False.elim (hnybad (mem_badNbrs.mp hyb).2)
    · exact hx
    · have hN := (isL4_structure hm hpq hx).2.2.2.2.2.2.2.2
      have hyN : y ∈ oneThreadNbrs G x ∪ leafNbrs G x := by
        rw [← hN]; exact (G.mem_neighborFinset x y).mpr hxy
      rw [Finset.mem_union] at hyN
      rcases hyN with hy1 | hyl
      · have := (mem_oneThreadNbrs.mp hy1).2.1; omega
      · have := (mem_leafNbrs.mp hyl).2; omega
  exact ⟨hside hu hv hadj, hside hv hu hadj.symm⟩

/-! ## 2. 纯 `Finset` / `List` 组合引理与单点上界引擎 -/

private lemma hasUniqueColor_triple_iff (a b c : ℕ) :
    HasUniqueColor [a, b, c] ↔ ¬ (a = b ∧ b = c) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨rfl, rfl⟩
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx
    split_ifs at hx <;> omega
  · intro h
    by_cases hab : a = b
    · subst hab
      have hac : a ≠ c := fun h' => h ⟨rfl, h'⟩
      refine ⟨c, ?_⟩
      simp [hac]
    · by_cases hac : a = c
      · subst hac
        refine ⟨b, ?_⟩
        simp [hab]
      · refine ⟨a, ?_⟩
        simp [Ne.symm hab, Ne.symm hac]

private lemma not_hasUniqueColor_quad_iff (a b c d : ℕ) :
    ¬ HasUniqueColor [a, b, c, d] ↔
      (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro hno
    have hcount : ∀ x, ([a, b, c, d] : List ℕ).count x ≠ 1 := fun x hx => hno ⟨x, hx⟩
    have ha := hcount a
    have hb := hcount b
    have hc := hcount c
    have hd := hcount d
    by_cases hab : a = b
    · subst hab
      by_cases hcd : c = d
      · exact Or.inl ⟨rfl, hcd⟩
      · by_cases hac : a = c
        · subst hac
          simp only [List.count_cons, List.count_nil, beq_iff_eq, hcd, ite_true, ite_false] at hd
          omega
        · simp only [List.count_cons, List.count_nil, beq_iff_eq, hac, Ne.symm hcd,
            ite_true, ite_false] at hc
          omega
    · by_cases hac : a = c
      · subst hac
        by_cases hbd : b = d
        · exact Or.inr (Or.inl ⟨rfl, hbd⟩)
        · simp only [List.count_cons, List.count_nil, beq_iff_eq, hab, Ne.symm hbd,
            ite_true, ite_false] at hb
          omega
      · by_cases had : a = d
        · subst had
          by_cases hbc : b = c
          · exact Or.inr (Or.inr ⟨rfl, hbc⟩)
          · simp only [List.count_cons, List.count_nil, beq_iff_eq, hab, Ne.symm hbc,
              ite_true, ite_false] at hb
            omega
        · simp only [List.count_cons, List.count_nil, beq_iff_eq, Ne.symm hab, Ne.symm hac,
            Ne.symm had, ite_true, ite_false] at ha
          omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ⟨x, hx⟩
    · simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx
      split_ifs at hx <;> omega
    · simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx
      split_ifs at hx <;> omega
    · simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx
      split_ifs at hx <;> omega

private lemma hasUniqueColor_quad_or_of_ne_last {a b c x y : ℕ} (hne : x ≠ y) :
    HasUniqueColor [a, b, c, x] ∨ HasUniqueColor [a, b, c, y] := by
  by_contra h
  push Not at h
  rcases h with ⟨h1, h2⟩
  rw [not_hasUniqueColor_quad_iff] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
  exact hne (by omega)

private lemma hasUniqueColor_quad_or_of_ne_third {a b x y d : ℕ} (hne : x ≠ y) :
    HasUniqueColor [a, b, x, d] ∨ HasUniqueColor [a, b, y, d] := by
  by_contra h
  push Not at h
  rcases h with ⟨h1, h2⟩
  rw [not_hasUniqueColor_quad_iff] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
  exact hne (by omega)

private lemma hasUniqueColor_quad_or_of_ne_second {a x y c d : ℕ} (hne : x ≠ y) :
    HasUniqueColor [a, x, c, d] ∨ HasUniqueColor [a, y, c, d] := by
  by_contra h
  push Not at h
  rcases h with ⟨h1, h2⟩
  rw [not_hasUniqueColor_quad_iff] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
  exact hne (by omega)

private lemma exists_fourth_unique_color {a b c : ℕ} {Y : Finset ℕ}
    (hY : 2 ≤ Y.card) : ∃ y ∈ Y, HasUniqueColor [a, b, c, y] := by
  rcases exists_two_of_card_ge_two hY with ⟨y₁, hy₁, y₂, hy₂, hne⟩
  rcases hasUniqueColor_quad_or_of_ne_last (a := a) (b := b) (c := c) hne with h1 | h2
  · exact ⟨y₁, hy₁, h1⟩
  · exact ⟨y₂, hy₂, h2⟩

private lemma exists_two_in_four_unique_quad {L : Finset ℕ} (hL : L.card = 4)
    (γ a b c : ℕ) :
    ∃ x ∈ L \ {γ}, ∃ y ∈ L \ {γ}, x ≠ y ∧
      HasUniqueColor [a, b, c, x] ∧ HasUniqueColor [a, b, c, y] := by
  classical
  have hcard3 : 3 ≤ (L \ {γ}).card := by
    have := card_sdiff_ge L {γ}
    simp only [Finset.card_singleton] at this
    omega
  rcases Finset.card_pos.mp (by omega : 0 < (L \ {γ}).card) with ⟨x₁, hx₁⟩
  rcases exists_mem_sdiff_of_lt (A := L \ {γ}) (B := {x₁})
    (by simp only [Finset.card_singleton]; omega) with ⟨x₂, hx₂, hx21⟩
  rcases exists_mem_sdiff_of_lt (A := L \ {γ}) (B := {x₁, x₂})
    (by have := Finset.card_le_two (a := x₁) (b := x₂); omega) with ⟨x₃, hx₃, hx312⟩
  rw [Finset.mem_singleton] at hx21
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx312
  rcases hasUniqueColor_quad_or_of_ne_last (a := a) (b := b) (c := c) (Ne.symm hx21) with h1 | h2
  · rcases hasUniqueColor_quad_or_of_ne_last (a := a) (b := b) (c := c) (Ne.symm hx312.2) with
      h2' | h3'
    · exact ⟨x₁, hx₁, x₂, hx₂, Ne.symm hx21, h1, h2'⟩
    · exact ⟨x₁, hx₁, x₃, hx₃, Ne.symm hx312.1, h1, h3'⟩
  · rcases hasUniqueColor_quad_or_of_ne_last (a := a) (b := b) (c := c) (Ne.symm hx312.1) with
      h1' | h3'
    · exact ⟨x₁, hx₁, x₂, hx₂, Ne.symm hx21, h1', h2⟩
    · exact ⟨x₂, hx₂, x₃, hx₃, Ne.symm hx312.2, h2, h3'⟩

/-- 双端邻域 `w`（已有 1 或 2 个邻居色 `B_w`）与 `v`（已有邻色 `ca`）的联合选色引理。 -/
private lemma pair_double_pcf {A₁ A₂ : Finset ℕ} (hA1 : 2 ≤ A₁.card) (hA2 : 2 ≤ A₂.card)
    (ca : ℕ) (B_w : List ℕ) (hB : B_w.length = 1 ∨ B_w.length = 2) :
    ∃ c₁ ∈ A₁, ∃ c₂ ∈ A₂, ¬ (ca = c₁ ∧ c₁ = c₂) ∧ HasUniqueColor (B_w ++ [c₁, c₂]) := by
  classical
  rcases hB with h1 | h2
  · rcases List.length_eq_one_iff.mp h1 with ⟨x, rfl⟩
    rcases Finset.card_pos.mp (by omega : 0 < A₁.card) with ⟨c₁, hc₁⟩
    rcases exists_mem_sdiff_of_lt (A := A₂) (B := {c₁})
      (by simp only [Finset.card_singleton]; omega) with ⟨c₂, hc₂, hc21⟩
    rw [Finset.mem_singleton] at hc21
    refine ⟨c₁, hc₁, c₂, hc₂, fun h => hc21 h.2.symm, ?_⟩
    simp only [List.cons_append, List.nil_append, hasUniqueColor_triple_iff]
    exact fun h => hc21 h.2.symm
  · rcases List.length_eq_two.mp h2 with ⟨x, y, rfl⟩
    by_cases hxy : x = y
    · subst hxy
      rcases Finset.card_pos.mp (by omega : 0 < A₁.card) with ⟨c₁, hc₁⟩
      rcases exists_mem_sdiff_of_lt (A := A₂) (B := {c₁})
        (by simp only [Finset.card_singleton]; omega) with ⟨c₂, hc₂, hc21⟩
      rw [Finset.mem_singleton] at hc21
      refine ⟨c₁, hc₁, c₂, hc₂, fun h => hc21 h.2.symm, ?_⟩
      simp only [List.cons_append, List.nil_append]
      by_contra hno
      rw [not_hasUniqueColor_quad_iff] at hno
      rcases hno with ⟨_, hEq⟩ | ⟨hEq1, hEq2⟩ | ⟨hEq1, hEq2⟩
      · exact hc21 hEq.symm
      · exact hc21 (hEq2.symm.trans hEq1)
      · exact hc21 (hEq1.symm.trans hEq2)
    · by_cases hsub : A₁ ⊆ {x, y} ∧ A₂ ⊆ {x, y}
      · have hA1eq : A₁ = {x, y} :=
          Finset.eq_of_subset_of_card_le hsub.1 (by rw [Finset.card_pair hxy]; exact hA1)
        have hA2eq : A₂ = {x, y} :=
          Finset.eq_of_subset_of_card_le hsub.2 (by rw [Finset.card_pair hxy]; exact hA2)
        by_cases hcax : ca = x
        · refine ⟨y, by rw [hA1eq]; simp, y, by rw [hA2eq]; simp,
            fun h => hxy (hcax.symm.trans h.1), ?_⟩
          simp only [List.cons_append, List.nil_append]
          refine ⟨x, ?_⟩
          simp [Ne.symm hxy]
        · refine ⟨x, by rw [hA1eq]; simp, x, by rw [hA2eq]; simp, fun h => hcax h.1, ?_⟩
          simp only [List.cons_append, List.nil_append]
          refine ⟨y, ?_⟩
          simp [hxy]
      · have hex : (∃ c₁ ∈ A₁, c₁ ∉ ({x, y} : Finset ℕ)) ∨
            (∃ c₂ ∈ A₂, c₂ ∉ ({x, y} : Finset ℕ)) := by
          by_contra hno
          push Not at hno
          exact hsub ⟨fun c hc => hno.1 c hc, fun c hc => hno.2 c hc⟩
        rcases hex with ⟨c₁, hc₁, hc1out⟩ | ⟨c₂, hc₂, hc2out⟩
        · rcases exists_mem_sdiff_of_lt (A := A₂) (B := {c₁})
            (by simp only [Finset.card_singleton]; omega) with ⟨c₂, hc₂, hc21⟩
          rw [Finset.mem_singleton] at hc21
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1out
          refine ⟨c₁, hc₁, c₂, hc₂, fun h => hc21 h.2.symm, ?_⟩
          simp only [List.cons_append, List.nil_append]
          refine ⟨c₁, ?_⟩
          simp [Ne.symm hc1out.1, Ne.symm hc1out.2, hc21]
        · rcases exists_mem_sdiff_of_lt (A := A₁) (B := {c₂})
            (by simp only [Finset.card_singleton]; omega) with ⟨c₁, hc₁, hc12⟩
          rw [Finset.mem_singleton] at hc12
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2out
          refine ⟨c₁, hc₁, c₂, hc₂, fun h => hc12 h.2, ?_⟩
          simp only [List.cons_append, List.nil_append]
          refine ⟨c₂, ?_⟩
          simp [Ne.symm hc2out.1, Ne.symm hc2out.2, hc12]

/-- 将 `HasUniqueColor [ψ n₁, ψ n₂, ψ n₃]` 直接转化为图上 `3`-度点的 PCF 条件。 -/
private lemma pcf_at_of_hasUniqueColor_three {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {u n₁ n₂ n₃ : V}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃)
    (hall : ∀ z, G.Adj u z → z = n₁ ∨ z = n₂ ∨ z = n₃)
    (huniq : HasUniqueColor [ψ n₁, ψ n₂, ψ n₃]) :
    ∃ y, G.Adj u y ∧ ∀ z, G.Adj u z → ψ z = ψ y → z = y := by
  rcases huniq with ⟨c, hc⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc
  by_cases h1c : ψ n₁ = c
  · have h2c : ψ n₂ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h3c : ψ n₃ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    refine ⟨n₁, h1, fun z hz hψz => ?_⟩
    rcases hall z hz with rfl | rfl | rfl
    · rfl
    · exact False.elim (h2c (hψz.trans h1c))
    · exact False.elim (h3c (hψz.trans h1c))
  · by_cases h2c : ψ n₂ = c
    · have h3c : ψ n₃ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; omega
      refine ⟨n₂, h2, fun z hz hψz => ?_⟩
      rcases hall z hz with rfl | rfl | rfl
      · exact False.elim (h1c (hψz.trans h2c))
      · rfl
      · exact False.elim (h3c (hψz.trans h2c))
    · have h3c : ψ n₃ = c := by
        by_contra h3n; simp only [h1c, h2c, h3n, ite_false] at hc; omega
      refine ⟨n₃, h3, fun z hz hψz => ?_⟩
      rcases hall z hz with rfl | rfl | rfl
      · exact False.elim (h1c (hψz.trans h3c))
      · exact False.elim (h2c (hψz.trans h3c))
      · rfl

/-- 将 `HasUniqueColor [ψ n₁, ψ n₂, ψ n₃, ψ n₄]` 直接转化为图上 `4`-度点的 PCF 条件。 -/
private lemma pcf_at_of_hasUniqueColor_four {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {u n₁ n₂ n₃ n₄ : V}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃) (h4 : G.Adj u n₄)
    (hall : ∀ z, G.Adj u z → z = n₁ ∨ z = n₂ ∨ z = n₃ ∨ z = n₄)
    (huniq : HasUniqueColor [ψ n₁, ψ n₂, ψ n₃, ψ n₄]) :
    ∃ y, G.Adj u y ∧ ∀ z, G.Adj u z → ψ z = ψ y → z = y := by
  rcases huniq with ⟨c, hc⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc
  by_cases h1c : ψ n₁ = c
  · have h2c : ψ n₂ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h3c : ψ n₃ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h4c : ψ n₄ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    refine ⟨n₁, h1, fun z hz hψz => ?_⟩
    rcases hall z hz with rfl | rfl | rfl | rfl
    · rfl
    · exact False.elim (h2c (hψz.trans h1c))
    · exact False.elim (h3c (hψz.trans h1c))
    · exact False.elim (h4c (hψz.trans h1c))
  · by_cases h2c : ψ n₂ = c
    · have h3c : ψ n₃ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; split_ifs at hc <;> omega
      have h4c : ψ n₄ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; split_ifs at hc <;> omega
      refine ⟨n₂, h2, fun z hz hψz => ?_⟩
      rcases hall z hz with rfl | rfl | rfl | rfl
      · exact False.elim (h1c (hψz.trans h2c))
      · rfl
      · exact False.elim (h3c (hψz.trans h2c))
      · exact False.elim (h4c (hψz.trans h2c))
    · by_cases h3c : ψ n₃ = c
      · have h4c : ψ n₄ ≠ c := by
          intro h; simp only [h1c, h2c, h3c, h, ite_false, ite_true] at hc; omega
        refine ⟨n₃, h3, fun z hz hψz => ?_⟩
        rcases hall z hz with rfl | rfl | rfl | rfl
        · exact False.elim (h1c (hψz.trans h3c))
        · exact False.elim (h2c (hψz.trans h3c))
        · rfl
        · exact False.elim (h4c (hψz.trans h3c))
      · have h4c : ψ n₄ = c := by
          by_contra h4n; simp only [h1c, h2c, h3c, h4n, ite_false] at hc; omega
        refine ⟨n₄, h4, fun z hz hψz => ?_⟩
        rcases hall z hz with rfl | rfl | rfl | rfl
        · exact False.elim (h1c (hψz.trans h4c))
        · exact False.elim (h2c (hψz.trans h4c))
        · exact False.elim (h3c (hψz.trans h4c))
        · rfl

/-- 将 `HasUniqueColor [ψ n₁, ψ n₂, ψ n₃, ψ n₄, ψ n₅]` 转化为图上 `5`-度点的 PCF 条件。 -/
private lemma pcf_at_of_hasUniqueColor_five {V : Type*}
    {G : SimpleGraph V} {ψ : V → ℕ} {u n₁ n₂ n₃ n₄ n₅ : V}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃) (h4 : G.Adj u n₄) (h5 : G.Adj u n₅)
    (hall : ∀ z, G.Adj u z → z = n₁ ∨ z = n₂ ∨ z = n₃ ∨ z = n₄ ∨ z = n₅)
    (huniq : HasUniqueColor [ψ n₁, ψ n₂, ψ n₃, ψ n₄, ψ n₅]) :
    ∃ y, G.Adj u y ∧ ∀ z, G.Adj u z → ψ z = ψ y → z = y := by
  rcases huniq with ⟨c, hc⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc
  by_cases h1c : ψ n₁ = c
  · have h2c : ψ n₂ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h3c : ψ n₃ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h4c : ψ n₄ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    have h5c : ψ n₅ ≠ c := by
      intro h; simp only [h1c, h, ite_true] at hc; split_ifs at hc <;> omega
    refine ⟨n₁, h1, fun z hz hψz => ?_⟩
    rcases hall z hz with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact False.elim (h2c (hψz.trans h1c))
    · exact False.elim (h3c (hψz.trans h1c))
    · exact False.elim (h4c (hψz.trans h1c))
    · exact False.elim (h5c (hψz.trans h1c))
  · by_cases h2c : ψ n₂ = c
    · have h3c : ψ n₃ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; split_ifs at hc <;> omega
      have h4c : ψ n₄ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; split_ifs at hc <;> omega
      have h5c : ψ n₅ ≠ c := by
        intro h; simp only [h1c, h2c, h, ite_false, ite_true] at hc; split_ifs at hc <;> omega
      refine ⟨n₂, h2, fun z hz hψz => ?_⟩
      rcases hall z hz with rfl | rfl | rfl | rfl | rfl
      · exact False.elim (h1c (hψz.trans h2c))
      · rfl
      · exact False.elim (h3c (hψz.trans h2c))
      · exact False.elim (h4c (hψz.trans h2c))
      · exact False.elim (h5c (hψz.trans h2c))
    · by_cases h3c : ψ n₃ = c
      · have h4c : ψ n₄ ≠ c := by
          intro h; simp only [h1c, h2c, h3c, h, ite_false, ite_true] at hc
          split_ifs at hc <;> omega
        have h5c : ψ n₅ ≠ c := by
          intro h; simp only [h1c, h2c, h3c, h, ite_false, ite_true] at hc
          split_ifs at hc <;> omega
        refine ⟨n₃, h3, fun z hz hψz => ?_⟩
        rcases hall z hz with rfl | rfl | rfl | rfl | rfl
        · exact False.elim (h1c (hψz.trans h3c))
        · exact False.elim (h2c (hψz.trans h3c))
        · rfl
        · exact False.elim (h4c (hψz.trans h3c))
        · exact False.elim (h5c (hψz.trans h3c))
      · by_cases h4c : ψ n₄ = c
        · have h5c : ψ n₅ ≠ c := by
            intro h; simp only [h1c, h2c, h3c, h4c, h, ite_false, ite_true] at hc; omega
          refine ⟨n₄, h4, fun z hz hψz => ?_⟩
          rcases hall z hz with rfl | rfl | rfl | rfl | rfl
          · exact False.elim (h1c (hψz.trans h4c))
          · exact False.elim (h2c (hψz.trans h4c))
          · exact False.elim (h3c (hψz.trans h4c))
          · rfl
          · exact False.elim (h5c (hψz.trans h4c))
        · have h5c : ψ n₅ = c := by
            by_contra h5n; simp only [h1c, h2c, h3c, h4c, h5n, ite_false] at hc; omega
          refine ⟨n₅, h5, fun z hz hψz => ?_⟩
          rcases hall z hz with rfl | rfl | rfl | rfl | rfl
          · exact False.elim (h1c (hψz.trans h5c))
          · exact False.elim (h2c (hψz.trans h5c))
          · exact False.elim (h3c (hψz.trans h5c))
          · exact False.elim (h4c (hψz.trans h5c))
          · rfl

/-- `L3` 与 `B3` 共用的 `1`-线串端元可延拓颜色集 `pairGoodA`。 -/
private noncomputable def pairGoodA (C₂ A₂ A₃ L_a : Finset ℕ) (γ : ℕ) : Finset ℕ := by
  classical
  exact (L_a \ {γ}).filter (fun ca =>
    ∃ α ∈ C₂ \ {γ}, α ≠ ca ∧
      ∃ c₂ ∈ A₂ \ {α}, ∃ c₃ ∈ A₃ \ {α}, ¬ (ca = c₂ ∧ c₂ = c₃))

/-- `pairGoodA` 核心性质：对任意 `γ` 非空，且单点计数不超过 `2`。 -/
private lemma pair_goodA_props {C₂ A₂ A₃ L_a : Finset ℕ}
    (hC2 : 2 ≤ C₂.card) (hA2 : 2 ≤ A₂.card) (hA3 : 2 ≤ A₃.card) (hLa : L_a.card = 4) :
    (∀ γ, (pairGoodA C₂ A₂ A₃ L_a γ).Nonempty) ∧
    (∀ C : Finset ℕ, (C.filter (fun γ => (pairGoodA C₂ A₂ A₃ L_a γ).card = 1)).card ≤ 2) := by
  classical
  constructor
  · intro γ
    have hC2' : 0 < (C₂ \ {γ}).card := by
      have := card_sdiff_ge C₂ {γ}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hC2' with ⟨α, hα⟩
    have hA2' : 0 < (A₂ \ {α}).card := by
      have := card_sdiff_ge A₂ {α}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hA2' with ⟨c₂, hc₂⟩
    have hA3' : 0 < (A₃ \ {α}).card := by
      have := card_sdiff_ge A₃ {α}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hA3' with ⟨c₃, hc₃⟩
    rcases exists_mem_sdiff_of_lt (A := L_a) (B := {γ, α, c₂})
      (by have := card_triple_le γ α c₂; omega) with ⟨ca, hcaL, hcaN⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcaN
    refine ⟨ca, ?_⟩
    simp only [pairGoodA, Finset.mem_filter]
    exact ⟨Finset.mem_sdiff.mpr ⟨hcaL, by simp [hcaN.1]⟩,
      α, hα, Ne.symm hcaN.2.1, c₂, hc₂, c₃, hc₃, fun h => hcaN.2.2 h.1⟩
  · intro C
    have hkey : ∀ γ, (pairGoodA C₂ A₂ A₃ L_a γ).card = 1 →
        A₂.card = 2 ∧ A₂ ⊆ L_a ∧ γ ∈ L_a \ A₂ := by
      intro γ hcard1
      have hC2' : 0 < (C₂ \ {γ}).card := by
        have := card_sdiff_ge C₂ {γ}; simp only [Finset.card_singleton] at this; omega
      rcases Finset.card_pos.mp hC2' with ⟨α, hα⟩
      have hA2' : 0 < (A₂ \ {α}).card := by
        have := card_sdiff_ge A₂ {α}; simp only [Finset.card_singleton] at this; omega
      rcases Finset.card_pos.mp hA2' with ⟨c₂₀, hc₂₀⟩
      have hA3' : 0 < (A₃ \ {α}).card := by
        have := card_sdiff_ge A₃ {α}; simp only [Finset.card_singleton] at this; omega
      rcases Finset.card_pos.mp hA3' with ⟨c₃₀, hc₃₀⟩
      have hsame : ∀ c₂ ∈ A₂ \ {α}, ∀ c₃ ∈ A₃ \ {α}, c₂ = c₃ := by
        intro c₂ hc₂ c₃ hc₃
        by_contra hne
        have hsub : L_a \ {γ, α} ⊆ pairGoodA C₂ A₂ A₃ L_a γ := by
          intro ca hca
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca
          simp only [pairGoodA, Finset.mem_filter]
          exact ⟨Finset.mem_sdiff.mpr ⟨hca.1, by simp [hca.2.1]⟩,
            α, hα, Ne.symm hca.2.2, c₂, hc₂, c₃, hc₃, fun h => hne h.2⟩
        have hle := Finset.card_le_card hsub
        have hge2 : 2 ≤ (L_a \ {γ, α}).card := by
          have := card_sdiff_ge L_a {γ, α}; have := Finset.card_le_two (a := γ) (b := α); omega
        omega
      have hc23 : c₂₀ = c₃₀ := hsame c₂₀ hc₂₀ c₃₀ hc₃₀
      have hA2_sdiff : A₂ \ {α} = {c₂₀} := by
        ext x; simp only [Finset.mem_singleton]
        exact ⟨fun hx => (hsame x hx c₃₀ hc₃₀).trans hc23.symm, fun hx => hx ▸ hc₂₀⟩
      have hαA2 : α ∈ A₂ := by
        by_contra hnot
        have hEq : A₂ \ {α} = A₂ := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨And.left, fun hx => ⟨hx, fun h => hnot (h ▸ hx)⟩⟩
        rw [hEq] at hA2_sdiff
        have : A₂.card = 1 := by rw [hA2_sdiff, Finset.card_singleton]
        omega
      have hc20_ne : c₂₀ ≠ α := by
        have h := (Finset.mem_sdiff.mp hc₂₀).2; simpa using h
      have hA2_eq : A₂ = {α, c₂₀} := by
        ext x
        by_cases hxa : x = α
        · subst hxa; simp [hαA2]
        · have hxiff : x ∈ A₂ ↔ x ∈ A₂ \ {α} := by simp [hxa]
          rw [hxiff, hA2_sdiff]; simp [hxa]
      have hA2_card : A₂.card = 2 := by rw [hA2_eq, Finset.card_pair hc20_ne.symm]
      have hsub3 : L_a \ insert γ A₂ ⊆ pairGoodA C₂ A₂ A₃ L_a γ := by
        intro ca hca
        simp only [Finset.mem_sdiff, Finset.mem_insert, hA2_eq, Finset.mem_singleton, not_or] at hca
        simp only [pairGoodA, Finset.mem_filter]
        exact ⟨Finset.mem_sdiff.mpr ⟨hca.1, by simp [hca.2.1]⟩,
          α, hα, Ne.symm hca.2.2.1, c₂₀, hc₂₀, c₃₀, hc₃₀, fun h => hca.2.2.2 h.1⟩
      have hle1 : (L_a \ insert γ A₂).card ≤ 1 := by
        have := Finset.card_le_card hsub3; omega
      have hinter : 3 ≤ (L_a ∩ insert γ A₂).card := by
        have := Finset.card_sdiff_add_card_inter L_a (insert γ A₂); omega
      have hcard_ins : (insert γ A₂).card ≤ 3 := by
        have := Finset.card_insert_le γ A₂; omega
      have hle_ins : (L_a ∩ insert γ A₂).card ≤ (insert γ A₂).card :=
        Finset.card_le_card Finset.inter_subset_right
      have hEq_ins : L_a ∩ insert γ A₂ = insert γ A₂ :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have hins_sub : insert γ A₂ ⊆ L_a := by
        intro x hx; rw [← hEq_ins] at hx; exact (Finset.mem_inter.mp hx).1
      have hγA2 : γ ∉ A₂ := by
        intro hmem
        have : (insert γ A₂).card = 2 := by rw [Finset.insert_eq_of_mem hmem, hA2_card]
        omega
      refine ⟨hA2_card, fun x hx => hins_sub (Finset.mem_insert_of_mem hx), ?_⟩
      exact Finset.mem_sdiff.mpr ⟨hins_sub (Finset.mem_insert_self γ A₂), hγA2⟩
    by_cases hne : (C.filter (fun γ => (pairGoodA C₂ A₂ A₃ L_a γ).card = 1)).Nonempty
    · rcases hne with ⟨γ₀, hγ₀⟩
      have h0 := hkey γ₀ (Finset.mem_filter.mp hγ₀).2
      have hsub : C.filter (fun γ => (pairGoodA C₂ A₂ A₃ L_a γ).card = 1) ⊆ L_a \ A₂ :=
        fun γ hγ => (hkey γ (Finset.mem_filter.mp hγ).2).2.2
      calc (C.filter (fun γ => (pairGoodA C₂ A₂ A₃ L_a γ).card = 1)).card
          ≤ (L_a \ A₂).card := Finset.card_le_card hsub
        _ = 2 := by rw [Finset.card_sdiff_of_subset h0.2.1, hLa, h0.1]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty]; omega

/-- `T21` 与 `L4` 共用的含叶 `4`-度端元可延拓颜色集 `leafQuadGoodA`。 -/
private noncomputable def leafQuadGoodA (C_v L_y L_a : Finset ℕ) (P : ℕ → ℕ → ℕ → Prop)
    (γ : ℕ) : Finset ℕ := by
  classical
  exact (L_a \ {γ}).filter (fun ca =>
    ∃ α ∈ C_v \ {γ}, α ≠ ca ∧ ∃ cy ∈ L_y \ {α}, ∃ c₁ c₂, P α c₁ c₂ ∧
      HasUniqueColor [c₁, c₂, cy, ca])

/-- `leafQuadGoodA` 核心性质：对任意 `γ` 非空，且单点计数不超过 `1`。 -/
private lemma leafQuad_goodA_props {C_v L_y L_a : Finset ℕ} {P : ℕ → ℕ → ℕ → Prop}
    (hCv : 3 ≤ C_v.card) (hLy : L_y.card = 2) (hLa : L_a.card = 4)
    (hP : ∀ α ∈ C_v, ∃ c₁ c₂, P α c₁ c₂) :
    (∀ γ, (leafQuadGoodA C_v L_y L_a P γ).Nonempty) ∧
    (∀ C : Finset ℕ, (C.filter (fun γ => (leafQuadGoodA C_v L_y L_a P γ).card = 1)).card ≤ 1) := by
  classical
  constructor
  · intro γ
    have hCv' : 0 < (C_v \ {γ}).card := by
      have := card_sdiff_ge C_v {γ}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hCv' with ⟨α, hα⟩
    rcases hP α (Finset.mem_sdiff.mp hα).1 with ⟨c₁, c₂, hPα⟩
    have hLy' : 0 < (L_y \ {α}).card := by
      have := card_sdiff_ge L_y {α}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hLy' with ⟨cy, hcy⟩
    have hLa2 : 2 ≤ (L_a \ {γ, α}).card := by
      have := card_sdiff_ge L_a {γ, α}; have := Finset.card_le_two (a := γ) (b := α); omega
    rcases exists_two_of_card_ge_two hLa2 with ⟨ca₁, hca₁, ca₂, hca₂, hne⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca₁ hca₂
    rcases hasUniqueColor_quad_or_of_ne_last (a := c₁) (b := c₂) (c := cy) hne with h1 | h2
    · refine ⟨ca₁, ?_⟩
      simp only [leafQuadGoodA, Finset.mem_filter]
      exact ⟨Finset.mem_sdiff.mpr ⟨hca₁.1, by simp [hca₁.2.1]⟩,
        α, hα, Ne.symm hca₁.2.2, cy, hcy, c₁, c₂, hPα, h1⟩
    · refine ⟨ca₂, ?_⟩
      simp only [leafQuadGoodA, Finset.mem_filter]
      exact ⟨Finset.mem_sdiff.mpr ⟨hca₂.1, by simp [hca₂.2.1]⟩,
        α, hα, Ne.symm hca₂.2.2, cy, hcy, c₁, c₂, hPα, h2⟩
  · intro C
    have hsubLy : ∀ γ, (leafQuadGoodA C_v L_y L_a P γ).card = 1 → C_v \ {γ} ⊆ L_y := by
      intro γ hcard1 α hα
      by_contra hαnot
      have hLy_eq : L_y \ {α} = L_y := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨And.left, fun hx => ⟨hx, fun h => hαnot (h ▸ hx)⟩⟩
      rcases exists_two_of_card_ge_two (by rw [hLy_eq, hLy] : 2 ≤ (L_y \ {α}).card) with
        ⟨cy₁, hcy₁, cy₂, hcy₂, hne_cy⟩
      rcases hP α (Finset.mem_sdiff.mp hα).1 with ⟨c₁, c₂, hPα⟩
      have hsub : L_a \ {γ, α} ⊆ leafQuadGoodA C_v L_y L_a P γ := by
        intro ca hca
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca
        simp only [leafQuadGoodA, Finset.mem_filter]
        rcases hasUniqueColor_quad_or_of_ne_third (a := c₁) (b := c₂) (d := ca) hne_cy with
          h1 | h2
        · exact ⟨Finset.mem_sdiff.mpr ⟨hca.1, by simp [hca.2.1]⟩,
            α, hα, Ne.symm hca.2.2, cy₁, hcy₁, c₁, c₂, hPα, h1⟩
        · exact ⟨Finset.mem_sdiff.mpr ⟨hca.1, by simp [hca.2.1]⟩,
            α, hα, Ne.symm hca.2.2, cy₂, hcy₂, c₁, c₂, hPα, h2⟩
      have hle := Finset.card_le_card hsub
      have hge2 : 2 ≤ (L_a \ {γ, α}).card := by
        have := card_sdiff_ge L_a {γ, α}; have := Finset.card_le_two (a := γ) (b := α); omega
      omega
    by_contra hgt
    push Not at hgt
    rcases exists_two_of_card_ge_two (by omega :
        2 ≤ (C.filter (fun γ => (leafQuadGoodA C_v L_y L_a P γ).card = 1)).card) with
      ⟨γ₁, hγ₁, γ₂, hγ₂, hne⟩
    have hs1 := hsubLy γ₁ (Finset.mem_filter.mp hγ₁).2
    have hs2 := hsubLy γ₂ (Finset.mem_filter.mp hγ₂).2
    have hCv_sub : C_v ⊆ L_y := by
      intro x hx
      by_cases hx1 : x = γ₁
      · exact hs2 (Finset.mem_sdiff.mpr ⟨hx, by simp [hx1, hne]⟩)
      · exact hs1 (Finset.mem_sdiff.mpr ⟨hx, by simp [hx1]⟩)
    have hle := Finset.card_le_card hCv_sub
    omega

/-- `no_T21_two_thread_T21` 核心纯 `Finset` 引理。 -/
private lemma t21_two_thread_ext {C₁ C₂ L_y1 L_y2 A₁ A₂ L_v L_w : Finset ℕ} {β₁ β₂ : ℕ}
    (hC1 : 2 ≤ C₁.card) (hC2 : 2 ≤ C₂.card)
    (hLy1 : L_y1.card = 2) (hLy2 : L_y2.card = 2)
    (hA1 : 2 ≤ A₁.card) (hA2 : 2 ≤ A₂.card)
    (hLv : L_v.card = 4) (hLw : L_w.card = 4) (hβ1 : β₁ ∉ C₁) :
    ∃ γ ∈ C₁, ∃ α ∈ C₂,
      ∃ cy₁ ∈ L_y1 \ {γ}, ∃ ca₁ ∈ A₁ \ {γ},
      ∃ cy₂ ∈ L_y2 \ {α}, ∃ ca₂ ∈ A₂ \ {α},
      ∃ cv ∈ L_v \ {γ, α}, ∃ cw ∈ L_w \ {α, γ},
      cv ≠ cw ∧ HasUniqueColor [β₁, cy₁, ca₁, cv] ∧ HasUniqueColor [β₂, cy₂, ca₂, cw] := by
  classical
  have hpick2 : ∀ (γ : ℕ) (α : ℕ), α ∈ C₂ →
      ∃ cy₂ ∈ L_y2 \ {α}, ∃ ca₂ ∈ A₂ \ {α}, ∃ cw ∈ L_w \ {α, γ},
        HasUniqueColor [β₂, cy₂, ca₂, cw] := by
    intro γ α _
    have hy2 : 0 < (L_y2 \ {α}).card := by
      have := card_sdiff_ge L_y2 {α}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp hy2 with ⟨cy₂, hcy₂⟩
    have ha2 : 0 < (A₂ \ {α}).card := by
      have := card_sdiff_ge A₂ {α}; simp only [Finset.card_singleton] at this; omega
    rcases Finset.card_pos.mp ha2 with ⟨ca₂, hca₂⟩
    have hw2 : 2 ≤ (L_w \ {α, γ}).card := by
      have := card_sdiff_ge L_w {α, γ}; have := Finset.card_le_two (a := α) (b := γ); omega
    rcases exists_fourth_unique_color (a := β₂) (b := cy₂) (c := ca₂) hw2 with ⟨cw, hcw, hu2⟩
    exact ⟨cy₂, hcy₂, ca₂, hca₂, cw, hcw, hu2⟩
  by_cases hflex : ∃ γ ∈ C₁, 2 ≤ (L_y1 \ {γ}).card ∨ 2 ≤ (A₁ \ {γ}).card
  · rcases hflex with ⟨γ, hγ, hcase⟩
    rcases Finset.card_pos.mp (by omega : 0 < C₂.card) with ⟨α, hα⟩
    rcases hpick2 γ α hα with ⟨cy₂, hcy₂, ca₂, hca₂, cw, hcw, hu2⟩
    rcases exists_mem_sdiff_of_lt (A := L_v) (B := {γ, α, cw})
      (by have := card_triple_le γ α cw; omega) with ⟨cv, hcvL, hcvN⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcvN
    have hcv_mem : cv ∈ L_v \ {γ, α} :=
      Finset.mem_sdiff.mpr ⟨hcvL, by simp [hcvN.1, hcvN.2.1]⟩
    rcases hcase with hyflex | haflex
    · have ha1 : 0 < (A₁ \ {γ}).card := by
        have := card_sdiff_ge A₁ {γ}; simp only [Finset.card_singleton] at this; omega
      rcases Finset.card_pos.mp ha1 with ⟨ca₁, hca₁⟩
      rcases exists_two_of_card_ge_two hyflex with ⟨y₁, hy₁, y₂, hy₂, hne⟩
      rcases hasUniqueColor_quad_or_of_ne_second (a := β₁) (c := ca₁) (d := cv) hne with h1 | h2
      · exact ⟨γ, hγ, α, hα, y₁, hy₁, ca₁, hca₁, cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
          hcvN.2.2, h1, hu2⟩
      · exact ⟨γ, hγ, α, hα, y₂, hy₂, ca₁, hca₁, cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
          hcvN.2.2, h2, hu2⟩
    · have hy1 : 0 < (L_y1 \ {γ}).card := by
        have := card_sdiff_ge L_y1 {γ}; simp only [Finset.card_singleton] at this; omega
      rcases Finset.card_pos.mp hy1 with ⟨cy₁, hcy₁⟩
      rcases exists_two_of_card_ge_two haflex with ⟨a₁, ha₁, a₂, ha₂, hne⟩
      rcases hasUniqueColor_quad_or_of_ne_third (a := β₁) (b := cy₁) (d := cv) hne with h1 | h2
      · exact ⟨γ, hγ, α, hα, cy₁, hcy₁, a₁, ha₁, cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
          hcvN.2.2, h1, hu2⟩
      · exact ⟨γ, hγ, α, hα, cy₁, hcy₁, a₂, ha₂, cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
          hcvN.2.2, h2, hu2⟩
  · push Not at hflex
    rcases exists_two_of_card_ge_two hC1 with ⟨γ₁, hγ₁, γ₂, hγ₂, hγ12⟩
    rcases exists_two_of_card_ge_two hC2 with ⟨α₁, hα₁, α₂, hα₂, hα12⟩
    have hmem_of_lt2 : ∀ (S : Finset ℕ), 2 ≤ S.card → ∀ γ ∈ C₁, (S \ {γ}).card < 2 →
        γ ∈ S ∧ S.card = 2 := by
      intro S hS γ _ hlt
      have hγS : γ ∈ S := by
        by_contra hnot
        have hEq : S \ {γ} = S := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨And.left, fun hx => ⟨hx, fun h => hnot (h ▸ hx)⟩⟩
        rw [hEq] at hlt; omega
      have hcard := Finset.card_sdiff_add_card_inter S {γ}
      have hI : S ∩ {γ} = {γ} := by ext x; simp [hγS]
      rw [hI, Finset.card_singleton] at hcard
      exact ⟨hγS, by omega⟩
    have hLy1_eq : L_y1 = {γ₁, γ₂} := by
      have h1 := hmem_of_lt2 L_y1 (by omega) γ₁ hγ₁ (hflex γ₁ hγ₁).1
      have h2 := hmem_of_lt2 L_y1 (by omega) γ₂ hγ₂ (hflex γ₂ hγ₂).1
      symm
      exact Finset.eq_of_subset_of_card_le
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h1.1
          · exact h2.1)
        (by rw [Finset.card_pair hγ12, hLy1])
    have hA1_eq : A₁ = {γ₁, γ₂} := by
      have h1 := hmem_of_lt2 A₁ hA1 γ₁ hγ₁ (hflex γ₁ hγ₁).2
      have h2 := hmem_of_lt2 A₁ hA1 γ₂ hγ₂ (hflex γ₂ hγ₂).2
      symm
      exact Finset.eq_of_subset_of_card_le
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h1.1
          · exact h2.1)
        (by rw [Finset.card_pair hγ12, h1.2])
    have hpair_good : ∃ γ ∈ ({γ₁, γ₂} : Finset ℕ), ∃ α ∈ ({α₁, α₂} : Finset ℕ),
        2 ≤ (L_v \ {γ, α, β₁}).card := by
      by_contra hno
      push Not at hno
      have hsub_Lv : ∀ γ ∈ ({γ₁, γ₂} : Finset ℕ), ∀ α ∈ ({α₁, α₂} : Finset ℕ),
          ({γ, α, β₁} : Finset ℕ) ⊆ L_v ∧ γ ≠ α ∧ γ ≠ β₁ ∧ α ≠ β₁ := by
        intro γ hγm α hαm
        have hlt := hno γ hγm α hαm
        have hinter : 3 ≤ (L_v ∩ {γ, α, β₁}).card := by
          have := Finset.card_sdiff_add_card_inter L_v {γ, α, β₁}; omega
        have htri_le := card_triple_le γ α β₁
        have hle_tri : (L_v ∩ {γ, α, β₁}).card ≤ ({γ, α, β₁} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_right
        have htri_eq : ({γ, α, β₁} : Finset ℕ).card = 3 := by omega
        have hEqI : L_v ∩ {γ, α, β₁} = {γ, α, β₁} :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        have hsub : ({γ, α, β₁} : Finset ℕ) ⊆ L_v := by
          intro x hx; rw [← hEqI] at hx; exact (Finset.mem_inter.mp hx).1
        have hγα : γ ≠ α := by
          intro h; subst h
          have : ({γ, γ, β₁} : Finset ℕ) = {γ, β₁} := by ext x; simp
          rw [this] at htri_eq; have := Finset.card_le_two (a := γ) (b := β₁); omega
        have hγβ : γ ≠ β₁ := by
          intro h; subst h
          have : ({γ, α, γ} : Finset ℕ) = {γ, α} := by ext x; simp; tauto
          rw [this] at htri_eq; have := Finset.card_le_two (a := γ) (b := α); omega
        have hαβ : α ≠ β₁ := by
          intro h; subst h
          have : ({γ, α, α} : Finset ℕ) = {γ, α} := by ext x; simp
          rw [this] at htri_eq; have := Finset.card_le_two (a := γ) (b := α); omega
        exact ⟨hsub, hγα, hγβ, hαβ⟩
      have h11 := hsub_Lv γ₁ (by simp) α₁ (by simp)
      have h21 := hsub_Lv γ₂ (by simp) α₁ (by simp)
      have h12 := hsub_Lv γ₁ (by simp) α₂ (by simp)
      have h22 := hsub_Lv γ₂ (by simp) α₂ (by simp)
      have h5sub : ({γ₁, γ₂, α₁, α₂, β₁} : Finset ℕ) ⊆ L_v := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h11.1 (by simp)
        · exact h21.1 (by simp)
        · exact h11.1 (by simp)
        · exact h12.1 (by simp)
        · exact h11.1 (by simp)
      have h5card : ({γ₁, γ₂, α₁, α₂, β₁} : Finset ℕ).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [hγ12, h11.2.1, h12.2.1, h11.2.2.1]),
            Finset.card_insert_of_notMem (by simp [h21.2.1, h22.2.1, h21.2.2.1]),
            Finset.card_insert_of_notMem (by simp [hα12, h11.2.2.2]),
            Finset.card_pair h12.2.2.2]
      have hle := Finset.card_le_card h5sub
      omega
    rcases hpair_good with ⟨γ, hγm, α, hαm, hLv2⟩
    have hγC : γ ∈ C₁ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hγm
      rcases hγm with rfl | rfl <;> assumption
    have hαC : α ∈ C₂ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hαm
      rcases hαm with rfl | rfl <;> assumption
    rcases hpick2 γ α hαC with ⟨cy₂, hcy₂, ca₂, hca₂, cw, hcw, hu2⟩
    rcases exists_mem_sdiff_of_lt (A := L_v \ {γ, α, β₁}) (B := {cw})
      (by simp only [Finset.card_singleton]; omega) with ⟨cv, hcv, hcvw⟩
    rw [Finset.mem_singleton] at hcvw
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcv
    have hcv_mem : cv ∈ L_v \ {γ, α} :=
      Finset.mem_sdiff.mpr ⟨hcv.1, by simp [hcv.2.1, hcv.2.2.1]⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγm
    rcases hγm with hγ_eq | hγ_eq
    · subst hγ_eq
      have hβγ2 : β₁ ≠ γ₂ := fun h => hβ1 (h ▸ hγ₂)
      refine ⟨γ, hγ₁, α, hαC, γ₂, by rw [hLy1_eq]; simp [hγ12.symm],
        γ₂, by rw [hA1_eq]; simp [hγ12.symm], cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
        hcvw, ?_, hu2⟩
      refine ⟨β₁, ?_⟩
      simp [Ne.symm hβγ2, hcv.2.2.2]
    · subst hγ_eq
      have hβγ1 : β₁ ≠ γ₁ := fun h => hβ1 (h ▸ hγ₁)
      refine ⟨γ, hγ₂, α, hαC, γ₁, by rw [hLy1_eq]; simp [hγ12],
        γ₁, by rw [hA1_eq]; simp [hγ12], cy₂, hcy₂, ca₂, hca₂, cv, hcv_mem, cw, hcw,
        hcvw, ?_, hu2⟩
      refine ⟨β₁, ?_⟩
      simp [Ne.symm hβγ1, hcv.2.2.2]

/-! ## 3. 结构解包助手与引理 5（`no_T21_two_thread_T21`） -/

/-- 将 `bad_fixed_color_extension` 给出的多重度为 `1` 条件转化为坏点 `b` 的 PCF 条件。 -/
private lemma pcf_at_bad_of_count_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ψ : V → ℕ} {b u h : V}
    (hbu : G.Adj b u) (hbh : G.Adj b h)
    (hall : ∀ r, G.Adj b r → r = u ∨ r = h ∨ r ∈ leafNbrs G b)
    {γ : ℕ} (hcnt : ((leafNbrs G b).filter (fun p => ψ p = γ)).card +
      ([ψ h, ψ u] : List ℕ).count γ = 1) :
    ∃ y, G.Adj b y ∧ ∀ z, G.Adj b z → ψ z = ψ y → z = y := by
  classical
  by_cases h1 : ((leafNbrs G b).filter (fun p => ψ p = γ)).card = 1
  · have hlist0 : ([ψ h, ψ u] : List ℕ).count γ = 0 := by omega
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hlist0
    have hψh : ψ h ≠ γ := by intro heq; rw [heq] at hlist0; simp only [ite_true] at hlist0; omega
    have hψu : ψ u ≠ γ := by intro heq; rw [heq] at hlist0; simp only [ite_true] at hlist0; omega
    rcases Finset.card_eq_one.mp h1 with ⟨p₀, hp₀eq⟩
    have hp₀m : p₀ ∈ (leafNbrs G b).filter (fun p => ψ p = γ) := by rw [hp₀eq]; simp
    rw [Finset.mem_filter] at hp₀m
    refine ⟨p₀, (mem_leafNbrs.mp hp₀m.1).1, fun z hz hψz => ?_⟩
    have hψzγ : ψ z = γ := hψz.trans hp₀m.2
    rcases hall z hz with rfl | rfl | hzL
    · exact False.elim (hψu hψzγ)
    · exact False.elim (hψh hψzγ)
    · have : z ∈ (leafNbrs G b).filter (fun p => ψ p = γ) := Finset.mem_filter.mpr ⟨hzL, hψzγ⟩
      rw [hp₀eq, Finset.mem_singleton] at this
      exact this
  · have hleaf0 : ((leafNbrs G b).filter (fun p => ψ p = γ)).card = 0 := by omega
    have hlist1 : ([ψ h, ψ u] : List ℕ).count γ = 1 := by omega
    have hnoL : ∀ p ∈ leafNbrs G b, ψ p ≠ γ := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hleaf0; exact hleaf0
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hlist1
    by_cases hψh : ψ h = γ
    · have hψu : ψ u ≠ γ := by
        intro heq; simp only [hψh, heq, ite_true] at hlist1; omega
      refine ⟨h, hbh, fun z hz hψz => ?_⟩
      have hψzγ : ψ z = γ := hψz.trans hψh
      rcases hall z hz with rfl | rfl | hzL
      · exact False.elim (hψu hψzγ)
      · rfl
      · exact False.elim (hnoL z hzL hψzγ)
    · have hψu : ψ u = γ := by
        by_contra hne; simp only [hψh, hne, ite_false] at hlist1; omega
      refine ⟨u, hbu, fun z hz hψz => ?_⟩
      have hψzγ : ψ z = γ := hψz.trans hψu
      rcases hall z hz with rfl | rfl | hzL
      · rfl
      · exact False.elim (hψh hψzγ)
      · exact False.elim (hnoL z hzL hψzγ)

private lemma isT21_unpack_at {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u t₁ : V}
    (hu : IsT21 G u) (ht1 : t₁ ∈ twoThreadNbrs G u) :
    ∃ y a x : V, y ∈ leafNbrs G u ∧ a ∈ oneThreadNbrs G u ∧ x ∈ goodNbrs G u ∧
      t₁ ≠ y ∧ t₁ ≠ a ∧ t₁ ≠ x ∧ y ≠ a ∧ y ≠ x ∧ a ≠ x ∧
      ∀ r, G.Adj u r → r = t₁ ∨ r = y ∨ r = a ∨ r = x := by
  classical
  rcases isT21_structure hm hpq hu with ⟨hdu4, hleaf1, _, _, h1c, _, hgood1⟩
  rcases Finset.card_eq_one.mp hleaf1 with ⟨y, hy_eq⟩
  rcases Finset.card_eq_one.mp h1c with ⟨a, ha_eq⟩
  rcases Finset.card_eq_one.mp hgood1 with ⟨x, hx_eq⟩
  have hy : y ∈ leafNbrs G u := by rw [hy_eq]; simp
  have ha : a ∈ oneThreadNbrs G u := by rw [ha_eq]; simp
  have hx : x ∈ goodNbrs G u := by rw [hx_eq]; simp
  have hdt1 : G.degree t₁ = 2 := (mem_twoThreadNbrs.mp ht1).2.1
  have hdy : G.degree y = 1 := (mem_leafNbrs.mp hy).2
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hdx : 3 ≤ G.degree x := deg_ge_three_of_isGood (mem_goodNbrs.mp hx).2
  have ht1y : t₁ ≠ y := ne_of_deg_eq_ne hdt1 hdy (by omega)
  have ht1a : t₁ ≠ a := by
    intro h; subst h
    exact not_oneThread_and_longThread (mem_oneThreadNbrs.mp ha)
      (by rcases mem_twoThreadNbrs.mp ht1 with ⟨h1, h2, z, _, h3, h4, h5, _⟩
          exact ⟨h1, h2, z, h3, h4, h5⟩)
  have ht1x : t₁ ≠ x := (ne_of_deg_ge_lt hdx hdt1 (by omega)).symm
  have hya : y ≠ a := ne_of_deg_eq_ne hdy hda (by omega)
  have hyx : y ≠ x := (ne_of_deg_ge_lt hdx hdy (by omega)).symm
  have hax : a ≠ x := (ne_of_deg_ge_lt hdx hda (by omega)).symm
  have hN : G.neighborFinset u = {t₁, y, a, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (G.mem_neighborFinset u r).mpr (mem_twoThreadNbrs.mp ht1).1
      · exact (G.mem_neighborFinset u r).mpr (mem_leafNbrs.mp hy).1
      · exact (G.mem_neighborFinset u r).mpr (mem_oneThreadNbrs.mp ha).1
      · exact (G.mem_neighborFinset u r).mpr (mem_goodNbrs.mp hx).1
    · rw [Finset.card_insert_of_notMem (by simp [ht1y, ht1a, ht1x]),
          Finset.card_insert_of_notMem (by simp [hya, hyx]),
          Finset.card_pair hax, SimpleGraph.card_neighborFinset_eq_degree, hdu4]
  refine ⟨y, a, x, hy, ha, hx, ht1y, ht1a, ht1x, hya, hyx, hax, fun r hr => ?_⟩
  have hmem : r ∈ ({t₁, y, a, x} : Finset V) := by
    rw [← hN]; exact (G.mem_neighborFinset u r).mpr hr
  simpa using hmem

private lemma isT21_unpack_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsT21 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ y t₁ x : V, y ∈ leafNbrs G u ∧ t₁ ∈ twoThreadNbrs G u ∧ x ∈ goodNbrs G u ∧
      a ≠ y ∧ a ≠ t₁ ∧ a ≠ x ∧ y ≠ t₁ ∧ y ≠ x ∧ t₁ ≠ x ∧
      ∀ r, G.Adj u r → r = a ∨ r = y ∨ r = t₁ ∨ r = x := by
  rcases isT21_structure hm hpq hu with ⟨_, _, _, ht2c, h1c, _, _⟩
  rcases Finset.card_eq_one.mp ht2c with ⟨t₁, ht1_eq⟩
  have ht1 : t₁ ∈ twoThreadNbrs G u := by rw [ht1_eq]; simp
  rcases isT21_unpack_at hm hpq hu ht1 with
    ⟨y, a', x, hy, ha', hx, ht1y, ht1a', ht1x, hya', hyx, ha'x, hall⟩
  rcases Finset.card_eq_one.mp h1c with ⟨a₀, ha₀_eq⟩
  have haeq : a' = a := by
    have h1 : a' = a₀ := by simpa [ha₀_eq] using ha'
    have h2 : a = a₀ := by simpa [ha₀_eq] using ha
    exact h1.trans h2.symm
  subst haeq
  refine ⟨y, t₁, x, hy, ht1, hx, hya'.symm, ht1a'.symm, ha'x, ht1y.symm, hyx, ht1x, fun r hr => ?_⟩
  rcases hall r hr with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))

private lemma isL3_unpack_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u a : V}
    (hu : IsL3 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ a₂ a₃ : V, a₂ ∈ oneThreadNbrs G u ∧ a₃ ∈ oneThreadNbrs G u ∧
      a ≠ a₂ ∧ a ≠ a₃ ∧ a₂ ≠ a₃ ∧ ∀ r, G.Adj u r → r = a ∨ r = a₂ ∨ r = a₃ := by
  classical
  rcases isL3_structure hm hu with ⟨_, _, _, hN, _, _⟩
  have hc : (oneThreadNbrs G u \ {a}).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter (oneThreadNbrs G u) {a}
    have hI : oneThreadNbrs G u ∩ {a} = {a} := by ext x; simp [ha]
    rw [hI, Finset.card_singleton, hu.2] at h; omega
  rcases Finset.card_eq_two.mp hc with ⟨a₂, a₃, h23, hpair⟩
  have ha2m : a₂ ∈ oneThreadNbrs G u \ {a} := by rw [hpair]; simp
  have ha3m : a₃ ∈ oneThreadNbrs G u \ {a} := by rw [hpair]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at ha2m ha3m
  refine ⟨a₂, a₃, ha2m.1, ha3m.1, Ne.symm ha2m.2, Ne.symm ha3m.2, h23, fun r hr => ?_⟩
  have hr1 : r ∈ oneThreadNbrs G u := by rw [← hN]; exact (G.mem_neighborFinset u r).mpr hr
  by_cases hra : r = a
  · exact Or.inl hra
  · have hrm : r ∈ ({a₂, a₃} : Finset V) := by
      rw [← hpair]; exact Finset.mem_sdiff.mpr ⟨hr1, by simp [hra]⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrm
    rcases hrm with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private lemma isB3_unpack_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsB3 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ a₂ b h : V, a₂ ∈ oneThreadNbrs G u ∧ b ∈ badNbrs G u ∧
      a ≠ a₂ ∧ a ≠ b ∧ a₂ ≠ b ∧ (∀ r, G.Adj u r → r = a ∨ r = a₂ ∨ r = b) ∧
      G.Adj b h ∧ h ≠ u ∧ 3 ≤ G.degree h ∧ coreNbrs G b = {u, h} ∧
      (∀ r, G.Adj b r → r = u ∨ r = h ∨ r ∈ leafNbrs G b) := by
  classical
  rcases isB3_structure hm hpq hu with ⟨hdu3, _, _, h1c, hbc, _, _, hN⟩
  have hc1 : (oneThreadNbrs G u \ {a}).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter (oneThreadNbrs G u) {a}
    have hI : oneThreadNbrs G u ∩ {a} = {a} := by ext x; simp [ha]
    rw [hI, Finset.card_singleton, h1c] at h; omega
  rcases Finset.card_eq_one.mp hc1 with ⟨a₂, ha2_eq⟩
  have ha2m : a₂ ∈ oneThreadNbrs G u \ {a} := by rw [ha2_eq]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at ha2m
  rcases Finset.card_eq_one.mp hbc with ⟨b, hb_eq⟩
  have hbm : b ∈ badNbrs G u := by rw [hb_eq]; simp
  rcases mem_badNbrs.mp hbm with ⟨hub, hbad⟩
  have hab : a ≠ b :=
    (ne_of_deg_ge_lt hbad.1 (mem_oneThreadNbrs.mp ha).2.1 (by omega)).symm
  have ha2b : a₂ ≠ b :=
    (ne_of_deg_ge_lt hbad.1 (mem_oneThreadNbrs.mp ha2m.1).2.1 (by omega)).symm
  have hu_coreb : u ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hub.symm, by omega⟩
  have hb_other : (coreNbrs G b \ {u}).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter (coreNbrs G b) {u}
    have hI : coreNbrs G b ∩ {u} = {u} := by ext x; simp [hu_coreb]
    rw [hI, Finset.card_singleton] at h; have := hbad.2; unfold coreDeg at this; omega
  rcases Finset.card_eq_one.mp hb_other with ⟨h, hh_eq⟩
  have hhm : h ∈ coreNbrs G b \ {u} := by rw [hh_eq]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hhm
  have hbh : G.Adj b h := (mem_coreNbrs.mp hhm.1).1
  have hdh3 : 3 ≤ G.degree h := bad_coreNbrs_deg_ge_three hm hpq hbad hhm.1
  have hcoreb : coreNbrs G b = {u, h} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hu_coreb
      · exact hhm.1
    · rw [Finset.card_pair (Ne.symm hhm.2)]; have := hbad.2; unfold coreDeg at this; omega
  refine ⟨a₂, b, h, ha2m.1, hbm, Ne.symm ha2m.2, hab, ha2b, fun r hr => ?_,
    hbh, hhm.2, hdh3, hcoreb, fun r hr => ?_⟩
  · have hrN : r ∈ oneThreadNbrs G u ∪ badNbrs G u := by
      rw [← hN]; exact (G.mem_neighborFinset u r).mpr hr
    rw [Finset.mem_union] at hrN
    rcases hrN with hr1 | hrb
    · by_cases hra : r = a
      · exact Or.inl hra
      · have : r ∈ ({a₂} : Finset V) := by
          rw [← ha2_eq]; exact Finset.mem_sdiff.mpr ⟨hr1, by simp [hra]⟩
        exact Or.inr (Or.inl (Finset.mem_singleton.mp this))
    · rw [hb_eq, Finset.mem_singleton] at hrb; exact Or.inr (Or.inr hrb)
  · have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcoreb, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

private lemma isL4_unpack_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsL4 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ y a₂ a₃ : V, y ∈ leafNbrs G u ∧ a₂ ∈ oneThreadNbrs G u ∧ a₃ ∈ oneThreadNbrs G u ∧
      a ≠ y ∧ a ≠ a₂ ∧ a ≠ a₃ ∧ y ≠ a₂ ∧ y ≠ a₃ ∧ a₂ ≠ a₃ ∧
      ∀ r, G.Adj u r → r = a ∨ r = y ∨ r = a₂ ∨ r = a₃ := by
  classical
  rcases isL4_structure hm hpq hu with ⟨_, _, hleaf1, h1c, _, _, _, _, hN⟩
  rcases Finset.card_eq_one.mp hleaf1 with ⟨y, hy_eq⟩
  have hy : y ∈ leafNbrs G u := by rw [hy_eq]; simp
  have hc : (oneThreadNbrs G u \ {a}).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter (oneThreadNbrs G u) {a}
    have hI : oneThreadNbrs G u ∩ {a} = {a} := by ext x; simp [ha]
    rw [hI, Finset.card_singleton, h1c] at h; omega
  rcases Finset.card_eq_two.mp hc with ⟨a₂, a₃, h23, hpair⟩
  have ha2m : a₂ ∈ oneThreadNbrs G u \ {a} := by rw [hpair]; simp
  have ha3m : a₃ ∈ oneThreadNbrs G u \ {a} := by rw [hpair]; simp
  rw [Finset.mem_sdiff, Finset.mem_singleton] at ha2m ha3m
  have hay : a ≠ y :=
    ne_of_deg_eq_ne (mem_oneThreadNbrs.mp ha).2.1 (mem_leafNbrs.mp hy).2 (by omega)
  have hya2 : y ≠ a₂ :=
    ne_of_deg_eq_ne (mem_leafNbrs.mp hy).2 (mem_oneThreadNbrs.mp ha2m.1).2.1 (by omega)
  have hya3 : y ≠ a₃ :=
    ne_of_deg_eq_ne (mem_leafNbrs.mp hy).2 (mem_oneThreadNbrs.mp ha3m.1).2.1 (by omega)
  refine ⟨y, a₂, a₃, hy, ha2m.1, ha3m.1, hay, Ne.symm ha2m.2, Ne.symm ha3m.2, hya2, hya3, h23,
    fun r hr => ?_⟩
  have hrN : r ∈ oneThreadNbrs G u ∪ leafNbrs G u := by
    rw [← hN]; exact (G.mem_neighborFinset u r).mpr hr
  rw [Finset.mem_union] at hrN
  rcases hrN with hr1 | hrl
  · by_cases hra : r = a
    · exact Or.inl hra
    · have hrm : r ∈ ({a₂, a₃} : Finset V) := by
        rw [← hpair]; exact Finset.mem_sdiff.mpr ⟨hr1, by simp [hra]⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrm
      rcases hrm with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · rw [hy_eq, Finset.mem_singleton] at hrl; exact Or.inr (Or.inl hrl)

private lemma hasUniqueColor_quad_perm_4123 {a b c d : ℕ}
    (h : HasUniqueColor [a, b, c, d]) : HasUniqueColor [d, b, c, a] := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx ⊢
  omega

private lemma hasUniqueColor_quad_perm_3421 {a b c d : ℕ}
    (h : HasUniqueColor [a, b, c, d]) : HasUniqueColor [c, d, b, a] := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx ⊢
  omega

private lemma hasUniqueColor_quad_perm_4321 {a b c d : ℕ}
    (h : HasUniqueColor [a, b, c, d]) : HasUniqueColor [d, c, b, a] := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hx ⊢
  omega

/-- 两个由 `2`-线串相连的 `T21` 顶点的局部结构数据。 -/
private structure T21TwoData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  t₁ : V
  t₂ : V
  y₁ : V
  a₁ : V
  x₁ : V
  p₁ : V
  y₂ : V
  a₂ : V
  x₂ : V
  p₂ : V
  huv : u ≠ v
  hut1 : G.Adj u t₁
  hdt1 : G.degree t₁ = 2
  ht12 : G.Adj t₁ t₂
  ht2u : t₂ ≠ u
  hdt2 : G.degree t₂ = 2
  ht2v : G.Adj t₂ v
  hvt1 : v ≠ t₁
  hdu4 : G.degree u = 4
  hdv4 : G.degree v = 4
  huy1 : G.Adj u y₁
  hdy1 : G.degree y₁ = 1
  hua1 : G.Adj u a₁
  hda1 : G.degree a₁ = 2
  ha1p1 : G.Adj a₁ p₁
  hp1u : p₁ ≠ u
  hdp1 : 3 ≤ G.degree p₁
  hux1 : G.Adj u x₁
  hdx1 : 3 ≤ G.degree x₁
  hvy2 : G.Adj v y₂
  hdy2 : G.degree y₂ = 1
  hva2 : G.Adj v a₂
  hda2 : G.degree a₂ = 2
  ha2p2 : G.Adj a₂ p₂
  hp2v : p₂ ≠ v
  hdp2 : 3 ≤ G.degree p₂
  hvx2 : G.Adj v x₂
  hdx2 : 3 ≤ G.degree x₂
  ht1y1 : t₁ ≠ y₁
  ht1a1 : t₁ ≠ a₁
  ht1x1 : t₁ ≠ x₁
  hy1a1 : y₁ ≠ a₁
  hy1x1 : y₁ ≠ x₁
  ha1x1 : a₁ ≠ x₁
  ht2y2 : t₂ ≠ y₂
  ht2a2 : t₂ ≠ a₂
  ht2x2 : t₂ ≠ x₂
  hy2a2 : y₂ ≠ a₂
  hy2x2 : y₂ ≠ x₂
  ha2x2 : a₂ ≠ x₂
  hu_all : ∀ r, G.Adj u r → r = t₁ ∨ r = y₁ ∨ r = a₁ ∨ r = x₁
  hv_all : ∀ r, G.Adj v r → r = t₂ ∨ r = y₂ ∨ r = a₂ ∨ r = x₂
  ht1_all : ∀ r, G.Adj t₁ r → r = u ∨ r = t₂
  ht2_all : ∀ r, G.Adj t₂ r → r = t₁ ∨ r = v
  ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = p₁
  ha2_all : ∀ r, G.Adj a₂ r → r = v ∨ r = p₂
  ha1_ne_t2 : a₁ ≠ t₂
  ha2_ne_t1 : a₂ ≠ t₁
  hy1_ne_y2 : y₁ ≠ y₂
  ha1_eq_of_p1v : p₁ = v → a₁ = a₂
  ha1_eq_of_p2u : p₂ = u → a₁ = a₂

private def T21TwoData.swap {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : T21TwoData G) : T21TwoData G where
  u := D.v
  v := D.u
  t₁ := D.t₂
  t₂ := D.t₁
  y₁ := D.y₂
  a₁ := D.a₂
  x₁ := D.x₂
  p₁ := D.p₂
  y₂ := D.y₁
  a₂ := D.a₁
  x₂ := D.x₁
  p₂ := D.p₁
  huv := D.huv.symm
  hut1 := D.ht2v.symm
  hdt1 := D.hdt2
  ht12 := D.ht12.symm
  ht2u := D.hvt1.symm
  hdt2 := D.hdt1
  ht2v := D.hut1.symm
  hvt1 := D.ht2u.symm
  hdu4 := D.hdv4
  hdv4 := D.hdu4
  huy1 := D.hvy2
  hdy1 := D.hdy2
  hua1 := D.hva2
  hda1 := D.hda2
  ha1p1 := D.ha2p2
  hp1u := D.hp2v
  hdp1 := D.hdp2
  hux1 := D.hvx2
  hdx1 := D.hdx2
  hvy2 := D.huy1
  hdy2 := D.hdy1
  hva2 := D.hua1
  hda2 := D.hda1
  ha2p2 := D.ha1p1
  hp2v := D.hp1u
  hdp2 := D.hdp1
  hvx2 := D.hux1
  hdx2 := D.hdx1
  ht1y1 := D.ht2y2
  ht1a1 := D.ht2a2
  ht1x1 := D.ht2x2
  hy1a1 := D.hy2a2
  hy1x1 := D.hy2x2
  ha1x1 := D.ha2x2
  ht2y2 := D.ht1y1
  ht2a2 := D.ht1a1
  ht2x2 := D.ht1x1
  hy2a2 := D.hy1a1
  hy2x2 := D.hy1x1
  ha2x2 := D.ha1x1
  hu_all := D.hv_all
  hv_all := D.hu_all
  ht1_all := fun r hr => (D.ht2_all r hr).symm
  ht2_all := fun r hr => (D.ht1_all r hr).symm
  ha1_all := D.ha2_all
  ha2_all := D.ha1_all
  ha1_ne_t2 := D.ha2_ne_t1
  ha2_ne_t1 := D.ha1_ne_t2
  hy1_ne_y2 := D.hy1_ne_y2.symm
  ha1_eq_of_p1v := fun h => (D.ha1_eq_of_p2u h).symm
  ha1_eq_of_p2u := fun h => (D.ha1_eq_of_p1v h).symm

private lemma T21TwoData.S_out {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : T21TwoData G)
    {w s : V} (hwS : w ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V))
    (hsS : s ∈ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V)) (hws : G.Adj w s) :
    (s = D.u ∧ w = D.x₁) ∨ (s = D.v ∧ w = D.x₂) ∨
      (s = D.a₁ ∧ w = D.p₁) ∨ (s = D.a₂ ∧ w = D.p₂) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
  rcases hsS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases D.hu_all w hws.symm with rfl | rfl | rfl | rfl
    · exact False.elim (hwS (by simp))
    · exact False.elim (hwS (by simp))
    · exact False.elim (hwS (by simp))
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases D.hv_all w hws.symm with rfl | rfl | rfl | rfl
    · exact False.elim (hwS (by simp))
    · exact False.elim (hwS (by simp))
    · exact False.elim (hwS (by simp))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases D.ht1_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp))
  · rcases D.ht2_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp))
  · rcases exists_unique_neighbor_of_deg_one D.hdy1 with ⟨z, _, huniq⟩
    have hwu : w = D.u := (huniq w hws.symm).trans (huniq D.u D.huy1.symm).symm
    exact False.elim (hwS (by rw [hwu]; simp))
  · rcases exists_unique_neighbor_of_deg_one D.hdy2 with ⟨z, _, huniq⟩
    have hwv : w = D.v := (huniq w hws.symm).trans (huniq D.v D.hvy2.symm).symm
    exact False.elim (hwS (by rw [hwv]; simp))
  · rcases D.ha1_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rcases D.ha2_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- 引理 5 子情形 A：`G.Adj u v` 且 `a₁ = a₂`。 -/
private lemma no_T21_two_thread_adj_same {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hadj : G.Adj D.u D.v) (ha12 : D.a₁ = D.a₂) : False := by
  classical
  have hx1_eq : D.x₁ = D.v := by
    rcases D.hu_all D.v hadj with h | h | h | h
    · exact False.elim (D.hvt1 h)
    · exact False.elim (ne_of_deg_eq_ne D.hdv4 D.hdy1 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne D.hdv4 D.hda1 (by omega) h)
    · exact h.symm
  have hx2_eq : D.x₂ = D.u := by
    rcases D.hv_all D.u hadj.symm with h | h | h | h
    · exact False.elim (D.ht2u.symm h)
    · exact False.elim (ne_of_deg_eq_ne D.hdu4 D.hdy2 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne D.hdu4 D.hda2 (by omega) h)
    · exact h.symm
  have hp1_eq : D.p₁ = D.v := by
    rcases D.ha1_all D.v (ha12 ▸ D.hva2.symm) with h | h
    · exact False.elim (D.huv h.symm)
    · exact h.symm
  have hp2_eq : D.p₂ = D.u := by
    rcases D.ha2_all D.u (ha12 ▸ D.hua1.symm) with h | h
    · exact False.elim (D.huv h)
    · exact h.symm
  let S : Finset V := {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂}
  rcases exists_admissible_coloring hm (S := S) ⟨D.u, by simp [S]⟩ with ⟨adm⟩
  have hLu5 : (L D.u).card = 5 := by rw [hm.list_card D.u]; simp [kappa, D.hdu4]
  have hLv5 : (L D.v).card = 5 := by rw [hm.list_card D.v]; simp [kappa, D.hdv4]
  have hLy1 : (L D.y₁).card = 2 := by rw [hm.list_card D.y₁]; simp [kappa, D.hdy1]
  have hLy2 : (L D.y₂).card = 2 := by rw [hm.list_card D.y₂]; simp [kappa, D.hdy2]
  have hLt1 : (L D.t₁).card = 4 := by rw [hm.list_card D.t₁]; simp [kappa, D.hdt1]
  have hLt2 : (L D.t₂).card = 4 := by rw [hm.list_card D.t₂]; simp [kappa, D.hdt2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  rcases exists_mem_sdiff_of_lt (A := L D.u) (B := L D.y₁) (by omega) with ⟨α, hαL, hαy1⟩
  rcases exists_mem_sdiff_of_lt (A := L D.v) (B := insert α (L D.y₂))
    (by have := Finset.card_insert_le α (L D.y₂); omega) with ⟨β, hβL, hβN⟩
  rw [Finset.mem_insert, not_or] at hβN
  rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨ca, hcaL, hcaN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcaN
  rcases exists_mem_sdiff_of_lt (A := L D.t₁) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨ct1, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_mem_sdiff_of_lt (A := L D.t₂) (B := {α, β, ct1})
    (by have := card_triple_le α β ct1; omega) with ⟨ct2, hct2L, hct2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct2N
  rcases exists_fourth_unique_color (a := β) (b := ca) (c := ct1) (by omega : 2 ≤ (L D.y₁).card)
    with ⟨cy1, hcy1L, huniq_u⟩
  rcases exists_fourth_unique_color (a := α) (b := ca) (c := ct2) (by omega : 2 ≤ (L D.y₂).card)
    with ⟨cy2, hcy2L, huniq_v⟩
  have hcy1α : cy1 ≠ α := fun h => hαy1 (h ▸ hcy1L)
  have hcy2β : cy2 ≠ β := fun h => hβN.2 (h ▸ hcy2L)
  let ψ : V → ℕ := fun z =>
    if z = D.u then α else if z = D.v then β else if z = D.t₁ then ct1 else if z = D.t₂ then ct2
    else if z = D.y₁ then cy1 else if z = D.y₂ then cy2 else if z = D.a₁ then ca else adm.φ z
  have hψu : ψ D.u = α := by simp [ψ]
  have hψv : ψ D.v = β := by simp [ψ, D.huv.symm]
  have hψt1 : ψ D.t₁ = ct1 := by simp [ψ, (G.ne_of_adj D.hut1).symm, D.hvt1.symm]
  have hψt2 : ψ D.t₂ = ct2 := by
    simp [ψ, D.ht2u, G.ne_of_adj D.ht2v, (G.ne_of_adj D.ht12).symm]
  have hψy1 : ψ D.y₁ = cy1 := by
    simp [ψ, (G.ne_of_adj D.huy1).symm, ne_of_deg_eq_ne D.hdy1 D.hdv4 (by omega),
      D.ht1y1.symm, ne_of_deg_eq_ne D.hdy1 D.hdt2 (by omega)]
  have hψy2 : ψ D.y₂ = cy2 := by
    simp [ψ, ne_of_deg_eq_ne D.hdy2 D.hdu4 (by omega), (G.ne_of_adj D.hvy2).symm,
      ne_of_deg_eq_ne D.hdy2 D.hdt1 (by omega), D.ht2y2.symm, D.hy1_ne_y2.symm]
  have hψa1 : ψ D.a₁ = ca := by
    simp [ψ, (G.ne_of_adj D.hua1).symm, ne_of_deg_eq_ne D.hda1 D.hdv4 (by omega),
      D.ht1a1.symm, D.ha1_ne_t2, D.hy1a1.symm, ne_of_deg_eq_ne D.hda1 D.hdy2 (by omega)]
  have hno_out : ∀ w, w ∉ S → ∀ s ∈ S, ¬ G.Adj w s := by
    intro w hwS s hsS hws
    rcases D.S_out hwS hsS hws with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact hwS (by rw [h, hx1_eq]; simp [S])
    · exact hwS (by rw [h, hx2_eq]; simp [S])
    · exact hwS (by rw [h, hp1_eq]; simp [S])
    · exact hwS (by rw [h, hp2_eq]; simp [S])
  apply adm.contradiction hm ψ (fun z hz => by
    simp only [S, ha12, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      ha12 ▸ hz.2.2.2.2.2.2.1, ite_false])
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψt1]; exact hct1L
    · rw [hψt2]; exact hct2L
    · rw [hψy1]; exact hcy1L
    · rw [hψy2]; exact hcy2L
    · rw [hψa1]; exact hcaL
    · rw [← ha12, hψa1]; exact hcaL
  · intro z₁ z₂ h12 hor
    have hcase : ∀ a b, G.Adj a b → a ∈ S → ψ a ≠ ψ b := by
      intro a b hab haS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at haS
      rcases haS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all b hab with rfl | rfl | rfl | rfl
        · rw [hψu, hψt1]; exact Ne.symm hct1N.1
        · rw [hψu, hψy1]; exact Ne.symm hcy1α
        · rw [hψu, hψa1]; exact Ne.symm hcaN.1
        · rw [hx1_eq, hψu, hψv]; exact Ne.symm hβN.1
      · rcases D.hv_all b hab with rfl | rfl | rfl | rfl
        · rw [hψv, hψt2]; exact Ne.symm hct2N.2.1
        · rw [hψv, hψy2]; exact Ne.symm hcy2β
        · rw [← ha12, hψv, hψa1]; exact Ne.symm hcaN.2
        · rw [hx2_eq, hψv, hψu]; exact hβN.1
      · rcases D.ht1_all b hab with rfl | rfl
        · rw [hψt1, hψu]; exact hct1N.1
        · rw [hψt1, hψt2]; exact Ne.symm hct2N.2.2
      · rcases D.ht2_all b hab with rfl | rfl
        · rw [hψt2, hψt1]; exact hct2N.2.2
        · rw [hψt2, hψv]; exact hct2N.2.1
      · rcases exists_unique_neighbor_of_deg_one D.hdy1 with ⟨w, _, huniq⟩
        have hbu : b = D.u := (huniq b hab).trans (huniq D.u D.huy1.symm).symm
        rw [hbu, hψy1, hψu]; exact hcy1α
      · rcases exists_unique_neighbor_of_deg_one D.hdy2 with ⟨w, _, huniq⟩
        have hbv : b = D.v := (huniq b hab).trans (huniq D.v D.hvy2.symm).symm
        rw [hbv, hψy2, hψv]; exact hcy2β
      · rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hcaN.1
        · rw [hp1_eq, hψa1, hψv]; exact hcaN.2
      · rw [← ha12] at hab ⊢
        rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hcaN.1
        · rw [hp1_eq, hψa1, hψv]; exact hcaN.2
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12 h1
    · exact (hcase z₂ z₁ h12.symm h2).symm
  · intro w hwS _ s hsS hws; exact False.elim (hno_out w hwS s hsS hws)
  · intro w hwS hiso ⟨s, hws⟩
    have hsS : s ∈ S := by by_contra h; exact hiso s h hws
    exact False.elim (hno_out w hwS s hsS hws)
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_four D.hut1 D.huy1 D.hua1 D.hux1 D.hu_all
        (by rw [hψt1, hψy1, hψa1, hx1_eq, hψv]; exact hasUniqueColor_quad_perm_3421 huniq_u)
    · exact pcf_at_of_hasUniqueColor_four D.ht2v.symm D.hvy2 D.hva2 D.hvx2 D.hv_all
        (by rw [hψt2, hψy2, ← ha12, hψa1, hx2_eq, hψu]; exact hasUniqueColor_quad_perm_3421 huniq_v)
    · exact pcf_at_of_two_distinct_neighbors D.hdt1 D.hut1.symm D.ht12 D.ht2u.symm
        (by rw [hψu, hψt2]; exact Ne.symm hct2N.1)
    · exact pcf_at_of_two_distinct_neighbors D.hdt2 D.ht12.symm D.ht2v D.hvt1.symm
        (by rw [hψt1, hψv]; exact hct1N.2)
    · exact pcf_at_deg_one D.hdy1 D.huy1.symm
    · exact pcf_at_deg_one D.hdy2 D.hvy2.symm
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hp1_eq, hψu, hψv]; exact Ne.symm hβN.1)
    · rw [← ha12]
      exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hp1_eq, hψu, hψv]; exact Ne.symm hβN.1)

/-- 引理 5 子情形 B：`G.Adj u v` 且 `a₁ ≠ a₂`。 -/
private lemma no_T21_two_thread_adj_diff {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hadj : G.Adj D.u D.v) (ha12 : D.a₁ ≠ D.a₂) : False := by
  classical
  have hx1_eq : D.x₁ = D.v := by
    rcases D.hu_all D.v hadj with h | h | h | h
    · exact False.elim (D.hvt1 h)
    · exact False.elim (ne_of_deg_eq_ne D.hdv4 D.hdy1 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne D.hdv4 D.hda1 (by omega) h)
    · exact h.symm
  have hx2_eq : D.x₂ = D.u := by
    rcases D.hv_all D.u hadj.symm with h | h | h | h
    · exact False.elim (D.ht2u.symm h)
    · exact False.elim (ne_of_deg_eq_ne D.hdu4 D.hdy2 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne D.hdu4 D.hda2 (by omega) h)
    · exact h.symm
  have hp1v : D.p₁ ≠ D.v := fun h => ha12 (D.ha1_eq_of_p1v h)
  have hp2u : D.p₂ ≠ D.u := fun h => ha12 (D.ha1_eq_of_p2u h)
  let S : Finset V := {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂}
  have hp1S : D.p₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.hp1u, hp1v, ne_of_deg_ge_lt D.hdp1 D.hdt1 (by omega),
      ne_of_deg_ge_lt D.hdp1 D.hdt2 (by omega), ne_of_deg_ge_lt D.hdp1 D.hdy1 (by omega),
      ne_of_deg_ge_lt D.hdp1 D.hdy2 (by omega), (G.ne_of_adj D.ha1p1).symm,
      ne_of_deg_ge_lt D.hdp1 D.hda2 (by omega)⟩
  have hp2S : D.p₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp2u, D.hp2v, ne_of_deg_ge_lt D.hdp2 D.hdt1 (by omega),
      ne_of_deg_ge_lt D.hdp2 D.hdt2 (by omega), ne_of_deg_ge_lt D.hdp2 D.hdy1 (by omega),
      ne_of_deg_ge_lt D.hdp2 D.hdy2 (by omega), ne_of_deg_ge_lt D.hdp2 D.hda1 (by omega),
      (G.ne_of_adj D.ha2p2).symm⟩
  have hS_out' : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s →
      (s = D.a₁ ∧ w = D.p₁) ∨ (s = D.a₂ ∧ w = D.p₂) := by
    intro w hwS s hsS hws
    rcases D.S_out hwS hsS hws with ⟨_, h⟩ | ⟨_, h⟩ | h | h
    · exact False.elim (hwS (by rw [h, hx1_eq]; simp [S]))
    · exact False.elim (hwS (by rw [h, hx2_eq]; simp [S]))
    · exact Or.inl h
    · exact Or.inr h
  have hnoniso : ∀ w, w ∉ S → (∃ s ∈ S, G.Adj w s) → ∃ r, r ∉ S ∧ G.Adj w r := by
    intro w hwS ⟨s, hsS, hws⟩
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out' w hwS s hsS hws with ⟨_, h⟩ | ⟨_, h⟩
      · rw [h]; exact D.hdp1
      · rw [h]; exact D.hdp2
    rcases exists_mem_sdiff_of_lt (A := G.neighborFinset w) (B := {D.a₁, D.a₂})
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]
          have := Finset.card_le_two (a := D.a₁) (b := D.a₂); omega) with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, fun hrS => ?_, hr⟩
    rcases hS_out' w hwS r hrS hr with ⟨h, _⟩ | ⟨h, _⟩
    · exact hrn.1 h
    · exact hrn.2 h
  rcases exists_admissible_coloring hm (S := S) ⟨D.u, by simp [S]⟩ with ⟨adm⟩
  have hLu5 : (L D.u).card = 5 := by rw [hm.list_card D.u]; simp [kappa, D.hdu4]
  have hLv5 : (L D.v).card = 5 := by rw [hm.list_card D.v]; simp [kappa, D.hdv4]
  have hLy1 : (L D.y₁).card = 2 := by rw [hm.list_card D.y₁]; simp [kappa, D.hdy1]
  have hLy2 : (L D.y₂).card = 2 := by rw [hm.list_card D.y₂]; simp [kappa, D.hdy2]
  have hLt1 : (L D.t₁).card = 4 := by rw [hm.list_card D.t₁]; simp [kappa, D.hdt1]
  have hLt2 : (L D.t₂).card = 4 := by rw [hm.list_card D.t₂]; simp [kappa, D.hdt2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  have hLa2 : (L D.a₂).card = 4 := by rw [hm.list_card D.a₂]; simp [kappa, D.hda2]
  rcases exists_mem_sdiff_of_lt (A := L D.u) (B := insert (adm.φ D.p₁) (L D.y₁))
    (by have := Finset.card_insert_le (adm.φ D.p₁) (L D.y₁); omega) with ⟨α, hαL, hαN⟩
  rw [Finset.mem_insert, not_or] at hαN
  rcases exists_mem_sdiff_of_lt (A := L D.v) (B := insert α (insert (adm.φ D.p₂) (L D.y₂)))
    (by have := Finset.card_insert_le α (insert (adm.φ D.p₂) (L D.y₂))
        have := Finset.card_insert_le (adm.φ D.p₂) (L D.y₂); omega) with ⟨β, hβL, hβN⟩
  simp only [Finset.mem_insert, not_or] at hβN
  rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {adm.φ D.p₁, adm.φs D.p₁, α})
    (by have := card_triple_le (adm.φ D.p₁) (adm.φs D.p₁) α; omega) with ⟨ca1, hca1L, hca1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca1N
  rcases exists_mem_sdiff_of_lt (A := L D.a₂) (B := {adm.φ D.p₂, adm.φs D.p₂, β})
    (by have := card_triple_le (adm.φ D.p₂) (adm.φs D.p₂) β; omega) with ⟨ca2, hca2L, hca2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca2N
  rcases exists_mem_sdiff_of_lt (A := L D.t₁) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨ct1, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_mem_sdiff_of_lt (A := L D.t₂) (B := {α, β, ct1})
    (by have := card_triple_le α β ct1; omega) with ⟨ct2, hct2L, hct2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct2N
  rcases exists_fourth_unique_color (a := β) (b := ca1) (c := ct1) (by omega : 2 ≤ (L D.y₁).card)
    with ⟨cy1, hcy1L, huniq_u⟩
  rcases exists_fourth_unique_color (a := α) (b := ca2) (c := ct2) (by omega : 2 ≤ (L D.y₂).card)
    with ⟨cy2, hcy2L, huniq_v⟩
  have hcy1α : cy1 ≠ α := fun h => hαN.2 (h ▸ hcy1L)
  have hcy2β : cy2 ≠ β := fun h => hβN.2.2 (h ▸ hcy2L)
  let ψ : V → ℕ := fun z =>
    if z = D.u then α else if z = D.v then β else if z = D.t₁ then ct1 else if z = D.t₂ then ct2
    else if z = D.y₁ then cy1 else if z = D.y₂ then cy2
    else if z = D.a₁ then ca1 else if z = D.a₂ then ca2 else adm.φ z
  have hψu : ψ D.u = α := by simp [ψ]
  have hψv : ψ D.v = β := by simp [ψ, D.huv.symm]
  have hψt1 : ψ D.t₁ = ct1 := by simp [ψ, (G.ne_of_adj D.hut1).symm, D.hvt1.symm]
  have hψt2 : ψ D.t₂ = ct2 := by
    simp [ψ, D.ht2u, G.ne_of_adj D.ht2v, (G.ne_of_adj D.ht12).symm]
  have hψy1 : ψ D.y₁ = cy1 := by
    simp [ψ, (G.ne_of_adj D.huy1).symm, ne_of_deg_eq_ne D.hdy1 D.hdv4 (by omega),
      D.ht1y1.symm, ne_of_deg_eq_ne D.hdy1 D.hdt2 (by omega)]
  have hψy2 : ψ D.y₂ = cy2 := by
    simp [ψ, ne_of_deg_eq_ne D.hdy2 D.hdu4 (by omega), (G.ne_of_adj D.hvy2).symm,
      ne_of_deg_eq_ne D.hdy2 D.hdt1 (by omega), D.ht2y2.symm, D.hy1_ne_y2.symm]
  have hψa1 : ψ D.a₁ = ca1 := by
    simp [ψ, (G.ne_of_adj D.hua1).symm, ne_of_deg_eq_ne D.hda1 D.hdv4 (by omega),
      D.ht1a1.symm, D.ha1_ne_t2, D.hy1a1.symm, ne_of_deg_eq_ne D.hda1 D.hdy2 (by omega)]
  have hψa2 : ψ D.a₂ = ca2 := by
    simp [ψ, ne_of_deg_eq_ne D.hda2 D.hdu4 (by omega), (G.ne_of_adj D.hva2).symm, D.ha2_ne_t1,
      D.ht2a2.symm, ne_of_deg_eq_ne D.hda2 D.hdy1 (by omega), D.hy2a2.symm, ha12.symm]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := by
    intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψt1]; exact hct1L
    · rw [hψt2]; exact hct2L
    · rw [hψy1]; exact hcy1L
    · rw [hψy2]; exact hcy2L
    · rw [hψa1]; exact hca1L
    · rw [hψa2]; exact hca2L
  · intro z₁ z₂ h12 hor
    have hcase : ∀ a b, G.Adj a b → a ∈ S → ψ a ≠ ψ b := by
      intro a b hab haS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at haS
      rcases haS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all b hab with rfl | rfl | rfl | rfl
        · rw [hψu, hψt1]; exact Ne.symm hct1N.1
        · rw [hψu, hψy1]; exact Ne.symm hcy1α
        · rw [hψu, hψa1]; exact Ne.symm hca1N.2.2
        · rw [hx1_eq, hψu, hψv]; exact Ne.symm hβN.1
      · rcases D.hv_all b hab with rfl | rfl | rfl | rfl
        · rw [hψv, hψt2]; exact Ne.symm hct2N.2.1
        · rw [hψv, hψy2]; exact Ne.symm hcy2β
        · rw [hψv, hψa2]; exact Ne.symm hca2N.2.2
        · rw [hx2_eq, hψv, hψu]; exact hβN.1
      · rcases D.ht1_all b hab with rfl | rfl
        · rw [hψt1, hψu]; exact hct1N.1
        · rw [hψt1, hψt2]; exact Ne.symm hct2N.2.2
      · rcases D.ht2_all b hab with rfl | rfl
        · rw [hψt2, hψt1]; exact hct2N.2.2
        · rw [hψt2, hψv]; exact hct2N.2.1
      · rcases exists_unique_neighbor_of_deg_one D.hdy1 with ⟨w, _, huniq⟩
        have hbu : b = D.u := (huniq b hab).trans (huniq D.u D.huy1.symm).symm
        rw [hbu, hψy1, hψu]; exact hcy1α
      · rcases exists_unique_neighbor_of_deg_one D.hdy2 with ⟨w, _, huniq⟩
        have hbv : b = D.v := (huniq b hab).trans (huniq D.v D.hvy2.symm).symm
        rw [hbv, hψy2, hψv]; exact hcy2β
      · rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hca1N.2.2
        · rw [hψa1, hψ_out D.p₁ hp1S]; exact hca1N.1
      · rcases D.ha2_all b hab with rfl | rfl
        · rw [hψa2, hψv]; exact hca2N.2.2
        · rw [hψa2, hψ_out D.p₂ hp2S]; exact hca2N.1
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12 h1
    · exact (hcase z₂ z₁ h12.symm h2).symm
  · intro w hwS _ s hsS hws
    rcases hS_out' w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψa1]; exact hca1N.2.1
    · rw [hψa2]; exact hca2N.2.1
  · intro w hwS hiso ⟨s, hws⟩
    have hsS : s ∈ S := by by_contra h; exact hiso s h hws
    rcases hnoniso w hwS ⟨s, hsS, hws⟩ with ⟨r, hrS, hwr⟩
    exact False.elim (hiso r hrS hwr)
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_four D.hut1 D.huy1 D.hua1 D.hux1 D.hu_all
        (by rw [hψt1, hψy1, hψa1, hx1_eq, hψv]; exact hasUniqueColor_quad_perm_3421 huniq_u)
    · exact pcf_at_of_hasUniqueColor_four D.ht2v.symm D.hvy2 D.hva2 D.hvx2 D.hv_all
        (by rw [hψt2, hψy2, hψa2, hx2_eq, hψu]; exact hasUniqueColor_quad_perm_3421 huniq_v)
    · exact pcf_at_of_two_distinct_neighbors D.hdt1 D.hut1.symm D.ht12 D.ht2u.symm
        (by rw [hψu, hψt2]; exact Ne.symm hct2N.1)
    · exact pcf_at_of_two_distinct_neighbors D.hdt2 D.ht12.symm D.ht2v D.hvt1.symm
        (by rw [hψt1, hψv]; exact hct1N.2)
    · exact pcf_at_deg_one D.hdy1 D.huy1.symm
    · exact pcf_at_deg_one D.hdy2 D.hvy2.symm
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hψu, hψ_out D.p₁ hp1S]; exact hαN.1)
    · exact pcf_at_of_two_distinct_neighbors D.hda2 D.hva2.symm D.ha2p2 D.hp2v.symm
        (by rw [hψv, hψ_out D.p₂ hp2S]; exact hβN.2.1)

/-- 引理 5 子情形 C：`¬ G.Adj u v` 且 `a₁ = a₂`。 -/
private lemma no_T21_two_thread_same_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hnadj : ¬ G.Adj D.u D.v) (ha12 : D.a₁ = D.a₂) : False := by
  classical
  have hx1v : D.x₁ ≠ D.v := fun h => hnadj (h ▸ D.hux1)
  have hx2u : D.x₂ ≠ D.u := fun h => hnadj (h ▸ D.hvx2).symm
  have hp1_eq : D.p₁ = D.v := by
    rcases D.ha1_all D.v (ha12 ▸ D.hva2.symm) with h | h
    · exact False.elim (D.huv h.symm)
    · exact h.symm
  have hp2_eq : D.p₂ = D.u := by
    rcases D.ha2_all D.u (ha12 ▸ D.hua1.symm) with h | h
    · exact False.elim (D.huv h)
    · exact h.symm
  let S : Finset V := {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂}
  have hx1S : D.x₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(G.ne_of_adj D.hux1).symm, hx1v, D.ht1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hdt2 (by omega), D.hy1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hdy2 (by omega), D.ha1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hda2 (by omega)⟩
  have hx2S : D.x₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx2u, (G.ne_of_adj D.hvx2).symm, ne_of_deg_ge_lt D.hdx2 D.hdt1 (by omega), D.ht2x2.symm,
      ne_of_deg_ge_lt D.hdx2 D.hdy1 (by omega), D.hy2x2.symm,
      ne_of_deg_ge_lt D.hdx2 D.hda1 (by omega), D.ha2x2.symm⟩
  have hS_out' : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s →
      (s = D.u ∧ w = D.x₁) ∨ (s = D.v ∧ w = D.x₂) := by
    intro w hwS s hsS hws
    rcases D.S_out hwS hsS hws with h | h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hwS (by rw [h, hp1_eq]; simp [S]))
    · exact False.elim (hwS (by rw [h, hp2_eq]; simp [S]))
  have hnoniso : ∀ w, w ∉ S → (∃ s ∈ S, G.Adj w s) → ∃ r, r ∉ S ∧ G.Adj w r := by
    intro w hwS ⟨s, hsS, hws⟩
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out' w hwS s hsS hws with ⟨_, h⟩ | ⟨_, h⟩
      · rw [h]; exact D.hdx1
      · rw [h]; exact D.hdx2
    rcases exists_mem_sdiff_of_lt (A := G.neighborFinset w) (B := {D.u, D.v})
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]
          have := Finset.card_le_two (a := D.u) (b := D.v); omega) with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, fun hrS => ?_, hr⟩
    rcases hS_out' w hwS r hrS hr with ⟨h, _⟩ | ⟨h, _⟩
    · exact hrn.1 h
    · exact hrn.2 h
  rcases exists_admissible_coloring hm (S := S) ⟨D.u, by simp [S]⟩ with ⟨adm⟩
  have hLu5 : (L D.u).card = 5 := by rw [hm.list_card D.u]; simp [kappa, D.hdu4]
  have hLv5 : (L D.v).card = 5 := by rw [hm.list_card D.v]; simp [kappa, D.hdv4]
  have hLy1 : (L D.y₁).card = 2 := by rw [hm.list_card D.y₁]; simp [kappa, D.hdy1]
  have hLy2 : (L D.y₂).card = 2 := by rw [hm.list_card D.y₂]; simp [kappa, D.hdy2]
  have hLt1 : (L D.t₁).card = 4 := by rw [hm.list_card D.t₁]; simp [kappa, D.hdt1]
  have hLt2 : (L D.t₂).card = 4 := by rw [hm.list_card D.t₂]; simp [kappa, D.hdt2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  rcases exists_mem_sdiff_of_lt (A := L D.u)
    (B := insert (adm.φ D.x₁) (insert (adm.φs D.x₁) (L D.y₁)))
    (by have := Finset.card_insert_le (adm.φ D.x₁) (insert (adm.φs D.x₁) (L D.y₁))
        have := Finset.card_insert_le (adm.φs D.x₁) (L D.y₁); omega) with ⟨α, hαL, hαN⟩
  simp only [Finset.mem_insert, not_or] at hαN
  rcases exists_mem_sdiff_of_lt (A := L D.v) (B := {adm.φ D.x₂, adm.φs D.x₂, α})
    (by have := card_triple_le (adm.φ D.x₂) (adm.φs D.x₂) α; omega) with ⟨β, hβL, hβN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hβN
  rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {α, β, adm.φ D.x₁})
    (by have := card_triple_le α β (adm.φ D.x₁); omega) with ⟨ca, hcaL, hcaN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcaN
  rcases exists_mem_sdiff_of_lt (A := L D.y₂) (B := {β}) (by simp [hLy2]) with ⟨cy2, hcy2L, hcy2β⟩
  rw [Finset.mem_singleton] at hcy2β
  have hLt2_2 : 2 ≤ (L D.t₂ \ {α, β}).card := by
    have := card_sdiff_ge (L D.t₂) {α, β}; have := Finset.card_le_two (a := α) (b := β); omega
  rcases exists_fourth_unique_color (a := adm.φ D.x₂) (b := ca) (c := cy2) hLt2_2 with
    ⟨ct2, hct2m, huniq_v⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hct2m
  rcases exists_mem_sdiff_of_lt (A := L D.t₁) (B := {α, β, ct2})
    (by have := card_triple_le α β ct2; omega) with ⟨ct1, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_fourth_unique_color (a := adm.φ D.x₁) (b := ca) (c := ct1)
    (by omega : 2 ≤ (L D.y₁).card) with ⟨cy1, hcy1L, huniq_u⟩
  have hcy1α : cy1 ≠ α := fun h => hαN.2.2 (h ▸ hcy1L)
  let ψ : V → ℕ := fun z =>
    if z = D.u then α else if z = D.v then β else if z = D.t₁ then ct1 else if z = D.t₂ then ct2
    else if z = D.y₁ then cy1 else if z = D.y₂ then cy2 else if z = D.a₁ then ca else adm.φ z
  have hψu : ψ D.u = α := by simp [ψ]
  have hψv : ψ D.v = β := by simp [ψ, D.huv.symm]
  have hψt1 : ψ D.t₁ = ct1 := by simp [ψ, (G.ne_of_adj D.hut1).symm, D.hvt1.symm]
  have hψt2 : ψ D.t₂ = ct2 := by
    simp [ψ, D.ht2u, G.ne_of_adj D.ht2v, (G.ne_of_adj D.ht12).symm]
  have hψy1 : ψ D.y₁ = cy1 := by
    simp [ψ, (G.ne_of_adj D.huy1).symm, ne_of_deg_eq_ne D.hdy1 D.hdv4 (by omega),
      D.ht1y1.symm, ne_of_deg_eq_ne D.hdy1 D.hdt2 (by omega)]
  have hψy2 : ψ D.y₂ = cy2 := by
    simp [ψ, ne_of_deg_eq_ne D.hdy2 D.hdu4 (by omega), (G.ne_of_adj D.hvy2).symm,
      ne_of_deg_eq_ne D.hdy2 D.hdt1 (by omega), D.ht2y2.symm, D.hy1_ne_y2.symm]
  have hψa1 : ψ D.a₁ = ca := by
    simp [ψ, (G.ne_of_adj D.hua1).symm, ne_of_deg_eq_ne D.hda1 D.hdv4 (by omega),
      D.ht1a1.symm, D.ha1_ne_t2, D.hy1a1.symm, ne_of_deg_eq_ne D.hda1 D.hdy2 (by omega)]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := by
    intro z hz; simp only [S, ha12, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      ha12 ▸ hz.2.2.2.2.2.2.1, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψt1]; exact hct1L
    · rw [hψt2]; exact hct2m.1
    · rw [hψy1]; exact hcy1L
    · rw [hψy2]; exact hcy2L
    · rw [hψa1]; exact hcaL
    · rw [← ha12, hψa1]; exact hcaL
  · intro z₁ z₂ h12 hor
    have hcase : ∀ a b, G.Adj a b → a ∈ S → ψ a ≠ ψ b := by
      intro a b hab haS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at haS
      rcases haS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all b hab with rfl | rfl | rfl | rfl
        · rw [hψu, hψt1]; exact Ne.symm hct1N.1
        · rw [hψu, hψy1]; exact Ne.symm hcy1α
        · rw [hψu, hψa1]; exact Ne.symm hcaN.1
        · rw [hψu, hψ_out D.x₁ hx1S]; exact hαN.1
      · rcases D.hv_all b hab with rfl | rfl | rfl | rfl
        · rw [hψv, hψt2]; exact Ne.symm hct2m.2.2
        · rw [hψv, hψy2]; exact Ne.symm hcy2β
        · rw [← ha12, hψv, hψa1]; exact Ne.symm hcaN.2.1
        · rw [hψv, hψ_out D.x₂ hx2S]; exact hβN.1
      · rcases D.ht1_all b hab with rfl | rfl
        · rw [hψt1, hψu]; exact hct1N.1
        · rw [hψt1, hψt2]; exact hct1N.2.2
      · rcases D.ht2_all b hab with rfl | rfl
        · rw [hψt2, hψt1]; exact Ne.symm hct1N.2.2
        · rw [hψt2, hψv]; exact hct2m.2.2
      · rcases exists_unique_neighbor_of_deg_one D.hdy1 with ⟨w, _, huniq⟩
        have hbu : b = D.u := (huniq b hab).trans (huniq D.u D.huy1.symm).symm
        rw [hbu, hψy1, hψu]; exact hcy1α
      · rcases exists_unique_neighbor_of_deg_one D.hdy2 with ⟨w, _, huniq⟩
        have hbv : b = D.v := (huniq b hab).trans (huniq D.v D.hvy2.symm).symm
        rw [hbv, hψy2, hψv]; exact hcy2β
      · rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hcaN.1
        · rw [hp1_eq, hψa1, hψv]; exact hcaN.2.1
      · rw [← ha12] at hab ⊢
        rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hcaN.1
        · rw [hp1_eq, hψa1, hψv]; exact hcaN.2.1
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12 h1
    · exact (hcase z₂ z₁ h12.symm h2).symm
  · intro w hwS _ s hsS hws
    rcases hS_out' w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψu]; exact hαN.2.1
    · rw [hψv]; exact hβN.2.1
  · intro w hwS hiso ⟨s, hws⟩
    have hsS : s ∈ S := by by_contra h; exact hiso s h hws
    rcases hnoniso w hwS ⟨s, hsS, hws⟩ with ⟨r, hrS, hwr⟩
    exact False.elim (hiso r hrS hwr)
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_four D.hut1 D.huy1 D.hua1 D.hux1 D.hu_all
        (by rw [hψt1, hψy1, hψa1, hψ_out D.x₁ hx1S]; exact hasUniqueColor_quad_perm_3421 huniq_u)
    · exact pcf_at_of_hasUniqueColor_four D.ht2v.symm D.hvy2 D.hva2 D.hvx2 D.hv_all
        (by rw [hψt2, hψy2, ← ha12, hψa1, hψ_out D.x₂ hx2S]
            exact hasUniqueColor_quad_perm_4321 huniq_v)
    · exact pcf_at_of_two_distinct_neighbors D.hdt1 D.hut1.symm D.ht12 D.ht2u.symm
        (by rw [hψu, hψt2]; exact Ne.symm hct2m.2.1)
    · exact pcf_at_of_two_distinct_neighbors D.hdt2 D.ht12.symm D.ht2v D.hvt1.symm
        (by rw [hψt1, hψv]; exact hct1N.2.1)
    · exact pcf_at_deg_one D.hdy1 D.huy1.symm
    · exact pcf_at_deg_one D.hdy2 D.hvy2.symm
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hp1_eq, hψu, hψv]; exact Ne.symm hβN.2.2)
    · rw [← ha12]
      exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hp1_eq, hψu, hψv]; exact Ne.symm hβN.2.2)

/-- 引理 5 主情形公共验证器（`¬ G.Adj u v ∧ a₁ ≠ a₂`）。 -/
private lemma no_T21_two_thread_gen_close {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hnadj : ¬ G.Adj D.u D.v) (ha12 : D.a₁ ≠ D.a₂)
    (adm : AdmissibleColoring G L {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂})
    {γ α cy1 ca1 cy2 ca2 ct1 ct2 : ℕ}
    (hγL : γ ∈ L D.u) (hαL : α ∈ L D.v) (hcy1L : cy1 ∈ L D.y₁) (hca1L : ca1 ∈ L D.a₁)
    (hcy2L : cy2 ∈ L D.y₂) (hca2L : ca2 ∈ L D.a₂) (hct1L : ct1 ∈ L D.t₁) (hct2L : ct2 ∈ L D.t₂)
    (hγx1 : γ ≠ adm.φ D.x₁) (hγp1 : γ ≠ adm.φ D.p₁)
    (hαx2 : α ≠ adm.φ D.x₂) (hαp2 : α ≠ adm.φ D.p₂)
    (hcy1γ : cy1 ≠ γ) (hca1γ : ca1 ≠ γ) (hca1p1 : ca1 ≠ adm.φ D.p₁)
    (hcy2α : cy2 ≠ α) (hca2α : ca2 ≠ α) (hca2p2 : ca2 ≠ adm.φ D.p₂)
    (hct1γ : ct1 ≠ γ) (hct1α : ct1 ≠ α) (hct2α : ct2 ≠ α) (hct2γ : ct2 ≠ γ) (hct12 : ct1 ≠ ct2)
    (havx1 : (∃ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) ∧
      G.Adj D.x₁ r) → γ ≠ adm.φs D.x₁)
    (havp1 : (∃ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) ∧
      G.Adj D.p₁ r) → ca1 ≠ adm.φs D.p₁)
    (havx2 : (∃ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) ∧
      G.Adj D.x₂ r) → α ≠ adm.φs D.x₂)
    (havp2 : (∃ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) ∧
      G.Adj D.p₂ r) → ca2 ≠ adm.φs D.p₂)
    (hu1 : HasUniqueColor [adm.φ D.x₁, cy1, ca1, ct1])
    (hu2 : HasUniqueColor [adm.φ D.x₂, cy2, ca2, ct2])
    (hiso_ok : ∀ w, w ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) →
      (∀ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) → ¬ G.Adj w r) →
      (∃ s, G.Adj w s) →
      let ψ' : V → ℕ := fun z =>
        if z = D.u then γ else if z = D.v then α else if z = D.t₁ then ct1
        else if z = D.t₂ then ct2 else if z = D.y₁ then cy1 else if z = D.y₂ then cy2
        else if z = D.a₁ then ca1 else if z = D.a₂ then ca2 else adm.φ z
      ∃ y, G.Adj w y ∧ ∀ z, G.Adj w z → ψ' z = ψ' y → z = y) : False := by
  classical
  let S : Finset V := {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂}
  have hx1S : D.x₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(G.ne_of_adj D.hux1).symm, fun h => hnadj (h ▸ D.hux1), D.ht1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hdt2 (by omega), D.hy1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hdy2 (by omega), D.ha1x1.symm,
      ne_of_deg_ge_lt D.hdx1 D.hda2 (by omega)⟩
  have hx2S : D.x₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hnadj (h ▸ D.hvx2).symm, (G.ne_of_adj D.hvx2).symm,
      ne_of_deg_ge_lt D.hdx2 D.hdt1 (by omega), D.ht2x2.symm,
      ne_of_deg_ge_lt D.hdx2 D.hdy1 (by omega), D.hy2x2.symm,
      ne_of_deg_ge_lt D.hdx2 D.hda1 (by omega), D.ha2x2.symm⟩
  have hp1S : D.p₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.hp1u, fun h => ha12 (D.ha1_eq_of_p1v h),
      ne_of_deg_ge_lt D.hdp1 D.hdt1 (by omega), ne_of_deg_ge_lt D.hdp1 D.hdt2 (by omega),
      ne_of_deg_ge_lt D.hdp1 D.hdy1 (by omega), ne_of_deg_ge_lt D.hdp1 D.hdy2 (by omega),
      (G.ne_of_adj D.ha1p1).symm, ne_of_deg_ge_lt D.hdp1 D.hda2 (by omega)⟩
  have hp2S : D.p₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha12 (D.ha1_eq_of_p2u h), D.hp2v,
      ne_of_deg_ge_lt D.hdp2 D.hdt1 (by omega), ne_of_deg_ge_lt D.hdp2 D.hdt2 (by omega),
      ne_of_deg_ge_lt D.hdp2 D.hdy1 (by omega), ne_of_deg_ge_lt D.hdp2 D.hdy2 (by omega),
      ne_of_deg_ge_lt D.hdp2 D.hda1 (by omega), (G.ne_of_adj D.ha2p2).symm⟩
  let ψ : V → ℕ := fun z =>
    if z = D.u then γ else if z = D.v then α else if z = D.t₁ then ct1 else if z = D.t₂ then ct2
    else if z = D.y₁ then cy1 else if z = D.y₂ then cy2
    else if z = D.a₁ then ca1 else if z = D.a₂ then ca2 else adm.φ z
  have hψu : ψ D.u = γ := by simp [ψ]
  have hψv : ψ D.v = α := by simp [ψ, D.huv.symm]
  have hψt1 : ψ D.t₁ = ct1 := by simp [ψ, (G.ne_of_adj D.hut1).symm, D.hvt1.symm]
  have hψt2 : ψ D.t₂ = ct2 := by
    simp [ψ, D.ht2u, G.ne_of_adj D.ht2v, (G.ne_of_adj D.ht12).symm]
  have hψy1 : ψ D.y₁ = cy1 := by
    simp [ψ, (G.ne_of_adj D.huy1).symm, ne_of_deg_eq_ne D.hdy1 D.hdv4 (by omega),
      D.ht1y1.symm, ne_of_deg_eq_ne D.hdy1 D.hdt2 (by omega)]
  have hψy2 : ψ D.y₂ = cy2 := by
    simp [ψ, ne_of_deg_eq_ne D.hdy2 D.hdu4 (by omega), (G.ne_of_adj D.hvy2).symm,
      ne_of_deg_eq_ne D.hdy2 D.hdt1 (by omega), D.ht2y2.symm, D.hy1_ne_y2.symm]
  have hψa1 : ψ D.a₁ = ca1 := by
    simp [ψ, (G.ne_of_adj D.hua1).symm, ne_of_deg_eq_ne D.hda1 D.hdv4 (by omega),
      D.ht1a1.symm, D.ha1_ne_t2, D.hy1a1.symm, ne_of_deg_eq_ne D.hda1 D.hdy2 (by omega)]
  have hψa2 : ψ D.a₂ = ca2 := by
    simp [ψ, ne_of_deg_eq_ne D.hda2 D.hdu4 (by omega), (G.ne_of_adj D.hva2).symm, D.ha2_ne_t1,
      D.ht2a2.symm, ne_of_deg_eq_ne D.hda2 D.hdy1 (by omega), D.hy2a2.symm, ha12.symm]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := by
    intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hγL
    · rw [hψv]; exact hαL
    · rw [hψt1]; exact hct1L
    · rw [hψt2]; exact hct2L
    · rw [hψy1]; exact hcy1L
    · rw [hψy2]; exact hcy2L
    · rw [hψa1]; exact hca1L
    · rw [hψa2]; exact hca2L
  · intro z₁ z₂ h12 hor
    have hcase : ∀ a b, G.Adj a b → a ∈ S → ψ a ≠ ψ b := by
      intro a b hab haS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at haS
      rcases haS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all b hab with rfl | rfl | rfl | rfl
        · rw [hψu, hψt1]; exact Ne.symm hct1γ
        · rw [hψu, hψy1]; exact Ne.symm hcy1γ
        · rw [hψu, hψa1]; exact Ne.symm hca1γ
        · rw [hψu, hψ_out D.x₁ hx1S]; exact hγx1
      · rcases D.hv_all b hab with rfl | rfl | rfl | rfl
        · rw [hψv, hψt2]; exact Ne.symm hct2α
        · rw [hψv, hψy2]; exact Ne.symm hcy2α
        · rw [hψv, hψa2]; exact Ne.symm hca2α
        · rw [hψv, hψ_out D.x₂ hx2S]; exact hαx2
      · rcases D.ht1_all b hab with rfl | rfl
        · rw [hψt1, hψu]; exact hct1γ
        · rw [hψt1, hψt2]; exact hct12
      · rcases D.ht2_all b hab with rfl | rfl
        · rw [hψt2, hψt1]; exact Ne.symm hct12
        · rw [hψt2, hψv]; exact hct2α
      · rcases exists_unique_neighbor_of_deg_one D.hdy1 with ⟨w, _, huniq⟩
        have hbu : b = D.u := (huniq b hab).trans (huniq D.u D.huy1.symm).symm
        rw [hbu, hψy1, hψu]; exact hcy1γ
      · rcases exists_unique_neighbor_of_deg_one D.hdy2 with ⟨w, _, huniq⟩
        have hbv : b = D.v := (huniq b hab).trans (huniq D.v D.hvy2.symm).symm
        rw [hbv, hψy2, hψv]; exact hcy2α
      · rcases D.ha1_all b hab with rfl | rfl
        · rw [hψa1, hψu]; exact hca1γ
        · rw [hψa1, hψ_out D.p₁ hp1S]; exact hca1p1
      · rcases D.ha2_all b hab with rfl | rfl
        · rw [hψa2, hψv]; exact hca2α
        · rw [hψa2, hψ_out D.p₂ hp2S]; exact hca2p2
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12 h1
    · exact (hcase z₂ z₁ h12.symm h2).symm
  · intro w hwS hnon s hsS hws
    rcases D.S_out hwS hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψu]; exact havx1 hnon
    · rw [hψv]; exact havx2 hnon
    · rw [hψa1]; exact havp1 hnon
    · rw [hψa2]; exact havp2 hnon
  · exact hiso_ok
  · intro z hzS _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_four D.hut1 D.huy1 D.hua1 D.hux1 D.hu_all
        (by rw [hψt1, hψy1, hψa1, hψ_out D.x₁ hx1S]; exact hasUniqueColor_quad_perm_4123 hu1)
    · exact pcf_at_of_hasUniqueColor_four D.ht2v.symm D.hvy2 D.hva2 D.hvx2 D.hv_all
        (by rw [hψt2, hψy2, hψa2, hψ_out D.x₂ hx2S]; exact hasUniqueColor_quad_perm_4123 hu2)
    · exact pcf_at_of_two_distinct_neighbors D.hdt1 D.hut1.symm D.ht12 D.ht2u.symm
        (by rw [hψu, hψt2]; exact Ne.symm hct2γ)
    · exact pcf_at_of_two_distinct_neighbors D.hdt2 D.ht12.symm D.ht2v D.hvt1.symm
        (by rw [hψt1, hψv]; exact hct1α)
    · exact pcf_at_deg_one D.hdy1 D.huy1.symm
    · exact pcf_at_deg_one D.hdy2 D.hvy2.symm
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1p1 D.hp1u.symm
        (by rw [hψu, hψ_out D.p₁ hp1S]; exact hγp1)
    · exact pcf_at_of_two_distinct_neighbors D.hda2 D.hva2.symm D.ha2p2 D.hp2v.symm
        (by rw [hψv, hψ_out D.p₂ hp2S]; exact hαp2)

/-- 引理 5 孤立外邻点子情形（`{u, a₁} ⊆ N_G(w)`；`{v, a₂}` 情形通过对偶 `D.swap` 复用！）。 -/
private lemma no_T21_two_thread_gen_iso_u {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hnadj : ¬ G.Adj D.u D.v) (ha12 : D.a₁ ≠ D.a₂)
    (adm : AdmissibleColoring G L {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂})
    {w : V} (hwS : w ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V))
    (hw_iso : ∀ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) → ¬ G.Adj w r)
    (hdw3 : 3 ≤ G.degree w)
    (hNw_sub : G.neighborFinset w ⊆ {D.u, D.a₁, D.v, D.a₂})
    (hw_uniq : ∀ w', w' ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) →
      (∀ r, r ∉ ({D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂} : Finset V) → ¬ G.Adj w' r) →
      (∃ s, G.Adj w' s) → w' = w)
    (hwu : G.Adj w D.u) (hwa1 : G.Adj w D.a₁) : False := by
  classical
  have hu_ne_a1 : D.u ≠ D.a₁ := G.ne_of_adj D.hua1
  have hu_ne_a2 : D.u ≠ D.a₂ := ne_of_deg_eq_ne D.hdu4 D.hda2 (by omega)
  have hv_ne_a1 : D.v ≠ D.a₁ := ne_of_deg_eq_ne D.hdv4 D.hda1 (by omega)
  have hx1w : D.x₁ = w := by
    rcases D.S_out hwS (by simp) hwu with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · rfl
    · exact False.elim (D.huv h)
    · exact False.elim (hu_ne_a1 h)
    · exact False.elim (hu_ne_a2 h)
  have hp1w : D.p₁ = w := by
    rcases D.S_out hwS (by simp) hwa1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
    · exact False.elim (hu_ne_a1.symm h)
    · exact False.elim (hv_ne_a1.symm h)
    · rfl
    · exact False.elim (ha12 h)
  have hLu5 : (L D.u).card = 5 := by rw [hm.list_card D.u]; simp [kappa, D.hdu4]
  have hLv5 : (L D.v).card = 5 := by rw [hm.list_card D.v]; simp [kappa, D.hdv4]
  have hLy1 : (L D.y₁).card = 2 := by rw [hm.list_card D.y₁]; simp [kappa, D.hdy1]
  have hLy2 : (L D.y₂).card = 2 := by rw [hm.list_card D.y₂]; simp [kappa, D.hdy2]
  have hLt1 : (L D.t₁).card = 4 := by rw [hm.list_card D.t₁]; simp [kappa, D.hdt1]
  have hLt2 : (L D.t₂).card = 4 := by rw [hm.list_card D.t₂]; simp [kappa, D.hdt2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  have hLa2 : (L D.a₂).card = 4 := by rw [hm.list_card D.a₂]; simp [kappa, D.hda2]
  rcases exists_mem_sdiff_of_lt (A := L D.v) (B := {adm.φ D.x₂, adm.φs D.x₂, adm.φ D.p₂})
    (by have := card_triple_le (adm.φ D.x₂) (adm.φs D.x₂) (adm.φ D.p₂); omega) with ⟨α, hαL, hαN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hαN
  rcases exists_mem_sdiff_of_lt (A := L D.a₂) (B := {adm.φ D.p₂, adm.φs D.p₂, α})
    (by have := card_triple_le (adm.φ D.p₂) (adm.φs D.p₂) α; omega) with ⟨ca2, hca2L, hca2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca2N
  rcases exists_mem_sdiff_of_lt (A := L D.y₂) (B := {α}) (by simp [hLy2]) with ⟨cy2, hcy2L, hcy2α⟩
  rw [Finset.mem_singleton] at hcy2α
  let Gu : Finset ℕ := L D.u \ insert (adm.φ w) (L D.y₁)
  have hGu2 : 2 ≤ Gu.card := by
    dsimp only [Gu]
    have h1 := card_sdiff_ge (L D.u) (insert (adm.φ w) (L D.y₁))
    have h2 := Finset.card_insert_le (adm.φ w) (L D.y₁); omega
  have hγca1 : ∃ γ ∈ Gu, ∃ ca1 ∈ L D.a₁ \ {adm.φ w, γ},
      (G.Adj w D.v ∧ G.Adj w D.a₂ → HasUniqueColor [α, ca2, γ, ca1]) := by
    by_cases hboth : G.Adj w D.v ∧ G.Adj w D.a₂
    · by_cases hout : ∃ γ ∈ Gu, γ ∉ ({α, ca2} : Finset ℕ)
      · rcases hout with ⟨γ, hγG, hγout⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγout
        rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {adm.φ w, γ})
          (by have := Finset.card_le_two (a := adm.φ w) (b := γ); omega) with ⟨ca1, hca1L, hca1N⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca1N
        refine ⟨γ, hγG, ca1, Finset.mem_sdiff.mpr ⟨hca1L, by simp [hca1N.1, hca1N.2]⟩,
          fun _ => ⟨γ, ?_⟩⟩
        simp [Ne.symm hγout.1, Ne.symm hγout.2, hca1N.2]
      · push Not at hout
        have hGu_eq : Gu = {α, ca2} :=
          Finset.eq_of_subset_of_card_le (fun x hx => hout x hx)
            (by rw [Finset.card_pair (Ne.symm hca2N.2.2)]; exact hGu2)
        have hαG : α ∈ Gu := by rw [hGu_eq]; simp
        rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {adm.φ w, α, ca2})
          (by have := card_triple_le (adm.φ w) α ca2; omega) with ⟨ca1, hca1L, hca1N⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca1N
        refine ⟨α, hαG, ca1, Finset.mem_sdiff.mpr ⟨hca1L, by simp [hca1N.1, hca1N.2.1]⟩,
          fun _ => ⟨ca1, ?_⟩⟩
        simp [Ne.symm hca1N.2.1, Ne.symm hca1N.2.2]
    · rcases Finset.card_pos.mp (by omega : 0 < Gu.card) with ⟨γ, hγG⟩
      rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {adm.φ w, γ})
        (by have := Finset.card_le_two (a := adm.φ w) (b := γ); omega) with ⟨ca1, hca1L, hca1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hca1N
      exact ⟨γ, hγG, ca1, Finset.mem_sdiff.mpr ⟨hca1L, by simp [hca1N.1, hca1N.2]⟩,
        fun h => False.elim (hboth h)⟩
  rcases hγca1 with ⟨γ, hγG, ca1, hca1m, hw4⟩
  simp only [Gu, Finset.mem_sdiff, Finset.mem_insert, not_or] at hγG
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca1m
  have hLt2_2 : 2 ≤ (L D.t₂ \ {α, γ}).card := by
    have := card_sdiff_ge (L D.t₂) {α, γ}; have := Finset.card_le_two (a := α) (b := γ); omega
  rcases exists_fourth_unique_color (a := adm.φ D.x₂) (b := cy2) (c := ca2) hLt2_2 with
    ⟨ct2, hct2m, hu2⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hct2m
  rcases exists_mem_sdiff_of_lt (A := L D.t₁) (B := {γ, α, ct2})
    (by have := card_triple_le γ α ct2; omega) with ⟨ct1, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_fourth_unique_color (a := adm.φ w) (b := ca1) (c := ct1)
    (by omega : 2 ≤ (L D.y₁).card) with ⟨cy1, hcy1L, hu1'⟩
  have hcy1γ : cy1 ≠ γ := fun h => hγG.2.2 (h ▸ hcy1L)
  have hu1 : HasUniqueColor [adm.φ D.x₁, cy1, ca1, ct1] := by
    rcases hu1' with ⟨c, hc⟩; refine ⟨c, ?_⟩
    rw [hx1w]; simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
  refine no_T21_two_thread_gen_close hm D hnadj ha12 adm hγG.1 hαL hcy1L hca1m.1 hcy2L hca2L
    hct1L hct2m.1 (hx1w ▸ hγG.2.1) (hp1w ▸ hγG.2.1) hαN.1 hαN.2.2 hcy1γ hca1m.2.2
    (hp1w ▸ hca1m.2.1) hcy2α hca2N.2.2 hca2N.1 hct1N.1 hct1N.2.1 hct2m.2.1 hct2m.2.2 hct1N.2.2
    (fun h => False.elim (by rcases h with ⟨r, hr, hxr⟩; exact hw_iso r hr (hx1w ▸ hxr)))
    (fun h => False.elim (by rcases h with ⟨r, hr, hpr⟩; exact hw_iso r hr (hp1w ▸ hpr)))
    (fun _ => hαN.2.1) (fun _ => hca2N.2.1) hu1 hu2 ?_
  intro w' hw'S hw'_iso hw'_adj
  have hw'_eq : w = w' := (hw_uniq w' hw'S hw'_iso hw'_adj).symm
  subst hw'_eq
  dsimp only
  let ψ' : V → ℕ := fun z =>
    if z = D.u then γ else if z = D.v then α else if z = D.t₁ then ct1 else if z = D.t₂ then ct2
    else if z = D.y₁ then cy1 else if z = D.y₂ then cy2
    else if z = D.a₁ then ca1 else if z = D.a₂ then ca2 else adm.φ z
  change ∃ y, G.Adj w y ∧ ∀ z, G.Adj w z → ψ' z = ψ' y → z = y
  have hψ'u : ψ' D.u = γ := by simp [ψ']
  have hψ'v : ψ' D.v = α := by simp [ψ', D.huv.symm]
  have hψ'a1 : ψ' D.a₁ = ca1 := by
    simp [ψ', hu_ne_a1.symm, hv_ne_a1.symm, D.ht1a1.symm, D.ha1_ne_t2, D.hy1a1.symm,
      ne_of_deg_eq_ne D.hda1 D.hdy2 (by omega)]
  have hψ'a2 : ψ' D.a₂ = ca2 := by
    simp [ψ', hu_ne_a2.symm, (G.ne_of_adj D.hva2).symm, D.ha2_ne_t1, D.ht2a2.symm,
      ne_of_deg_eq_ne D.hda2 D.hdy1 (by omega), D.hy2a2.symm, ha12.symm]
  by_cases hwv : G.Adj w D.v
  · by_cases hwa2 : G.Adj w D.a₂
    · exact pcf_at_of_hasUniqueColor_four hwv hwa2 hwu hwa1
        (fun r hr => by
          have hm4 := hNw_sub ((G.mem_neighborFinset w r).mpr hr)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm4
          rcases hm4 with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
        (by rw [hψ'v, hψ'a2, hψ'u, hψ'a1]; exact hw4 ⟨hwv, hwa2⟩)
    · exact pcf_at_of_hasUniqueColor_three hwv hwu hwa1
        (fun r hr => by
          have hm4 := hNw_sub ((G.mem_neighborFinset w r).mpr hr)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm4
          rcases hm4 with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl rfl
          · exact False.elim (hwa2 hr))
        (by rw [hψ'v, hψ'u, hψ'a1, hasUniqueColor_triple_iff]
            exact fun h => hca1m.2.2 h.2.symm)
  · have hwa2 : G.Adj w D.a₂ := by
      by_contra hno2
      have hsub : G.neighborFinset w ⊆ {D.u, D.a₁} := by
        intro r hr; have hm4 := hNw_sub hr; rw [SimpleGraph.mem_neighborFinset] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm4 ⊢
        rcases hm4 with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hwv hr)
        · exact False.elim (hno2 hr)
      have hle := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
      have := Finset.card_le_two (a := D.u) (b := D.a₁); omega
    exact pcf_at_of_hasUniqueColor_three hwa2 hwu hwa1
      (fun r hr => by
        have hm4 := hNw_sub ((G.mem_neighborFinset w r).mpr hr)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm4
        rcases hm4 with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact False.elim (hwv hr)
        · exact Or.inl rfl)
      (by rw [hψ'a2, hψ'u, hψ'a1, hasUniqueColor_triple_iff]
          exact fun h => hca1m.2.2 h.2.symm)

/-- 引理 5 通用主情形（`¬ G.Adj u v ∧ a₁ ≠ a₂`）：统一处理孤立与非孤立分支。 -/
private lemma no_T21_two_thread_gen {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : T21TwoData G)
    (hadj : ¬ G.Adj D.u D.v) (ha12 : D.a₁ ≠ D.a₂) : False := by
  classical
  let S : Finset V := {D.u, D.v, D.t₁, D.t₂, D.y₁, D.y₂, D.a₁, D.a₂}
  rcases exists_admissible_coloring hm (S := S) ⟨D.u, by simp [S]⟩ with ⟨adm⟩
  by_cases hiso_ex : ∃ w, w ∉ S ∧ (∀ r, r ∉ S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)
  · rcases hiso_ex with ⟨w, hwS, hw_iso, ⟨s₀, hws₀⟩⟩
    have hs₀S : s₀ ∈ S := by by_contra h; exact hw_iso s₀ h hws₀
    have hdw3 : 3 ≤ G.degree w := by
      rcases D.S_out hwS hs₀S hws₀ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact D.hdx1
      · exact D.hdx2
      · exact D.hdp1
      · exact D.hdp2
    have hNw_sub : G.neighborFinset w ⊆ {D.u, D.a₁, D.v, D.a₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr
      rcases D.S_out hwS hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hw_uniq : ∀ w', w' ∉ S → (∀ r, r ∉ S → ¬ G.Adj w' r) → (∃ s, G.Adj w' s) → w' = w := by
      intro w' hw'S hw'_iso ⟨s', hw's'⟩
      by_contra hne
      have hs'S : s' ∈ S := by by_contra h; exact hw'_iso s' h hw's'
      have hdw'3 : 3 ≤ G.degree w' := by
        rcases D.S_out hw'S hs'S hw's' with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact D.hdx1
        · exact D.hdx2
        · exact D.hdp1
        · exact D.hdp2
      have hNw'_sub : G.neighborFinset w' ⊆ {D.u, D.a₁, D.v, D.a₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hw'_iso r h hr
        rcases D.S_out hw'S hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      have hdisj : Disjoint (G.neighborFinset w) (G.neighborFinset w') := by
        rw [Finset.disjoint_left]; intro r hr1 hr2
        rw [SimpleGraph.mem_neighborFinset] at hr1 hr2
        have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr1
        have hua1_ne : D.u ≠ D.a₁ := G.ne_of_adj D.hua1
        have hva2_ne : D.v ≠ D.a₂ := G.ne_of_adj D.hva2
        have hua2_ne : D.u ≠ D.a₂ := ne_of_deg_eq_ne D.hdu4 D.hda2 (by omega)
        have hva1_ne : D.v ≠ D.a₁ := ne_of_deg_eq_ne D.hdv4 D.hda1 (by omega)
        rcases D.S_out hwS hrS hr1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        rcases D.S_out hw'S hrS hr2 with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
        first
        | exact hne (h3.trans h1.symm)
        | exact D.huv h2 | exact D.huv h2.symm
        | exact hua1_ne h2 | exact hua1_ne h2.symm
        | exact hua2_ne h2 | exact hua2_ne h2.symm
        | exact hva1_ne h2 | exact hva1_ne h2.symm
        | exact hva2_ne h2 | exact hva2_ne h2.symm
        | exact ha12 h2 | exact ha12 h2.symm
      have hle := Finset.card_le_card (Finset.union_subset hNw_sub hNw'_sub)
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree] at hle
      have := card_quad_le D.u D.a₁ D.v D.a₂; omega
    have hpig : (G.Adj w D.u ∧ G.Adj w D.a₁) ∨ (G.Adj w D.v ∧ G.Adj w D.a₂) := by
      by_contra hno; push Not at hno
      have hle1 : ∀ {x y : V}, (G.Adj w x → ¬ G.Adj w y) →
          (G.neighborFinset w ∩ {x, y}).card ≤ 1 := by
        intro x y hxy
        by_cases hwx : G.Adj w x
        · have hsub : G.neighborFinset w ∩ {x, y} ⊆ {x} := by
            intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
              Finset.mem_insert, Finset.mem_singleton] at hr ⊢
            rcases hr.2 with rfl | rfl
            · rfl
            · exact False.elim (hxy hwx hr.1)
          exact le_trans (Finset.card_le_card hsub) (by simp)
        · have hsub : G.neighborFinset w ∩ {x, y} ⊆ {y} := by
            intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
              Finset.mem_insert, Finset.mem_singleton] at hr ⊢
            rcases hr.2 with rfl | rfl
            · exact False.elim (hwx hr.1)
            · rfl
          exact le_trans (Finset.card_le_card hsub) (by simp)
      have hun : G.neighborFinset w ⊆
          (G.neighborFinset w ∩ {D.u, D.a₁}) ∪ (G.neighborFinset w ∩ {D.v, D.a₂}) := by
        intro r hr; have hm4 := hNw_sub hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm4
        rw [Finset.mem_union]
        rcases hm4 with rfl | rfl | rfl | rfl
        · exact Or.inl (Finset.mem_inter.mpr ⟨hr, by simp⟩)
        · exact Or.inl (Finset.mem_inter.mpr ⟨hr, by simp⟩)
        · exact Or.inr (Finset.mem_inter.mpr ⟨hr, by simp⟩)
        · exact Or.inr (Finset.mem_inter.mpr ⟨hr, by simp⟩)
      have h1 := hle1 hno.1
      have h2 := hle1 hno.2
      have hle := le_trans (Finset.card_le_card hun) (Finset.card_union_le _ _)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hle; omega
    rcases hpig with ⟨hwu, hwa1⟩ | ⟨hwv, hwa2⟩
    · exact no_T21_two_thread_gen_iso_u hm D hadj ha12 adm hwS hw_iso hdw3 hNw_sub hw_uniq
        hwu hwa1
    · have hSeq : ({D.swap.u, D.swap.v, D.swap.t₁, D.swap.t₂, D.swap.y₁, D.swap.y₂,
          D.swap.a₁, D.swap.a₂} : Finset V) = S := by
        ext z; simp only [T21TwoData.swap, S, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
      have hNw_swap : G.neighborFinset w ⊆ {D.swap.u, D.swap.a₁, D.swap.v, D.swap.a₂} := by
        intro r hr; have hm4 := hNw_sub hr
        simp only [T21TwoData.swap, Finset.mem_insert, Finset.mem_singleton] at hm4 ⊢
        rcases hm4 with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      exact no_T21_two_thread_gen_iso_u hm D.swap (fun h => hadj h.symm) (Ne.symm ha12)
        (hSeq ▸ adm) (hSeq.symm ▸ hwS) (fun r hr => hw_iso r (hSeq ▸ hr)) hdw3 hNw_swap
        (fun w' hw' h1 h2 => hw_uniq w' (hSeq ▸ hw') (fun r hr => h1 r (hSeq.symm ▸ hr)) h2)
        hwv hwa2
  · have hLu5 : (L D.u).card = 5 := by rw [hm.list_card D.u]; simp [kappa, D.hdu4]
    have hLv5 : (L D.v).card = 5 := by rw [hm.list_card D.v]; simp [kappa, D.hdv4]
    have hLy1 : (L D.y₁).card = 2 := by rw [hm.list_card D.y₁]; simp [kappa, D.hdy1]
    have hLy2 : (L D.y₂).card = 2 := by rw [hm.list_card D.y₂]; simp [kappa, D.hdy2]
    have hLt1 : (L D.t₁).card = 4 := by rw [hm.list_card D.t₁]; simp [kappa, D.hdt1]
    have hLt2 : (L D.t₂).card = 4 := by rw [hm.list_card D.t₂]; simp [kappa, D.hdt2]
    have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
    have hLa2 : (L D.a₂).card = 4 := by rw [hm.list_card D.a₂]; simp [kappa, D.hda2]
    let C₁ : Finset ℕ := L D.u \ {adm.φ D.x₁, adm.φs D.x₁, adm.φ D.p₁}
    let C₂ : Finset ℕ := L D.v \ {adm.φ D.x₂, adm.φs D.x₂, adm.φ D.p₂}
    let A₁ : Finset ℕ := L D.a₁ \ {adm.φ D.p₁, adm.φs D.p₁}
    let A₂ : Finset ℕ := L D.a₂ \ {adm.φ D.p₂, adm.φs D.p₂}
    have hC1 : 2 ≤ C₁.card := by
      dsimp only [C₁]
      have := card_sdiff_ge (L D.u) {adm.φ D.x₁, adm.φs D.x₁, adm.φ D.p₁}
      have := card_triple_le (adm.φ D.x₁) (adm.φs D.x₁) (adm.φ D.p₁); omega
    have hC2 : 2 ≤ C₂.card := by
      dsimp only [C₂]
      have := card_sdiff_ge (L D.v) {adm.φ D.x₂, adm.φs D.x₂, adm.φ D.p₂}
      have := card_triple_le (adm.φ D.x₂) (adm.φs D.x₂) (adm.φ D.p₂); omega
    have hA1 : 2 ≤ A₁.card := by
      dsimp only [A₁]
      have := card_sdiff_ge (L D.a₁) {adm.φ D.p₁, adm.φs D.p₁}
      have := Finset.card_le_two (a := adm.φ D.p₁) (b := adm.φs D.p₁); omega
    have hA2 : 2 ≤ A₂.card := by
      dsimp only [A₂]
      have := card_sdiff_ge (L D.a₂) {adm.φ D.p₂, adm.φs D.p₂}
      have := Finset.card_le_two (a := adm.φ D.p₂) (b := adm.φs D.p₂); omega
    have hβ1 : adm.φ D.x₁ ∉ C₁ := by simp [C₁]
    rcases t21_two_thread_ext (β₁ := adm.φ D.x₁) (β₂ := adm.φ D.x₂) hC1 hC2 hLy1 hLy2 hA1 hA2
      hLt1 hLt2 hβ1 with
      ⟨γ, hγm, α, hαm, cy1, hcy1m, ca1, hca1m, cy2, hcy2m, ca2, hca2m,
        ct1, hct1m, ct2, hct2m, hct12, hu1, hu2⟩
    simp only [C₁, C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hγm hαm
    simp only [A₁, A₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hcy1m hca1m hcy2m hca2m hct1m hct2m
    exact no_T21_two_thread_gen_close hm D hadj ha12 adm hγm.1 hαm.1 hcy1m.1 hca1m.1.1
      hcy2m.1 hca2m.1.1 hct1m.1 hct2m.1 hγm.2.1 hγm.2.2.2 hαm.2.1 hαm.2.2.2
      hcy1m.2 hca1m.2 hca1m.1.2.1 hcy2m.2 hca2m.2 hca2m.1.2.1 hct1m.2.1 hct1m.2.2
      hct2m.2.1 hct2m.2.2 hct12
      (fun _ => hγm.2.2.1) (fun _ => hca1m.1.2.2) (fun _ => hαm.2.2.1) (fun _ => hca2m.1.2.2)
      hu1 hu2 (fun w hwS hiso hadj' => False.elim (hiso_ex ⟨w, hwS, hiso, hadj'⟩))

/-- 引理 5：极小反例中，两个 `T21` 顶点不能通过 `2`-线串相连。 -/
lemma no_T21_two_thread_T21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v : V}
    (hu : IsT21 G u) (hv : IsT21 G v) (h2 : HasTwoThreadBetween G u v) : False := by
  classical
  rcases h2 with ⟨t₁, t₂, hut1, hdt1, ht12, ht2u, hdt2, ht2v, hvt1, huv⟩
  have hdu4 : G.degree u = 4 := (isT21_structure hm hpq hu).1
  have hdv4 : G.degree v = 4 := (isT21_structure hm hpq hv).1
  have ht1_mem : t₁ ∈ twoThreadNbrs G u := by
    rw [mem_twoThreadNbrs]; exact ⟨hut1, hdt1, t₂, v, ht12, ht2u, hdt2, ht2v, hvt1, by omega⟩
  have ht2_mem : t₂ ∈ twoThreadNbrs G v := by
    rw [mem_twoThreadNbrs]
    exact ⟨ht2v.symm, hdt2, t₁, u, ht12.symm, hvt1.symm, hdt1, hut1.symm, ht2u.symm, by omega⟩
  rcases isT21_unpack_at hm hpq hu ht1_mem with
    ⟨y₁, a₁, x₁, hy1, ha1, hx1, ht1y1, ht1a1, ht1x1, hy1a1, hy1x1, ha1x1, hu_all⟩
  rcases isT21_unpack_at hm hpq hv ht2_mem with
    ⟨y₂, a₂, x₂, hy2, ha2, hx2, ht2y2, ht2a2, ht2x2, hy2a2, hy2x2, ha2x2, hv_all⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) ha1 with ⟨p₁, ha1p1, hp1u, hdp1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) ha2 with ⟨p₂, ha2p2, hp2v, hdp2, _, _⟩
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hva2 : G.Adj v a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have huy1 : G.Adj u y₁ := (mem_leafNbrs.mp hy1).1
  have hdy1 : G.degree y₁ = 1 := (mem_leafNbrs.mp hy1).2
  have hvy2 : G.Adj v y₂ := (mem_leafNbrs.mp hy2).1
  have hdy2 : G.degree y₂ = 1 := (mem_leafNbrs.mp hy2).2
  have hux1 : G.Adj u x₁ := (mem_goodNbrs.mp hx1).1
  have hdx1 : 3 ≤ G.degree x₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hx1).2
  have hvx2 : G.Adj v x₂ := (mem_goodNbrs.mp hx2).1
  have hdx2 : 3 ≤ G.degree x₂ := deg_ge_three_of_isGood (mem_goodNbrs.mp hx2).2
  let D : T21TwoData G := {
    u, v, t₁, t₂, y₁, a₁, x₁, p₁, y₂, a₂, x₂, p₂, huv, hut1, hdt1, ht12, ht2u, hdt2, ht2v, hvt1,
    hdu4, hdv4, huy1, hdy1, hua1, hda1, ha1p1, hp1u, hdp1, hux1, hdx1,
    hvy2, hdy2, hva2, hda2, ha2p2, hp2v, hdp2, hvx2, hdx2,
    ht1y1, ht1a1, ht1x1, hy1a1, hy1x1, ha1x1, ht2y2, ht2a2, ht2x2, hy2a2, hy2x2, ha2x2,
    hu_all, hv_all,
    ht1_all := fun r hr => by
      have hN := neighborFinset_eq_pair_of_deg_two hdt1 hut1.symm ht12 ht2u.symm
      have : r ∈ ({u, t₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₁ r).mpr hr
      simpa using this,
    ht2_all := fun r hr => by
      have hN := neighborFinset_eq_pair_of_deg_two hdt2 ht12.symm ht2v hvt1.symm
      have : r ∈ ({t₁, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₂ r).mpr hr
      simpa using this,
    ha1_all := fun r hr => by
      have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm ha1p1 hp1u.symm
      have : r ∈ ({u, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
      simpa using this,
    ha2_all := fun r hr => by
      have hN := neighborFinset_eq_pair_of_deg_two hda2 hva2.symm ha2p2 hp2v.symm
      have : r ∈ ({v, p₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
      simpa using this,
    ha1_ne_t2 := by
      intro h; subst h
      have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm ha1p1 hp1u.symm
      have hm1 : t₁ ∈ ({u, p₁} : Finset V) := by
        rw [← hN]; exact (G.mem_neighborFinset a₁ t₁).mpr ht12.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1
      rcases hm1 with h1 | h1
      · exact G.ne_of_adj hut1 h1.symm
      · rw [← h1] at hdp1; omega,
    ha2_ne_t1 := by
      intro h; subst h
      have hN := neighborFinset_eq_pair_of_deg_two hda2 hva2.symm ha2p2 hp2v.symm
      have hm2 : t₂ ∈ ({v, p₂} : Finset V) := by
        rw [← hN]; exact (G.mem_neighborFinset a₂ t₂).mpr ht12
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm2
      rcases hm2 with h1 | h1
      · exact G.ne_of_adj ht2v.symm h1.symm
      · rw [← h1] at hdp2; omega,
    hy1_ne_y2 := by
      intro h; subst h
      rcases exists_unique_neighbor_of_deg_one hdy1 with ⟨w, _, huniq⟩
      exact huv ((huniq u huy1.symm).trans (huniq v hvy2.symm).symm),
    ha1_eq_of_p1v := fun hp => by
      have ha1_1 : a₁ ∈ oneThreadNbrs G v := by
        rw [mem_oneThreadNbrs]; exact ⟨hp ▸ ha1p1.symm, hda1, u, hua1.symm, huv, by omega⟩
      rcases Finset.card_eq_one.mp (isT21_structure hm hpq hv).2.2.2.2.1 with ⟨a₀, ha₀⟩
      have h1 : a₁ = a₀ := by simpa [ha₀] using ha1_1
      have h2 : a₂ = a₀ := by simpa [ha₀] using ha2
      exact h1.trans h2.symm,
    ha1_eq_of_p2u := fun hp => by
      have ha2_1 : a₂ ∈ oneThreadNbrs G u := by
        rw [mem_oneThreadNbrs]; exact ⟨hp ▸ ha2p2.symm, hda2, v, hva2.symm, huv.symm, by omega⟩
      rcases Finset.card_eq_one.mp (isT21_structure hm hpq hu).2.2.2.2.1 with ⟨a₀, ha₀⟩
      have h1 : a₁ = a₀ := by simpa [ha₀] using ha1
      have h2 : a₂ = a₀ := by simpa [ha₀] using ha2_1
      exact h1.trans h2.symm }
  by_cases hadj : G.Adj u v
  · by_cases ha12 : a₁ = a₂
    · exact no_T21_two_thread_adj_same hm D hadj ha12
    · exact no_T21_two_thread_adj_diff hm D hadj ha12
  · by_cases ha12 : a₁ = a₂
    · exact no_T21_two_thread_same_one hm D hadj ha12
    · exact no_T21_two_thread_gen hm D hadj ha12

/-! ## 4. 预排除构型（重 `1`-线串、邻接 `T21`、共坏点 `B3`、三 `L3` 细分三角形） -/

/-- `u, v ∈ {L3, L4}` 共享全部 3 条 `1`-线串 `a₁, a₂, a₃` 时可染色矛盾。 -/
private lemma no_three_oneThreads_L3L4 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a₁ a₂ a₃ : V}
    (hu : IsL3 G u ∨ IsL4 G u) (hv : IsL3 G v ∨ IsL4 G v) (huv : u ≠ v)
    (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (ha3 : a₃ ∈ oneThreadNbrs G u)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (hv1 : G.Adj a₁ v) (hv2 : G.Adj a₂ v) (hv3 : G.Adj a₃ v) : False := by
  classical
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hua2 : G.Adj u a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hua3 : G.Adj u a₃ := (mem_oneThreadNbrs.mp ha3).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have hda3 : G.degree a₃ = 2 := (mem_oneThreadNbrs.mp ha3).2.1
  have hdu3 : 3 ≤ G.degree u := by rcases hu with h | h <;> [have := h.1; have := h.1] <;> omega
  have hdv3 : 3 ≤ G.degree v := by rcases hv with h | h <;> [have := h.1; have := h.1] <;> omega
  have ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm hv1 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
    simpa using this
  have ha2_all : ∀ r, G.Adj a₂ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda2 hua2.symm hv2 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
    simpa using this
  have ha3_all : ∀ r, G.Adj a₃ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda3 hua3.symm hv3 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₃ r).mpr hr
    simpa using this
  have hside_info : ∀ {x : V}, (IsL3 G x ∨ IsL4 G x) →
      a₁ ∈ oneThreadNbrs G x → a₂ ∈ oneThreadNbrs G x → a₃ ∈ oneThreadNbrs G x →
      (∀ r, G.Adj x r → r = a₁ ∨ r = a₂ ∨ r = a₃ ∨ r ∈ leafNbrs G x) ∧
      ∃ A ⊆ L x, 3 ≤ A.card ∧ ∀ α ∈ A, ∀ y ∈ leafNbrs G x, α ∉ L y := by
    intro x hx hx1 hx2 hx3
    rcases hx with hL3 | hL4
    · have hst := isL3_structure hm hL3
      have hsub3 : ({a₁, a₂, a₃} : Finset V) ⊆ G.neighborFinset x := by
        intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact (G.mem_neighborFinset x r).mpr (mem_oneThreadNbrs.mp hx1).1
        · exact (G.mem_neighborFinset x r).mpr (mem_oneThreadNbrs.mp hx2).1
        · exact (G.mem_neighborFinset x r).mpr (mem_oneThreadNbrs.mp hx3).1
      have hNx : G.neighborFinset x = {a₁, a₂, a₃} := by
        symm; apply Finset.eq_of_subset_of_card_le hsub3
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23,
            SimpleGraph.card_neighborFinset_eq_degree, hst.1]
      have hLx4 : (L x).card = 4 := by rw [hm.list_card x]; simp [kappa, hst.1]
      refine ⟨fun r hr => ?_, L x, Finset.Subset.refl _, by omega,
        fun _ _ y hy => False.elim (by rw [hst.2.2.1] at hy; exact Finset.notMem_empty y hy)⟩
      have : r ∈ ({a₁, a₂, a₃} : Finset V) := by rw [← hNx]; exact (G.mem_neighborFinset x r).mpr hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · have hst := isL4_structure hm hpq hL4
      rcases Finset.card_eq_one.mp hst.2.2.1 with ⟨y, hy_eq⟩
      have hy : y ∈ leafNbrs G x := by rw [hy_eq]; simp
      have hLy : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, (mem_leafNbrs.mp hy).2]
      have hLx5 : (L x).card = 5 := by rw [hm.list_card x]; simp [kappa, hst.1]
      have hsub1 : ({a₁, a₂, a₃} : Finset V) ⊆ oneThreadNbrs G x := by
        intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl <;> assumption
      have h1eq : oneThreadNbrs G x = {a₁, a₂, a₃} := by
        symm; apply Finset.eq_of_subset_of_card_le hsub1
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23, hst.2.2.2.1]
      refine ⟨fun r hr => ?_, L x \ L y, Finset.sdiff_subset,
        by have := card_sdiff_ge (L x) (L y); omega, fun α hα y' hy' => ?_⟩
      · have hrN : r ∈ oneThreadNbrs G x ∪ leafNbrs G x := by
          rw [← hst.2.2.2.2.2.2.2.2]; exact (G.mem_neighborFinset x r).mpr hr
        rw [Finset.mem_union, h1eq] at hrN
        rcases hrN with hr1 | hrl
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hr1
          rcases hr1 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr hrl))
      · rw [hy_eq, Finset.mem_singleton] at hy'; subst hy'
        exact (Finset.mem_sdiff.mp hα).2
  have hv_a1 : a₁ ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hv1.symm, hda1, u, hua1.symm, huv, hdu3⟩
  have hv_a2 : a₂ ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hv2.symm, hda2, u, hua2.symm, huv, hdu3⟩
  have hv_a3 : a₃ ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hv3.symm, hda3, u, hua3.symm, huv, hdu3⟩
  rcases hside_info hu ha1 ha2 ha3 with ⟨hu_all, Au, hAu_sub, hAu3, hAu_leaf⟩
  rcases hside_info hv hv_a1 hv_a2 hv_a3 with ⟨hv_all, Av, hAv_sub, hAv3, hAv_leaf⟩
  rcases Finset.card_pos.mp (by omega : 0 < Au.card) with ⟨α, hαA⟩
  rcases exists_mem_sdiff_of_lt (A := Av) (B := {α})
    (by simp only [Finset.card_singleton]; omega) with ⟨β, hβA, hβα⟩
  rw [Finset.mem_singleton] at hβα
  have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  have hLa3 : (L a₃).card = 4 := by rw [hm.list_card a₃]; simp [kappa, hda3]
  rcases exists_mem_sdiff_of_lt (A := L a₁) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨c₁, hc1L, hc1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
  rcases exists_mem_sdiff_of_lt (A := L a₂) (B := {α, β, c₁})
    (by have := card_triple_le α β c₁; omega) with ⟨c₂, hc2L, hc2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
  rcases exists_mem_sdiff_of_lt (A := L a₃) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨c₃, hc3L, hc3N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
  have hleaf_pick : ∀ (x : V) (col : ℕ), (∀ y ∈ leafNbrs G x, col ∉ L y) →
      ∀ y ∈ leafNbrs G x, ∃ cy ∈ L y, cy ≠ col ∧ HasUniqueColor [c₁, c₂, c₃, cy] := by
    intro x col havoid y hy
    have hLy2 : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, (mem_leafNbrs.mp hy).2]
    rcases exists_fourth_unique_color (a := c₁) (b := c₂) (c := c₃) (by omega : 2 ≤ (L y).card)
      with ⟨cy, hcyL, huniq⟩
    exact ⟨cy, hcyL, fun h => havoid y hy (h ▸ hcyL), huniq⟩
  let S : Finset V := insert u (insert v (insert a₁ (insert a₂ (insert a₃
    (leafNbrs G u ∪ leafNbrs G v)))))
  have hlu_disj : Disjoint (leafNbrs G u) (leafNbrs G v) := by
    rw [Finset.disjoint_left]; intro y hy1 hy2
    rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hy1).2 with ⟨w, _, huniq⟩
    exact huv ((huniq u (mem_leafNbrs.mp hy1).1.symm).trans
      (huniq v (mem_leafNbrs.mp hy2).1.symm).symm)
  let ψ : V → ℕ := fun z =>
    if z = u then α else if z = v then β else if z = a₁ then c₁ else if z = a₂ then c₂
    else if z = a₃ then c₃
    else if hyu : z ∈ leafNbrs G u then (hleaf_pick u α (hAu_leaf α hαA) z hyu).choose
    else if hyv : z ∈ leafNbrs G v then (hleaf_pick v β (hAv_leaf β hβA) z hyv).choose
    else 0
  have hψu : ψ u = α := by simp [ψ]
  have hψv : ψ v = β := by simp [ψ, huv.symm]
  have hψa1 : ψ a₁ = c₁ := by
    simp [ψ, (ne_of_deg_ge_lt hdu3 hda1 (by omega)).symm,
      (ne_of_deg_ge_lt hdv3 hda1 (by omega)).symm]
  have hψa2 : ψ a₂ = c₂ := by
    simp [ψ, (ne_of_deg_ge_lt hdu3 hda2 (by omega)).symm,
      (ne_of_deg_ge_lt hdv3 hda2 (by omega)).symm, h12.symm]
  have hψa3 : ψ a₃ = c₃ := by
    simp [ψ, (ne_of_deg_ge_lt hdu3 hda3 (by omega)).symm,
      (ne_of_deg_ge_lt hdv3 hda3 (by omega)).symm, h13.symm, h23.symm]
  have hψlu : ∀ y (hy : y ∈ leafNbrs G u), ψ y = (hleaf_pick u α (hAu_leaf α hαA) y hy).choose := by
    intro y hy; have hdy := (mem_leafNbrs.mp hy).2
    simp [ψ, (ne_of_deg_ge_lt hdu3 hdy (by omega)).symm, (ne_of_deg_ge_lt hdv3 hdy (by omega)).symm,
      ne_of_deg_eq_ne hdy hda1 (by omega), ne_of_deg_eq_ne hdy hda2 (by omega),
      ne_of_deg_eq_ne hdy hda3 (by omega), hy]
  have hψlv : ∀ y (hy : y ∈ leafNbrs G v), ψ y = (hleaf_pick v β (hAv_leaf β hβA) y hy).choose := by
    intro y hy; have hdy := (mem_leafNbrs.mp hy).2
    have hnotu : y ∉ leafNbrs G u := fun h => Finset.disjoint_left.mp hlu_disj h hy
    simp [ψ, (ne_of_deg_ge_lt hdu3 hdy (by omega)).symm, (ne_of_deg_ge_lt hdv3 hdy (by omega)).symm,
      ne_of_deg_eq_ne hdy hda1 (by omega), ne_of_deg_eq_ne hdy hda2 (by omega),
      ne_of_deg_eq_ne hdy hda3 (by omega), hnotu, hy]
  have hS_closed : ∀ x ∈ S, ∀ r, G.Adj x r → r ∈ S := by
    intro x hx r hxr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | hlu | hlv
    · rcases hu_all r hxr with rfl | rfl | rfl | hrL
      · simp
      · simp
      · simp
      · simp [hrL]
    · rcases hv_all r hxr with rfl | rfl | rfl | hrL
      · simp
      · simp
      · simp
      · simp [hrL]
    · rcases ha1_all r hxr with rfl | rfl <;> simp
    · rcases ha2_all r hxr with rfl | rfl <;> simp
    · rcases ha3_all r hxr with rfl | rfl <;> simp
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hlu).2 with ⟨w, _, huniq⟩
      have hru : r = u := (huniq r hxr).trans (huniq u (mem_leafNbrs.mp hlu).1.symm).symm
      rw [hru]; simp
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hlv).2 with ⟨w, _, huniq⟩
      have hrv : r = v := (huniq r hxr).trans (huniq v (mem_leafNbrs.mp hlv).1.symm).symm
      rw [hrv]; simp
  have hallS : S = Finset.univ := eq_univ_of_closed hm.conn (v₀ := u) (by simp [S]) hS_closed
  rcases exists_admissible_coloring hm (S := S) ⟨u, by simp [S]⟩ with ⟨adm⟩
  apply adm.contradiction hm ψ (fun z hz => False.elim (hz (hallS ▸ Finset.mem_univ z)))
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_union] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | hlu | hlv
    · rw [hψu]; exact hAu_sub hαA
    · rw [hψv]; exact hAv_sub hβA
    · rw [hψa1]; exact hc1L
    · rw [hψa2]; exact hc2L
    · rw [hψa3]; exact hc3L
    · rw [hψlu z hlu]; exact (hleaf_pick u α (hAu_leaf α hαA) z hlu).choose_spec.1
    · rw [hψlv z hlv]; exact (hleaf_pick v β (hAv_leaf β hβA) z hlv).choose_spec.1
  · intro z₁ z₂ h12' _
    have hz1 : z₁ ∈ S := hallS ▸ Finset.mem_univ z₁
    simp only [S, Finset.mem_insert, Finset.mem_union] at hz1
    rcases hz1 with rfl | rfl | rfl | rfl | rfl | hlu | hlv
    · rcases hu_all z₂ h12' with rfl | rfl | rfl | hzl
      · rw [hψu, hψa1]; exact Ne.symm hc1N.1
      · rw [hψu, hψa2]; exact Ne.symm hc2N.1
      · rw [hψu, hψa3]; exact Ne.symm hc3N.1
      · rw [hψu, hψlu z₂ hzl]; exact (hleaf_pick z₁ α (hAu_leaf α hαA) z₂ hzl).choose_spec.2.1.symm
    · rcases hv_all z₂ h12' with rfl | rfl | rfl | hzl
      · rw [hψv, hψa1]; exact Ne.symm hc1N.2
      · rw [hψv, hψa2]; exact Ne.symm hc2N.2.1
      · rw [hψv, hψa3]; exact Ne.symm hc3N.2
      · rw [hψv, hψlv z₂ hzl]; exact (hleaf_pick z₁ β (hAv_leaf β hβA) z₂ hzl).choose_spec.2.1.symm
    · rcases ha1_all z₂ h12' with rfl | rfl
      · rw [hψa1, hψu]; exact hc1N.1
      · rw [hψa1, hψv]; exact hc1N.2
    · rcases ha2_all z₂ h12' with rfl | rfl
      · rw [hψa2, hψu]; exact hc2N.1
      · rw [hψa2, hψv]; exact hc2N.2.1
    · rcases ha3_all z₂ h12' with rfl | rfl
      · rw [hψa3, hψu]; exact hc3N.1
      · rw [hψa3, hψv]; exact hc3N.2
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hlu).2 with ⟨w, _, huniq⟩
      have hz2u : z₂ = u := (huniq z₂ h12').trans (huniq u (mem_leafNbrs.mp hlu).1.symm).symm
      rw [hz2u, hψlu z₁ hlu, hψu]; exact (hleaf_pick u α (hAu_leaf α hαA) z₁ hlu).choose_spec.2.1
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hlv).2 with ⟨w, _, huniq⟩
      have hz2v : z₂ = v := (huniq z₂ h12').trans (huniq v (mem_leafNbrs.mp hlv).1.symm).symm
      rw [hz2v, hψlv z₁ hlv, hψv]; exact (hleaf_pick v β (hAv_leaf β hβA) z₁ hlv).choose_spec.2.1
  · intro w hwS; exact False.elim (hwS (hallS ▸ Finset.mem_univ w))
  · intro w hwS; exact False.elim (hwS (hallS ▸ Finset.mem_univ w))
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_union] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | hlu | hlv
    · rcases hu with hL3 | hL4
      · exact pcf_at_deg_three_of_two_distinct hL3.1 hua1 hua2 h12
          (by rw [hψa1, hψa2]; exact Ne.symm hc2N.2.2)
      · rcases Finset.card_eq_one.mp (isL4_structure hm hpq hL4).2.2.1 with ⟨y, hy_eq⟩
        have hy : y ∈ leafNbrs G z := by rw [hy_eq]; simp
        exact pcf_at_of_hasUniqueColor_four hua1 hua2 hua3 (mem_leafNbrs.mp hy).1
          (fun r hr => by
            rcases hu_all r hr with h | h | h | hL
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · rw [hy_eq, Finset.mem_singleton] at hL; exact Or.inr (Or.inr (Or.inr hL)))
          (by rw [hψa1, hψa2, hψa3, hψlu y hy]
              exact (hleaf_pick z α (hAu_leaf α hαA) y hy).choose_spec.2.2)
    · rcases hv with hL3 | hL4
      · exact pcf_at_deg_three_of_two_distinct hL3.1 hv1.symm hv2.symm h12
          (by rw [hψa1, hψa2]; exact Ne.symm hc2N.2.2)
      · rcases Finset.card_eq_one.mp (isL4_structure hm hpq hL4).2.2.1 with ⟨y, hy_eq⟩
        have hy : y ∈ leafNbrs G z := by rw [hy_eq]; simp
        exact pcf_at_of_hasUniqueColor_four hv1.symm hv2.symm hv3.symm (mem_leafNbrs.mp hy).1
          (fun r hr => by
            rcases hv_all r hr with h | h | h | hL
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · rw [hy_eq, Finset.mem_singleton] at hL; exact Or.inr (Or.inr (Or.inr hL)))
          (by rw [hψa1, hψa2, hψa3, hψlv y hy]
              exact (hleaf_pick z β (hAv_leaf β hβA) y hy).choose_spec.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda1 hua1.symm hv1 huv
        (by rw [hψu, hψv]; exact Ne.symm hβα)
    · exact pcf_at_of_two_distinct_neighbors hda2 hua2.symm hv2 huv
        (by rw [hψu, hψv]; exact Ne.symm hβα)
    · exact pcf_at_of_two_distinct_neighbors hda3 hua3.symm hv3 huv
        (by rw [hψu, hψv]; exact Ne.symm hβα)
    · exact pcf_at_deg_one (mem_leafNbrs.mp hlu).2 (mem_leafNbrs.mp hlu).1.symm
    · exact pcf_at_deg_one (mem_leafNbrs.mp hlv).2 (mem_leafNbrs.mp hlv).1.symm

/-- 两个 `B3` 顶点既共享坏邻点 `b` 又通过两条 `1`-线串 `a₁, a₂` 相连时可染色矛盾。 -/
private lemma no_two_oneThreads_B3_shared_bad {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a₁ a₂ b : V}
    (hu : IsB3 G u) (hv : IsB3 G v) (huv : u ≠ v)
    (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (h12 : a₁ ≠ a₂)
    (hv1 : G.Adj a₁ v) (hv2 : G.Adj a₂ v) (hbu : b ∈ badNbrs G u) (hbv : b ∈ badNbrs G v) :
    False := by
  classical
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hua2 : G.Adj u a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have hub : G.Adj u b := (mem_badNbrs.mp hbu).1
  have hvb : G.Adj v b := (mem_badNbrs.mp hbv).1
  have hbad : IsBad G b := (mem_badNbrs.mp hbu).2
  have hdb4 : 4 ≤ G.degree b := hbad.1
  have hdu3 : G.degree u = 3 := hu.1
  have hdv3 : G.degree v = 3 := hv.1
  have ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm hv1 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
    simpa using this
  have ha2_all : ∀ r, G.Adj a₂ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda2 hua2.symm hv2 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
    simpa using this
  have hu_all : ∀ r, G.Adj u r → r = a₁ ∨ r = a₂ ∨ r = b := by
    have hN : G.neighborFinset u = {a₁, a₂, b} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact (G.mem_neighborFinset u r).mpr hua1
        · exact (G.mem_neighborFinset u r).mpr hua2
        · exact (G.mem_neighborFinset u r).mpr hub
      · rw [Finset.card_insert_of_notMem
              (by simp [h12, (ne_of_deg_ge_lt hdb4 hda1 (by omega)).symm]),
            Finset.card_pair (ne_of_deg_ge_lt hdb4 hda2 (by omega)).symm,
            SimpleGraph.card_neighborFinset_eq_degree, hdu3]
    intro r hr; have : r ∈ ({a₁, a₂, b} : Finset V) := by
      rw [← hN]; exact (G.mem_neighborFinset u r).mpr hr
    simpa using this
  have hv_all : ∀ r, G.Adj v r → r = a₁ ∨ r = a₂ ∨ r = b := by
    have hN : G.neighborFinset v = {a₁, a₂, b} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact (G.mem_neighborFinset v r).mpr hv1.symm
        · exact (G.mem_neighborFinset v r).mpr hv2.symm
        · exact (G.mem_neighborFinset v r).mpr hvb
      · rw [Finset.card_insert_of_notMem
              (by simp [h12, (ne_of_deg_ge_lt hdb4 hda1 (by omega)).symm]),
            Finset.card_pair (ne_of_deg_ge_lt hdb4 hda2 (by omega)).symm,
            SimpleGraph.card_neighborFinset_eq_degree, hdv3]
    intro r hr; have : r ∈ ({a₁, a₂, b} : Finset V) := by
      rw [← hN]; exact (G.mem_neighborFinset v r).mpr hr
    simpa using this
  have hcoreb : coreNbrs G b = {u, v} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact mem_coreNbrs.mpr ⟨hub.symm, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hvb.symm, by omega⟩
    · rw [Finset.card_pair huv]; have := hbad.2; unfold coreDeg at this; omega
  have hb_all : ∀ r, G.Adj b r → r = u ∨ r = v ∨ r ∈ leafNbrs G b := by
    intro r hr; have hdr := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hr, h1⟩))
    · have hc : r ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hr, by omega⟩
      rw [hcoreb, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  let Y := leafNbrs G b
  have hYcard : Y.card = G.degree b - 2 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLv4 : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv3]
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  rcases Finset.card_pos.mp (by omega : 0 < (L u).card) with ⟨α, hαL⟩
  rcases exists_mem_sdiff_of_lt (A := L v) (B := {α})
    (by simp only [Finset.card_singleton]; omega) with ⟨β, hβL, hβα⟩
  rw [Finset.mem_singleton] at hβα
  let R : Finset ℕ := L b \ {β, α}
  have hRcard : (if β = α then Y.card + 1 else Y.card) ≤ R.card := by
    dsimp only [R]; simp only [hβα, ite_false]
    have := card_sdiff_ge (L b) {β, α}; have := Finset.card_le_two (a := β) (b := α); omega
  rcases bad_fixed_color_extension (by omega : 2 ≤ Y.card)
    (fun p hp => by rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2])
    (by simp [R]) hRcard with ⟨cb, hcbR, fY, hfY, γb, hγb⟩
  simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
  rcases exists_mem_sdiff_of_lt (A := L a₁) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨c₁, hc1L, hc1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
  rcases exists_mem_sdiff_of_lt (A := L a₂) (B := {α, β, c₁})
    (by have := card_triple_le α β c₁; omega) with ⟨c₂, hc2L, hc2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
  let S : Finset V := insert u (insert v (insert a₁ (insert a₂ (insert b Y))))
  have hallS : S = Finset.univ := by
    apply eq_univ_of_closed hm.conn (v₀ := u) (by simp [S])
    intro x hx r hxr; simp only [S, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | hxY
    · rcases hu_all r hxr with rfl | rfl | rfl <;> simp
    · rcases hv_all r hxr with rfl | rfl | rfl <;> simp
    · rcases ha1_all r hxr with rfl | rfl <;> simp
    · rcases ha2_all r hxr with rfl | rfl <;> simp
    · rcases hb_all r hxr with rfl | rfl | hrY
      · simp
      · simp
      · simp [Y, hrY]
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hxY).2 with ⟨w, _, huniq⟩
      have hrb : r = b := (huniq r hxr).trans (huniq b (mem_leafNbrs.mp hxY).1.symm).symm
      rw [hrb]; simp
  let ψ : V → ℕ := fun z =>
    if z = u then α else if z = v then β else if z = a₁ then c₁ else if z = a₂ then c₂
    else if z = b then cb else fY z
  have hψu : ψ u = α := by simp [ψ]
  have hψv : ψ v = β := by simp [ψ, huv.symm]
  have hψa1 : ψ a₁ = c₁ := by
    simp [ψ, ne_of_deg_eq_ne hda1 hdu3 (by omega), ne_of_deg_eq_ne hda1 hdv3 (by omega)]
  have hψa2 : ψ a₂ = c₂ := by
    simp [ψ, ne_of_deg_eq_ne hda2 hdu3 (by omega), ne_of_deg_eq_ne hda2 hdv3 (by omega), h12.symm]
  have hψb : ψ b = cb := by
    simp [ψ, ne_of_deg_ge_lt hdb4 hdu3 (by omega), ne_of_deg_ge_lt hdb4 hdv3 (by omega),
      ne_of_deg_ge_lt hdb4 hda1 (by omega), ne_of_deg_ge_lt hdb4 hda2 (by omega)]
  have hψY : ∀ y ∈ Y, ψ y = fY y := by
    intro y hy; have hdy := (mem_leafNbrs.mp hy).2
    simp [ψ, ne_of_deg_eq_ne hdy hdu3 (by omega), ne_of_deg_eq_ne hdy hdv3 (by omega),
      ne_of_deg_eq_ne hdy hda1 (by omega), ne_of_deg_eq_ne hdy hda2 (by omega),
      (ne_of_deg_ge_lt hdb4 hdy (by omega)).symm]
  rcases exists_admissible_coloring hm (S := S) ⟨u, by simp [S]⟩ with ⟨adm⟩
  apply adm.contradiction hm ψ (fun z hz => False.elim (hz (hallS ▸ Finset.mem_univ z)))
  · intro z hz; simp only [S, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | hzY
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψa1]; exact hc1L
    · rw [hψa2]; exact hc2L
    · rw [hψb]; exact hcbR.1
    · rw [hψY z hzY]; exact (hfY z hzY).1
  · intro z₁ z₂ h12' _
    have hz1 : z₁ ∈ S := hallS ▸ Finset.mem_univ z₁
    simp only [S, Finset.mem_insert] at hz1
    rcases hz1 with rfl | rfl | rfl | rfl | rfl | hzY
    · rcases hu_all z₂ h12' with rfl | rfl | rfl
      · rw [hψu, hψa1]; exact Ne.symm hc1N.1
      · rw [hψu, hψa2]; exact Ne.symm hc2N.1
      · rw [hψu, hψb]; exact Ne.symm hcbR.2.2
    · rcases hv_all z₂ h12' with rfl | rfl | rfl
      · rw [hψv, hψa1]; exact Ne.symm hc1N.2
      · rw [hψv, hψa2]; exact Ne.symm hc2N.2.1
      · rw [hψv, hψb]; exact Ne.symm hcbR.2.1
    · rcases ha1_all z₂ h12' with rfl | rfl
      · rw [hψa1, hψu]; exact hc1N.1
      · rw [hψa1, hψv]; exact hc1N.2
    · rcases ha2_all z₂ h12' with rfl | rfl
      · rw [hψa2, hψu]; exact hc2N.1
      · rw [hψa2, hψv]; exact hc2N.2.1
    · rcases hb_all z₂ h12' with rfl | rfl | hz2Y
      · rw [hψb, hψu]; exact hcbR.2.2
      · rw [hψb, hψv]; exact hcbR.2.1
      · rw [hψb, hψY z₂ hz2Y]; exact (hfY z₂ hz2Y).2.symm
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hzY).2 with ⟨w, _, huniq⟩
      have hz2b : z₂ = b := (huniq z₂ h12').trans (huniq b (mem_leafNbrs.mp hzY).1.symm).symm
      rw [hz2b, hψY z₁ hzY, hψb]; exact (hfY z₁ hzY).2
  · intro w hwS; exact False.elim (hwS (hallS ▸ Finset.mem_univ w))
  · intro w hwS; exact False.elim (hwS (hallS ▸ Finset.mem_univ w))
  · intro z hzS _
    simp only [S, Finset.mem_insert] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | hzY
    · exact pcf_at_deg_three_of_two_distinct hdu3 hua1 hua2 h12
        (by rw [hψa1, hψa2]; exact Ne.symm hc2N.2.2)
    · exact pcf_at_deg_three_of_two_distinct hdv3 hv1.symm hv2.symm h12
        (by rw [hψa1, hψa2]; exact Ne.symm hc2N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda1 hua1.symm hv1 huv
        (by rw [hψu, hψv]; exact Ne.symm hβα)
    · exact pcf_at_of_two_distinct_neighbors hda2 hua2.symm hv2 huv
        (by rw [hψu, hψv]; exact Ne.symm hβα)
    · refine pcf_at_bad_of_count_one hub.symm hvb.symm hb_all (γ := γb) ?_
      have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
        ext p; simp only [Finset.mem_filter]; exact and_congr_right fun hp => by rw [hψY p hp]
      rw [hfeq, hψv, hψu]; exact hγb
    · exact pcf_at_deg_one (mem_leafNbrs.mp hzY).2 (mem_leafNbrs.mp hzY).1.symm

/-- 重 `1`-线串单侧余团接口（用于 `L3 / B3 / L4` 共享两条 `1`-线串的通用归约）。 -/
private structure DoubleOneRem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset ℕ) (u v a₁ a₂ : V) where
  S_rem : Finset V
  e : V
  p : V
  huS : u ∈ S_rem
  heS : e ∈ S_rem
  ha1_not : a₁ ∉ S_rem
  ha2_not : a₂ ∉ S_rem
  hp_not : p ∉ S_rem
  hp_ne_v : p ≠ v
  hep : G.Adj e p
  hdp3 : 3 ≤ G.degree p
  he_type : (G.degree e = 2 ∧ e ∈ oneThreadNbrs G u) ∨ (IsBad G e ∧ G.Adj u e)
  hdeg3_only : ∀ x ∈ S_rem, 3 ≤ G.degree x → x = u ∨ (IsBad G x ∧ G.Adj u x)
  hdeg2_only : ∀ x ∈ S_rem, G.degree x = 2 → x = e ∧ x ∈ oneThreadNbrs G u ∧ G.Adj u x
  hdeg1_only : ∀ x ∈ S_rem, G.degree x = 1 → ∃ w ∈ S_rem, 3 ≤ G.degree w ∧ G.Adj x w
  hout : ∀ w, w ∉ S_rem → ∀ s ∈ S_rem, G.Adj w s →
    (s = u ∧ (w = a₁ ∨ w = a₂)) ∨ (s = e ∧ w = p)
  hext : ∀ (φ φs : V → ℕ), ∃ A ⊆ L u, 2 ≤ A.card ∧
    ∀ α ∈ A, ∀ c₁ c₂ : ℕ, c₁ ≠ α → c₂ ≠ α → c₁ ≠ c₂ →
      ∃ ψu : V → ℕ, ψu u = α ∧
        (∀ x ∈ S_rem, ψu x ∈ L x) ∧
        (∀ x ∈ S_rem, ∀ y ∈ S_rem, G.Adj x y → ψu x ≠ ψu y) ∧
        ψu e ≠ φ p ∧ ψu e ≠ φs p ∧
        (∀ ψ : V → ℕ, (∀ x ∈ S_rem, ψ x = ψu x) → ψ a₁ = c₁ → ψ a₂ = c₂ → ψ p = φ p →
          ∀ x ∈ S_rem, ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → ψ z = ψ y → z = y)

private lemma doubleOneRem_of_L3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a₁ a₂ : V}
    (hu : IsL3 G u) (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (h12 : a₁ ≠ a₂)
    (hno3 : ∀ a₃ ∈ oneThreadNbrs G u, a₃ ≠ a₁ → a₃ ≠ a₂ → ¬ G.Adj a₃ v) :
    Nonempty (DoubleOneRem G L u v a₁ a₂) := by
  classical
  rcases isL3_unpack_one hm hu ha1 with ⟨b₁, b₂, hb1, hb2, ha1b1, ha1b2, hb12, hu_all⟩
  have hpick : ∃ a₃, a₃ ∈ oneThreadNbrs G u ∧ a₃ ≠ a₁ ∧ a₃ ≠ a₂ ∧
      ∀ r, G.Adj u r → r = a₁ ∨ r = a₂ ∨ r = a₃ := by
    rcases hu_all a₂ (mem_oneThreadNbrs.mp ha2).1 with h | h | h
    · exact False.elim (h12 h.symm)
    · exact ⟨b₂, hb2, ha1b2.symm, h ▸ hb12.symm, fun r hr => by
        rcases hu_all r hr with hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inl (hr'.trans h.symm))
        · exact Or.inr (Or.inr hr')⟩
    · exact ⟨b₁, hb1, ha1b1.symm, h ▸ hb12, fun r hr => by
        rcases hu_all r hr with hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inr hr')
        · exact Or.inr (Or.inl (hr'.trans h.symm))⟩
  rcases hpick with ⟨a₃, ha3, h31, h32, hu_all'⟩
  have hdu3 : G.degree u = 3 := hu.1
  rcases oneThreadNbr_other_endpoint hm (by omega) ha3 with ⟨p₃, ha3p3, hp3u, hdp3, _, _⟩
  have hua3 : G.Adj u a₃ := (mem_oneThreadNbrs.mp ha3).1
  have hda3 : G.degree a₃ = 2 := (mem_oneThreadNbrs.mp ha3).2.1
  have hp3v : p₃ ≠ v := fun h => hno3 a₃ ha3 h31 h32 (h ▸ ha3p3)
  have ha3_all : ∀ r, G.Adj a₃ r → r = u ∨ r = p₃ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda3 hua3.symm ha3p3 hp3u.symm
    have : r ∈ ({u, p₃} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₃ r).mpr hr
    simpa using this
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLa3 : (L a₃).card = 4 := by rw [hm.list_card a₃]; simp [kappa, hda3]
  refine ⟨{
    S_rem := {u, a₃}, e := a₃, p := p₃,
    huS := by simp, heS := by simp,
    ha1_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha1).1).symm, h31.symm⟩,
    ha2_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha2).1).symm, h32.symm⟩,
    hp_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp3u, (G.ne_of_adj ha3p3).symm⟩,
    hp_ne_v := hp3v, hep := ha3p3, hdp3 := hdp3,
    he_type := Or.inl ⟨hda3, ha3⟩,
    hdeg3_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · omega,
    hdeg2_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · omega
      · exact ⟨rfl, ha3, hua3⟩,
    hdeg1_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega,
    hout := fun w hwS s hsS hws => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
      rcases hsS with rfl | rfl
      · rcases hu_all' w hws.symm with rfl | rfl | rfl
        · exact Or.inl ⟨rfl, Or.inl rfl⟩
        · exact Or.inl ⟨rfl, Or.inr rfl⟩
        · exact False.elim (hwS (by simp))
      · rcases ha3_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr ⟨rfl, rfl⟩,
    hext := fun φ φs => by
      refine ⟨L u \ {φ p₃}, Finset.sdiff_subset,
        by have := card_sdiff_ge (L u) {φ p₃}; simp only [Finset.card_singleton] at this; omega,
        fun α hα c₁ c₂ _ _ hc12 => ?_⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hα
      rcases exists_mem_sdiff_of_lt (A := L a₃) (B := {φ p₃, φs p₃, α})
        (by have := card_triple_le (φ p₃) (φs p₃) α; omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      let ψu : V → ℕ := fun z => if z = u then α else c₃
      have hψu : ψu u = α := by simp [ψu]
      have hψa3 : ψu a₃ = c₃ := by simp [ψu, (G.ne_of_adj hua3).symm]
      refine ⟨ψu, hψu, ?_, ?_, by rw [hψa3]; exact hc3N.1, by rw [hψa3]; exact hc3N.2.1, ?_⟩
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · rw [hψu]; exact hα.1
        · rw [hψa3]; exact hc3L
      · intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (G.ne_of_adj hxy rfl)
        · rw [hψu, hψa3]; exact Ne.symm hc3N.2.2
        · rw [hψa3, hψu]; exact hc3N.2.2
        · exact False.elim (G.ne_of_adj hxy rfl)
      · intro ψ hagree ha1c ha2c hpc x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact pcf_at_deg_three_of_two_distinct hdu3 (mem_oneThreadNbrs.mp ha1).1
            (mem_oneThreadNbrs.mp ha2).1 h12 (by rw [ha1c, ha2c]; exact hc12)
        · exact pcf_at_of_two_distinct_neighbors hda3 hua3.symm ha3p3 hp3u.symm
            (by rw [hagree u (by simp), hψu, hpc]; exact hα.2) }⟩

private lemma doubleOneRem_of_B3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a₁ a₂ : V}
    (hu : IsB3 G u) (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (h12 : a₁ ≠ a₂)
    (hnoshare : ∀ b ∈ badNbrs G u, ¬ G.Adj b v) :
    Nonempty (DoubleOneRem G L u v a₁ a₂) := by
  classical
  rcases isB3_unpack_one hm hpq hu ha1 with
    ⟨a', b, h, ha', hb, ha1a', ha1b, ha'b, hu_all, hbh, hhu, hdh3, _, hb_all⟩
  have ha'_eq : a' = a₂ := by
    rcases hu_all a₂ (mem_oneThreadNbrs.mp ha2).1 with h1 | h1 | h1
    · exact False.elim (h12 h1.symm)
    · exact h1.symm
    · exact False.elim (ne_of_deg_ge_lt (mem_badNbrs.mp hb).2.1 (mem_oneThreadNbrs.mp ha2).2.1
        (by omega) h1.symm)
  subst ha'_eq
  have hub : G.Adj u b := (mem_badNbrs.mp hb).1
  have hbad : IsBad G b := (mem_badNbrs.mp hb).2
  have hdu3 : G.degree u = 3 := hu.1
  have hdb4 : 4 ≤ G.degree b := hbad.1
  have hhv : h ≠ v := fun heq => hnoshare b hb (heq ▸ hbh)
  let Y := leafNbrs G b
  have hYcard : Y.card = G.degree b - 2 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  let S_rem : Finset V := insert u (insert b Y)
  refine ⟨{
    S_rem := S_rem, e := b, p := h,
    huS := by simp [S_rem], heS := by simp [S_rem],
    ha1_not := by
      simp only [S_rem, Finset.mem_insert, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha1).1).symm, ha1b,
        fun hmY => by
          have := (mem_leafNbrs.mp hmY).2; have := (mem_oneThreadNbrs.mp ha1).2.1; omega⟩,
    ha2_not := by
      simp only [S_rem, Finset.mem_insert, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha2).1).symm, ha'b,
        fun hmY => by
          have := (mem_leafNbrs.mp hmY).2; have := (mem_oneThreadNbrs.mp ha2).2.1; omega⟩,
    hp_not := by
      simp only [S_rem, Finset.mem_insert, not_or]
      exact ⟨hhu, (G.ne_of_adj hbh).symm, fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩,
    hp_ne_v := hhv, hep := hbh, hdp3 := hdh3,
    he_type := Or.inr ⟨hbad, hub⟩,
    hdeg3_only := fun x hx hdx => by
      simp only [S_rem, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hxY
      · exact Or.inl rfl
      · exact Or.inr ⟨hbad, hub⟩
      · have := (mem_leafNbrs.mp hxY).2; omega,
    hdeg2_only := fun x hx hdx => by
      simp only [S_rem, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hxY
      · omega
      · omega
      · have := (mem_leafNbrs.mp hxY).2; omega,
    hdeg1_only := fun x hx hdx => by
      simp only [S_rem, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hxY
      · omega
      · omega
      · exact ⟨b, by simp [S_rem], by omega, (mem_leafNbrs.mp hxY).1.symm⟩,
    hout := fun w hwS s hsS hws => by
      simp only [S_rem, Finset.mem_insert] at hsS
      rcases hsS with rfl | rfl | hsY
      · rcases hu_all w hws.symm with rfl | rfl | rfl
        · exact Or.inl ⟨rfl, Or.inl rfl⟩
        · exact Or.inl ⟨rfl, Or.inr rfl⟩
        · exact False.elim (hwS (by simp [S_rem]))
      · rcases hb_all w hws.symm with rfl | rfl | hwY
        · exact False.elim (hwS (by simp [S_rem]))
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hwS (by simp [S_rem, Y, hwY]))
      · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hsY).2 with ⟨z, _, huniq⟩
        have hwb : w = b := (huniq w hws.symm).trans (huniq b (mem_leafNbrs.mp hsY).1.symm).symm
        exact False.elim (hwS (by rw [hwb]; simp [S_rem])),
    hext := fun φ φs => by
      refine ⟨L u, Finset.Subset.refl _, by omega, fun α hα c₁ c₂ _ _ hc12 => ?_⟩
      let R : Finset ℕ := L b \ {φ h, φs h, α}
      have hRcard : (if φ h = α then Y.card + 1 else Y.card) ≤ R.card := by
        dsimp only [R]
        by_cases hEq : φ h = α
        · simp only [hEq, ite_true]
          have hset : ({α, φs h, α} : Finset ℕ) = {α, φs h} := by ext z; simp; tauto
          rw [hset]
          have := card_sdiff_ge (L b) {α, φs h}; have := Finset.card_le_two (a := α) (b := φs h)
          omega
        · simp only [hEq, ite_false]
          have := card_sdiff_ge (L b) {φ h, φs h, α}
          have := card_triple_le (φ h) (φs h) α; omega
      rcases bad_fixed_color_extension (by omega : 2 ≤ Y.card)
        (fun p hp => by rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2])
        (by simp [R]) hRcard with ⟨cb, hcbR, fY, hfY, γb, hγb⟩
      simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
      let ψu : V → ℕ := fun z => if z = u then α else if z = b then cb else fY z
      have hψu : ψu u = α := by simp [ψu]
      have hψb : ψu b = cb := by simp [ψu, (G.ne_of_adj hub).symm]
      have hψY : ∀ y ∈ Y, ψu y = fY y := by
        intro y hy; have hdy := (mem_leafNbrs.mp hy).2
        simp [ψu, ne_of_deg_eq_ne hdy hdu3 (by omega), (ne_of_deg_ge_lt hdb4 hdy (by omega)).symm]
      refine ⟨ψu, hψu, ?_, ?_, by rw [hψb]; exact hcbR.2.1, by rw [hψb]; exact hcbR.2.2.1, ?_⟩
      · intro x hx; simp only [S_rem, Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxY
        · rw [hψu]; exact hα
        · rw [hψb]; exact hcbR.1
        · rw [hψY x hxY]; exact (hfY x hxY).1
      · intro x hx y hy hxy
        simp only [S_rem, Finset.mem_insert] at hx hy
        rcases hx with rfl | rfl | hxY
        · rcases hu_all y hxy with rfl | rfl | rfl
          · exact False.elim (by
              rcases hy with hy | hy | hy
              · exact G.ne_of_adj (mem_oneThreadNbrs.mp ha1).1 hy.symm
              · exact ha1b hy
              · have := (mem_leafNbrs.mp hy).2; have := (mem_oneThreadNbrs.mp ha1).2.1; omega)
          · exact False.elim (by
              rcases hy with hy | hy | hy
              · exact G.ne_of_adj (mem_oneThreadNbrs.mp ha2).1 hy.symm
              · exact ha'b hy
              · have := (mem_leafNbrs.mp hy).2; have := (mem_oneThreadNbrs.mp ha2).2.1; omega)
          · rw [hψu, hψb]; exact Ne.symm hcbR.2.2.2
        · rcases hb_all y hxy with rfl | rfl | hyY
          · rw [hψb, hψu]; exact hcbR.2.2.2
          · exact False.elim (by
              rcases hy with hy | hy | hy
              · exact hhu hy
              · exact G.ne_of_adj hbh hy.symm
              · have := (mem_leafNbrs.mp hy).2; omega)
          · rw [hψb, hψY y hyY]; exact (hfY y hyY).2.symm
        · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hxY).2 with ⟨w, _, huniq⟩
          have hyb : y = b := (huniq y hxy).trans (huniq b (mem_leafNbrs.mp hxY).1.symm).symm
          rw [hyb, hψY x hxY, hψb]; exact (hfY x hxY).2
      · intro ψ hagree ha1c ha2c hpc x hx
        simp only [S_rem, Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxY
        · exact pcf_at_deg_three_of_two_distinct hdu3 (mem_oneThreadNbrs.mp ha1).1
            (mem_oneThreadNbrs.mp ha2).1 h12 (by rw [ha1c, ha2c]; exact hc12)
        · refine pcf_at_bad_of_count_one hub.symm hbh hb_all (γ := γb) ?_
          have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
            ext p; simp only [Finset.mem_filter]
            exact and_congr_right fun hp => by rw [hagree p (by simp [S_rem, Y, hp]), hψY p hp]
          rw [hfeq, hpc, hagree u (by simp [S_rem]), hψu]; exact hγb
        · exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm }⟩

private lemma doubleOneRem_of_L4 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a₁ a₂ : V}
    (hu : IsL4 G u) (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (h12 : a₁ ≠ a₂)
    (hno3 : ∀ a₃ ∈ oneThreadNbrs G u, a₃ ≠ a₁ → a₃ ≠ a₂ → ¬ G.Adj a₃ v) :
    Nonempty (DoubleOneRem G L u v a₁ a₂) := by
  classical
  rcases isL4_unpack_one hm hpq hu ha1 with
    ⟨y, b₁, b₂, hy, hb1, hb2, ha1y, ha1b1, ha1b2, hyb1, hyb2, hb12, hu_all⟩
  have hpick : ∃ a₃, a₃ ∈ oneThreadNbrs G u ∧ a₃ ≠ a₁ ∧ a₃ ≠ a₂ ∧ y ≠ a₃ ∧
      ∀ r, G.Adj u r → r = a₁ ∨ r = a₂ ∨ r = a₃ ∨ r = y := by
    rcases hu_all a₂ (mem_oneThreadNbrs.mp ha2).1 with h | h | h | h
    · exact False.elim (h12 h.symm)
    · exact False.elim (ne_of_deg_eq_ne (mem_oneThreadNbrs.mp ha2).2.1 (mem_leafNbrs.mp hy).2
        (by omega) h)
    · exact ⟨b₂, hb2, ha1b2.symm, h ▸ hb12.symm, hyb2, fun r hr => by
        rcases hu_all r hr with hr' | hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inr (Or.inr hr'))
        · exact Or.inr (Or.inl (hr'.trans h.symm))
        · exact Or.inr (Or.inr (Or.inl hr'))⟩
    · exact ⟨b₁, hb1, ha1b1.symm, h ▸ hb12, hyb1, fun r hr => by
        rcases hu_all r hr with hr' | hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inr (Or.inr hr'))
        · exact Or.inr (Or.inr (Or.inl hr'))
        · exact Or.inr (Or.inl (hr'.trans h.symm))⟩
  rcases hpick with ⟨a₃, ha3, h31, h32, hya3, hu_all'⟩
  have hdu4 : G.degree u = 4 := hu.1
  rcases oneThreadNbr_other_endpoint hm (by omega) ha3 with ⟨p₃, ha3p3, hp3u, hdp3, _, _⟩
  have hua3 : G.Adj u a₃ := (mem_oneThreadNbrs.mp ha3).1
  have hda3 : G.degree a₃ = 2 := (mem_oneThreadNbrs.mp ha3).2.1
  have huy : G.Adj u y := (mem_leafNbrs.mp hy).1
  have hdy : G.degree y = 1 := (mem_leafNbrs.mp hy).2
  have hp3v : p₃ ≠ v := fun h => hno3 a₃ ha3 h31 h32 (h ▸ ha3p3)
  have ha3_all : ∀ r, G.Adj a₃ r → r = u ∨ r = p₃ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda3 hua3.symm ha3p3 hp3u.symm
    have : r ∈ ({u, p₃} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₃ r).mpr hr
    simpa using this
  have hLu5 : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLy2 : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  have hLa3 : (L a₃).card = 4 := by rw [hm.list_card a₃]; simp [kappa, hda3]
  refine ⟨{
    S_rem := {u, y, a₃}, e := a₃, p := p₃,
    huS := by simp, heS := by simp,
    ha1_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha1).1).symm, ha1y, h31.symm⟩,
    ha2_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj (mem_oneThreadNbrs.mp ha2).1).symm,
        ne_of_deg_eq_ne (mem_oneThreadNbrs.mp ha2).2.1 hdy (by omega), h32.symm⟩,
    hp_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp3u, ne_of_deg_ge_lt hdp3 hdy (by omega), (G.ne_of_adj ha3p3).symm⟩,
    hp_ne_v := hp3v, hep := ha3p3, hdp3 := hdp3,
    he_type := Or.inl ⟨hda3, ha3⟩,
    hdeg3_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · omega,
    hdeg2_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · omega
      · exact ⟨rfl, ha3, hua3⟩,
    hdeg1_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · exact ⟨u, by simp, by omega, huy.symm⟩
      · omega,
    hout := fun w hwS s hsS hws => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
      rcases hsS with rfl | rfl | rfl
      · rcases hu_all' w hws.symm with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨rfl, Or.inl rfl⟩
        · exact Or.inl ⟨rfl, Or.inr rfl⟩
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
      · rcases exists_unique_neighbor_of_deg_one hdy with ⟨z, _, huniq⟩
        have hwu : w = u := (huniq w hws.symm).trans (huniq u huy.symm).symm
        exact False.elim (hwS (by rw [hwu]; simp))
      · rcases ha3_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr ⟨rfl, rfl⟩,
    hext := fun φ φs => by
      let A : Finset ℕ := L u \ insert (φ p₃) (L y)
      refine ⟨A, Finset.sdiff_subset,
        by dsimp only [A]; have := card_sdiff_ge (L u) (insert (φ p₃) (L y))
           have := Finset.card_insert_le (φ p₃) (L y); omega,
        fun α hα c₁ c₂ _ _ _ => ?_⟩
      simp only [A, Finset.mem_sdiff, Finset.mem_insert, not_or] at hα
      rcases exists_mem_sdiff_of_lt (A := L a₃) (B := {φ p₃, φs p₃, α})
        (by have := card_triple_le (φ p₃) (φs p₃) α; omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      rcases exists_fourth_unique_color (a := c₁) (b := c₂) (c := c₃) (by omega : 2 ≤ (L y).card)
        with ⟨cy, hcyL, huniq_u⟩
      have hcyα : cy ≠ α := fun h => hα.2.2 (h ▸ hcyL)
      let ψu : V → ℕ := fun z => if z = u then α else if z = y then cy else c₃
      have hψu : ψu u = α := by simp [ψu]
      have hψy : ψu y = cy := by simp [ψu, (G.ne_of_adj huy).symm]
      have hψa3 : ψu a₃ = c₃ := by simp [ψu, (G.ne_of_adj hua3).symm, hya3.symm]
      refine ⟨ψu, hψu, ?_, ?_, by rw [hψa3]; exact hc3N.1, by rw [hψa3]; exact hc3N.2.1, ?_⟩
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · rw [hψu]; exact hα.1
        · rw [hψy]; exact hcyL
        · rw [hψa3]; exact hc3L
      · intro x hx z hz hxz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
        rcases hx with rfl | rfl | hx3 <;> rcases hz with rfl | rfl | hz3
        · exact False.elim (G.ne_of_adj hxz rfl)
        · rw [hψu, hψy]; exact Ne.symm hcyα
        · rw [hz3, hψu, hψa3]; exact Ne.symm hc3N.2.2
        · rw [hψy, hψu]; exact hcyα
        · exact False.elim (G.ne_of_adj hxz rfl)
        · exact False.elim (by
            rw [hz3] at hxz
            rcases exists_unique_neighbor_of_deg_one hdy with ⟨w, _, huniq⟩
            exact (G.ne_of_adj hua3).symm ((huniq a₃ hxz).trans (huniq u huy.symm).symm))
        · rw [hx3, hψa3, hψu]; exact hc3N.2.2
        · exact False.elim (by
            rw [hx3] at hxz
            rcases exists_unique_neighbor_of_deg_one hdy with ⟨w, _, huniq⟩
            exact (G.ne_of_adj hua3).symm ((huniq a₃ hxz.symm).trans (huniq u huy.symm).symm))
        · rw [hx3, hz3] at hxz; exact False.elim (G.ne_of_adj hxz rfl)
      · intro ψ hagree ha1c ha2c hpc x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact pcf_at_of_hasUniqueColor_four (mem_oneThreadNbrs.mp ha1).1
            (mem_oneThreadNbrs.mp ha2).1 hua3 huy hu_all'
            (by rw [ha1c, ha2c, hagree a₃ (by simp), hψa3, hagree y (by simp), hψy]; exact huniq_u)
        · exact pcf_at_deg_one hdy huy.symm
        · exact pcf_at_of_two_distinct_neighbors hda3 hua3.symm ha3p3 hp3u.symm
            (by rw [hagree u (by simp), hψu, hpc]; exact hα.2.1) }⟩

/-- 预排除引理 1：任意两个 `IsPoor1Ext` 顶点不能通过两条不同的 `1`-线串相连。 -/
private lemma no_two_oneThreads_between_Poor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a₁ a₂ : V}
    (hu : IsPoor1Ext G u) (hv : IsPoor1Ext G v) (huv : u ≠ v)
    (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u) (h12 : a₁ ≠ a₂)
    (hv1 : G.Adj a₁ v) (hv2 : G.Adj a₂ v) : False := by
  classical
  have hdu3 := deg_ge_three_of_isPoor1Ext hm hu
  have hdv3 := deg_ge_three_of_isPoor1Ext hm hv
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hua2 : G.Adj u a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm hv1 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
    simpa using this
  have ha2_all : ∀ r, G.Adj a₂ r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda2 hua2.symm hv2 huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
    simpa using this
  have hv_a1 : a₁ ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hv1.symm, hda1, u, hua1.symm, huv, hdu3⟩
  have hv_a2 : a₂ ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hv2.symm, hda2, u, hua2.symm, huv, hdu3⟩
  have hu_not_T21 : ¬ IsT21 G u := by
    intro hT
    have h1 := (isT21_structure hm hpq hT).2.2.2.2.1
    have hle : ({a₁, a₂} : Finset V).card ≤ (oneThreadNbrs G u).card :=
      Finset.card_le_card (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                              rcases hx with rfl | rfl <;> assumption)
    rw [Finset.card_pair h12, h1] at hle; omega
  have hv_not_T21 : ¬ IsT21 G v := by
    intro hT
    have h1 := (isT21_structure hm hpq hT).2.2.2.2.1
    have hle : ({a₁, a₂} : Finset V).card ≤ (oneThreadNbrs G v).card :=
      Finset.card_le_card (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                              rcases hx with rfl | rfl <;> assumption)
    rw [Finset.card_pair h12, h1] at hle; omega
  by_cases h3 : ∃ a₃ ∈ oneThreadNbrs G u, a₃ ≠ a₁ ∧ a₃ ≠ a₂ ∧ G.Adj a₃ v
  · rcases h3 with ⟨a₃, ha3, h31, h32, hv3⟩
    have hv_a3 : a₃ ∈ oneThreadNbrs G v :=
      mem_oneThreadNbrs.mpr ⟨hv3.symm, (mem_oneThreadNbrs.mp ha3).2.1, u,
        (mem_oneThreadNbrs.mp ha3).1.symm, huv, hdu3⟩
    have h3sub : ∀ {x : V}, a₁ ∈ oneThreadNbrs G x → a₂ ∈ oneThreadNbrs G x →
        a₃ ∈ oneThreadNbrs G x → 3 ≤ (oneThreadNbrs G x).card := by
      intro x h1 h2 h3'
      have hle : ({a₁, a₂, a₃} : Finset V).card ≤ (oneThreadNbrs G x).card :=
        Finset.card_le_card (by
          intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl | rfl <;> assumption)
      rw [Finset.card_insert_of_notMem (by simp [h12, h31.symm]), Finset.card_pair h32.symm] at hle
      exact hle
    have huL : IsL3 G u ∨ IsL4 G u := by
      rcases hu with h | h | h | h
      · exact Or.inl h
      · have := h.2.1; have := h3sub ha1 ha2 ha3; omega
      · exact False.elim (hu_not_T21 h)
      · exact Or.inr h
    have hvL : IsL3 G v ∨ IsL4 G v := by
      rcases hv with h | h | h | h
      · exact Or.inl h
      · have := h.2.1; have := h3sub hv_a1 hv_a2 hv_a3; omega
      · exact False.elim (hv_not_T21 h)
      · exact Or.inr h
    exact no_three_oneThreads_L3L4 hm hpq huL hvL huv ha1 ha2 ha3 h12 h31.symm h32.symm hv1 hv2 hv3
  · push Not at h3
    by_cases hshb : ∃ b ∈ badNbrs G u, G.Adj b v
    · rcases hshb with ⟨b, hbu, hbv⟩
      have hbv_mem : b ∈ badNbrs G v := mem_badNbrs.mpr ⟨hbv.symm, (mem_badNbrs.mp hbu).2⟩
      have huB : IsB3 G u := by
        rcases hu with h | h | h | h
        · rw [(isL3_structure hm h).2.2.2.2.2] at hbu; exact False.elim (Finset.notMem_empty b hbu)
        · exact h
        · exact False.elim (hu_not_T21 h)
        · rw [(isL4_structure hm hpq h).2.2.2.2.2.1] at hbu
          exact False.elim (Finset.notMem_empty b hbu)
      have hvB : IsB3 G v := by
        rcases hv with h | h | h | h
        · rw [(isL3_structure hm h).2.2.2.2.2] at hbv_mem
          exact False.elim (Finset.notMem_empty b hbv_mem)
        · exact h
        · exact False.elim (hv_not_T21 h)
        · rw [(isL4_structure hm hpq h).2.2.2.2.2.1] at hbv_mem
          exact False.elim (Finset.notMem_empty b hbv_mem)
      exact no_two_oneThreads_B3_shared_bad hm huB hvB huv ha1 ha2 h12 hv1 hv2 hbu hbv_mem
    · push Not at hshb
      have hrem_u : Nonempty (DoubleOneRem G L u v a₁ a₂) := by
        rcases hu with h | h | h | h
        · exact doubleOneRem_of_L3 hm h ha1 ha2 h12 h3
        · exact doubleOneRem_of_B3 hm hpq h ha1 ha2 h12 hshb
        · exact False.elim (hu_not_T21 h)
        · exact doubleOneRem_of_L4 hm hpq h ha1 ha2 h12 h3
      have h3v : ∀ a₃ ∈ oneThreadNbrs G v, a₃ ≠ a₁ → a₃ ≠ a₂ → ¬ G.Adj a₃ u :=
        fun a₃ ha3 h31 h32 h =>
          h3 a₃ (mem_oneThreadNbrs.mpr ⟨h.symm, (mem_oneThreadNbrs.mp ha3).2.1, v,
            (mem_oneThreadNbrs.mp ha3).1.symm, huv.symm, hdv3⟩) h31 h32
            (mem_oneThreadNbrs.mp ha3).1.symm
      have hshbv : ∀ b ∈ badNbrs G v, ¬ G.Adj b u := fun b hbv hbu =>
        hshb b (mem_badNbrs.mpr ⟨hbu.symm, (mem_badNbrs.mp hbv).2⟩) (mem_badNbrs.mp hbv).1.symm
      have hrem_v : Nonempty (DoubleOneRem G L v u a₁ a₂) := by
        rcases hv with h | h | h | h
        · exact doubleOneRem_of_L3 hm h hv_a1 hv_a2 h12 h3v
        · exact doubleOneRem_of_B3 hm hpq h hv_a1 hv_a2 h12 hshbv
        · exact False.elim (hv_not_T21 h)
        · exact doubleOneRem_of_L4 hm hpq h hv_a1 hv_a2 h12 h3v
      rcases hrem_u with ⟨Ru⟩
      rcases hrem_v with ⟨Rv⟩
      have hdisj3 : ∀ x ∈ Ru.S_rem, x ∈ Rv.S_rem → ¬ 3 ≤ G.degree x := by
        intro x hxu hxv hdx3
        rcases Ru.hdeg3_only x hxu hdx3 with rfl | ⟨hbx, hux⟩ <;>
        rcases Rv.hdeg3_only x hxv hdx3 with hx2 | ⟨hbx2, hvx⟩
        · exact huv hx2
        · exact not_isBad_of_isPoor1Ext hm hu hbx2
        · exact not_isBad_of_isPoor1Ext hm hv (hx2 ▸ hbx)
        · exact hshb x (mem_badNbrs.mpr ⟨hux, hbx⟩) hvx.symm
      have hdisj : Disjoint Ru.S_rem Rv.S_rem := by
        rw [Finset.disjoint_left]; intro x hxu hxv
        have hdx1 := degree_ge_one hm x
        by_cases hdx3 : 3 ≤ G.degree x
        · exact hdisj3 x hxu hxv hdx3
        · by_cases hdx2 : G.degree x = 2
          · rcases Ru.hdeg2_only x hxu hdx2 with ⟨_, hx1u, _⟩
            rcases Rv.hdeg2_only x hxv hdx2 with ⟨_, _, hvx⟩
            have hx1 : x ≠ a₁ := fun h => Ru.ha1_not (h ▸ hxu)
            have hx2 : x ≠ a₂ := fun h => Ru.ha2_not (h ▸ hxu)
            exact h3 x hx1u hx1 hx2 hvx.symm
          · have hdx1' : G.degree x = 1 := by omega
            rcases Ru.hdeg1_only x hxu hdx1' with ⟨w₁, hw1S, hdw1, hxw1⟩
            rcases Rv.hdeg1_only x hxv hdx1' with ⟨w₂, hw2S, _, hxw2⟩
            rcases exists_unique_neighbor_of_deg_one hdx1' with ⟨z, _, huniq⟩
            have hw12 : w₁ = w₂ := (huniq w₁ hxw1).trans (huniq w₂ hxw2).symm
            exact hdisj3 w₁ hw1S (hw12 ▸ hw2S) hdw1
      have hpu_not_Rv : Ru.p ∉ Rv.S_rem := by
        intro hpv
        rcases Rv.hdeg3_only Ru.p hpv Ru.hdp3 with h | ⟨hbp, _⟩
        · exact Ru.hp_ne_v h
        · rcases Ru.he_type with ⟨hde2, he1⟩ | ⟨hbe, _⟩
          · have he_in : Ru.e ∈ oneThreadNbrs G Ru.p :=
              mem_oneThreadNbrs.mpr ⟨Ru.hep.symm, hde2, u, (mem_oneThreadNbrs.mp he1).1.symm,
                fun h => Ru.hp_not (h ▸ Ru.huS), hdu3⟩
            rw [bad_no_one_thread hm hbp] at he_in; exact Finset.notMem_empty _ he_in
          · exact no_adjacent_bad hm hpq hbe hbp Ru.hep
      have hpv_not_Ru : Rv.p ∉ Ru.S_rem := by
        intro hpu
        rcases Ru.hdeg3_only Rv.p hpu Rv.hdp3 with h | ⟨hbp, _⟩
        · exact Rv.hp_ne_v h
        · rcases Rv.he_type with ⟨hde2, he1⟩ | ⟨hbe, _⟩
          · have he_in : Rv.e ∈ oneThreadNbrs G Rv.p :=
              mem_oneThreadNbrs.mpr ⟨Rv.hep.symm, hde2, v, (mem_oneThreadNbrs.mp he1).1.symm,
                fun h => Rv.hp_not (h ▸ Rv.huS), hdv3⟩
            rw [bad_no_one_thread hm hbp] at he_in; exact Finset.notMem_empty _ he_in
          · exact no_adjacent_bad hm hpq hbe hbp Rv.hep
      let S : Finset V := insert a₁ (insert a₂ (Ru.S_rem ∪ Rv.S_rem))
      have hpu_not_S : Ru.p ∉ S := by
        simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
        exact ⟨ne_of_deg_ge_lt Ru.hdp3 hda1 (by omega), ne_of_deg_ge_lt Ru.hdp3 hda2 (by omega),
          Ru.hp_not, hpu_not_Rv⟩
      have hpv_not_S : Rv.p ∉ S := by
        simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
        exact ⟨ne_of_deg_ge_lt Rv.hdp3 hda1 (by omega), ne_of_deg_ge_lt Rv.hdp3 hda2 (by omega),
          hpv_not_Ru, Rv.hp_not⟩
      have hS_out : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s →
          (s = Ru.e ∧ w = Ru.p) ∨ (s = Rv.e ∧ w = Rv.p) := by
        intro w hwS s hsS hws
        simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hwS
        simp only [S, Finset.mem_insert, Finset.mem_union] at hsS
        rcases hsS with rfl | rfl | hsU | hsV
        · rcases ha1_all w hws.symm with rfl | rfl
          · exact False.elim (hwS.2.2.1 Ru.huS)
          · exact False.elim (hwS.2.2.2 Rv.huS)
        · rcases ha2_all w hws.symm with rfl | rfl
          · exact False.elim (hwS.2.2.1 Ru.huS)
          · exact False.elim (hwS.2.2.2 Rv.huS)
        · rcases Ru.hout w hwS.2.2.1 s hsU hws with ⟨_, rfl | rfl⟩ | h
          · exact False.elim (hwS.1 rfl)
          · exact False.elim (hwS.2.1 rfl)
          · exact Or.inl h
        · rcases Rv.hout w hwS.2.2.2 s hsV hws with ⟨_, rfl | rfl⟩ | h
          · exact False.elim (hwS.1 rfl)
          · exact False.elim (hwS.2.1 rfl)
          · exact Or.inr h
      have hno_cross : ∀ x ∈ Ru.S_rem, ∀ y ∈ Rv.S_rem, ¬ G.Adj x y := by
        intro x hxu y hyv hxy
        have hy_not_U : y ∉ Ru.S_rem := fun h => Finset.disjoint_left.mp hdisj h hyv
        rcases Ru.hout y hy_not_U x hxu hxy.symm with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩
        · exact Rv.ha1_not hyv
        · exact Rv.ha2_not hyv
        · exact hpu_not_Rv hyv
      have hnoniso : ∀ w, w ∉ S → (∃ s ∈ S, G.Adj w s) → ∃ r, r ∉ S ∧ G.Adj w r := by
        intro w hwS ⟨s, hsS, hws⟩
        have hdw3 : 3 ≤ G.degree w := by
          rcases hS_out w hwS s hsS hws with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact Ru.hdp3
          · exact Rv.hdp3
        rcases exists_mem_sdiff_of_lt (A := G.neighborFinset w) (B := {Ru.e, Rv.e})
          (by rw [SimpleGraph.card_neighborFinset_eq_degree]
              have := Finset.card_le_two (a := Ru.e) (b := Rv.e); omega) with ⟨r, hr, hrn⟩
        rw [SimpleGraph.mem_neighborFinset] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
        refine ⟨r, fun hrS => ?_, hr⟩
        rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hrn.1 rfl
        · exact hrn.2 rfl
      rcases exists_admissible_coloring hm (S := S) ⟨a₁, by simp [S]⟩ with ⟨adm⟩
      rcases Ru.hext adm.φ adm.φs with ⟨Au, hAu_sub, hAu2, hRu_ext⟩
      rcases Rv.hext adm.φ adm.φs with ⟨Av, hAv_sub, hAv2, hRv_ext⟩
      rcases Finset.card_pos.mp (by omega : 0 < Au.card) with ⟨α, hαA⟩
      rcases exists_mem_sdiff_of_lt (A := Av) (B := {α})
        (by simp only [Finset.card_singleton]; omega) with ⟨β, hβA, hβα⟩
      rw [Finset.mem_singleton] at hβα
      have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
      have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
      rcases exists_mem_sdiff_of_lt (A := L a₁) (B := {α, β})
        (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨c₁, hc1L, hc1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
      rcases exists_mem_sdiff_of_lt (A := L a₂) (B := {α, β, c₁})
        (by have := card_triple_le α β c₁; omega) with ⟨c₂, hc2L, hc2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
      rcases hRu_ext α hαA c₁ c₂ hc1N.1 hc2N.1 (Ne.symm hc2N.2.2) with
        ⟨ψu, hψu_u, hψu_L, hψu_prop, hψu_ep, hψu_eps, hψu_pcf⟩
      rcases hRv_ext β hβA c₁ c₂ hc1N.2 hc2N.2.1 (Ne.symm hc2N.2.2) with
        ⟨ψv, hψv_v, hψv_L, hψv_prop, hψv_ep, hψv_eps, hψv_pcf⟩
      let ψ : V → ℕ := fun z =>
        if z = a₁ then c₁ else if z = a₂ then c₂
        else if z ∈ Ru.S_rem then ψu z else if z ∈ Rv.S_rem then ψv z else adm.φ z
      have hψa1 : ψ a₁ = c₁ := by simp [ψ]
      have hψa2 : ψ a₂ = c₂ := by simp [ψ, h12.symm]
      have hψU : ∀ x ∈ Ru.S_rem, ψ x = ψu x := fun x hx => by
        have h1 : x ≠ a₁ := fun h => Ru.ha1_not (h ▸ hx)
        have h2 : x ≠ a₂ := fun h => Ru.ha2_not (h ▸ hx)
        simp [ψ, h1, h2, hx]
      have hψV : ∀ x ∈ Rv.S_rem, ψ x = ψv x := fun x hx => by
        have h1 : x ≠ a₁ := fun h => Rv.ha1_not (h ▸ hx)
        have h2 : x ≠ a₂ := fun h => Rv.ha2_not (h ▸ hx)
        have h3 : x ∉ Ru.S_rem := fun h => Finset.disjoint_left.mp hdisj h hx
        simp [ψ, h1, h2, h3, hx]
      have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
        simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hz
        simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, ite_false]
      apply adm.contradiction hm ψ hψ_out
      · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_union] at hz
        rcases hz with rfl | rfl | hzU | hzV
        · rw [hψa1]; exact hc1L
        · rw [hψa2]; exact hc2L
        · rw [hψU z hzU]; exact hψu_L z hzU
        · rw [hψV z hzV]; exact hψv_L z hzV
      · intro z₁ z₂ h12' hor
        have hcase : ∀ a b, G.Adj a b → a ∈ S → ψ a ≠ ψ b := by
          intro a b hab haS
          simp only [S, Finset.mem_insert, Finset.mem_union] at haS
          rcases haS with rfl | rfl | haU | haV
          · rcases ha1_all b hab with hb | hb
            · rw [hb, hψa1, hψU u Ru.huS, hψu_u]; exact hc1N.1
            · rw [hb, hψa1, hψV v Rv.huS, hψv_v]; exact hc1N.2
          · rcases ha2_all b hab with hb | hb
            · rw [hb, hψa2, hψU u Ru.huS, hψu_u]; exact hc2N.1
            · rw [hb, hψa2, hψV v Rv.huS, hψv_v]; exact hc2N.2.1
          · by_cases hbU : b ∈ Ru.S_rem
            · rw [hψU a haU, hψU b hbU]; exact hψu_prop a haU b hbU hab
            · rcases Ru.hout b hbU a haU hab.symm with ⟨ha_eq, hb_eq | hb_eq⟩ | ⟨ha_eq, hb_eq⟩
              · rw [ha_eq, hb_eq, hψU u Ru.huS, hψu_u, hψa1]; exact Ne.symm hc1N.1
              · rw [ha_eq, hb_eq, hψU u Ru.huS, hψu_u, hψa2]; exact Ne.symm hc2N.1
              · rw [ha_eq, hb_eq, hψU Ru.e Ru.heS, hψ_out Ru.p hpu_not_S]; exact hψu_ep
          · by_cases hbV : b ∈ Rv.S_rem
            · rw [hψV a haV, hψV b hbV]; exact hψv_prop a haV b hbV hab
            · rcases Rv.hout b hbV a haV hab.symm with ⟨ha_eq, hb_eq | hb_eq⟩ | ⟨ha_eq, hb_eq⟩
              · rw [ha_eq, hb_eq, hψV v Rv.huS, hψv_v, hψa1]; exact Ne.symm hc1N.2
              · rw [ha_eq, hb_eq, hψV v Rv.huS, hψv_v, hψa2]; exact Ne.symm hc2N.2.1
              · rw [ha_eq, hb_eq, hψV Rv.e Rv.heS, hψ_out Rv.p hpv_not_S]; exact hψv_ep
        rcases hor with h1 | h2
        · exact hcase z₁ z₂ h12' h1
        · exact (hcase z₂ z₁ h12'.symm h2).symm
      · intro w hwS _ s hsS hws
        rcases hS_out w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hψU Ru.e Ru.heS]; exact hψu_eps
        · rw [hψV Rv.e Rv.heS]; exact hψv_eps
      · intro w hwS hiso ⟨s, hws⟩
        have hsS : s ∈ S := by by_contra h; exact hiso s h hws
        rcases hnoniso w hwS ⟨s, hsS, hws⟩ with ⟨r, hrS, hwr⟩
        exact False.elim (hiso r hrS hwr)
      · intro z hzS _
        simp only [S, Finset.mem_insert, Finset.mem_union] at hzS
        rcases hzS with rfl | rfl | hzU | hzV
        · exact pcf_at_of_two_distinct_neighbors hda1 hua1.symm hv1 huv
            (by rw [hψU u Ru.huS, hψu_u, hψV v Rv.huS, hψv_v]; exact Ne.symm hβα)
        · exact pcf_at_of_two_distinct_neighbors hda2 hua2.symm hv2 huv
            (by rw [hψU u Ru.huS, hψu_u, hψV v Rv.huS, hψv_v]; exact Ne.symm hβα)
        · exact hψu_pcf ψ hψU hψa1 hψa2 (hψ_out Ru.p hpu_not_S) z hzU
        · exact hψv_pcf ψ hψV hψa1 hψa2 (hψ_out Rv.p hpv_not_S) z hzV

/-- 预排除引理 2：两个相邻的 `T21` 顶点不能再通过 `1`-线串相连。 -/
private lemma no_T21_adj_T21_with_oneThread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a : V}
    (hu : IsT21 G u) (hv : IsT21 G v) (hadj : G.Adj u v)
    (ha : a ∈ oneThreadNbrs G u) (hav : G.Adj a v) : False := by
  classical
  have huv : u ≠ v := G.ne_of_adj hadj
  have hdu4 : G.degree u = 4 := (isT21_structure hm hpq hu).1
  have hdv4 : G.degree v = 4 := (isT21_structure hm hpq hv).1
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hv_a : a ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hav.symm, hda, u, hua.symm, huv, by omega⟩
  rcases isT21_unpack_one hm hpq hu ha with
    ⟨y₁, t₁, x₁, hy1, ht1, hx1, hay1, hat1, hax1, hy1t1, hy1x1, ht1x1, hu_all⟩
  rcases isT21_unpack_one hm hpq hv hv_a with
    ⟨y₂, s₁, x₂, hy2, hs1, hx2, hay2, has1, hax2, hy2s1, hy2x2, hs1x2, hv_all⟩
  have hx1_eq : x₁ = v := by
    rcases hu_all v hadj with h | h | h | h
    · exact False.elim (ne_of_deg_eq_ne hdv4 hda (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne hdv4 (mem_leafNbrs.mp hy1).2 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne hdv4 (mem_twoThreadNbrs.mp ht1).2.1 (by omega) h)
    · exact h.symm
  have hx2_eq : x₂ = u := by
    rcases hv_all u hadj.symm with h | h | h | h
    · exact False.elim (ne_of_deg_eq_ne hdu4 hda (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne hdu4 (mem_leafNbrs.mp hy2).2 (by omega) h)
    · exact False.elim (ne_of_deg_eq_ne hdu4 (mem_twoThreadNbrs.mp hs1).2.1 (by omega) h)
    · exact h.symm
  rcases twoThreadNbr_other_endpoint hm (by omega) ht1 with
    ⟨t₂, z₁, hut1, hdt1, ht12, ht2u, hdt2, ht2z1, hz1t1, huz1, hdz1, h2u, hanch_t1, hanch_t2⟩
  rcases twoThreadNbr_other_endpoint hm (by omega) hs1 with
    ⟨s₂, z₂, hvs1, hds1, hs12, hs2v, hds2, hs2z2, hz2s1, hvz2, hdz2, h2v, hanch_s1, hanch_s2⟩
  have hz1v : z₁ ≠ v := fun h => no_T21_two_thread_T21 hm hpq hu hv (h ▸ h2u)
  have hz2u : z₂ ≠ u := fun h => no_T21_two_thread_T21 hm hpq hv hu (h ▸ h2v)
  have ht_disj_s : ∀ p ∈ ({t₁, t₂} : Finset V), ∀ q ∈ ({s₁, s₂} : Finset V), p ≠ q := by
    intro p hp q hq heq; subst heq
    have h1 : threadAnchors G p = {u, z₁} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> assumption
    have h2 : threadAnchors G p = {v, z₂} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have hv_in : v ∈ ({u, z₁} : Finset V) := by rw [← h1, h2]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_in
    rcases hv_in with h | h
    · exact huv h.symm
    · exact hz1v h.symm
  have ht1s1 : t₁ ≠ s₁ := ht_disj_s t₁ (by simp) s₁ (by simp)
  have ht1s2 : t₁ ≠ s₂ := ht_disj_s t₁ (by simp) s₂ (by simp)
  have ht2s1 : t₂ ≠ s₁ := ht_disj_s t₂ (by simp) s₁ (by simp)
  have ht2s2 : t₂ ≠ s₂ := ht_disj_s t₂ (by simp) s₂ (by simp)
  have huy1 : G.Adj u y₁ := (mem_leafNbrs.mp hy1).1
  have hdy1 : G.degree y₁ = 1 := (mem_leafNbrs.mp hy1).2
  have hvy2 : G.Adj v y₂ := (mem_leafNbrs.mp hy2).1
  have hdy2 : G.degree y₂ = 1 := (mem_leafNbrs.mp hy2).2
  have hy12 : y₁ ≠ y₂ := by
    intro h; subst h; rcases exists_unique_neighbor_of_deg_one hdy1 with ⟨w, _, huniq⟩
    exact huv ((huniq u huy1.symm).trans (huniq v hvy2.symm).symm)
  have ha_ne_t2 : a ≠ t₂ := by
    intro h; subst h
    have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have hm1 : t₁ ∈ ({u, v} : Finset V) := by
      rw [← hN]; exact (G.mem_neighborFinset a t₁).mpr ht12.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1
    rcases hm1 with h1 | h1
    · exact G.ne_of_adj hut1 h1.symm
    · exact ne_of_deg_eq_ne hdt1 hdv4 (by omega) h1
  have ha_ne_s2 : a ≠ s₂ := by
    intro h; subst h
    have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have hm1 : s₁ ∈ ({u, v} : Finset V) := by
      rw [← hN]; exact (G.mem_neighborFinset a s₁).mpr hs12.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1
    rcases hm1 with h1 | h1
    · exact ne_of_deg_eq_ne hds1 hdu4 (by omega) h1
    · exact G.ne_of_adj hvs1 h1.symm
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  have ht1_all : ∀ r, G.Adj t₁ r → r = u ∨ r = t₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdt1 hut1.symm ht12 ht2u.symm
    have : r ∈ ({u, t₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₁ r).mpr hr
    simpa using this
  have ht2_all : ∀ r, G.Adj t₂ r → r = t₁ ∨ r = z₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdt2 ht12.symm ht2z1 hz1t1.symm
    have : r ∈ ({t₁, z₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₂ r).mpr hr
    simpa using this
  have hs1_all : ∀ r, G.Adj s₁ r → r = v ∨ r = s₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hds1 hvs1.symm hs12 hs2v.symm
    have : r ∈ ({v, s₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset s₁ r).mpr hr
    simpa using this
  have hs2_all : ∀ r, G.Adj s₂ r → r = s₁ ∨ r = z₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hds2 hs12.symm hs2z2 hz2s1.symm
    have : r ∈ ({s₁, z₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset s₂ r).mpr hr
    simpa using this
  let S : Finset V := {u, v, a, y₁, y₂, t₁, t₂, s₁, s₂}
  have hz1S : z₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huz1.symm, hz1v, ne_of_deg_ge_lt hdz1 hda (by omega),
      ne_of_deg_ge_lt hdz1 hdy1 (by omega), ne_of_deg_ge_lt hdz1 hdy2 (by omega),
      hz1t1, (G.ne_of_adj ht2z1).symm, ne_of_deg_ge_lt hdz1 hds1 (by omega),
      ne_of_deg_ge_lt hdz1 hds2 (by omega)⟩
  have hz2S : z₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hz2u, hvz2.symm, ne_of_deg_ge_lt hdz2 hda (by omega),
      ne_of_deg_ge_lt hdz2 hdy1 (by omega), ne_of_deg_ge_lt hdz2 hdy2 (by omega),
      ne_of_deg_ge_lt hdz2 hdt1 (by omega), ne_of_deg_ge_lt hdz2 hdt2 (by omega),
      hz2s1, (G.ne_of_adj hs2z2).symm⟩
  have hS_out : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s → (s = t₂ ∧ w = z₁) ∨ (s = s₂ ∧ w = z₂) := by
    intro w hwS s hsS hws
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsS
    rcases hsS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hu_all w hws.symm with rfl | rfl | rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by rw [hx1_eq]; simp [S]))
    · rcases hv_all w hws.symm with rfl | rfl | rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by rw [hx2_eq]; simp [S]))
    · rcases ha_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases exists_unique_neighbor_of_deg_one hdy1 with ⟨q', _, huniq⟩
      have hwu : w = u := (huniq w hws.symm).trans (huniq u huy1.symm).symm
      exact False.elim (hwS (by rw [hwu]; simp [S]))
    · rcases exists_unique_neighbor_of_deg_one hdy2 with ⟨q', _, huniq⟩
      have hwv : w = v := (huniq w hws.symm).trans (huniq v hvy2.symm).symm
      exact False.elim (hwS (by rw [hwv]; simp [S]))
    · rcases ht1_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ht2_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hs1_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases hs2_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inr ⟨rfl, rfl⟩
  have hnoniso : ∀ w, w ∉ S → (∃ s ∈ S, G.Adj w s) → ∃ r, r ∉ S ∧ G.Adj w r := by
    intro w hwS ⟨s, hsS, hws⟩
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out w hwS s hsS hws with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    rcases exists_mem_sdiff_of_lt (A := G.neighborFinset w) (B := {t₂, s₂})
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]
          have := Finset.card_le_two (a := t₂) (b := s₂); omega) with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, fun hrS => ?_, hr⟩
    rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, by simp [S]⟩ with ⟨adm⟩
  have hLu5 : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLv5 : (L v).card = 5 := by rw [hm.list_card v]; simp [kappa, hdv4]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLy1 : (L y₁).card = 2 := by rw [hm.list_card y₁]; simp [kappa, hdy1]
  have hLy2 : (L y₂).card = 2 := by rw [hm.list_card y₂]; simp [kappa, hdy2]
  have hLt1 : (L t₁).card = 4 := by rw [hm.list_card t₁]; simp [kappa, hdt1]
  have hLt2 : (L t₂).card = 4 := by rw [hm.list_card t₂]; simp [kappa, hdt2]
  have hLs1 : (L s₁).card = 4 := by rw [hm.list_card s₁]; simp [kappa, hds1]
  have hLs2 : (L s₂).card = 4 := by rw [hm.list_card s₂]; simp [kappa, hds2]
  rcases exists_mem_sdiff_of_lt (A := L u) (B := L y₁) (by omega) with ⟨α, hαL, hαy1⟩
  rcases exists_mem_sdiff_of_lt (A := L v) (B := insert α (L y₂))
    (by have := Finset.card_insert_le α (L y₂); omega) with ⟨β, hβL, hβN⟩
  rw [Finset.mem_insert, not_or] at hβN
  rcases exists_mem_sdiff_of_lt (A := L a) (B := {α, β})
    (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨ca, hcaL, hcaN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcaN
  rcases exists_mem_sdiff_of_lt (A := L t₂) (B := {adm.φ z₁, adm.φs z₁, α})
    (by have := card_triple_le (adm.φ z₁) (adm.φs z₁) α; omega) with ⟨ct2, hct2L, hct2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct2N
  rcases exists_mem_sdiff_of_lt (A := L t₁) (B := {α, ct2, adm.φ z₁})
    (by have := card_triple_le α ct2 (adm.φ z₁); omega) with ⟨ct1, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_mem_sdiff_of_lt (A := L s₂) (B := {adm.φ z₂, adm.φs z₂, β})
    (by have := card_triple_le (adm.φ z₂) (adm.φs z₂) β; omega) with ⟨cs2, hcs2L, hcs2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs2N
  rcases exists_mem_sdiff_of_lt (A := L s₁) (B := {β, cs2, adm.φ z₂})
    (by have := card_triple_le β cs2 (adm.φ z₂); omega) with ⟨cs1, hcs1L, hcs1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs1N
  rcases exists_fourth_unique_color (a := ca) (b := ct1) (c := β) (by omega : 2 ≤ (L y₁).card)
    with ⟨cy1, hcy1L, huniq_u⟩
  rcases exists_fourth_unique_color (a := ca) (b := cs1) (c := α) (by omega : 2 ≤ (L y₂).card)
    with ⟨cy2, hcy2L, huniq_v⟩
  have hcy1α : cy1 ≠ α := fun h => hαy1 (h ▸ hcy1L)
  have hcy2β : cy2 ≠ β := fun h => hβN.2 (h ▸ hcy2L)
  let ψ : V → ℕ := fun z =>
    if z = u then α else if z = v then β else if z = a then ca
    else if z = y₁ then cy1 else if z = y₂ then cy2
    else if z = t₁ then ct1 else if z = t₂ then ct2
    else if z = s₁ then cs1 else if z = s₂ then cs2 else adm.φ z
  have hψu : ψ u = α := by simp [ψ]
  have hψv : ψ v = β := by simp [ψ, huv.symm]
  have hψa : ψ a = ca := by
    simp [ψ, ne_of_deg_eq_ne hda hdu4 (by omega), ne_of_deg_eq_ne hda hdv4 (by omega)]
  have hψy1 : ψ y₁ = cy1 := by
    simp [ψ, ne_of_deg_eq_ne hdy1 hdu4 (by omega), ne_of_deg_eq_ne hdy1 hdv4 (by omega), hay1.symm]
  have hψy2 : ψ y₂ = cy2 := by
    simp [ψ, ne_of_deg_eq_ne hdy2 hdu4 (by omega), ne_of_deg_eq_ne hdy2 hdv4 (by omega),
      hay2.symm, hy12.symm]
  have hψt1 : ψ t₁ = ct1 := by
    simp [ψ, ne_of_deg_eq_ne hdt1 hdu4 (by omega), ne_of_deg_eq_ne hdt1 hdv4 (by omega),
      hat1.symm, hy1t1.symm, ne_of_deg_eq_ne hdt1 hdy2 (by omega)]
  have hψt2 : ψ t₂ = ct2 := by
    simp [ψ, ne_of_deg_eq_ne hdt2 hdu4 (by omega), ne_of_deg_eq_ne hdt2 hdv4 (by omega),
      ha_ne_t2.symm, ne_of_deg_eq_ne hdt2 hdy1 (by omega), ne_of_deg_eq_ne hdt2 hdy2 (by omega),
      (G.ne_of_adj ht12).symm]
  have hψs1 : ψ s₁ = cs1 := by
    simp [ψ, ne_of_deg_eq_ne hds1 hdu4 (by omega), ne_of_deg_eq_ne hds1 hdv4 (by omega),
      has1.symm, ne_of_deg_eq_ne hds1 hdy1 (by omega), hy2s1.symm, ht1s1.symm, ht2s1.symm]
  have hψs2 : ψ s₂ = cs2 := by
    simp [ψ, ne_of_deg_eq_ne hds2 hdu4 (by omega), ne_of_deg_eq_ne hds2 hdv4 (by omega),
      ha_ne_s2.symm, ne_of_deg_eq_ne hds2 hdy1 (by omega), ne_of_deg_eq_ne hds2 hdy2 (by omega),
      ht1s2.symm, ht2s2.symm, (G.ne_of_adj hs12).symm]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψa]; exact hcaL
    · rw [hψy1]; exact hcy1L
    · rw [hψy2]; exact hcy2L
    · rw [hψt1]; exact hct1L
    · rw [hψt2]; exact hct2L
    · rw [hψs1]; exact hcs1L
    · rw [hψs2]; exact hcs2L
  · intro z₁' z₂' h12' hor
    have hcase : ∀ p r, G.Adj p r → p ∈ S → ψ p ≠ ψ r := by
      intro p r hpr hpS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hu_all r hpr with rfl | rfl | rfl | rfl
        · rw [hψu, hψa]; exact Ne.symm hcaN.1
        · rw [hψu, hψy1]; exact Ne.symm hcy1α
        · rw [hψu, hψt1]; exact Ne.symm hct1N.1
        · rw [hx1_eq, hψu, hψv]; exact Ne.symm hβN.1
      · rcases hv_all r hpr with rfl | rfl | rfl | rfl
        · rw [hψv, hψa]; exact Ne.symm hcaN.2
        · rw [hψv, hψy2]; exact Ne.symm hcy2β
        · rw [hψv, hψs1]; exact Ne.symm hcs1N.1
        · rw [hx2_eq, hψv, hψu]; exact hβN.1
      · rcases ha_all r hpr with rfl | rfl
        · rw [hψa, hψu]; exact hcaN.1
        · rw [hψa, hψv]; exact hcaN.2
      · rcases exists_unique_neighbor_of_deg_one hdy1 with ⟨w, _, huniq⟩
        have hru : r = u := (huniq r hpr).trans (huniq u huy1.symm).symm
        rw [hru, hψy1, hψu]; exact hcy1α
      · rcases exists_unique_neighbor_of_deg_one hdy2 with ⟨w, _, huniq⟩
        have hrv : r = v := (huniq r hpr).trans (huniq v hvy2.symm).symm
        rw [hrv, hψy2, hψv]; exact hcy2β
      · rcases ht1_all r hpr with rfl | rfl
        · rw [hψt1, hψu]; exact hct1N.1
        · rw [hψt1, hψt2]; exact hct1N.2.1
      · rcases ht2_all r hpr with hr | hr
        · rw [hr, hψt2, hψt1]; exact Ne.symm hct1N.2.1
        · rw [hr, hψt2, hψ_out z₁ hz1S]; exact hct2N.1
      · rcases hs1_all r hpr with hr | hr
        · rw [hr, hψs1, hψv]; exact hcs1N.1
        · rw [hr, hψs1, hψs2]; exact hcs1N.2.1
      · rcases hs2_all r hpr with hr | hr
        · rw [hr, hψs2, hψs1]; exact Ne.symm hcs1N.2.1
        · rw [hr, hψs2, hψ_out z₂ hz2S]; exact hcs2N.1
    rcases hor with h1 | h2
    · exact hcase z₁' z₂' h12' h1
    · exact (hcase z₂' z₁' h12'.symm h2).symm
  · intro w hwS _ s hsS hws
    rcases hS_out w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψt2]; exact hct2N.2.1
    · rw [hψs2]; exact hcs2N.2.1
  · intro w hwS hiso ⟨s, hws⟩
    have hsS : s ∈ S := by by_contra h; exact hiso s h hws
    rcases hnoniso w hwS ⟨s, hsS, hws⟩ with ⟨r, hrS, hwr⟩
    exact False.elim (hiso r hrS hwr)
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_four hua huy1 hut1 (mem_goodNbrs.mp hx1).1 hu_all
        (by rw [hψa, hψy1, hψt1, hx1_eq, hψv]
            rcases huniq_u with ⟨c, hc⟩; refine ⟨c, ?_⟩
            simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega)
    · exact pcf_at_of_hasUniqueColor_four hav.symm hvy2 hvs1 (mem_goodNbrs.mp hx2).1 hv_all
        (by rw [hψa, hψy2, hψs1, hx2_eq, hψu]
            rcases huniq_v with ⟨c, hc⟩; refine ⟨c, ?_⟩
            simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega)
    · exact pcf_at_of_two_distinct_neighbors hda hua.symm hav huv
        (by rw [hψu, hψv]; exact Ne.symm hβN.1)
    · exact pcf_at_deg_one hdy1 huy1.symm
    · exact pcf_at_deg_one hdy2 hvy2.symm
    · exact pcf_at_of_two_distinct_neighbors hdt1 hut1.symm ht12 ht2u.symm
        (by rw [hψu, hψt2]; exact Ne.symm hct2N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hdt2 ht12.symm ht2z1 hz1t1.symm
        (by rw [hψt1, hψ_out z₁ hz1S]; exact hct1N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hds1 hvs1.symm hs12 hs2v.symm
        (by rw [hψv, hψs2]; exact Ne.symm hcs2N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hds2 hs12.symm hs2z2 hz2s1.symm
        (by rw [hψs1, hψ_out z₂ hz2S]; exact hcs1N.2.2)

/-- 预排除引理 3：两个共享坏邻点 `b` 的 `B3` 顶点不能通过 `1`-线串相连。 -/
private lemma no_B3_B3_shared_bad_with_oneThread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a b : V}
    (hu : IsB3 G u) (hv : IsB3 G v) (huv : u ≠ v)
    (ha : a ∈ oneThreadNbrs G u) (hav : G.Adj a v)
    (hbu : b ∈ badNbrs G u) (hbv : b ∈ badNbrs G v) : False := by
  classical
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hdu3 : G.degree u = 3 := hu.1
  have hdv3 : G.degree v = 3 := hv.1
  have hv_a : a ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hav.symm, hda, u, hua.symm, huv, by omega⟩
  rcases isB3_unpack_one hm hpq hu ha with
    ⟨a₁, b₁, h₁, ha1, hb1, haa1, hab1, ha1b1, hu_all, _, _, _, hcoreb1, hb1_all⟩
  rcases isB3_unpack_one hm hpq hv hv_a with
    ⟨a₂, b₂, _, ha2, hb2, haa2, hab2, ha2b2, hv_all, _, _, _, _, _⟩
  have hb1_eq : b₁ = b := by
    rcases Finset.card_eq_one.mp hu.2.2 with ⟨b₀, hb₀⟩
    exact (by simpa [hb₀] using hb1 : b₁ = b₀).trans (by simpa [hb₀] using hbu : b = b₀).symm
  have hb2_eq : b₂ = b := by
    rcases Finset.card_eq_one.mp hv.2.2 with ⟨b₀, hb₀⟩
    exact (by simpa [hb₀] using hb2 : b₂ = b₀).trans (by simpa [hb₀] using hbv : b = b₀).symm
  subst b₁; subst b₂
  have hub : G.Adj u b := (mem_badNbrs.mp hbu).1
  have hvb : G.Adj v b := (mem_badNbrs.mp hbv).1
  have hbad : IsBad G b := (mem_badNbrs.mp hbu).2
  have hdb4 : 4 ≤ G.degree b := hbad.1
  have hh1_eq : h₁ = v := by
    have hv_core : v ∈ coreNbrs G b := mem_coreNbrs.mpr ⟨hvb.symm, by omega⟩
    rw [hcoreb1, Finset.mem_insert, Finset.mem_singleton] at hv_core
    rcases hv_core with h | h
    · exact False.elim (huv h.symm)
    · exact h.symm
  subst h₁
  rcases oneThreadNbr_other_endpoint hm (by omega) ha1 with ⟨p₁, ha1p1, hp1u, hdp1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) ha2 with ⟨p₂, ha2p2, hp2v, hdp2, _, _⟩
  have hp1v : p₁ ≠ v := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inr (Or.inl hu)) (Or.inr (Or.inl hv)) huv
      ha ha1 haa1 hav (h ▸ ha1p1)
  have hp2u : p₂ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inr (Or.inl hv)) (Or.inr (Or.inl hu)) huv.symm
      hv_a ha2 haa2 hua.symm (h ▸ ha2p2)
  have ha12 : a₁ ≠ a₂ := fun h => hp1v (by
    rcases exists_other_neighbor_of_deg_two (mem_oneThreadNbrs.mp ha1).2.1
      (mem_oneThreadNbrs.mp ha1).1.symm with ⟨w, _, _, hall⟩
    have hv_adj : G.Adj a₁ v := h ▸ (mem_oneThreadNbrs.mp ha2).1.symm
    rcases hall p₁ ha1p1 with h1 | h1
    · exact False.elim (hp1u h1)
    · rcases hall v hv_adj with h2 | h2
      · exact False.elim (huv h2.symm)
      · exact h1.trans h2.symm)
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hva2 : G.Adj v a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  have ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = p₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm ha1p1 hp1u.symm
    have : r ∈ ({u, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
    simpa using this
  have ha2_all : ∀ r, G.Adj a₂ r → r = v ∨ r = p₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda2 hva2.symm ha2p2 hp2v.symm
    have : r ∈ ({v, p₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
    simpa using this
  have hp1b : p₁ ≠ b := fun h => by
    have : a₁ ∈ oneThreadNbrs G b := mem_oneThreadNbrs.mpr ⟨h ▸ ha1p1.symm, hda1, u, hua1.symm,
      G.ne_of_adj hub, by omega⟩
    rw [bad_no_one_thread hm hbad] at this; exact Finset.notMem_empty _ this
  have hp2b : p₂ ≠ b := fun h => by
    have : a₂ ∈ oneThreadNbrs G b := mem_oneThreadNbrs.mpr ⟨h ▸ ha2p2.symm, hda2, v, hva2.symm,
      G.ne_of_adj hvb, by omega⟩
    rw [bad_no_one_thread hm hbad] at this; exact Finset.notMem_empty _ this
  let Y := leafNbrs G b
  have hYcard : Y.card = G.degree b - 2 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  let S : Finset V := insert u (insert v (insert a (insert a₁ (insert a₂ (insert b Y)))))
  have hp1S : p₁ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hp1u, hp1v, ne_of_deg_ge_lt hdp1 hda (by omega), (G.ne_of_adj ha1p1).symm,
      ne_of_deg_ge_lt hdp1 hda2 (by omega), hp1b,
      fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩
  have hp2S : p₂ ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hp2u, hp2v, ne_of_deg_ge_lt hdp2 hda (by omega), ne_of_deg_ge_lt hdp2 hda1 (by omega),
      (G.ne_of_adj ha2p2).symm, hp2b, fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩
  have hS_out : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s → (s = a₁ ∧ w = p₁) ∨ (s = a₂ ∧ w = p₂) := by
    intro w hwS s hsS hws
    simp only [S, Finset.mem_insert] at hsS
    rcases hsS with rfl | rfl | rfl | rfl | rfl | rfl | hsY
    · rcases hu_all w hws.symm with rfl | rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases hv_all w hws.symm with rfl | rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha1_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases ha2_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inr ⟨rfl, rfl⟩
    · rcases hb1_all w hws.symm with rfl | rfl | hwY
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S]))
      · exact False.elim (hwS (by simp [S, Y, hwY]))
    · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hsY).2 with ⟨z, _, huniq⟩
      have hwb : w = b := (huniq w hws.symm).trans (huniq b (mem_leafNbrs.mp hsY).1.symm).symm
      exact False.elim (hwS (by rw [hwb]; simp [S]))
  have hnoniso : ∀ w, w ∉ S → (∃ s ∈ S, G.Adj w s) → ∃ r, r ∉ S ∧ G.Adj w r := by
    intro w hwS ⟨s, hsS, hws⟩
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out w hwS s hsS hws with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    rcases exists_mem_sdiff_of_lt (A := G.neighborFinset w) (B := {a₁, a₂})
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]
          have := Finset.card_le_two (a := a₁) (b := a₂); omega) with ⟨r, hr, hrn⟩
    rw [SimpleGraph.mem_neighborFinset] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    refine ⟨r, fun hrS => ?_, hr⟩
    rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hrn.1 rfl
    · exact hrn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨u, by simp [S]⟩ with ⟨adm⟩
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLv4 : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv3]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  rcases exists_mem_sdiff_of_lt (A := L u) (B := {adm.φ p₁})
    (by simp only [Finset.card_singleton]; omega) with ⟨α, hαL, hαp1⟩
  rw [Finset.mem_singleton] at hαp1
  rcases exists_mem_sdiff_of_lt (A := L v) (B := {adm.φ p₂, α})
    (by have := Finset.card_le_two (a := adm.φ p₂) (b := α); omega) with ⟨β, hβL, hβN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hβN
  let R : Finset ℕ := L b \ {β, α}
  have hRcard : (if β = α then Y.card + 1 else Y.card) ≤ R.card := by
    dsimp only [R]; simp only [hβN.2, ite_false]
    have := card_sdiff_ge (L b) {β, α}; have := Finset.card_le_two (a := β) (b := α); omega
  rcases bad_fixed_color_extension (by omega : 2 ≤ Y.card)
    (fun p hp => by rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2])
    (by simp [R]) hRcard with ⟨cb, hcbR, fY, hfY, γb, hγb⟩
  simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
  rcases exists_mem_sdiff_of_lt (A := L a₁) (B := {adm.φ p₁, adm.φs p₁, α})
    (by have := card_triple_le (adm.φ p₁) (adm.φs p₁) α; omega) with ⟨c₁, hc1L, hc1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
  rcases exists_mem_sdiff_of_lt (A := L a₂) (B := {adm.φ p₂, adm.φs p₂, β})
    (by have := card_triple_le (adm.φ p₂) (adm.φs p₂) β; omega) with ⟨c₂, hc2L, hc2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
  rcases exists_mem_sdiff_of_lt (A := L a) (B := {α, β, cb})
    (by have := card_triple_le α β cb; omega) with ⟨ca, hcaL, hcaN⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcaN
  let ψ : V → ℕ := fun z =>
    if z = u then α else if z = v then β else if z = a then ca
    else if z = a₁ then c₁ else if z = a₂ then c₂ else if z = b then cb
    else if z ∈ Y then fY z else adm.φ z
  have hψu : ψ u = α := by simp [ψ]
  have hψv : ψ v = β := by simp [ψ, huv.symm]
  have hψa : ψ a = ca := by
    simp [ψ, ne_of_deg_eq_ne hda hdu3 (by omega), ne_of_deg_eq_ne hda hdv3 (by omega)]
  have hψa1 : ψ a₁ = c₁ := by
    simp [ψ, ne_of_deg_eq_ne hda1 hdu3 (by omega), ne_of_deg_eq_ne hda1 hdv3 (by omega), haa1.symm]
  have hψa2 : ψ a₂ = c₂ := by
    simp [ψ, ne_of_deg_eq_ne hda2 hdu3 (by omega), ne_of_deg_eq_ne hda2 hdv3 (by omega),
      haa2.symm, ha12.symm]
  have hψb : ψ b = cb := by
    simp [ψ, ne_of_deg_ge_lt hdb4 hdu3 (by omega), ne_of_deg_ge_lt hdb4 hdv3 (by omega),
      hab1.symm, ha1b1.symm, ha2b2.symm]
  have hψY : ∀ y ∈ Y, ψ y = fY y := fun y hy => by
    have hdy := (mem_leafNbrs.mp hy).2
    simp [ψ, ne_of_deg_eq_ne hdy hdu3 (by omega), ne_of_deg_eq_ne hdy hdv3 (by omega),
      ne_of_deg_eq_ne hdy hda (by omega), ne_of_deg_eq_ne hdy hda1 (by omega),
      ne_of_deg_eq_ne hdy hda2 (by omega), (ne_of_deg_ge_lt hdb4 hdy (by omega)).symm, hy]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
    simp only [S, Finset.mem_insert, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [S, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | hzY
    · rw [hψu]; exact hαL
    · rw [hψv]; exact hβL
    · rw [hψa]; exact hcaL
    · rw [hψa1]; exact hc1L
    · rw [hψa2]; exact hc2L
    · rw [hψb]; exact hcbR.1
    · rw [hψY z hzY]; exact (hfY z hzY).1
  · intro z₁ z₂ h12' hor
    have hcase : ∀ p r, G.Adj p r → p ∈ S → ψ p ≠ ψ r := by
      intro p r hpr hpS
      simp only [S, Finset.mem_insert] at hpS
      rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | hpY
      · rcases hu_all r hpr with rfl | rfl | rfl
        · rw [hψu, hψa]; exact Ne.symm hcaN.1
        · rw [hψu, hψa1]; exact Ne.symm hc1N.2.2
        · rw [hψu, hψb]; exact Ne.symm hcbR.2.2
      · rcases hv_all r hpr with rfl | rfl | rfl
        · rw [hψv, hψa]; exact Ne.symm hcaN.2.1
        · rw [hψv, hψa2]; exact Ne.symm hc2N.2.2
        · rw [hψv, hψb]; exact Ne.symm hcbR.2.1
      · rcases ha_all r hpr with rfl | rfl
        · rw [hψa, hψu]; exact hcaN.1
        · rw [hψa, hψv]; exact hcaN.2.1
      · rcases ha1_all r hpr with hr | hr
        · rw [hr, hψa1, hψu]; exact hc1N.2.2
        · rw [hr, hψa1, hψ_out p₁ hp1S]; exact hc1N.1
      · rcases ha2_all r hpr with hr | hr
        · rw [hr, hψa2, hψv]; exact hc2N.2.2
        · rw [hr, hψa2, hψ_out p₂ hp2S]; exact hc2N.1
      · rcases hb1_all r hpr with rfl | rfl | hrY
        · rw [hψb, hψu]; exact hcbR.2.2
        · rw [hψb, hψv]; exact hcbR.2.1
        · rw [hψb, hψY r hrY]; exact (hfY r hrY).2.symm
      · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hpY).2 with ⟨w, _, huniq⟩
        have hrb : r = b := (huniq r hpr).trans (huniq b (mem_leafNbrs.mp hpY).1.symm).symm
        rw [hrb, hψY p hpY, hψb]; exact (hfY p hpY).2
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12' h1
    · exact (hcase z₂ z₁ h12'.symm h2).symm
  · intro w hwS _ s hsS hws
    rcases hS_out w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψa1]; exact hc1N.2.1
    · rw [hψa2]; exact hc2N.2.1
  · intro w hwS hiso ⟨s, hws⟩
    have hsS : s ∈ S := by by_contra h; exact hiso s h hws
    rcases hnoniso w hwS ⟨s, hsS, hws⟩ with ⟨r, hrS, hwr⟩
    exact False.elim (hiso r hrS hwr)
  · intro z hzS _
    simp only [S, Finset.mem_insert] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | hzY
    · exact pcf_at_deg_three_of_two_distinct hdu3 hua hub hab1
        (by rw [hψa, hψb]; exact hcaN.2.2)
    · exact pcf_at_deg_three_of_two_distinct hdv3 hav.symm hvb hab2
        (by rw [hψa, hψb]; exact hcaN.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda hua.symm hav huv
        (by rw [hψu, hψv]; exact Ne.symm hβN.2)
    · exact pcf_at_of_two_distinct_neighbors hda1 hua1.symm ha1p1 hp1u.symm
        (by rw [hψu, hψ_out p₁ hp1S]; exact hαp1)
    · exact pcf_at_of_two_distinct_neighbors hda2 hva2.symm ha2p2 hp2v.symm
        (by rw [hψv, hψ_out p₂ hp2S]; exact hβN.1)
    · refine pcf_at_bad_of_count_one hub.symm hvb.symm hb1_all (γ := γb) ?_
      have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
        ext p; simp only [Finset.mem_filter]; exact and_congr_right fun hp => by rw [hψY p hp]
      rw [hfeq, hψv, hψu]; exact hγb
    · exact pcf_at_deg_one (mem_leafNbrs.mp hzY).2 (mem_leafNbrs.mp hzY).1.symm

/-- 预排除引理 4：三个互异的 `L3` 顶点不能构成细分三角形（两两均由 `1`-线串相连）。 -/
private lemma no_L3_subdivided_triangle {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v₁ v₂ a₁ a₂ a' : V}
    (hu : IsL3 G u) (hv1 : IsL3 G v₁) (hv2 : IsL3 G v₂)
    (huv1 : u ≠ v₁) (huv2 : u ≠ v₂) (hv12 : v₁ ≠ v₂)
    (ha1 : a₁ ∈ oneThreadNbrs G u) (ha1v : G.Adj a₁ v₁)
    (ha2 : a₂ ∈ oneThreadNbrs G u) (ha2v : G.Adj a₂ v₂)
    (ha' : a' ∈ oneThreadNbrs G v₁) (ha'v : G.Adj a' v₂) : False := by
  classical
  have hdu3 : G.degree u = 3 := hu.1
  have hdv1 : G.degree v₁ = 3 := hv1.1
  have hdv2 : G.degree v₂ = 3 := hv2.1
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hua2 : G.Adj u a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have hv1a' : G.Adj v₁ a' := (mem_oneThreadNbrs.mp ha').1
  have hda' : G.degree a' = 2 := (mem_oneThreadNbrs.mp ha').2.1
  have ha1_all : ∀ r, G.Adj a₁ r → r = u ∨ r = v₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm ha1v huv1
    have : r ∈ ({u, v₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ r).mpr hr
    simpa using this
  have ha2_all : ∀ r, G.Adj a₂ r → r = u ∨ r = v₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda2 hua2.symm ha2v huv2
    have : r ∈ ({u, v₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ r).mpr hr
    simpa using this
  have ha'_all : ∀ r, G.Adj a' r → r = v₁ ∨ r = v₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda' hv1a'.symm ha'v hv12
    have : r ∈ ({v₁, v₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a' r).mpr hr
    simpa using this
  have ha12 : a₁ ≠ a₂ := fun h => by
    rcases ha1_all v₂ (h ▸ ha2v) with h1 | h1
    · exact huv2 h1.symm
    · exact hv12 h1.symm
  have ha1a' : a₁ ≠ a' := fun h => by
    rcases ha1_all v₂ (h ▸ ha'v) with h1 | h1
    · exact huv2 h1.symm
    · exact hv12 h1.symm
  have ha2a' : a₂ ≠ a' := fun h => by
    rcases ha2_all v₁ (h ▸ hv1a'.symm) with h1 | h1
    · exact huv1 h1.symm
    · exact hv12 h1
  have hv1_a1 : a₁ ∈ oneThreadNbrs G v₁ :=
    mem_oneThreadNbrs.mpr ⟨ha1v.symm, hda1, u, hua1.symm, huv1, by omega⟩
  have hv2_a2 : a₂ ∈ oneThreadNbrs G v₂ :=
    mem_oneThreadNbrs.mpr ⟨ha2v.symm, hda2, u, hua2.symm, huv2, by omega⟩
  have hv2_a' : a' ∈ oneThreadNbrs G v₂ :=
    mem_oneThreadNbrs.mpr ⟨ha'v.symm, hda', v₁, hv1a'.symm, hv12, by omega⟩
  -- 拆出三顶点的第 3 条 `1`-线串 `a₃ - p₀`, `b₁ - p₁`, `b₂ - p₂`
  have hthird : ∀ {x y₁ y₂ : V}, IsL3 G x → y₁ ∈ oneThreadNbrs G x → y₂ ∈ oneThreadNbrs G x →
      y₁ ≠ y₂ → ∃ z ∈ oneThreadNbrs G x, z ≠ y₁ ∧ z ≠ y₂ ∧
        ∀ r, G.Adj x r → r = y₁ ∨ r = y₂ ∨ r = z := by
    intro x y₁ y₂ hx hy1 hy2 h12'
    rcases isL3_unpack_one hm hx hy1 with ⟨z₁, z₂, hz1, hz2, h1, h2, h3, hall⟩
    rcases hall y₂ (mem_oneThreadNbrs.mp hy2).1 with h | h | h
    · exact False.elim (h12' h.symm)
    · exact ⟨z₂, hz2, h2.symm, h ▸ h3.symm, fun r hr => by
        rcases hall r hr with hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inl (hr'.trans h.symm))
        · exact Or.inr (Or.inr hr')⟩
    · exact ⟨z₁, hz1, h1.symm, h ▸ h3, fun r hr => by
        rcases hall r hr with hr' | hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr (Or.inr hr')
        · exact Or.inr (Or.inl (hr'.trans h.symm))⟩
  rcases hthird hu ha1 ha2 ha12 with ⟨a₃, ha3, ha31, ha32, hu_all⟩
  rcases hthird hv1 hv1_a1 ha' ha1a' with ⟨b₁, hb1, hb1a1, hb1a', hv1_all⟩
  rcases hthird hv2 hv2_a2 hv2_a' ha2a' with ⟨b₂, hb2, hb2a2, hb2a', hv2_all⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) ha3 with ⟨p₀, ha3p0, hp0u, hdp0, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb1 with ⟨p₁, hb1p1, hp1v1, hdp1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb2 with ⟨p₂, hb2p2, hp2v2, hdp2, _, _⟩
  have hp0v1 : p₀ ≠ v₁ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hu) (Or.inl hv1) huv1 ha1 ha3 ha31.symm
      ha1v (h ▸ ha3p0)
  have hp0v2 : p₀ ≠ v₂ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hu) (Or.inl hv2) huv2 ha2 ha3 ha32.symm
      ha2v (h ▸ ha3p0)
  have hp1u : p₁ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hv1) (Or.inl hu) huv1.symm hv1_a1 hb1
      hb1a1.symm hua1.symm (h ▸ hb1p1)
  have hp1v2 : p₁ ≠ v₂ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hv1) (Or.inl hv2) hv12 ha' hb1 hb1a'.symm
      ha'v (h ▸ hb1p1)
  have hp2u : p₂ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hv2) (Or.inl hu) huv2.symm hv2_a2 hb2
      hb2a2.symm hua2.symm (h ▸ hb2p2)
  have hp2v1 : p₂ ≠ v₁ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hv2) (Or.inl hv1) hv12.symm hv2_a' hb2
      hb2a'.symm hv1a'.symm (h ▸ hb2p2)
  have hua3 : G.Adj u a₃ := (mem_oneThreadNbrs.mp ha3).1
  have hda3 : G.degree a₃ = 2 := (mem_oneThreadNbrs.mp ha3).2.1
  have hv1b1 : G.Adj v₁ b₁ := (mem_oneThreadNbrs.mp hb1).1
  have hdb1 : G.degree b₁ = 2 := (mem_oneThreadNbrs.mp hb1).2.1
  have hv2b2 : G.Adj v₂ b₂ := (mem_oneThreadNbrs.mp hb2).1
  have hdb2 : G.degree b₂ = 2 := (mem_oneThreadNbrs.mp hb2).2.1
  have ha3_all : ∀ r, G.Adj a₃ r → r = u ∨ r = p₀ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda3 hua3.symm ha3p0 hp0u.symm
    have : r ∈ ({u, p₀} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₃ r).mpr hr
    simpa using this
  have hb1_all : ∀ r, G.Adj b₁ r → r = v₁ ∨ r = p₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb1 hv1b1.symm hb1p1 hp1v1.symm
    have : r ∈ ({v₁, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₁ r).mpr hr
    simpa using this
  have hb2_all : ∀ r, G.Adj b₂ r → r = v₂ ∨ r = p₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb2 hv2b2.symm hb2p2 hp2v2.symm
    have : r ∈ ({v₂, p₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₂ r).mpr hr
    simpa using this
  have ha3a' : a₃ ≠ a' := fun h => by
    rcases ha3_all v₁ (h ▸ hv1a'.symm) with h1 | h1
    · exact huv1 h1.symm
    · exact hp0v1 h1.symm
  have ha3b1 : a₃ ≠ b₁ := fun h => by
    rcases ha3_all v₁ (h ▸ hv1b1.symm) with h1 | h1
    · exact huv1 h1.symm
    · exact hp0v1 h1.symm
  have ha3b2 : a₃ ≠ b₂ := fun h => by
    rcases ha3_all v₂ (h ▸ hv2b2.symm) with h1 | h1
    · exact huv2 h1.symm
    · exact hp0v2 h1.symm
  have hb1a2 : b₁ ≠ a₂ := fun h => by
    rcases hb1_all u (h ▸ hua2.symm) with h1 | h1
    · exact huv1 h1
    · exact hp1u h1.symm
  have hb2a1 : b₂ ≠ a₁ := fun h => by
    rcases hb2_all u (h ▸ hua1.symm) with h1 | h1
    · exact huv2 h1
    · exact hp2u h1.symm
  have hb1b2 : b₁ ≠ b₂ := fun h => by
    rcases hb1_all v₂ (h ▸ hv2b2.symm) with h1 | h1
    · exact hv12 h1.symm
    · exact hp1v2 h1.symm
  let S : Finset V := {u, v₁, v₂, a₁, a₂, a', a₃, b₁, b₂}
  have hp0S : p₀ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp0u, hp0v1, hp0v2, ne_of_deg_ge_lt hdp0 hda1 (by omega),
      ne_of_deg_ge_lt hdp0 hda2 (by omega), ne_of_deg_ge_lt hdp0 hda' (by omega),
      (G.ne_of_adj ha3p0).symm, ne_of_deg_ge_lt hdp0 hdb1 (by omega),
      ne_of_deg_ge_lt hdp0 hdb2 (by omega)⟩
  have hp1S : p₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp1u, hp1v1, hp1v2, ne_of_deg_ge_lt hdp1 hda1 (by omega),
      ne_of_deg_ge_lt hdp1 hda2 (by omega), ne_of_deg_ge_lt hdp1 hda' (by omega),
      ne_of_deg_ge_lt hdp1 hda3 (by omega), (G.ne_of_adj hb1p1).symm,
      ne_of_deg_ge_lt hdp1 hdb2 (by omega)⟩
  have hp2S : p₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp2u, hp2v1, hp2v2, ne_of_deg_ge_lt hdp2 hda1 (by omega),
      ne_of_deg_ge_lt hdp2 hda2 (by omega), ne_of_deg_ge_lt hdp2 hda' (by omega),
      ne_of_deg_ge_lt hdp2 hda3 (by omega), ne_of_deg_ge_lt hdp2 hdb1 (by omega),
      (G.ne_of_adj hb2p2).symm⟩
  have hS_out : ∀ w, w ∉ S → ∀ s ∈ S, G.Adj w s →
      (s = a₃ ∧ w = p₀) ∨ (s = b₁ ∧ w = p₁) ∨ (s = b₂ ∧ w = p₂) := by
    intro w hwS s hsS hws
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsS
    rcases hsS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hu_all w hws.symm with rfl | rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases hv1_all w hws.symm with rfl | rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases hv2_all w hws.symm with rfl | rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha1_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha2_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha'_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [S]))
    · rcases ha3_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hb1_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hb2_all w hws.symm with rfl | rfl
      · exact False.elim (hwS (by simp [S]))
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  rcases exists_admissible_coloring hm (S := S) ⟨u, by simp [S]⟩ with ⟨adm⟩
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLv1_4 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv1]
  have hLv2_4 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv2]
  have hLa1 : (L a₁).card = 4 := by rw [hm.list_card a₁]; simp [kappa, hda1]
  have hLa2 : (L a₂).card = 4 := by rw [hm.list_card a₂]; simp [kappa, hda2]
  have hLa' : (L a').card = 4 := by rw [hm.list_card a']; simp [kappa, hda']
  have hLa3 : (L a₃).card = 4 := by rw [hm.list_card a₃]; simp [kappa, hda3]
  have hLb1 : (L b₁).card = 4 := by rw [hm.list_card b₁]; simp [kappa, hdb1]
  have hLb2 : (L b₂).card = 4 := by rw [hm.list_card b₂]; simp [kappa, hdb2]
  rcases exists_mem_sdiff_of_lt (A := L u) (B := {adm.φ p₀})
    (by simp only [Finset.card_singleton]; omega) with ⟨γ, hγL, hγp0⟩
  rw [Finset.mem_singleton] at hγp0
  rcases exists_mem_sdiff_of_lt (A := L v₁) (B := {adm.φ p₁, γ})
    (by have := Finset.card_le_two (a := adm.φ p₁) (b := γ); omega) with ⟨α₁, hα1L, hα1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα1N
  rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {adm.φ p₂, γ, α₁})
    (by have := card_triple_le (adm.φ p₂) γ α₁; omega) with ⟨α₂, hα2L, hα2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα2N
  have hbdry_pick : ∃ c₃ d₁ d₂ : ℕ,
      c₃ ∈ L a₃ ∧ c₃ ≠ γ ∧ c₃ ≠ adm.φ p₀ ∧
      d₁ ∈ L b₁ ∧ d₁ ≠ α₁ ∧ d₁ ≠ adm.φ p₁ ∧
      d₂ ∈ L b₂ ∧ d₂ ≠ α₂ ∧ d₂ ≠ adm.φ p₂ ∧
      ((∃ r, r ∉ S ∧ G.Adj p₀ r) → c₃ ≠ adm.φs p₀) ∧
      ((∃ r, r ∉ S ∧ G.Adj p₁ r) → d₁ ≠ adm.φs p₁) ∧
      ((∃ r, r ∉ S ∧ G.Adj p₂ r) → d₂ ≠ adm.φs p₂) ∧
      ((∃ w, w ∉ S ∧ (∀ r, r ∉ S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)) → c₃ ≠ d₁) := by
    by_cases hiso : ∃ w, w ∉ S ∧ (∀ r, r ∉ S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)
    · rcases hiso with ⟨w, hwS, hw_iso, ⟨s₀, hws₀⟩⟩
      have hs₀S : s₀ ∈ S := by by_contra h; exact hw_iso s₀ h hws₀
      have hdw3 : 3 ≤ G.degree w := by
        rcases hS_out w hwS s₀ hs₀S hws₀ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      have hNw_sub : G.neighborFinset w ⊆ {a₃, b₁, b₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr
        rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      have hNw_eq : G.neighborFinset w = {a₃, b₁, b₂} := Finset.eq_of_subset_of_card_le hNw_sub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree,
            Finset.card_insert_of_notMem (by simp [ha3b1, ha3b2]), Finset.card_pair hb1b2]
        exact hdw3)
      have hwp0 : p₀ = w := by
        have hadj : G.Adj w a₃ := (G.mem_neighborFinset w a₃).mp (by rw [hNw_eq]; simp)
        rcases ha3_all w hadj.symm with rfl | rfl
        · exact False.elim (hwS (by simp [S]))
        · rfl
      have hwp1 : p₁ = w := by
        have hadj : G.Adj w b₁ := (G.mem_neighborFinset w b₁).mp (by rw [hNw_eq]; simp)
        rcases hb1_all w hadj.symm with rfl | rfl
        · exact False.elim (hwS (by simp [S]))
        · rfl
      have hwp2 : p₂ = w := by
        have hadj : G.Adj w b₂ := (G.mem_neighborFinset w b₂).mp (by rw [hNw_eq]; simp)
        rcases hb2_all w hadj.symm with rfl | rfl
        · exact False.elim (hwS (by simp [S]))
        · rfl
      rcases exists_mem_sdiff_of_lt (A := L a₃) (B := {γ, adm.φ w})
        (by have := Finset.card_le_two (a := γ) (b := adm.φ w); omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {α₁, adm.φ w, c₃})
        (by have := card_triple_le α₁ (adm.φ w) c₃; omega) with ⟨d₁, hd1L, hd1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd1N
      rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {α₂, adm.φ w})
        (by have := Finset.card_le_two (a := α₂) (b := adm.φ w); omega) with ⟨d₂, hd2L, hd2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2N
      exact ⟨c₃, d₁, d₂, hc3L, hc3N.1, hwp0 ▸ hc3N.2, hd1L, hd1N.1, hwp1 ▸ hd1N.2.1,
        hd2L, hd2N.1, hwp2 ▸ hd2N.2,
        fun ⟨r, hr, hxr⟩ => False.elim (hw_iso r hr (hwp0 ▸ hxr)),
        fun ⟨r, hr, hxr⟩ => False.elim (hw_iso r hr (hwp1 ▸ hxr)),
        fun ⟨r, hr, hxr⟩ => False.elim (hw_iso r hr (hwp2 ▸ hxr)),
        fun _ => Ne.symm hd1N.2.2⟩
    · rcases exists_mem_sdiff_of_lt (A := L a₃) (B := {γ, adm.φ p₀, adm.φs p₀})
        (by have := card_triple_le γ (adm.φ p₀) (adm.φs p₀); omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {α₁, adm.φ p₁, adm.φs p₁})
        (by have := card_triple_le α₁ (adm.φ p₁) (adm.φs p₁); omega) with ⟨d₁, hd1L, hd1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd1N
      rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {α₂, adm.φ p₂, adm.φs p₂})
        (by have := card_triple_le α₂ (adm.φ p₂) (adm.φs p₂); omega) with ⟨d₂, hd2L, hd2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2N
      exact ⟨c₃, d₁, d₂, hc3L, hc3N.1, hc3N.2.1, hd1L, hd1N.1, hd1N.2.1, hd2L, hd2N.1, hd2N.2.1,
        fun _ => hc3N.2.2, fun _ => hd1N.2.2, fun _ => hd2N.2.2, fun h => False.elim (hiso h)⟩
  rcases hbdry_pick with
    ⟨c₃, d₁, d₂, hc3L, hc3γ, hc3p0, hd1L, hd1α1, hd1p1, hd2L, hd2α2, hd2p2,
      hav0, hav1, hav2, hc3d1⟩
  rcases exists_mem_sdiff_of_lt (A := L a₁) (B := {γ, α₁, c₃})
    (by have := card_triple_le γ α₁ c₃; omega) with ⟨c₁, hc1L, hc1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
  rcases exists_mem_sdiff_of_lt (A := L a') (B := {α₁, α₂, d₁})
    (by have := card_triple_le α₁ α₂ d₁; omega) with ⟨c', hc'L, hc'N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'N
  rcases exists_mem_sdiff_of_lt (A := L a₂) (B := {γ, α₂, d₂})
    (by have := card_triple_le γ α₂ d₂; omega) with ⟨c₂, hc2L, hc2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
  let ψ : V → ℕ := fun z =>
    if z = u then γ else if z = v₁ then α₁ else if z = v₂ then α₂
    else if z = a₁ then c₁ else if z = a₂ then c₂ else if z = a' then c'
    else if z = a₃ then c₃ else if z = b₁ then d₁ else if z = b₂ then d₂ else adm.φ z
  have hψu : ψ u = γ := by simp [ψ]
  have hψv1 : ψ v₁ = α₁ := by simp [ψ, huv1.symm]
  have hψv2 : ψ v₂ = α₂ := by simp [ψ, huv2.symm, hv12.symm]
  have hψa1 : ψ a₁ = c₁ := by
    simp [ψ, ne_of_deg_eq_ne hda1 hdu3 (by omega), ne_of_deg_eq_ne hda1 hdv1 (by omega),
      ne_of_deg_eq_ne hda1 hdv2 (by omega)]
  have hψa2 : ψ a₂ = c₂ := by
    simp [ψ, ne_of_deg_eq_ne hda2 hdu3 (by omega), ne_of_deg_eq_ne hda2 hdv1 (by omega),
      ne_of_deg_eq_ne hda2 hdv2 (by omega), ha12.symm]
  have hψa' : ψ a' = c' := by
    simp [ψ, ne_of_deg_eq_ne hda' hdu3 (by omega), ne_of_deg_eq_ne hda' hdv1 (by omega),
      ne_of_deg_eq_ne hda' hdv2 (by omega), ha1a'.symm, ha2a'.symm]
  have hψa3 : ψ a₃ = c₃ := by
    simp [ψ, ne_of_deg_eq_ne hda3 hdu3 (by omega), ne_of_deg_eq_ne hda3 hdv1 (by omega),
      ne_of_deg_eq_ne hda3 hdv2 (by omega), ha31, ha32, ha3a']
  have hψb1 : ψ b₁ = d₁ := by
    simp [ψ, ne_of_deg_eq_ne hdb1 hdu3 (by omega), ne_of_deg_eq_ne hdb1 hdv1 (by omega),
      ne_of_deg_eq_ne hdb1 hdv2 (by omega), hb1a1, hb1a2, hb1a', ha3b1.symm]
  have hψb2 : ψ b₂ = d₂ := by
    simp [ψ, ne_of_deg_eq_ne hdb2 hdu3 (by omega), ne_of_deg_eq_ne hdb2 hdv1 (by omega),
      ne_of_deg_eq_ne hdb2 hdv2 (by omega), hb2a1, hb2a2, hb2a', ha3b2.symm, hb1b2.symm]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hγL
    · rw [hψv1]; exact hα1L
    · rw [hψv2]; exact hα2L
    · rw [hψa1]; exact hc1L
    · rw [hψa2]; exact hc2L
    · rw [hψa']; exact hc'L
    · rw [hψa3]; exact hc3L
    · rw [hψb1]; exact hd1L
    · rw [hψb2]; exact hd2L
  · intro z₁ z₂ h12' hor
    have hcase : ∀ p r, G.Adj p r → p ∈ S → ψ p ≠ ψ r := by
      intro p r hpr hpS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hu_all r hpr with rfl | rfl | rfl
        · rw [hψu, hψa1]; exact Ne.symm hc1N.1
        · rw [hψu, hψa2]; exact Ne.symm hc2N.1
        · rw [hψu, hψa3]; exact Ne.symm hc3γ
      · rcases hv1_all r hpr with rfl | rfl | rfl
        · rw [hψv1, hψa1]; exact Ne.symm hc1N.2.1
        · rw [hψv1, hψa']; exact Ne.symm hc'N.1
        · rw [hψv1, hψb1]; exact Ne.symm hd1α1
      · rcases hv2_all r hpr with rfl | rfl | rfl
        · rw [hψv2, hψa2]; exact Ne.symm hc2N.2.1
        · rw [hψv2, hψa']; exact Ne.symm hc'N.2.1
        · rw [hψv2, hψb2]; exact Ne.symm hd2α2
      · rcases ha1_all r hpr with rfl | rfl
        · rw [hψa1, hψu]; exact hc1N.1
        · rw [hψa1, hψv1]; exact hc1N.2.1
      · rcases ha2_all r hpr with rfl | rfl
        · rw [hψa2, hψu]; exact hc2N.1
        · rw [hψa2, hψv2]; exact hc2N.2.1
      · rcases ha'_all r hpr with rfl | rfl
        · rw [hψa', hψv1]; exact hc'N.1
        · rw [hψa', hψv2]; exact hc'N.2.1
      · rcases ha3_all r hpr with hr | hr
        · rw [hr, hψa3, hψu]; exact hc3γ
        · rw [hr, hψa3, hψ_out p₀ hp0S]; exact hc3p0
      · rcases hb1_all r hpr with hr | hr
        · rw [hr, hψb1, hψv1]; exact hd1α1
        · rw [hr, hψb1, hψ_out p₁ hp1S]; exact hd1p1
      · rcases hb2_all r hpr with hr | hr
        · rw [hr, hψb2, hψv2]; exact hd2α2
        · rw [hr, hψb2, hψ_out p₂ hp2S]; exact hd2p2
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12' h1
    · exact (hcase z₂ z₁ h12'.symm h2).symm
  · intro w hwS hnon s hsS hws
    rcases hS_out w hwS s hsS hws with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψa3]; exact hav0 hnon
    · rw [hψb1]; exact hav1 hnon
    · rw [hψb2]; exact hav2 hnon
  · intro w hwS hw_iso ⟨s₀, hws₀⟩
    have hs₀S : s₀ ∈ S := by by_contra h; exact hw_iso s₀ h hws₀
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out w hwS s₀ hs₀S hws₀ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hNw_sub : G.neighborFinset w ⊆ {a₃, b₁, b₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr
      rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hNw_eq : G.neighborFinset w = {a₃, b₁, b₂} := Finset.eq_of_subset_of_card_le hNw_sub (by
      rw [SimpleGraph.card_neighborFinset_eq_degree,
          Finset.card_insert_of_notMem (by simp [ha3b1, ha3b2]), Finset.card_pair hb1b2]
      exact hdw3)
    have hdw_eq3 : G.degree w = 3 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hNw_eq,
          Finset.card_insert_of_notMem (by simp [ha3b1, ha3b2]), Finset.card_pair hb1b2]
    exact pcf_at_deg_three_of_two_distinct hdw_eq3
      ((G.mem_neighborFinset w a₃).mp (by rw [hNw_eq]; simp))
      ((G.mem_neighborFinset w b₁).mp (by rw [hNw_eq]; simp)) ha3b1
      (by rw [hψa3, hψb1]; exact hc3d1 ⟨w, hwS, hw_iso, ⟨s₀, hws₀⟩⟩)
  · intro z hzS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_deg_three_of_two_distinct hdu3 hua1 hua3 ha31.symm
        (by rw [hψa1, hψa3]; exact hc1N.2.2)
    · exact pcf_at_deg_three_of_two_distinct hdv1 hv1a' hv1b1 hb1a'.symm
        (by rw [hψa', hψb1]; exact hc'N.2.2)
    · exact pcf_at_deg_three_of_two_distinct hdv2 ha2v.symm hv2b2 hb2a2.symm
        (by rw [hψa2, hψb2]; exact hc2N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda1 hua1.symm ha1v huv1
        (by rw [hψu, hψv1]; exact Ne.symm hα1N.2)
    · exact pcf_at_of_two_distinct_neighbors hda2 hua2.symm ha2v huv2
        (by rw [hψu, hψv2]; exact Ne.symm hα2N.2.1)
    · exact pcf_at_of_two_distinct_neighbors hda' hv1a'.symm ha'v hv12
        (by rw [hψv1, hψv2]; exact Ne.symm hα2N.2.2)
    · exact pcf_at_of_two_distinct_neighbors hda3 hua3.symm ha3p0 hp0u.symm
        (by rw [hψu, hψ_out p₀ hp0S]; exact hγp0)
    · exact pcf_at_of_two_distinct_neighbors hdb1 hv1b1.symm hb1p1 hp1v1.symm
        (by rw [hψv1, hψ_out p₁ hp1S]; exact hα1N.1)
    · exact pcf_at_of_two_distinct_neighbors hdb2 hv2b2.symm hb2p2 hp2v2.symm
        (by rw [hψv2, hψ_out p₂ hp2S]; exact hα2N.1)

/-! ## 5. 统一 `1`-线串端元接口与引理 2–4 -/

/-- `1`-线串 `u - a - v` 单侧 `u ∈ {L3, B3, T21, L4}` 的统一端元结构与四大染色算子。 -/
private structure SideData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset ℕ) (u a : V) where
  S_side : Finset V
  e₁ : V
  e₂ : V
  p₁ : V
  p₂ : V
  huS : u ∈ S_side
  he1S : e₁ ∈ S_side
  he2S : e₂ ∈ S_side
  he12 : e₁ ≠ e₂
  ha_not : a ∉ S_side
  hp1_not : p₁ ∉ S_side
  hp2_not : p₂ ∉ S_side
  he1p1 : G.Adj e₁ p₁
  he2p2 : G.Adj e₂ p₂
  hdp1 : 3 ≤ G.degree p₁
  hdp2 : 3 ≤ G.degree p₂
  hdeg3_only : ∀ x ∈ S_side, 3 ≤ G.degree x → x = u ∨ (IsBad G x ∧ x ∈ badNbrs G u)
  hdeg2_only : ∀ x ∈ S_side, G.degree x = 2 →
    (x ∈ oneThreadNbrs G u ∧ x ≠ a) ∨
    (IsT21 G u ∧ ∃ t₁ t₂ z, t₁ ∈ twoThreadNbrs G u ∧ G.Adj t₁ t₂ ∧ G.degree t₂ = 2 ∧
      t₂ ≠ u ∧ G.Adj t₂ z ∧ z ≠ t₁ ∧ 4 ≤ G.degree z ∧ (x = t₁ ∨ x = t₂))
  hdeg1_only : ∀ x ∈ S_side, G.degree x = 1 → ∃ w ∈ S_side, 3 ≤ G.degree w ∧ G.Adj x w
  he_kind : ∀ e p, ((e = e₁ ∧ p = p₁) ∨ (e = e₂ ∧ p = p₂)) →
    (e ∈ oneThreadNbrs G u ∧ e ≠ a ∧ G.Adj e p) ∨
    (IsBad G e ∧ e ∈ badNbrs G u ∧ G.Adj e p) ∨
    (e = u ∧ p ∈ goodNbrs G u ∧ G.Adj u p) ∨
    (IsT21 G u ∧ ∃ t₁, t₁ ∈ twoThreadNbrs G u ∧ G.Adj t₁ e ∧ G.degree e = 2 ∧
      e ≠ u ∧ G.Adj e p ∧ p ≠ t₁ ∧ 4 ≤ G.degree p)
  hout : ∀ w, w ∉ S_side → ∀ s ∈ S_side, G.Adj w s →
    (s = u ∧ w = a) ∨ (s = e₁ ∧ w = p₁) ∨ (s = e₂ ∧ w = p₂)
  hgoodA : ∀ (φ φs : V → ℕ), ∃ G_a : ℕ → Finset ℕ,
    (∀ γ, (G_a γ).Nonempty) ∧
    (∀ C : Finset ℕ, (C.filter (fun γ => (G_a γ).card = 1)).card ≤ 2) ∧
    (∀ γ, G_a γ ⊆ L a \ {γ}) ∧
    (∀ γ ca, ca ∈ G_a γ → ∃ ψs : V → ℕ,
      ψs u ≠ γ ∧ ψs u ≠ ca ∧
      (∀ x ∈ S_side, ψs x ∈ L x) ∧
      (∀ x ∈ S_side, ∀ y ∈ S_side, G.Adj x y → ψs x ≠ ψs y) ∧
      ψs e₁ ≠ φ p₁ ∧ ψs e₁ ≠ φs p₁ ∧ ψs e₂ ≠ φ p₂ ∧ ψs e₂ ≠ φs p₂ ∧
      (∀ ψ : V → ℕ, (∀ x ∈ S_side, ψ x = ψs x) → ψ a = ca → ψ p₁ = φ p₁ → ψ p₂ = φ p₂ →
        ∀ x ∈ S_side, ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → ψ z = ψ y → z = y))
  hgreedy : ∀ (φ φs : V → ℕ), ∃ γ ca₁ ca₂ : ℕ, ∃ ψs : V → ℕ,
    ca₁ ∈ L a \ {γ} ∧ ca₂ ∈ L a \ {γ} ∧ ca₁ ≠ ca₂ ∧ ψs u = γ ∧
    (∀ x ∈ S_side, ψs x ∈ L x) ∧
    (∀ x ∈ S_side, ∀ y ∈ S_side, G.Adj x y → ψs x ≠ ψs y) ∧
    ψs e₁ ≠ φ p₁ ∧ ψs e₁ ≠ φs p₁ ∧ ψs e₂ ≠ φ p₂ ∧ ψs e₂ ≠ φs p₂ ∧
    (∀ ca, (ca = ca₁ ∨ ca = ca₂) →
      ∀ ψ : V → ℕ, (∀ x ∈ S_side, ψ x = ψs x) → ψ a = ca → ψ p₁ = φ p₁ → ψ p₂ = φ p₂ →
        ∀ x ∈ S_side, ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → ψ z = ψ y → z = y)
  hisoDouble : ∀ (w : V) (ω γ_other ca₁ ca₂ : ℕ) (B_w : List ℕ),
    p₁ = w → p₂ = w →
    ca₁ ∈ L a \ {γ_other} → ca₂ ∈ L a \ {γ_other} → ca₁ ≠ ca₂ →
    (B_w.length = 1 ∨ B_w.length = 2) → B_w.length + 2 = G.degree w →
    ∃ ca : ℕ, (ca = ca₁ ∨ ca = ca₂) ∧ ∃ ψs : V → ℕ,
      ψs u ≠ γ_other ∧ ψs u ≠ ca ∧
      (∀ x ∈ S_side, ψs x ∈ L x) ∧
      (∀ x ∈ S_side, ∀ y ∈ S_side, G.Adj x y → ψs x ≠ ψs y) ∧
      ψs e₁ ≠ ω ∧ ψs e₂ ≠ ω ∧
      HasUniqueColor (B_w ++ [ψs e₁, ψs e₂]) ∧
      (∀ ψ : V → ℕ, (∀ x ∈ S_side, ψ x = ψs x) → ψ a = ca → ψ w = ω →
        ∀ x ∈ S_side, ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → ψ z = ψ y → z = y)

/-- 强端元性质（`B3 / T21 / L4` 均满足）：在 `3` 个以上的 `u` 色中选择其一配合任意 `≥ 2` 备选的 `G_a`。 -/
private def SideData.IsStrong {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ} {u a : V}
    (S : SideData G L u a) : Prop :=
  ∀ (φ φs : V → ℕ), ∃ C_u ⊆ L u, 3 ≤ C_u.card ∧
    ∀ γ ∈ C_u, ∀ G_a : Finset ℕ, G_a ⊆ L a \ {γ} → 2 ≤ G_a.card →
      ∃ ca ∈ G_a, ∃ ψs : V → ℕ, ψs u = γ ∧
        (∀ x ∈ S.S_side, ψs x ∈ L x) ∧
        (∀ x ∈ S.S_side, ∀ y ∈ S.S_side, G.Adj x y → ψs x ≠ ψs y) ∧
        ψs S.e₁ ≠ φ S.p₁ ∧ ψs S.e₁ ≠ φs S.p₁ ∧ ψs S.e₂ ≠ φ S.p₂ ∧ ψs S.e₂ ≠ φs S.p₂ ∧
        (∀ ψ : V → ℕ, (∀ x ∈ S.S_side, ψ x = ψs x) → ψ a = ca →
          ψ S.p₁ = φ S.p₁ → ψ S.p₂ = φ S.p₂ →
          ∀ x ∈ S.S_side, ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → ψ z = ψ y → z = y)

/-- `L3` 端元的 `SideData` 构造。 -/
private lemma sideData_L3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u a : V}
    (hu : IsL3 G u) (ha : a ∈ oneThreadNbrs G u) :
    Nonempty (SideData G L u a) := by
  classical
  rcases isL3_unpack_one hm hu ha with ⟨b₁, b₂, hb1, hb2, hab1, hab2, hb12, hu_all⟩
  have hdu3 : G.degree u = 3 := hu.1
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hub1 : G.Adj u b₁ := (mem_oneThreadNbrs.mp hb1).1
  have hdb1 : G.degree b₁ = 2 := (mem_oneThreadNbrs.mp hb1).2.1
  have hub2 : G.Adj u b₂ := (mem_oneThreadNbrs.mp hb2).1
  have hdb2 : G.degree b₂ = 2 := (mem_oneThreadNbrs.mp hb2).2.1
  rcases oneThreadNbr_other_endpoint hm (by omega) hb1 with ⟨p₁, hb1p1, hp1u, hdp1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb2 with ⟨p₂, hb2p2, hp2u, hdp2, _, _⟩
  have hb1_all : ∀ r, G.Adj b₁ r → r = u ∨ r = p₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb1 hub1.symm hb1p1 hp1u.symm
    have : r ∈ ({u, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₁ r).mpr hr
    simpa using this
  have hb2_all : ∀ r, G.Adj b₂ r → r = u ∨ r = p₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb2 hub2.symm hb2p2 hp2u.symm
    have : r ∈ ({u, p₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₂ r).mpr hr
    simpa using this
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLb1 : (L b₁).card = 4 := by rw [hm.list_card b₁]; simp [kappa, hdb1]
  have hLb2 : (L b₂).card = 4 := by rw [hm.list_card b₂]; simp [kappa, hdb2]
  have hbuild : ∀ (α c₁ c₂ : ℕ), α ∈ L u → c₁ ∈ L b₁ → c₂ ∈ L b₂ → c₁ ≠ α → c₂ ≠ α →
      ∃ ψs : V → ℕ, ψs u = α ∧ ψs b₁ = c₁ ∧ ψs b₂ = c₂ ∧
        (∀ x ∈ ({u, b₁, b₂} : Finset V), ψs x ∈ L x) ∧
        (∀ x ∈ ({u, b₁, b₂} : Finset V), ∀ y ∈ ({u, b₁, b₂} : Finset V),
          G.Adj x y → ψs x ≠ ψs y) := by
    intro α c₁ c₂ hα hc1 hc2 hc1α hc2α
    let ψs : V → ℕ := fun z => if z = u then α else if z = b₁ then c₁ else c₂
    have hψu : ψs u = α := by simp [ψs]
    have hψb1 : ψs b₁ = c₁ := by simp [ψs, (G.ne_of_adj hub1).symm]
    have hψb2 : ψs b₂ = c₂ := by simp [ψs, (G.ne_of_adj hub2).symm, hb12.symm]
    refine ⟨ψs, hψu, hψb1, hψb2, ?_, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hψu]; exact hα
      · rw [hψb1]; exact hc1
      · rw [hψb2]; exact hc2
    · intro x hx y hy hxy; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
      · rw [hx, hy] at hxy; exact False.elim (G.ne_of_adj hxy rfl)
      · rw [hx, hy, hψu, hψb1]; exact Ne.symm hc1α
      · rw [hx, hy, hψu, hψb2]; exact Ne.symm hc2α
      · rw [hx, hy, hψb1, hψu]; exact hc1α
      · rw [hx, hy] at hxy; exact False.elim (G.ne_of_adj hxy rfl)
      · rw [hx, hy] at hxy
        rcases hb1_all b₂ hxy with h | h
        · exact False.elim (G.ne_of_adj hub2 h.symm)
        · exact False.elim (ne_of_deg_ge_lt hdp1 hdb2 (by omega) h.symm)
      · rw [hx, hy, hψb2, hψu]; exact hc2α
      · rw [hx, hy] at hxy
        rcases hb1_all b₂ hxy.symm with h | h
        · exact False.elim (G.ne_of_adj hub2 h.symm)
        · exact False.elim (ne_of_deg_ge_lt hdp1 hdb2 (by omega) h.symm)
      · rw [hx, hy] at hxy; exact False.elim (G.ne_of_adj hxy rfl)
  refine ⟨{
    S_side := {u, b₁, b₂}, e₁ := b₁, e₂ := b₂, p₁ := p₁, p₂ := p₂,
    huS := by simp, he1S := by simp, he2S := by simp, he12 := hb12,
    ha_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj hua).symm, hab1, hab2⟩,
    hp1_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp1u, (G.ne_of_adj hb1p1).symm, ne_of_deg_ge_lt hdp1 hdb2 (by omega)⟩,
    hp2_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp2u, ne_of_deg_ge_lt hdp2 hdb1 (by omega), (G.ne_of_adj hb2p2).symm⟩,
    he1p1 := hb1p1, he2p2 := hb2p2, hdp1 := hdp1, hdp2 := hdp2,
    hdeg3_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · omega,
    hdeg2_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · exact Or.inl ⟨hb1, hab1.symm⟩
      · exact Or.inl ⟨hb2, hab2.symm⟩,
    hdeg1_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> omega,
    he_kind := fun e p hep => by
      rcases hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hb1, hab1.symm, hb1p1⟩
      · exact Or.inl ⟨hb2, hab2.symm, hb2p2⟩,
    hout := fun w hwS s hsS hws => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
      rcases hsS with rfl | rfl | rfl
      · rcases hu_all w hws.symm with rfl | rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
      · rcases hb1_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases hb2_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩),
    hgoodA := fun φ φs => by
      let C₂ : Finset ℕ := L u \ {φ p₁, φ p₂}
      let A₂ : Finset ℕ := L b₁ \ {φ p₁, φs p₁}
      let A₃ : Finset ℕ := L b₂ \ {φ p₂, φs p₂}
      have hC2 : 2 ≤ C₂.card := by
        dsimp only [C₂]; have := card_sdiff_ge (L u) {φ p₁, φ p₂}
        have := Finset.card_le_two (a := φ p₁) (b := φ p₂); omega
      have hA2 : 2 ≤ A₂.card := by
        dsimp only [A₂]; have := card_sdiff_ge (L b₁) {φ p₁, φs p₁}
        have := Finset.card_le_two (a := φ p₁) (b := φs p₁); omega
      have hA3 : 2 ≤ A₃.card := by
        dsimp only [A₃]; have := card_sdiff_ge (L b₂) {φ p₂, φs p₂}
        have := Finset.card_le_two (a := φ p₂) (b := φs p₂); omega
      rcases pair_goodA_props hC2 hA2 hA3 hLa4 with ⟨hne, hsing⟩
      refine ⟨pairGoodA C₂ A₂ A₃ (L a), hne, hsing, fun γ => Finset.filter_subset _ _, ?_⟩
      intro γ ca hca
      simp only [pairGoodA, Finset.mem_filter] at hca
      rcases hca with ⟨_, α, hα, hαca, c₁, hc1, c₂, hc2, hnot3⟩
      simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
      simp only [A₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1
      simp only [A₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2
      rcases hbuild α c₁ c₂ hα.1.1 hc1.1.1 hc2.1.1 hc1.2 hc2.2 with
        ⟨ψs, hψu, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨ψs, by rw [hψu]; exact hα.2, by rw [hψu]; exact hαca, hψL, hψprop,
        by rw [hψb1]; exact hc1.1.2.1, by rw [hψb1]; exact hc1.1.2.2,
        by rw [hψb2]; exact hc2.1.2.1, by rw [hψb2]; exact hc2.1.2.2, ?_⟩
      intro ψ hagree ha_eq hp1_eq hp2_eq x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact pcf_at_of_hasUniqueColor_three hua hub1 hub2 hu_all
          (by rw [ha_eq, hagree b₁ (by simp), hψb1, hagree b₂ (by simp), hψb2,
                  hasUniqueColor_triple_iff]; exact hnot3)
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1_eq]; exact hα.1.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2_eq]; exact hα.1.2.2),
    hgreedy := fun φ φs => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := {φ p₁, φ p₂})
        (by have := Finset.card_le_two (a := φ p₁) (b := φ p₂); omega) with ⟨γ, hγL, hγN⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγN
      rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {φ p₁, φs p₁, γ})
        (by have := card_triple_le (φ p₁) (φs p₁) γ; omega) with ⟨c₁, hc1L, hc1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
      rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {φ p₂, φs p₂, γ})
        (by have := card_triple_le (φ p₂) (φs p₂) γ; omega) with ⟨c₂, hc2L, hc2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
      have hLa2 : 2 ≤ (L a \ {γ, c₁}).card := by
        have := card_sdiff_ge (L a) {γ, c₁}; have := Finset.card_le_two (a := γ) (b := c₁); omega
      rcases exists_two_of_card_ge_two hLa2 with ⟨ca₁, hca1, ca₂, hca2, hca12⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca1 hca2
      rcases hbuild γ c₁ c₂ hγL hc1L hc2L hc1N.2.2 hc2N.2.2 with
        ⟨ψs, hψu, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨γ, ca₁, ca₂, ψs,
        Finset.mem_sdiff.mpr ⟨hca1.1, by simp [hca1.2.1]⟩,
        Finset.mem_sdiff.mpr ⟨hca2.1, by simp [hca2.2.1]⟩, hca12, hψu, hψL, hψprop,
        by rw [hψb1]; exact hc1N.1, by rw [hψb1]; exact hc1N.2.1,
        by rw [hψb2]; exact hc2N.1, by rw [hψb2]; exact hc2N.2.1, ?_⟩
      intro ca hca ψ hagree ha_eq hp1_eq hp2_eq x hx
      have hcac1 : ca ≠ c₁ := by rcases hca with rfl | rfl <;> [exact hca1.2.2; exact hca2.2.2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact pcf_at_deg_three_of_two_distinct hdu3 hua hub1 hab1
          (by rw [ha_eq, hagree b₁ (by simp), hψb1]; exact hcac1)
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1_eq]; exact hγN.1)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2_eq]; exact hγN.2),
    hisoDouble := fun w ω γ_other ca₁ ca₂ B_w hp1w hp2w hca1 _ _ hB12 _ => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := {γ_other, ca₁, ω})
        (by have := card_triple_le γ_other ca₁ ω; omega) with ⟨α, hαL, hαN⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hαN
      have hB1 : 2 ≤ (L b₁ \ {α, ω}).card := by
        have := card_sdiff_ge (L b₁) {α, ω}; have := Finset.card_le_two (a := α) (b := ω); omega
      have hB2 : 2 ≤ (L b₂ \ {α, ω}).card := by
        have := card_sdiff_ge (L b₂) {α, ω}; have := Finset.card_le_two (a := α) (b := ω); omega
      rcases pair_double_pcf hB1 hB2 ca₁ B_w hB12 with ⟨c₁, hc1, c₂, hc2, hnot3, hBw⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1 hc2
      rcases hbuild α c₁ c₂ hαL hc1.1 hc2.1 hc1.2.1 hc2.2.1 with
        ⟨ψs, hψu, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨ca₁, Or.inl rfl, ψs, by rw [hψu]; exact hαN.1, by rw [hψu]; exact hαN.2.1,
        hψL, hψprop, by rw [hψb1]; exact hc1.2.2, by rw [hψb2]; exact hc2.2.2,
        by rw [hψb1, hψb2]; exact hBw, ?_⟩
      intro ψ hagree ha_eq hw_eq x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact pcf_at_of_hasUniqueColor_three hua hub1 hub2 hu_all
          (by rw [ha_eq, hagree b₁ (by simp), hψb1, hagree b₂ (by simp), hψb2,
                  hasUniqueColor_triple_iff]; exact hnot3)
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1w, hw_eq]; exact hαN.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2w, hw_eq]; exact hαN.2.2) }⟩

/-- `B3` 端元的强 `SideData` 构造。 -/
private lemma sideData_B3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsB3 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ S : SideData G L u a, S.IsStrong := by
  classical
  rcases isB3_unpack_one hm hpq hu ha with
    ⟨a', b, h, ha', hb, haa', hab, ha'b, hu_all, hbh, hhu, hdh3, _, hb_all⟩
  have hdu3 : G.degree u = 3 := hu.1
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hua' : G.Adj u a' := (mem_oneThreadNbrs.mp ha').1
  have hda' : G.degree a' = 2 := (mem_oneThreadNbrs.mp ha').2.1
  have hub : G.Adj u b := (mem_badNbrs.mp hb).1
  have hbad : IsBad G b := (mem_badNbrs.mp hb).2
  have hdb4 : 4 ≤ G.degree b := hbad.1
  rcases oneThreadNbr_other_endpoint hm (by omega) ha' with ⟨p₁, ha'p1, hp1u, hdp1, _, _⟩
  have hp1b : p₁ ≠ b := fun heq => by
    have : a' ∈ oneThreadNbrs G b :=
      mem_oneThreadNbrs.mpr ⟨heq ▸ ha'p1.symm, hda', u, hua'.symm, G.ne_of_adj hub, by omega⟩
    rw [bad_no_one_thread hm hbad] at this; exact Finset.notMem_empty _ this
  have ha'_all : ∀ r, G.Adj a' r → r = u ∨ r = p₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda' hua'.symm ha'p1 hp1u.symm
    have : r ∈ ({u, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a' r).mpr hr
    simpa using this
  let Y := leafNbrs G b
  have hYcard : Y.card = G.degree b - 2 := by
    dsimp only [Y]; have := coreDeg_add_leafNbrs hm b; have := hbad.2; omega
  have hL2Y : ∀ p ∈ Y, (L p).card = 2 := fun p hp => by
    rw [hm.list_card p]; simp [kappa, (mem_leafNbrs.mp hp).2]
  have hLu4 : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu3]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLa'4 : (L a').card = 4 := by rw [hm.list_card a']; simp [kappa, hda']
  have hLb : (L b).card = G.degree b + 1 := by
    rw [hm.list_card b]; simp [kappa, show G.degree b ≠ 2 by omega]
  let S_side : Finset V := insert u (insert a' (insert b Y))
  have hbuild : ∀ (α c' cb : ℕ) (fY : V → ℕ),
      α ∈ L u → c' ∈ L a' → cb ∈ L b → c' ≠ α → cb ≠ α →
      (∀ p ∈ Y, fY p ∈ L p ∧ fY p ≠ cb) →
      ∃ ψs : V → ℕ, ψs u = α ∧ ψs a' = c' ∧ ψs b = cb ∧ (∀ p ∈ Y, ψs p = fY p) ∧
        (∀ x ∈ S_side, ψs x ∈ L x) ∧
        (∀ x ∈ S_side, ∀ y ∈ S_side, G.Adj x y → ψs x ≠ ψs y) := by
    intro α c' cb fY hα hc' hcb hc'α hcbα hfY
    let ψs : V → ℕ := fun z =>
      if z = u then α else if z = a' then c' else if z = b then cb else fY z
    have hψu : ψs u = α := by simp [ψs]
    have hψa' : ψs a' = c' := by simp [ψs, (G.ne_of_adj hua').symm]
    have hψb : ψs b = cb := by simp [ψs, (G.ne_of_adj hub).symm, ha'b.symm]
    have hψY : ∀ p ∈ Y, ψs p = fY p := fun p hp => by
      have hdp := (mem_leafNbrs.mp hp).2
      simp [ψs, ne_of_deg_eq_ne hdp hdu3 (by omega), ne_of_deg_eq_ne hdp hda' (by omega),
        (ne_of_deg_ge_lt hdb4 hdp (by omega)).symm]
    refine ⟨ψs, hψu, hψa', hψb, hψY, ?_, ?_⟩
    · intro x hx; simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · rw [hψu]; exact hα
      · rw [hψa']; exact hc'
      · rw [hψb]; exact hcb
      · rw [hψY x hxY]; exact (hfY x hxY).1
    · intro x hx y hy hxy; simp only [S_side, Finset.mem_insert] at hx hy
      rcases hx with hx | hx | hx | hxY
      · rw [hx] at hxy ⊢
        rcases hu_all y hxy with hy_eq | hy_eq | hy_eq
        · exfalso; rw [hy_eq] at hy
          rcases hy with h1 | h1 | h1 | h1
          · exact G.ne_of_adj hua h1.symm
          · exact haa' h1
          · exact hab h1
          · have := (mem_leafNbrs.mp h1).2; omega
        · rw [hy_eq, hψu, hψa']; exact Ne.symm hc'α
        · rw [hy_eq, hψu, hψb]; exact Ne.symm hcbα
      · rw [hx] at hxy ⊢
        rcases ha'_all y hxy with hy_eq | hy_eq
        · rw [hy_eq, hψa', hψu]; exact hc'α
        · exfalso; rw [hy_eq] at hy
          rcases hy with h1 | h1 | h1 | h1
          · exact hp1u h1
          · exact G.ne_of_adj ha'p1 h1.symm
          · exact hp1b h1
          · have := (mem_leafNbrs.mp h1).2; omega
      · rw [hx] at hxy ⊢
        rcases hb_all y hxy with hy_eq | hy_eq | hyY
        · rw [hy_eq, hψb, hψu]; exact hcbα
        · exfalso; rw [hy_eq] at hy
          rcases hy with h1 | h1 | h1 | h1
          · exact hhu h1
          · exact ne_of_deg_ge_lt hdh3 hda' (by omega) h1
          · exact G.ne_of_adj hbh h1.symm
          · have := (mem_leafNbrs.mp h1).2; omega
        · rw [hψb, hψY y hyY]; exact (hfY y hyY).2.symm
      · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hxY).2 with ⟨z, _, huniq⟩
        have hyb : y = b := (huniq y hxy).trans (huniq b (mem_leafNbrs.mp hxY).1.symm).symm
        rw [hyb, hψY x hxY, hψb]; exact (hfY x hxY).2
  have hbad_fix : ∀ (ω ωs α : ℕ),
      ∃ cb ∈ L b \ {ω, ωs, α}, ∃ fY : V → ℕ, (∀ p ∈ Y, fY p ∈ L p ∧ fY p ≠ cb) ∧
        ∃ γb, (Y.filter (fun p => fY p = γb)).card + ([ω, α] : List ℕ).count γb = 1 := by
    intro ω ωs α
    let R : Finset ℕ := L b \ {ω, ωs, α}
    have hRcard : (if ω = α then Y.card + 1 else Y.card) ≤ R.card := by
      dsimp only [R]
      by_cases hEq : ω = α
      · simp only [hEq, ite_true]
        have hset : ({α, ωs, α} : Finset ℕ) = {α, ωs} := by ext z; simp; tauto
        rw [hset]; have := card_sdiff_ge (L b) {α, ωs}
        have := Finset.card_le_two (a := α) (b := ωs); omega
      · simp only [hEq, ite_false]
        have := card_sdiff_ge (L b) {ω, ωs, α}; have := card_triple_le ω ωs α; omega
    exact bad_fixed_color_extension (by omega : 2 ≤ Y.card) hL2Y (by simp) hRcard
  let S : SideData G L u a := {
    S_side := S_side, e₁ := a', e₂ := b, p₁ := p₁, p₂ := h,
    huS := by simp [S_side], he1S := by simp [S_side], he2S := by simp [S_side], he12 := ha'b,
    ha_not := by
      simp only [S_side, Finset.mem_insert, not_or]
      exact ⟨(G.ne_of_adj hua).symm, haa', hab,
        fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩,
    hp1_not := by
      simp only [S_side, Finset.mem_insert, not_or]
      exact ⟨hp1u, (G.ne_of_adj ha'p1).symm, hp1b,
        fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩,
    hp2_not := by
      simp only [S_side, Finset.mem_insert, not_or]
      exact ⟨hhu, ne_of_deg_ge_lt hdh3 hda' (by omega), (G.ne_of_adj hbh).symm,
        fun hmY => by have := (mem_leafNbrs.mp hmY).2; omega⟩,
    he1p1 := ha'p1, he2p2 := hbh, hdp1 := hdp1, hdp2 := hdh3,
    hdeg3_only := fun x hx hdx => by
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · exact Or.inl rfl
      · omega
      · exact Or.inr ⟨hbad, hb⟩
      · have := (mem_leafNbrs.mp hxY).2; omega,
    hdeg2_only := fun x hx hdx => by
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · omega
      · exact Or.inl ⟨ha', haa'.symm⟩
      · omega
      · have := (mem_leafNbrs.mp hxY).2; omega,
    hdeg1_only := fun x hx hdx => by
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · omega
      · omega
      · omega
      · exact ⟨b, by simp [S_side], by omega, (mem_leafNbrs.mp hxY).1.symm⟩,
    he_kind := fun e p hep => by
      rcases hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨ha', haa'.symm, ha'p1⟩
      · exact Or.inr (Or.inl ⟨hbad, hb, hbh⟩),
    hout := fun w hwS s hsS hws => by
      simp only [S_side, Finset.mem_insert] at hsS
      rcases hsS with rfl | rfl | rfl | hsY
      · rcases hu_all w hws.symm with rfl | rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hwS (by simp [S_side]))
        · exact False.elim (hwS (by simp [S_side]))
      · rcases ha'_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp [S_side]))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases hb_all w hws.symm with rfl | rfl | hwY
        · exact False.elim (hwS (by simp [S_side]))
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact False.elim (hwS (by simp [S_side, Y, hwY]))
      · rcases exists_unique_neighbor_of_deg_one (mem_leafNbrs.mp hsY).2 with ⟨z, _, huniq⟩
        have hwb : w = b := (huniq w hws.symm).trans (huniq b (mem_leafNbrs.mp hsY).1.symm).symm
        exact False.elim (hwS (by rw [hwb]; simp [S_side])),
    hgoodA := fun φ φs => by
      let C_b : Finset ℕ := L b \ {φ h, φs h}
      have hCb : Y.card + 1 ≤ C_b.card := by
        dsimp only [C_b]; have := card_sdiff_ge (L b) {φ h, φs h}
        have := Finset.card_le_two (a := φ h) (b := φs h); omega
      rcases bad_two_color_extension (δ := φ h) (by omega : 2 ≤ Y.card) hL2Y hCb
          (by simp [C_b]) with
        ⟨γ₁, γ₂, lam, hγ1C, hγ2C, hγ12, ⟨f₁, hf1, hlam1⟩, ⟨f₂, hf2, hlam2⟩⟩
      simp only [C_b, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hγ1C
      simp only [C_b, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hγ2C
      let C₂ : Finset ℕ := L u \ {φ p₁, lam}
      let A₂ : Finset ℕ := L a' \ {φ p₁, φs p₁}
      let A₃ : Finset ℕ := {γ₁, γ₂}
      have hC2 : 2 ≤ C₂.card := by
        dsimp only [C₂]; have := card_sdiff_ge (L u) {φ p₁, lam}
        have := Finset.card_le_two (a := φ p₁) (b := lam); omega
      have hA2 : 2 ≤ A₂.card := by
        dsimp only [A₂]; have := card_sdiff_ge (L a') {φ p₁, φs p₁}
        have := Finset.card_le_two (a := φ p₁) (b := φs p₁); omega
      have hA3 : 2 ≤ A₃.card := by dsimp only [A₃]; rw [Finset.card_pair hγ12]
      rcases pair_goodA_props hC2 hA2 hA3 hLa4 with ⟨hne, hsing⟩
      refine ⟨pairGoodA C₂ A₂ A₃ (L a), hne, hsing, fun γ => Finset.filter_subset _ _, ?_⟩
      intro γ ca hca
      simp only [pairGoodA, Finset.mem_filter] at hca
      rcases hca with ⟨_, α, hα, hαca, c', hc', cb, hcb, hnot3⟩
      simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
      simp only [A₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
      simp only [A₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hcb
      have hcb_ext : cb ∈ L b ∧ cb ≠ φ h ∧ cb ≠ φs h ∧
          ∃ fY : V → ℕ, (∀ p ∈ Y, fY p ∈ L p ∧ fY p ≠ cb) ∧
            (Y.filter (fun p => fY p = lam)).card + (if φ h = lam then 1 else 0) = 1 := by
        rcases hcb.1 with rfl | rfl
        · exact ⟨hγ1C.1, hγ1C.2.1, hγ1C.2.2, f₁, hf1, hlam1⟩
        · exact ⟨hγ2C.1, hγ2C.2.1, hγ2C.2.2, f₂, hf2, hlam2⟩
      rcases hcb_ext with ⟨hcbL, hcbh, hcbhs, fY, hfY, hlam_cnt⟩
      rcases hbuild α c' cb fY hα.1.1 hc'.1.1 hcbL hc'.2 hcb.2 hfY with
        ⟨ψs, hψu, hψa', hψb, hψY, hψL, hψprop⟩
      refine ⟨ψs, by rw [hψu]; exact hα.2, by rw [hψu]; exact hαca, hψL, hψprop,
        by rw [hψa']; exact hc'.1.2.1, by rw [hψa']; exact hc'.1.2.2,
        by rw [hψb]; exact hcbh, by rw [hψb]; exact hcbhs, ?_⟩
      intro ψ hagree ha_eq hp1_eq hph_eq x hx
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · exact pcf_at_of_hasUniqueColor_three hua hua' hub hu_all
          (by rw [ha_eq, hagree a' (by simp [S_side]), hψa', hagree b (by simp [S_side]), hψb,
                  hasUniqueColor_triple_iff]; exact hnot3)
      · exact pcf_at_of_two_distinct_neighbors hda' hua'.symm ha'p1 hp1u.symm
          (by rw [hagree u (by simp [S_side]), hψu, hp1_eq]; exact hα.1.2.1)
      · refine pcf_at_bad_of_count_one hub.symm hbh hb_all (γ := lam) ?_
        have hfeq : Y.filter (fun p => ψ p = lam) = Y.filter (fun p => fY p = lam) := by
          ext p; simp only [Finset.mem_filter]
          exact and_congr_right fun hp => by rw [hagree p (by simp [S_side, hp]), hψY p hp]
        rw [hfeq, hph_eq, hagree u (by simp [S_side]), hψu]
        simp only [List.count_cons, List.count_nil, beq_iff_eq, hα.1.2.2, ite_false]
        omega
      · exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm,
    hgreedy := fun φ φs => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := {φ p₁})
        (by simp only [Finset.card_singleton]; omega) with ⟨γ, hγL, hγp1⟩
      rw [Finset.mem_singleton] at hγp1
      rcases exists_mem_sdiff_of_lt (A := L a') (B := {φ p₁, φs p₁, γ})
        (by have := card_triple_le (φ p₁) (φs p₁) γ; omega) with ⟨c', hc'L, hc'N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'N
      rcases hbad_fix (φ h) (φs h) γ with ⟨cb, hcbR, fY, hfY, γb, hγb⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
      have hLa2 : 2 ≤ (L a \ {γ, c'}).card := by
        have := card_sdiff_ge (L a) {γ, c'}; have := Finset.card_le_two (a := γ) (b := c'); omega
      rcases exists_two_of_card_ge_two hLa2 with ⟨ca₁, hca1, ca₂, hca2, hca12⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hca1 hca2
      rcases hbuild γ c' cb fY hγL hc'L hcbR.1 hc'N.2.2 hcbR.2.2.2 hfY with
        ⟨ψs, hψu, hψa', hψb, hψY, hψL, hψprop⟩
      refine ⟨γ, ca₁, ca₂, ψs,
        Finset.mem_sdiff.mpr ⟨hca1.1, by simp [hca1.2.1]⟩,
        Finset.mem_sdiff.mpr ⟨hca2.1, by simp [hca2.2.1]⟩, hca12, hψu, hψL, hψprop,
        by rw [hψa']; exact hc'N.1, by rw [hψa']; exact hc'N.2.1,
        by rw [hψb]; exact hcbR.2.1, by rw [hψb]; exact hcbR.2.2.1, ?_⟩
      intro ca hca ψ hagree ha_eq hp1_eq hph_eq x hx
      have hcac' : ca ≠ c' := by rcases hca with rfl | rfl <;> [exact hca1.2.2; exact hca2.2.2]
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · exact pcf_at_deg_three_of_two_distinct hdu3 hua hua' haa'
          (by rw [ha_eq, hagree a' (by simp [S_side]), hψa']; exact hcac')
      · exact pcf_at_of_two_distinct_neighbors hda' hua'.symm ha'p1 hp1u.symm
          (by rw [hagree u (by simp [S_side]), hψu, hp1_eq]; exact hγp1)
      · refine pcf_at_bad_of_count_one hub.symm hbh hb_all (γ := γb) ?_
        have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
          ext p; simp only [Finset.mem_filter]
          exact and_congr_right fun hp => by rw [hagree p (by simp [S_side, hp]), hψY p hp]
        rw [hfeq, hph_eq, hagree u (by simp [S_side]), hψu]; exact hγb
      · exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm,
    hisoDouble := fun w ω γ_other ca₁ ca₂ B_w hp1w hp2w hca1 _ _ hB12 _ => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := {γ_other, ca₁, ω})
        (by have := card_triple_le γ_other ca₁ ω; omega) with ⟨α, hαL, hαN⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hαN
      have hA'2 : 2 ≤ (L a' \ {α, ω}).card := by
        have := card_sdiff_ge (L a') {α, ω}; have := Finset.card_le_two (a := α) (b := ω); omega
      have hpick_cb : ∀ (forb : ℕ), ∃ cb ∈ L b \ {ω, α, forb}, ∃ fY : V → ℕ,
          (∀ p ∈ Y, fY p ∈ L p ∧ fY p ≠ cb) ∧
          ∃ γb, (Y.filter (fun p => fY p = γb)).card + ([ω, α] : List ℕ).count γb = 1 := by
        intro forb
        have hR : (if ω = α then Y.card + 1 else Y.card) ≤ (L b \ {ω, α, forb}).card := by
          simp only [Ne.symm hαN.2.2, ite_false]
          have := card_sdiff_ge (L b) {ω, α, forb}; have := card_triple_le ω α forb; omega
        exact bad_fixed_color_extension (by omega : 2 ≤ Y.card) hL2Y (by simp) hR
      have hpair : ∃ c' ∈ L a' \ {α, ω}, ∃ cb ∈ L b \ {ω, α}, ∃ fY : V → ℕ,
          (∀ p ∈ Y, fY p ∈ L p ∧ fY p ≠ cb) ∧
          (∃ γb, (Y.filter (fun p => fY p = γb)).card + ([ω, α] : List ℕ).count γb = 1) ∧
          ¬ (ca₁ = c' ∧ c' = cb) ∧ HasUniqueColor (B_w ++ [c', cb]) := by
        rcases hB12 with h1 | h2
        · rcases List.length_eq_one_iff.mp h1 with ⟨x, rfl⟩
          rcases hpick_cb 0 with ⟨cb, hcb, fY, hfY, γb, hγb⟩
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb
          rcases exists_mem_sdiff_of_lt (A := L a' \ {α, ω}) (B := {cb})
            (by simp only [Finset.card_singleton]; omega) with ⟨c', hc', hc'cb⟩
          rw [Finset.mem_singleton] at hc'cb
          refine ⟨c', hc', cb, Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
            fY, hfY, ⟨γb, hγb⟩, fun h => hc'cb h.2, ?_⟩
          simp only [List.cons_append, List.nil_append, hasUniqueColor_triple_iff]
          exact fun h => hc'cb h.2
        · rcases List.length_eq_two.mp h2 with ⟨x, y', rfl⟩
          by_cases hxy : x = y'
          · subst hxy
            rcases hpick_cb 0 with ⟨cb, hcb, fY, hfY, γb, hγb⟩
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb
            rcases exists_mem_sdiff_of_lt (A := L a' \ {α, ω}) (B := {cb})
              (by simp only [Finset.card_singleton]; omega) with ⟨c', hc', hc'cb⟩
            rw [Finset.mem_singleton] at hc'cb
            refine ⟨c', hc', cb, Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
              fY, hfY, ⟨γb, hγb⟩, fun h => hc'cb h.2, ?_⟩
            simp only [List.cons_append, List.nil_append]
            by_contra hno; rw [not_hasUniqueColor_quad_iff] at hno
            rcases hno with ⟨_, hEq⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact hc'cb hEq
            · exact hc'cb (h1.symm.trans h2)
            · exact hc'cb (h2.symm.trans h1)
          · by_cases hsub : L a' \ {α, ω} ⊆ {x, y'}
            · have hAeq : L a' \ {α, ω} = {x, y'} :=
                Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hxy]; exact hA'2)
              rcases hpick_cb ca₁ with ⟨cb, hcb, fY, hfY, γb, hγb⟩
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb
              by_cases hcbx : cb = x
              · refine ⟨x, by rw [hAeq]; simp, cb,
                  Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
                  fY, hfY, ⟨γb, hγb⟩, fun h => hcb.2.2.2 (h.1.trans h.2).symm, ?_⟩
                simp only [List.cons_append, List.nil_append]
                refine ⟨y', ?_⟩; simp [hxy, hcbx]
              · by_cases hcby : cb = y'
                · refine ⟨y', by rw [hAeq]; simp, cb,
                    Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
                    fY, hfY, ⟨γb, hγb⟩, fun h => hcb.2.2.2 (h.1.trans h.2).symm, ?_⟩
                  simp only [List.cons_append, List.nil_append]
                  refine ⟨x, ?_⟩; simp [Ne.symm hxy, hcby]
                · refine ⟨x, by rw [hAeq]; simp, cb,
                    Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
                    fY, hfY, ⟨γb, hγb⟩, fun h => hcbx h.2.symm, ?_⟩
                  simp only [List.cons_append, List.nil_append]
                  refine ⟨cb, ?_⟩; simp [Ne.symm hcbx, Ne.symm hcby]
            · have hex : ∃ c' ∈ L a' \ {α, ω}, c' ∉ ({x, y'} : Finset ℕ) := by
                by_contra hno; push Not at hno; exact hsub hno
              rcases hex with ⟨c', hc', hc'out⟩
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'out
              rcases hpick_cb c' with ⟨cb, hcb, fY, hfY, γb, hγb⟩
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb
              refine ⟨c', hc', cb, Finset.mem_sdiff.mpr ⟨hcb.1, by simp [hcb.2.1, hcb.2.2.1]⟩,
                fY, hfY, ⟨γb, hγb⟩, fun h => hcb.2.2.2 h.2.symm, ?_⟩
              simp only [List.cons_append, List.nil_append]
              refine ⟨c', ?_⟩; simp [Ne.symm hc'out.1, Ne.symm hc'out.2, hcb.2.2.2]
      rcases hpair with ⟨c', hc', cb, hcb, fY, hfY, ⟨γb, hγb⟩, hnot3, hBw⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc' hcb
      rcases hbuild α c' cb fY hαL hc'.1 hcb.1 hc'.2.1 hcb.2.2 hfY with
        ⟨ψs, hψu, hψa', hψb, hψY, hψL, hψprop⟩
      refine ⟨ca₁, Or.inl rfl, ψs, by rw [hψu]; exact hαN.1, by rw [hψu]; exact hαN.2.1,
        hψL, hψprop, by rw [hψa']; exact hc'.2.2, by rw [hψb]; exact hcb.2.1,
        by rw [hψa', hψb]; exact hBw, ?_⟩
      intro ψ hagree ha_eq hw_eq x hx
      simp only [S_side, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hxY
      · exact pcf_at_of_hasUniqueColor_three hua hua' hub hu_all
          (by rw [ha_eq, hagree a' (by simp [S_side]), hψa', hagree b (by simp [S_side]), hψb,
                  hasUniqueColor_triple_iff]; exact hnot3)
      · exact pcf_at_of_two_distinct_neighbors hda' hua'.symm ha'p1 hp1u.symm
          (by rw [hagree u (by simp [S_side]), hψu, hp1w, hw_eq]; exact hαN.2.2)
      · refine pcf_at_bad_of_count_one hub.symm hbh hb_all (γ := γb) ?_
        have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
          ext p; simp only [Finset.mem_filter]
          exact and_congr_right fun hp => by rw [hagree p (by simp [S_side, hp]), hψY p hp]
        rw [hfeq, hp2w, hw_eq, hagree u (by simp [S_side]), hψu]; exact hγb
      · exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm }
  refine ⟨S, fun φ φs => ?_⟩
  refine ⟨L u \ {φ p₁}, Finset.sdiff_subset,
    by have := card_sdiff_ge (L u) {φ p₁}; simp only [Finset.card_singleton] at this; omega,
    fun γ hγ G_a hGa_sub hGa2 => ?_⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hγ
  rcases exists_mem_sdiff_of_lt (A := L a') (B := {φ p₁, φs p₁, γ})
    (by have := card_triple_le (φ p₁) (φs p₁) γ; omega) with ⟨c', hc'L, hc'N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'N
  rcases hbad_fix (φ h) (φs h) γ with ⟨cb, hcbR, fY, hfY, γb, hγb⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcbR
  rcases exists_mem_sdiff_of_lt (A := G_a) (B := {c'})
    (by simp only [Finset.card_singleton]; omega) with ⟨ca, hcaG, hcac'⟩
  rw [Finset.mem_singleton] at hcac'
  rcases hbuild γ c' cb fY hγ.1 hc'L hcbR.1 hc'N.2.2 hcbR.2.2.2 hfY with
    ⟨ψs, hψu, hψa', hψb, hψY, hψL, hψprop⟩
  refine ⟨ca, hcaG, ψs, hψu, hψL, hψprop,
    by rw [hψa']; exact hc'N.1, by rw [hψa']; exact hc'N.2.1,
    by rw [hψb]; exact hcbR.2.1, by rw [hψb]; exact hcbR.2.2.1, ?_⟩
  intro ψ hagree ha_eq hp1_eq hph_eq x hx
  simp only [S, S_side, Finset.mem_insert] at hx
  rcases hx with rfl | rfl | rfl | hxY
  · exact pcf_at_deg_three_of_two_distinct hdu3 hua hua' haa'
      (by rw [ha_eq, hagree a' (by simp [S, S_side]), hψa']; exact hcac')
  · exact pcf_at_of_two_distinct_neighbors hda' hua'.symm ha'p1 hp1u.symm
      (by rw [hagree u (by simp [S, S_side]), hψu, hp1_eq]; exact hγ.2)
  · refine pcf_at_bad_of_count_one hub.symm hbh hb_all (γ := γb) ?_
    have hfeq : Y.filter (fun p => ψ p = γb) = Y.filter (fun p => fY p = γb) := by
      ext p; simp only [Finset.mem_filter]
      exact and_congr_right fun hp => by rw [hagree p (by simp [S, S_side, hp]), hψY p hp]
    rw [hfeq, hph_eq, hagree u (by simp [S, S_side]), hψu]; exact hγb
  · exact pcf_at_deg_one (mem_leafNbrs.mp hxY).2 (mem_leafNbrs.mp hxY).1.symm

/-- `L4` 端元的强 `SideData` 构造。 -/
private lemma sideData_L4 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsL4 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ S : SideData G L u a, S.IsStrong := by
  classical
  rcases isL4_unpack_one hm hpq hu ha with
    ⟨y, b₁, b₂, hy, hb1, hb2, hay, hab1, hab2, hyb1, hyb2, hb12, hu_all⟩
  have hdu4 : G.degree u = 4 := hu.1
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have huy : G.Adj u y := (mem_leafNbrs.mp hy).1
  have hdy : G.degree y = 1 := (mem_leafNbrs.mp hy).2
  have hub1 : G.Adj u b₁ := (mem_oneThreadNbrs.mp hb1).1
  have hdb1 : G.degree b₁ = 2 := (mem_oneThreadNbrs.mp hb1).2.1
  have hub2 : G.Adj u b₂ := (mem_oneThreadNbrs.mp hb2).1
  have hdb2 : G.degree b₂ = 2 := (mem_oneThreadNbrs.mp hb2).2.1
  rcases oneThreadNbr_other_endpoint hm (by omega) hb1 with ⟨p₁, hb1p1, hp1u, hdp1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb2 with ⟨p₂, hb2p2, hp2u, hdp2, _, _⟩
  have hb1_all : ∀ r, G.Adj b₁ r → r = u ∨ r = p₁ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb1 hub1.symm hb1p1 hp1u.symm
    have : r ∈ ({u, p₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₁ r).mpr hr
    simpa using this
  have hb2_all : ∀ r, G.Adj b₂ r → r = u ∨ r = p₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdb2 hub2.symm hb2p2 hp2u.symm
    have : r ∈ ({u, p₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₂ r).mpr hr
    simpa using this
  have hLu5 : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLy2 : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLb1 : (L b₁).card = 4 := by rw [hm.list_card b₁]; simp [kappa, hdb1]
  have hLb2 : (L b₂).card = 4 := by rw [hm.list_card b₂]; simp [kappa, hdb2]
  have hbuild : ∀ (α cy c₁ c₂ : ℕ), α ∈ L u → cy ∈ L y → c₁ ∈ L b₁ → c₂ ∈ L b₂ →
      cy ≠ α → c₁ ≠ α → c₂ ≠ α →
      ∃ ψs : V → ℕ, ψs u = α ∧ ψs y = cy ∧ ψs b₁ = c₁ ∧ ψs b₂ = c₂ ∧
        (∀ x ∈ ({u, y, b₁, b₂} : Finset V), ψs x ∈ L x) ∧
        (∀ x ∈ ({u, y, b₁, b₂} : Finset V), ∀ z ∈ ({u, y, b₁, b₂} : Finset V),
          G.Adj x z → ψs x ≠ ψs z) := by
    intro α cy c₁ c₂ hα hcy hc1 hc2 hcyα hc1α hc2α
    let ψs : V → ℕ := fun z => if z = u then α else if z = y then cy else if z = b₁ then c₁ else c₂
    have hψu : ψs u = α := by simp [ψs]
    have hψy : ψs y = cy := by simp [ψs, (G.ne_of_adj huy).symm]
    have hψb1 : ψs b₁ = c₁ := by simp [ψs, (G.ne_of_adj hub1).symm, hyb1.symm]
    have hψb2 : ψs b₂ = c₂ := by simp [ψs, (G.ne_of_adj hub2).symm, hyb2.symm, hb12.symm]
    refine ⟨ψs, hψu, hψy, hψb1, hψb2, ?_, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [hψu]; exact hα
      · rw [hψy]; exact hcy
      · rw [hψb1]; exact hc1
      · rw [hψb2]; exact hc2
    · intro x hx z hz hxz; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
      rcases hx with hx | hx | hx | hx
      · rw [hx] at hxz ⊢
        rcases hz with hz | hz | hz | hz
        · rw [hz] at hxz; exact False.elim (G.ne_of_adj hxz rfl)
        · rw [hz, hψu, hψy]; exact Ne.symm hcyα
        · rw [hz, hψu, hψb1]; exact Ne.symm hc1α
        · rw [hz, hψu, hψb2]; exact Ne.symm hc2α
      · rw [hx] at hxz ⊢
        rcases exists_unique_neighbor_of_deg_one hdy with ⟨w, _, huniq⟩
        have hzu : z = u := (huniq z hxz).trans (huniq u huy.symm).symm
        rw [hzu, hψy, hψu]; exact hcyα
      · rw [hx] at hxz ⊢
        rcases hb1_all z hxz with hz_eq | hz_eq
        · rw [hz_eq, hψb1, hψu]; exact hc1α
        · exfalso; rw [hz_eq] at hz
          rcases hz with h1 | h1 | h1 | h1
          · exact hp1u h1
          · exact ne_of_deg_ge_lt hdp1 hdy (by omega) h1
          · exact G.ne_of_adj hb1p1 h1.symm
          · exact ne_of_deg_ge_lt hdp1 hdb2 (by omega) h1
      · rw [hx] at hxz ⊢
        rcases hb2_all z hxz with hz_eq | hz_eq
        · rw [hz_eq, hψb2, hψu]; exact hc2α
        · exfalso; rw [hz_eq] at hz
          rcases hz with h1 | h1 | h1 | h1
          · exact hp2u h1
          · exact ne_of_deg_ge_lt hdp2 hdy (by omega) h1
          · exact ne_of_deg_ge_lt hdp2 hdb1 (by omega) h1
          · exact G.ne_of_adj hb2p2 h1.symm
  let S : SideData G L u a := {
    S_side := {u, y, b₁, b₂}, e₁ := b₁, e₂ := b₂, p₁ := p₁, p₂ := p₂,
    huS := by simp, he1S := by simp, he2S := by simp, he12 := hb12,
    ha_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj hua).symm, hay, hab1, hab2⟩,
    hp1_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp1u, ne_of_deg_ge_lt hdp1 hdy (by omega), (G.ne_of_adj hb1p1).symm,
        ne_of_deg_ge_lt hdp1 hdb2 (by omega)⟩,
    hp2_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hp2u, ne_of_deg_ge_lt hdp2 hdy (by omega), ne_of_deg_ge_lt hdp2 hdb1 (by omega),
        (G.ne_of_adj hb2p2).symm⟩,
    he1p1 := hb1p1, he2p2 := hb2p2, hdp1 := hdp1, hdp2 := hdp2,
    hdeg3_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · omega
      · omega,
    hdeg2_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact Or.inl ⟨hb1, hab1.symm⟩
      · exact Or.inl ⟨hb2, hab2.symm⟩,
    hdeg1_only := fun x hx hdx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · omega
      · exact ⟨u, by simp, by omega, huy.symm⟩
      · omega
      · omega,
    he_kind := fun e p hep => by
      rcases hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hb1, hab1.symm, hb1p1⟩
      · exact Or.inl ⟨hb2, hab2.symm, hb2p2⟩,
    hout := fun w hwS s hsS hws => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
      rcases hsS with rfl | rfl | rfl | rfl
      · rcases hu_all w hws.symm with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
      · rcases exists_unique_neighbor_of_deg_one hdy with ⟨z, _, huniq⟩
        have hwu : w = u := (huniq w hws.symm).trans (huniq u huy.symm).symm
        exact False.elim (hwS (by rw [hwu]; simp))
      · rcases hb1_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases hb2_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩),
    hgoodA := fun φ φs => by
      let C_v : Finset ℕ := L u \ {φ p₁, φ p₂}
      let P : ℕ → ℕ → ℕ → Prop := fun α c₁ c₂ =>
        c₁ ∈ L b₁ \ {φ p₁, φs p₁, α} ∧ c₂ ∈ L b₂ \ {φ p₂, φs p₂, α}
      have hCv : 3 ≤ C_v.card := by
        dsimp only [C_v]; have := card_sdiff_ge (L u) {φ p₁, φ p₂}
        have := Finset.card_le_two (a := φ p₁) (b := φ p₂); omega
      have hP : ∀ α ∈ C_v, ∃ c₁ c₂, P α c₁ c₂ := by
        intro α _
        rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {φ p₁, φs p₁, α})
          (by have := card_triple_le (φ p₁) (φs p₁) α; omega) with ⟨c₁, hc1L, hc1N⟩
        rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {φ p₂, φs p₂, α})
          (by have := card_triple_le (φ p₂) (φs p₂) α; omega) with ⟨c₂, hc2L, hc2N⟩
        exact ⟨c₁, c₂, Finset.mem_sdiff.mpr ⟨hc1L, hc1N⟩, Finset.mem_sdiff.mpr ⟨hc2L, hc2N⟩⟩
      rcases leafQuad_goodA_props hCv hLy2 hLa4 hP with ⟨hne, hsing⟩
      refine ⟨leafQuadGoodA C_v (L y) (L a) P, hne, fun C => le_trans (hsing C) (by omega),
        fun γ => Finset.filter_subset _ _, ?_⟩
      intro γ ca hca
      simp only [leafQuadGoodA, Finset.mem_filter] at hca
      rcases hca with ⟨_, α, hα, hαca, cy, hcy, c₁, c₂, ⟨hc1, hc2⟩, huniq⟩
      simp only [C_v, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcy hc1 hc2
      rcases hbuild α cy c₁ c₂ hα.1.1 hcy.1 hc1.1 hc2.1 hcy.2 hc1.2.2.2 hc2.2.2.2 with
        ⟨ψs, hψu, hψy, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨ψs, by rw [hψu]; exact hα.2, by rw [hψu]; exact hαca, hψL, hψprop,
        by rw [hψb1]; exact hc1.2.1, by rw [hψb1]; exact hc1.2.2.1,
        by rw [hψb2]; exact hc2.2.1, by rw [hψb2]; exact hc2.2.2.1, ?_⟩
      intro ψ hagree ha_eq hp1_eq hp2_eq x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hub1 hub2 hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree b₁ (by simp), hψb1, hagree b₂ (by simp), hψb2]
        rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1_eq]; exact hα.1.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2_eq]; exact hα.1.2.2),
    hgreedy := fun φ φs => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := insert (φ p₁) (insert (φ p₂) (L y)))
        (by have h1 : (insert (φ p₁) (insert (φ p₂) (L y))).card ≤ (L y).card + 2 :=
              le_trans (Finset.card_insert_le _ _)
                (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
            omega) with ⟨γ, hγL, hγN⟩
      simp only [Finset.mem_insert, not_or] at hγN
      rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {φ p₁, φs p₁, γ})
        (by have := card_triple_le (φ p₁) (φs p₁) γ; omega) with ⟨c₁, hc1L, hc1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
      rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {φ p₂, φs p₂, γ})
        (by have := card_triple_le (φ p₂) (φs p₂) γ; omega) with ⟨c₂, hc2L, hc2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
      rcases Finset.card_pos.mp (by omega : 0 < (L y).card) with ⟨cy, hcyL⟩
      have hcyγ : cy ≠ γ := fun h => hγN.2.2 (h ▸ hcyL)
      rcases exists_two_in_four_unique_quad hLa4 γ c₁ c₂ cy with
        ⟨ca₁, hca1, ca₂, hca2, hca12, hu1, hu2⟩
      rcases hbuild γ cy c₁ c₂ hγL hcyL hc1L hc2L hcyγ hc1N.2.2 hc2N.2.2 with
        ⟨ψs, hψu, hψy, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨γ, ca₁, ca₂, ψs, hca1, hca2, hca12, hψu, hψL, hψprop,
        by rw [hψb1]; exact hc1N.1, by rw [hψb1]; exact hc1N.2.1,
        by rw [hψb2]; exact hc2N.1, by rw [hψb2]; exact hc2N.2.1, ?_⟩
      intro ca hca ψ hagree ha_eq hp1_eq hp2_eq x hx
      have huniq : HasUniqueColor [c₁, c₂, cy, ca] := by
        rcases hca with rfl | rfl <;> assumption
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hub1 hub2 hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree b₁ (by simp), hψb1, hagree b₂ (by simp), hψb2]
        rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1_eq]; exact hγN.1)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2_eq]; exact hγN.2.1),
    hisoDouble := fun w ω γ_other ca₁ ca₂ B_w hp1w hp2w _ _ hca12 hB12 _ => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := insert γ_other (insert ω (L y)))
        (by have h1 : (insert γ_other (insert ω (L y))).card ≤ (L y).card + 2 :=
              le_trans (Finset.card_insert_le _ _)
                (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
            omega) with ⟨α, hαL, hαN⟩
      simp only [Finset.mem_insert, not_or] at hαN
      have hpick_ca : ∃ ca, (ca = ca₁ ∨ ca = ca₂) ∧ α ≠ ca := by
        by_cases h1 : α = ca₁
        · exact ⟨ca₂, Or.inr rfl, fun h => hca12 (h1.symm.trans h)⟩
        · exact ⟨ca₁, Or.inl rfl, h1⟩
      rcases hpick_ca with ⟨ca, hca_or, hαca⟩
      have hB1 : 2 ≤ (L b₁ \ {α, ω}).card := by
        have := card_sdiff_ge (L b₁) {α, ω}; have := Finset.card_le_two (a := α) (b := ω); omega
      have hB2 : 2 ≤ (L b₂ \ {α, ω}).card := by
        have := card_sdiff_ge (L b₂) {α, ω}; have := Finset.card_le_two (a := α) (b := ω); omega
      rcases pair_double_pcf hB1 hB2 ca B_w hB12 with ⟨c₁, hc1, c₂, hc2, _, hBw⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1 hc2
      rcases exists_fourth_unique_color (a := ca) (b := c₁) (c := c₂) (by omega : 2 ≤ (L y).card)
        with ⟨cy, hcyL, huniq_u⟩
      have hcyα : cy ≠ α := fun h => hαN.2.2 (h ▸ hcyL)
      rcases hbuild α cy c₁ c₂ hαL hcyL hc1.1 hc2.1 hcyα hc1.2.1 hc2.2.1 with
        ⟨ψs, hψu, hψy, hψb1, hψb2, hψL, hψprop⟩
      refine ⟨ca, hca_or, ψs, by rw [hψu]; exact hαN.1, by rw [hψu]; exact hαca,
        hψL, hψprop, by rw [hψb1]; exact hc1.2.2, by rw [hψb2]; exact hc2.2.2,
        by rw [hψb1, hψb2]; exact hBw, ?_⟩
      intro ψ hagree ha_eq hw_eq x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hub1 hub2 hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree b₁ (by simp), hψb1, hagree b₂ (by simp), hψb2]
        rcases huniq_u with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
          (by rw [hagree u (by simp), hψu, hp1w, hw_eq]; exact hαN.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
          (by rw [hagree u (by simp), hψu, hp2w, hw_eq]; exact hαN.2.1) }
  refine ⟨S, fun φ φs => ?_⟩
  refine ⟨L u \ {φ p₁, φ p₂}, Finset.sdiff_subset,
    by have := card_sdiff_ge (L u) {φ p₁, φ p₂}
       have := Finset.card_le_two (a := φ p₁) (b := φ p₂); omega,
    fun γ hγ G_a _ hGa2 => ?_⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
  rcases exists_mem_sdiff_of_lt (A := L b₁) (B := {φ p₁, φs p₁, γ})
    (by have := card_triple_le (φ p₁) (φs p₁) γ; omega) with ⟨c₁, hc1L, hc1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
  rcases exists_mem_sdiff_of_lt (A := L b₂) (B := {φ p₂, φs p₂, γ})
    (by have := card_triple_le (φ p₂) (φs p₂) γ; omega) with ⟨c₂, hc2L, hc2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
  rcases exists_mem_sdiff_of_lt (A := L y) (B := {γ})
    (by simp only [Finset.card_singleton]; omega) with ⟨cy, hcyL, hcyγ⟩
  rw [Finset.mem_singleton] at hcyγ
  rcases exists_two_of_card_ge_two hGa2 with ⟨ca₁, hca1G, ca₂, hca2G, hca12⟩
  have hpick_ca : ∃ ca ∈ G_a, HasUniqueColor [c₁, c₂, cy, ca] := by
    rcases hasUniqueColor_quad_or_of_ne_last (a := c₁) (b := c₂) (c := cy) hca12 with h1 | h2
    · exact ⟨ca₁, hca1G, h1⟩
    · exact ⟨ca₂, hca2G, h2⟩
  rcases hpick_ca with ⟨ca, hcaG, huniq⟩
  rcases hbuild γ cy c₁ c₂ hγ.1 hcyL hc1L hc2L hcyγ hc1N.2.2 hc2N.2.2 with
    ⟨ψs, hψu, hψy, hψb1, hψb2, hψL, hψprop⟩
  refine ⟨ca, hcaG, ψs, hψu, hψL, hψprop,
    by rw [hψb1]; exact hc1N.1, by rw [hψb1]; exact hc1N.2.1,
    by rw [hψb2]; exact hc2N.1, by rw [hψb2]; exact hc2N.2.1, ?_⟩
  intro ψ hagree ha_eq hp1_eq hp2_eq x hx
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine pcf_at_of_hasUniqueColor_four hua huy hub1 hub2 hu_all ?_
    rw [ha_eq, hagree y (by simp [S]), hψy, hagree b₁ (by simp [S]), hψb1,
      hagree b₂ (by simp [S]), hψb2]
    rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
  · exact pcf_at_deg_one hdy huy.symm
  · exact pcf_at_of_two_distinct_neighbors hdb1 hub1.symm hb1p1 hp1u.symm
      (by rw [hagree u (by simp [S]), hψu, hp1_eq]; exact hγ.2.1)
  · exact pcf_at_of_two_distinct_neighbors hdb2 hub2.symm hb2p2 hp2u.symm
      (by rw [hagree u (by simp [S]), hψu, hp2_eq]; exact hγ.2.2)

/-- `T21` 端元的强 `SideData` 构造。 -/
private lemma sideData_T21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsT21 G u) (ha : a ∈ oneThreadNbrs G u) :
    ∃ S : SideData G L u a, S.IsStrong := by
  classical
  rcases isT21_unpack_one hm hpq hu ha with
    ⟨y, t₁, x, hy, ht1, hx, hay, hat1, hax, hyt1, hyx, ht1x, hu_all⟩
  have hdu4 : G.degree u = 4 := (isT21_structure hm hpq hu).1
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have huy : G.Adj u y := (mem_leafNbrs.mp hy).1
  have hdy : G.degree y = 1 := (mem_leafNbrs.mp hy).2
  have hux : G.Adj u x := (mem_goodNbrs.mp hx).1
  have hdx3 : 3 ≤ G.degree x := deg_ge_three_of_isGood (mem_goodNbrs.mp hx).2
  rcases twoThreadNbr_other_endpoint hm (by omega) ht1 with
    ⟨t₂, z, hut1, hdt1, ht12, ht2u, hdt2, ht2z, hzt1, huz, hdz3, _, _, _⟩
  have hdz4 : 4 ≤ G.degree z := by
    by_contra hlt; push Not at hlt
    exact no_three_vertex_two_thread hm (by omega : G.degree z = 3) hdt2 hdt1 ht2z.symm ht12.symm
  have ht1_all : ∀ r, G.Adj t₁ r → r = u ∨ r = t₂ := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdt1 hut1.symm ht12 ht2u.symm
    have : r ∈ ({u, t₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₁ r).mpr hr
    simpa using this
  have ht2_all : ∀ r, G.Adj t₂ r → r = t₁ ∨ r = z := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdt2 ht12.symm ht2z hzt1.symm
    have : r ∈ ({t₁, z} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset t₂ r).mpr hr
    simpa using this
  have ht2a : t₂ ≠ a := fun heq => by
    have : u = t₁ ∨ u = z := ht2_all u (heq ▸ hua.symm)
    rcases this with h1 | h1
    · exact G.ne_of_adj hut1 h1
    · exact huz h1
  have ht2y : t₂ ≠ y := ne_of_deg_eq_ne hdt2 hdy (by omega)
  have ht2x : t₂ ≠ x := (ne_of_deg_ge_lt hdx3 hdt2 (by omega)).symm
  have hLu5 : (L u).card = 5 := by rw [hm.list_card u]; simp [kappa, hdu4]
  have hLy2 : (L y).card = 2 := by rw [hm.list_card y]; simp [kappa, hdy]
  have hLa4 : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hda]
  have hLt1 : (L t₁).card = 4 := by rw [hm.list_card t₁]; simp [kappa, hdt1]
  have hLt2 : (L t₂).card = 4 := by rw [hm.list_card t₂]; simp [kappa, hdt2]
  have hbuild : ∀ (α cy ct₁ ct₂ : ℕ), α ∈ L u → cy ∈ L y → ct₁ ∈ L t₁ → ct₂ ∈ L t₂ →
      cy ≠ α → ct₁ ≠ α → ct₁ ≠ ct₂ →
      ∃ ψs : V → ℕ, ψs u = α ∧ ψs y = cy ∧ ψs t₁ = ct₁ ∧ ψs t₂ = ct₂ ∧
        (∀ r ∈ ({u, y, t₁, t₂} : Finset V), ψs r ∈ L r) ∧
        (∀ r ∈ ({u, y, t₁, t₂} : Finset V), ∀ s ∈ ({u, y, t₁, t₂} : Finset V),
          G.Adj r s → ψs r ≠ ψs s) := by
    intro α cy ct₁ ct₂ hα hcy hct1 hct2 hcyα hct1α hct12
    let ψs : V → ℕ := fun r =>
      if r = u then α else if r = y then cy else if r = t₁ then ct₁ else ct₂
    have hψu : ψs u = α := by simp [ψs]
    have hψy : ψs y = cy := by simp [ψs, (G.ne_of_adj huy).symm]
    have hψt1 : ψs t₁ = ct₁ := by simp [ψs, (G.ne_of_adj hut1).symm, hyt1.symm]
    have hψt2 : ψs t₂ = ct₂ := by simp [ψs, ht2u, ht2y, (G.ne_of_adj ht12).symm]
    refine ⟨ψs, hψu, hψy, hψt1, hψt2, ?_, ?_⟩
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hψu]; exact hα
      · rw [hψy]; exact hcy
      · rw [hψt1]; exact hct1
      · rw [hψt2]; exact hct2
    · intro r hr s hs hrs; simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs
      rcases hr with hr | hr | hr | hr
      · rw [hr] at hrs ⊢
        rcases hu_all s hrs with hs_eq | hs_eq | hs_eq | hs_eq
        · exfalso; rw [hs_eq] at hs
          rcases hs with h1 | h1 | h1 | h1
          · exact G.ne_of_adj hua h1.symm
          · exact hay h1
          · exact hat1 h1
          · exact ht2a h1.symm
        · rw [hs_eq, hψu, hψy]; exact Ne.symm hcyα
        · rw [hs_eq, hψu, hψt1]; exact Ne.symm hct1α
        · exfalso; rw [hs_eq] at hs
          rcases hs with h1 | h1 | h1 | h1
          · exact G.ne_of_adj hux h1.symm
          · exact hyx h1.symm
          · exact ht1x h1.symm
          · exact ht2x h1.symm
      · rw [hr] at hrs ⊢
        rcases exists_unique_neighbor_of_deg_one hdy with ⟨w, _, huniq⟩
        have hsu : s = u := (huniq s hrs).trans (huniq u huy.symm).symm
        rw [hsu, hψy, hψu]; exact hcyα
      · rw [hr] at hrs ⊢
        rcases ht1_all s hrs with hs_eq | hs_eq
        · rw [hs_eq, hψt1, hψu]; exact hct1α
        · rw [hs_eq, hψt1, hψt2]; exact hct12
      · rw [hr] at hrs ⊢
        rcases ht2_all s hrs with hs_eq | hs_eq
        · rw [hs_eq, hψt2, hψt1]; exact Ne.symm hct12
        · exfalso; rw [hs_eq] at hs
          rcases hs with h1 | h1 | h1 | h1
          · exact huz h1.symm
          · exact ne_of_deg_ge_lt hdz3 hdy (by omega) h1
          · exact hzt1 h1
          · exact G.ne_of_adj ht2z h1.symm
  let S : SideData G L u a := {
    S_side := {u, y, t₁, t₂}, e₁ := u, e₂ := t₂, p₁ := x, p₂ := z,
    huS := by simp, he1S := by simp, he2S := by simp, he12 := ht2u.symm,
    ha_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj hua).symm, hay, hat1, ht2a.symm⟩,
    hp1_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj hux).symm, hyx.symm, ht1x.symm, ht2x.symm⟩,
    hp2_not := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huz.symm, ne_of_deg_ge_lt hdz3 hdy (by omega), hzt1, (G.ne_of_adj ht2z).symm⟩,
    he1p1 := hux, he2p2 := ht2z, hdp1 := hdx3, hdp2 := hdz3,
    hdeg3_only := fun r hr hdr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · omega
      · omega,
    hdeg2_only := fun r hr hdr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with hr | hr | hr | hr
      · rw [hr] at hdr; omega
      · rw [hr] at hdr; omega
      · exact Or.inr ⟨hu, t₁, t₂, z, ht1, ht12, hdt2, ht2u, ht2z, hzt1, hdz4, Or.inl hr⟩
      · exact Or.inr ⟨hu, t₁, t₂, z, ht1, ht12, hdt2, ht2u, ht2z, hzt1, hdz4, Or.inr hr⟩,
    hdeg1_only := fun r hr hdr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · omega
      · exact ⟨u, by simp, by omega, huy.symm⟩
      · omega
      · omega,
    he_kind := fun e p hep => by
      rcases hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hx, hux⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hu, t₁, ht1, ht12, hdt2, ht2u, ht2z, hzt1, hdz4⟩)),
    hout := fun w hwS s hsS hws => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
      rcases hsS with rfl | rfl | rfl | rfl
      · rcases hu_all w hws.symm with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases exists_unique_neighbor_of_deg_one hdy with ⟨w₀, _, huniq⟩
        have hwu : w = u := (huniq w hws.symm).trans (huniq u huy.symm).symm
        exact False.elim (hwS (by rw [hwu]; simp))
      · rcases ht1_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact False.elim (hwS (by simp))
      · rcases ht2_all w hws.symm with rfl | rfl
        · exact False.elim (hwS (by simp))
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩),
    hgoodA := fun φ φs => by
      let C_v : Finset ℕ := L u \ {φ x, φs x}
      let P : ℕ → ℕ → ℕ → Prop := fun α c₁ c₂ =>
        c₁ = φ x ∧ ∃ ct₂ ∈ L t₂ \ {φ z, φs z, α}, c₂ ∈ L t₁ \ {α, ct₂, φ z}
      have hCv : 3 ≤ C_v.card := by
        dsimp only [C_v]; have := card_sdiff_ge (L u) {φ x, φs x}
        have := Finset.card_le_two (a := φ x) (b := φs x); omega
      have hP : ∀ α ∈ C_v, ∃ c₁ c₂, P α c₁ c₂ := by
        intro α _
        rcases exists_mem_sdiff_of_lt (A := L t₂) (B := {φ z, φs z, α})
          (by have := card_triple_le (φ z) (φs z) α; omega) with ⟨ct₂, hct2L, hct2N⟩
        rcases exists_mem_sdiff_of_lt (A := L t₁) (B := {α, ct₂, φ z})
          (by have := card_triple_le α ct₂ (φ z); omega) with ⟨ct₁, hct1L, hct1N⟩
        exact ⟨φ x, ct₁, rfl, ct₂, Finset.mem_sdiff.mpr ⟨hct2L, hct2N⟩,
          Finset.mem_sdiff.mpr ⟨hct1L, hct1N⟩⟩
      rcases leafQuad_goodA_props hCv hLy2 hLa4 hP with ⟨hne, hsing⟩
      refine ⟨leafQuadGoodA C_v (L y) (L a) P, hne, fun C => le_trans (hsing C) (by omega),
        fun γ => Finset.filter_subset _ _, ?_⟩
      intro γ ca hca
      simp only [leafQuadGoodA, Finset.mem_filter] at hca
      rcases hca with ⟨_, α, hα, hαca, cy, hcy, _, ct₁, ⟨rfl, ct₂, hct2, hct1⟩, huniq⟩
      simp only [C_v, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcy hct2 hct1
      rcases hbuild α cy ct₁ ct₂ hα.1.1 hcy.1 hct1.1 hct2.1 hcy.2 hct1.2.1 hct1.2.2.1 with
        ⟨ψs, hψu, hψy, hψt1, hψt2, hψL, hψprop⟩
      refine ⟨ψs, by rw [hψu]; exact hα.2, by rw [hψu]; exact hαca, hψL, hψprop,
        by rw [hψu]; exact hα.1.2.1, by rw [hψu]; exact hα.1.2.2,
        by rw [hψt2]; exact hct2.2.1, by rw [hψt2]; exact hct2.2.2.1, ?_⟩
      intro ψ hagree ha_eq hpx_eq hpz_eq r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hut1 hux hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree t₁ (by simp), hψt1, hpx_eq]
        rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdt1 hut1.symm ht12 ht2u.symm
          (by rw [hagree u (by simp), hψu, hagree t₂ (by simp), hψt2]; exact Ne.symm hct2.2.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdt2 ht12.symm ht2z hzt1.symm
          (by rw [hagree t₁ (by simp), hψt1, hpz_eq]; exact hct1.2.2.2),
    hgreedy := fun φ φs => by
      rcases exists_mem_sdiff_of_lt (A := L u) (B := insert (φ x) (insert (φs x) (L y)))
        (by have h1 : (insert (φ x) (insert (φs x) (L y))).card ≤ (L y).card + 2 :=
              le_trans (Finset.card_insert_le _ _)
                (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
            omega) with ⟨γ, hγL, hγN⟩
      simp only [Finset.mem_insert, not_or] at hγN
      rcases exists_mem_sdiff_of_lt (A := L t₂) (B := {φ z, φs z, γ})
        (by have := card_triple_le (φ z) (φs z) γ; omega) with ⟨ct₂, hct2L, hct2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct2N
      rcases exists_mem_sdiff_of_lt (A := L t₁) (B := {γ, ct₂, φ z})
        (by have := card_triple_le γ ct₂ (φ z); omega) with ⟨ct₁, hct1L, hct1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
      rcases Finset.card_pos.mp (by omega : 0 < (L y).card) with ⟨cy, hcyL⟩
      have hcyγ : cy ≠ γ := fun h => hγN.2.2 (h ▸ hcyL)
      rcases exists_two_in_four_unique_quad hLa4 γ (φ x) ct₁ cy with
        ⟨ca₁, hca1, ca₂, hca2, hca12, hu1, hu2⟩
      rcases hbuild γ cy ct₁ ct₂ hγL hcyL hct1L hct2L hcyγ hct1N.1 hct1N.2.1 with
        ⟨ψs, hψu, hψy, hψt1, hψt2, hψL, hψprop⟩
      refine ⟨γ, ca₁, ca₂, ψs, hca1, hca2, hca12, hψu, hψL, hψprop,
        by rw [hψu]; exact hγN.1, by rw [hψu]; exact hγN.2.1,
        by rw [hψt2]; exact hct2N.1, by rw [hψt2]; exact hct2N.2.1, ?_⟩
      intro ca hca ψ hagree ha_eq hpx_eq hpz_eq r hr
      have huniq : HasUniqueColor [φ x, ct₁, cy, ca] := by
        rcases hca with rfl | rfl <;> assumption
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hut1 hux hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree t₁ (by simp), hψt1, hpx_eq]
        rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdt1 hut1.symm ht12 ht2u.symm
          (by rw [hagree u (by simp), hψu, hagree t₂ (by simp), hψt2]; exact Ne.symm hct2N.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdt2 ht12.symm ht2z hzt1.symm
          (by rw [hagree t₁ (by simp), hψt1, hpz_eq]; exact hct1N.2.2),
    hisoDouble := fun w ω γ_other ca₁ ca₂ B_w hp1w hp2w _ _ hca12 _ hBlen => by
      have hB2 : B_w.length = 2 := by rw [hp2w] at hdz4; omega
      rcases List.length_eq_two.mp hB2 with ⟨c₁, c₂, rfl⟩
      rcases exists_mem_sdiff_of_lt (A := L u) (B := insert γ_other (insert ω (L y)))
        (by have h1 : (insert γ_other (insert ω (L y))).card ≤ (L y).card + 2 :=
              le_trans (Finset.card_insert_le _ _)
                (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
            omega) with ⟨α, hαL, hαN⟩
      simp only [Finset.mem_insert, not_or] at hαN
      have hpick_ca : ∃ ca, (ca = ca₁ ∨ ca = ca₂) ∧ α ≠ ca := by
        by_cases h1 : α = ca₁
        · exact ⟨ca₂, Or.inr rfl, fun h => hca12 (h1.symm.trans h)⟩
        · exact ⟨ca₁, Or.inl rfl, h1⟩
      rcases hpick_ca with ⟨ca, hca_or, hαca⟩
      have hLt2' : 2 ≤ (L t₂ \ {ω, α}).card := by
        have := card_sdiff_ge (L t₂) {ω, α}; have := Finset.card_le_two (a := ω) (b := α); omega
      rcases exists_fourth_unique_color (a := c₁) (b := c₂) (c := α) hLt2' with ⟨ct₂, hct2, hBw⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hct2
      rcases exists_mem_sdiff_of_lt (A := L t₁) (B := {α, ct₂, ω})
        (by have := card_triple_le α ct₂ ω; omega) with ⟨ct₁, hct1L, hct1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
      rcases exists_fourth_unique_color (a := ω) (b := ca) (c := ct₁) (by omega : 2 ≤ (L y).card)
        with ⟨cy, hcyL, huniq_u⟩
      have hcyα : cy ≠ α := fun h => hαN.2.2 (h ▸ hcyL)
      rcases hbuild α cy ct₁ ct₂ hαL hcyL hct1L hct2.1 hcyα hct1N.1 hct1N.2.1 with
        ⟨ψs, hψu, hψy, hψt1, hψt2, hψL, hψprop⟩
      refine ⟨ca, hca_or, ψs, by rw [hψu]; exact hαN.1, by rw [hψu]; exact hαca,
        hψL, hψprop, by rw [hψu]; exact hαN.2.1, by rw [hψt2]; exact hct2.2.1,
        by rw [hψu, hψt2]; exact hBw, ?_⟩
      intro ψ hagree ha_eq hw_eq r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · refine pcf_at_of_hasUniqueColor_four hua huy hut1 hux hu_all ?_
        rw [ha_eq, hagree y (by simp), hψy, hagree t₁ (by simp), hψt1, hp1w, hw_eq]
        rcases huniq_u with ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
      · exact pcf_at_deg_one hdy huy.symm
      · exact pcf_at_of_two_distinct_neighbors hdt1 hut1.symm ht12 ht2u.symm
          (by rw [hagree u (by simp), hψu, hagree t₂ (by simp), hψt2]; exact Ne.symm hct2.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdt2 ht12.symm ht2z hzt1.symm
          (by rw [hagree t₁ (by simp), hψt1, hp2w, hw_eq]; exact hct1N.2.2) }
  refine ⟨S, fun φ φs => ?_⟩
  refine ⟨L u \ {φ x, φs x}, Finset.sdiff_subset,
    by have := card_sdiff_ge (L u) {φ x, φs x}
       have := Finset.card_le_two (a := φ x) (b := φs x); omega,
    fun γ hγ G_a _ hGa2 => ?_⟩
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
  rcases exists_mem_sdiff_of_lt (A := L t₂) (B := {φ z, φs z, γ})
    (by have := card_triple_le (φ z) (φs z) γ; omega) with ⟨ct₂, hct2L, hct2N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct2N
  rcases exists_mem_sdiff_of_lt (A := L t₁) (B := {γ, ct₂, φ z})
    (by have := card_triple_le γ ct₂ (φ z); omega) with ⟨ct₁, hct1L, hct1N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct1N
  rcases exists_mem_sdiff_of_lt (A := L y) (B := {γ})
    (by simp only [Finset.card_singleton]; omega) with ⟨cy, hcyL, hcyγ⟩
  rw [Finset.mem_singleton] at hcyγ
  rcases exists_two_of_card_ge_two hGa2 with ⟨ca₁, hca1G, ca₂, hca2G, hca12⟩
  have hpick_ca : ∃ ca ∈ G_a, HasUniqueColor [φ x, ct₁, cy, ca] := by
    rcases hasUniqueColor_quad_or_of_ne_last (a := φ x) (b := ct₁) (c := cy) hca12 with h1 | h2
    · exact ⟨ca₁, hca1G, h1⟩
    · exact ⟨ca₂, hca2G, h2⟩
  rcases hpick_ca with ⟨ca, hcaG, huniq⟩
  rcases hbuild γ cy ct₁ ct₂ hγ.1 hcyL hct1L hct2L hcyγ hct1N.1 hct1N.2.1 with
    ⟨ψs, hψu, hψy, hψt1, hψt2, hψL, hψprop⟩
  refine ⟨ca, hcaG, ψs, hψu, hψL, hψprop,
    by rw [hψu]; exact hγ.2.1, by rw [hψu]; exact hγ.2.2,
    by rw [hψt2]; exact hct2N.1, by rw [hψt2]; exact hct2N.2.1, ?_⟩
  intro ψ hagree ha_eq hpx_eq hpz_eq r hr
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine pcf_at_of_hasUniqueColor_four hua huy hut1 hux hu_all ?_
    dsimp only [S] at hpx_eq
    rw [ha_eq, hagree y (by simp [S]), hψy, hagree t₁ (by simp [S]), hψt1, hpx_eq]
    rcases huniq with ⟨c, hc⟩; refine ⟨c, ?_⟩
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc ⊢; omega
  · exact pcf_at_deg_one hdy huy.symm
  · exact pcf_at_of_two_distinct_neighbors hdt1 hut1.symm ht12 ht2u.symm
      (by rw [hagree u (by simp [S]), hψu, hagree t₂ (by simp [S]), hψt2]; exact Ne.symm hct2N.2.2)
  · exact pcf_at_of_two_distinct_neighbors hdt2 ht12.symm ht2z hzt1.symm
      (by rw [hagree t₁ (by simp [S]), hψt1, hpz_eq]; exact hct1N.2.2)

/-- `IsPoor1Ext` 顶点若有坏邻点，则必为 `B3`。 -/
private lemma isB3_of_isPoor1Ext_badNbr {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u b : V}
    (hu : IsPoor1Ext G u) (hb : b ∈ badNbrs G u) : IsB3 G u := by
  rcases hu with hL3 | hB3 | hT21 | hL4
  · exfalso
    have hst := isL3_structure hm hL3
    have : b ∈ oneThreadNbrs G u := by
      rw [← hst.2.2.2.1]; exact (G.mem_neighborFinset u b).mpr (mem_badNbrs.mp hb).1
    have h1 := (mem_oneThreadNbrs.mp this).2.1
    have h2 := (mem_badNbrs.mp hb).2.1
    omega
  · exact hB3
  · exfalso
    have hst := isT21_structure hm hpq hT21
    have h0 := hst.2.2.2.2.2.1
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hb
    exact Finset.notMem_empty _ hb
  · exfalso
    have hst := isL4_structure hm hpq hL4
    have h0 := hst.2.2.2.2.2.1
    rw [h0] at hb
    exact Finset.notMem_empty _ hb

/-- 任意 `IsPoor1Ext` 顶点均能构造其 `SideData`。 -/
private lemma sideData_of_isPoor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u a : V}
    (hu : IsPoor1Ext G u) (ha : a ∈ oneThreadNbrs G u) :
    Nonempty (SideData G L u a) := by
  rcases hu with hL3 | hB3 | hT21 | hL4
  · exact sideData_L3 hm hL3 ha
  · rcases sideData_B3 hm hpq hB3 ha with ⟨S, _⟩; exact ⟨S⟩
  · rcases sideData_T21 hm hpq hT21 ha with ⟨S, _⟩; exact ⟨S⟩
  · rcases sideData_L4 hm hpq hL4 ha with ⟨S, _⟩; exact ⟨S⟩

/-- 两个由 `1`-线串 `u - a - v` 相连的 `IsPoor1Ext` 端元：双侧 `S_side` 不交，且边界外点互不落入对侧。 -/
private lemma sideData_disjoint_and_ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a : V}
    (hu : IsPoor1Ext G u) (hv : IsPoor1Ext G v) (huv : u ≠ v)
    (ha : a ∈ oneThreadNbrs G u) (hav : G.Adj a v)
    (Su : SideData G L u a) (Sv : SideData G L v a) :
    Disjoint Su.S_side Sv.S_side ∧
      Su.p₁ ∉ Sv.S_side ∧ Su.p₂ ∉ Sv.S_side ∧
      Sv.p₁ ∉ Su.S_side ∧ Sv.p₂ ∉ Su.S_side := by
  classical
  have hdu3 : 3 ≤ G.degree u := deg_ge_three_of_isPoor1Ext hm hu
  have hdv3 : 3 ≤ G.degree v := deg_ge_three_of_isPoor1Ext hm hv
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hv_a : a ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hav.symm, hda, u, hua.symm, huv, hdu3⟩
  have hno_3plus : ∀ z, 3 ≤ G.degree z → z ∈ Su.S_side → z ∈ Sv.S_side → False := by
    intro z hdz hzu hzv
    rcases Su.hdeg3_only z hzu hdz with rfl | ⟨hbz, hbu⟩
    · rcases Sv.hdeg3_only z hzv hdz with h | ⟨hbz, _⟩
      · exact huv h
      · exact not_isBad_of_isPoor1Ext hm hu hbz
    · rcases Sv.hdeg3_only z hzv hdz with rfl | ⟨_, hbv⟩
      · exact not_isBad_of_isPoor1Ext hm hv hbz
      · exact no_B3_B3_shared_bad_with_oneThread hm hpq
          (isB3_of_isPoor1Ext_badNbr hm hpq hu hbu)
          (isB3_of_isPoor1Ext_badNbr hm hpq hv hbv) huv ha hav hbu hbv
  have hdisj : Disjoint Su.S_side Sv.S_side := by
    rw [Finset.disjoint_left]
    intro z hzu hzv
    have hdz1 := degree_ge_one hm z
    by_cases hdz3 : 3 ≤ G.degree z
    · exact hno_3plus z hdz3 hzu hzv
    · by_cases hdz1' : G.degree z = 1
      · rcases Su.hdeg1_only z hzu hdz1' with ⟨w₁, hw1S, hdw1, hzw1⟩
        rcases Sv.hdeg1_only z hzv hdz1' with ⟨w₂, hw2S, _, hzw2⟩
        rcases exists_unique_neighbor_of_deg_one hdz1' with ⟨w₀, _, huniq⟩
        have hEq : w₁ = w₂ := (huniq w₁ hzw1).trans (huniq w₂ hzw2).symm
        exact hno_3plus w₁ hdw1 hw1S (hEq ▸ hw2S)
      · have hdz2 : G.degree z = 2 := by omega
        have hone_ne_two : ∀ {x y t₁ t₂ z₀ : V}, 3 ≤ G.degree x →
            z ∈ oneThreadNbrs G x → t₁ ∈ twoThreadNbrs G y → G.Adj t₁ t₂ →
            G.degree t₂ = 2 → (z = t₁ ∨ z = t₂) → False := by
          intro x y t₁ t₂ z₀ hdx hz1 ht1 ht12 hdt2 hzor
          rcases oneThreadNbr_other_endpoint hm hdx hz1 with ⟨w, hzw, hwx, hdw3, _, _⟩
          have hN := neighborFinset_eq_pair_of_deg_two hdz2 (mem_oneThreadNbrs.mp hz1).1.symm hzw
            hwx.symm
          rcases hzor with rfl | rfl
          · have : t₂ ∈ ({x, w} : Finset V) := by
              rw [← hN]; exact (G.mem_neighborFinset z t₂).mpr ht12
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h <;> (rw [h] at hdt2; omega)
          · have hdt1 : G.degree t₁ = 2 := (mem_twoThreadNbrs.mp ht1).2.1
            have : t₁ ∈ ({x, w} : Finset V) := by
              rw [← hN]; exact (G.mem_neighborFinset z t₁).mpr ht12.symm
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h <;> (rw [h] at hdt1; omega)
        rcases Su.hdeg2_only z hzu hdz2 with ⟨hz1u, hza⟩ |
            ⟨huT, t₁, t₂, z₁, ht1, ht12, hdt2, ht2u, ht2z1, hz1t1, hdz1, hzu_or⟩
        · rcases Sv.hdeg2_only z hzv hdz2 with ⟨hz1v, _⟩ |
              ⟨_, s₁, s₂, z₂, hs1, hs12, hds2, _, _, _, _, hzv_or⟩
          · exact no_two_oneThreads_between_Poor1Ext hm hpq hu hv huv ha hz1u hza.symm hav
              (mem_oneThreadNbrs.mp hz1v).1.symm
          · exact hone_ne_two (z₀ := z₂) hdu3 hz1u hs1 hs12 hds2 hzv_or
        · rcases Sv.hdeg2_only z hzv hdz2 with ⟨hz1v, _⟩ |
              ⟨hvT, s₁, s₂, z₂, hs1, hs12, hds2, hs2v, hs2z2, hz2s1, hdz2_4, hzv_or⟩
          · exact hone_ne_two (z₀ := z₁) hdv3 hz1v ht1 ht12 hdt2 hzu_or
          · have hut1 : G.Adj u t₁ := (mem_twoThreadNbrs.mp ht1).1
            have hdt1 : G.degree t₁ = 2 := (mem_twoThreadNbrs.mp ht1).2.1
            have hvs1 : G.Adj v s₁ := (mem_twoThreadNbrs.mp hs1).1
            have hds1 : G.degree s₁ = 2 := (mem_twoThreadNbrs.mp hs1).2.1
            have ht1_all : ∀ r, G.Adj t₁ r → r = u ∨ r = t₂ := by
              intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hdt1 hut1.symm ht12 ht2u.symm
              have : r ∈ ({u, t₂} : Finset V) := by
                rw [← hN]; exact (G.mem_neighborFinset t₁ r).mpr hr
              simpa using this
            have ht2_all : ∀ r, G.Adj t₂ r → r = t₁ ∨ r = z₁ := by
              intro r hr
              have hN := neighborFinset_eq_pair_of_deg_two hdt2 ht12.symm ht2z1 hz1t1.symm
              have : r ∈ ({t₁, z₁} : Finset V) := by
                rw [← hN]; exact (G.mem_neighborFinset t₂ r).mpr hr
              simpa using this
            rcases hzu_or with hz_eq | hz_eq <;> rcases hzv_or with hs_eq | hs_eq
            · have ht1s1 : t₁ = s₁ := hz_eq.symm.trans hs_eq
              rcases ht1_all v (ht1s1 ▸ hvs1.symm) with h | h
              · exact huv h.symm
              · rw [h] at hdv3; omega
            · have ht1s2 : t₁ = s₂ := hz_eq.symm.trans hs_eq
              have hs1_eq : s₁ = t₂ := by
                rcases ht1_all s₁ (ht1s2 ▸ hs12.symm) with h | h
                · rw [h] at hds1; omega
                · exact h
              have ht2v : G.Adj t₂ v := hs1_eq ▸ hvs1.symm
              have hvt1 : v ≠ t₁ := ne_of_deg_ge_lt hdv3 hdt1 (by omega)
              exact no_T21_two_thread_T21 hm hpq huT hvT
                ⟨t₁, t₂, hut1, hdt1, ht12, ht2u, hdt2, ht2v, hvt1, huv⟩
            · have ht2s1 : t₂ = s₁ := hz_eq.symm.trans hs_eq
              have ht1_eq : t₁ = s₂ := by
                have hs1_all : ∀ r, G.Adj s₁ r → r = v ∨ r = s₂ := by
                  intro r hr
                  have hN := neighborFinset_eq_pair_of_deg_two hds1 hvs1.symm hs12 hs2v.symm
                  have : r ∈ ({v, s₂} : Finset V) := by
                    rw [← hN]; exact (G.mem_neighborFinset s₁ r).mpr hr
                  simpa using this
                rcases hs1_all t₁ (ht2s1 ▸ ht12.symm) with h | h
                · rw [h] at hdt1; omega
                · exact h
              have hs2u : G.Adj s₂ u := ht1_eq ▸ hut1.symm
              have hus1 : u ≠ s₁ := ne_of_deg_ge_lt hdu3 hds1 (by omega)
              exact no_T21_two_thread_T21 hm hpq hvT huT
                ⟨s₁, s₂, hvs1, hds1, hs12, hs2v, hds2, hs2u, hus1, huv.symm⟩
            · have ht2s2 : t₂ = s₂ := hz_eq.symm.trans hs_eq
              have hs1_eq : s₁ = t₁ := by
                rcases ht2_all s₁ (ht2s2 ▸ hs12.symm) with h | h
                · exact h
                · rw [h] at hds1; omega
              rcases ht1_all v (hs1_eq ▸ hvs1.symm) with h | h
              · exact huv h.symm
              · rw [h] at hdv3; omega
  have hp_not_other : ∀ {x y : V} (hx : IsPoor1Ext G x) (hy : IsPoor1Ext G y) (hxy : x ≠ y)
      (hxa : a ∈ oneThreadNbrs G x) (hay : G.Adj a y)
      (Sx : SideData G L x a) (Sy : SideData G L y a) (e p : V),
      ((e = Sx.e₁ ∧ p = Sx.p₁) ∨ (e = Sx.e₂ ∧ p = Sx.p₂)) → 3 ≤ G.degree p → p ∉ Sy.S_side := by
    intro x y hx hy hxy hxa hay Sx Sy e p hep hdp hpS
    have hdx3 : 3 ≤ G.degree x := deg_ge_three_of_isPoor1Ext hm hx
    have hdy3 : 3 ≤ G.degree y := deg_ge_three_of_isPoor1Ext hm hy
    rcases Sy.hdeg3_only p hpS hdp with hp_eq | ⟨hbadp, hpby⟩
    · rcases Sx.he_kind e p hep with
          ⟨he1, hea, he_adj⟩ | ⟨_, heb, he_adj⟩ | ⟨_, _, hxp⟩ |
          ⟨hxT, t₁, ht1, ht1e, hde, hex, he_adj, hpt1, _⟩
      · exact no_two_oneThreads_between_Poor1Ext hm hpq hx hy hxy hxa he1 hea.symm hay
          (hp_eq ▸ he_adj)
      · have heby : e ∈ badNbrs G y := mem_badNbrs.mpr ⟨hp_eq ▸ he_adj.symm, (mem_badNbrs.mp heb).2⟩
        exact no_B3_B3_shared_bad_with_oneThread hm hpq
          (isB3_of_isPoor1Ext_badNbr hm hpq hx heb)
          (isB3_of_isPoor1Ext_badNbr hm hpq hy heby) hxy hxa hay heb heby
      · have hxy_adj : G.Adj x y := hp_eq ▸ hxp
        rcases adj_isPoor1Ext_implies_both_T21 hm hpq hx hy hxy_adj with ⟨hxT, hyT⟩
        exact no_T21_adj_T21_with_oneThread hm hpq hxT hyT hxy_adj hxa hay
      · by_cases hyT : IsT21 G y
        · exact no_T21_two_thread_T21 hm hpq hxT hyT
            ⟨t₁, e, (mem_twoThreadNbrs.mp ht1).1, (mem_twoThreadNbrs.mp ht1).2.1,
              ht1e, hex, hde, hp_eq ▸ he_adj, hp_eq ▸ hpt1, hxy⟩
        · have he2y : e ∈ twoThreadNbrs G y := by
            rw [mem_twoThreadNbrs]
            refine ⟨hp_eq ▸ he_adj.symm, hde, t₁, x, ht1e.symm,
              (ne_of_deg_ge_lt hdy3 (mem_twoThreadNbrs.mp ht1).2.1 (by omega)).symm,
              (mem_twoThreadNbrs.mp ht1).2.1, (mem_twoThreadNbrs.mp ht1).1.symm, hex.symm, hdx3⟩
          rw [twoThreadNbrs_eq_empty_of_not_isT21 hm hpq hy hyT] at he2y
          exact Finset.notMem_empty _ he2y
    · rcases Sx.he_kind e p hep with
          ⟨he1, _, he_adj⟩ | ⟨hbade, _, he_adj⟩ | ⟨_, hpgood, _⟩ |
          ⟨_, t₁, ht1, ht1e, hde, _, he_adj, hpt1, _⟩
      · have he1p : e ∈ oneThreadNbrs G p :=
          mem_oneThreadNbrs.mpr ⟨he_adj.symm, (mem_oneThreadNbrs.mp he1).2.1, x,
            (mem_oneThreadNbrs.mp he1).1.symm,
            fun h => not_isBad_of_isPoor1Ext hm hx (h ▸ hbadp), hdx3⟩
        rw [bad_no_one_thread hm hbadp] at he1p
        exact Finset.notMem_empty _ he1p
      · exact no_adjacent_bad hm hpq hbade hbadp he_adj
      · have hpg := (mem_goodNbrs.mp hpgood).2
        have hpb := hbadp.2
        unfold IsGood at hpg; omega
      · have helong : e ∈ longThreadNbrs G p := by
          dsimp only [longThreadNbrs]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p e).mpr he_adj.symm, hde⟩,
            he_adj.symm, hde, t₁, ht1e.symm, hpt1.symm, (mem_twoThreadNbrs.mp ht1).2.1⟩
        rw [bad_no_long_thread hm hpq hbadp] at helong
        exact Finset.notMem_empty _ helong
  exact ⟨hdisj,
    hp_not_other hu hv huv ha hav Su Sv Su.e₁ Su.p₁ (Or.inl ⟨rfl, rfl⟩) Su.hdp1,
    hp_not_other hu hv huv ha hav Su Sv Su.e₂ Su.p₂ (Or.inr ⟨rfl, rfl⟩) Su.hdp2,
    hp_not_other hv hu huv.symm hv_a hua.symm Sv Su Sv.e₁ Sv.p₁ (Or.inl ⟨rfl, rfl⟩) Sv.hdp1,
    hp_not_other hv hu huv.symm hv_a hua.symm Sv Su Sv.e₂ Sv.p₂ (Or.inr ⟨rfl, rfl⟩) Sv.hdp2⟩

/-- 孤立外点情形通用归约：当唯一孤立外点 `w` 与 `Sv` 两侧均相连（`Sv.p₁ = w ∧ Sv.p₂ = w`）时推出矛盾。 -/
private lemma one_thread_iso_contradiction {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v a : V}
    (huv : u ≠ v) (hua : G.Adj u a) (hav : G.Adj a v) (hda : G.degree a = 2)
    (Su : SideData G L u a) (Sv : SideData G L v a)
    (hdisj : Disjoint Su.S_side Sv.S_side)
    (hp1u_not : Su.p₁ ∉ Sv.S_side) (hp2u_not : Su.p₂ ∉ Sv.S_side)
    (adm : AdmissibleColoring G L (insert a (Su.S_side ∪ Sv.S_side)))
    (w : V) (hwS : w ∉ insert a (Su.S_side ∪ Sv.S_side))
    (hw_iso : ∀ r, r ∉ insert a (Su.S_side ∪ Sv.S_side) → ¬ G.Adj w r)
    (hwe1v : G.Adj w Sv.e₁) (hwe2v : G.Adj w Sv.e₂)
    (hS_out : ∀ z, z ∉ insert a (Su.S_side ∪ Sv.S_side) →
      ∀ s ∈ insert a (Su.S_side ∪ Sv.S_side), G.Adj z s →
        (s = Su.e₁ ∧ z = Su.p₁) ∨ (s = Su.e₂ ∧ z = Su.p₂) ∨
        (s = Sv.e₁ ∧ z = Sv.p₁) ∨ (s = Sv.e₂ ∧ z = Sv.p₂))
    (hw_uniq : ∀ w', w' ∉ insert a (Su.S_side ∪ Sv.S_side) →
      (∀ r, r ∉ insert a (Su.S_side ∪ Sv.S_side) → ¬ G.Adj w' r) → (∃ s, G.Adj w' s) → w' = w) :
    False := by
  classical
  let S : Finset V := insert a (Su.S_side ∪ Sv.S_side)
  have hwSv : w ∉ Sv.S_side := fun h => hwS (by simp [h])
  have hwa : w ≠ a := fun h => hwS (by simp [h])
  have hp1v : Sv.p₁ = w := by
    rcases Sv.hout w hwSv Sv.e₁ Sv.he1S hwe1v with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact False.elim (hwa h)
    · exact h.symm
    · exact False.elim (Sv.he12 h)
  have hp2v : Sv.p₂ = w := by
    rcases Sv.hout w hwSv Sv.e₂ Sv.he2S hwe2v with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact False.elim (hwa h)
    · exact False.elim (Sv.he12 h.symm)
    · exact h.symm
  have hdw3 : 3 ≤ G.degree w := hp1v ▸ Sv.hdp1
  have hp1uS : Su.p₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨ne_of_deg_ge_lt Su.hdp1 hda (by omega), Su.hp1_not, hp1u_not⟩
  have hp2uS : Su.p₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨ne_of_deg_ge_lt Su.hdp2 hda (by omega), Su.hp2_not, hp2u_not⟩
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  rcases Su.hgreedy adm.φ adm.φs with
    ⟨γ, ca₁, ca₂, ψ_u, hca1, hca2, hca12, hψu_u, hψu_L, hψu_prop,
      hψu_e1p, hψu_e1ps, hψu_e2p, hψu_e2ps, hψu_pcf⟩
  have hNw_sub : G.neighborFinset w ⊆ {Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} := by
    intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
    have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr
    rcases hS_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have heu1_v1 : Su.e₁ ≠ Sv.e₁ := fun h => Finset.disjoint_left.mp hdisj Su.he1S (h ▸ Sv.he1S)
  have heu1_v2 : Su.e₁ ≠ Sv.e₂ := fun h => Finset.disjoint_left.mp hdisj Su.he1S (h ▸ Sv.he2S)
  have heu2_v1 : Su.e₂ ≠ Sv.e₁ := fun h => Finset.disjoint_left.mp hdisj Su.he2S (h ▸ Sv.he1S)
  have heu2_v2 : Su.e₂ ≠ Sv.e₂ := fun h => Finset.disjoint_left.mp hdisj Su.he2S (h ▸ Sv.he2S)
  have hBw_build : ∃ B_w : List ℕ, (B_w.length = 1 ∨ B_w.length = 2) ∧ B_w.length + 2 = G.degree w ∧
      ∀ (ψ : V → ℕ), ψ Su.e₁ = ψ_u Su.e₁ → ψ Su.e₂ = ψ_u Su.e₂ →
        HasUniqueColor (B_w ++ [ψ Sv.e₁, ψ Sv.e₂]) →
        ∃ y, G.Adj w y ∧ ∀ z, G.Adj w z → ψ z = ψ y → z = y := by
    by_cases h1 : G.Adj w Su.e₁
    · by_cases h2 : G.Adj w Su.e₂
      · have hNw_eq : G.neighborFinset w = {Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} := by
          apply Finset.Subset.antisymm hNw_sub
          intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl | rfl | rfl <;>
            exact (G.mem_neighborFinset w _).mpr (by assumption)
        have hdw4 : G.degree w = 4 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hNw_eq,
              Finset.card_insert_of_notMem (by simp [Su.he12, heu1_v1, heu1_v2]),
              Finset.card_insert_of_notMem (by simp [heu2_v1, heu2_v2]),
              Finset.card_pair Sv.he12]
        refine ⟨[ψ_u Su.e₁, ψ_u Su.e₂], Or.inr rfl,
          by simp only [List.length_cons, List.length_nil]; omega, fun ψ he1 he2 huniq => ?_⟩
        refine pcf_at_of_hasUniqueColor_four h1 h2 hwe1v hwe2v (fun z hz => ?_)
          (by rw [he1, he2]; exact huniq)
        have : z ∈ ({Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} : Finset V) := by
          rw [← hNw_eq]; exact (G.mem_neighborFinset w z).mpr hz
        simpa using this
      · have hNw_eq : G.neighborFinset w = {Su.e₁, Sv.e₁, Sv.e₂} := by
          apply Finset.Subset.antisymm
          · intro r hr
            have hm := hNw_sub hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (h2 ((G.mem_neighborFinset w _).mp hr))
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with rfl | rfl | rfl <;> exact (G.mem_neighborFinset w _).mpr (by assumption)
        have hdw3' : G.degree w = 3 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hNw_eq,
              Finset.card_insert_of_notMem (by simp [heu1_v1, heu1_v2]),
              Finset.card_pair Sv.he12]
        refine ⟨[ψ_u Su.e₁], Or.inl rfl,
          by simp only [List.length_cons, List.length_nil]; omega, fun ψ he1 _ huniq => ?_⟩
        refine pcf_at_of_hasUniqueColor_three h1 hwe1v hwe2v (fun z hz => ?_)
          (by rw [he1]; exact huniq)
        have : z ∈ ({Su.e₁, Sv.e₁, Sv.e₂} : Finset V) := by
          rw [← hNw_eq]; exact (G.mem_neighborFinset w z).mpr hz
        simpa using this
    · by_cases h2 : G.Adj w Su.e₂
      · have hNw_eq : G.neighborFinset w = {Su.e₂, Sv.e₁, Sv.e₂} := by
          apply Finset.Subset.antisymm
          · intro r hr
            have hm := hNw_sub hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
            rcases hm with rfl | rfl | rfl | rfl
            · exact False.elim (h1 ((G.mem_neighborFinset w _).mp hr))
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with rfl | rfl | rfl <;> exact (G.mem_neighborFinset w _).mpr (by assumption)
        have hdw3' : G.degree w = 3 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hNw_eq,
              Finset.card_insert_of_notMem (by simp [heu2_v1, heu2_v2]),
              Finset.card_pair Sv.he12]
        refine ⟨[ψ_u Su.e₂], Or.inl rfl,
          by simp only [List.length_cons, List.length_nil]; omega, fun ψ _ he2 huniq => ?_⟩
        refine pcf_at_of_hasUniqueColor_three h2 hwe1v hwe2v (fun z hz => ?_)
          (by rw [he2]; exact huniq)
        have : z ∈ ({Su.e₂, Sv.e₁, Sv.e₂} : Finset V) := by
          rw [← hNw_eq]; exact (G.mem_neighborFinset w z).mpr hz
        simpa using this
      · exfalso
        have hsub2 : G.neighborFinset w ⊆ {Sv.e₁, Sv.e₂} := by
          intro r hr; have hm := hNw_sub hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
          rcases hm with rfl | rfl | rfl | rfl
          · exact False.elim (h1 ((G.mem_neighborFinset w _).mp hr))
          · exact False.elim (h2 ((G.mem_neighborFinset w _).mp hr))
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hle := Finset.card_le_card hsub2
        rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pair Sv.he12] at hle
        omega
  rcases hBw_build with ⟨B_w, hB12, hBlen, hBw_pcf⟩
  rcases Sv.hisoDouble w (adm.φ w) γ ca₁ ca₂ B_w hp1v hp2v hca1 hca2 hca12 hB12 hBlen with
    ⟨ca, hca_or, ψ_v, hψv_ne_γ, hψv_ne_ca, hψv_L, hψv_prop, hψv_e1w, hψv_e2w, hBw_uniq, hψv_pcf⟩
  have hca_mem : ca ∈ L a \ {γ} := by rcases hca_or with rfl | rfl <;> assumption
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hca_mem
  let ψ : V → ℕ := fun z =>
    if z = a then ca else if z ∈ Su.S_side then ψ_u z else if z ∈ Sv.S_side then ψ_v z else adm.φ z
  have hψa : ψ a = ca := by simp [ψ]
  have hψU : ∀ x ∈ Su.S_side, ψ x = ψ_u x := fun x hx => by
    have hne : x ≠ a := fun h => Su.ha_not (h ▸ hx)
    simp [ψ, hne, hx]
  have hψV : ∀ x ∈ Sv.S_side, ψ x = ψ_v x := fun x hx => by
    have hne : x ≠ a := fun h => Sv.ha_not (h ▸ hx)
    have hnotU : x ∉ Su.S_side := fun h => Finset.disjoint_left.mp hdisj h hx
    simp [ψ, hne, hnotU, hx]
  have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [Finset.mem_insert, Finset.mem_union] at hz
    rcases hz with rfl | hzU | hzV
    · rw [hψa]; exact hca_mem.1
    · rw [hψU z hzU]; exact hψu_L z hzU
    · rw [hψV z hzV]; exact hψv_L z hzV
  · intro z₁ z₂ h12' hor
    have hcase : ∀ r s, G.Adj r s → r ∈ S → ψ r ≠ ψ s := by
      intro r s hrs hrS
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | hrU | hrV
      · rcases ha_all s hrs with hs | hs
        · rw [hs, hψa, hψU u Su.huS, hψu_u]; exact hca_mem.2
        · rw [hs, hψa, hψV v Sv.huS]; exact hψv_ne_ca.symm
      · by_cases hsU : s ∈ Su.S_side
        · rw [hψU r hrU, hψU s hsU]; exact hψu_prop r hrU s hsU hrs
        · rcases Su.hout s hsU r hrU hrs.symm with ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩
          · rw [hr_eq, hs_eq, hψU u Su.huS, hψu_u, hψa]; exact Ne.symm hca_mem.2
          · rw [hr_eq, hs_eq, hψU Su.e₁ Su.he1S, hψ_out Su.p₁ hp1uS]; exact hψu_e1p
          · rw [hr_eq, hs_eq, hψU Su.e₂ Su.he2S, hψ_out Su.p₂ hp2uS]; exact hψu_e2p
      · by_cases hsV : s ∈ Sv.S_side
        · rw [hψV r hrV, hψV s hsV]; exact hψv_prop r hrV s hsV hrs
        · rcases Sv.hout s hsV r hrV hrs.symm with ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩
          · rw [hr_eq, hs_eq, hψV v Sv.huS, hψa]; exact hψv_ne_ca
          · rw [hr_eq, hs_eq, hψV Sv.e₁ Sv.he1S, hp1v, hψ_out w hwS]; exact hψv_e1w
          · rw [hr_eq, hs_eq, hψV Sv.e₂ Sv.he2S, hp2v, hψ_out w hwS]; exact hψv_e2w
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12' h1
    · exact (hcase z₂ z₁ h12'.symm h2).symm
  · intro z hzS hnon s hsS hzs
    rcases hS_out z hzS s hsS hzs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψU Su.e₁ Su.he1S]; exact hψu_e1ps
    · rw [hψU Su.e₂ Su.he2S]; exact hψu_e2ps
    · exfalso; rcases hnon with ⟨r, hrS, hzr⟩; exact hw_iso r hrS (hp1v ▸ hzr)
    · exfalso; rcases hnon with ⟨r, hrS, hzr⟩; exact hw_iso r hrS (hp2v ▸ hzr)
  · intro w' hw'S hw'_iso hw'_ex
    have hw'_eq : w' = w := hw_uniq w' hw'S hw'_iso hw'_ex
    subst hw'_eq
    exact hBw_pcf ψ (hψU Su.e₁ Su.he1S) (hψU Su.e₂ Su.he2S)
      (by rw [hψV Sv.e₁ Sv.he1S, hψV Sv.e₂ Sv.he2S]; exact hBw_uniq)
  · intro z hzS _
    simp only [Finset.mem_insert, Finset.mem_union] at hzS
    rcases hzS with rfl | hzU | hzV
    · exact pcf_at_of_two_distinct_neighbors hda hua.symm hav huv
        (by rw [hψU u Su.huS, hψu_u, hψV v Sv.huS]; exact hψv_ne_γ.symm)
    · exact hψu_pcf ca hca_or ψ hψU hψa (hψ_out Su.p₁ hp1uS) (hψ_out Su.p₂ hp2uS) z hzU
    · exact hψv_pcf ψ hψV hψa (hψ_out w hwS) z hzV

/-- 统一主组合引理：若强端元 `u ∈ {B3, T21, L4}` 通过 `1`-线串连接任意 `IsPoor1Ext` 顶点 `v`，则矛盾。 -/
private lemma no_strong_one_thread_Poor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v a : V}
    (hu : IsPoor1Ext G u) (hv : IsPoor1Ext G v) (huv : u ≠ v)
    (ha : a ∈ oneThreadNbrs G u) (hav : G.Adj a v)
    (Su : SideData G L u a) (hSu_strong : Su.IsStrong) : False := by
  classical
  have hdu3 : 3 ≤ G.degree u := deg_ge_three_of_isPoor1Ext hm hu
  have hua : G.Adj u a := (mem_oneThreadNbrs.mp ha).1
  have hda : G.degree a = 2 := (mem_oneThreadNbrs.mp ha).2.1
  have hv_a : a ∈ oneThreadNbrs G v :=
    mem_oneThreadNbrs.mpr ⟨hav.symm, hda, u, hua.symm, huv, hdu3⟩
  rcases sideData_of_isPoor1Ext hm hpq hv hv_a with ⟨Sv⟩
  rcases sideData_disjoint_and_ext hm hpq hu hv huv ha hav Su Sv with
    ⟨hdisj, hp1u_not_Sv, hp2u_not_Sv, hp1v_not_Su, hp2v_not_Su⟩
  let S : Finset V := insert a (Su.S_side ∪ Sv.S_side)
  have ha_all : ∀ r, G.Adj a r → r = u ∨ r = v := by
    intro r hr; have hN := neighborFinset_eq_pair_of_deg_two hda hua.symm hav huv
    have : r ∈ ({u, v} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a r).mpr hr
    simpa using this
  have hS_out : ∀ z, z ∉ S → ∀ s ∈ S, G.Adj z s →
      (s = Su.e₁ ∧ z = Su.p₁) ∨ (s = Su.e₂ ∧ z = Su.p₂) ∨
      (s = Sv.e₁ ∧ z = Sv.p₁) ∨ (s = Sv.e₂ ∧ z = Sv.p₂) := by
    intro z hzS s hsS hzs
    have hzU : z ∉ Su.S_side := fun h => hzS (by simp [S, h])
    have hzV : z ∉ Sv.S_side := fun h => hzS (by simp [S, h])
    have hza : z ≠ a := fun h => hzS (by simp [S, h])
    simp only [S, Finset.mem_insert, Finset.mem_union] at hsS
    rcases hsS with rfl | hsU | hsV
    · rcases ha_all z hzs.symm with rfl | rfl
      · exact False.elim (hzU Su.huS)
      · exact False.elim (hzV Sv.huS)
    · rcases Su.hout z hzU s hsU hzs with ⟨_, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hza h)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases Sv.hout z hzV s hsV hzs with ⟨_, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hza h)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  rcases exists_admissible_coloring hm (S := S) ⟨a, by simp [S]⟩ with ⟨adm⟩
  by_cases hiso : ∃ w, w ∉ S ∧ (∀ r, r ∉ S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)
  · rcases hiso with ⟨w, hwS, hw_iso, ⟨s₀, hws₀⟩⟩
    have hs₀S : s₀ ∈ S := by by_contra h; exact hw_iso s₀ h hws₀
    have hdw3 : 3 ≤ G.degree w := by
      rcases hS_out w hwS s₀ hs₀S hws₀ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Su.hdp1
      · exact Su.hdp2
      · exact Sv.hdp1
      · exact Sv.hdp2
    have hNw_sub : ∀ z, z ∉ S → (∀ r, r ∉ S → ¬ G.Adj z r) →
        G.neighborFinset z ⊆ {Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} := by
      intro z hzS hz_iso r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ S := by by_contra h; exact hz_iso r h hr
      rcases hS_out z hzS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hw_uniq : ∀ w', w' ∉ S → (∀ r, r ∉ S → ¬ G.Adj w' r) → (∃ s, G.Adj w' s) → w' = w := by
      intro w' hw'S hw'_iso ⟨s', hw's'⟩
      by_contra hne
      have hs'S : s' ∈ S := by by_contra h; exact hw'_iso s' h hw's'
      have hdw'3 : 3 ≤ G.degree w' := by
        rcases hS_out w' hw'S s' hs'S hw's' with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact Su.hdp1
        · exact Su.hdp2
        · exact Sv.hdp1
        · exact Sv.hdp2
      have hdisj_N : Disjoint (G.neighborFinset w) (G.neighborFinset w') := by
        rw [Finset.disjoint_left]; intro r hr1 hr2
        rw [SimpleGraph.mem_neighborFinset] at hr1 hr2
        have hrS : r ∈ S := by by_contra h; exact hw_iso r h hr1
        rcases hS_out w hwS r hrS hr1 with ⟨he1, h1⟩ | ⟨he1, h1⟩ | ⟨he1, h1⟩ | ⟨he1, h1⟩ <;>
        rcases hS_out w' hw'S r hrS hr2 with ⟨he2, h2⟩ | ⟨he2, h2⟩ | ⟨he2, h2⟩ | ⟨he2, h2⟩
        · exact hne (h2.trans h1.symm)
        · exact Su.he12 (he1.symm.trans he2)
        · exact Finset.disjoint_left.mp hdisj Su.he1S ((he1.symm.trans he2) ▸ Sv.he1S)
        · exact Finset.disjoint_left.mp hdisj Su.he1S ((he1.symm.trans he2) ▸ Sv.he2S)
        · exact Su.he12 (he2.symm.trans he1)
        · exact hne (h2.trans h1.symm)
        · exact Finset.disjoint_left.mp hdisj Su.he2S ((he1.symm.trans he2) ▸ Sv.he1S)
        · exact Finset.disjoint_left.mp hdisj Su.he2S ((he1.symm.trans he2) ▸ Sv.he2S)
        · exact Finset.disjoint_left.mp hdisj ((he2.symm.trans he1) ▸ Su.he1S) Sv.he1S
        · exact Finset.disjoint_left.mp hdisj ((he2.symm.trans he1) ▸ Su.he2S) Sv.he1S
        · exact hne (h2.trans h1.symm)
        · exact Sv.he12 (he1.symm.trans he2)
        · exact Finset.disjoint_left.mp hdisj ((he2.symm.trans he1) ▸ Su.he1S) Sv.he2S
        · exact Finset.disjoint_left.mp hdisj ((he2.symm.trans he1) ▸ Su.he2S) Sv.he2S
        · exact Sv.he12 (he2.symm.trans he1)
        · exact hne (h2.trans h1.symm)
      have hU_sub : G.neighborFinset w ∪ G.neighborFinset w' ⊆ {Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} :=
        Finset.union_subset (hNw_sub w hwS hw_iso) (hNw_sub w' hw'S hw'_iso)
      have hle := Finset.card_le_card hU_sub
      rw [Finset.card_union_of_disjoint hdisj_N, SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree] at hle
      have h4 : ({Su.e₁, Su.e₂, Sv.e₁, Sv.e₂} : Finset V).card ≤ 4 :=
        le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
          (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
            (Finset.card_le_two (a := Sv.e₁) (b := Sv.e₂)) 1)) 1)
      omega
    by_cases hvboth : G.Adj w Sv.e₁ ∧ G.Adj w Sv.e₂
    · exact one_thread_iso_contradiction hm huv hua hav hda Su Sv hdisj hp1u_not_Sv hp2u_not_Sv
        adm w hwS hw_iso hvboth.1 hvboth.2 hS_out hw_uniq
    · have huboth : G.Adj w Su.e₁ ∧ G.Adj w Su.e₂ := by
        by_contra hnot
        have h1 : (G.neighborFinset w ∩ {Su.e₁, Su.e₂}).card ≤ 1 := by
          by_cases ha1 : G.Adj w Su.e₁
          · have ha2 : ¬ G.Adj w Su.e₂ := fun h => hnot ⟨ha1, h⟩
            have hsub : G.neighborFinset w ∩ {Su.e₁, Su.e₂} ⊆ {Su.e₁} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · rfl
              · exact False.elim (ha2 hr.1)
            exact le_trans (Finset.card_le_card hsub) (by simp)
          · have hsub : G.neighborFinset w ∩ {Su.e₁, Su.e₂} ⊆ {Su.e₂} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · exact False.elim (ha1 hr.1)
              · rfl
            exact le_trans (Finset.card_le_card hsub) (by simp)
        have h2 : (G.neighborFinset w ∩ {Sv.e₁, Sv.e₂}).card ≤ 1 := by
          by_cases ha1 : G.Adj w Sv.e₁
          · have ha2 : ¬ G.Adj w Sv.e₂ := fun h => hvboth ⟨ha1, h⟩
            have hsub : G.neighborFinset w ∩ {Sv.e₁, Sv.e₂} ⊆ {Sv.e₁} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · rfl
              · exact False.elim (ha2 hr.1)
            exact le_trans (Finset.card_le_card hsub) (by simp)
          · have hsub : G.neighborFinset w ∩ {Sv.e₁, Sv.e₂} ⊆ {Sv.e₂} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · exact False.elim (ha1 hr.1)
              · rfl
            exact le_trans (Finset.card_le_card hsub) (by simp)
        have hcov : G.neighborFinset w ⊆
            (G.neighborFinset w ∩ {Su.e₁, Su.e₂}) ∪ (G.neighborFinset w ∩ {Sv.e₁, Sv.e₂}) := by
          intro r hr; have hm := hNw_sub w hwS hw_iso hr
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            at hm ⊢
          rcases hm with rfl | rfl | rfl | rfl
          · exact Or.inl ⟨hr, Or.inl rfl⟩
          · exact Or.inl ⟨hr, Or.inr rfl⟩
          · exact Or.inr ⟨hr, Or.inl rfl⟩
          · exact Or.inr ⟨hr, Or.inr rfl⟩
        have hle := le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
        omega
      have hSswap : insert a (Sv.S_side ∪ Su.S_side) = S := by
        dsimp only [S]; rw [Finset.union_comm]
      exact one_thread_iso_contradiction hm huv.symm hav.symm hua.symm hda Sv Su hdisj.symm
        hp1v_not_Su hp2v_not_Su (hSswap.symm ▸ adm) w (hSswap.symm ▸ hwS)
        (fun r hr => hw_iso r (hSswap ▸ hr)) huboth.1 huboth.2
        (fun z hz s hs hzs => by
          rcases hS_out z (hSswap ▸ hz) s (hSswap ▸ hs) hzs with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h))
        (fun w' hw' h1 h2 => hw_uniq w' (hSswap ▸ hw') (fun r hr => h1 r (hSswap.symm ▸ hr)) h2)
  · -- 无孤立外点情形：强端元 `Su`（`|C_u| ≥ 3`）与 `Sv.hgoodA`（单点 `≤ 2`）直接配对！
    have hp1uS : Su.p₁ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨ne_of_deg_ge_lt Su.hdp1 hda (by omega), Su.hp1_not, hp1u_not_Sv⟩
    have hp2uS : Su.p₂ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨ne_of_deg_ge_lt Su.hdp2 hda (by omega), Su.hp2_not, hp2u_not_Sv⟩
    have hp1vS : Sv.p₁ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨ne_of_deg_ge_lt Sv.hdp1 hda (by omega), hp1v_not_Su, Sv.hp1_not⟩
    have hp2vS : Sv.p₂ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨ne_of_deg_ge_lt Sv.hdp2 hda (by omega), hp2v_not_Su, Sv.hp2_not⟩
    rcases Sv.hgoodA adm.φ adm.φs with ⟨G_a, hGa_ne, hGa_sing, hGa_sub, hGa_ext⟩
    rcases hSu_strong adm.φ adm.φs with ⟨C_u, _, hCu3, hCu_ext⟩
    have hsing_le2 := hGa_sing C_u
    have hpick_γ : ∃ γ ∈ C_u, 2 ≤ (G_a γ).card := by
      have hcard_pos : 0 < (C_u \ C_u.filter (fun γ => (G_a γ).card = 1)).card := by
        have := card_sdiff_ge C_u (C_u.filter (fun γ => (G_a γ).card = 1)); omega
      rcases Finset.card_pos.mp hcard_pos with ⟨γ, hγ⟩
      rw [Finset.mem_sdiff, Finset.mem_filter] at hγ
      have hne1 : (G_a γ).card ≠ 1 := fun h => hγ.2 ⟨hγ.1, h⟩
      have hpos : 0 < (G_a γ).card := Finset.card_pos.mpr (hGa_ne γ)
      exact ⟨γ, hγ.1, by omega⟩
    rcases hpick_γ with ⟨γ, hγCu, hGa2⟩
    rcases hCu_ext γ hγCu (G_a γ) (hGa_sub γ) hGa2 with
      ⟨ca, hcaG, ψ_u, hψu_u, hψu_L, hψu_prop, hψu_e1p, hψu_e1ps, hψu_e2p, hψu_e2ps, hψu_pcf⟩
    rcases hGa_ext γ ca hcaG with
      ⟨ψ_v, hψv_ne_γ, hψv_ne_ca, hψv_L, hψv_prop, hψv_e1p, hψv_e1ps, hψv_e2p, hψv_e2ps, hψv_pcf⟩
    have hca_mem : ca ∈ L a \ {γ} := hGa_sub γ hcaG
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hca_mem
    let ψ : V → ℕ := fun z =>
      if z = a then ca else if z ∈ Su.S_side then ψ_u z else if z ∈ Sv.S_side then ψ_v z
      else adm.φ z
    have hψa : ψ a = ca := by simp [ψ]
    have hψU : ∀ x ∈ Su.S_side, ψ x = ψ_u x := fun x hx => by
      have hne : x ≠ a := fun h => Su.ha_not (h ▸ hx)
      simp [ψ, hne, hx]
    have hψV : ∀ x ∈ Sv.S_side, ψ x = ψ_v x := fun x hx => by
      have hne : x ≠ a := fun h => Sv.ha_not (h ▸ hx)
      have hnotU : x ∉ Su.S_side := fun h => Finset.disjoint_left.mp hdisj h hx
      simp [ψ, hne, hnotU, hx]
    have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := fun z hz => by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hz
      simp only [ψ, hz.1, hz.2.1, hz.2.2, ite_false]
    apply adm.contradiction hm ψ hψ_out
    · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_union] at hz
      rcases hz with rfl | hzU | hzV
      · rw [hψa]; exact hca_mem.1
      · rw [hψU z hzU]; exact hψu_L z hzU
      · rw [hψV z hzV]; exact hψv_L z hzV
    · intro z₁ z₂ h12' hor
      have hcase : ∀ r s, G.Adj r s → r ∈ S → ψ r ≠ ψ s := by
        intro r s hrs hrS
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with rfl | hrU | hrV
        · rcases ha_all s hrs with hs | hs
          · rw [hs, hψa, hψU u Su.huS, hψu_u]; exact hca_mem.2
          · rw [hs, hψa, hψV v Sv.huS]; exact hψv_ne_ca.symm
        · by_cases hsU : s ∈ Su.S_side
          · rw [hψU r hrU, hψU s hsU]; exact hψu_prop r hrU s hsU hrs
          · rcases Su.hout s hsU r hrU hrs.symm with
              ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩
            · rw [hr_eq, hs_eq, hψU u Su.huS, hψu_u, hψa]; exact Ne.symm hca_mem.2
            · rw [hr_eq, hs_eq, hψU Su.e₁ Su.he1S, hψ_out Su.p₁ hp1uS]; exact hψu_e1p
            · rw [hr_eq, hs_eq, hψU Su.e₂ Su.he2S, hψ_out Su.p₂ hp2uS]; exact hψu_e2p
        · by_cases hsV : s ∈ Sv.S_side
          · rw [hψV r hrV, hψV s hsV]; exact hψv_prop r hrV s hsV hrs
          · rcases Sv.hout s hsV r hrV hrs.symm with
              ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩ | ⟨hr_eq, hs_eq⟩
            · rw [hr_eq, hs_eq, hψV v Sv.huS, hψa]; exact hψv_ne_ca
            · rw [hr_eq, hs_eq, hψV Sv.e₁ Sv.he1S, hψ_out Sv.p₁ hp1vS]; exact hψv_e1p
            · rw [hr_eq, hs_eq, hψV Sv.e₂ Sv.he2S, hψ_out Sv.p₂ hp2vS]; exact hψv_e2p
      rcases hor with h1 | h2
      · exact hcase z₁ z₂ h12' h1
      · exact (hcase z₂ z₁ h12'.symm h2).symm
    · intro z hzS _ s hsS hzs
      rcases hS_out z hzS s hsS hzs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hψU Su.e₁ Su.he1S]; exact hψu_e1ps
      · rw [hψU Su.e₂ Su.he2S]; exact hψu_e2ps
      · rw [hψV Sv.e₁ Sv.he1S]; exact hψv_e1ps
      · rw [hψV Sv.e₂ Sv.he2S]; exact hψv_e2ps
    · intro w hwS hw_iso hw_ex
      exact False.elim (hiso ⟨w, hwS, hw_iso, hw_ex⟩)
    · intro z hzS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hzS
      rcases hzS with rfl | hzU | hzV
      · exact pcf_at_of_two_distinct_neighbors hda hua.symm hav huv
          (by rw [hψU u Su.huS, hψu_u, hψV v Sv.huS]; exact hψv_ne_γ.symm)
      · exact hψu_pcf ψ hψU hψa (hψ_out Su.p₁ hp1uS) (hψ_out Su.p₂ hp2uS) z hzU
      · exact hψv_pcf ψ hψV hψa (hψ_out Sv.p₁ hp1vS) (hψ_out Sv.p₂ hp2vS) z hzV

/-- 主引理 2：`B3` 顶点不能通过 `1`-线串连接任何 `IsPoor1Ext` 顶点。 -/
lemma no_B3_one_thread_Poor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v : V}
    (hu : IsB3 G u) (hv : IsPoor1Ext G v) (h1 : HasOneThreadBetween G u v) : False := by
  rcases h1 with ⟨a, hua, hda, hav, huv⟩
  have ha : a ∈ oneThreadNbrs G u :=
    mem_oneThreadNbrs.mpr ⟨hua, hda, v, hav, huv.symm, deg_ge_three_of_isPoor1Ext hm hv⟩
  rcases sideData_B3 hm hpq hu ha with ⟨Su, hSu⟩
  exact no_strong_one_thread_Poor1Ext hm hpq (Or.inr (Or.inl hu)) hv huv ha hav Su hSu

/-- 主引理 3：`T21` 顶点不能通过 `1`-线串连接任何 `IsPoor1Ext` 顶点。 -/
lemma no_T21_one_thread_Poor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v : V}
    (hu : IsT21 G u) (hv : IsPoor1Ext G v) (h1 : HasOneThreadBetween G u v) : False := by
  rcases h1 with ⟨a, hua, hda, hav, huv⟩
  have ha : a ∈ oneThreadNbrs G u :=
    mem_oneThreadNbrs.mpr ⟨hua, hda, v, hav, huv.symm, deg_ge_three_of_isPoor1Ext hm hv⟩
  rcases sideData_T21 hm hpq hu ha with ⟨Su, hSu⟩
  exact no_strong_one_thread_Poor1Ext hm hpq (Or.inr (Or.inr (Or.inl hu))) hv huv ha hav Su hSu

/-- 主引理 4：`L4` 顶点不能通过 `1`-线串连接任何 `IsPoor1Ext` 顶点。 -/
lemma no_L4_one_thread_Poor1Ext {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u v : V}
    (hu : IsL4 G u) (hv : IsPoor1Ext G v) (h1 : HasOneThreadBetween G u v) : False := by
  rcases h1 with ⟨a, hua, hda, hav, huv⟩
  have ha : a ∈ oneThreadNbrs G u :=
    mem_oneThreadNbrs.mpr ⟨hua, hda, v, hav, huv.symm, deg_ge_three_of_isPoor1Ext hm hv⟩
  rcases sideData_L4 hm hpq hu ha with ⟨Su, hSu⟩
  exact no_strong_one_thread_Poor1Ext hm hpq (Or.inr (Or.inr (Or.inr hu))) hv huv ha hav Su hSu

/-! ## 6. 引理 1（`L3_at_most_one_L3_nbr`） -/

/-- `L3` 顶点 `u` 通过 `1`-线串连接两个互异 `L3` 顶点 `v₁, v₂` 的 10-点构型数据。 -/
private structure L3TwoNbrData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v₁ : V
  v₂ : V
  a₁ : V
  a₂ : V
  a₃ : V
  b₁ : V
  b₂ : V
  d₁ : V
  d₂ : V
  p₀ : V
  q₁ : V
  q₂ : V
  r₁ : V
  r₂ : V
  hdu : G.degree u = 3
  hdv1 : G.degree v₁ = 3
  hdv2 : G.degree v₂ = 3
  hda1 : G.degree a₁ = 2
  hda2 : G.degree a₂ = 2
  hda3 : G.degree a₃ = 2
  hdb1 : G.degree b₁ = 2
  hdb2 : G.degree b₂ = 2
  hdd1 : G.degree d₁ = 2
  hdd2 : G.degree d₂ = 2
  hdp0 : 3 ≤ G.degree p₀
  hdq1 : 3 ≤ G.degree q₁
  hdq2 : 3 ≤ G.degree q₂
  hdr1 : 3 ≤ G.degree r₁
  hdr2 : 3 ≤ G.degree r₂
  huv1 : u ≠ v₁
  huv2 : u ≠ v₂
  hv12 : v₁ ≠ v₂
  ha12 : a₁ ≠ a₂
  ha13 : a₁ ≠ a₃
  ha23 : a₂ ≠ a₃
  hb12 : b₁ ≠ b₂
  hd12 : d₁ ≠ d₂
  ha1b1 : a₁ ≠ b₁
  ha1b2 : a₁ ≠ b₂
  ha1d1 : a₁ ≠ d₁
  ha1d2 : a₁ ≠ d₂
  ha2b1 : a₂ ≠ b₁
  ha2b2 : a₂ ≠ b₂
  ha2d1 : a₂ ≠ d₁
  ha2d2 : a₂ ≠ d₂
  ha3b1 : a₃ ≠ b₁
  ha3b2 : a₃ ≠ b₂
  ha3d1 : a₃ ≠ d₁
  ha3d2 : a₃ ≠ d₂
  hb1d1 : b₁ ≠ d₁
  hb1d2 : b₁ ≠ d₂
  hb2d1 : b₂ ≠ d₁
  hb2d2 : b₂ ≠ d₂
  hua1 : G.Adj u a₁
  hua2 : G.Adj u a₂
  hua3 : G.Adj u a₃
  ha1v1 : G.Adj a₁ v₁
  ha2v2 : G.Adj a₂ v₂
  ha3p0 : G.Adj a₃ p₀
  hv1b1 : G.Adj v₁ b₁
  hv1b2 : G.Adj v₁ b₂
  hb1q1 : G.Adj b₁ q₁
  hb2q2 : G.Adj b₂ q₂
  hv2d1 : G.Adj v₂ d₁
  hv2d2 : G.Adj v₂ d₂
  hd1r1 : G.Adj d₁ r₁
  hd2r2 : G.Adj d₂ r₂
  hu_all : ∀ z, G.Adj u z → z = a₁ ∨ z = a₂ ∨ z = a₃
  hv1_all : ∀ z, G.Adj v₁ z → z = a₁ ∨ z = b₁ ∨ z = b₂
  hv2_all : ∀ z, G.Adj v₂ z → z = a₂ ∨ z = d₁ ∨ z = d₂
  ha1_all : ∀ z, G.Adj a₁ z → z = u ∨ z = v₁
  ha2_all : ∀ z, G.Adj a₂ z → z = u ∨ z = v₂
  ha3_all : ∀ z, G.Adj a₃ z → z = u ∨ z = p₀
  hb1_all : ∀ z, G.Adj b₁ z → z = v₁ ∨ z = q₁
  hb2_all : ∀ z, G.Adj b₂ z → z = v₁ ∨ z = q₂
  hd1_all : ∀ z, G.Adj d₁ z → z = v₂ ∨ z = r₁
  hd2_all : ∀ z, G.Adj d₂ z → z = v₂ ∨ z = r₂
  hp0u : p₀ ≠ u
  hp0v1 : p₀ ≠ v₁
  hp0v2 : p₀ ≠ v₂
  hq1u : q₁ ≠ u
  hq1v1 : q₁ ≠ v₁
  hq1v2 : q₁ ≠ v₂
  hq2u : q₂ ≠ u
  hq2v1 : q₂ ≠ v₁
  hq2v2 : q₂ ≠ v₂
  hr1u : r₁ ≠ u
  hr1v1 : r₁ ≠ v₁
  hr1v2 : r₁ ≠ v₂
  hr2u : r₂ ≠ u
  hr2v1 : r₂ ≠ v₁
  hr2v2 : r₂ ≠ v₂

private def L3TwoNbrData.S {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : L3TwoNbrData G) : Finset V :=
  {D.u, D.v₁, D.v₂, D.a₁, D.a₂, D.a₃, D.b₁, D.b₂, D.d₁, D.d₂}

private def L3TwoNbrData.swap {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : L3TwoNbrData G) : L3TwoNbrData G where
  u := D.u; v₁ := D.v₂; v₂ := D.v₁; a₁ := D.a₂; a₂ := D.a₁; a₃ := D.a₃
  b₁ := D.d₁; b₂ := D.d₂; d₁ := D.b₁; d₂ := D.b₂
  p₀ := D.p₀; q₁ := D.r₁; q₂ := D.r₂; r₁ := D.q₁; r₂ := D.q₂
  hdu := D.hdu; hdv1 := D.hdv2; hdv2 := D.hdv1
  hda1 := D.hda2; hda2 := D.hda1; hda3 := D.hda3
  hdb1 := D.hdd1; hdb2 := D.hdd2; hdd1 := D.hdb1; hdd2 := D.hdb2
  hdp0 := D.hdp0; hdq1 := D.hdr1; hdq2 := D.hdr2; hdr1 := D.hdq1; hdr2 := D.hdq2
  huv1 := D.huv2; huv2 := D.huv1; hv12 := D.hv12.symm
  ha12 := D.ha12.symm; ha13 := D.ha23; ha23 := D.ha13
  hb12 := D.hd12; hd12 := D.hb12
  ha1b1 := D.ha2d1; ha1b2 := D.ha2d2; ha1d1 := D.ha2b1; ha1d2 := D.ha2b2
  ha2b1 := D.ha1d1; ha2b2 := D.ha1d2; ha2d1 := D.ha1b1; ha2d2 := D.ha1b2
  ha3b1 := D.ha3d1; ha3b2 := D.ha3d2; ha3d1 := D.ha3b1; ha3d2 := D.ha3b2
  hb1d1 := D.hb1d1.symm; hb1d2 := D.hb2d1.symm; hb2d1 := D.hb1d2.symm; hb2d2 := D.hb2d2.symm
  hua1 := D.hua2; hua2 := D.hua1; hua3 := D.hua3
  ha1v1 := D.ha2v2; ha2v2 := D.ha1v1; ha3p0 := D.ha3p0
  hv1b1 := D.hv2d1; hv1b2 := D.hv2d2; hb1q1 := D.hd1r1; hb2q2 := D.hd2r2
  hv2d1 := D.hv1b1; hv2d2 := D.hv1b2; hd1r1 := D.hb1q1; hd2r2 := D.hb2q2
  hu_all := fun z hz => by
    rcases D.hu_all z hz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  hv1_all := D.hv2_all; hv2_all := D.hv1_all
  ha1_all := D.ha2_all; ha2_all := D.ha1_all; ha3_all := D.ha3_all
  hb1_all := D.hd1_all; hb2_all := D.hd2_all; hd1_all := D.hb1_all; hd2_all := D.hb2_all
  hp0u := D.hp0u; hp0v1 := D.hp0v2; hp0v2 := D.hp0v1
  hq1u := D.hr1u; hq1v1 := D.hr1v2; hq1v2 := D.hr1v1
  hq2u := D.hr2u; hq2v1 := D.hr2v2; hq2v2 := D.hr2v1
  hr1u := D.hq1u; hr1v1 := D.hq1v2; hr1v2 := D.hq1v1
  hr2u := D.hq2u; hr2v1 := D.hq2v2; hr2v2 := D.hq2v1

private lemma L3TwoNbrData.S_swap {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : L3TwoNbrData G) :
    D.swap.S = D.S := by
  ext z; simp only [L3TwoNbrData.S, L3TwoNbrData.swap, Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma L3TwoNbrData.ext_not_S {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : L3TwoNbrData G) :
    D.p₀ ∉ D.S ∧ D.q₁ ∉ D.S ∧ D.q₂ ∉ D.S ∧ D.r₁ ∉ D.S ∧ D.r₂ ∉ D.S := by
  have hcheck : ∀ x, 3 ≤ G.degree x → x ≠ D.u → x ≠ D.v₁ → x ≠ D.v₂ → x ∉ D.S := by
    intro x hdx h1 h2 h3
    simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, h2, h3, ne_of_deg_ge_lt hdx D.hda1 (by omega),
      ne_of_deg_ge_lt hdx D.hda2 (by omega), ne_of_deg_ge_lt hdx D.hda3 (by omega),
      ne_of_deg_ge_lt hdx D.hdb1 (by omega), ne_of_deg_ge_lt hdx D.hdb2 (by omega),
      ne_of_deg_ge_lt hdx D.hdd1 (by omega), ne_of_deg_ge_lt hdx D.hdd2 (by omega)⟩
  exact ⟨hcheck D.p₀ D.hdp0 D.hp0u D.hp0v1 D.hp0v2,
    hcheck D.q₁ D.hdq1 D.hq1u D.hq1v1 D.hq1v2,
    hcheck D.q₂ D.hdq2 D.hq2u D.hq2v1 D.hq2v2,
    hcheck D.r₁ D.hdr1 D.hr1u D.hr1v1 D.hr1v2,
    hcheck D.r₂ D.hdr2 D.hr2u D.hr2v1 D.hr2v2⟩

private lemma L3TwoNbrData.S_out {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : L3TwoNbrData G) :
    ∀ w, w ∉ D.S → ∀ s ∈ D.S, G.Adj w s →
      (s = D.a₃ ∧ w = D.p₀) ∨ (s = D.b₁ ∧ w = D.q₁) ∨ (s = D.b₂ ∧ w = D.q₂) ∨
      (s = D.d₁ ∧ w = D.r₁) ∨ (s = D.d₂ ∧ w = D.r₂) := by
  intro w hwS s hsS hws
  simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hsS
  rcases hsS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases D.hu_all w hws.symm with rfl | rfl | rfl <;>
      exact False.elim (hwS (by simp [L3TwoNbrData.S]))
  · rcases D.hv1_all w hws.symm with rfl | rfl | rfl <;>
      exact False.elim (hwS (by simp [L3TwoNbrData.S]))
  · rcases D.hv2_all w hws.symm with rfl | rfl | rfl <;>
      exact False.elim (hwS (by simp [L3TwoNbrData.S]))
  · rcases D.ha1_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [L3TwoNbrData.S]))
  · rcases D.ha2_all w hws.symm with rfl | rfl <;> exact False.elim (hwS (by simp [L3TwoNbrData.S]))
  · rcases D.ha3_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp [L3TwoNbrData.S]))
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases D.hb1_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp [L3TwoNbrData.S]))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases D.hb2_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp [L3TwoNbrData.S]))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rcases D.hd1_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp [L3TwoNbrData.S]))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rcases D.hd2_all w hws.symm with rfl | rfl
    · exact False.elim (hwS (by simp [L3TwoNbrData.S]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- `L3TwoNbrData` 无孤立外点情形：利用 `pair_goodA_props` 直接完成 10-点延拓。 -/
private lemma L3_two_nbr_noniso {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : L3TwoNbrData G)
    (adm : AdmissibleColoring G L D.S)
    (hnoiso : ¬ ∃ w, w ∉ D.S ∧ (∀ r, r ∉ D.S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)) : False := by
  classical
  rcases D.ext_not_S with ⟨hp0S, hq1S, hq2S, hr1S, hr2S⟩
  have hLu4 : (L D.u).card = 4 := by rw [hm.list_card D.u]; simp [kappa, D.hdu]
  have hLv1 : (L D.v₁).card = 4 := by rw [hm.list_card D.v₁]; simp [kappa, D.hdv1]
  have hLv2 : (L D.v₂).card = 4 := by rw [hm.list_card D.v₂]; simp [kappa, D.hdv2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  have hLa2 : (L D.a₂).card = 4 := by rw [hm.list_card D.a₂]; simp [kappa, D.hda2]
  have hLa3 : (L D.a₃).card = 4 := by rw [hm.list_card D.a₃]; simp [kappa, D.hda3]
  have hLb1 : (L D.b₁).card = 4 := by rw [hm.list_card D.b₁]; simp [kappa, D.hdb1]
  have hLb2 : (L D.b₂).card = 4 := by rw [hm.list_card D.b₂]; simp [kappa, D.hdb2]
  have hLd1 : (L D.d₁).card = 4 := by rw [hm.list_card D.d₁]; simp [kappa, D.hdd1]
  have hLd2 : (L D.d₂).card = 4 := by rw [hm.list_card D.d₂]; simp [kappa, D.hdd2]
  let C₁ : Finset ℕ := L D.v₁ \ {adm.φ D.q₁, adm.φ D.q₂}
  let B₁ : Finset ℕ := L D.b₁ \ {adm.φ D.q₁, adm.φs D.q₁}
  let B₂ : Finset ℕ := L D.b₂ \ {adm.φ D.q₂, adm.φs D.q₂}
  let C₂ : Finset ℕ := L D.v₂ \ {adm.φ D.r₁, adm.φ D.r₂}
  let D₁ : Finset ℕ := L D.d₁ \ {adm.φ D.r₁, adm.φs D.r₁}
  let D₂ : Finset ℕ := L D.d₂ \ {adm.φ D.r₂, adm.φs D.r₂}
  have hC1 : 2 ≤ C₁.card := by
    dsimp only [C₁]; have := card_sdiff_ge (L D.v₁) {adm.φ D.q₁, adm.φ D.q₂}
    have := Finset.card_le_two (a := adm.φ D.q₁) (b := adm.φ D.q₂); omega
  have hB1 : 2 ≤ B₁.card := by
    dsimp only [B₁]; have := card_sdiff_ge (L D.b₁) {adm.φ D.q₁, adm.φs D.q₁}
    have := Finset.card_le_two (a := adm.φ D.q₁) (b := adm.φs D.q₁); omega
  have hB2 : 2 ≤ B₂.card := by
    dsimp only [B₂]; have := card_sdiff_ge (L D.b₂) {adm.φ D.q₂, adm.φs D.q₂}
    have := Finset.card_le_two (a := adm.φ D.q₂) (b := adm.φs D.q₂); omega
  have hC2 : 2 ≤ C₂.card := by
    dsimp only [C₂]; have := card_sdiff_ge (L D.v₂) {adm.φ D.r₁, adm.φ D.r₂}
    have := Finset.card_le_two (a := adm.φ D.r₁) (b := adm.φ D.r₂); omega
  have hD1 : 2 ≤ D₁.card := by
    dsimp only [D₁]; have := card_sdiff_ge (L D.d₁) {adm.φ D.r₁, adm.φs D.r₁}
    have := Finset.card_le_two (a := adm.φ D.r₁) (b := adm.φs D.r₁); omega
  have hD2 : 2 ≤ D₂.card := by
    dsimp only [D₂]; have := card_sdiff_ge (L D.d₂) {adm.φ D.r₂, adm.φs D.r₂}
    have := Finset.card_le_two (a := adm.φ D.r₂) (b := adm.φs D.r₂); omega
  rcases pair_goodA_props hC1 hB1 hB2 hLa1 with ⟨hG1_ne, hG1_sing⟩
  rcases pair_goodA_props hC2 hD1 hD2 hLa2 with ⟨hG2_ne, _⟩
  let Cu : Finset ℕ := L D.u \ {adm.φ D.p₀}
  have hCu3 : 3 ≤ Cu.card := by
    dsimp only [Cu]; have := card_sdiff_ge (L D.u) {adm.φ D.p₀}
    simp only [Finset.card_singleton] at this; omega
  have hsing := hG1_sing Cu
  have hpick_γ : ∃ γ ∈ Cu, 2 ≤ (pairGoodA C₁ B₁ B₂ (L D.a₁) γ).card := by
    have hpos : 0 < (Cu \ Cu.filter (fun γ => (pairGoodA C₁ B₁ B₂ (L D.a₁) γ).card = 1)).card := by
      have := card_sdiff_ge Cu (Cu.filter (fun γ => (pairGoodA C₁ B₁ B₂ (L D.a₁) γ).card = 1))
      omega
    rcases Finset.card_pos.mp hpos with ⟨γ, hγ⟩
    rw [Finset.mem_sdiff, Finset.mem_filter] at hγ
    have hne1 : (pairGoodA C₁ B₁ B₂ (L D.a₁) γ).card ≠ 1 := fun h => hγ.2 ⟨hγ.1, h⟩
    have hgt0 : 0 < (pairGoodA C₁ B₁ B₂ (L D.a₁) γ).card := Finset.card_pos.mpr (hG1_ne γ)
    exact ⟨γ, hγ.1, by omega⟩
  rcases hpick_γ with ⟨γ, hγCu, hG1_2⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hγCu
  rcases hG2_ne γ with ⟨c₂, hc2G⟩
  rcases exists_mem_sdiff_of_lt (A := pairGoodA C₁ B₁ B₂ (L D.a₁) γ) (B := {c₂})
    (by simp only [Finset.card_singleton]; omega) with ⟨c₁, hc1G, hc12⟩
  rw [Finset.mem_singleton] at hc12
  rcases exists_mem_sdiff_of_lt (A := L D.a₃) (B := {adm.φ D.p₀, adm.φs D.p₀, γ})
    (by have := card_triple_le (adm.φ D.p₀) (adm.φs D.p₀) γ; omega) with ⟨c₃, hc3L, hc3N⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
  simp only [pairGoodA, Finset.mem_filter] at hc1G hc2G
  rcases hc1G with ⟨hc1L, α₁, hα1, hα1c1, cb₁, hcb1, cb₂, hcb2, hnot_v1⟩
  rcases hc2G with ⟨hc2L, α₂, hα2, hα2c2, cd₁, hcd1, cd₂, hcd2, hnot_v2⟩
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hc1L hc2L
  simp only [C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1
  simp only [B₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb1
  simp only [B₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb2
  simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2
  simp only [D₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcd1
  simp only [D₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcd2
  let ψ : V → ℕ := fun z =>
    if z = D.u then γ else if z = D.v₁ then α₁ else if z = D.v₂ then α₂
    else if z = D.a₁ then c₁ else if z = D.a₂ then c₂ else if z = D.a₃ then c₃
    else if z = D.b₁ then cb₁ else if z = D.b₂ then cb₂
    else if z = D.d₁ then cd₁ else if z = D.d₂ then cd₂ else adm.φ z
  have hψu : ψ D.u = γ := by simp [ψ]
  have hψv1 : ψ D.v₁ = α₁ := by simp [ψ, D.huv1.symm]
  have hψv2 : ψ D.v₂ = α₂ := by simp [ψ, D.huv2.symm, D.hv12.symm]
  have hψa1 : ψ D.a₁ = c₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hda1 D.hdu (by omega), ne_of_deg_eq_ne D.hda1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda1 D.hdv2 (by omega)]
  have hψa2 : ψ D.a₂ = c₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hda2 D.hdu (by omega), ne_of_deg_eq_ne D.hda2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda2 D.hdv2 (by omega), D.ha12.symm]
  have hψa3 : ψ D.a₃ = c₃ := by
    simp [ψ, ne_of_deg_eq_ne D.hda3 D.hdu (by omega), ne_of_deg_eq_ne D.hda3 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda3 D.hdv2 (by omega), D.ha13.symm, D.ha23.symm]
  have hψb1 : ψ D.b₁ = cb₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hdb1 D.hdu (by omega), ne_of_deg_eq_ne D.hdb1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdb1 D.hdv2 (by omega), D.ha1b1.symm, D.ha2b1.symm, D.ha3b1.symm]
  have hψb2 : ψ D.b₂ = cb₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hdb2 D.hdu (by omega), ne_of_deg_eq_ne D.hdb2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdb2 D.hdv2 (by omega), D.ha1b2.symm, D.ha2b2.symm, D.ha3b2.symm,
      D.hb12.symm]
  have hψd1 : ψ D.d₁ = cd₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hdd1 D.hdu (by omega), ne_of_deg_eq_ne D.hdd1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdd1 D.hdv2 (by omega), D.ha1d1.symm, D.ha2d1.symm, D.ha3d1.symm,
      D.hb1d1.symm, D.hb2d1.symm]
  have hψd2 : ψ D.d₂ = cd₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hdd2 D.hdu (by omega), ne_of_deg_eq_ne D.hdd2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdd2 D.hdv2 (by omega), D.ha1d2.symm, D.ha2d2.symm, D.ha3d2.symm,
      D.hb1d2.symm, D.hb2d2.symm, D.hd12.symm]
  have hψ_out : ∀ z, z ∉ D.S → ψ z = adm.φ z := fun z hz => by
    simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hγCu.1
    · rw [hψv1]; exact hα1.1.1
    · rw [hψv2]; exact hα2.1.1
    · rw [hψa1]; exact hc1L.1
    · rw [hψa2]; exact hc2L.1
    · rw [hψa3]; exact hc3L
    · rw [hψb1]; exact hcb1.1.1
    · rw [hψb2]; exact hcb2.1.1
    · rw [hψd1]; exact hcd1.1.1
    · rw [hψd2]; exact hcd2.1.1
  · intro z₁ z₂ h12' hor
    have hcase : ∀ p r, G.Adj p r → p ∈ D.S → ψ p ≠ ψ r := by
      intro p r hpr hpS
      simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all r hpr with hr | hr | hr
        · rw [hr, hψu, hψa1]; exact Ne.symm hc1L.2
        · rw [hr, hψu, hψa2]; exact Ne.symm hc2L.2
        · rw [hr, hψu, hψa3]; exact Ne.symm hc3N.2.2
      · rcases D.hv1_all r hpr with hr | hr | hr
        · rw [hr, hψv1, hψa1]; exact hα1c1
        · rw [hr, hψv1, hψb1]; exact Ne.symm hcb1.2
        · rw [hr, hψv1, hψb2]; exact Ne.symm hcb2.2
      · rcases D.hv2_all r hpr with hr | hr | hr
        · rw [hr, hψv2, hψa2]; exact hα2c2
        · rw [hr, hψv2, hψd1]; exact Ne.symm hcd1.2
        · rw [hr, hψv2, hψd2]; exact Ne.symm hcd2.2
      · rcases D.ha1_all r hpr with hr | hr
        · rw [hr, hψa1, hψu]; exact hc1L.2
        · rw [hr, hψa1, hψv1]; exact hα1c1.symm
      · rcases D.ha2_all r hpr with hr | hr
        · rw [hr, hψa2, hψu]; exact hc2L.2
        · rw [hr, hψa2, hψv2]; exact hα2c2.symm
      · rcases D.ha3_all r hpr with hr | hr
        · rw [hr, hψa3, hψu]; exact hc3N.2.2
        · rw [hr, hψa3, hψ_out D.p₀ hp0S]; exact hc3N.1
      · rcases D.hb1_all r hpr with hr | hr
        · rw [hr, hψb1, hψv1]; exact hcb1.2
        · rw [hr, hψb1, hψ_out D.q₁ hq1S]; exact hcb1.1.2.1
      · rcases D.hb2_all r hpr with hr | hr
        · rw [hr, hψb2, hψv1]; exact hcb2.2
        · rw [hr, hψb2, hψ_out D.q₂ hq2S]; exact hcb2.1.2.1
      · rcases D.hd1_all r hpr with hr | hr
        · rw [hr, hψd1, hψv2]; exact hcd1.2
        · rw [hr, hψd1, hψ_out D.r₁ hr1S]; exact hcd1.1.2.1
      · rcases D.hd2_all r hpr with hr | hr
        · rw [hr, hψd2, hψv2]; exact hcd2.2
        · rw [hr, hψd2, hψ_out D.r₂ hr2S]; exact hcd2.1.2.1
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12' h1
    · exact (hcase z₂ z₁ h12'.symm h2).symm
  · intro w hwS _ s hsS hws
    rcases D.S_out w hwS s hsS hws with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψa3]; exact hc3N.2.1
    · rw [hψb1]; exact hcb1.1.2.2
    · rw [hψb2]; exact hcb2.1.2.2
    · rw [hψd1]; exact hcd1.1.2.2
    · rw [hψd2]; exact hcd2.1.2.2
  · intro w hwS hw_iso hw_ex
    exact False.elim (hnoiso ⟨w, hwS, hw_iso, hw_ex⟩)
  · intro z hzS _
    simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_deg_three_of_two_distinct D.hdu D.hua1 D.hua2 D.ha12
        (by rw [hψa1, hψa2]; exact hc12)
    · exact pcf_at_of_hasUniqueColor_three D.ha1v1.symm D.hv1b1 D.hv1b2 D.hv1_all
        (by rw [hψa1, hψb1, hψb2, hasUniqueColor_triple_iff]; exact hnot_v1)
    · exact pcf_at_of_hasUniqueColor_three D.ha2v2.symm D.hv2d1 D.hv2d2 D.hv2_all
        (by rw [hψa2, hψd1, hψd2, hasUniqueColor_triple_iff]; exact hnot_v2)
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1v1 D.huv1
        (by rw [hψu, hψv1]; exact Ne.symm hα1.2)
    · exact pcf_at_of_two_distinct_neighbors D.hda2 D.hua2.symm D.ha2v2 D.huv2
        (by rw [hψu, hψv2]; exact Ne.symm hα2.2)
    · exact pcf_at_of_two_distinct_neighbors D.hda3 D.hua3.symm D.ha3p0 D.hp0u.symm
        (by rw [hψu, hψ_out D.p₀ hp0S]; exact hγCu.2)
    · exact pcf_at_of_two_distinct_neighbors D.hdb1 D.hv1b1.symm D.hb1q1 D.hq1v1.symm
        (by rw [hψv1, hψ_out D.q₁ hq1S]; exact hα1.1.2.1)
    · exact pcf_at_of_two_distinct_neighbors D.hdb2 D.hv1b2.symm D.hb2q2 D.hq2v1.symm
        (by rw [hψv1, hψ_out D.q₂ hq2S]; exact hα1.1.2.2)
    · exact pcf_at_of_two_distinct_neighbors D.hdd1 D.hv2d1.symm D.hd1r1 D.hr1v2.symm
        (by rw [hψv2, hψ_out D.r₁ hr1S]; exact hα2.1.2.1)
    · exact pcf_at_of_two_distinct_neighbors D.hdd2 D.hv2d2.symm D.hd2r2 D.hr2v2.symm
        (by rw [hψv2, hψ_out D.r₂ hr2S]; exact hα2.1.2.2)

/-- `L3TwoNbrData` 孤立外点 `w` 双连 `b₁, b₂` 情形（涵盖 `d(w) ∈ {3, 4, 5}`）。 -/
private lemma L3_two_nbr_iso_double {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (D : L3TwoNbrData G)
    (adm : AdmissibleColoring G L D.S) (w : V) (hwS : w ∉ D.S)
    (hw_iso : ∀ r, r ∉ D.S → ¬ G.Adj w r)
    (hwb1 : G.Adj w D.b₁) (hwb2 : G.Adj w D.b₂)
    (hw_uniq : ∀ w', w' ∉ D.S → (∀ r, r ∉ D.S → ¬ G.Adj w' r) → (∃ s, G.Adj w' s) → w' = w) :
    False := by
  classical
  rcases D.ext_not_S with ⟨hp0S, hq1S, hq2S, hr1S, hr2S⟩
  have hq1w : D.q₁ = w := by
    rcases D.hb1_all w hwb1.symm with h | h
    · exact False.elim (hwS (by rw [h]; simp [L3TwoNbrData.S]))
    · exact h.symm
  have hq2w : D.q₂ = w := by
    rcases D.hb2_all w hwb2.symm with h | h
    · exact False.elim (hwS (by rw [h]; simp [L3TwoNbrData.S]))
    · exact h.symm
  have hdw3 : 3 ≤ G.degree w := hq1w ▸ D.hdq1
  have hNw_sub : G.neighborFinset w ⊆ {D.a₃, D.b₁, D.b₂, D.d₁, D.d₂} := by
    intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
    have hrS : r ∈ D.S := by by_contra h; exact hw_iso r h hr
    rcases D.S_out w hwS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have hLu4 : (L D.u).card = 4 := by rw [hm.list_card D.u]; simp [kappa, D.hdu]
  have hLv1 : (L D.v₁).card = 4 := by rw [hm.list_card D.v₁]; simp [kappa, D.hdv1]
  have hLv2 : (L D.v₂).card = 4 := by rw [hm.list_card D.v₂]; simp [kappa, D.hdv2]
  have hLa1 : (L D.a₁).card = 4 := by rw [hm.list_card D.a₁]; simp [kappa, D.hda1]
  have hLa2 : (L D.a₂).card = 4 := by rw [hm.list_card D.a₂]; simp [kappa, D.hda2]
  have hLa3 : (L D.a₃).card = 4 := by rw [hm.list_card D.a₃]; simp [kappa, D.hda3]
  have hLb1 : (L D.b₁).card = 4 := by rw [hm.list_card D.b₁]; simp [kappa, D.hdb1]
  have hLb2 : (L D.b₂).card = 4 := by rw [hm.list_card D.b₂]; simp [kappa, D.hdb2]
  have hLd1 : (L D.d₁).card = 4 := by rw [hm.list_card D.d₁]; simp [kappa, D.hdd1]
  have hLd2 : (L D.d₂).card = 4 := by rw [hm.list_card D.d₂]; simp [kappa, D.hdd2]
  let ω := adm.φ w
  -- 统一选取 10 色，分别覆盖 `d(w) = 5` 与 `d(w) ∈ {3, 4}` 两种子情形
  have hpick : ∃ γ α₁ α₂ c₁ c₂ c₃ cb₁ cb₂ cd₁ cd₂ : ℕ,
      γ ∈ L D.u ∧ α₁ ∈ L D.v₁ ∧ α₂ ∈ L D.v₂ ∧ c₁ ∈ L D.a₁ ∧ c₂ ∈ L D.a₂ ∧ c₃ ∈ L D.a₃ ∧
      cb₁ ∈ L D.b₁ ∧ cb₂ ∈ L D.b₂ ∧ cd₁ ∈ L D.d₁ ∧ cd₂ ∈ L D.d₂ ∧
      γ ≠ α₁ ∧ γ ≠ α₂ ∧ γ ≠ adm.φ D.p₀ ∧ α₁ ≠ ω ∧ α₂ ≠ adm.φ D.r₁ ∧ α₂ ≠ adm.φ D.r₂ ∧
      c₁ ≠ γ ∧ c₁ ≠ α₁ ∧ c₂ ≠ γ ∧ c₂ ≠ α₂ ∧ c₃ ≠ γ ∧ c₃ ≠ adm.φ D.p₀ ∧
      cb₁ ≠ α₁ ∧ cb₁ ≠ ω ∧ cb₂ ≠ α₁ ∧ cb₂ ≠ ω ∧
      cd₁ ≠ α₂ ∧ cd₁ ≠ adm.φ D.r₁ ∧ cd₂ ≠ α₂ ∧ cd₂ ≠ adm.φ D.r₂ ∧
      ((∃ r, r ∉ D.S ∧ G.Adj D.p₀ r) → c₃ ≠ adm.φs D.p₀) ∧
      ((∃ r, r ∉ D.S ∧ G.Adj D.r₁ r) → cd₁ ≠ adm.φs D.r₁) ∧
      ((∃ r, r ∉ D.S ∧ G.Adj D.r₂ r) → cd₂ ≠ adm.φs D.r₂) ∧
      HasUniqueColor [c₁, c₂, c₃] ∧ HasUniqueColor [c₁, cb₁, cb₂] ∧
      HasUniqueColor [c₂, cd₁, cd₂] ∧
      (∀ ψ : V → ℕ, ψ D.a₃ = c₃ → ψ D.b₁ = cb₁ → ψ D.b₂ = cb₂ → ψ D.d₁ = cd₁ → ψ D.d₂ = cd₂ →
        ∃ y, G.Adj w y ∧ ∀ z, G.Adj w z → ψ z = ψ y → z = y) := by
    rcases exists_mem_sdiff_of_lt (A := L D.v₂) (B := {adm.φ D.r₁, adm.φ D.r₂})
      (by have := Finset.card_le_two (a := adm.φ D.r₁) (b := adm.φ D.r₂); omega) with
      ⟨α₂, hα2L, hα2N⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα2N
    rcases exists_mem_sdiff_of_lt (A := L D.u) (B := {adm.φ D.p₀, α₂})
      (by have := Finset.card_le_two (a := adm.φ D.p₀) (b := α₂); omega) with ⟨γ, hγL, hγN⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγN
    rcases exists_mem_sdiff_of_lt (A := L D.v₁) (B := {γ, ω})
      (by have := Finset.card_le_two (a := γ) (b := ω); omega) with ⟨α₁, hα1L, hα1N⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα1N
    by_cases hM3 : G.Adj w D.a₃ ∧ G.Adj w D.d₁ ∧ G.Adj w D.d₂
    · -- 子情形 1：`d(w) = 5`，`p₀ = r₁ = r₂ = w`，外部三边均无 `φs` 限制！
      have hp0w : D.p₀ = w := by
        rcases D.ha3_all w hM3.1.symm with h | h
        · exact False.elim (hwS (by rw [h]; simp [L3TwoNbrData.S]))
        · exact h.symm
      have hr1w : D.r₁ = w := by
        rcases D.hd1_all w hM3.2.1.symm with h | h
        · exact False.elim (hwS (by rw [h]; simp [L3TwoNbrData.S]))
        · exact h.symm
      have hr2w : D.r₂ = w := by
        rcases D.hd2_all w hM3.2.2.symm with h | h
        · exact False.elim (hwS (by rw [h]; simp [L3TwoNbrData.S]))
        · exact h.symm
      rcases exists_mem_sdiff_of_lt (A := L D.d₁) (B := {ω, α₂})
        (by have := Finset.card_le_two (a := ω) (b := α₂); omega) with ⟨cd₁, hcd1L, hcd1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcd1N
      rcases exists_mem_sdiff_of_lt (A := L D.d₂) (B := {ω, α₂, cd₁})
        (by have := card_triple_le ω α₂ cd₁; omega) with ⟨cd₂, hcd2L, hcd2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcd2N
      rcases exists_mem_sdiff_of_lt (A := L D.a₃) (B := {ω, γ, cd₁})
        (by have := card_triple_le ω γ cd₁; omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      rcases exists_mem_sdiff_of_lt (A := L D.a₂) (B := {γ, α₂, c₃})
        (by have := card_triple_le γ α₂ c₃; omega) with ⟨c₂, hc2L, hc2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
      rcases exists_mem_sdiff_of_lt (A := L D.b₁) (B := {α₁, ω, cd₁})
        (by have := card_triple_le α₁ ω cd₁; omega) with ⟨cb₁, hcb1L, hcb1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcb1N
      rcases exists_mem_sdiff_of_lt (A := L D.b₂) (B := {α₁, ω, cd₁})
        (by have := card_triple_le α₁ ω cd₁; omega) with ⟨cb₂, hcb2L, hcb2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcb2N
      rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {γ, α₁, cb₁})
        (by have := card_triple_le γ α₁ cb₁; omega) with ⟨c₁, hc1L, hc1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
      refine ⟨γ, α₁, α₂, c₁, c₂, c₃, cb₁, cb₂, cd₁, cd₂,
        hγL, hα1L, hα2L, hc1L, hc2L, hc3L, hcb1L, hcb2L, hcd1L, hcd2L,
        Ne.symm hα1N.1, hγN.2, hγN.1, hα1N.2, hα2N.1, hα2N.2,
        hc1N.1, hc1N.2.1, hc2N.1, hc2N.2.1, hc3N.2.1, hp0w ▸ hc3N.1,
        hcb1N.1, hcb1N.2.1, hcb2N.1, hcb2N.2.1,
        hcd1N.2, hr1w ▸ hcd1N.1, hcd2N.2.1, hr2w ▸ hcd2N.1,
        fun ⟨r, hr, hwr⟩ => False.elim (hw_iso r hr (hp0w ▸ hwr)),
        fun ⟨r, hr, hwr⟩ => False.elim (hw_iso r hr (hr1w ▸ hwr)),
        fun ⟨r, hr, hwr⟩ => False.elim (hw_iso r hr (hr2w ▸ hwr)),
        by rw [hasUniqueColor_triple_iff]; exact fun h => hc2N.2.2 h.2,
        by rw [hasUniqueColor_triple_iff]; exact fun h => hc1N.2.2 h.1,
        by rw [hasUniqueColor_triple_iff]; exact fun h => hcd2N.2.2 h.2.symm, ?_⟩
      intro ψ ha3 hb1 hb2 hd1 hd2
      refine pcf_at_of_hasUniqueColor_five hM3.1 hwb1 hwb2 hM3.2.1 hM3.2.2 (fun z hz => ?_) ?_
      · have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        exact hm
      · rw [ha3, hb1, hb2, hd1, hd2]
        refine ⟨cd₁, ?_⟩
        simp [hc3N.2.2, hcb1N.2.2, hcb2N.2.2, hcd2N.2.2]
    · -- 子情形 2：`d(w) ∈ {3, 4}`，由 `pair_double_pcf` 一次性选定 `(cb₁, cb₂)`！
      rcases exists_mem_sdiff_of_lt (A := L D.a₃) (B := {adm.φ D.p₀, adm.φs D.p₀, γ})
        (by have := card_triple_le (adm.φ D.p₀) (adm.φs D.p₀) γ; omega) with ⟨c₃, hc3L, hc3N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc3N
      rcases exists_mem_sdiff_of_lt (A := L D.d₁) (B := {adm.φ D.r₁, adm.φs D.r₁, α₂})
        (by have := card_triple_le (adm.φ D.r₁) (adm.φs D.r₁) α₂; omega) with ⟨cd₁, hcd1L, hcd1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcd1N
      rcases exists_mem_sdiff_of_lt (A := L D.d₂) (B := {adm.φ D.r₂, adm.φs D.r₂, α₂})
        (by have := card_triple_le (adm.φ D.r₂) (adm.φs D.r₂) α₂; omega) with ⟨cd₂, hcd2L, hcd2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcd2N
      rcases exists_mem_sdiff_of_lt (A := L D.a₂) (B := {γ, α₂, cd₁})
        (by have := card_triple_le γ α₂ cd₁; omega) with ⟨c₂, hc2L, hc2N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2N
      rcases exists_mem_sdiff_of_lt (A := L D.a₁) (B := {γ, α₁, c₂})
        (by have := card_triple_le γ α₁ c₂; omega) with ⟨c₁, hc1L, hc1N⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1N
      have hBw_build : ∃ B_w : List ℕ, (B_w.length = 1 ∨ B_w.length = 2) ∧
          ∀ ψ : V → ℕ, ψ D.a₃ = c₃ → ψ D.d₁ = cd₁ → ψ D.d₂ = cd₂ →
            HasUniqueColor (B_w ++ [ψ D.b₁, ψ D.b₂]) →
            ∃ y, G.Adj w y ∧ ∀ z, G.Adj w z → ψ z = ψ y → z = y := by
        by_cases ha3 : G.Adj w D.a₃
        · by_cases hd1 : G.Adj w D.d₁
          · have hd2 : ¬ G.Adj w D.d₂ := fun h => hM3 ⟨ha3, hd1, h⟩
            refine ⟨[c₃, cd₁], Or.inr rfl, fun ψ h1 h2 _ hu => ?_⟩
            refine pcf_at_of_hasUniqueColor_four ha3 hd1 hwb1 hwb2 (fun z hz => ?_)
              (by rw [h1, h2]; exact hu)
            have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
            · exact Or.inr (Or.inl rfl)
            · exact False.elim (hd2 hz)
          · by_cases hd2 : G.Adj w D.d₂
            · refine ⟨[c₃, cd₂], Or.inr rfl, fun ψ h1 _ h3 hu => ?_⟩
              refine pcf_at_of_hasUniqueColor_four ha3 hd2 hwb1 hwb2 (fun z hz => ?_)
                (by rw [h1, h3]; exact hu)
              have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr rfl))
              · exact False.elim (hd1 hz)
              · exact Or.inr (Or.inl rfl)
            · refine ⟨[c₃], Or.inl rfl, fun ψ h1 _ _ hu => ?_⟩
              refine pcf_at_of_hasUniqueColor_three ha3 hwb1 hwb2 (fun z hz => ?_)
                (by rw [h1]; exact hu)
              have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
              · exact False.elim (hd1 hz)
              · exact False.elim (hd2 hz)
        · by_cases hd1 : G.Adj w D.d₁
          · by_cases hd2 : G.Adj w D.d₂
            · refine ⟨[cd₁, cd₂], Or.inr rfl, fun ψ _ h2 h3 hu => ?_⟩
              refine pcf_at_of_hasUniqueColor_four hd1 hd2 hwb1 hwb2 (fun z hz => ?_)
                (by rw [h2, h3]; exact hu)
              have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl
              · exact False.elim (ha3 hz)
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr rfl))
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
            · refine ⟨[cd₁], Or.inl rfl, fun ψ _ h2 _ hu => ?_⟩
              refine pcf_at_of_hasUniqueColor_three hd1 hwb1 hwb2 (fun z hz => ?_)
                (by rw [h2]; exact hu)
              have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl
              · exact False.elim (ha3 hz)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
              · exact Or.inl rfl
              · exact False.elim (hd2 hz)
          · by_cases hd2 : G.Adj w D.d₂
            · refine ⟨[cd₂], Or.inl rfl, fun ψ _ _ h3 hu => ?_⟩
              refine pcf_at_of_hasUniqueColor_three hd2 hwb1 hwb2 (fun z hz => ?_)
                (by rw [h3]; exact hu)
              have hm := hNw_sub ((G.mem_neighborFinset w z).mpr hz)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl
              · exact False.elim (ha3 hz)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
              · exact False.elim (hd1 hz)
              · exact Or.inl rfl
            · exfalso
              have hsub2 : G.neighborFinset w ⊆ {D.b₁, D.b₂} := by
                intro z hz; have hm := hNw_sub hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
                rcases hm with rfl | rfl | rfl | rfl | rfl
                · exact False.elim (ha3 ((G.mem_neighborFinset w _).mp hz))
                · exact Or.inl rfl
                · exact Or.inr rfl
                · exact False.elim (hd1 ((G.mem_neighborFinset w _).mp hz))
                · exact False.elim (hd2 ((G.mem_neighborFinset w _).mp hz))
              have hle := Finset.card_le_card hsub2
              rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pair D.hb12] at hle
              omega
      rcases hBw_build with ⟨B_w, hB12, hBw_pcf⟩
      have hB1 : 2 ≤ (L D.b₁ \ {α₁, ω}).card := by
        have := card_sdiff_ge (L D.b₁) {α₁, ω}; have := Finset.card_le_two (a := α₁) (b := ω); omega
      have hB2 : 2 ≤ (L D.b₂ \ {α₁, ω}).card := by
        have := card_sdiff_ge (L D.b₂) {α₁, ω}; have := Finset.card_le_two (a := α₁) (b := ω); omega
      rcases pair_double_pcf hB1 hB2 c₁ B_w hB12 with ⟨cb₁, hcb1, cb₂, hcb2, hnot_v1, hBw_uniq⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcb1 hcb2
      refine ⟨γ, α₁, α₂, c₁, c₂, c₃, cb₁, cb₂, cd₁, cd₂,
        hγL, hα1L, hα2L, hc1L, hc2L, hc3L, hcb1.1, hcb2.1, hcd1L, hcd2L,
        Ne.symm hα1N.1, hγN.2, hγN.1, hα1N.2, hα2N.1, hα2N.2,
        hc1N.1, hc1N.2.1, hc2N.1, hc2N.2.1, hc3N.2.2, hc3N.1,
        hcb1.2.1, hcb1.2.2, hcb2.2.1, hcb2.2.2,
        hcd1N.2.2, hcd1N.1, hcd2N.2.2, hcd2N.1,
        fun _ => hc3N.2.1, fun _ => hcd1N.2.1, fun _ => hcd2N.2.1,
        by rw [hasUniqueColor_triple_iff]; exact fun h => hc1N.2.2 h.1,
        by rw [hasUniqueColor_triple_iff]; exact hnot_v1,
        by rw [hasUniqueColor_triple_iff]; exact fun h => hc2N.2.2 h.1,
        fun ψ ha3 hb1 hb2 hd1 hd2 => hBw_pcf ψ ha3 hd1 hd2 (by rw [hb1, hb2]; exact hBw_uniq)⟩
  rcases hpick with
    ⟨γ, α₁, α₂, c₁, c₂, c₃, cb₁, cb₂, cd₁, cd₂,
      hγL, hα1L, hα2L, hc1L, hc2L, hc3L, hcb1L, hcb2L, hcd1L, hcd2L,
      hγα1, hγα2, hγp0, hα1ω, hα2r1, hα2r2,
      hc1γ, hc1α1, hc2γ, hc2α2, hc3γ, hc3p0, hcb1α1, hcb1ω, hcb2α1, hcb2ω,
      hcd1α2, hcd1r1, hcd2α2, hcd2r2, hav0, hav1, hav2, hu_uniq, hv1_uniq, hv2_uniq, hw_pcf⟩
  let ψ : V → ℕ := fun z =>
    if z = D.u then γ else if z = D.v₁ then α₁ else if z = D.v₂ then α₂
    else if z = D.a₁ then c₁ else if z = D.a₂ then c₂ else if z = D.a₃ then c₃
    else if z = D.b₁ then cb₁ else if z = D.b₂ then cb₂
    else if z = D.d₁ then cd₁ else if z = D.d₂ then cd₂ else adm.φ z
  have hψu : ψ D.u = γ := by simp [ψ]
  have hψv1 : ψ D.v₁ = α₁ := by simp [ψ, D.huv1.symm]
  have hψv2 : ψ D.v₂ = α₂ := by simp [ψ, D.huv2.symm, D.hv12.symm]
  have hψa1 : ψ D.a₁ = c₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hda1 D.hdu (by omega), ne_of_deg_eq_ne D.hda1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda1 D.hdv2 (by omega)]
  have hψa2 : ψ D.a₂ = c₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hda2 D.hdu (by omega), ne_of_deg_eq_ne D.hda2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda2 D.hdv2 (by omega), D.ha12.symm]
  have hψa3 : ψ D.a₃ = c₃ := by
    simp [ψ, ne_of_deg_eq_ne D.hda3 D.hdu (by omega), ne_of_deg_eq_ne D.hda3 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hda3 D.hdv2 (by omega), D.ha13.symm, D.ha23.symm]
  have hψb1 : ψ D.b₁ = cb₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hdb1 D.hdu (by omega), ne_of_deg_eq_ne D.hdb1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdb1 D.hdv2 (by omega), D.ha1b1.symm, D.ha2b1.symm, D.ha3b1.symm]
  have hψb2 : ψ D.b₂ = cb₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hdb2 D.hdu (by omega), ne_of_deg_eq_ne D.hdb2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdb2 D.hdv2 (by omega), D.ha1b2.symm, D.ha2b2.symm, D.ha3b2.symm,
      D.hb12.symm]
  have hψd1 : ψ D.d₁ = cd₁ := by
    simp [ψ, ne_of_deg_eq_ne D.hdd1 D.hdu (by omega), ne_of_deg_eq_ne D.hdd1 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdd1 D.hdv2 (by omega), D.ha1d1.symm, D.ha2d1.symm, D.ha3d1.symm,
      D.hb1d1.symm, D.hb2d1.symm]
  have hψd2 : ψ D.d₂ = cd₂ := by
    simp [ψ, ne_of_deg_eq_ne D.hdd2 D.hdu (by omega), ne_of_deg_eq_ne D.hdd2 D.hdv1 (by omega),
      ne_of_deg_eq_ne D.hdd2 D.hdv2 (by omega), D.ha1d2.symm, D.ha2d2.symm, D.ha3d2.symm,
      D.hb1d2.symm, D.hb2d2.symm, D.hd12.symm]
  have hψ_out : ∀ z, z ∉ D.S → ψ z = adm.φ z := fun z hz => by
    simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [ψ, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
      hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2, ite_false]
  apply adm.contradiction hm ψ hψ_out
  · intro z hz; simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hψu]; exact hγL
    · rw [hψv1]; exact hα1L
    · rw [hψv2]; exact hα2L
    · rw [hψa1]; exact hc1L
    · rw [hψa2]; exact hc2L
    · rw [hψa3]; exact hc3L
    · rw [hψb1]; exact hcb1L
    · rw [hψb2]; exact hcb2L
    · rw [hψd1]; exact hcd1L
    · rw [hψd2]; exact hcd2L
  · intro z₁ z₂ h12' hor
    have hcase : ∀ p r, G.Adj p r → p ∈ D.S → ψ p ≠ ψ r := by
      intro p r hpr hpS
      simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases D.hu_all r hpr with hr | hr | hr
        · rw [hr, hψu, hψa1]; exact hc1γ.symm
        · rw [hr, hψu, hψa2]; exact hc2γ.symm
        · rw [hr, hψu, hψa3]; exact hc3γ.symm
      · rcases D.hv1_all r hpr with hr | hr | hr
        · rw [hr, hψv1, hψa1]; exact hc1α1.symm
        · rw [hr, hψv1, hψb1]; exact hcb1α1.symm
        · rw [hr, hψv1, hψb2]; exact hcb2α1.symm
      · rcases D.hv2_all r hpr with hr | hr | hr
        · rw [hr, hψv2, hψa2]; exact hc2α2.symm
        · rw [hr, hψv2, hψd1]; exact hcd1α2.symm
        · rw [hr, hψv2, hψd2]; exact hcd2α2.symm
      · rcases D.ha1_all r hpr with hr | hr
        · rw [hr, hψa1, hψu]; exact hc1γ
        · rw [hr, hψa1, hψv1]; exact hc1α1
      · rcases D.ha2_all r hpr with hr | hr
        · rw [hr, hψa2, hψu]; exact hc2γ
        · rw [hr, hψa2, hψv2]; exact hc2α2
      · rcases D.ha3_all r hpr with hr | hr
        · rw [hr, hψa3, hψu]; exact hc3γ
        · rw [hr, hψa3, hψ_out D.p₀ hp0S]; exact hc3p0
      · rcases D.hb1_all r hpr with hr | hr
        · rw [hr, hψb1, hψv1]; exact hcb1α1
        · rw [hr, hψb1, hψ_out D.q₁ hq1S, hq1w]; exact hcb1ω
      · rcases D.hb2_all r hpr with hr | hr
        · rw [hr, hψb2, hψv1]; exact hcb2α1
        · rw [hr, hψb2, hψ_out D.q₂ hq2S, hq2w]; exact hcb2ω
      · rcases D.hd1_all r hpr with hr | hr
        · rw [hr, hψd1, hψv2]; exact hcd1α2
        · rw [hr, hψd1, hψ_out D.r₁ hr1S]; exact hcd1r1
      · rcases D.hd2_all r hpr with hr | hr
        · rw [hr, hψd2, hψv2]; exact hcd2α2
        · rw [hr, hψd2, hψ_out D.r₂ hr2S]; exact hcd2r2
    rcases hor with h1 | h2
    · exact hcase z₁ z₂ h12' h1
    · exact (hcase z₂ z₁ h12'.symm h2).symm
  · intro z hzS hnon s hsS hzs
    rcases D.S_out z hzS s hsS hzs with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψa3]; exact hav0 hnon
    · exfalso; rcases hnon with ⟨r, hr, hzr⟩; exact hw_iso r hr (hq1w ▸ hzr)
    · exfalso; rcases hnon with ⟨r, hr, hzr⟩; exact hw_iso r hr (hq2w ▸ hzr)
    · rw [hψd1]; exact hav1 hnon
    · rw [hψd2]; exact hav2 hnon
  · intro w' hw'S hw'_iso hw'_ex
    have hw'_eq : w' = w := hw_uniq w' hw'S hw'_iso hw'_ex
    subst hw'_eq
    exact hw_pcf ψ hψa3 hψb1 hψb2 hψd1 hψd2
  · intro z hzS _
    simp only [L3TwoNbrData.S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pcf_at_of_hasUniqueColor_three D.hua1 D.hua2 D.hua3 D.hu_all
        (by rw [hψa1, hψa2, hψa3]; exact hu_uniq)
    · exact pcf_at_of_hasUniqueColor_three D.ha1v1.symm D.hv1b1 D.hv1b2 D.hv1_all
        (by rw [hψa1, hψb1, hψb2]; exact hv1_uniq)
    · exact pcf_at_of_hasUniqueColor_three D.ha2v2.symm D.hv2d1 D.hv2d2 D.hv2_all
        (by rw [hψa2, hψd1, hψd2]; exact hv2_uniq)
    · exact pcf_at_of_two_distinct_neighbors D.hda1 D.hua1.symm D.ha1v1 D.huv1
        (by rw [hψu, hψv1]; exact hγα1)
    · exact pcf_at_of_two_distinct_neighbors D.hda2 D.hua2.symm D.ha2v2 D.huv2
        (by rw [hψu, hψv2]; exact hγα2)
    · exact pcf_at_of_two_distinct_neighbors D.hda3 D.hua3.symm D.ha3p0 D.hp0u.symm
        (by rw [hψu, hψ_out D.p₀ hp0S]; exact hγp0)
    · exact pcf_at_of_two_distinct_neighbors D.hdb1 D.hv1b1.symm D.hb1q1 D.hq1v1.symm
        (by rw [hψv1, hψ_out D.q₁ hq1S, hq1w]; exact hα1ω)
    · exact pcf_at_of_two_distinct_neighbors D.hdb2 D.hv1b2.symm D.hb2q2 D.hq2v1.symm
        (by rw [hψv1, hψ_out D.q₂ hq2S, hq2w]; exact hα1ω)
    · exact pcf_at_of_two_distinct_neighbors D.hdd1 D.hv2d1.symm D.hd1r1 D.hr1v2.symm
        (by rw [hψv2, hψ_out D.r₁ hr1S]; exact hα2r1)
    · exact pcf_at_of_two_distinct_neighbors D.hdd2 D.hv2d2.symm D.hd2r2 D.hr2v2.symm
        (by rw [hψv2, hψ_out D.r₂ hr2S]; exact hα2r2)

/-- 主引理 1：每个 `L3` 顶点至多通过 `1`-线串连接 `1` 个 `L3` 顶点。 -/
lemma L3_at_most_one_L3_nbr {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (hu : IsL3 G u)
    {a₁ a₂ v₁ v₂ : V} (ha1 : a₁ ∈ oneThreadNbrs G u) (ha2 : a₂ ∈ oneThreadNbrs G u)
    (hne : a₁ ≠ a₂) (hv1 : G.Adj a₁ v₁) (hv1u : v₁ ≠ u) (hv2 : G.Adj a₂ v₂) (hv2u : v₂ ≠ u)
    (hL1 : IsL3 G v₁) (hL2 : IsL3 G v₂) : False := by
  classical
  have hdu3 : G.degree u = 3 := hu.1
  have hdv1 : G.degree v₁ = 3 := hL1.1
  have hdv2 : G.degree v₂ = 3 := hL2.1
  have hua1 : G.Adj u a₁ := (mem_oneThreadNbrs.mp ha1).1
  have hda1 : G.degree a₁ = 2 := (mem_oneThreadNbrs.mp ha1).2.1
  have hua2 : G.Adj u a₂ := (mem_oneThreadNbrs.mp ha2).1
  have hda2 : G.degree a₂ = 2 := (mem_oneThreadNbrs.mp ha2).2.1
  have hv12 : v₁ ≠ v₂ := fun heq =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hu) (Or.inl hL1) hv1u.symm ha1 ha2 hne
      hv1 (heq ▸ hv2)
  rcases isL3_unpack_one hm hu ha1 with ⟨x₁, x₂, hx1, hx2, ha1x1, ha1x2, hx12, hu_raw⟩
  have ha3_pick : ∃ a₃, a₃ ∈ oneThreadNbrs G u ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
      ∀ z, G.Adj u z → z = a₁ ∨ z = a₂ ∨ z = a₃ := by
    rcases hu_raw a₂ hua2 with h | h | h
    · exact False.elim (hne h.symm)
    · exact ⟨x₂, hx2, ha1x2, h ▸ hx12, fun z hz => by
        rcases hu_raw z hz with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (h1.trans h.symm))
        · exact Or.inr (Or.inr h1)⟩
    · exact ⟨x₁, hx1, ha1x1, h ▸ hx12.symm, fun z hz => by
        rcases hu_raw z hz with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
        · exact Or.inr (Or.inl (h1.trans h.symm))⟩
  rcases ha3_pick with ⟨a₃, ha3, ha13, ha23, hu_all⟩
  have hua3 : G.Adj u a₃ := (mem_oneThreadNbrs.mp ha3).1
  have hda3 : G.degree a₃ = 2 := (mem_oneThreadNbrs.mp ha3).2.1
  have hv1_a1 : a₁ ∈ oneThreadNbrs G v₁ :=
    mem_oneThreadNbrs.mpr ⟨hv1.symm, hda1, u, hua1.symm, hv1u.symm, by omega⟩
  have hv2_a2 : a₂ ∈ oneThreadNbrs G v₂ :=
    mem_oneThreadNbrs.mpr ⟨hv2.symm, hda2, u, hua2.symm, hv2u.symm, by omega⟩
  rcases isL3_unpack_one hm hL1 hv1_a1 with ⟨b₁, b₂, hb1, hb2, ha1b1, ha1b2, hb12, hv1_all⟩
  rcases isL3_unpack_one hm hL2 hv2_a2 with ⟨d₁, d₂, hd1, hd2, ha2d1, ha2d2, hd12, hv2_all⟩
  have hv1b1 : G.Adj v₁ b₁ := (mem_oneThreadNbrs.mp hb1).1
  have hdb1 : G.degree b₁ = 2 := (mem_oneThreadNbrs.mp hb1).2.1
  have hv1b2 : G.Adj v₁ b₂ := (mem_oneThreadNbrs.mp hb2).1
  have hdb2 : G.degree b₂ = 2 := (mem_oneThreadNbrs.mp hb2).2.1
  have hv2d1 : G.Adj v₂ d₁ := (mem_oneThreadNbrs.mp hd1).1
  have hdd1 : G.degree d₁ = 2 := (mem_oneThreadNbrs.mp hd1).2.1
  have hv2d2 : G.Adj v₂ d₂ := (mem_oneThreadNbrs.mp hd2).1
  have hdd2 : G.degree d₂ = 2 := (mem_oneThreadNbrs.mp hd2).2.1
  rcases oneThreadNbr_other_endpoint hm (by omega) ha3 with ⟨p₀, ha3p0, hp0u, hdp0, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb1 with ⟨q₁, hb1q1, hq1v1, hdq1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hb2 with ⟨q₂, hb2q2, hq2v1, hdq2, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hd1 with ⟨r₁, hd1r1, hr1v2, hdr1, _, _⟩
  rcases oneThreadNbr_other_endpoint hm (by omega) hd2 with ⟨r₂, hd2r2, hr2v2, hdr2, _, _⟩
  have hp0v1 : p₀ ≠ v₁ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hu) (Or.inl hL1) hv1u.symm ha1 ha3 ha13
      hv1 (h ▸ ha3p0)
  have hp0v2 : p₀ ≠ v₂ := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hu) (Or.inl hL2) hv2u.symm ha2 ha3 ha23
      hv2 (h ▸ ha3p0)
  have hq1u : q₁ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hL1) (Or.inl hu) hv1u hv1_a1 hb1 ha1b1
      hua1.symm (h ▸ hb1q1)
  have hq2u : q₂ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hL1) (Or.inl hu) hv1u hv1_a1 hb2 ha1b2
      hua1.symm (h ▸ hb2q2)
  have hr1u : r₁ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hL2) (Or.inl hu) hv2u hv2_a2 hd1 ha2d1
      hua2.symm (h ▸ hd1r1)
  have hr2u : r₂ ≠ u := fun h =>
    no_two_oneThreads_between_Poor1Ext hm hpq (Or.inl hL2) (Or.inl hu) hv2u hv2_a2 hd2 ha2d2
      hua2.symm (h ▸ hd2r2)
  have hq1v2 : q₁ ≠ v₂ := fun h =>
    no_L3_subdivided_triangle hm hpq hu hL1 hL2 hv1u.symm hv2u.symm hv12 ha1 hv1 ha2 hv2 hb1
      (h ▸ hb1q1)
  have hq2v2 : q₂ ≠ v₂ := fun h =>
    no_L3_subdivided_triangle hm hpq hu hL1 hL2 hv1u.symm hv2u.symm hv12 ha1 hv1 ha2 hv2 hb2
      (h ▸ hb2q2)
  have hr1v1 : r₁ ≠ v₁ := fun h =>
    no_L3_subdivided_triangle hm hpq hu hL2 hL1 hv2u.symm hv1u.symm hv12.symm ha2 hv2 ha1 hv1 hd1
      (h ▸ hd1r1)
  have hr2v1 : r₂ ≠ v₁ := fun h =>
    no_L3_subdivided_triangle hm hpq hu hL2 hL1 hv2u.symm hv1u.symm hv12.symm ha2 hv2 ha1 hv1 hd2
      (h ▸ hd2r2)
  have ha1_all : ∀ z, G.Adj a₁ z → z = u ∨ z = v₁ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hda1 hua1.symm hv1 hv1u.symm
    have : z ∈ ({u, v₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₁ z).mpr hz
    simpa using this
  have ha2_all : ∀ z, G.Adj a₂ z → z = u ∨ z = v₂ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hda2 hua2.symm hv2 hv2u.symm
    have : z ∈ ({u, v₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₂ z).mpr hz
    simpa using this
  have ha3_all : ∀ z, G.Adj a₃ z → z = u ∨ z = p₀ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hda3 hua3.symm ha3p0 hp0u.symm
    have : z ∈ ({u, p₀} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset a₃ z).mpr hz
    simpa using this
  have hb1_all : ∀ z, G.Adj b₁ z → z = v₁ ∨ z = q₁ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hdb1 hv1b1.symm hb1q1 hq1v1.symm
    have : z ∈ ({v₁, q₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₁ z).mpr hz
    simpa using this
  have hb2_all : ∀ z, G.Adj b₂ z → z = v₁ ∨ z = q₂ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hdb2 hv1b2.symm hb2q2 hq2v1.symm
    have : z ∈ ({v₁, q₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset b₂ z).mpr hz
    simpa using this
  have hd1_all : ∀ z, G.Adj d₁ z → z = v₂ ∨ z = r₁ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hdd1 hv2d1.symm hd1r1 hr1v2.symm
    have : z ∈ ({v₂, r₁} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset d₁ z).mpr hz
    simpa using this
  have hd2_all : ∀ z, G.Adj d₂ z → z = v₂ ∨ z = r₂ := by
    intro z hz; have hN := neighborFinset_eq_pair_of_deg_two hdd2 hv2d2.symm hd2r2 hr2v2.symm
    have : z ∈ ({v₂, r₂} : Finset V) := by rw [← hN]; exact (G.mem_neighborFinset d₂ z).mpr hz
    simpa using this
  let D : L3TwoNbrData G := {
    u := u, v₁ := v₁, v₂ := v₂, a₁ := a₁, a₂ := a₂, a₃ := a₃, b₁ := b₁, b₂ := b₂,
    d₁ := d₁, d₂ := d₂, p₀ := p₀, q₁ := q₁, q₂ := q₂, r₁ := r₁, r₂ := r₂,
    hdu := hdu3, hdv1 := hdv1, hdv2 := hdv2, hda1 := hda1, hda2 := hda2, hda3 := hda3,
    hdb1 := hdb1, hdb2 := hdb2, hdd1 := hdd1, hdd2 := hdd2,
    hdp0 := hdp0, hdq1 := hdq1, hdq2 := hdq2, hdr1 := hdr1, hdr2 := hdr2,
    huv1 := hv1u.symm, huv2 := hv2u.symm, hv12 := hv12,
    ha12 := hne, ha13 := ha13, ha23 := ha23, hb12 := hb12, hd12 := hd12,
    ha1b1 := ha1b1, ha1b2 := ha1b2,
    ha1d1 := fun h => by
      rcases ha1_all v₂ (h ▸ hv2d1.symm) with h1 | h1
      · exact hv2u h1
      · exact hv12 h1.symm,
    ha1d2 := fun h => by
      rcases ha1_all v₂ (h ▸ hv2d2.symm) with h1 | h1
      · exact hv2u h1
      · exact hv12 h1.symm,
    ha2b1 := fun h => by
      rcases ha2_all v₁ (h ▸ hv1b1.symm) with h1 | h1
      · exact hv1u h1
      · exact hv12 h1,
    ha2b2 := fun h => by
      rcases ha2_all v₁ (h ▸ hv1b2.symm) with h1 | h1
      · exact hv1u h1
      · exact hv12 h1,
    ha2d1 := ha2d1, ha2d2 := ha2d2,
    ha3b1 := fun h => by
      rcases ha3_all v₁ (h ▸ hv1b1.symm) with h1 | h1
      · exact hv1u h1
      · exact hp0v1 h1.symm,
    ha3b2 := fun h => by
      rcases ha3_all v₁ (h ▸ hv1b2.symm) with h1 | h1
      · exact hv1u h1
      · exact hp0v1 h1.symm,
    ha3d1 := fun h => by
      rcases ha3_all v₂ (h ▸ hv2d1.symm) with h1 | h1
      · exact hv2u h1
      · exact hp0v2 h1.symm,
    ha3d2 := fun h => by
      rcases ha3_all v₂ (h ▸ hv2d2.symm) with h1 | h1
      · exact hv2u h1
      · exact hp0v2 h1.symm,
    hb1d1 := fun h => by
      rcases hb1_all v₂ (h ▸ hv2d1.symm) with h1 | h1
      · exact hv12 h1.symm
      · exact hq1v2 h1.symm,
    hb1d2 := fun h => by
      rcases hb1_all v₂ (h ▸ hv2d2.symm) with h1 | h1
      · exact hv12 h1.symm
      · exact hq1v2 h1.symm,
    hb2d1 := fun h => by
      rcases hb2_all v₂ (h ▸ hv2d1.symm) with h1 | h1
      · exact hv12 h1.symm
      · exact hq2v2 h1.symm,
    hb2d2 := fun h => by
      rcases hb2_all v₂ (h ▸ hv2d2.symm) with h1 | h1
      · exact hv12 h1.symm
      · exact hq2v2 h1.symm,
    hua1 := hua1, hua2 := hua2, hua3 := hua3, ha1v1 := hv1, ha2v2 := hv2, ha3p0 := ha3p0,
    hv1b1 := hv1b1, hv1b2 := hv1b2, hb1q1 := hb1q1, hb2q2 := hb2q2,
    hv2d1 := hv2d1, hv2d2 := hv2d2, hd1r1 := hd1r1, hd2r2 := hd2r2,
    hu_all := hu_all, hv1_all := hv1_all, hv2_all := hv2_all,
    ha1_all := ha1_all, ha2_all := ha2_all, ha3_all := ha3_all,
    hb1_all := hb1_all, hb2_all := hb2_all, hd1_all := hd1_all, hd2_all := hd2_all,
    hp0u := hp0u, hp0v1 := hp0v1, hp0v2 := hp0v2,
    hq1u := hq1u, hq1v1 := hq1v1, hq1v2 := hq1v2,
    hq2u := hq2u, hq2v1 := hq2v1, hq2v2 := hq2v2,
    hr1u := hr1u, hr1v1 := hr1v1, hr1v2 := hr1v2,
    hr2u := hr2u, hr2v1 := hr2v1, hr2v2 := hr2v2 }
  rcases exists_admissible_coloring hm (S := D.S) ⟨D.u, by simp [L3TwoNbrData.S]⟩ with ⟨adm⟩
  by_cases hiso : ∃ w, w ∉ D.S ∧ (∀ r, r ∉ D.S → ¬ G.Adj w r) ∧ (∃ s, G.Adj w s)
  · rcases hiso with ⟨w, hwS, hw_iso, ⟨s₀, hws₀⟩⟩
    have hs₀S : s₀ ∈ D.S := by by_contra h; exact hw_iso s₀ h hws₀
    have hdw3 : 3 ≤ G.degree w := by
      rcases D.S_out w hwS s₀ hs₀S hws₀ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact D.hdp0
      · exact D.hdq1
      · exact D.hdq2
      · exact D.hdr1
      · exact D.hdr2
    have hNw_sub : ∀ z, z ∉ D.S → (∀ r, r ∉ D.S → ¬ G.Adj z r) →
        G.neighborFinset z ⊆ {D.a₃, D.b₁, D.b₂, D.d₁, D.d₂} := by
      intro z hzS hz_iso r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      have hrS : r ∈ D.S := by by_contra h; exact hz_iso r h hr
      rcases D.S_out z hzS r hrS hr with
        ⟨hr_eq, _⟩ | ⟨hr_eq, _⟩ | ⟨hr_eq, _⟩ | ⟨hr_eq, _⟩ | ⟨hr_eq, _⟩ <;> simp [hr_eq]
    have hw_uniq : ∀ w', w' ∉ D.S → (∀ r, r ∉ D.S → ¬ G.Adj w' r) → (∃ s, G.Adj w' s) → w' = w := by
      intro w' hw'S hw'_iso ⟨s', hw's'⟩
      by_contra hne'
      have hs'S : s' ∈ D.S := by by_contra h; exact hw'_iso s' h hw's'
      have hdw'3 : 3 ≤ G.degree w' := by
        rcases D.S_out w' hw'S s' hs'S hw's' with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact D.hdp0
        · exact D.hdq1
        · exact D.hdq2
        · exact D.hdr1
        · exact D.hdr2
      have hdisj_N : Disjoint (G.neighborFinset w) (G.neighborFinset w') := by
        rw [Finset.disjoint_left]; intro r hr1 hr2
        rw [SimpleGraph.mem_neighborFinset] at hr1 hr2
        have hrS : r ∈ D.S := by by_contra h; exact hw_iso r h hr1
        rcases D.S_out w hwS r hrS hr1 with
          ⟨he1, h1⟩ | ⟨he1, h1⟩ | ⟨he1, h1⟩ | ⟨he1, h1⟩ | ⟨he1, h1⟩ <;>
        rcases D.S_out w' hw'S r hrS hr2 with
          ⟨he2, h2⟩ | ⟨he2, h2⟩ | ⟨he2, h2⟩ | ⟨he2, h2⟩ | ⟨he2, h2⟩
        · exact hne' (h2.trans h1.symm)
        · exact D.ha3b1 (he1.symm.trans he2)
        · exact D.ha3b2 (he1.symm.trans he2)
        · exact D.ha3d1 (he1.symm.trans he2)
        · exact D.ha3d2 (he1.symm.trans he2)
        · exact D.ha3b1 (he2.symm.trans he1)
        · exact hne' (h2.trans h1.symm)
        · exact D.hb12 (he1.symm.trans he2)
        · exact D.hb1d1 (he1.symm.trans he2)
        · exact D.hb1d2 (he1.symm.trans he2)
        · exact D.ha3b2 (he2.symm.trans he1)
        · exact D.hb12 (he2.symm.trans he1)
        · exact hne' (h2.trans h1.symm)
        · exact D.hb2d1 (he1.symm.trans he2)
        · exact D.hb2d2 (he1.symm.trans he2)
        · exact D.ha3d1 (he2.symm.trans he1)
        · exact D.hb1d1 (he2.symm.trans he1)
        · exact D.hb2d1 (he2.symm.trans he1)
        · exact hne' (h2.trans h1.symm)
        · exact D.hd12 (he1.symm.trans he2)
        · exact D.ha3d2 (he2.symm.trans he1)
        · exact D.hb1d2 (he2.symm.trans he1)
        · exact D.hb2d2 (he2.symm.trans he1)
        · exact D.hd12 (he2.symm.trans he1)
        · exact hne' (h2.trans h1.symm)
      have hU_sub : G.neighborFinset w ∪ G.neighborFinset w' ⊆ {D.a₃, D.b₁, D.b₂, D.d₁, D.d₂} :=
        Finset.union_subset (hNw_sub w hwS hw_iso) (hNw_sub w' hw'S hw'_iso)
      have hle := Finset.card_le_card hU_sub
      rw [Finset.card_union_of_disjoint hdisj_N, SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree] at hle
      have h5 : ({D.a₃, D.b₁, D.b₂, D.d₁, D.d₂} : Finset V).card ≤ 5 :=
        le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
          (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
            (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
              (Finset.card_le_two (a := D.d₁) (b := D.d₂)) 1)) 1)) 1)
      omega
    by_cases hbb : G.Adj w D.b₁ ∧ G.Adj w D.b₂
    · exact L3_two_nbr_iso_double hm D adm w hwS hw_iso hbb.1 hbb.2 hw_uniq
    · by_cases hdd : G.Adj w D.d₁ ∧ G.Adj w D.d₂
      · have hSsw : D.swap.S = D.S := D.S_swap
        exact L3_two_nbr_iso_double hm D.swap (hSsw.symm ▸ adm) w (hSsw.symm ▸ hwS)
          (fun r hr => hw_iso r (hSsw ▸ hr)) hdd.1 hdd.2
          (fun w' hw' h1 h2 => hw_uniq w' (hSsw ▸ hw') (fun r hr => h1 r (hSsw.symm ▸ hr)) h2)
      · -- 若 `w` 至多连 `{b₁, b₂}` 中 1 个且至多连 `{d₁, d₂}` 中 1 个，则 `w` 是 `L3` 且与 `{u, v₁}` 构成细分三角形！
        have h1 : (G.neighborFinset w ∩ {D.b₁, D.b₂}).card ≤ 1 := by
          by_cases h1a : G.Adj w D.b₁
          · have h1b : ¬ G.Adj w D.b₂ := fun h => hbb ⟨h1a, h⟩
            have hsub : G.neighborFinset w ∩ {D.b₁, D.b₂} ⊆ {D.b₁} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · rfl
              · exact False.elim (h1b hr.1)
            exact le_trans (Finset.card_le_card hsub) (by simp)
          · have hsub : G.neighborFinset w ∩ {D.b₁, D.b₂} ⊆ {D.b₂} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · exact False.elim (h1a hr.1)
              · rfl
            exact le_trans (Finset.card_le_card hsub) (by simp)
        have h2 : (G.neighborFinset w ∩ {D.d₁, D.d₂}).card ≤ 1 := by
          by_cases h2a : G.Adj w D.d₁
          · have h2b : ¬ G.Adj w D.d₂ := fun h => hdd ⟨h2a, h⟩
            have hsub : G.neighborFinset w ∩ {D.d₁, D.d₂} ⊆ {D.d₁} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · rfl
              · exact False.elim (h2b hr.1)
            exact le_trans (Finset.card_le_card hsub) (by simp)
          · have hsub : G.neighborFinset w ∩ {D.d₁, D.d₂} ⊆ {D.d₂} := by
              intro r hr; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                Finset.mem_insert, Finset.mem_singleton] at hr ⊢
              rcases hr.2 with rfl | rfl
              · exact False.elim (h2a hr.1)
              · rfl
            exact le_trans (Finset.card_le_card hsub) (by simp)
        have h3 : (G.neighborFinset w ∩ {D.a₃}).card ≤ 1 :=
          le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp)
        have hcov : G.neighborFinset w ⊆
            (G.neighborFinset w ∩ {D.a₃}) ∪
              ((G.neighborFinset w ∩ {D.b₁, D.b₂}) ∪ (G.neighborFinset w ∩ {D.d₁, D.d₂})) := by
          intro r hr; have hm := hNw_sub w hwS hw_iso hr
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            at hm ⊢
          rcases hm with rfl | rfl | rfl | rfl | rfl
          · exact Or.inl ⟨hr, rfl⟩
          · exact Or.inr (Or.inl ⟨hr, Or.inl rfl⟩)
          · exact Or.inr (Or.inl ⟨hr, Or.inr rfl⟩)
          · exact Or.inr (Or.inr ⟨hr, Or.inl rfl⟩)
          · exact Or.inr (Or.inr ⟨hr, Or.inr rfl⟩)
        have hle := le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
        have hle2 := Finset.card_union_le (G.neighborFinset w ∩ {D.b₁, D.b₂})
          (G.neighborFinset w ∩ {D.d₁, D.d₂})
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
        have hdw_eq3 : G.degree w = 3 := by omega
        have hcard_a3 : (G.neighborFinset w ∩ {D.a₃}).card = 1 := by omega
        have hcard_b : (G.neighborFinset w ∩ {D.b₁, D.b₂}).card = 1 := by omega
        have hcard_d : (G.neighborFinset w ∩ {D.d₁, D.d₂}).card = 1 := by omega
        have hwa3 : G.Adj w D.a₃ := by
          rcases Finset.card_pos.mp (by omega : 0 < (G.neighborFinset w ∩ {D.a₃}).card) with ⟨r, hr⟩
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton] at hr
          exact hr.2 ▸ hr.1
        have hwb_ex : ∃ b, b ∈ oneThreadNbrs G v₁ ∧ G.Adj w b ∧ b ≠ a₃ := by
          rcases Finset.card_pos.mp (by omega : 0 < (G.neighborFinset w ∩ {D.b₁, D.b₂}).card) with
            ⟨r, hr⟩
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
            Finset.mem_singleton] at hr
          rcases hr.2 with hr_eq | hr_eq
          · exact ⟨b₁, hb1, by dsimp only [D] at hr_eq; exact hr_eq ▸ hr.1, D.ha3b1.symm⟩
          · exact ⟨b₂, hb2, by dsimp only [D] at hr_eq; exact hr_eq ▸ hr.1, D.ha3b2.symm⟩
        rcases hwb_ex with ⟨b, hb_v1, hwb, hba3⟩
        have hwu : u ≠ w := fun h => hwS (by rw [← h]; simp [D, L3TwoNbrData.S])
        have hwv1 : v₁ ≠ w := fun h => hwS (by rw [← h]; simp [D, L3TwoNbrData.S])
        have hwv2 : v₂ ≠ w := fun h => hwS (by rw [← h]; simp [D, L3TwoNbrData.S])
        have hsub1 : G.neighborFinset w ⊆ oneThreadNbrs G w := by
          intro r hr; have hm := hNw_sub w hwS hw_iso hr
          rw [SimpleGraph.mem_neighborFinset] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl
          · exact mem_oneThreadNbrs.mpr ⟨hr, D.hda3, u, D.hua3.symm, hwu, by omega⟩
          · exact mem_oneThreadNbrs.mpr ⟨hr, D.hdb1, v₁, D.hv1b1.symm, hwv1, by omega⟩
          · exact mem_oneThreadNbrs.mpr ⟨hr, D.hdb2, v₁, D.hv1b2.symm, hwv1, by omega⟩
          · exact mem_oneThreadNbrs.mpr ⟨hr, D.hdd1, v₂, D.hv2d1.symm, hwv2, by omega⟩
          · exact mem_oneThreadNbrs.mpr ⟨hr, D.hdd2, v₂, D.hv2d2.symm, hwv2, by omega⟩
        have h1_sub_N : oneThreadNbrs G w ⊆ G.neighborFinset w := fun r hr =>
          (G.mem_neighborFinset w r).mpr (mem_oneThreadNbrs.mp hr).1
        have hwL3 : IsL3 G w := by
          refine ⟨hdw_eq3, ?_⟩
          rw [Finset.Subset.antisymm h1_sub_N hsub1, SimpleGraph.card_neighborFinset_eq_degree,
              hdw_eq3]
        exact no_L3_subdivided_triangle hm hpq hu hL1 hwL3 hv1u.symm hwu hwv1 ha1 hv1 ha3
          hwa3.symm hb_v1 hwb.symm
  · exact L3_two_nbr_noniso hm D adm hiso

end LeanResearch.Proposal3
