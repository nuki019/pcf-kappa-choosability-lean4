/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BadAndThreads2

/-!
# 里程碑 2 公共结构谓词与线串双锚点接口（`BeyondDefs`）

本模块为突破 `mad(G) < 12/5 → 22/9` 的各并行子模块（`ThreeThreadExt`、`Q4Ext`、`Core3Ext`、
`T3Adjacency`、`T3Adjacency2`、`BridgeExt`、`ThreadPartition`、`Discharging22_9`）提供统一的
顶点分类谓词、`T3`/`T21`/`T20` 结构引理、核心度完整五分恒等式，以及 `1`-线串 / `2`-线串的对端锚点提取引理。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 坏/好邻点集合与核心度完整五分恒等式 -/

/-- 顶点 `u` 的坏核心邻点集合。 -/
def badNbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (coreNbrs G u).filter (IsBad G)

/-- 顶点 `u` 的好核心邻点集合。 -/
def goodNbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (coreNbrs G u).filter (IsGood G)

lemma mem_badNbrs {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ badNbrs G u ↔ G.Adj u v ∧ IsBad G v := by
  simp only [badNbrs, Finset.mem_filter, mem_coreNbrs]
  exact ⟨fun ⟨⟨h, _⟩, hb⟩ => ⟨h, hb⟩, fun ⟨h, hb⟩ => ⟨⟨h, by have := hb.1; omega⟩, hb⟩⟩

lemma mem_goodNbrs {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ goodNbrs G u ↔ G.Adj u v ∧ IsGood G v := by
  simp only [goodNbrs, Finset.mem_filter, mem_coreNbrs]
  exact ⟨fun ⟨⟨h, _⟩, hg⟩ => ⟨h, hg⟩,
    fun ⟨h, hg⟩ => ⟨⟨h, by have := deg_ge_three_of_isGood hg; omega⟩, hg⟩⟩

lemma badNbrs_disjoint_goodNbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Disjoint (badNbrs G u) (goodNbrs G u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  rw [mem_badNbrs] at h1; rw [mem_goodNbrs] at h2
  have := h1.2.2; unfold IsGood at h2; omega

lemma degThreePlusNbrs_eq_bad_union_good {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) (u : V) :
    degThreePlusNbrs G u = badNbrs G u ∪ goodNbrs G u := by
  ext v
  simp only [degThreePlusNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
    Finset.mem_union, mem_badNbrs, mem_goodNbrs]
  constructor
  · rintro ⟨huv, hdv⟩
    rcases good_or_bad_of_deg_ge_three hm hpq hdv with hg | hb
    · exact Or.inr ⟨huv, hg⟩
    · exact Or.inl ⟨huv, hb⟩
  · rintro (⟨huv, hb⟩ | ⟨huv, hg⟩)
    · exact ⟨huv, by have := hb.1; omega⟩
    · exact ⟨huv, deg_ge_three_of_isGood hg⟩

/-- 极小反例中任意顶点的核心度精确五分恒等式：
`coreDeg = |1-th| + |2-th| + |3-th| + |bad| + |good|`。 -/
lemma coreDeg_eq_five_parts {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) (u : V) :
    coreDeg G u = (oneThreadNbrs G u).card + (twoThreadNbrs G u).card +
      (threeThreadNbrs G u).card + (badNbrs G u).card + (goodNbrs G u).card := by
  classical
  have h1 := coreDeg_eq_degTwo_add_degThreePlus G u
  have h2 : (degTwoNbrs G u).card =
      (oneThreadNbrs G u).card + (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
    rw [degTwoNbrs_eq_one_union_long hm u,
        Finset.card_union_of_disjoint (oneThreadNbrs_disjoint_longThreadNbrs G u),
        longThreadNbrs_eq_two_union_three hm u,
        Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
    omega
  have h3 : (degThreePlusNbrs G u).card = (badNbrs G u).card + (goodNbrs G u).card := by
    rw [degThreePlusNbrs_eq_bad_union_good hm hpq u,
        Finset.card_union_of_disjoint (badNbrs_disjoint_goodNbrs G u)]
  omega

/-! ## 2. `22/9` 放电使用的核心 `q = 3` 顶点分类谓词 -/

/-- `T3` 顶点：`coreDeg = 3` 且关联 `3`-线串（自动推出 `d_G ≥ 4, t3 = 1, t2 = a = b = 0, g = 2`）。 -/
def IsT3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  coreDeg G u = 3 ∧ (threeThreadNbrs G u).Nonempty

/-- `T21` 顶点：`coreDeg = 3` 且同时关联 `2`-线串与 `1`-线串（自动推出 `d_G = 4, h = 1, g = 1`）。 -/
def IsT21 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  coreDeg G u = 3 ∧ (twoThreadNbrs G u).Nonempty ∧ (oneThreadNbrs G u).Nonempty

/-- `T20` 顶点：`coreDeg = 3`、关联 `2`-线串且无 `1`-线串（自动推出 `d_G ≥ 4, t2 = 1, g = 2`）。 -/
def IsT20 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  coreDeg G u = 3 ∧ (twoThreadNbrs G u).Nonempty ∧ oneThreadNbrs G u = ∅

/-- `L3` 顶点：`d_G = 3` 且关联 `3` 条 `1`-线串。 -/
def IsL3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  G.degree u = 3 ∧ (oneThreadNbrs G u).card = 3

/-- `B3` 顶点：`d_G = 3`、关联 `2` 条 `1`-线串与 `1` 个坏核心邻点。 -/
def IsB3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  G.degree u = 3 ∧ (oneThreadNbrs G u).card = 2 ∧ (badNbrs G u).card = 1

/-- `u` 与 `v` 通过 `1`-线串相连（`u - a - v`，`d(a) = 2`）。 -/
def HasOneThreadBetween {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  ∃ a : V, G.Adj u a ∧ G.degree a = 2 ∧ G.Adj a v ∧ u ≠ v

/-- `u` 与 `v` 通过 `2`-线串相连（`u - x - y - v`，`d(x) = d(y) = 2`）。 -/
def HasTwoThreadBetween {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  ∃ x y : V, G.Adj u x ∧ G.degree x = 2 ∧ G.Adj x y ∧ y ≠ u ∧
    G.degree y = 2 ∧ G.Adj y v ∧ v ≠ x ∧ u ≠ v

/-! ## 3. 结构刻画快捷引理 -/

lemma isT3_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (h : IsT3 G u) :
    4 ≤ G.degree u ∧ (threeThreadNbrs G u).card = 1 ∧ (twoThreadNbrs G u).card = 0 ∧
      (oneThreadNbrs G u).card = 0 ∧ (badNbrs G u).card = 0 ∧ (goodNbrs G u).card = 2 := by
  classical
  rcases h with ⟨hc3, hv3⟩
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  rcases hv3 with ⟨v, hv⟩
  have hvlong : v ∈ longThreadNbrs G u := by
    rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_right _ hv
  have hdu4 := deg_ge_four_of_longThreadNbr hm hdu3 hvlong
  have hlong1 := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq hc3
  have hlong_eq : (longThreadNbrs G u).card =
      (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
    rw [longThreadNbrs_eq_two_union_three hm u,
        Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
  have ht3_pos : 1 ≤ (threeThreadNbrs G u).card := Finset.card_pos.mpr ⟨v, hv⟩
  have hsum := (good_coreDeg_three_long_thread_summary hm hpq hc3).1 ⟨v, hv⟩
  have h1c : (oneThreadNbrs G u).card = 0 := by rw [hsum.1, Finset.card_empty]
  have hbc : (badNbrs G u).card = 0 := by
    rw [badNbrs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun b hb => hsum.2 b hb
  have hfive := coreDeg_eq_five_parts hm hpq u
  omega

lemma isT21_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (h : IsT21 G u) :
    G.degree u = 4 ∧ (leafNbrs G u).card = 1 ∧ (threeThreadNbrs G u).card = 0 ∧
      (twoThreadNbrs G u).card = 1 ∧ (oneThreadNbrs G u).card = 1 ∧
      (badNbrs G u).card = 0 ∧ (goodNbrs G u).card = 1 := by
  classical
  rcases h with ⟨hc3, ⟨v, hv2⟩, ⟨a, ha1⟩⟩
  have hvlong : v ∈ longThreadNbrs G u := by
    rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_left _ hv2
  have hdu4 := (thread_reduction hm hc3 hvlong ha1).1
  have hleaf : (leafNbrs G u).card = 1 := by have := coreDeg_add_leafNbrs hm u; omega
  have hlong1 := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq hc3
  have hlong_eq : (longThreadNbrs G u).card =
      (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
    rw [longThreadNbrs_eq_two_union_three hm u,
        Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
  have ht2_pos : 1 ≤ (twoThreadNbrs G u).card := Finset.card_pos.mpr ⟨v, hv2⟩
  have h1_pos : 1 ≤ (oneThreadNbrs G u).card := Finset.card_pos.mpr ⟨a, ha1⟩
  have hsum := (good_coreDeg_three_long_thread_summary hm hpq hc3).2 ⟨v, hv2⟩
  have hbc : (badNbrs G u).card = 0 := by
    rw [badNbrs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun b hb => hsum.2 b hb
  have hfive := coreDeg_eq_five_parts hm hpq u
  omega

lemma isT20_structure {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (h : IsT20 G u) :
    4 ≤ G.degree u ∧ (threeThreadNbrs G u).card = 0 ∧ (twoThreadNbrs G u).card = 1 ∧
      (oneThreadNbrs G u).card = 0 ∧ (badNbrs G u).card = 0 ∧ (goodNbrs G u).card = 2 := by
  classical
  rcases h with ⟨hc3, ⟨v, hv2⟩, h1e⟩
  have hdu3 : 3 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hvlong : v ∈ longThreadNbrs G u := by
    rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_left _ hv2
  have hdu4 := deg_ge_four_of_longThreadNbr hm hdu3 hvlong
  have hlong1 := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq hc3
  have hlong_eq : (longThreadNbrs G u).card =
      (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
    rw [longThreadNbrs_eq_two_union_three hm u,
        Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
  have ht2_pos : 1 ≤ (twoThreadNbrs G u).card := Finset.card_pos.mpr ⟨v, hv2⟩
  have h1c : (oneThreadNbrs G u).card = 0 := by rw [h1e, Finset.card_empty]
  have hsum := (good_coreDeg_three_long_thread_summary hm hpq hc3).2 ⟨v, hv2⟩
  have hbc : (badNbrs G u).card = 0 := by
    rw [badNbrs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun b hb => hsum.2 b hb
  have hfive := coreDeg_eq_five_parts hm hpq u
  omega

lemma mem_oneThreadNbrs {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u a : V} :
    a ∈ oneThreadNbrs G u ↔ IsOneThreadStart G u a := by
  classical
  simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

lemma mem_twoThreadNbrs {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ twoThreadNbrs G u ↔ IsTwoThreadStart G u x := by
  classical
  simp only [twoThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

lemma mem_threeThreadNbrs {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ threeThreadNbrs G u ↔ IsThreeThreadStart G u x := by
  classical
  simp only [threeThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

/-- 若 `a ∈ oneThreadNbrs G u`（且 `3 ≤ d(u)`），则 `a` 的另一邻点 `v` 是 `3⁺`-度点，
且 `u ≠ v`、`HasOneThreadBetween G u v`、`threadAnchors G a = {u, v}`。 -/
lemma oneThreadNbr_other_endpoint {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u a : V} (hdu : 3 ≤ G.degree u)
    (ha : a ∈ oneThreadNbrs G u) :
    ∃ v : V, G.Adj a v ∧ v ≠ u ∧ 3 ≤ G.degree v ∧
      HasOneThreadBetween G u v ∧ threadAnchors G a = {u, v} := by
  rw [mem_oneThreadNbrs] at ha
  rcases ha with ⟨hua, hda, v, hav, hvu, hdv⟩
  refine ⟨v, hav, hvu, hdv, ⟨a, hua, hda, hav, hvu.symm⟩, ?_⟩
  have hsub : ({u, v} : Finset V) ⊆ threadAnchors G a := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_threadAnchors]
    rcases hx with rfl | rfl
    · exact ⟨hdu, hda, Or.inl hua⟩
    · exact ⟨hdv, hda, Or.inl hav.symm⟩
  symm
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [card_threadAnchors_eq_two hm hda, Finset.card_pair hvu.symm])

/-- 若 `x ∈ twoThreadNbrs G u`（且 `3 ≤ d(u)`），则沿 `2`-线串 `u - x - y - v` 的对端 `v` 满足
`u ≠ v`、`3 ≤ d(v)`、`HasTwoThreadBetween G u v`，且 `x, y` 的双锚点均为 `{u, v}`。 -/
lemma twoThreadNbr_other_endpoint {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u x : V} (hdu : 3 ≤ G.degree u)
    (hx : x ∈ twoThreadNbrs G u) :
    ∃ y v : V, G.Adj u x ∧ G.degree x = 2 ∧ G.Adj x y ∧ y ≠ u ∧ G.degree y = 2 ∧
      G.Adj y v ∧ v ≠ x ∧ u ≠ v ∧ 3 ≤ G.degree v ∧
      HasTwoThreadBetween G u v ∧
      threadAnchors G x = {u, v} ∧ threadAnchors G y = {u, v} := by
  rw [mem_twoThreadNbrs] at hx
  rcases hx with ⟨hux, hdx, y, v, hxy, hyu, hdy, hyv, hvx, hdv⟩
  have huv : u ≠ v := fun h =>
    no_two_thread_same_anchor hm hdu hdx hdy hux hxy (h ▸ hyv)
  have hax : threadAnchors G x = {u, v} := by
    have hsub : ({u, v} : Finset V) ⊆ threadAnchors G x := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_threadAnchors]
      rcases ht with rfl | rfl
      · exact ⟨hdu, hdx, Or.inl hux⟩
      · exact ⟨hdv, hdx, Or.inr (Or.inl ⟨y, hdy, hyv.symm, hxy.symm, hvx.symm⟩)⟩
    symm
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [card_threadAnchors_eq_two hm hdx, Finset.card_pair huv])
  have hay : threadAnchors G y = {u, v} := by
    have hsub : ({u, v} : Finset V) ⊆ threadAnchors G y := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_threadAnchors]
      rcases ht with rfl | rfl
      · exact ⟨hdu, hdy, Or.inr (Or.inl ⟨x, hdx, hux, hxy, hyu⟩)⟩
      · exact ⟨hdv, hdy, Or.inl hyv.symm⟩
    symm
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [card_threadAnchors_eq_two hm hdy, Finset.card_pair huv])
  exact ⟨y, v, hux, hdx, hxy, hyu, hdy, hyv, hvx, huv, hdv,
    ⟨x, y, hux, hdx, hxy, hyu, hdy, hyv, hvx, huv⟩, hax, hay⟩

end LeanResearch.Proposal3
