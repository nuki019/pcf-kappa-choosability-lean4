/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.ThreeThreadExt

/-!
# 引理 A 推论：`q = 4` 核心顶点长线串好邻点下界（`Q4Ext`）

本模块针对 `mad(G) < 22/9`（即 `9 * p ≤ 22 * q`）的极小反例，证明唯一主定理
`q4_three_thread_good_bound`：
若 `coreDeg G u = 4`、`1 ≤ |threeThreadNbrs G u|` 且
`|twoThreadNbrs G u| + |threeThreadNbrs G u| = 2`，则
`|threeThreadNbrs G u| ≤ |goodNbrs G u|`，从而一次性消灭 `q = 4` 的全部 8 个高代价阻塞配置。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 基础几何、线串拆解与 `(1-线串 ∨ 坏邻点)` 统一打包引理 -/

/-- 不同顶点的 `1`-度叶邻点集合互不相交。 -/
private lemma leafNbrs_disjoint_of_ne {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V} (hne : a ≠ b) :
    Disjoint (leafNbrs G a) (leafNbrs G b) := by
  rw [Finset.disjoint_left]
  intro r hra hrb
  have h1 := mem_leafNbrs.mp hra
  have h2 := mem_leafNbrs.mp hrb
  rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨t, _, huniq⟩
  exact hne ((huniq a h1.1.symm).trans (huniq b h2.1.symm).symm)

/-- 已知 `2`-度点 `v` 的两个不同邻点 `a ≠ b`，则 `v` 的任意邻点必为 `a` 或 `b`。 -/
private lemma deg_two_nbr_all {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v a b : V}
    (hd : G.degree v = 2) (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) :
    ∀ r, G.Adj v r → r = a ∨ r = b := by
  classical
  have hpair := neighborFinset_eq_pair_of_deg_two hd ha hb hab
  intro r hr
  have : r ∈ ({a, b} : Finset V) := by rw [← hpair]; exact (G.mem_neighborFinset v r).mpr hr
  simpa using this

/-- 辅助：`3`-线串起点 `v₁ ∈ threeThreadNbrs G u` 的完整几何拆解。 -/
private lemma threeThread_unpack {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ : V} (hdu : 3 ≤ G.degree u)
    (hv : v₁ ∈ threeThreadNbrs G u) :
    ∃ v₂ v₃ z : V,
      G.Adj u v₁ ∧ G.degree v₁ = 2 ∧
      G.Adj v₁ v₂ ∧ v₂ ≠ u ∧ G.degree v₂ = 2 ∧
      G.Adj v₂ v₃ ∧ v₃ ≠ v₁ ∧ v₃ ≠ u ∧ G.degree v₃ = 2 ∧
      G.Adj v₃ z ∧ z ≠ v₂ ∧ z ≠ u ∧ 4 ≤ G.degree z ∧
      v₃ ∈ longThreadNbrs G z ∧
      (∀ r, G.Adj v₁ r → r = u ∨ r = v₂) ∧
      (∀ r, G.Adj v₂ r → r = v₁ ∨ r = v₃) ∧
      (∀ r, G.Adj v₃ r → r = v₂ ∨ r = z) := by
  classical
  have hv3 := mem_threeThreadNbrs.mp hv
  rcases hv3 with ⟨huv₁, hdv₁, v₂, v₃, z, hv12, hv2u, hdv₂, hv23, hv31, hdv₃, hv3z, hzv2, hdz3⟩
  have hv3u : v₃ ≠ u := fun h => by subst h; omega
  have hzu : z ≠ u := fun h =>
    no_three_thread_same_anchor hm hdu hdv₁ hdv₂ hdv₃ huv₁ hv12 hv23 (h ▸ hv3z) hv31.symm
  have hv3long : v₃ ∈ longThreadNbrs G z := by
    unfold longThreadNbrs degTwoNbrs
    rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hv3z.symm, hdv₃⟩, hv3z.symm, hdv₃, v₂, hv23.symm, hzv2.symm, hdv₂⟩
  have hdz4 : 4 ≤ G.degree z := deg_ge_four_of_longThreadNbr hm hdz3 hv3long
  exact ⟨v₂, v₃, z, huv₁, hdv₁, hv12, hv2u, hdv₂, hv23, hv31, hv3u, hdv₃, hv3z, hzv2, hzu, hdz4,
    hv3long,
    deg_two_nbr_all hdv₁ huv₁.symm hv12 hv2u.symm,
    deg_two_nbr_all hdv₂ hv12.symm hv23 hv31.symm,
    deg_two_nbr_all hdv₃ hv23.symm hv3z hzv2.symm⟩

/-- 辅助：`2`-线串起点 `w₁ ∈ twoThreadNbrs G u` 的完整几何拆解。 -/
private lemma twoThread_unpack {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u w₁ : V} (hdu : 3 ≤ G.degree u)
    (hw : w₁ ∈ twoThreadNbrs G u) :
    ∃ w₂ z : V,
      G.Adj u w₁ ∧ G.degree w₁ = 2 ∧
      G.Adj w₁ w₂ ∧ w₂ ≠ u ∧ G.degree w₂ = 2 ∧
      G.Adj w₂ z ∧ z ≠ w₁ ∧ z ≠ u ∧ 4 ≤ G.degree z ∧
      w₂ ∈ longThreadNbrs G z ∧
      (∀ r, G.Adj w₁ r → r = u ∨ r = w₂) ∧
      (∀ r, G.Adj w₂ r → r = w₁ ∨ r = z) := by
  classical
  have hw2 := mem_twoThreadNbrs.mp hw
  rcases hw2 with ⟨huw₁, hdw₁, w₂, z, hw12, hw2u, hdw₂, hw2z, hzw1, hdz3⟩
  have hzu : z ≠ u := fun h =>
    no_two_thread_same_anchor hm hdu hdw₁ hdw₂ huw₁ hw12 (h ▸ hw2z)
  have hw2long : w₂ ∈ longThreadNbrs G z := by
    unfold longThreadNbrs degTwoNbrs
    rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hw2z.symm, hdw₂⟩, hw2z.symm, hdw₂, w₁, hw12.symm, hzw1.symm, hdw₁⟩
  have hdz4 : 4 ≤ G.degree z := deg_ge_four_of_longThreadNbr hm hdz3 hw2long
  exact ⟨w₂, z, huw₁, hdw₁, hw12, hw2u, hdw₂, hw2z, hzw1, hzu, hdz4, hw2long,
    deg_two_nbr_all hdw₁ huw₁.symm hw12 hw2u.symm,
    deg_two_nbr_all hdw₂ hw12.symm hw2z hzw1.symm⟩

/-- 同一 `3⁺`-度点 `u` 出发的两条不同起点线串，前两步内部顶点两两互异。 -/
private lemma two_step_segs_disjoint {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ w₁ w₂ : V}
    (hdu : 3 ≤ G.degree u) (hvw1 : v₁ ≠ w₁)
    (huv1 : G.Adj u v₁) (hdv1 : G.degree v₁ = 2) (hv12 : G.Adj v₁ v₂) (hdv2 : G.degree v₂ = 2)
    (huw1 : G.Adj u w₁) (hdw1 : G.degree w₁ = 2) (hw12 : G.Adj w₁ w₂) (hdw2 : G.degree w₂ = 2) :
    v₁ ≠ w₂ ∧ v₂ ≠ w₁ ∧ v₂ ≠ w₂ := by
  have hv1w2 : v₁ ≠ w₂ := fun h =>
    no_two_thread_same_anchor hm hdu hdw1 hdw2 huw1 hw12 (h ▸ huv1.symm)
  have hv2w1 : v₂ ≠ w₁ := fun h =>
    no_two_thread_same_anchor hm hdu hdv1 hdv2 huv1 hv12 (h ▸ huw1.symm)
  have hv2w2 : v₂ ≠ w₂ := fun h =>
    no_three_thread_same_anchor hm hdu hdv1 hdv2 hdw1 huv1 hv12 (h ▸ hw12.symm) huw1.symm hvw1
  exact ⟨hv1w2, hv2w1, hv2w2⟩

/-- 同一 `3⁺`-度点 `u` 出发的 `3`-线串与另一不同起点 `2`-线串的内部顶点完全不交。 -/
private lemma three_two_segs_disjoint {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ v₃ w₁ w₂ : V}
    (hdu : 3 ≤ G.degree u) (hvw1 : v₁ ≠ w₁)
    (huv1 : G.Adj u v₁) (hdv1 : G.degree v₁ = 2)
    (hv12 : G.Adj v₁ v₂) (hdv2 : G.degree v₂ = 2)
    (hv23 : G.Adj v₂ v₃) (hv31 : v₃ ≠ v₁) (hdv3 : G.degree v₃ = 2)
    (huw1 : G.Adj u w₁) (hdw1 : G.degree w₁ = 2)
    (hw12 : G.Adj w₁ w₂) (hdw2 : G.degree w₂ = 2) :
    v₁ ≠ w₂ ∧ v₂ ≠ w₁ ∧ v₂ ≠ w₂ ∧ v₃ ≠ w₁ ∧ v₃ ≠ w₂ := by
  rcases two_step_segs_disjoint hm hdu hvw1 huv1 hdv1 hv12 hdv2 huw1 hdw1 hw12 hdw2 with
    ⟨hv1w2, hv2w1, hv2w2⟩
  have hv3w1 : v₃ ≠ w₁ := fun h =>
    no_three_thread_same_anchor hm hdu hdv1 hdv2 hdv3 huv1 hv12 hv23 (h ▸ huw1.symm) hv31.symm
  have hv3w2 : v₃ ≠ w₂ := fun h =>
    no_four_path_of_deg_two hm hdv1 hdv2 hdv3 hdw1 hv12 hv23 (h ▸ hw12.symm) hv31.symm hvw1 hv2w1
  exact ⟨hv1w2, hv2w1, hv2w2, hv3w1, hv3w2⟩

/-- 同一 `3⁺`-度点 `u` 出发的两条不同起点 `3`-线串的内部顶点完全不交。 -/
private lemma three_three_segs_disjoint {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ v₃ w₁ w₂ w₃ : V}
    (hdu : 3 ≤ G.degree u) (hvw1 : v₁ ≠ w₁)
    (huv1 : G.Adj u v₁) (hdv1 : G.degree v₁ = 2)
    (hv12 : G.Adj v₁ v₂) (hdv2 : G.degree v₂ = 2)
    (hv23 : G.Adj v₂ v₃) (hv31 : v₃ ≠ v₁) (hdv3 : G.degree v₃ = 2)
    (huw1 : G.Adj u w₁) (hdw1 : G.degree w₁ = 2)
    (hw12 : G.Adj w₁ w₂) (hdw2 : G.degree w₂ = 2)
    (hw23 : G.Adj w₂ w₃) (hw31 : w₃ ≠ w₁) (hdw3 : G.degree w₃ = 2) :
    v₁ ≠ w₂ ∧ v₁ ≠ w₃ ∧ v₂ ≠ w₁ ∧ v₂ ≠ w₂ ∧ v₂ ≠ w₃ ∧ v₃ ≠ w₁ ∧ v₃ ≠ w₂ ∧ v₃ ≠ w₃ := by
  rcases three_two_segs_disjoint hm hdu hvw1 huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3
    huw1 hdw1 hw12 hdw2 with ⟨hv1w2, hv2w1, hv2w2, hv3w1, hv3w2⟩
  rcases three_two_segs_disjoint hm hdu hvw1.symm huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3
    huv1 hdv1 hv12 hdv2 with ⟨_, _, _, hw3v1, hw3v2⟩
  have hv3w3 : v₃ ≠ w₃ := fun h =>
    no_four_path_of_deg_two hm hdv1 hdv2 hdv3 hdw2 hv12 hv23 (h ▸ hw23.symm)
      hv31.symm hv1w2 hv2w2
  exact ⟨hv1w2, hw3v1.symm, hv2w1, hv2w2, hw3v2.symm, hv3w1, hv3w2, hv3w3⟩

/-- `oneThreadNbrs G u ∪ badNbrs G u` 中的顶点不能等于 `u` 的任何 `3`-线串内部点。 -/
private lemma ab_not_mem_three_seg {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u r v₁ v₂ v₃ : V}
    (hdu : 3 ≤ G.degree u) (hr : r ∈ oneThreadNbrs G u ∪ badNbrs G u)
    (hv1 : v₁ ∈ threeThreadNbrs G u)
    (huv1 : G.Adj u v₁) (hdv1 : G.degree v₁ = 2)
    (hv12 : G.Adj v₁ v₂) (hdv2 : G.degree v₂ = 2)
    (hv23 : G.Adj v₂ v₃) (hv31 : v₃ ≠ v₁) (hdv3 : G.degree v₃ = 2) :
    r ≠ v₁ ∧ r ≠ v₂ ∧ r ≠ v₃ := by
  rcases Finset.mem_union.mp hr with hr1 | hrb
  · have hrv1 : r ≠ v₁ := by
      intro h; subst h
      have hvlong : r ∈ longThreadNbrs G u := by
        rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_right _ hv1
      exact Finset.disjoint_left.mp (oneThreadNbrs_disjoint_longThreadNbrs G u) hr1 hvlong
    rcases mem_oneThreadNbrs.mp hr1 with ⟨hur, _, _, _, _, _⟩
    have hrv2 : r ≠ v₂ := fun h =>
      no_two_thread_same_anchor hm hdu hdv1 hdv2 huv1 hv12 (h ▸ hur.symm)
    have hrv3 : r ≠ v₃ := fun h =>
      no_three_thread_same_anchor hm hdu hdv1 hdv2 hdv3 huv1 hv12 hv23 (h ▸ hur.symm) hv31.symm
    exact ⟨hrv1, hrv2, hrv3⟩
  · have hdr4 : 4 ≤ G.degree r := (mem_badNbrs.mp hrb).2.1
    exact ⟨fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega⟩

/-- `oneThreadNbrs G u ∪ badNbrs G u` 中的顶点不能等于 `u` 的任何 `2`-线串内部点。 -/
private lemma ab_not_mem_two_seg {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u r w₁ w₂ : V}
    (hdu : 3 ≤ G.degree u) (hr : r ∈ oneThreadNbrs G u ∪ badNbrs G u)
    (hw1 : w₁ ∈ twoThreadNbrs G u)
    (huw1 : G.Adj u w₁) (hdw1 : G.degree w₁ = 2)
    (hw12 : G.Adj w₁ w₂) (hdw2 : G.degree w₂ = 2) :
    r ≠ w₁ ∧ r ≠ w₂ := by
  rcases Finset.mem_union.mp hr with hr1 | hrb
  · have hrw1 : r ≠ w₁ := by
      intro h; subst h
      have hwlong : r ∈ longThreadNbrs G u := by
        rw [longThreadNbrs_eq_two_union_three hm u]; exact Finset.mem_union_left _ hw1
      exact Finset.disjoint_left.mp (oneThreadNbrs_disjoint_longThreadNbrs G u) hr1 hwlong
    rcases mem_oneThreadNbrs.mp hr1 with ⟨hur, _, _, _, _, _⟩
    have hrw2 : r ≠ w₂ := fun h =>
      no_two_thread_same_anchor hm hdu hdw1 hdw2 huw1 hw12 (h ▸ hur.symm)
    exact ⟨hrw1, hrw2⟩
  · have hdr4 : 4 ≤ G.degree r := (mem_badNbrs.mp hrb).2.1
    exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩

/-- 任何关联长线串的顶点 `z` 必不同于 `oneThreadNbrs G u ∪ badNbrs G u` 中的任意点。 -/
private lemma longEnd_ne_ab {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u r z t : V} (hr : r ∈ oneThreadNbrs G u ∪ badNbrs G u)
    (hdz4 : 4 ≤ G.degree z) (ht : t ∈ longThreadNbrs G z) : z ≠ r := by
  intro h; subst h
  rcases Finset.mem_union.mp hr with hr1 | hrb
  · have hdr2 : G.degree z = 2 := (mem_oneThreadNbrs.mp hr1).2.1
    omega
  · have hbad : IsBad G z := (mem_badNbrs.mp hrb).2
    have hemp := bad_no_long_thread hm hpq hbad
    rw [hemp] at ht
    exact Finset.notMem_empty t ht

/-- `oneThreadNbrs G u ∪ badNbrs G u` 中任意两顶点互不相邻。 -/
private lemma ab_not_adj {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u r₁ r₂ : V} (hdu : 3 ≤ G.degree u)
    (hr1 : r₁ ∈ oneThreadNbrs G u ∪ badNbrs G u)
    (hr2 : r₂ ∈ oneThreadNbrs G u ∪ badNbrs G u) :
    ¬ G.Adj r₁ r₂ := by
  intro hadj
  rcases Finset.mem_union.mp hr1 with h1 | h1 <;> rcases Finset.mem_union.mp hr2 with h2 | h2
  · rcases mem_oneThreadNbrs.mp h1 with ⟨hur1, hdr1, _, _, _, _⟩
    rcases mem_oneThreadNbrs.mp h2 with ⟨hur2, hdr2, _, _, _, _⟩
    exact no_two_thread_same_anchor hm hdu hdr1 hdr2 hur1 hadj hur2.symm
  · rcases mem_oneThreadNbrs.mp h1 with ⟨hur1, hdr1, _, _, _, _⟩
    have hbad2 : IsBad G r₂ := (mem_badNbrs.mp h2).2
    have hr1_one : r₁ ∈ oneThreadNbrs G r₂ :=
      mem_oneThreadNbrs.mpr
        ⟨hadj.symm, hdr1, u, hur1.symm, G.ne_of_adj (mem_badNbrs.mp h2).1, hdu⟩
    rw [bad_no_one_thread hm hbad2] at hr1_one
    exact Finset.notMem_empty r₁ hr1_one
  · rcases mem_oneThreadNbrs.mp h2 with ⟨hur2, hdr2, _, _, _, _⟩
    have hbad1 : IsBad G r₁ := (mem_badNbrs.mp h1).2
    have hr2_one : r₂ ∈ oneThreadNbrs G r₁ :=
      mem_oneThreadNbrs.mpr
        ⟨hadj, hdr2, u, hur2.symm, G.ne_of_adj (mem_badNbrs.mp h1).1, hdu⟩
    rw [bad_no_one_thread hm hbad1] at hr2_one
    exact Finset.notMem_empty r₂ hr2_one
  · exact no_adjacent_bad hm hpq (mem_badNbrs.mp h1).2 (mem_badNbrs.mp h2).2 hadj

/-- 统一 `(1-线串 ∨ 坏邻点)` 几何拆解：提取唯一外部核心邻点 `ext` 及全邻域刻画。 -/
private lemma ab_geom_unpack {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q)
    {u r : V} (hdu : 3 ≤ G.degree u) (hr : r ∈ oneThreadNbrs G u ∪ badNbrs G u) :
    ∃ ext : V,
      G.Adj u r ∧ G.Adj r ext ∧ ext ≠ u ∧ 3 ≤ G.degree ext ∧
      2 ≤ G.degree r ∧ coreDeg G r = 2 ∧
      (∀ t, G.Adj r t → t = u ∨ t = ext ∨ t ∈ leafNbrs G r) := by
  rcases Finset.mem_union.mp hr with hr1 | hrb
  · rcases mem_oneThreadNbrs.mp hr1 with ⟨hur, hdr, ext, hre, heu, hde3⟩
    have hcr : coreDeg G r = 2 := by
      rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdr]
    refine ⟨ext, hur, hre, heu, hde3, by omega, hcr, ?_⟩
    intro t hrt
    rcases deg_two_nbr_all hdr hur.symm hre heu.symm t hrt with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases mem_badNbrs.mp hrb with ⟨hur, hbad⟩
    have hu_core : u ∈ coreNbrs G r := mem_coreNbrs.mpr ⟨hur.symm, by omega⟩
    have hother : (coreNbrs G r \ {u}).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu_core),
          Finset.card_singleton]
      have h2 := hbad.2; unfold coreDeg at h2; omega
    rcases Finset.card_eq_one.mp hother with ⟨ext, hext_eq⟩
    have hext_mem : ext ∈ coreNbrs G r \ {u} := by rw [hext_eq]; simp
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hext_mem
    have hre : G.Adj r ext := (mem_coreNbrs.mp hext_mem.1).1
    have hde3 : 3 ≤ G.degree ext := bad_coreNbrs_deg_ge_three hm hpq hbad hext_mem.1
    have hcore_eq : coreNbrs G r = {u, ext} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact hu_core
        · exact hext_mem.1
      · rw [Finset.card_pair (Ne.symm hext_mem.2)]; have h2 := hbad.2; unfold coreDeg at h2; omega
    refine ⟨ext, hur, hre, hext_mem.2, hde3, by have := hbad.1; omega, hbad.2, ?_⟩
    intro t hrt
    have hdt1 := degree_ge_one hm t
    by_cases h1 : G.degree t = 1
    · exact Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hrt, h1⟩))
    · have htc : t ∈ coreNbrs G r := mem_coreNbrs.mpr ⟨hrt, by omega⟩
      rw [hcore_eq, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

/-- 统一 `(1-线串 ∨ 坏邻点)` 着色打包引理：
给定外部邻点色 `δ` 与外侧避色 `γ_forb`，输出 `u` 的单个禁色 `forb` 与 `r` 的备选色集 `P`
（`|P| ≥ 2`），使任意 `α ≠ forb` 与 `c ∈ P \ {α}` 都能合法延拓 `r` 及其全部叶点并满足 PCF。 -/
private lemma ab_color_pack {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L)
    {u r ext : V} (hr : r ∈ oneThreadNbrs G u ∪ badNbrs G u)
    (hur : G.Adj u r) (hre : G.Adj r ext) (heu : ext ≠ u)
    (hall : ∀ t, G.Adj r t → t = u ∨ t = ext ∨ t ∈ leafNbrs G r)
    (δ γ_forb : ℕ) :
    ∃ (forb : ℕ) (P : Finset ℕ), 2 ≤ P.card ∧
      ∀ α : ℕ, α ≠ forb → ∀ c ∈ P \ {α},
        c ∈ L r ∧ c ≠ α ∧ c ≠ δ ∧ c ≠ γ_forb ∧
        ∃ aP : V → ℕ, (∀ w ∈ leafNbrs G r, aP w ∈ L w ∧ aP w ≠ c) ∧
          ∀ ψ : V → ℕ, ψ u = α → ψ ext = δ → (∀ w ∈ leafNbrs G r, ψ w = aP w) →
            ∃ w, G.Adj r w ∧ ∀ t, G.Adj r t → ψ t = ψ w → t = w := by
  classical
  rcases Finset.mem_union.mp hr with hr1 | hrb
  · have hdr2 : G.degree r = 2 := (mem_oneThreadNbrs.mp hr1).2.1
    have hleaf_emp : leafNbrs G r = ∅ := leafNbrs_eq_empty_of_deg_le_three hm (by omega)
    have hLr4 : (L r).card = 4 := by rw [hm.list_card r]; simp [kappa, hdr2]
    let P : Finset ℕ := L r \ {δ, γ_forb}
    have hP2 : 2 ≤ P.card := by
      dsimp only [P]
      have h1 := card_sdiff_ge (L r) {δ, γ_forb}
      have h2 := Finset.card_le_two (a := δ) (b := γ_forb); omega
    refine ⟨δ, P, hP2, fun α hαδ c hc => ?_⟩
    simp only [P, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    refine ⟨hc.1.1, hc.2, hc.1.2.1, hc.1.2.2, fun _ => 0, fun w hw => ?_, fun ψ hψu hψe _ => ?_⟩
    · rw [hleaf_emp] at hw; exact False.elim (Finset.notMem_empty w hw)
    · exact pcf_at_of_two_distinct_neighbors hdr2 hur.symm hre heu.symm
        (by rw [hψu, hψe]; exact hαδ)
  · have hbad : IsBad G r := (mem_badNbrs.mp hrb).2
    let Yr := leafNbrs G r
    have hYr_card : Yr.card = G.degree r - 2 := by
      dsimp only [Yr]; have := coreDeg_add_leafNbrs hm r; have := hbad.2; omega
    have hYr2 : 2 ≤ Yr.card := by have := hbad.1; omega
    have hYr_L2 : ∀ w ∈ Yr, (L w).card = 2 := fun w hw => by
      rw [hm.list_card w]; simp [kappa, (mem_leafNbrs.mp hw).2]
    have hLr : (L r).card = G.degree r + 1 := by
      rw [hm.list_card r]; simp [kappa, show G.degree r ≠ 2 by have := hbad.1; omega]
    let Cb : Finset ℕ := L r \ {δ, γ_forb}
    have hCb : Yr.card + 1 ≤ Cb.card := by
      dsimp only [Cb]
      have h1 := card_sdiff_ge (L r) {δ, γ_forb}
      have h2 := Finset.card_le_two (a := δ) (b := γ_forb)
      have := hbad.1; omega
    have hδCb : δ ∉ Cb := by simp [Cb]
    rcases bad_two_color_extension (Y := Yr) (C := Cb) (δ := δ) hYr2 hYr_L2 hCb hδCb with
      ⟨γ₁, γ₂, lam, hγ1, hγ2, hγ12, ⟨a₁, ha1_mem, ha1_u⟩, ⟨a₂, ha2_mem, ha2_u⟩⟩
    refine ⟨lam, {γ₁, γ₂}, by rw [Finset.card_pair hγ12], fun α hαlam c hc => ?_⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hc
    have hcCb : c ∈ Cb := by
      rcases hc.1 with rfl | rfl
      · exact hγ1
      · exact hγ2
    simp only [Cb, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcCb
    have hex_a : ∃ aP : V → ℕ, (∀ w ∈ Yr, aP w ∈ L w ∧ aP w ≠ c) ∧
        (Yr.filter (fun w => aP w = lam)).card + (if δ = lam then 1 else 0) = 1 := by
      rcases hc.1 with rfl | rfl
      · exact ⟨a₁, ha1_mem, ha1_u⟩
      · exact ⟨a₂, ha2_mem, ha2_u⟩
    rcases hex_a with ⟨aP, haP_mem, haP_u⟩
    refine ⟨hcCb.1, hc.2, hcCb.2.1, hcCb.2.2, aP, haP_mem, fun ψ hψu hψe hψYr => ?_⟩
    by_cases hδlam : δ = lam
    · simp only [hδlam, ite_true] at haP_u
      have hzero : (Yr.filter (fun w => aP w = lam)).card = 0 := by omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
      refine ⟨ext, hre, fun t hrt hψt => ?_⟩
      rw [hψe, hδlam] at hψt
      rcases hall t hrt with rfl | rfl | htYr
      · exact False.elim (hαlam (hψu.symm.trans hψt))
      · rfl
      · exact False.elim (hzero htYr ((hψYr t htYr).symm.trans hψt))
    · simp only [hδlam, ite_false] at haP_u
      have hone : (Yr.filter (fun w => aP w = lam)).card = 1 := by omega
      rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
      have hw₀_mem : w₀ ∈ Yr.filter (fun w => aP w = lam) := by rw [hw₀_eq]; simp
      rw [Finset.mem_filter] at hw₀_mem
      refine ⟨w₀, (mem_leafNbrs.mp hw₀_mem.1).1, fun t hrt hψt => ?_⟩
      rw [hψYr w₀ hw₀_mem.1, hw₀_mem.2] at hψt
      rcases hall t hrt with rfl | rfl | htYr
      · exact False.elim (hαlam (hψu.symm.trans hψt))
      · exact False.elim (hδlam (hψe.symm.trans hψt))
      · have hmem : t ∈ Yr.filter (fun w => aP w = lam) :=
          Finset.mem_filter.mpr ⟨htYr, (hψYr t htYr).symm.trans hψt⟩
        rw [hw₀_eq, Finset.mem_singleton] at hmem
        exact hmem

/-- 辅助：`insert x T` 大小为 `n + 1` 且 `T.card ≤ n` 时，必有 `x ∉ T ∧ T.card = n`。 -/
private lemma notMem_and_card_of_card_insert_eq {V : Type*} [DecidableEq V]
    {x : V} {T : Finset V} {n : ℕ} (h1 : (insert x T).card = n + 1) (h2 : T.card ≤ n) :
    x ∉ T ∧ T.card = n := by
  by_cases hx : x ∈ T
  · rw [Finset.insert_eq_of_mem hx] at h1; omega
  · rw [Finset.card_insert_of_notMem hx] at h1; exact ⟨hx, by omega⟩

/-- `mad < 22/9` 的 9 核心点精确矛盾引理：
若 `coreVerts G` 恰含 9 个互异顶点，核心度为两个 `4` 与七个 `2`（和为 `22`），则与 `9*p ≤ 22*q` 矛盾。 -/
private lemma mad_contra_nine_core {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q)
    {a₁ a₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : V}
    (hcore : coreVerts G = {a₁, a₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇})
    (hcard : ({a₁, a₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇} : Finset V).card = 9)
    (ha1 : coreDeg G a₁ = 4) (ha2 : coreDeg G a₂ = 4)
    (hb1 : coreDeg G b₁ = 2) (hb2 : coreDeg G b₂ = 2) (hb3 : coreDeg G b₃ = 2)
    (hb4 : coreDeg G b₄ = 2) (hb5 : coreDeg G b₅ = 2) (hb6 : coreDeg G b₆ = 2)
    (hb7 : coreDeg G b₇ = 2) : False := by
  have hc1 : ({b₇} : Finset V).card ≤ 1 := by simp
  have hc2 : ({b₆, b₇} : Finset V).card ≤ 2 := Finset.card_le_two
  have hc3 : ({b₅, b₆, b₇} : Finset V).card ≤ 3 := card_triple_le b₅ b₆ b₇
  have hc4 : ({b₄, b₅, b₆, b₇} : Finset V).card ≤ 4 := card_quad_le b₄ b₅ b₆ b₇
  have hc5 : ({b₃, b₄, b₅, b₆, b₇} : Finset V).card ≤ 5 :=
    le_trans (Finset.card_insert_le _ _) (by omega)
  have hc6 : ({b₂, b₃, b₄, b₅, b₆, b₇} : Finset V).card ≤ 6 :=
    le_trans (Finset.card_insert_le _ _) (by omega)
  have hc7 : ({b₁, b₂, b₃, b₄, b₅, b₆, b₇} : Finset V).card ≤ 7 :=
    le_trans (Finset.card_insert_le _ _) (by omega)
  have hc8 : ({a₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇} : Finset V).card ≤ 8 :=
    le_trans (Finset.card_insert_le _ _) (by omega)
  rcases notMem_and_card_of_card_insert_eq hcard hc8 with ⟨hn1, hk8⟩
  rcases notMem_and_card_of_card_insert_eq hk8 hc7 with ⟨hn2, hk7⟩
  rcases notMem_and_card_of_card_insert_eq hk7 hc6 with ⟨hn3, hk6⟩
  rcases notMem_and_card_of_card_insert_eq hk6 hc5 with ⟨hn4, hk5⟩
  rcases notMem_and_card_of_card_insert_eq hk5 hc4 with ⟨hn5, hk4⟩
  rcases notMem_and_card_of_card_insert_eq hk4 hc3 with ⟨hn6, hk3⟩
  rcases notMem_and_card_of_card_insert_eq hk3 hc2 with ⟨hn7, hk2⟩
  rcases notMem_and_card_of_card_insert_eq hk2 hc1 with ⟨hn8, _⟩
  have hmad := mad_core_sum_lt hm.mad (coreVerts_nonempty hm)
  have hsum : ∑ v ∈ coreVerts G, (G.neighborFinset v ∩ coreVerts G).card = 22 := by
    have heq : ∀ v : V, (G.neighborFinset v ∩ coreVerts G).card = coreDeg G v := fun _ => rfl
    simp_rw [heq]
    rw [hcore, Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3,
        Finset.sum_insert hn4, Finset.sum_insert hn5, Finset.sum_insert hn6,
        Finset.sum_insert hn7, Finset.sum_insert hn8, Finset.sum_singleton,
        ha1, ha2, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
    rfl
  rw [hsum, hcore, hcard] at hmad
  omega

/-! ## 2. 纯组合双计数与四核心邻点 PCF 校验引理 -/

/-- 若 `u` 的全部邻点为 `n₁, n₂, n₃, n₄` 与叶集 `Y`，且 `γ` 总出现次数为 `1`，则 `u` 满足 PCF。 -/
private lemma pcf_from_leaf_and_four {V : Type*}
    {G : SimpleGraph V} {ψ aY : V → ℕ} {u n₁ n₂ n₃ n₄ : V} {Y : Finset V} {γ : ℕ}
    (h1 : G.Adj u n₁) (h2 : G.Adj u n₂) (h3 : G.Adj u n₃) (h4 : G.Adj u n₄)
    (hYadj : ∀ r ∈ Y, G.Adj u r) (hYψ : ∀ r ∈ Y, ψ r = aY r)
    (hall : ∀ r, G.Adj u r → r = n₁ ∨ r = n₂ ∨ r = n₃ ∨ r = n₄ ∨ r ∈ Y)
    (hcnt : (Y.filter (fun r => aY r = γ)).card +
      ([ψ n₁, ψ n₂, ψ n₃, ψ n₄] : List ℕ).count γ = 1) :
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
    have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
      simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h4γ,
        ite_true, ite_false] at hcnt
      omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    refine ⟨n₁, h1, fun r hur hψ => ?_⟩
    rw [h1γ] at hψ
    rcases hall r hur with rfl | rfl | rfl | rfl | hrY
    · rfl
    · exact False.elim (h2γ hψ)
    · exact False.elim (h3γ hψ)
    · exact False.elim (h4γ hψ)
    · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
  · by_cases h2γ : ψ n₂ = γ
    · have h3γ : ψ n₃ ≠ γ := by
        intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h2γ, h, ite_true] at hcnt
        omega
      have h4γ : ψ n₄ ≠ γ := by
        intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h2γ, h, ite_true] at hcnt
        omega
      have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h4γ,
          ite_true, ite_false] at hcnt
        omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
      refine ⟨n₂, h2, fun r hur hψ => ?_⟩
      rw [h2γ] at hψ
      rcases hall r hur with rfl | rfl | rfl | rfl | hrY
      · exact False.elim (h1γ hψ)
      · rfl
      · exact False.elim (h3γ hψ)
      · exact False.elim (h4γ hψ)
      · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
    · by_cases h3γ : ψ n₃ = γ
      · have h4γ : ψ n₄ ≠ γ := by
          intro h; simp only [List.count_cons, List.count_nil, beq_iff_eq, h3γ, h, ite_true] at hcnt
          omega
        have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
          simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h4γ,
            ite_true, ite_false] at hcnt
          omega
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
        refine ⟨n₃, h3, fun r hur hψ => ?_⟩
        rw [h3γ] at hψ
        rcases hall r hur with rfl | rfl | rfl | rfl | hrY
        · exact False.elim (h1γ hψ)
        · exact False.elim (h2γ hψ)
        · rfl
        · exact False.elim (h4γ hψ)
        · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
      · by_cases h4γ : ψ n₄ = γ
        · have hzero : (Y.filter (fun r => aY r = γ)).card = 0 := by
            simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h4γ,
              ite_true, ite_false] at hcnt
            omega
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
          refine ⟨n₄, h4, fun r hur hψ => ?_⟩
          rw [h4γ] at hψ
          rcases hall r hur with rfl | rfl | rfl | rfl | hrY
          · exact False.elim (h1γ hψ)
          · exact False.elim (h2γ hψ)
          · exact False.elim (h3γ hψ)
          · rfl
          · exact False.elim (hzero hrY ((hYψ r hrY).symm.trans hψ))
        · have hone : (Y.filter (fun r => aY r = γ)).card = 1 := by
            simp only [List.count_cons, List.count_nil, beq_iff_eq, h1γ, h2γ, h3γ, h4γ,
              ite_false] at hcnt
            omega
          rcases Finset.card_eq_one.mp hone with ⟨w₀, hw₀_eq⟩
          have hw₀_mem : w₀ ∈ Y.filter (fun r => aY r = γ) := by rw [hw₀_eq]; simp
          rw [Finset.mem_filter] at hw₀_mem
          refine ⟨w₀, hYadj w₀ hw₀_mem.1, fun r hur hψ => ?_⟩
          rw [hYψ w₀ hw₀_mem.1, hw₀_mem.2] at hψ
          rcases hall r hur with rfl | rfl | rfl | rfl | hrY
          · exact False.elim (h1γ hψ)
          · exact False.elim (h2γ hψ)
          · exact False.elim (h3γ hψ)
          · exact False.elim (h4γ hψ)
          · have : r ∈ Y.filter (fun t => aY t = γ) :=
              Finset.mem_filter.mpr ⟨hrY, (hYψ r hrY).symm.trans hψ⟩
            rw [hw₀_eq, Finset.mem_singleton] at this; exact this

/-- 情形 1 纯组合双计数延拓引擎（`B = [φx]`，两条 `3`-线串 + 一条 `ab` 支路 + 叶集 `Y`）。 -/
private lemma q4_case1_comb {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {C P_ab : Finset ℕ}
    {F₁ F₂ : ℕ → Finset ℕ} {φx : ℕ}
    (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hF1_ne : ∀ α, (F₁ α).Nonempty) (hF2_ne : ∀ α, (F₂ α).Nonempty)
    (hF1_le : (C.filter (fun α => (F₁ α).card = 1)).card ≤ 1)
    (hF2_le : (C.filter (fun α => (F₂ α).card = 1)).card ≤ 1)
    (hPab : 2 ≤ P_ab.card) (hC : Y.card + 2 ≤ C.card) :
    ∃ α ∈ C, ∃ c₁ ∈ F₁ α, ∃ d₁ ∈ F₂ α, ∃ c_ab ∈ P_ab \ {α},
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, d₁, c_ab, φx] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → {r : V // r ∈ Y} ⊕ Fin 3 → Finset ℕ := fun α s =>
    match s with
    | Sum.inl r => L r.val \ {α}
    | Sum.inr ⟨0, _⟩ => F₁ α
    | Sum.inr ⟨1, _⟩ => F₂ α
    | Sum.inr ⟨2, _⟩ => P_ab \ {α}
  have hA_ne : ∀ α s, (A α s).Nonempty := by
    intro α s; rcases s with r | i
    · dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}; have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
    · fin_cases i
      · exact hF1_ne α
      · exact hF2_ne α
      · dsimp only [A]; rw [← Finset.card_pos]
        have h1 := card_sdiff_ge P_ab {α}; simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C, ¬ ∃ f, IsPCFRep (A α) [φx] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (Sum.inl ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (Sum.inl ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt : (Y.filter (fun r => aY r = γ)).card +
        ([f (Sum.inr 0), f (Sum.inr 1), f (Sum.inr 2), φx] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 3 => f s = γ)).card =
          (Y.filter (fun r => aY r = γ)).card +
          (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) +
          (if f (Sum.inr 2) = γ then 1 else 0) := by
        rw [Finset.card_filter, Fintype.sum_sum_type]
        have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
        have hR : ∑ i : Fin 3, (if f (Sum.inr i) = γ then 1 else 0) =
            (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) +
            (if f (Sum.inr 2) = γ then 1 else 0) := by
          rw [hu3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_singleton]; omega
        have hL : ∑ r : {r // r ∈ Y}, (if f (Sum.inl r) = γ then 1 else 0) =
            (Y.filter (fun r => aY r = γ)).card := by
          rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
          apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
        rw [hL, hR]; omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq] at hγ ⊢
      omega
    exact hno α hα (f (Sum.inr 0)) (hf_mem (Sum.inr 0)) (f (Sum.inr 1)) (hf_mem (Sum.inr 1))
      (f (Sum.inr 2)) (hf_mem (Sum.inr 2)) aY haY γ hcnt
  have hlower : 3 * C.card ≤
      ∑ α ∈ C, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 3 => (A α s).card = 1)).card := by
    calc 3 * C.card = ∑ _α ∈ C, 3 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        (no_pcfRep_single_bounds (hA_ne α) (hno_rep α hα)).2.2.1
          (by rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]; omega)
  have hupper :
      ∑ α ∈ C, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 3 => (A α s).card = 1)).card ≤
        2 * Y.card + 4 := by
    rw [sum_filter_card_comm, Fintype.sum_sum_type]
    have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    have hR : ∑ i : Fin 3, (C.filter (fun α => (A α (Sum.inr i)).card = 1)).card ≤ 4 := by
      rw [hu3, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      have hP := (card_filter_sdiff_singleton_eq_one_le C P_ab hPab).1
      dsimp only [A]; omega
    have hL : ∑ r : {r // r ∈ Y}, (C.filter (fun α => (A α (Sum.inl r)).card = 1)).card ≤
        2 * Y.card := by
      have heq : ∑ r : {r // r ∈ Y}, (C.filter (fun α => (A α (Sum.inl r)).card = 1)).card =
          ∑ r ∈ Y, (C.filter (fun α => (L r \ {α}).card = 1)).card := by
        rw [← Finset.sum_attach Y (fun r => (C.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
      rw [heq]
      calc ∑ r ∈ Y, (C.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    omega
  omega

/-- 情形 2 纯组合双计数延拓引擎（`B = []`，两长线串单点上界 `1` 与 `3` + 两条 `ab` 支路 + 叶集 `Y`）。 -/
private lemma q4_case2_comb {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {C P₁ P₂ : Finset ℕ}
    {F₁ F₂ : ℕ → Finset ℕ}
    (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hF1_ne : ∀ α, (F₁ α).Nonempty) (hF2_ne : ∀ α, (F₂ α).Nonempty)
    (hF1_le : (C.filter (fun α => (F₁ α).card = 1)).card ≤ 1)
    (hF2_le : (C.filter (fun α => (F₂ α).card = 1)).card ≤ 3)
    (hP1 : 2 ≤ P₁.card) (hP2 : 2 ≤ P₂.card) (hC : Y.card + 3 ≤ C.card) :
    ∃ α ∈ C, ∃ c₁ ∈ F₁ α, ∃ d₁ ∈ F₂ α, ∃ c_ab1 ∈ P₁ \ {α}, ∃ c_ab2 ∈ P₂ \ {α},
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card +
      ([c₁, d₁, c_ab1, c_ab2] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → {r : V // r ∈ Y} ⊕ Fin 4 → Finset ℕ := fun α s =>
    match s with
    | Sum.inl r => L r.val \ {α}
    | Sum.inr ⟨0, _⟩ => F₁ α
    | Sum.inr ⟨1, _⟩ => F₂ α
    | Sum.inr ⟨2, _⟩ => P₁ \ {α}
    | Sum.inr ⟨3, _⟩ => P₂ \ {α}
  have hA_ne : ∀ α s, (A α s).Nonempty := by
    intro α s; rcases s with r | i
    · dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}; have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
    · fin_cases i
      · exact hF1_ne α
      · exact hF2_ne α
      · dsimp only [A]; rw [← Finset.card_pos]
        have h1 := card_sdiff_ge P₁ {α}; simp only [Finset.card_singleton] at h1; omega
      · dsimp only [A]; rw [← Finset.card_pos]
        have h1 := card_sdiff_ge P₂ {α}; simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C, ¬ ∃ f, IsPCFRep (A α) [] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (Sum.inl ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (Sum.inl ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt : (Y.filter (fun r => aY r = γ)).card +
        ([f (Sum.inr 0), f (Sum.inr 1), f (Sum.inr 2), f (Sum.inr 3)] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 4 => f s = γ)).card =
          (Y.filter (fun r => aY r = γ)).card +
          (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) +
          (if f (Sum.inr 2) = γ then 1 else 0) + (if f (Sum.inr 3) = γ then 1 else 0) := by
        rw [Finset.card_filter, Fintype.sum_sum_type]
        have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
        have hR : ∑ i : Fin 4, (if f (Sum.inr i) = γ then 1 else 0) =
            (if f (Sum.inr 0) = γ then 1 else 0) + (if f (Sum.inr 1) = γ then 1 else 0) +
            (if f (Sum.inr 2) = γ then 1 else 0) + (if f (Sum.inr 3) = γ then 1 else 0) := by
          rw [hu4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]; omega
        have hL : ∑ r : {r // r ∈ Y}, (if f (Sum.inl r) = γ then 1 else 0) =
            (Y.filter (fun r => aY r = γ)).card := by
          rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
          apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
        rw [hL, hR]; omega
      simp only [List.count_cons, List.count_nil, beq_iff_eq, add_zero] at hγ ⊢
      omega
    exact hno α hα (f (Sum.inr 0)) (hf_mem (Sum.inr 0)) (f (Sum.inr 1)) (hf_mem (Sum.inr 1))
      (f (Sum.inr 2)) (hf_mem (Sum.inr 2)) (f (Sum.inr 3)) (hf_mem (Sum.inr 3)) aY haY γ hcnt
  have hlower : 4 * C.card ≤
      ∑ α ∈ C, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 4 => (A α s).card = 1)).card := by
    calc 4 * C.card = ∑ _α ∈ C, 4 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        (no_pcfRep_nil_bounds (hA_ne α) (hno_rep α hα)).2
          (by rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]; omega)
  have hupper :
      ∑ α ∈ C, (Finset.univ.filter (fun s : {r // r ∈ Y} ⊕ Fin 4 => (A α s).card = 1)).card ≤
        2 * Y.card + 8 := by
    rw [sum_filter_card_comm, Fintype.sum_sum_type]
    have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    have hR : ∑ i : Fin 4, (C.filter (fun α => (A α (Sum.inr i)).card = 1)).card ≤ 8 := by
      rw [hu4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      have h1 := (card_filter_sdiff_singleton_eq_one_le C P₁ hP1).1
      have h2 := (card_filter_sdiff_singleton_eq_one_le C P₂ hP2).1
      dsimp only [A]; omega
    have hL : ∑ r : {r // r ∈ Y}, (C.filter (fun α => (A α (Sum.inl r)).card = 1)).card ≤
        2 * Y.card := by
      have heq : ∑ r : {r // r ∈ Y}, (C.filter (fun α => (A α (Sum.inl r)).card = 1)).card =
          ∑ r ∈ Y, (C.filter (fun α => (L r \ {α}).card = 1)).card := by
        rw [← Finset.sum_attach Y (fun r => (C.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
      rw [heq]
      calc ∑ r ∈ Y, (C.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    omega
  omega

/-! ## 3. 情形 1：`g = 1, t₃ = 2, t₂ = 0, a + b = 1` -/

private lemma q4_case_good_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u : V}
    (hc4 : coreDeg G u = 4)
    (ht3 : (threeThreadNbrs G u).card = 2)
    (hgood1 : (goodNbrs G u).card = 1)
    (hab1 : (oneThreadNbrs G u).card + (badNbrs G u).card = 1) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hdu4 : 4 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hdu3 : 3 ≤ G.degree u := by omega
  -- 拆出两条 `3`-线串 `v₁ ≠ w₁`、唯一好邻点 `x` 与唯一 `ab ∈ oneThreadNbrs ∪ badNbrs`
  rcases Finset.card_eq_two.mp ht3 with ⟨v₁, w₁, hvw1, ht3_eq⟩
  have hv1_mem : v₁ ∈ threeThreadNbrs G u := by rw [ht3_eq]; simp
  have hw1_mem : w₁ ∈ threeThreadNbrs G u := by rw [ht3_eq]; simp
  rcases threeThread_unpack hm hdu3 hv1_mem with
    ⟨v₂, v₃, zv, huv1, hdv1, hv12, hv2u, hdv2, hv23, hv31, hv3u, hdv3, hv3z, hzv2, hzu, hdzv4,
      hv3long, hall_v1, hall_v2, hall_v3⟩
  rcases threeThread_unpack hm hdu3 hw1_mem with
    ⟨w₂, w₃, zw, huw1, hdw1, hw12, hw2u, hdw2, hw23, hw31, hw3u, hdw3, hw3z, hzw2, hzwu, hdzw4,
      hw3long, hall_w1, hall_w2, hall_w3⟩
  rcases three_three_segs_disjoint hm hdu3 hvw1 huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3
    huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3 with
    ⟨hv1w2, hv1w3, hv2w1, hv2w2, hv2w3, hv3w1, hv3w2, hv3w3⟩
  rcases Finset.card_eq_one.mp hgood1 with ⟨x, hgood_eq⟩
  have hx_mem : x ∈ goodNbrs G u := by rw [hgood_eq]; simp
  have hux : G.Adj u x := (mem_goodNbrs.mp hx_mem).1
  have hxgood : IsGood G x := (mem_goodNbrs.mp hx_mem).2
  have hdx3 : 3 ≤ G.degree x := deg_ge_three_of_isGood hxgood
  have hab_disj : Disjoint (oneThreadNbrs G u) (badNbrs G u) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    have := (mem_oneThreadNbrs.mp h1).2.1; have := (mem_badNbrs.mp h2).2.1; omega
  have hab_card : (oneThreadNbrs G u ∪ badNbrs G u).card = 1 := by
    rw [Finset.card_union_of_disjoint hab_disj]; exact hab1
  rcases Finset.card_eq_one.mp hab_card with ⟨ab, hab_eq⟩
  have hab_mem : ab ∈ oneThreadNbrs G u ∪ badNbrs G u := by rw [hab_eq]; simp
  rcases ab_geom_unpack hm hpq25 hdu3 hab_mem with
    ⟨e, huab, habe, heu, hde3, hdab2, hcab2, hall_ab⟩
  rcases ab_not_mem_three_seg hm hdu3 hab_mem hv1_mem huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3 with
    ⟨habv1, habv2, habv3⟩
  rcases ab_not_mem_three_seg hm hdu3 hab_mem hw1_mem huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3 with
    ⟨habw1, habw2, habw3⟩
  have hxab : x ≠ ab := by
    intro h; subst h
    rcases Finset.mem_union.mp hab_mem with h1 | h2
    · have := (mem_oneThreadNbrs.mp h1).2.1; omega
    · have := (mem_badNbrs.mp h2).2.2; unfold IsGood at hxgood; omega
  have hxv1 : x ≠ v₁ := fun h => by subst h; omega
  have hxw1 : x ≠ w₁ := fun h => by subst h; omega
  have hcore_u : coreNbrs G u = {v₁, w₁, x, ab} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huw1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨hux, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huab, hdab2⟩
    · rw [Finset.card_insert_of_notMem (by simp [hvw1, hxv1.symm, habv1.symm]),
          Finset.card_insert_of_notMem (by simp [hxw1.symm, habw1.symm]),
          Finset.card_pair hxab]
      unfold coreDeg at hc4; omega
  let Y := leafNbrs G u
  let Pab := leafNbrs G ab
  have hY_Pab_disj : Disjoint Y Pab := leafNbrs_disjoint_of_ne (G.ne_of_adj huab)
  have hall_u : ∀ r, G.Adj u r → r = v₁ ∨ r = w₁ ∨ r = x ∨ r = ab ∨ r ∈ Y := by
    intro r hur
    have hdr1 := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, h1⟩))))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_u, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  -- 删点集 `S` 与边界刻画
  let S : Finset V :=
    insert u (insert v₁ (insert v₂ (insert v₃ (insert w₁ (insert w₂ (insert w₃
      (insert ab (Y ∪ Pab))))))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have habS : ab ∈ S := by simp [S]
  have hnot_YP : ∀ r : V, 2 ≤ G.degree r → r ∉ Y ∧ r ∉ Pab := fun r hdr =>
    ⟨fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hzv_ab : zv ≠ ab := longEnd_ne_ab hm hpq25 hab_mem hdzv4 hv3long
  have hzw_ab : zw ≠ ab := longEnd_ne_ab hm hpq25 hab_mem hdzw4 hw3long
  have hx_not_S : x ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hYP := hnot_YP x (by omega)
    exact ⟨(G.ne_of_adj hux).symm, hxv1, fun h => by subst h; omega, fun h => by subst h; omega,
      hxw1, fun h => by subst h; omega, fun h => by subst h; omega, hxab, hYP.1, hYP.2⟩
  have hzv_not_S : zv ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hYP := hnot_YP zv (by omega)
    exact ⟨hzu, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      hzv_ab, hYP.1, hYP.2⟩
  have hzw_not_S : zw ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hYP := hnot_YP zw (by omega)
    exact ⟨hzwu, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      hzw_ab, hYP.1, hYP.2⟩
  have he_not_S : e ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hYP := hnot_YP e (by omega)
    exact ⟨heu, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      (G.ne_of_adj habe).symm, hYP.1, hYP.2⟩
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = u ∧ s = x) ∨ (r = v₃ ∧ s = zv) ∨ (r = w₃ ∧ s = zw) ∨ (r = ab ∧ s = e) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY | hrP
    · rcases hall_u s hsr.symm with rfl | rfl | rfl | rfl | hsY
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S, hsY]))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rcases hall_ab s hsr.symm with rfl | rfl | hsP
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact False.elim (hsS (by simp [S, Pab, hsP]))
    · have hL := mem_leafNbrs.mp hrY
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq u hL.1.symm).symm) ▸ huS))
    · have hL := mem_leafNbrs.mp hrP
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq ab hL.1.symm).symm) ▸ habS))
  -- 分是否出现 `G - S` 孤立点
  by_cases hiso_ex : ∃ s ∉ S, ∀ t ∉ S, ¬ G.Adj s t
  · rcases hiso_ex with ⟨s, hsS, hs_iso⟩
    have hs_nbr_S : ∀ r, G.Adj s r → r ∈ S := fun r hsr => by
      by_contra h; exact hs_iso r h hsr
    have hpos : 0 < (G.neighborFinset s).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree_ge_one hm s; omega
    rcases Finset.card_pos.mp hpos with ⟨r₀, hr₀⟩
    have hsr0 : G.Adj s r₀ := (G.mem_neighborFinset s r₀).mp hr₀
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ (hs_nbr_S r₀ hsr0) hsr0 with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hds4 : 4 ≤ G.degree s := by
      by_contra hlt; push Not at hlt
      have hsub2 : G.neighborFinset s ⊆ {u, ab} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        rcases hS_out s hsS r (hs_nbr_S r hr) hr with
          ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩
        · simp
        · omega
        · omega
        · simp
      have h1 := Finset.card_le_card hsub2
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 := Finset.card_le_two (a := u) (b := ab); omega
    have hsub4 : G.neighborFinset s ⊆ {u, v₃, w₃, ab} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      rcases hS_out s hsS r (hs_nbr_S r hr) hr with
        ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hcard4 : ({u, v₃, w₃, ab} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hv3u.symm, hw3u.symm, G.ne_of_adj huab]),
          Finset.card_insert_of_notMem (by simp [hv3w3, habv3.symm]),
          Finset.card_pair habw3.symm]
    have hNs_eq : G.neighborFinset s = {u, v₃, w₃, ab} :=
      Finset.eq_of_subset_of_card_le hsub4
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hcard4]; omega)
    have hsu : G.Adj s u := (G.mem_neighborFinset s u).mp (by rw [hNs_eq]; simp)
    have hsv3 : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hNs_eq]; simp)
    have hsw3 : G.Adj s w₃ := (G.mem_neighborFinset s w₃).mp (by rw [hNs_eq]; simp)
    have hsab : G.Adj s ab := (G.mem_neighborFinset s ab).mp (by rw [hNs_eq]; simp)
    have hs_eq_x : s = x := by
      rcases hS_out s hsS u huS hsu with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hv3u h.symm)
      · exact False.elim (hw3u h.symm)
      · exact False.elim (G.ne_of_adj huab h)
    have hs_eq_zv : s = zv := by
      rcases hS_out s hsS v₃ (by simp [S]) hsv3 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (hv3u h)
      · exact h
      · exact False.elim (hv3w3 h)
      · exact False.elim (habv3 h.symm)
    have hs_eq_zw : s = zw := by
      rcases hS_out s hsS w₃ (by simp [S]) hsw3 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim (hw3u h)
      · exact False.elim (hv3w3 h.symm)
      · exact h
      · exact False.elim (habw3 h.symm)
    have hs_eq_e : s = e := by
      rcases hS_out s hsS ab habS hsab with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (G.ne_of_adj huab h.symm)
      · exact False.elim (habv3 h)
      · exact False.elim (habw3 h)
      · exact h
    have huniv : insert s S = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := u) (Finset.mem_insert_of_mem huS)
      intro a ha b hab
      rcases Finset.mem_insert.mp ha with rfl | haS
      · exact Finset.mem_insert_of_mem (hs_nbr_S b hab)
      · by_cases hbS : b ∈ S
        · exact Finset.mem_insert_of_mem hbS
        · rcases hS_out b hbS a haS hab.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · rw [← hs_eq_x]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_zv]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_zw]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_e]; exact Finset.mem_insert_self s S
    have hcore_eq : coreVerts G = {u, s, v₁, v₂, v₃, w₁, w₂, w₃, ab} := by
      ext r
      simp only [mem_coreVerts, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hdr2
        have hmem : r ∈ insert s S := by rw [huniv]; exact Finset.mem_univ r
        simp only [S, Finset.mem_insert, Finset.mem_union] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY | hrP
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
        · rw [mem_leafNbrs] at hrY; omega
        · rw [mem_leafNbrs] at hrP; omega
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
    have hcore_s : coreDeg G s = 4 := by
      unfold coreDeg coreNbrs
      have hsub_core : G.neighborFinset s ⊆ coreVerts G := by
        intro r hr; rw [hNs_eq] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rw [mem_coreVerts]
        rcases hr with rfl | rfl | rfl | rfl <;> omega
      rw [Finset.inter_eq_left.mpr hsub_core, hNs_eq, hcard4]
    have hcard9 : ({u, s, v₁, v₂, v₃, w₁, w₂, w₃, ab} : Finset V).card = 9 := by
      have hsn : s ∉ ({v₁, v₂, v₃, w₁, w₂, w₃, ab} : Finset V) := fun h => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hsS (by simp [S])
      have hun : u ∉ ({s, v₁, v₂, v₃, w₁, w₂, w₃, ab} : Finset V) := fun h => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hsS huS
        · exact G.ne_of_adj huv1 rfl
        · exact hv2u rfl
        · exact hv3u rfl
        · exact G.ne_of_adj huw1 rfl
        · exact hw2u rfl
        · exact hw3u rfl
        · exact G.ne_of_adj huab rfl
      rw [Finset.card_insert_of_notMem hun, Finset.card_insert_of_notMem hsn,
          Finset.card_insert_of_notMem
            (by simp [G.ne_of_adj hv12, hv31.symm, hvw1, hv1w2, hv1w3, habv1.symm]),
          Finset.card_insert_of_notMem
            (by simp [G.ne_of_adj hv23, hv2w1, hv2w2, hv2w3, habv2.symm]),
          Finset.card_insert_of_notMem (by simp [hv3w1, hv3w2, hv3w3, habv3.symm]),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hw12, hw31.symm, habw1.symm]),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hw23, habw2.symm]),
          Finset.card_pair habw3.symm]
    exact mad_contra_nine_core hm hpq hcore_eq hcard9 hc4 hcore_s
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv1])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv2])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv3])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw1])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw2])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw3])
      hcab2
  · -- 非孤立情形：取 `G - S` 容许染色并调用 `q4_case1_comb`！
    push Not at hiso_ex
    rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm⟩
    rcases ab_color_pack hm hab_mem huab habe heu hall_ab (adm.φ e) (adm.φs e) with
      ⟨forb_ab, P_ab, hPab2, hPab_spec⟩
    have hLu : (L u).card = Y.card + 5 := by
      have h1 := coreDeg_add_leafNbrs hm u
      dsimp only [Y]
      rw [hm.list_card u]; simp only [kappa, show G.degree u ≠ 2 by omega, ite_false]; omega
    have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv1]
    have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv2]
    have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv3]
    have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw1]
    have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw2]
    have hLw3 : (L w₃).card = 4 := by rw [hm.list_card w₃]; simp [kappa, hdw3]
    have hY_L2 : ∀ r ∈ Y, (L r).card = 2 := fun r hr => by
      rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
    let Z₃v : Finset ℕ := L v₃ \ {adm.φ zv, adm.φs zv}
    let Z₃w : Finset ℕ := L w₃ \ {adm.φ zw, adm.φs zw}
    have hZ3v : 2 ≤ Z₃v.card := by
      dsimp only [Z₃v]; have := card_sdiff_ge (L v₃) {adm.φ zv, adm.φs zv}
      have := Finset.card_le_two (a := adm.φ zv) (b := adm.φs zv); omega
    have hZ3w : 2 ≤ Z₃w.card := by
      dsimp only [Z₃w]; have := card_sdiff_ge (L w₃) {adm.φ zw, adm.φs zw}
      have := Finset.card_le_two (a := adm.φ zw) (b := adm.φs zw); omega
    let C : Finset ℕ := L u \ {adm.φ x, adm.φs x, forb_ab}
    have hC : Y.card + 2 ≤ C.card := by
      dsimp only [C]; have := card_sdiff_ge (L u) {adm.φ x, adm.φs x, forb_ab}
      have := card_triple_le (adm.φ x) (adm.φs x) forb_ab; omega
    rcases q4_case1_comb (L := L) (Y := Y) (C := C) (P_ab := P_ab)
      (F₁ := threeThreadGoodCols (L v₁) (L v₂) Z₃v (adm.φ zv))
      (F₂ := threeThreadGoodCols (L w₁) (L w₂) Z₃w (adm.φ zw))
      (φx := adm.φ x) hY_L2
      (fun _ => threeThreadGoodCols_nonempty hLv1 hLv2 (Finset.card_pos.mp (by omega)))
      (fun _ => threeThreadGoodCols_nonempty hLw1 hLw2 (Finset.card_pos.mp (by omega)))
      (threeThreadGoodCols_card_one_le_one C hLv1 hLv2 hZ3v)
      (threeThreadGoodCols_card_one_le_one C hLw1 hLw2 hZ3w)
      hPab2 hC with ⟨α, hαC, c₁, hc₁, d₁, hd₁, c_ab, hc_ab, aY, haY, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁ hd₁
    rcases hc₁ with ⟨⟨hc1L, hc1α⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
    rcases hd₁ with ⟨⟨hd1L, hd1α⟩, d₃, hd3Z, hd31, d₂, hd2B, hd21⟩
    simp only [Z₃v, Z₃w, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hc3Z hd3Z hc2B hd2B
    rcases hPab_spec α hαC.2.2.2 c_ab hc_ab with
      ⟨hcabL, hcabα, hcab_e, hcab_se, aP, haP_mem, haP_pcf⟩
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v₁ then c₁ else if r = v₂ then c₂ else if r = v₃ then c₃
      else if r = w₁ then d₁ else if r = w₂ then d₂ else if r = w₃ then d₃
      else if r = ab then c_ab else if r ∈ Y then aY r else if r ∈ Pab then aP r else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψv1 : ψ v₁ = c₁ := by simp [ψ, (G.ne_of_adj huv1).symm]
    have hψv2 : ψ v₂ = c₂ := by simp [ψ, hv2u, (G.ne_of_adj hv12).symm]
    have hψv3 : ψ v₃ = c₃ := by simp [ψ, hv3u, hv31, (G.ne_of_adj hv23).symm]
    have hψw1 : ψ w₁ = d₁ := by simp [ψ, (G.ne_of_adj huw1).symm, hvw1.symm, hv2w1.symm, hv3w1.symm]
    have hψw2 : ψ w₂ = d₂ := by
      simp [ψ, hw2u, hv1w2.symm, hv2w2.symm, hv3w2.symm, (G.ne_of_adj hw12).symm]
    have hψw3 : ψ w₃ = d₃ := by
      simp [ψ, hw3u, hv1w3.symm, hv2w3.symm, hv3w3.symm, hw31, (G.ne_of_adj hw23).symm]
    have hψab : ψ ab = c_ab := by
      simp [ψ, (G.ne_of_adj huab).symm, habv1, habv2, habv3, habw1, habw2, habw3]
    have hψY : ∀ r ∈ Y, ψ r = aY r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab by intro h; subst h; omega), hr]
    have hψP : ∀ r ∈ Pab, ψ r = aP r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_Pab_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab by intro h; subst h; omega), hrY, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY | hrP
      · rw [hψu]; exact hαC.1
      · rw [hψv1]; exact hc1L
      · rw [hψv2]; exact hc2B.1
      · rw [hψv3]; exact hc3Z.1
      · rw [hψw1]; exact hd1L
      · rw [hψw2]; exact hd2B.1
      · rw [hψw3]; exact hd3Z.1
      · rw [hψab]; exact hcabL
      · rw [hψY r hrY]; exact (haY r hrY).1
      · rw [hψP r hrP]; exact (haP_mem r hrP).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | haY' | haP
        · rcases hall_u b' hab with hb | hb | hb | hb | hbY
          · rw [hb, hψu, hψv1]; exact Ne.symm hc1α
          · rw [hb, hψu, hψw1]; exact Ne.symm hd1α
          · rw [hb, hψu, hψ_out x hx_not_S]; exact hαC.2.1
          · rw [hb, hψu, hψab]; exact Ne.symm hcabα
          · rw [hψu, hψY b' hbY]; exact (haY b' hbY).2.symm
        · rcases hall_v1 b' hab with hb | hb
          · rw [hb, hψv1, hψu]; exact hc1α
          · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
        · rcases hall_v2 b' hab with hb | hb
          · rw [hb, hψv2, hψv1]; exact hc21
          · rw [hb, hψv2, hψv3]; exact hc2B.2.2.1
        · rcases hall_v3 b' hab with hb | hb
          · rw [hb, hψv3, hψv2]; exact Ne.symm hc2B.2.2.1
          · rw [hb, hψv3, hψ_out zv hzv_not_S]; exact hc3Z.2.1
        · rcases hall_w1 b' hab with hb | hb
          · rw [hb, hψw1, hψu]; exact hd1α
          · rw [hb, hψw1, hψw2]; exact Ne.symm hd21
        · rcases hall_w2 b' hab with hb | hb
          · rw [hb, hψw2, hψw1]; exact hd21
          · rw [hb, hψw2, hψw3]; exact hd2B.2.2.1
        · rcases hall_w3 b' hab with hb | hb
          · rw [hb, hψw3, hψw2]; exact Ne.symm hd2B.2.2.1
          · rw [hb, hψw3, hψ_out zw hzw_not_S]; exact hd3Z.2.1
        · rcases hall_ab b' hab with hb | hb | hbP
          · rw [hb, hψab, hψu]; exact hcabα
          · rw [hb, hψab, hψ_out e he_not_S]; exact hcab_e
          · rw [hψab, hψP b' hbP]; exact (haP_mem b' hbP).2.symm
        · have hL := mem_leafNbrs.mp haY'
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u hL.1.symm).symm
          rw [hb, hψY a' haY', hψu]; exact (haY a' haY').2
        · have hL := mem_leafNbrs.mp haP
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab := (huniq b' hab).trans (huniq ab hL.1.symm).symm
          rw [hb, hψP a' haP, hψab]; exact (haP_mem a' haP).2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro s hsS _ r hrS hsr
      rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hψu]; exact hαC.2.2.1
      · rw [hψv3]; exact hc3Z.2.2
      · rw [hψw3]; exact hd3Z.2.2
      · rw [hψab]; exact hcab_se
    · intro s hsS hiso _
      rcases hiso_ex s hsS with ⟨t, htS, hst⟩
      exact False.elim (hiso t htS hst)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hrY | hrP
      · exact pcf_from_leaf_and_four huv1 huw1 huab hux (fun t ht => (mem_leafNbrs.mp ht).1) hψY
          (fun t ht => by
            rcases hall_u t ht with h | h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
          (by rw [hψv1, hψw1, hψab, hψ_out x hx_not_S]; exact hγ)
      · exact pcf_at_of_two_distinct_neighbors hdv1 huv1.symm hv12 hv2u.symm
          (by rw [hψu, hψv2]; exact Ne.symm hc2B.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdv2 hv12.symm hv23 hv31.symm
          (by rw [hψv1, hψv3]; exact Ne.symm hc31)
      · exact pcf_at_of_two_distinct_neighbors hdv3 hv23.symm hv3z hzv2.symm
          (by rw [hψv2, hψ_out zv hzv_not_S]; exact hc2B.2.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdw1 huw1.symm hw12 hw2u.symm
          (by rw [hψu, hψw2]; exact Ne.symm hd2B.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdw2 hw12.symm hw23 hw31.symm
          (by rw [hψw1, hψw3]; exact Ne.symm hd31)
      · exact pcf_at_of_two_distinct_neighbors hdw3 hw23.symm hw3z hzw2.symm
          (by rw [hψw2, hψ_out zw hzw_not_S]; exact hd2B.2.2.2)
      · exact haP_pcf ψ hψu (hψ_out e he_not_S) hψP
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrP).2 (mem_leafNbrs.mp hrP).1.symm

/-! ## 4. 情形 2a：`g = 0, t₃ = 1, t₂ = 1, a + b = 2` -/

private lemma q4_case_good_zero_t2 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u : V}
    (hc4 : coreDeg G u = 4)
    (ht3 : (threeThreadNbrs G u).card = 1)
    (ht2 : (twoThreadNbrs G u).card = 1)
    (hab2 : (oneThreadNbrs G u).card + (badNbrs G u).card = 2) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hdu4 : 4 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hdu3 : 3 ≤ G.degree u := by omega
  rcases Finset.card_eq_one.mp ht3 with ⟨v₁, ht3_eq⟩
  rcases Finset.card_eq_one.mp ht2 with ⟨w₁, ht2_eq⟩
  have hv1_mem : v₁ ∈ threeThreadNbrs G u := by rw [ht3_eq]; simp
  have hw1_mem : w₁ ∈ twoThreadNbrs G u := by rw [ht2_eq]; simp
  have hvw1 : v₁ ≠ w₁ := fun h => by
    subst h
    exact Finset.disjoint_left.mp (twoThreadNbrs_disjoint_threeThreadNbrs G u) hw1_mem hv1_mem
  rcases threeThread_unpack hm hdu3 hv1_mem with
    ⟨v₂, v₃, z₁, huv1, hdv1, hv12, hv2u, hdv2, hv23, hv31, hv3u, hdv3, hv3z, hz1v2, hz1u, hdz14,
      hv3long, hall_v1, hall_v2, hall_v3⟩
  rcases twoThread_unpack hm hdu3 hw1_mem with
    ⟨w₂, z₂, huw1, hdw1, hw12, hw2u, hdw2, hw2z, hz2w1, hz2u, hdz24, hw2long, hall_w1, hall_w2⟩
  rcases three_two_segs_disjoint hm hdu3 hvw1 huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3
    huw1 hdw1 hw12 hdw2 with ⟨hv1w2, hv2w1, hv2w2, hv3w1, hv3w2⟩
  have hab_disj : Disjoint (oneThreadNbrs G u) (badNbrs G u) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    have := (mem_oneThreadNbrs.mp h1).2.1; have := (mem_badNbrs.mp h2).2.1; omega
  have hab_card : (oneThreadNbrs G u ∪ badNbrs G u).card = 2 := by
    rw [Finset.card_union_of_disjoint hab_disj]; exact hab2
  rcases Finset.card_eq_two.mp hab_card with ⟨ab₁, ab₂, hab12, hab_eq⟩
  have hab1_mem : ab₁ ∈ oneThreadNbrs G u ∪ badNbrs G u := by rw [hab_eq]; simp
  have hab2_mem : ab₂ ∈ oneThreadNbrs G u ∪ badNbrs G u := by rw [hab_eq]; simp
  rcases ab_geom_unpack hm hpq25 hdu3 hab1_mem with
    ⟨e₁, huab1, hab1e, he1u, hde13, hdab12, hcab12, hall_ab1⟩
  rcases ab_geom_unpack hm hpq25 hdu3 hab2_mem with
    ⟨e₂, huab2, hab2e, he2u, hde23, hdab22, hcab22, hall_ab2⟩
  have hnotadj_ab : ¬ G.Adj ab₁ ab₂ := ab_not_adj hm hpq25 hdu3 hab1_mem hab2_mem
  have he1ab2 : e₁ ≠ ab₂ := fun h => hnotadj_ab (h ▸ hab1e)
  have he2ab1 : e₂ ≠ ab₁ := fun h => hnotadj_ab (h ▸ hab2e).symm
  rcases ab_not_mem_three_seg hm hdu3 hab1_mem hv1_mem huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3 with
    ⟨hab1v1, hab1v2, hab1v3⟩
  rcases ab_not_mem_three_seg hm hdu3 hab2_mem hv1_mem huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3 with
    ⟨hab2v1, hab2v2, hab2v3⟩
  rcases ab_not_mem_two_seg hm hdu3 hab1_mem hw1_mem huw1 hdw1 hw12 hdw2 with ⟨hab1w1, hab1w2⟩
  rcases ab_not_mem_two_seg hm hdu3 hab2_mem hw1_mem huw1 hdw1 hw12 hdw2 with ⟨hab2w1, hab2w2⟩
  have hcore_u : coreNbrs G u = {v₁, w₁, ab₁, ab₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huw1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huab1, hdab12⟩
      · exact mem_coreNbrs.mpr ⟨huab2, hdab22⟩
    · rw [Finset.card_insert_of_notMem (by simp [hvw1, hab1v1.symm, hab2v1.symm]),
          Finset.card_insert_of_notMem (by simp [hab1w1.symm, hab2w1.symm]),
          Finset.card_pair hab12]
      unfold coreDeg at hc4; omega
  let Y := leafNbrs G u
  let P₁ := leafNbrs G ab₁
  let P₂ := leafNbrs G ab₂
  have hY_P1_disj : Disjoint Y P₁ := leafNbrs_disjoint_of_ne (G.ne_of_adj huab1)
  have hY_P2_disj : Disjoint Y P₂ := leafNbrs_disjoint_of_ne (G.ne_of_adj huab2)
  have hP1_P2_disj : Disjoint P₁ P₂ := leafNbrs_disjoint_of_ne hab12
  have hall_u : ∀ r, G.Adj u r → r = v₁ ∨ r = w₁ ∨ r = ab₁ ∨ r = ab₂ ∨ r ∈ Y := by
    intro r hur
    have hdr1 := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, h1⟩))))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_u, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  let S : Finset V :=
    insert u (insert v₁ (insert v₂ (insert v₃ (insert w₁ (insert w₂
      (insert ab₁ (insert ab₂ (Y ∪ P₁ ∪ P₂))))))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hab1S : ab₁ ∈ S := by simp [S]
  have hab2S : ab₂ ∈ S := by simp [S]
  have hnot_YPP : ∀ r : V, 2 ≤ G.degree r → r ∉ Y ∧ r ∉ P₁ ∧ r ∉ P₂ := fun r hdr =>
    ⟨fun h => by rw [mem_leafNbrs] at h; omega,
     fun h => by rw [mem_leafNbrs] at h; omega,
     fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz1_ab1 : z₁ ≠ ab₁ := longEnd_ne_ab hm hpq25 hab1_mem hdz14 hv3long
  have hz1_ab2 : z₁ ≠ ab₂ := longEnd_ne_ab hm hpq25 hab2_mem hdz14 hv3long
  have hz2_ab1 : z₂ ≠ ab₁ := longEnd_ne_ab hm hpq25 hab1_mem hdz24 hw2long
  have hz2_ab2 : z₂ ≠ ab₂ := longEnd_ne_ab hm hpq25 hab2_mem hdz24 hw2long
  have hz1_not_S : z₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP z₁ (by omega)
    exact ⟨hz1u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, hz1_ab1, hz1_ab2,
      ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have hz2_not_S : z₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP z₂ (by omega)
    exact ⟨hz2u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, hz2_ab1, hz2_ab2,
      ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have he1_not_S : e₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP e₁ (by omega)
    exact ⟨he1u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, (G.ne_of_adj hab1e).symm, he1ab2,
      ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have he2_not_S : e₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP e₂ (by omega)
    exact ⟨he2u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, he2ab1, (G.ne_of_adj hab2e).symm,
      ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = v₃ ∧ s = z₁) ∨ (r = w₂ ∧ s = z₂) ∨ (r = ab₁ ∧ s = e₁) ∨ (r = ab₂ ∧ s = e₂) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
    · rcases hall_u s hsr.symm with rfl | rfl | rfl | rfl | hsY
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS hab1S)
      · exact False.elim (hsS hab2S)
      · exact False.elim (hsS (by simp [S, hsY]))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w2 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hall_ab1 s hsr.symm with rfl | rfl | hsP1
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact False.elim (hsS (by simp [S, P₁, hsP1]))
    · rcases hall_ab2 s hsr.symm with rfl | rfl | hsP2
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact False.elim (hsS (by simp [S, P₂, hsP2]))
    · have hL := mem_leafNbrs.mp hrY
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq u hL.1.symm).symm) ▸ huS))
    · have hL := mem_leafNbrs.mp hrP1
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq ab₁ hL.1.symm).symm) ▸ hab1S))
    · have hL := mem_leafNbrs.mp hrP2
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq ab₂ hL.1.symm).symm) ▸ hab2S))
  -- 分是否出现 `G - S` 孤立点
  by_cases hiso_ex : ∃ s ∉ S, ∀ t ∉ S, ¬ G.Adj s t
  · rcases hiso_ex with ⟨s, hsS, hs_iso⟩
    have hs_nbr_S : ∀ r, G.Adj s r → r ∈ S := fun r hsr => by
      by_contra h; exact hs_iso r h hsr
    have hpos : 0 < (G.neighborFinset s).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree_ge_one hm s; omega
    rcases Finset.card_pos.mp hpos with ⟨r₀, hr₀⟩
    have hsr0 : G.Adj s r₀ := (G.mem_neighborFinset s r₀).mp hr₀
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ (hs_nbr_S r₀ hsr0) hsr0 with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hds4 : 4 ≤ G.degree s := by
      by_contra hlt; push Not at hlt
      have hsub2 : G.neighborFinset s ⊆ {ab₁, ab₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        rcases hS_out s hsS r (hs_nbr_S r hr) hr with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · omega
        · omega
        · simp
        · simp
      have h1 := Finset.card_le_card hsub2
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 := Finset.card_le_two (a := ab₁) (b := ab₂); omega
    have hsub4 : G.neighborFinset s ⊆ {v₃, w₂, ab₁, ab₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      rcases hS_out s hsS r (hs_nbr_S r hr) hr with
        ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hcard4 : ({v₃, w₂, ab₁, ab₂} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hv3w2, hab1v3.symm, hab2v3.symm]),
          Finset.card_insert_of_notMem (by simp [hab1w2.symm, hab2w2.symm]),
          Finset.card_pair hab12]
    have hNs_eq : G.neighborFinset s = {v₃, w₂, ab₁, ab₂} :=
      Finset.eq_of_subset_of_card_le hsub4
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hcard4]; omega)
    have hsv3 : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hNs_eq]; simp)
    have hsw2 : G.Adj s w₂ := (G.mem_neighborFinset s w₂).mp (by rw [hNs_eq]; simp)
    have hsab1 : G.Adj s ab₁ := (G.mem_neighborFinset s ab₁).mp (by rw [hNs_eq]; simp)
    have hsab2 : G.Adj s ab₂ := (G.mem_neighborFinset s ab₂).mp (by rw [hNs_eq]; simp)
    have hs_eq_z1 : s = z₁ := by
      rcases hS_out s hsS v₃ (by simp [S]) hsv3 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hv3w2 h)
      · exact False.elim (hab1v3 h.symm)
      · exact False.elim (hab2v3 h.symm)
    have hs_eq_z2 : s = z₂ := by
      rcases hS_out s hsS w₂ (by simp [S]) hsw2 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (hv3w2 h.symm)
      · exact h
      · exact False.elim (hab1w2 h.symm)
      · exact False.elim (hab2w2 h.symm)
    have hs_eq_e1 : s = e₁ := by
      rcases hS_out s hsS ab₁ hab1S hsab1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim (hab1v3 h)
      · exact False.elim (hab1w2 h)
      · exact h
      · exact False.elim (hab12 h)
    have hs_eq_e2 : s = e₂ := by
      rcases hS_out s hsS ab₂ hab2S hsab2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hab2v3 h)
      · exact False.elim (hab2w2 h)
      · exact False.elim (hab12 h.symm)
      · exact h
    have huniv : insert s S = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := u) (Finset.mem_insert_of_mem huS)
      intro a ha b hab
      rcases Finset.mem_insert.mp ha with rfl | haS
      · exact Finset.mem_insert_of_mem (hs_nbr_S b hab)
      · by_cases hbS : b ∈ S
        · exact Finset.mem_insert_of_mem hbS
        · rcases hS_out b hbS a haS hab.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · rw [← hs_eq_z1]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_z2]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_e1]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_e2]; exact Finset.mem_insert_self s S
    have hcore_eq : coreVerts G = {u, s, v₁, v₂, v₃, w₁, w₂, ab₁, ab₂} := by
      ext r
      simp only [mem_coreVerts, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hdr2
        have hmem : r ∈ insert s S := by rw [huniv]; exact Finset.mem_univ r
        simp only [S, Finset.mem_insert, Finset.mem_union] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            (hrY | hrP1) | hrP2
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
        · rw [mem_leafNbrs] at hrY; omega
        · rw [mem_leafNbrs] at hrP1; omega
        · rw [mem_leafNbrs] at hrP2; omega
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
    have hcore_s : coreDeg G s = 4 := by
      unfold coreDeg coreNbrs
      have hsub_core : G.neighborFinset s ⊆ coreVerts G := by
        intro r hr; rw [hNs_eq] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rw [mem_coreVerts]
        rcases hr with rfl | rfl | rfl | rfl <;> omega
      rw [Finset.inter_eq_left.mpr hsub_core, hNs_eq, hcard4]
    have hcard9 : ({u, s, v₁, v₂, v₃, w₁, w₂, ab₁, ab₂} : Finset V).card = 9 := by
      have hsn : s ∉ ({v₁, v₂, v₃, w₁, w₂, ab₁, ab₂} : Finset V) := fun h => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hsS (by simp [S])
      have hun : u ∉ ({s, v₁, v₂, v₃, w₁, w₂, ab₁, ab₂} : Finset V) := fun h => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hsS huS
        · exact G.ne_of_adj huv1 rfl
        · exact hv2u rfl
        · exact hv3u rfl
        · exact G.ne_of_adj huw1 rfl
        · exact hw2u rfl
        · exact G.ne_of_adj huab1 rfl
        · exact G.ne_of_adj huab2 rfl
      rw [Finset.card_insert_of_notMem hun, Finset.card_insert_of_notMem hsn,
          Finset.card_insert_of_notMem
            (by simp [G.ne_of_adj hv12, hv31.symm, hvw1, hv1w2, hab1v1.symm, hab2v1.symm]),
          Finset.card_insert_of_notMem
            (by simp [G.ne_of_adj hv23, hv2w1, hv2w2, hab1v2.symm, hab2v2.symm]),
          Finset.card_insert_of_notMem (by simp [hv3w1, hv3w2, hab1v3.symm, hab2v3.symm]),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hw12, hab1w1.symm, hab2w1.symm]),
          Finset.card_insert_of_notMem (by simp [hab1w2.symm, hab2w2.symm]),
          Finset.card_pair hab12]
    exact mad_contra_nine_core hm hpq hcore_eq hcard9 hc4 hcore_s
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv1])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv2])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv3])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw1])
      (by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw2])
      hcab12 hcab22
  · -- 非孤立情形：取 `adm` 并调用 `q4_case2_comb`
    push Not at hiso_ex
    rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm⟩
    rcases ab_color_pack hm hab1_mem huab1 hab1e he1u hall_ab1 (adm.φ e₁) (adm.φs e₁) with
      ⟨forb₁, Pc₁, hPc1_2, hPc1_spec⟩
    rcases ab_color_pack hm hab2_mem huab2 hab2e he2u hall_ab2 (adm.φ e₂) (adm.φs e₂) with
      ⟨forb₂, Pc₂, hPc2_2, hPc2_spec⟩
    have hLu : (L u).card = Y.card + 5 := by
      have h1 := coreDeg_add_leafNbrs hm u
      dsimp only [Y]
      rw [hm.list_card u]; simp only [kappa, show G.degree u ≠ 2 by omega, ite_false]; omega
    have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv1]
    have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv2]
    have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv3]
    have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw1]
    have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw2]
    have hY_L2 : ∀ r ∈ Y, (L r).card = 2 := fun r hr => by
      rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
    let Z₃ : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
    have hZ3 : 2 ≤ Z₃.card := by
      dsimp only [Z₃]; have := card_sdiff_ge (L v₃) {adm.φ z₁, adm.φs z₁}
      have := Finset.card_le_two (a := adm.φ z₁) (b := adm.φs z₁); omega
    have hc2_ex : ∀ α : ℕ, ∃ d₂ ∈ L w₂, d₂ ≠ α ∧ d₂ ≠ adm.φ z₂ ∧ d₂ ≠ adm.φs z₂ := by
      intro α
      rcases exists_mem_sdiff_of_lt (A := L w₂) (B := {α, adm.φ z₂, adm.φs z₂})
        (by have := card_triple_le α (adm.φ z₂) (adm.φs z₂); omega) with ⟨d₂, hd2, hd2n⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2n
      exact ⟨d₂, hd2, hd2n.1, hd2n.2.1, hd2n.2.2⟩
    let d₂Fun : ℕ → ℕ := fun α => (hc2_ex α).choose
    have hd2_spec : ∀ α, d₂Fun α ∈ L w₂ ∧ d₂Fun α ≠ α ∧
        d₂Fun α ≠ adm.φ z₂ ∧ d₂Fun α ≠ adm.φs z₂ := fun α => (hc2_ex α).choose_spec
    let C : Finset ℕ := L u \ {forb₁, forb₂}
    have hC : Y.card + 3 ≤ C.card := by
      dsimp only [C]; have := card_sdiff_ge (L u) {forb₁, forb₂}
      have := Finset.card_le_two (a := forb₁) (b := forb₂); omega
    rcases q4_case2_comb (L := L) (Y := Y) (C := C) (P₁ := Pc₁) (P₂ := Pc₂)
      (F₁ := threeThreadGoodCols (L v₁) (L v₂) Z₃ (adm.φ z₁))
      (F₂ := fun α => L w₁ \ {α, d₂Fun α, adm.φ z₂}) hY_L2
      (fun _ => threeThreadGoodCols_nonempty hLv1 hLv2 (Finset.card_pos.mp (by omega)))
      (fun α => by
        rw [← Finset.card_pos]
        have := card_sdiff_ge (L w₁) {α, d₂Fun α, adm.φ z₂}
        have := card_triple_le α (d₂Fun α) (adm.φ z₂); omega)
      (threeThreadGoodCols_card_one_le_one C hLv1 hLv2 hZ3)
      (card_filter_sdiff_triple_eq_one_le C (L w₁) hLw1 d₂Fun (adm.φ z₂)).1
      hPc1_2 hPc2_2 hC with ⟨α, hαC, c₁, hc₁, d₁, hd₁, c_ab1, hc_ab1, c_ab2, hc_ab2, aY, haY, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁
    rcases hc₁ with ⟨⟨hc1L, hc1α⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
    simp only [Z₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hc3Z hc2B hd₁
    have hd2s := hd2_spec α
    rcases hPc1_spec α hαC.2.1 c_ab1 hc_ab1 with
      ⟨hcab1L, hcab1α, hcab1e, hcab1se, aP₁, haP1_mem, haP1_pcf⟩
    rcases hPc2_spec α hαC.2.2 c_ab2 hc_ab2 with
      ⟨hcab2L, hcab2α, hcab2e, hcab2se, aP₂, haP2_mem, haP2_pcf⟩
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v₁ then c₁ else if r = v₂ then c₂ else if r = v₃ then c₃
      else if r = w₁ then d₁ else if r = w₂ then d₂Fun α
      else if r = ab₁ then c_ab1 else if r = ab₂ then c_ab2
      else if r ∈ Y then aY r else if r ∈ P₁ then aP₁ r else if r ∈ P₂ then aP₂ r else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψv1 : ψ v₁ = c₁ := by simp [ψ, (G.ne_of_adj huv1).symm]
    have hψv2 : ψ v₂ = c₂ := by simp [ψ, hv2u, (G.ne_of_adj hv12).symm]
    have hψv3 : ψ v₃ = c₃ := by simp [ψ, hv3u, hv31, (G.ne_of_adj hv23).symm]
    have hψw1 : ψ w₁ = d₁ := by simp [ψ, (G.ne_of_adj huw1).symm, hvw1.symm, hv2w1.symm, hv3w1.symm]
    have hψw2 : ψ w₂ = d₂Fun α := by
      simp [ψ, hw2u, hv1w2.symm, hv2w2.symm, hv3w2.symm, (G.ne_of_adj hw12).symm]
    have hψab1 : ψ ab₁ = c_ab1 := by
      simp [ψ, (G.ne_of_adj huab1).symm, hab1v1, hab1v2, hab1v3, hab1w1, hab1w2]
    have hψab2 : ψ ab₂ = c_ab2 := by
      simp [ψ, (G.ne_of_adj huab2).symm, hab2v1, hab2v2, hab2v3, hab2w1, hab2w2, hab12.symm]
    have hψY : ∀ r ∈ Y, ψ r = aY r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ ab₁ by intro h; subst h; omega),
        (show r ≠ ab₂ by intro h; subst h; omega), hr]
    have hψP1 : ∀ r ∈ P₁, ψ r = aP₁ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P1_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ ab₁ by intro h; subst h; omega),
        (show r ≠ ab₂ by intro h; subst h; omega), hrY, hr]
    have hψP2 : ∀ r ∈ P₂, ψ r = aP₂ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P2_disj h hr
      have hrP1 : r ∉ P₁ := fun h => Finset.disjoint_left.mp hP1_P2_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ ab₁ by intro h; subst h; omega),
        (show r ≠ ab₂ by intro h; subst h; omega), hrY, hrP1, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1.1,
        hr.2.2.2.2.2.2.2.2.1.2, hr.2.2.2.2.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
      · rw [hψu]; exact hαC.1
      · rw [hψv1]; exact hc1L
      · rw [hψv2]; exact hc2B.1
      · rw [hψv3]; exact hc3Z.1
      · rw [hψw1]; exact hd₁.1
      · rw [hψw2]; exact hd2s.1
      · rw [hψab1]; exact hcab1L
      · rw [hψab2]; exact hcab2L
      · rw [hψY r hrY]; exact (haY r hrY).1
      · rw [hψP1 r hrP1]; exact (haP1_mem r hrP1).1
      · rw [hψP2 r hrP2]; exact (haP2_mem r hrP2).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (haY' | haP1) | haP2
        · rcases hall_u b' hab with hb | hb | hb | hb | hbY
          · rw [hb, hψu, hψv1]; exact Ne.symm hc1α
          · rw [hb, hψu, hψw1]; exact Ne.symm hd₁.2.1
          · rw [hb, hψu, hψab1]; exact Ne.symm hcab1α
          · rw [hb, hψu, hψab2]; exact Ne.symm hcab2α
          · rw [hψu, hψY b' hbY]; exact (haY b' hbY).2.symm
        · rcases hall_v1 b' hab with hb | hb
          · rw [hb, hψv1, hψu]; exact hc1α
          · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
        · rcases hall_v2 b' hab with hb | hb
          · rw [hb, hψv2, hψv1]; exact hc21
          · rw [hb, hψv2, hψv3]; exact hc2B.2.2.1
        · rcases hall_v3 b' hab with hb | hb
          · rw [hb, hψv3, hψv2]; exact Ne.symm hc2B.2.2.1
          · rw [hb, hψv3, hψ_out z₁ hz1_not_S]; exact hc3Z.2.1
        · rcases hall_w1 b' hab with hb | hb
          · rw [hb, hψw1, hψu]; exact hd₁.2.1
          · rw [hb, hψw1, hψw2]; exact hd₁.2.2.1
        · rcases hall_w2 b' hab with hb | hb
          · rw [hb, hψw2, hψw1]; exact Ne.symm hd₁.2.2.1
          · rw [hb, hψw2, hψ_out z₂ hz2_not_S]; exact hd2s.2.2.1
        · rcases hall_ab1 b' hab with hb | hb | hbP1
          · rw [hb, hψab1, hψu]; exact hcab1α
          · rw [hb, hψab1, hψ_out e₁ he1_not_S]; exact hcab1e
          · rw [hψab1, hψP1 b' hbP1]; exact (haP1_mem b' hbP1).2.symm
        · rcases hall_ab2 b' hab with hb | hb | hbP2
          · rw [hb, hψab2, hψu]; exact hcab2α
          · rw [hb, hψab2, hψ_out e₂ he2_not_S]; exact hcab2e
          · rw [hψab2, hψP2 b' hbP2]; exact (haP2_mem b' hbP2).2.symm
        · have hL := mem_leafNbrs.mp haY'
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u hL.1.symm).symm
          rw [hb, hψY a' haY', hψu]; exact (haY a' haY').2
        · have hL := mem_leafNbrs.mp haP1
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₁ := (huniq b' hab).trans (huniq ab₁ hL.1.symm).symm
          rw [hb, hψP1 a' haP1, hψab1]; exact (haP1_mem a' haP1).2
        · have hL := mem_leafNbrs.mp haP2
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₂ := (huniq b' hab).trans (huniq ab₂ hL.1.symm).symm
          rw [hb, hψP2 a' haP2, hψab2]; exact (haP2_mem a' haP2).2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro s hsS _ r hrS hsr
      rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hψv3]; exact hc3Z.2.2
      · rw [hψw2]; exact hd2s.2.2.2
      · rw [hψab1]; exact hcab1se
      · rw [hψab2]; exact hcab2se
    · intro s hsS hiso _
      rcases hiso_ex s hsS with ⟨t, htS, hst⟩
      exact False.elim (hiso t htS hst)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
      · exact pcf_from_leaf_and_four huv1 huw1 huab1 huab2 (fun t ht => (mem_leafNbrs.mp ht).1) hψY
          hall_u (by rw [hψv1, hψw1, hψab1, hψab2]; exact hγ)
      · exact pcf_at_of_two_distinct_neighbors hdv1 huv1.symm hv12 hv2u.symm
          (by rw [hψu, hψv2]; exact Ne.symm hc2B.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdv2 hv12.symm hv23 hv31.symm
          (by rw [hψv1, hψv3]; exact Ne.symm hc31)
      · exact pcf_at_of_two_distinct_neighbors hdv3 hv23.symm hv3z hz1v2.symm
          (by rw [hψv2, hψ_out z₁ hz1_not_S]; exact hc2B.2.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdw1 huw1.symm hw12 hw2u.symm
          (by rw [hψu, hψw2]; exact Ne.symm hd2s.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdw2 hw12.symm hw2z hz2w1.symm
          (by rw [hψw1, hψ_out z₂ hz2_not_S]; exact hd₁.2.2.2)
      · exact haP1_pcf ψ hψu (hψ_out e₁ he1_not_S) hψP1
      · exact haP2_pcf ψ hψu (hψ_out e₂ he2_not_S) hψP2
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrP1).2 (mem_leafNbrs.mp hrP1).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrP2).2 (mem_leafNbrs.mp hrP2).1.symm

/-! ## 5. 情形 2b：`g = 0, t₃ = 2, t₂ = 0, a + b = 2`（含孤立 `γ_s` 妙招） -/

private lemma q4_case_good_zero_t3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V}
    (hc4 : coreDeg G u = 4)
    (ht3 : (threeThreadNbrs G u).card = 2)
    (hab2 : (oneThreadNbrs G u).card + (badNbrs G u).card = 2) : False := by
  classical
  have hdu4 : 4 ≤ G.degree u := by have := coreDeg_le_degree G u; omega
  have hdu3 : 3 ≤ G.degree u := by omega
  rcases Finset.card_eq_two.mp ht3 with ⟨v₁, w₁, hvw1, ht3_eq⟩
  have hv1_mem : v₁ ∈ threeThreadNbrs G u := by rw [ht3_eq]; simp
  have hw1_mem : w₁ ∈ threeThreadNbrs G u := by rw [ht3_eq]; simp
  rcases threeThread_unpack hm hdu3 hv1_mem with
    ⟨v₂, v₃, z₁, huv1, hdv1, hv12, hv2u, hdv2, hv23, hv31, hv3u, hdv3, hv3z, hz1v2, hz1u, hdz14,
      hv3long, hall_v1, hall_v2, hall_v3⟩
  rcases threeThread_unpack hm hdu3 hw1_mem with
    ⟨w₂, w₃, z₂, huw1, hdw1, hw12, hw2u, hdw2, hw23, hw31, hw3u, hdw3, hw3z, hz2w2, hz2u, hdz24,
      hw3long, hall_w1, hall_w2, hall_w3⟩
  rcases three_three_segs_disjoint hm hdu3 hvw1 huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3
    huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3 with
    ⟨hv1w2, hv1w3, hv2w1, hv2w2, hv2w3, hv3w1, hv3w2, hv3w3⟩
  have hab_disj : Disjoint (oneThreadNbrs G u) (badNbrs G u) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    have := (mem_oneThreadNbrs.mp h1).2.1; have := (mem_badNbrs.mp h2).2.1; omega
  have hab_card : (oneThreadNbrs G u ∪ badNbrs G u).card = 2 := by
    rw [Finset.card_union_of_disjoint hab_disj]; exact hab2
  rcases Finset.card_eq_two.mp hab_card with ⟨ab₁, ab₂, hab12, hab_eq⟩
  have hab1_mem : ab₁ ∈ oneThreadNbrs G u ∪ badNbrs G u := by rw [hab_eq]; simp
  have hab2_mem : ab₂ ∈ oneThreadNbrs G u ∪ badNbrs G u := by rw [hab_eq]; simp
  rcases ab_geom_unpack hm hpq hdu3 hab1_mem with
    ⟨e₁, huab1, hab1e, he1u, hde13, hdab12, _, hall_ab1⟩
  rcases ab_geom_unpack hm hpq hdu3 hab2_mem with
    ⟨e₂, huab2, hab2e, he2u, hde23, hdab22, _, hall_ab2⟩
  have hnotadj_ab : ¬ G.Adj ab₁ ab₂ := ab_not_adj hm hpq hdu3 hab1_mem hab2_mem
  have he1ab2 : e₁ ≠ ab₂ := fun h => hnotadj_ab (h ▸ hab1e)
  have he2ab1 : e₂ ≠ ab₁ := fun h => hnotadj_ab (h ▸ hab2e).symm
  rcases ab_not_mem_three_seg hm hdu3 hab1_mem hv1_mem huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3 with
    ⟨hab1v1, hab1v2, hab1v3⟩
  rcases ab_not_mem_three_seg hm hdu3 hab2_mem hv1_mem huv1 hdv1 hv12 hdv2 hv23 hv31 hdv3 with
    ⟨hab2v1, hab2v2, hab2v3⟩
  rcases ab_not_mem_three_seg hm hdu3 hab1_mem hw1_mem huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3 with
    ⟨hab1w1, hab1w2, hab1w3⟩
  rcases ab_not_mem_three_seg hm hdu3 hab2_mem hw1_mem huw1 hdw1 hw12 hdw2 hw23 hw31 hdw3 with
    ⟨hab2w1, hab2w2, hab2w3⟩
  have hcore_u : coreNbrs G u = {v₁, w₁, ab₁, ab₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact mem_coreNbrs.mpr ⟨huv1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huw1, by omega⟩
      · exact mem_coreNbrs.mpr ⟨huab1, hdab12⟩
      · exact mem_coreNbrs.mpr ⟨huab2, hdab22⟩
    · rw [Finset.card_insert_of_notMem (by simp [hvw1, hab1v1.symm, hab2v1.symm]),
          Finset.card_insert_of_notMem (by simp [hab1w1.symm, hab2w1.symm]),
          Finset.card_pair hab12]
      unfold coreDeg at hc4; omega
  let Y := leafNbrs G u
  let P₁ := leafNbrs G ab₁
  let P₂ := leafNbrs G ab₂
  have hY_P1_disj : Disjoint Y P₁ := leafNbrs_disjoint_of_ne (G.ne_of_adj huab1)
  have hY_P2_disj : Disjoint Y P₂ := leafNbrs_disjoint_of_ne (G.ne_of_adj huab2)
  have hP1_P2_disj : Disjoint P₁ P₂ := leafNbrs_disjoint_of_ne hab12
  have hall_u : ∀ r, G.Adj u r → r = v₁ ∨ r = w₁ ∨ r = ab₁ ∨ r = ab₂ ∨ r ∈ Y := by
    intro r hur
    have hdr1 := degree_ge_one hm r
    by_cases h1 : G.degree r = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_leafNbrs.mpr ⟨hur, h1⟩))))
    · have hc : r ∈ coreNbrs G u := mem_coreNbrs.mpr ⟨hur, by omega⟩
      rw [hcore_u, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  let S : Finset V :=
    insert u (insert v₁ (insert v₂ (insert v₃ (insert w₁ (insert w₂ (insert w₃
      (insert ab₁ (insert ab₂ (Y ∪ P₁ ∪ P₂)))))))))
  have huS : u ∈ S := Finset.mem_insert_self u _
  have hab1S : ab₁ ∈ S := by simp [S]
  have hab2S : ab₂ ∈ S := by simp [S]
  have hnot_YPP : ∀ r : V, 2 ≤ G.degree r → r ∉ Y ∧ r ∉ P₁ ∧ r ∉ P₂ := fun r hdr =>
    ⟨fun h => by rw [mem_leafNbrs] at h; omega,
     fun h => by rw [mem_leafNbrs] at h; omega,
     fun h => by rw [mem_leafNbrs] at h; omega⟩
  have hz1_ab1 : z₁ ≠ ab₁ := longEnd_ne_ab hm hpq hab1_mem hdz14 hv3long
  have hz1_ab2 : z₁ ≠ ab₂ := longEnd_ne_ab hm hpq hab2_mem hdz14 hv3long
  have hz2_ab1 : z₂ ≠ ab₁ := longEnd_ne_ab hm hpq hab1_mem hdz24 hw3long
  have hz2_ab2 : z₂ ≠ ab₂ := longEnd_ne_ab hm hpq hab2_mem hdz24 hw3long
  have hz1_not_S : z₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP z₁ (by omega)
    exact ⟨hz1u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      hz1_ab1, hz1_ab2, ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have hz2_not_S : z₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP z₂ (by omega)
    exact ⟨hz2u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      hz2_ab1, hz2_ab2, ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have he1_not_S : e₁ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP e₁ (by omega)
    exact ⟨he1u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      (G.ne_of_adj hab1e).symm, he1ab2, ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have he2_not_S : e₂ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
    have hL := hnot_YPP e₂ (by omega)
    exact ⟨he2u, fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
      he2ab1, (G.ne_of_adj hab2e).symm, ⟨hL.1, hL.2.1⟩, hL.2.2⟩
  have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
      (r = v₃ ∧ s = z₁) ∨ (r = w₃ ∧ s = z₂) ∨ (r = ab₁ ∧ s = e₁) ∨ (r = ab₂ ∧ s = e₂) := by
    intro s hsS r hrS hsr
    simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
    rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
    · rcases hall_u s hsr.symm with rfl | rfl | rfl | rfl | hsY
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS (by simp [S]))
      · exact False.elim (hsS hab1S)
      · exact False.elim (hsS hab2S)
      · exact False.elim (hsS (by simp [S, hsY]))
    · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_v3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
    · rcases hall_w3 s hsr.symm with rfl | rfl
      · exact False.elim (hsS (by simp [S]))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hall_ab1 s hsr.symm with rfl | rfl | hsP1
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact False.elim (hsS (by simp [S, P₁, hsP1]))
    · rcases hall_ab2 s hsr.symm with rfl | rfl | hsP2
      · exact False.elim (hsS huS)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact False.elim (hsS (by simp [S, P₂, hsP2]))
    · have hL := mem_leafNbrs.mp hrY
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq u hL.1.symm).symm) ▸ huS))
    · have hL := mem_leafNbrs.mp hrP1
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq ab₁ hL.1.symm).symm) ▸ hab1S))
    · have hL := mem_leafNbrs.mp hrP2
      rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
      exact False.elim (hsS (((huniq s hsr.symm).trans (huniq ab₂ hL.1.symm).symm) ▸ hab2S))
  have hLu : (L u).card = Y.card + 5 := by
    have h1 := coreDeg_add_leafNbrs hm u
    dsimp only [Y]
    rw [hm.list_card u]; simp only [kappa, show G.degree u ≠ 2 by omega, ite_false]; omega
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv1]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv2]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv3]
  have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw1]
  have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw2]
  have hLw3 : (L w₃).card = 4 := by rw [hm.list_card w₃]; simp [kappa, hdw3]
  have hY_L2 : ∀ r ∈ Y, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  -- 分是否出现 `G - S` 孤立点
  by_cases hiso_ex : ∃ s ∉ S, ∀ t ∉ S, ¬ G.Adj s t
  · -- 孤立情形：`V(G) = insert s S`，启用 `γ_s` 妙招直接构造全图 PCF 染色！
    rcases hiso_ex with ⟨s, hsS, hs_iso⟩
    have hs_nbr_S : ∀ r, G.Adj s r → r ∈ S := fun r hsr => by
      by_contra h; exact hs_iso r h hsr
    have hpos : 0 < (G.neighborFinset s).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree_ge_one hm s; omega
    rcases Finset.card_pos.mp hpos with ⟨r₀, hr₀⟩
    have hsr0 : G.Adj s r₀ := (G.mem_neighborFinset s r₀).mp hr₀
    have hds3 : 3 ≤ G.degree s := by
      rcases hS_out s hsS r₀ (hs_nbr_S r₀ hsr0) hsr0 with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hds4 : 4 ≤ G.degree s := by
      by_contra hlt; push Not at hlt
      have hsub2 : G.neighborFinset s ⊆ {ab₁, ab₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        rcases hS_out s hsS r (hs_nbr_S r hr) hr with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · omega
        · omega
        · simp
        · simp
      have h1 := Finset.card_le_card hsub2
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 := Finset.card_le_two (a := ab₁) (b := ab₂); omega
    have hsub4 : G.neighborFinset s ⊆ {v₃, w₃, ab₁, ab₂} := by
      intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
      rcases hS_out s hsS r (hs_nbr_S r hr) hr with
        ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    have hcard4 : ({v₃, w₃, ab₁, ab₂} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hv3w3, hab1v3.symm, hab2v3.symm]),
          Finset.card_insert_of_notMem (by simp [hab1w3.symm, hab2w3.symm]),
          Finset.card_pair hab12]
    have hNs_eq : G.neighborFinset s = {v₃, w₃, ab₁, ab₂} :=
      Finset.eq_of_subset_of_card_le hsub4
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hcard4]; omega)
    have hds_eq4 : G.degree s = 4 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hNs_eq, hcard4]
    have hall_s : ∀ r, G.Adj s r → r = v₃ ∨ r = w₃ ∨ r = ab₁ ∨ r = ab₂ := fun r hr => by
      have : r ∈ ({v₃, w₃, ab₁, ab₂} : Finset V) := by
        rw [← hNs_eq]; exact (G.mem_neighborFinset s r).mpr hr
      simpa using this
    have hsv3 : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hNs_eq]; simp)
    have hsw3 : G.Adj s w₃ := (G.mem_neighborFinset s w₃).mp (by rw [hNs_eq]; simp)
    have hsab1 : G.Adj s ab₁ := (G.mem_neighborFinset s ab₁).mp (by rw [hNs_eq]; simp)
    have hsab2 : G.Adj s ab₂ := (G.mem_neighborFinset s ab₂).mp (by rw [hNs_eq]; simp)
    have hs_eq_z1 : s = z₁ := by
      rcases hS_out s hsS v₃ (by simp [S]) hsv3 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hv3w3 h)
      · exact False.elim (hab1v3 h.symm)
      · exact False.elim (hab2v3 h.symm)
    have hs_eq_z2 : s = z₂ := by
      rcases hS_out s hsS w₃ (by simp [S]) hsw3 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (hv3w3 h.symm)
      · exact h
      · exact False.elim (hab1w3 h.symm)
      · exact False.elim (hab2w3 h.symm)
    have hs_eq_e1 : s = e₁ := by
      rcases hS_out s hsS ab₁ hab1S hsab1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim (hab1v3 h)
      · exact False.elim (hab1w3 h)
      · exact h
      · exact False.elim (hab12 h)
    have hs_eq_e2 : s = e₂ := by
      rcases hS_out s hsS ab₂ hab2S hsab2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hab2v3 h)
      · exact False.elim (hab2w3 h)
      · exact False.elim (hab12 h.symm)
      · exact h
    have huniv : insert s S = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := u) (Finset.mem_insert_of_mem huS)
      intro a ha b hab
      rcases Finset.mem_insert.mp ha with rfl | haS
      · exact Finset.mem_insert_of_mem (hs_nbr_S b hab)
      · by_cases hbS : b ∈ S
        · exact Finset.mem_insert_of_mem hbS
        · rcases hS_out b hbS a haS hab.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · rw [← hs_eq_z1]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_z2]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_e1]; exact Finset.mem_insert_self s S
          · rw [← hs_eq_e2]; exact Finset.mem_insert_self s S
    have hnotS_eq : ∀ r, r ∉ S → r = s := fun r hr => by
      have : r ∈ insert s S := by rw [huniv]; exact Finset.mem_univ r
      exact (Finset.mem_insert.mp this).resolve_right hr
    -- 取 `φs ∈ L s`、`γs ∈ L v₃ \ {φs}` 固定 `v₃ ↦ γs`！
    have hLs5 : (L s).card = 5 := by rw [hm.list_card s]; simp [kappa, hds_eq4]
    rcases Finset.card_pos.mp (by omega : 0 < (L s).card) with ⟨φs, hφsL⟩
    rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {φs}) (by simp [hLv3]) with ⟨γs, hγsL, hγs_ne⟩
    rw [Finset.mem_singleton] at hγs_ne
    let Z₃w : Finset ℕ := L w₃ \ {φs, γs}
    have hZ3w : 2 ≤ Z₃w.card := by
      dsimp only [Z₃w]; have := card_sdiff_ge (L w₃) {φs, γs}
      have := Finset.card_le_two (a := φs) (b := γs); omega
    rcases ab_color_pack hm hab1_mem huab1 hab1e he1u hall_ab1 φs γs with
      ⟨forb₁, Pc₁, hPc1_2, hPc1_spec⟩
    rcases ab_color_pack hm hab2_mem huab2 hab2e he2u hall_ab2 φs γs with
      ⟨forb₂, Pc₂, hPc2_2, hPc2_spec⟩
    have hc2_ex : ∀ α : ℕ, ∃ c₂ ∈ L v₂, c₂ ≠ α ∧ c₂ ≠ γs ∧ c₂ ≠ φs := by
      intro α
      rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {α, γs, φs})
        (by have := card_triple_le α γs φs; omega) with ⟨c₂, hc2, hc2n⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc2n
      exact ⟨c₂, hc2, hc2n.1, hc2n.2.1, hc2n.2.2⟩
    let c₂Fun : ℕ → ℕ := fun α => (hc2_ex α).choose
    have hc2_spec : ∀ α, c₂Fun α ∈ L v₂ ∧ c₂Fun α ≠ α ∧ c₂Fun α ≠ γs ∧ c₂Fun α ≠ φs :=
      fun α => (hc2_ex α).choose_spec
    let C : Finset ℕ := L u \ {forb₁, forb₂}
    have hC : Y.card + 3 ≤ C.card := by
      dsimp only [C]; have := card_sdiff_ge (L u) {forb₁, forb₂}
      have := Finset.card_le_two (a := forb₁) (b := forb₂); omega
    -- 用 `q4_case2_comb`（令 `F₁` 为 `w₁` 的 `≤ 1` 集，`F₂` 为 `v₁` 的 `≤ 3` 集）
    rcases q4_case2_comb (L := L) (Y := Y) (C := C) (P₁ := Pc₁) (P₂ := Pc₂)
      (F₁ := threeThreadGoodCols (L w₁) (L w₂) Z₃w φs)
      (F₂ := fun α => L v₁ \ {α, c₂Fun α, γs}) hY_L2
      (fun _ => threeThreadGoodCols_nonempty hLw1 hLw2 (Finset.card_pos.mp (by omega)))
      (fun α => by
        rw [← Finset.card_pos]
        have := card_sdiff_ge (L v₁) {α, c₂Fun α, γs}
        have := card_triple_le α (c₂Fun α) γs; omega)
      (threeThreadGoodCols_card_one_le_one C hLw1 hLw2 hZ3w)
      (card_filter_sdiff_triple_eq_one_le C (L v₁) hLv1 c₂Fun γs).1
      hPc1_2 hPc2_2 hC with ⟨α, hαC, d₁, hd₁, c₁, hc₁, c_ab1, hc_ab1, c_ab2, hc_ab2, aY, haY, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hd₁
    rcases hd₁ with ⟨⟨hd1L, hd1α⟩, d₃, hd3Z, hd31, d₂, hd2B, hd21⟩
    simp only [Z₃w, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hd3Z hd2B hc₁
    have hc2s := hc2_spec α
    rcases hPc1_spec α hαC.2.1 c_ab1 hc_ab1 with
      ⟨hcab1L, hcab1α, hcab1s, hcab1γ, aP₁, haP1_mem, haP1_pcf⟩
    rcases hPc2_spec α hαC.2.2 c_ab2 hc_ab2 with
      ⟨hcab2L, hcab2α, hcab2s, hcab2γ, aP₂, haP2_mem, haP2_pcf⟩
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v₁ then c₁ else if r = v₂ then c₂Fun α else if r = v₃ then γs
      else if r = w₁ then d₁ else if r = w₂ then d₂ else if r = w₃ then d₃
      else if r = ab₁ then c_ab1 else if r = ab₂ then c_ab2
      else if r ∈ Y then aY r else if r ∈ P₁ then aP₁ r else if r ∈ P₂ then aP₂ r else φs
    have hψu : ψ u = α := by simp [ψ]
    have hψv1 : ψ v₁ = c₁ := by simp [ψ, (G.ne_of_adj huv1).symm]
    have hψv2 : ψ v₂ = c₂Fun α := by simp [ψ, hv2u, (G.ne_of_adj hv12).symm]
    have hψv3 : ψ v₃ = γs := by simp [ψ, hv3u, hv31, (G.ne_of_adj hv23).symm]
    have hψw1 : ψ w₁ = d₁ := by simp [ψ, (G.ne_of_adj huw1).symm, hvw1.symm, hv2w1.symm, hv3w1.symm]
    have hψw2 : ψ w₂ = d₂ := by
      simp [ψ, hw2u, hv1w2.symm, hv2w2.symm, hv3w2.symm, (G.ne_of_adj hw12).symm]
    have hψw3 : ψ w₃ = d₃ := by
      simp [ψ, hw3u, hv1w3.symm, hv2w3.symm, hv3w3.symm, hw31, (G.ne_of_adj hw23).symm]
    have hψab1 : ψ ab₁ = c_ab1 := by
      simp [ψ, (G.ne_of_adj huab1).symm, hab1v1, hab1v2, hab1v3, hab1w1, hab1w2, hab1w3]
    have hψab2 : ψ ab₂ = c_ab2 := by
      simp [ψ, (G.ne_of_adj huab2).symm, hab2v1, hab2v2, hab2v3, hab2w1, hab2w2, hab2w3, hab12.symm]
    have hψY : ∀ r ∈ Y, ψ r = aY r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega), hr]
    have hψP1 : ∀ r ∈ P₁, ψ r = aP₁ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P1_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega),
        hrY, hr]
    have hψP2 : ∀ r ∈ P₂, ψ r = aP₂ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P2_disj h hr
      have hrP1 : r ∉ P₁ := fun h => Finset.disjoint_left.mp hP1_P2_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega),
        hrY, hrP1, hr]
    have hψs : ψ s = φs := by
      have hs := hsS
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hs
      simp [ψ, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2.1.1, hs.2.2.2.2.2.2.2.2.2.1.2, hs.2.2.2.2.2.2.2.2.2.2]
    apply hm.not_colorable
    refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
    · -- 恰当性
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (haY' | haP1) | haP2
        · rcases hall_u b' hab with hb | hb | hb | hb | hbY
          · rw [hb, hψu, hψv1]; exact Ne.symm hc₁.2.1
          · rw [hb, hψu, hψw1]; exact Ne.symm hd1α
          · rw [hb, hψu, hψab1]; exact Ne.symm hcab1α
          · rw [hb, hψu, hψab2]; exact Ne.symm hcab2α
          · rw [hψu, hψY b' hbY]; exact (haY b' hbY).2.symm
        · rcases hall_v1 b' hab with hb | hb
          · rw [hb, hψv1, hψu]; exact hc₁.2.1
          · rw [hb, hψv1, hψv2]; exact hc₁.2.2.1
        · rcases hall_v2 b' hab with hb | hb
          · rw [hb, hψv2, hψv1]; exact Ne.symm hc₁.2.2.1
          · rw [hb, hψv2, hψv3]; exact hc2s.2.2.1
        · rcases hall_v3 b' hab with hb | hb
          · rw [hb, hψv3, hψv2]; exact Ne.symm hc2s.2.2.1
          · rw [hb, ← hs_eq_z1, hψv3, hψs]; exact hγs_ne
        · rcases hall_w1 b' hab with hb | hb
          · rw [hb, hψw1, hψu]; exact hd1α
          · rw [hb, hψw1, hψw2]; exact Ne.symm hd21
        · rcases hall_w2 b' hab with hb | hb
          · rw [hb, hψw2, hψw1]; exact hd21
          · rw [hb, hψw2, hψw3]; exact hd2B.2.2.1
        · rcases hall_w3 b' hab with hb | hb
          · rw [hb, hψw3, hψw2]; exact Ne.symm hd2B.2.2.1
          · rw [hb, ← hs_eq_z2, hψw3, hψs]; exact hd3Z.2.1
        · rcases hall_ab1 b' hab with hb | hb | hbP1
          · rw [hb, hψab1, hψu]; exact hcab1α
          · rw [hb, ← hs_eq_e1, hψab1, hψs]; exact hcab1s
          · rw [hψab1, hψP1 b' hbP1]; exact (haP1_mem b' hbP1).2.symm
        · rcases hall_ab2 b' hab with hb | hb | hbP2
          · rw [hb, hψab2, hψu]; exact hcab2α
          · rw [hb, ← hs_eq_e2, hψab2, hψs]; exact hcab2s
          · rw [hψab2, hψP2 b' hbP2]; exact (haP2_mem b' hbP2).2.symm
        · have hL := mem_leafNbrs.mp haY'
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u hL.1.symm).symm
          rw [hb, hψY a' haY', hψu]; exact (haY a' haY').2
        · have hL := mem_leafNbrs.mp haP1
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₁ := (huniq b' hab).trans (huniq ab₁ hL.1.symm).symm
          rw [hb, hψP1 a' haP1, hψab1]; exact (haP1_mem a' haP1).2
        · have hL := mem_leafNbrs.mp haP2
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₂ := (huniq b' hab).trans (huniq ab₂ hL.1.symm).symm
          rw [hb, hψP2 a' haP2, hψab2]; exact (haP2_mem a' haP2).2
      intro r₁ r₂ h12
      by_cases h1 : r₁ ∈ S
      · exact hcase r₁ r₂ h12 h1
      · have hr1s : r₁ = s := hnotS_eq r₁ h1
        have h2 : r₂ ∈ S := hs_nbr_S r₂ (hr1s ▸ h12)
        exact (hcase r₂ r₁ h12.symm h2).symm
    · -- 无冲突性（PCF）
      intro r _
      by_cases hrS : r ∈ S
      · simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
        · exact pcf_from_leaf_and_four huw1 huv1 huab1 huab2
            (fun t ht => (mem_leafNbrs.mp ht).1) hψY
            (fun t ht => by
              rcases hall_u t ht with h | h | h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
            (by rw [hψw1, hψv1, hψab1, hψab2]; exact hγ)
        · exact pcf_at_of_two_distinct_neighbors hdv1 huv1.symm hv12 hv2u.symm
            (by rw [hψu, hψv2]; exact Ne.symm hc2s.2.1)
        · exact pcf_at_of_two_distinct_neighbors hdv2 hv12.symm hv23 hv31.symm
            (by rw [hψv1, hψv3]; exact hc₁.2.2.2)
        · exact pcf_at_of_two_distinct_neighbors hdv3 hv23.symm hv3z hz1v2.symm
            (by rw [hψv2, ← hs_eq_z1, hψs]; exact hc2s.2.2.2)
        · exact pcf_at_of_two_distinct_neighbors hdw1 huw1.symm hw12 hw2u.symm
            (by rw [hψu, hψw2]; exact Ne.symm hd2B.2.1)
        · exact pcf_at_of_two_distinct_neighbors hdw2 hw12.symm hw23 hw31.symm
            (by rw [hψw1, hψw3]; exact Ne.symm hd31)
        · exact pcf_at_of_two_distinct_neighbors hdw3 hw23.symm hw3z hz2w2.symm
            (by rw [hψw2, ← hs_eq_z2, hψs]; exact hd2B.2.2.2)
        · exact haP1_pcf ψ hψu (by rw [← hs_eq_e1, hψs]) hψP1
        · exact haP2_pcf ψ hψu (by rw [← hs_eq_e2, hψs]) hψP2
        · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
        · exact pcf_at_deg_one (mem_leafNbrs.mp hrP1).2 (mem_leafNbrs.mp hrP1).1.symm
        · exact pcf_at_deg_one (mem_leafNbrs.mp hrP2).2 (mem_leafNbrs.mp hrP2).1.symm
      · -- `r = s`：`v₃` 是 `s` 的邻点中唯一染颜色 `γs` 的顶点！
        have hrs : r = s := hnotS_eq r hrS
        subst hrs
        refine ⟨v₃, hsv3, fun t hst hψt => ?_⟩
        rw [hψv3] at hψt
        rcases hall_s t hst with rfl | rfl | rfl | rfl
        · rfl
        · rw [hψw3] at hψt; exact False.elim (hd3Z.2.2 hψt)
        · rw [hψab1] at hψt; exact False.elim (hcab1γ hψt)
        · rw [hψab2] at hψt; exact False.elim (hcab2γ hψt)
    · -- 列表合法性
      intro r
      by_cases hrS : r ∈ S
      · simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
        · rw [hψu]; exact hαC.1
        · rw [hψv1]; exact hc₁.1
        · rw [hψv2]; exact hc2s.1
        · rw [hψv3]; exact hγsL
        · rw [hψw1]; exact hd1L
        · rw [hψw2]; exact hd2B.1
        · rw [hψw3]; exact hd3Z.1
        · rw [hψab1]; exact hcab1L
        · rw [hψab2]; exact hcab2L
        · rw [hψY r hrY]; exact (haY r hrY).1
        · rw [hψP1 r hrP1]; exact (haP1_mem r hrP1).1
        · rw [hψP2 r hrP2]; exact (haP2_mem r hrP2).1
      · rw [hnotS_eq r hrS, hψs]; exact hφsL
  · -- 非孤立情形：取 `adm` 并调用 `q4_case2_comb`
    push Not at hiso_ex
    rcases exists_admissible_coloring hm ⟨u, huS⟩ with ⟨adm⟩
    rcases ab_color_pack hm hab1_mem huab1 hab1e he1u hall_ab1 (adm.φ e₁) (adm.φs e₁) with
      ⟨forb₁, Pc₁, hPc1_2, hPc1_spec⟩
    rcases ab_color_pack hm hab2_mem huab2 hab2e he2u hall_ab2 (adm.φ e₂) (adm.φs e₂) with
      ⟨forb₂, Pc₂, hPc2_2, hPc2_spec⟩
    let Z₃v : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
    let Z₃w : Finset ℕ := L w₃ \ {adm.φ z₂, adm.φs z₂}
    have hZ3v : 2 ≤ Z₃v.card := by
      dsimp only [Z₃v]; have := card_sdiff_ge (L v₃) {adm.φ z₁, adm.φs z₁}
      have := Finset.card_le_two (a := adm.φ z₁) (b := adm.φs z₁); omega
    have hZ3w : 2 ≤ Z₃w.card := by
      dsimp only [Z₃w]; have := card_sdiff_ge (L w₃) {adm.φ z₂, adm.φs z₂}
      have := Finset.card_le_two (a := adm.φ z₂) (b := adm.φs z₂); omega
    let C : Finset ℕ := L u \ {forb₁, forb₂}
    have hC : Y.card + 3 ≤ C.card := by
      dsimp only [C]; have := card_sdiff_ge (L u) {forb₁, forb₂}
      have := Finset.card_le_two (a := forb₁) (b := forb₂); omega
    rcases q4_case2_comb (L := L) (Y := Y) (C := C) (P₁ := Pc₁) (P₂ := Pc₂)
      (F₁ := threeThreadGoodCols (L v₁) (L v₂) Z₃v (adm.φ z₁))
      (F₂ := threeThreadGoodCols (L w₁) (L w₂) Z₃w (adm.φ z₂)) hY_L2
      (fun _ => threeThreadGoodCols_nonempty hLv1 hLv2 (Finset.card_pos.mp (by omega)))
      (fun _ => threeThreadGoodCols_nonempty hLw1 hLw2 (Finset.card_pos.mp (by omega)))
      (threeThreadGoodCols_card_one_le_one C hLv1 hLv2 hZ3v)
      (le_trans (threeThreadGoodCols_card_one_le_one C hLw1 hLw2 hZ3w) (by omega))
      hPc1_2 hPc2_2 hC with ⟨α, hαC, c₁, hc₁, d₁, hd₁, c_ab1, hc_ab1, c_ab2, hc_ab2, aY, haY, γ, hγ⟩
    simp only [C, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hαC
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁ hd₁
    rcases hc₁ with ⟨⟨hc1L, hc1α⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
    rcases hd₁ with ⟨⟨hd1L, hd1α⟩, d₃, hd3Z, hd31, d₂, hd2B, hd21⟩
    simp only [Z₃v, Z₃w, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      at hc3Z hd3Z hc2B hd2B
    rcases hPc1_spec α hαC.2.1 c_ab1 hc_ab1 with
      ⟨hcab1L, hcab1α, hcab1e, hcab1se, aP₁, haP1_mem, haP1_pcf⟩
    rcases hPc2_spec α hαC.2.2 c_ab2 hc_ab2 with
      ⟨hcab2L, hcab2α, hcab2e, hcab2se, aP₂, haP2_mem, haP2_pcf⟩
    let ψ : V → ℕ := fun r =>
      if r = u then α else if r = v₁ then c₁ else if r = v₂ then c₂ else if r = v₃ then c₃
      else if r = w₁ then d₁ else if r = w₂ then d₂ else if r = w₃ then d₃
      else if r = ab₁ then c_ab1 else if r = ab₂ then c_ab2
      else if r ∈ Y then aY r else if r ∈ P₁ then aP₁ r else if r ∈ P₂ then aP₂ r else adm.φ r
    have hψu : ψ u = α := by simp [ψ]
    have hψv1 : ψ v₁ = c₁ := by simp [ψ, (G.ne_of_adj huv1).symm]
    have hψv2 : ψ v₂ = c₂ := by simp [ψ, hv2u, (G.ne_of_adj hv12).symm]
    have hψv3 : ψ v₃ = c₃ := by simp [ψ, hv3u, hv31, (G.ne_of_adj hv23).symm]
    have hψw1 : ψ w₁ = d₁ := by simp [ψ, (G.ne_of_adj huw1).symm, hvw1.symm, hv2w1.symm, hv3w1.symm]
    have hψw2 : ψ w₂ = d₂ := by
      simp [ψ, hw2u, hv1w2.symm, hv2w2.symm, hv3w2.symm, (G.ne_of_adj hw12).symm]
    have hψw3 : ψ w₃ = d₃ := by
      simp [ψ, hw3u, hv1w3.symm, hv2w3.symm, hv3w3.symm, hw31, (G.ne_of_adj hw23).symm]
    have hψab1 : ψ ab₁ = c_ab1 := by
      simp [ψ, (G.ne_of_adj huab1).symm, hab1v1, hab1v2, hab1v3, hab1w1, hab1w2, hab1w3]
    have hψab2 : ψ ab₂ = c_ab2 := by
      simp [ψ, (G.ne_of_adj huab2).symm, hab2v1, hab2v2, hab2v3, hab2w1, hab2w2, hab2w3, hab12.symm]
    have hψY : ∀ r ∈ Y, ψ r = aY r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega), hr]
    have hψP1 : ∀ r ∈ P₁, ψ r = aP₁ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P1_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega),
        hrY, hr]
    have hψP2 : ∀ r ∈ P₂, ψ r = aP₂ r := fun r hr => by
      have hdr1 : G.degree r = 1 := (mem_leafNbrs.mp hr).2
      have hrY : r ∉ Y := fun h => Finset.disjoint_left.mp hY_P2_disj h hr
      have hrP1 : r ∉ P₁ := fun h => Finset.disjoint_left.mp hP1_P2_disj h hr
      simp [ψ, (show r ≠ u by intro h; subst h; omega),
        (show r ≠ v₁ by intro h; subst h; omega), (show r ≠ v₂ by intro h; subst h; omega),
        (show r ≠ v₃ by intro h; subst h; omega), (show r ≠ w₁ by intro h; subst h; omega),
        (show r ≠ w₂ by intro h; subst h; omega), (show r ≠ w₃ by intro h; subst h; omega),
        (show r ≠ ab₁ by intro h; subst h; omega), (show r ≠ ab₂ by intro h; subst h; omega),
        hrY, hrP1, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := fun r hr => by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.1.1, hr.2.2.2.2.2.2.2.2.2.1.2, hr.2.2.2.2.2.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
      · rw [hψu]; exact hαC.1
      · rw [hψv1]; exact hc1L
      · rw [hψv2]; exact hc2B.1
      · rw [hψv3]; exact hc3Z.1
      · rw [hψw1]; exact hd1L
      · rw [hψw2]; exact hd2B.1
      · rw [hψw3]; exact hd3Z.1
      · rw [hψab1]; exact hcab1L
      · rw [hψab2]; exact hcab2L
      · rw [hψY r hrY]; exact (haY r hrY).1
      · rw [hψP1 r hrP1]; exact (haP1_mem r hrP1).1
      · rw [hψP2 r hrP2]; exact (haP2_mem r hrP2).1
    · intro r₁ r₂ h12 hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (haY' | haP1) | haP2
        · rcases hall_u b' hab with hb | hb | hb | hb | hbY
          · rw [hb, hψu, hψv1]; exact Ne.symm hc1α
          · rw [hb, hψu, hψw1]; exact Ne.symm hd1α
          · rw [hb, hψu, hψab1]; exact Ne.symm hcab1α
          · rw [hb, hψu, hψab2]; exact Ne.symm hcab2α
          · rw [hψu, hψY b' hbY]; exact (haY b' hbY).2.symm
        · rcases hall_v1 b' hab with hb | hb
          · rw [hb, hψv1, hψu]; exact hc1α
          · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
        · rcases hall_v2 b' hab with hb | hb
          · rw [hb, hψv2, hψv1]; exact hc21
          · rw [hb, hψv2, hψv3]; exact hc2B.2.2.1
        · rcases hall_v3 b' hab with hb | hb
          · rw [hb, hψv3, hψv2]; exact Ne.symm hc2B.2.2.1
          · rw [hb, hψv3, hψ_out z₁ hz1_not_S]; exact hc3Z.2.1
        · rcases hall_w1 b' hab with hb | hb
          · rw [hb, hψw1, hψu]; exact hd1α
          · rw [hb, hψw1, hψw2]; exact Ne.symm hd21
        · rcases hall_w2 b' hab with hb | hb
          · rw [hb, hψw2, hψw1]; exact hd21
          · rw [hb, hψw2, hψw3]; exact hd2B.2.2.1
        · rcases hall_w3 b' hab with hb | hb
          · rw [hb, hψw3, hψw2]; exact Ne.symm hd2B.2.2.1
          · rw [hb, hψw3, hψ_out z₂ hz2_not_S]; exact hd3Z.2.1
        · rcases hall_ab1 b' hab with hb | hb | hbP1
          · rw [hb, hψab1, hψu]; exact hcab1α
          · rw [hb, hψab1, hψ_out e₁ he1_not_S]; exact hcab1e
          · rw [hψab1, hψP1 b' hbP1]; exact (haP1_mem b' hbP1).2.symm
        · rcases hall_ab2 b' hab with hb | hb | hbP2
          · rw [hb, hψab2, hψu]; exact hcab2α
          · rw [hb, hψab2, hψ_out e₂ he2_not_S]; exact hcab2e
          · rw [hψab2, hψP2 b' hbP2]; exact (haP2_mem b' hbP2).2.symm
        · have hL := mem_leafNbrs.mp haY'
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = u := (huniq b' hab).trans (huniq u hL.1.symm).symm
          rw [hb, hψY a' haY', hψu]; exact (haY a' haY').2
        · have hL := mem_leafNbrs.mp haP1
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₁ := (huniq b' hab).trans (huniq ab₁ hL.1.symm).symm
          rw [hb, hψP1 a' haP1, hψab1]; exact (haP1_mem a' haP1).2
        · have hL := mem_leafNbrs.mp haP2
          rcases exists_unique_neighbor_of_deg_one hL.2 with ⟨t, _, huniq⟩
          have hb : b' = ab₂ := (huniq b' hab).trans (huniq ab₂ hL.1.symm).symm
          rw [hb, hψP2 a' haP2, hψab2]; exact (haP2_mem a' haP2).2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ h12 h1
      · exact (hcase r₂ r₁ h12.symm h2).symm
    · intro s hsS _ r hrS hsr
      rcases hS_out s hsS r hrS hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hψv3]; exact hc3Z.2.2
      · rw [hψw3]; exact hd3Z.2.2
      · rw [hψab1]; exact hcab1se
      · rw [hψab2]; exact hcab2se
    · intro s hsS hiso _
      rcases hiso_ex s hsS with ⟨t, htS, hst⟩
      exact False.elim (hiso t htS hst)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (hrY | hrP1) | hrP2
      · exact pcf_from_leaf_and_four huv1 huw1 huab1 huab2 (fun t ht => (mem_leafNbrs.mp ht).1) hψY
          hall_u (by rw [hψv1, hψw1, hψab1, hψab2]; exact hγ)
      · exact pcf_at_of_two_distinct_neighbors hdv1 huv1.symm hv12 hv2u.symm
          (by rw [hψu, hψv2]; exact Ne.symm hc2B.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdv2 hv12.symm hv23 hv31.symm
          (by rw [hψv1, hψv3]; exact Ne.symm hc31)
      · exact pcf_at_of_two_distinct_neighbors hdv3 hv23.symm hv3z hz1v2.symm
          (by rw [hψv2, hψ_out z₁ hz1_not_S]; exact hc2B.2.2.2)
      · exact pcf_at_of_two_distinct_neighbors hdw1 huw1.symm hw12 hw2u.symm
          (by rw [hψu, hψw2]; exact Ne.symm hd2B.2.1)
      · exact pcf_at_of_two_distinct_neighbors hdw2 hw12.symm hw23 hw31.symm
          (by rw [hψw1, hψw3]; exact Ne.symm hd31)
      · exact pcf_at_of_two_distinct_neighbors hdw3 hw23.symm hw3z hz2w2.symm
          (by rw [hψw2, hψ_out z₂ hz2_not_S]; exact hd2B.2.2.2)
      · exact haP1_pcf ψ hψu (hψ_out e₁ he1_not_S) hψP1
      · exact haP2_pcf ψ hψu (hψ_out e₂ he2_not_S) hψP2
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrY).2 (mem_leafNbrs.mp hrY).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrP1).2 (mem_leafNbrs.mp hrP1).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hrP2).2 (mem_leafNbrs.mp hrP2).1.symm

/-! ## 6. 主定理：引理 A 推论（消灭全部 8 个 `q = 4` 高代价阻塞配置） -/

/-- 引理 A 推论（消灭 `q = 4` 的全部 8 个高代价阻塞配置）：
若 `9 * p ≤ 22 * q`、`coreDeg G u = 4`、`1 ≤ |threeThreadNbrs G u|` 且
`|twoThreadNbrs G u| + |threeThreadNbrs G u| = 2`，则
`|threeThreadNbrs G u| ≤ |goodNbrs G u|`！ -/
lemma q4_three_thread_good_bound {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u : V}
    (hc4 : coreDeg G u = 4)
    (ht3 : 1 ≤ (threeThreadNbrs G u).card)
    (hlong2 : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card = 2) :
    (threeThreadNbrs G u).card ≤ (goodNbrs G u).card := by
  by_contra hlt
  push Not at hlt
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hfive := coreDeg_eq_five_parts hm hpq25 u
  by_cases hg1 : (goodNbrs G u).card = 1
  · exact q4_case_good_one hm hpq hc4 (by omega) hg1 (by omega)
  · have hg0 : (goodNbrs G u).card = 0 := by omega
    by_cases ht3_eq1 : (threeThreadNbrs G u).card = 1
    · exact q4_case_good_zero_t2 hm hpq hc4 ht3_eq1 (by omega) (by omega)
    · exact q4_case_good_zero_t3 hm hpq25 hc4 (by omega) (by omega)

end LeanResearch.Proposal3
