/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.CoreStructure

/-!
# 核心子图谓词、线串锚点关系与 `PCF`-代表系统双计数引擎（`ThreadDefs`）

本模块采用「零辅助图核心子图 `K = G - X`」范式，直接在原图 `G` 上定义：
1. 核心顶点集 `coreVerts G`、叶邻点集 `leafNbrs G u`、核心度 `coreDeg G u`、好点 `IsGood G u` 与坏点 `IsBad G u`；
2. `1`-线串、`2`-线串、`3`-线串的起点分类（`IsOneThreadStart` / `IsTwoThreadStart` / `IsThreeThreadStart`）
   及其不交划分恒等式；
3. 线串锚点二元关系 `IsThreadAnchor G u x`：证明在极小反例中，每个 `2`-度点恰有 `2` 个 `3⁺`-度锚点，
   且每个 `3⁺`-度点锚定的 `2`-度点总数精确等于 `n_{1-th} + 2·n_{2-th} + 3·n_{3-th}`；
4. `exists_pcfRep` 的单点集计数推论与双计数上界引理（显著压缩后续所有可约构型引理的篇幅）。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 核心子图 `K = G - X` 与好/坏顶点定义 -/

/-- 核心顶点集 `V(K) = {v ∈ V(G) | d_G(v) ≥ 2}`（在无孤立点图中等价于删去全体 `1`-度叶点）。 -/
def coreVerts {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => 2 ≤ G.degree v)

/-- 顶点 `u` 的 `1`-度叶邻点集合。 -/
def leafNbrs {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (G.neighborFinset u).filter (fun v => G.degree v = 1)

/-- 顶点 `u` 在核心子图 `K` 中的邻点集合 `N_G(u) ∩ V(K)`。 -/
def coreNbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  G.neighborFinset u ∩ coreVerts G

/-- 顶点 `u` 在核心子图 `K` 中的诱导度数 `d_K(u) = |N_G(u) ∩ V(K)|`。 -/
def coreDeg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℕ :=
  (coreNbrs G u).card

/-- 坏核心顶点：`d_G(u) ≥ 4` 且 `d_K(u) = 2`（即有 `d_G(u) - 2` 个 `1`-度叶邻点）。 -/
def IsBad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  4 ≤ G.degree u ∧ coreDeg G u = 2

/-- 好核心顶点：`d_K(u) ≥ 3`（自然满足 `d_G(u) ≥ 3`）。 -/
def IsGood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Prop :=
  3 ≤ coreDeg G u

/-- `IsBad G` 与 `IsGood G` 的可判定实例。 -/
instance instDecidablePredIsBad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (IsBad G) :=
  fun u => inferInstanceAs (Decidable (4 ≤ G.degree u ∧ coreDeg G u = 2))

instance instDecidablePredIsGood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (IsGood G) :=
  fun u => inferInstanceAs (Decidable (3 ≤ coreDeg G u))

/-- 顶点 `u` 的 `2`-度邻点集合。 -/
def degTwoNbrs {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Finset V :=
  (G.neighborFinset u).filter (fun v => G.degree v = 2)

/-- 顶点 `u` 的 `3⁺`-度邻点集合（核心 `3⁺`-邻点）。 -/
def degThreePlusNbrs {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Finset V :=
  (G.neighborFinset u).filter (fun v => 3 ≤ G.degree v)

lemma mem_coreVerts {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ coreVerts G ↔ 2 ≤ G.degree v := by
  simp [coreVerts]

lemma mem_leafNbrs {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ leafNbrs G u ↔ G.Adj u v ∧ G.degree v = 1 := by
  simp [leafNbrs, SimpleGraph.mem_neighborFinset]

lemma mem_coreNbrs {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ coreNbrs G u ↔ G.Adj u v ∧ 2 ≤ G.degree v := by
  simp [coreNbrs, coreVerts, SimpleGraph.mem_neighborFinset]

lemma coreNbrs_disjoint_leafNbrs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Disjoint (coreNbrs G u) (leafNbrs G u) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rw [mem_coreNbrs] at hv1
  rw [mem_leafNbrs] at hv2
  omega

lemma coreDeg_add_leafNbrs {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (u : V) :
    coreDeg G u + (leafNbrs G u).card = G.degree u := by
  have hun : coreNbrs G u ∪ leafNbrs G u = G.neighborFinset u := by
    ext v
    simp only [Finset.mem_union, mem_coreNbrs, mem_leafNbrs, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      have hge1 := degree_ge_one hm v
      by_cases h1 : G.degree v = 1
      · exact Or.inr ⟨h, h1⟩
      · exact Or.inl ⟨h, by omega⟩
  rw [coreDeg, ← Finset.card_union_of_disjoint (coreNbrs_disjoint_leafNbrs G u), hun,
      SimpleGraph.card_neighborFinset_eq_degree]

lemma coreDeg_le_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    coreDeg G u ≤ G.degree u := by
  rw [coreDeg, ← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

lemma leafNbrs_eq_empty_of_deg_le_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : G.degree u ≤ 3) :
    leafNbrs G u = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [mem_leafNbrs] at hv
  have := leaf_neighbor_deg_ge_four hm hv.2 hv.1.symm
  omega

lemma coreDeg_eq_degree_of_deg_le_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : G.degree u ≤ 3) :
    coreDeg G u = G.degree u := by
  have h := coreDeg_add_leafNbrs hm u
  rw [leafNbrs_eq_empty_of_deg_le_three hm hdu, Finset.card_empty] at h
  omega

lemma deg_ge_three_of_isGood {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u : V} (hg : IsGood G u) :
    3 ≤ G.degree u :=
  le_trans hg (coreDeg_le_degree G u)

lemma coreNbrs_eq_degTwo_union_degThreePlus {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    coreNbrs G u = degTwoNbrs G u ∪ degThreePlusNbrs G u := by
  ext v
  simp only [mem_coreNbrs, Finset.mem_union, degTwoNbrs, degThreePlusNbrs, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨h, hd⟩
    by_cases h2 : G.degree v = 2
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, by omega⟩
  · rintro (⟨h, hd⟩ | ⟨h, hd⟩) <;> exact ⟨h, by omega⟩

lemma degTwoNbrs_disjoint_degThreePlusNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Disjoint (degTwoNbrs G u) (degThreePlusNbrs G u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  simp only [degTwoNbrs, degThreePlusNbrs, Finset.mem_filter] at h1 h2
  omega

lemma coreDeg_eq_degTwo_add_degThreePlus {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    coreDeg G u = (degTwoNbrs G u).card + (degThreePlusNbrs G u).card := by
  rw [coreDeg, coreNbrs_eq_degTwo_union_degThreePlus,
      Finset.card_union_of_disjoint (degTwoNbrs_disjoint_degThreePlusNbrs G u)]

lemma coreVerts_nonempty {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) :
    (coreVerts G).Nonempty := by
  rcases exists_deg_ge_three hm with ⟨v, hv⟩
  exact ⟨v, mem_coreVerts.mpr (by omega)⟩

/-! ## 2. 线串起点分类与线串锚点关系 -/

/-- `v` 是从 `u` 出发的 `1`-线串的起点（`u-v-w`，`d(v)=2, d(w)≥3`）。 -/
def IsOneThreadStart {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  G.Adj u v ∧ G.degree v = 2 ∧ ∃ w : V, G.Adj v w ∧ w ≠ u ∧ 3 ≤ G.degree w

/-- `v` 是从 `u` 出发的 `2⁺`-线串（长线串）的起点（`u-v-w`，`d(v)=d(w)=2`）。 -/
def IsLongThreadStart {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  G.Adj u v ∧ G.degree v = 2 ∧ ∃ w : V, G.Adj v w ∧ w ≠ u ∧ G.degree w = 2

/-- `v` 是从 `u` 出发的 `2`-线串的起点（`u-v-w-z`，`d(v)=d(w)=2, d(z)≥3`）。 -/
def IsTwoThreadStart {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  G.Adj u v ∧ G.degree v = 2 ∧
  ∃ w z : V, G.Adj v w ∧ w ≠ u ∧ G.degree w = 2 ∧ G.Adj w z ∧ z ≠ v ∧ 3 ≤ G.degree z

/-- `v` 是从 `u` 出发的 `3`-线串的起点（`u-v-w-z-r`，`d(v)=d(w)=d(z)=2, d(r)≥3`）。 -/
def IsThreeThreadStart {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  G.Adj u v ∧ G.degree v = 2 ∧
  ∃ w z r : V, G.Adj v w ∧ w ≠ u ∧ G.degree w = 2 ∧
    G.Adj w z ∧ z ≠ v ∧ G.degree z = 2 ∧ G.Adj z r ∧ r ≠ w ∧ 3 ≤ G.degree r

/-- `u` 关联的 `1`-线串起点集合（`N_G(u)` 的子集）。 -/
noncomputable def oneThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact (degTwoNbrs G u).filter (fun v => IsOneThreadStart G u v)

/-- `u` 关联的 `2⁺`-线串起点集合（`N_G(u)` 的子集）。 -/
noncomputable def longThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact (degTwoNbrs G u).filter (fun v => IsLongThreadStart G u v)

/-- `u` 关联的 `2`-线串起点集合。 -/
noncomputable def twoThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact (degTwoNbrs G u).filter (fun v => IsTwoThreadStart G u v)

/-- `u` 关联的 `3`-线串起点集合。 -/
noncomputable def threeThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact (degTwoNbrs G u).filter (fun v => IsThreeThreadStart G u v)

/-- 在极小反例中，`2`-度邻点 `v` 恰为 `1`-线串或 `2⁺`-线串之一（互斥且完备）。 -/
lemma degTwo_thread_dichotomy {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v : V}
    (huv : G.Adj u v) (hdv : G.degree v = 2) :
    IsOneThreadStart G u v ∨ IsLongThreadStart G u v := by
  rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w, hvw, hwu, _⟩
  have hdw2 : 2 ≤ G.degree w := by
    have h1 := degree_ge_one hm w
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree w = 1) hvw.symm
    omega
  by_cases h2 : G.degree w = 2
  · exact Or.inr ⟨huv, hdv, w, hvw, hwu, h2⟩
  · exact Or.inl ⟨huv, hdv, w, hvw, hwu, by omega⟩

lemma not_oneThread_and_longThread {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    IsOneThreadStart G u v → IsLongThreadStart G u v → False := by
  rintro ⟨huv, hdv, w₁, hvw₁, hw₁u, hd1⟩ ⟨_, _, w₂, hvw₂, hw₂u, hd2⟩
  rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w, _, _, hall⟩
  have h1 : w₁ = w := (hall w₁ hvw₁).resolve_left hw₁u
  have h2 : w₂ = w := (hall w₂ hvw₂).resolve_left hw₂u
  rw [h1] at hd1; rw [h2] at hd2
  omega

/-- 在极小反例中，任意 `2⁺`-线串起点必为 `2`-线串或 `3`-线串之一（互斥且完备）。 -/
lemma longThread_dichotomy {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v : V}
    (hlong : IsLongThreadStart G u v) :
    IsTwoThreadStart G u v ∨ IsThreeThreadStart G u v := by
  rcases hlong with ⟨huv, hdv, w, hvw, hwu, hdw⟩
  rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨z, hwz, hzv, _⟩
  have hdz2 : 2 ≤ G.degree z := by
    have h1 := degree_ge_one hm z
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree z = 1) hwz.symm
    omega
  by_cases hdz : G.degree z = 2
  · rcases exists_other_neighbor_of_deg_two hdz hwz.symm with ⟨r, hzr, hrw, _⟩
    have hdr2 : 2 ≤ G.degree r := by
      have h1 := degree_ge_one hm r
      by_contra hlt; push Not at hlt
      have := leaf_neighbor_deg_ge_four hm (by omega : G.degree r = 1) hzr.symm
      omega
    have hdr3 : 3 ≤ G.degree r := by
      by_contra hlt; push Not at hlt
      have hdr_eq2 : G.degree r = 2 := by omega
      have hrv : r ≠ v := by
        intro h; subst r
        -- 若 `r = v`，则 `v-w-z-v` 为 3 个 `2`-度点闭环，与 `|V| ≥ 4` 矛盾
        have hNz := neighborFinset_eq_pair_of_deg_two hdz hwz.symm hzr (G.ne_of_adj hvw).symm
        have hNw := neighborFinset_eq_pair_of_deg_two hdw hvw.symm hwz hzv.symm
        have hNv := neighborFinset_eq_pair_of_deg_two hdv hvw hzr.symm (G.ne_of_adj hwz)
        have hall : ({v, w, z} : Finset V) = Finset.univ := by
          apply eq_univ_of_closed hm.conn (v₀ := v) (by simp)
          intro a ha b hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
          rcases ha with rfl | rfl | rfl
          · have : b ∈ ({w, z} : Finset V) := by
              rw [← hNv]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : b ∈ ({v, z} : Finset V) := by
              rw [← hNw]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : b ∈ ({w, v} : Finset V) := by
              rw [← hNz]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
        have hle := card_triple_le v w z
        rw [hall, Finset.card_univ] at hle
        have := card_ge_four hm; omega
      exact no_four_path_of_deg_two hm hdv hdw hdz hdr_eq2 hvw hwz hzr hzv.symm hrv.symm hrw.symm
    exact Or.inr ⟨huv, hdv, w, z, r, hvw, hwu, hdw, hwz, hzv, hdz, hzr, hrw, hdr3⟩
  · exact Or.inl ⟨huv, hdv, w, z, hvw, hwu, hdw, hwz, hzv, by omega⟩

lemma not_twoThread_and_threeThread {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    IsTwoThreadStart G u v → IsThreeThreadStart G u v → False := by
  rintro ⟨huv, hdv, w₁, z₁, hvw₁, hw₁u, hdw₁, hw₁z₁, hz₁v, hdz₁⟩
         ⟨_, _, w₂, z₂, _, hvw₂, hw₂u, _, hw₂z₂, hz₂v, hdz₂, _, _, _⟩
  rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w, _, _, hallv⟩
  have hw1 : w₁ = w := (hallv w₁ hvw₁).resolve_left hw₁u
  have hw2 : w₂ = w := (hallv w₂ hvw₂).resolve_left hw₂u
  subst hw1; rw [hw2] at hw₂z₂
  rcases exists_other_neighbor_of_deg_two hdw₁ hvw₁.symm with ⟨z, _, _, hallw⟩
  have hz1 : z₁ = z := (hallw z₁ hw₁z₁).resolve_left hz₁v
  have hz2 : z₂ = z := (hallw z₂ hw₂z₂).resolve_left hz₂v
  rw [hz1] at hdz₁; rw [hz2] at hdz₂
  omega

lemma degTwoNbrs_eq_one_union_long {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (u : V) :
    degTwoNbrs G u = oneThreadNbrs G u ∪ longThreadNbrs G u := by
  classical
  ext v
  simp only [Finset.mem_union, oneThreadNbrs, longThreadNbrs, Finset.mem_filter,
    degTwoNbrs, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨huv, hdv⟩
    rcases degTwo_thread_dichotomy hm huv hdv with h1 | h2
    · exact Or.inl ⟨⟨huv, hdv⟩, h1⟩
    · exact Or.inr ⟨⟨huv, hdv⟩, h2⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

lemma oneThreadNbrs_disjoint_longThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Disjoint (oneThreadNbrs G u) (longThreadNbrs G u) := by
  classical
  rw [Finset.disjoint_left]
  intro v h1 h2
  simp only [oneThreadNbrs, longThreadNbrs, Finset.mem_filter] at h1 h2
  exact not_oneThread_and_longThread h1.2 h2.2

lemma longThreadNbrs_eq_two_union_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (u : V) :
    longThreadNbrs G u = twoThreadNbrs G u ∪ threeThreadNbrs G u := by
  classical
  ext v
  simp only [Finset.mem_union, longThreadNbrs, twoThreadNbrs, threeThreadNbrs, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hlong⟩
    rcases longThread_dichotomy hm hlong with h2 | h3
    · exact Or.inl ⟨hv, h2⟩
    · exact Or.inr ⟨hv, h3⟩
  · rintro (⟨hv, h2⟩ | ⟨hv, h3⟩)
    · rcases h2 with ⟨huv, hdv, w, _, hvw, hwu, hdw, _, _, _⟩
      exact ⟨hv, huv, hdv, w, hvw, hwu, hdw⟩
    · rcases h3 with ⟨huv, hdv, w, _, _, hvw, hwu, hdw, _, _, _, _, _, _⟩
      exact ⟨hv, huv, hdv, w, hvw, hwu, hdw⟩

lemma twoThreadNbrs_disjoint_threeThreadNbrs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Disjoint (twoThreadNbrs G u) (threeThreadNbrs G u) := by
  classical
  rw [Finset.disjoint_left]
  intro v h1 h2
  simp only [twoThreadNbrs, threeThreadNbrs, Finset.mem_filter] at h1 h2
  exact not_twoThread_and_threeThread h1.2 h2.2

/-! ## 3. 线串锚点二元关系 `IsThreadAnchor` 及其双计数恒等式 -/

/-- `u` 是 `2`-度点 `x` 所在最长 `2`-度路径（线串）的一个 `3⁺`-度锚点：
通过至多 2 个内部 `2`-度点连接至 `x`（距离 1、2 或 3）。 -/
def IsThreadAnchor {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u x : V) : Prop :=
  3 ≤ G.degree u ∧ G.degree x = 2 ∧
  (G.Adj u x ∨
   (∃ v : V, G.degree v = 2 ∧ G.Adj u v ∧ G.Adj v x ∧ x ≠ u) ∨
   (∃ v w : V, G.degree v = 2 ∧ G.degree w = 2 ∧
      G.Adj u v ∧ G.Adj v w ∧ G.Adj w x ∧ u ≠ w ∧ v ≠ x ∧ u ≠ x))

/-- 辅助引理：在极小反例中，从 `2`-度点 `x` 沿一个方向 `a`（`G.Adj x a`）前进至首个 `3⁺`-度点，
恰有唯一 `u` 满足 `3 ≤ d(u)` 且经由该方向以长度 `≤ 3` 的 `2`-度路径连至 `x`。 -/
private lemma exists_unique_dir_anchor {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {x a : V}
    (hdx : G.degree x = 2) (hxa : G.Adj x a) :
    ∃ u : V, 3 ≤ G.degree u ∧
      ((u = a) ∨
       (G.degree a = 2 ∧ G.Adj a u ∧ u ≠ x) ∨
       (∃ b : V, G.degree a = 2 ∧ G.degree b = 2 ∧ G.Adj a b ∧ b ≠ x ∧
          G.Adj b u ∧ u ≠ a ∧ u ≠ x)) := by
  have hda2 : 2 ≤ G.degree a := by
    have h1 := degree_ge_one hm a
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree a = 1) hxa.symm; omega
  by_cases hda : G.degree a = 2
  · rcases exists_other_neighbor_of_deg_two hda hxa.symm with ⟨b, hab, hbx, _⟩
    have hdb2 : 2 ≤ G.degree b := by
      have h1 := degree_ge_one hm b
      by_contra hlt; push Not at hlt
      have := leaf_neighbor_deg_ge_four hm (by omega : G.degree b = 1) hab.symm; omega
    by_cases hdb : G.degree b = 2
    · rcases exists_other_neighbor_of_deg_two hdb hab.symm with ⟨u, hbu, hua, _⟩
      have hdu2 : 2 ≤ G.degree u := by
        have h1 := degree_ge_one hm u
        by_contra hlt; push Not at hlt
        have := leaf_neighbor_deg_ge_four hm (by omega : G.degree u = 1) hbu.symm; omega
      have hux : u ≠ x := by
        intro h; subst h
        have hNx := neighborFinset_eq_pair_of_deg_two hdx hxa hbu.symm (G.ne_of_adj hab)
        have hNa := neighborFinset_eq_pair_of_deg_two hda hxa.symm hab hbx.symm
        have hNb := neighborFinset_eq_pair_of_deg_two hdb hab.symm hbu (G.ne_of_adj hxa).symm
        have hall : ({u, a, b} : Finset V) = Finset.univ := by
          apply eq_univ_of_closed hm.conn (v₀ := u) (by simp)
          intro p hp r hpr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          rcases hp with rfl | rfl | rfl
          · have : r ∈ ({a, b} : Finset V) := by
              rw [← hNx]; exact (G.mem_neighborFinset p r).mpr hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : r ∈ ({u, b} : Finset V) := by
              rw [← hNa]; exact (G.mem_neighborFinset p r).mpr hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : r ∈ ({a, u} : Finset V) := by
              rw [← hNb]; exact (G.mem_neighborFinset p r).mpr hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
        have hle := card_triple_le u a b
        rw [hall, Finset.card_univ] at hle
        have := card_ge_four hm; omega
      have hdu3 : 3 ≤ G.degree u := by
        by_contra hlt; push Not at hlt
        exact no_four_path_of_deg_two hm hdx hda hdb (by omega) hxa hab hbu
          hbx.symm hux.symm hua.symm
      exact ⟨u, hdu3, Or.inr (Or.inr ⟨b, hda, hdb, hab, hbx, hbu, hua, hux⟩)⟩
    · exact ⟨b, by omega, Or.inr (Or.inl ⟨hda, hab, hbx⟩)⟩
  · exact ⟨a, by omega, Or.inl rfl⟩

/-- `2`-度点 `x` 的全体线串锚点集合。 -/
noncomputable def threadAnchors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => IsThreadAnchor G u x)

/-- 被 `3⁺`-度点 `u` 锚定的全体 `2`-度点集合。 -/
noncomputable def anchoredDegTwo {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => IsThreadAnchor G u x)

lemma mem_threadAnchors {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x u : V} :
    u ∈ threadAnchors G x ↔ IsThreadAnchor G u x := by
  classical
  simp [threadAnchors]

lemma mem_anchoredDegTwo {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ anchoredDegTwo G u ↔ IsThreadAnchor G u x := by
  classical
  simp [anchoredDegTwo]

/-- 在极小反例中，任意 `2`-度点 `x` 恰有 `2` 个满足 `IsThreadAnchor G u x` 的 `3⁺`-度锚点！ -/
lemma card_threadAnchors_eq_two {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {x : V} (hdx : G.degree x = 2) :
    (threadAnchors G x).card = 2 := by
  classical
  unfold threadAnchors
  rcases exists_two_neighbors_of_deg_two hdx with ⟨a₁, a₂, hxa₁, hxa₂, ha12, hallx⟩
  rcases exists_unique_dir_anchor hm hdx hxa₁ with ⟨u₁, hdu₁, hdir₁⟩
  rcases exists_unique_dir_anchor hm hdx hxa₂ with ⟨u₂, hdu₂, hdir₂⟩
  -- 证明 `u₁` 和 `u₂` 均满足 `IsThreadAnchor`
  have hanc₁ : IsThreadAnchor G u₁ x := by
    refine ⟨hdu₁, hdx, ?_⟩
    rcases hdir₁ with rfl | ⟨hda₁, ha₁u₁, hu₁x⟩ | ⟨b₁, hda₁, hdb₁, ha₁b₁, hb₁x, hb₁u₁, hu₁a₁, hu₁x⟩
    · exact Or.inl hxa₁.symm
    · exact Or.inr (Or.inl ⟨a₁, hda₁, ha₁u₁.symm, hxa₁.symm, hu₁x.symm⟩)
    · exact Or.inr (Or.inr ⟨b₁, a₁, hdb₁, hda₁, hb₁u₁.symm, ha₁b₁.symm, hxa₁.symm,
        hu₁a₁, hb₁x, hu₁x⟩)
  have hanc₂ : IsThreadAnchor G u₂ x := by
    refine ⟨hdu₂, hdx, ?_⟩
    rcases hdir₂ with rfl | ⟨hda₂, ha₂u₂, hu₂x⟩ | ⟨b₂, hda₂, hdb₂, ha₂b₂, hb₂x, hb₂u₂, hu₂a₂, hu₂x⟩
    · exact Or.inl hxa₂.symm
    · exact Or.inr (Or.inl ⟨a₂, hda₂, ha₂u₂.symm, hxa₂.symm, hu₂x.symm⟩)
    · exact Or.inr (Or.inr ⟨b₂, a₂, hdb₂, hda₂, hb₂u₂.symm, ha₂b₂.symm, hxa₂.symm,
        hu₂a₂, hb₂x, hu₂x⟩)
  -- 证明 `u₁ ≠ u₂`（否则出现长度 1/2/3 的同锚点线串或 4-路径或闭环！）
  have hu12 : u₁ ≠ u₂ := by
    intro heq; subst heq
    rcases hdir₁ with rfl | ⟨hda₁, ha₁u, hu₁x⟩ | ⟨b₁, hda₁, hdb₁, ha₁b₁, hb₁x, hb₁u, hu₁a₁, hu₁x⟩
    · rcases hdir₂ with h | ⟨hda₂, ha₂u, _⟩ | ⟨b₂, hda₂, hdb₂, ha₂b₂, hb₂x, hb₂u, hu₂a₂, _⟩
      · exact ha12 h
      · exact no_two_thread_same_anchor hm hdu₁ hdx hda₂ hxa₁.symm hxa₂ ha₂u
      · exact no_three_thread_same_anchor hm hdu₁ hdx hda₂ hdb₂ hxa₁.symm hxa₂ ha₂b₂ hb₂u
          hb₂x.symm
    · rcases hdir₂ with rfl | ⟨hda₂, ha₂u, _⟩ | ⟨b₂, hda₂, hdb₂, ha₂b₂, hb₂x, hb₂u, _, _⟩
      · exact no_two_thread_same_anchor hm hdu₁ hda₁ hdx ha₁u.symm hxa₁.symm hxa₂
      · exact no_three_thread_same_anchor hm hdu₁ hda₁ hdx hda₂ ha₁u.symm hxa₁.symm hxa₂ ha₂u
          ha12
      · -- `a₁ - x - a₂ - b₂` 为 4 个 `2`-度点（若 `b₂ = a₁` 则 3-闭环与 `|V| ≥ 4` 矛盾）
        have hb2a1 : b₂ ≠ a₁ := by
          intro h; subst h
          -- `a₁` 已有 `x` 和 `u₁`（3⁺度）为邻点，不可能邻 `a₂`（2度）
          rcases exists_other_neighbor_of_deg_two hda₁ hxa₁.symm with ⟨z, _, _, halla₁⟩
          have hz1 : u₁ = z := (halla₁ u₁ ha₁u).resolve_left hu₁x
          have hz2 : a₂ = z := (halla₁ a₂ ha₂b₂.symm).resolve_left (G.ne_of_adj hxa₂).symm
          rw [← hz2] at hz1; rw [hz1] at hdu₁; omega
        exact no_four_path_of_deg_two hm hda₁ hdx hda₂ hdb₂ hxa₁.symm hxa₂ ha₂b₂ ha12 hb2a1.symm
          hb₂x.symm
    · rcases hdir₂ with rfl | ⟨hda₂, ha₂u, _⟩ | ⟨b₂, hda₂, hdb₂, ha₂b₂, hb₂x, hb₂u, _, _⟩
      · exact no_three_thread_same_anchor hm hdu₁ hdb₁ hda₁ hdx hb₁u.symm ha₁b₁.symm hxa₁.symm
          hxa₂ hb₁x
      · have hb1a2 : b₁ ≠ a₂ := by
          intro h; subst h
          rcases exists_other_neighbor_of_deg_two hda₂ hxa₂.symm with ⟨z, _, _, halla₂⟩
          have hz1 : u₁ = z := (halla₂ u₁ ha₂u).resolve_left hu₁x
          have hz2 : a₁ = z := (halla₂ a₁ ha₁b₁.symm).resolve_left (G.ne_of_adj hxa₁).symm
          rw [← hz2] at hz1; rw [hz1] at hdu₁; omega
        exact no_four_path_of_deg_two hm hdb₁ hda₁ hdx hda₂ ha₁b₁.symm hxa₁.symm hxa₂ hb₁x hb1a2
          ha12
      · -- `b₁ - a₁ - x - a₂` 必为 4 个互异 `2`-度点！
        have hb1a2 : b₁ ≠ a₂ := by
          intro h; subst b₁
          -- `a₂` 有 `x` 和 `b₂`，故 `b₂` 不能既是 `a₁` 又不是 `a₁`；若 `b₁ = a₂` 则 `x-a₁-a₂-x` 是 3-闭环！
          have hNx := neighborFinset_eq_pair_of_deg_two hdx hxa₁ hxa₂ ha12
          have hNa₁ := neighborFinset_eq_pair_of_deg_two hda₁ hxa₁.symm ha₁b₁ (G.ne_of_adj hxa₂)
          have hNa₂ := neighborFinset_eq_pair_of_deg_two hda₂ hxa₂.symm ha₁b₁.symm
            (G.ne_of_adj hxa₁)
          have hall : ({x, a₁, a₂} : Finset V) = Finset.univ := by
            apply eq_univ_of_closed hm.conn (v₀ := x) (by simp)
            intro p hp r hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
            rcases hp with rfl | rfl | rfl
            · have : r ∈ ({a₁, a₂} : Finset V) := by
                rw [← hNx]; exact (G.mem_neighborFinset p r).mpr hpr
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl <;> simp
            · have : r ∈ ({x, a₂} : Finset V) := by
                rw [← hNa₁]; exact (G.mem_neighborFinset p r).mpr hpr
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl <;> simp
            · have : r ∈ ({x, a₁} : Finset V) := by
                rw [← hNa₂]; exact (G.mem_neighborFinset p r).mpr hpr
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl <;> simp
          have hle := card_triple_le x a₁ a₂
          rw [hall, Finset.card_univ] at hle
          have := card_ge_four hm; omega
        exact no_four_path_of_deg_two hm hdb₁ hda₁ hdx hda₂ ha₁b₁.symm hxa₁.symm hxa₂ hb₁x hb1a2
          ha12
  -- 证明过滤集精确等于 `{u₁, u₂}`！
  have hset : Finset.univ.filter (fun u => IsThreadAnchor G u x) = {u₁, u₂} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hdu, _, hpath⟩
      -- 断言沿 `a_i` 方向的唯一锚点就是 `u_i`
      have huniq : ∀ {a u₀ : V}, G.Adj x a → 3 ≤ G.degree u₀ →
          ((u₀ = a) ∨
           (G.degree a = 2 ∧ G.Adj a u₀ ∧ u₀ ≠ x) ∨
           (∃ b : V, G.degree a = 2 ∧ G.degree b = 2 ∧ G.Adj a b ∧ b ≠ x ∧
              G.Adj b u₀ ∧ u₀ ≠ a ∧ u₀ ≠ x)) →
          ((u = a) ∨
           (G.degree a = 2 ∧ G.Adj a u ∧ u ≠ x) ∨
           (∃ b : V, G.degree a = 2 ∧ G.degree b = 2 ∧ G.Adj a b ∧ b ≠ x ∧
              G.Adj b u ∧ u ≠ a ∧ u ≠ x)) → u = u₀ := by
        intro a u₀ hxa hdu₀ hd0 hdu_path
        rcases hd0 with rfl | ⟨hda, hau₀, hu₀x⟩ | ⟨b₀, hda, hdb₀, hab₀, hb₀x, hb₀u₀, hu₀a, _⟩
        · rcases hdu_path with rfl | ⟨hda, _, _⟩ | ⟨_, hda, _, _, _, _, _, _⟩
          · rfl
          · omega
          · omega
        · rcases hdu_path with rfl | ⟨_, hau, hux⟩ | ⟨b, _, hdb, hab, hbx, _, _, _⟩
          · omega
          · rcases exists_other_neighbor_of_deg_two hda hxa.symm with ⟨z, _, _, halla⟩
            exact ((halla u hau).resolve_left hux).trans ((halla u₀ hau₀).resolve_left hu₀x).symm
          · rcases exists_other_neighbor_of_deg_two hda hxa.symm with ⟨z, _, _, halla⟩
            have h1 : b = z := (halla b hab).resolve_left hbx
            have h2 : u₀ = z := (halla u₀ hau₀).resolve_left hu₀x
            rw [← h2] at h1; rw [h1] at hdb; omega
        · rcases hdu_path with rfl | ⟨_, hau, hux⟩ | ⟨b, _, hdb, hab, hbx, hbu, hua, _⟩
          · omega
          · rcases exists_other_neighbor_of_deg_two hda hxa.symm with ⟨z, _, _, halla⟩
            have h1 : u = z := (halla u hau).resolve_left hux
            have h2 : b₀ = z := (halla b₀ hab₀).resolve_left hb₀x
            rw [← h2] at h1; rw [h1] at hdu; omega
          · rcases exists_other_neighbor_of_deg_two hda hxa.symm with ⟨z, _, _, halla⟩
            have hb_eq : b = b₀ :=
              ((halla b hab).resolve_left hbx).trans ((halla b₀ hab₀).resolve_left hb₀x).symm
            subst hb_eq
            rcases exists_other_neighbor_of_deg_two hdb hab.symm with ⟨r, _, _, hallb⟩
            exact ((hallb u hbu).resolve_left hua).trans ((hallb u₀ hb₀u₀).resolve_left hu₀a).symm
      rcases hpath with hux | ⟨v, hdv, huv, hvx, hxu⟩ |
          ⟨v, w, hdv, hdw, huv, hvw, hwx, huw, hvx, hux⟩
      · rcases hallx u hux.symm with rfl | rfl
        · exact Or.inl (huniq hxa₁ hdu₁ hdir₁ (Or.inl rfl))
        · exact Or.inr (huniq hxa₂ hdu₂ hdir₂ (Or.inl rfl))
      · rcases hallx v hvx.symm with rfl | rfl
        · exact Or.inl (huniq hxa₁ hdu₁ hdir₁ (Or.inr (Or.inl ⟨hdv, huv.symm, hxu.symm⟩)))
        · exact Or.inr (huniq hxa₂ hdu₂ hdir₂ (Or.inr (Or.inl ⟨hdv, huv.symm, hxu.symm⟩)))
      · rcases hallx w hwx.symm with rfl | rfl
        · exact Or.inl (huniq hxa₁ hdu₁ hdir₁
            (Or.inr (Or.inr ⟨v, hdw, hdv, hvw.symm, hvx, huv.symm, huw, hux⟩)))
        · exact Or.inr (huniq hxa₂ hdu₂ hdir₂
            (Or.inr (Or.inr ⟨v, hdw, hdv, hvw.symm, hvx, huv.symm, huw, hux⟩)))
    · rintro (rfl | rfl)
      · exact hanc₁
      · exact hanc₂
  rw [hset, Finset.card_pair hu12]

/-- 每个 `3⁺`-度点 `u` 锚定的 `2`-度点总数精确等于
`1 * |oneThreadNbrs u| + 2 * |twoThreadNbrs u| + 3 * |threeThreadNbrs u|`！ -/
lemma card_anchored_degTwo_eq {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : 3 ≤ G.degree u) :
    (anchoredDegTwo G u).card =
      (oneThreadNbrs G u).card + 2 * (twoThreadNbrs G u).card + 3 * (threeThreadNbrs G u).card := by
  classical
  -- 对每个 `2`-度邻点 `v ∈ degTwoNbrs G u`，定义它对应的线串内部 `2`-度点集 `seg v`
  let seg : V → Finset V := fun v =>
    Finset.univ.filter (fun x => G.degree x = 2 ∧
      (x = v ∨
       (G.Adj v x ∧ x ≠ u) ∨
       (∃ w : V, G.degree w = 2 ∧ G.Adj v w ∧ w ≠ u ∧ G.Adj w x ∧ x ≠ v ∧ x ≠ u)))
  -- 1. 全体被 `u` 锚定的 `2`-度点恰好等于 `(degTwoNbrs G u).biUnion seg`
  have hunion : anchoredDegTwo G u = (degTwoNbrs G u).biUnion seg := by
    ext x
    rw [mem_anchoredDegTwo, Finset.mem_biUnion]
    simp only [seg, degTwoNbrs, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset, IsThreadAnchor]
    constructor
    · rintro ⟨_, hdx, hux | ⟨v, hdv, huv, hvx, hxu⟩ |
          ⟨v, w, hdv, hdw, huv, hvw, hwx, huw, hvx, hux⟩⟩
      · exact ⟨x, ⟨hux, hdx⟩, hdx, Or.inl rfl⟩
      · exact ⟨v, ⟨huv, hdv⟩, hdx, Or.inr (Or.inl ⟨hvx, hxu⟩)⟩
      · exact ⟨v, ⟨huv, hdv⟩, hdx,
          Or.inr (Or.inr ⟨w, hdw, hvw, huw.symm, hwx, hvx.symm, hux.symm⟩)⟩
    · rintro ⟨v, ⟨huv, hdv⟩, hdx, rfl | ⟨hvx, hxu⟩ | ⟨w, hdw, hvw, hwu, hwx, hxv, hxu⟩⟩
      · exact ⟨hdu, hdx, Or.inl huv⟩
      · exact ⟨hdu, hdx, Or.inr (Or.inl ⟨v, hdv, huv, hvx, hxu⟩)⟩
      · exact ⟨hdu, hdx,
          Or.inr (Or.inr ⟨v, w, hdv, hdw, huv, hvw, hwx, hwu.symm, hxv.symm, hxu.symm⟩)⟩
  -- 2. 任意不同 `v₁ ≠ v₂ ∈ degTwoNbrs G u` 对应的 `seg v₁` 与 `seg v₂` 互不相交！
  have hpw : (↑(degTwoNbrs G u) : Set V).PairwiseDisjoint seg := by
    intro v₁ hv₁ v₂ hv₂ hne
    change Disjoint (seg v₁) (seg v₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_coe, degTwoNbrs, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset] at hv₁ hv₂
    simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    rcases hv₁ with ⟨huv₁, hdv₁⟩
    rcases hv₂ with ⟨huv₂, hdv₂⟩
    rcases hx₁ with ⟨hdx, h1⟩
    rcases hx₂ with ⟨_, h2⟩
    rcases h1 with rfl | ⟨hv₁x, hxu⟩ | ⟨w₁, hdw₁, hv₁w₁, hw₁u, hw₁x, hxv₁, hxu⟩
    · rcases h2 with h | ⟨hv₂x, _⟩ | ⟨w₂, hdw₂, hv₂w₂, hw₂u, hw₂x, hxv₂, _⟩
      · exact hne h
      · exact no_two_thread_same_anchor hm hdu hdv₁ hdv₂ huv₁ hv₂x.symm huv₂.symm
      · exact no_three_thread_same_anchor hm hdu hdv₁ hdw₂ hdv₂ huv₁ hw₂x.symm hv₂w₂.symm huv₂.symm
          hne
    · rcases h2 with rfl | ⟨hv₂x, _⟩ | ⟨w₂, hdw₂, hv₂w₂, hw₂u, hw₂x, hxv₂, _⟩
      · exact no_two_thread_same_anchor hm hdu hdv₁ hdv₂ huv₁ hv₁x huv₂.symm
      · exact no_three_thread_same_anchor hm hdu hdv₁ hdx hdv₂ huv₁ hv₁x hv₂x.symm huv₂.symm hne
      · have hw2v1 : w₂ ≠ v₁ := by
          intro h; subst h
          rcases exists_other_neighbor_of_deg_two hdv₁ huv₁.symm with ⟨z, _, _, hallv₁⟩
          have h1 : x = z := (hallv₁ x hv₁x).resolve_left hxu
          have h2 : v₂ = z := (hallv₁ v₂ hv₂w₂.symm).resolve_left (G.ne_of_adj huv₂).symm
          -- 若 `x = v₂` 则与 `hxv₂` 矛盾！
          exact hxv₂ (h1.trans h2.symm)
        exact no_four_path_of_deg_two hm hdv₁ hdx hdw₂ hdv₂ hv₁x hw₂x.symm hv₂w₂.symm
          hw2v1.symm hne hxv₂
    · rcases h2 with rfl | ⟨hv₂x, _⟩ | ⟨w₂, hdw₂, hv₂w₂, hw₂u, hw₂x, hxv₂, _⟩
      · exact no_three_thread_same_anchor hm hdu hdv₁ hdw₁ hdv₂ huv₁ hv₁w₁ hw₁x huv₂.symm hne
      · have hw1v2 : w₁ ≠ v₂ := by
          intro h; subst h
          rcases exists_other_neighbor_of_deg_two hdv₂ huv₂.symm with ⟨z, _, _, hallv₂⟩
          have h1 : x = z := (hallv₂ x hv₂x).resolve_left hxu
          have h2 : v₁ = z := (hallv₂ v₁ hv₁w₁.symm).resolve_left (G.ne_of_adj huv₁).symm
          exact hxv₁ (h1.trans h2.symm)
        exact no_four_path_of_deg_two hm hdv₁ hdw₁ hdx hdv₂ hv₁w₁ hw₁x hv₂x.symm hxv₁.symm hne
          hw1v2
      · -- `v₁ - w₁ - x - w₂`（需证 `w₂ ≠ v₁`, `w₂ ≠ w₁`）
        have hw12 : w₁ ≠ w₂ := by
          intro h; subst h
          -- 若 `w₁ = w₂`，则 `w₁` 邻 `v₁, v₂, x`（三个互异点？但 `d(w₁) = 2`！）
          rcases exists_other_neighbor_of_deg_two hdw₁ hv₁w₁.symm with ⟨z, _, _, hallw₁⟩
          have h1 : x = z := (hallw₁ x hw₁x).resolve_left hxv₁
          have h2 : v₂ = z := (hallw₁ v₂ hv₂w₂.symm).resolve_left hne.symm
          exact hxv₂ (h1.trans h2.symm)
        have hw2v1 : w₂ ≠ v₁ := by
          intro h; subst h
          rcases exists_other_neighbor_of_deg_two hdv₁ huv₁.symm with ⟨z, _, _, hallv₁⟩
          have h1 : w₁ = z := (hallv₁ w₁ hv₁w₁).resolve_left hw₁u
          have h2 : v₂ = z := (hallv₁ v₂ hv₂w₂.symm).resolve_left (G.ne_of_adj huv₂).symm
          -- 若 `w₁ = v₂`，则 `v₁ - v₂ - u - v₁` 为 `2`-线串同锚点 `u`！
          exact no_two_thread_same_anchor hm hdu hdv₁ hdv₂ huv₁ (h1.trans h2.symm ▸ hv₁w₁) huv₂.symm
        exact no_four_path_of_deg_two hm hdv₁ hdw₁ hdx hdw₂ hv₁w₁ hw₁x hw₂x.symm hxv₁.symm
          hw2v1.symm hw12
  -- 3. 按 `1-/2-/3-` 线串精确计算 `seg v` 的大小！
  have hseg1 : ∀ v ∈ oneThreadNbrs G u, (seg v).card = 1 := by
    intro v hv
    simp only [oneThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
    rcases hv with ⟨⟨huv, hdv⟩, _, _, w₀, hvw₀, hw₀u, hdw₀⟩
    rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w', _, _, hallv⟩
    have hw_uniq : ∀ x, G.Adj v x → x ≠ u → x = w₀ := fun x hvx hxu =>
      ((hallv x hvx).resolve_left hxu).trans ((hallv w₀ hvw₀).resolve_left hw₀u).symm
    have hEq : seg v = {v} := by
      ext x; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hdx, rfl | ⟨hvx, hxu⟩ | ⟨w, hdw, hvw, hwu, _, _, _⟩⟩
        · rfl
        · rw [hw_uniq x hvx hxu] at hdx; omega
        · rw [hw_uniq w hvw hwu] at hdw; omega
      · rintro rfl; exact ⟨hdv, Or.inl rfl⟩
    rw [hEq, Finset.card_singleton]
  have hseg2 : ∀ v ∈ twoThreadNbrs G u, (seg v).card = 2 := by
    intro v hv
    simp only [twoThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
    rcases hv with ⟨⟨huv, hdv⟩, _, _, w₀, z₀, hvw₀, hw₀u, hdw₀, hw₀z₀, hz₀v, hdz₀⟩
    rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w', _, _, hallv⟩
    have hw_uniq : ∀ x, G.Adj v x → x ≠ u → x = w₀ := fun x hvx hxu =>
      ((hallv x hvx).resolve_left hxu).trans ((hallv w₀ hvw₀).resolve_left hw₀u).symm
    rcases exists_other_neighbor_of_deg_two hdw₀ hvw₀.symm with ⟨z', _, _, hallw⟩
    have hz_uniq : ∀ x, G.Adj w₀ x → x ≠ v → x = z₀ := fun x hwx hxv =>
      ((hallw x hwx).resolve_left hxv).trans ((hallw z₀ hw₀z₀).resolve_left hz₀v).symm
    have hEq : seg v = {v, w₀} := by
      ext x; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hdx, rfl | ⟨hvx, hxu⟩ | ⟨w, _, hvw, hwu, hwx, hxv, _⟩⟩
        · exact Or.inl rfl
        · exact Or.inr (hw_uniq x hvx hxu)
        · have hw : w = w₀ := hw_uniq w hvw hwu
          rw [hw] at hwx
          rw [hz_uniq x hwx hxv] at hdx; omega
      · rintro (rfl | rfl)
        · exact ⟨hdv, Or.inl rfl⟩
        · exact ⟨hdw₀, Or.inr (Or.inl ⟨hvw₀, hw₀u⟩)⟩
    rw [hEq, Finset.card_pair (G.ne_of_adj hvw₀)]
  have hseg3 : ∀ v ∈ threeThreadNbrs G u, (seg v).card = 3 := by
    intro v hv
    simp only [threeThreadNbrs, degTwoNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hv
    rcases hv with ⟨⟨huv, hdv⟩, _, _, w₀, z₀, r₀, hvw₀, hw₀u, hdw₀, hw₀z₀, hz₀v, hdz₀, hz₀r₀,
      hr₀w₀, hdr₀⟩
    rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w', _, _, hallv⟩
    have hw_uniq : ∀ x, G.Adj v x → x ≠ u → x = w₀ := fun x hvx hxu =>
      ((hallv x hvx).resolve_left hxu).trans ((hallv w₀ hvw₀).resolve_left hw₀u).symm
    rcases exists_other_neighbor_of_deg_two hdw₀ hvw₀.symm with ⟨z', _, _, hallw⟩
    have hz_uniq : ∀ x, G.Adj w₀ x → x ≠ v → x = z₀ := fun x hwx hxv =>
      ((hallw x hwx).resolve_left hxv).trans ((hallw z₀ hw₀z₀).resolve_left hz₀v).symm
    have hz₀u : z₀ ≠ u := fun h => by subst h; omega
    have hEq : seg v = {v, w₀, z₀} := by
      ext x; simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl | ⟨hvx, hxu⟩ | ⟨w, _, hvw, hwu, hwx, hxv, _⟩⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (hw_uniq x hvx hxu))
        · have hw : w = w₀ := hw_uniq w hvw hwu
          rw [hw] at hwx
          exact Or.inr (Or.inr (hz_uniq x hwx hxv))
      · rintro (rfl | rfl | rfl)
        · exact ⟨hdv, Or.inl rfl⟩
        · exact ⟨hdw₀, Or.inr (Or.inl ⟨hvw₀, hw₀u⟩)⟩
        · exact ⟨hdz₀, Or.inr (Or.inr ⟨w₀, hdw₀, hvw₀, hw₀u, hw₀z₀, hz₀v, hz₀u⟩)⟩
    rw [hEq, Finset.card_insert_of_notMem, Finset.card_pair (G.ne_of_adj hw₀z₀)]
    simp [G.ne_of_adj hvw₀, hz₀v.symm]
  -- 4. 合并三类线串求和！
  rw [hunion, Finset.card_biUnion hpw, degTwoNbrs_eq_one_union_long hm u,
      Finset.sum_union (oneThreadNbrs_disjoint_longThreadNbrs G u),
      longThreadNbrs_eq_two_union_three hm u,
      Finset.sum_union (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
  rw [Finset.sum_congr rfl hseg1, Finset.sum_congr rfl hseg2, Finset.sum_congr rfl hseg3]
  simp only [Finset.sum_const, smul_eq_mul]
  ring

/-! ## 4. `PCF`-代表系统单点集下界与双计数通用引理 -/

/-- `B = []` 时，若 `¬ ∃ a, IsPCFRep A [] a` 且索引数 `≥ 4`，则单点集数量 `≥ 4`（且 `2 * D ≤ q`）。 -/
lemma no_pcfRep_nil_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Finset ℕ} (hne : ∀ i, (A i).Nonempty)
    (hno : ¬ ∃ a : ι → ℕ, IsPCFRep A [] a) :
    let q := (Finset.univ.filter (fun i => (A i).card = 1)).card
    (∀ j : ι, (A j).card ≤ q / 2 ∨ q = Fintype.card ι) ∧
    (4 ≤ Fintype.card ι → 4 ≤ q) := by
  intro q
  have hbound : ∀ j : ι, (A j).card ≤ q / 2 := by
    intro j
    by_contra hlt; push Not at hlt
    apply hno
    apply exists_pcfRep A hne []
    right; refine ⟨j, ?_⟩
    simp only [List.toFinset_nil, Finset.filter_empty, Finset.card_empty, zero_add, Nat.sub_zero]
    exact hlt
  refine ⟨fun j => Or.inl (hbound j), ?_⟩
  intro hcard4
  by_cases hall1 : ∀ j : ι, (A j).card = 1
  · have hqeq : q = Fintype.card ι := by
      dsimp only [q]
      rw [Finset.filter_true_of_mem (fun j _ => hall1 j), Finset.card_univ]
    omega
  · push Not at hall1
    rcases hall1 with ⟨j, hj⟩
    have hge2 : 2 ≤ (A j).card := by have := (hne j).card_pos; omega
    have := hbound j
    omega

/-- `B = [β]` 时，若 `¬ ∃ a, IsPCFRep A [β] a`，则对任意 `j` 有 `(A j).card ≤ 1 + (q - 1) / 2`，
进而推出：`3 ≤ card ι → 3 ≤ q`、`∃ j, 3 ≤ (A j).card → 5 ≤ q`、`∃ j, 4 ≤ (A j).card → 7 ≤ q`！ -/
lemma no_pcfRep_single_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Finset ℕ} (hne : ∀ i, (A i).Nonempty) {β : ℕ}
    (hno : ¬ ∃ a : ι → ℕ, IsPCFRep A [β] a) :
    let q := (Finset.univ.filter (fun i => (A i).card = 1)).card
    1 ≤ q ∧
    (∀ j : ι, (A j).card ≤ 1 + (q - 1) / 2) ∧
    (3 ≤ Fintype.card ι → 3 ≤ q) ∧
    ((∃ j : ι, 3 ≤ (A j).card) → 5 ≤ q) ∧
    ((∃ j : ι, 4 ≤ (A j).card) → 7 ≤ q) := by
  intro q
  have huniq : (([β] : List ℕ).toFinset.filter (fun c => ([β] : List ℕ).count c = 1)).card = 1 := by
    have hEq : ([β] : List ℕ).toFinset.filter (fun c => ([β] : List ℕ).count c = 1) = {β} := by
      ext c
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
        Finset.mem_singleton]
      exact ⟨And.left, fun h => ⟨h, by subst h; simp⟩⟩
    rw [hEq, Finset.card_singleton]
  have hmult : (([β] : List ℕ).toFinset.filter (fun c => 2 ≤ ([β] : List ℕ).count c)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc
    have hcb : c = β := by simpa using hc
    subst hcb; simp
  have hq1 : 1 ≤ q := by
    by_contra hlt; push Not at hlt
    apply hno; apply exists_pcfRep A hne [β]
    left; dsimp only [q] at hlt; rw [huniq]; omega
  have hbound : ∀ j : ι, (A j).card ≤ 1 + (q - 1) / 2 := by
    intro j
    by_contra hlt; push Not at hlt
    apply hno; apply exists_pcfRep A hne [β]
    right; refine ⟨j, ?_⟩
    rw [hmult, huniq, zero_add]; exact hlt
  refine ⟨hq1, hbound, ?_, ?_, ?_⟩
  · intro hcard3
    by_cases hall1 : ∀ j : ι, (A j).card = 1
    · have hqeq : q = Fintype.card ι := by
        dsimp only [q]
        rw [Finset.filter_true_of_mem (fun j _ => hall1 j), Finset.card_univ]
      omega
    · push Not at hall1
      rcases hall1 with ⟨j, hj⟩
      have hge2 : 2 ≤ (A j).card := by have := (hne j).card_pos; omega
      have := hbound j; omega
  · rintro ⟨j, hj⟩; have := hbound j; omega
  · rintro ⟨j, hj⟩; have := hbound j; omega

/-- `B = [c₁, c₂]` 时，若 `¬ ∃ a, IsPCFRep A [c₁, c₂] a` 且 `2 ≤ card ι`，
则单点集数量 `q ≥ 2`（无论 `c₁ = c₂` 与否）！ -/
lemma no_pcfRep_pair_ge_two {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Finset ℕ} (hne : ∀ i, (A i).Nonempty)
    {c₁ c₂ : ℕ} (hcard2 : 2 ≤ Fintype.card ι)
    (hno : ¬ ∃ a : ι → ℕ, IsPCFRep A [c₁, c₂] a) :
    2 ≤ (Finset.univ.filter (fun i => (A i).card = 1)).card := by
  by_cases heq : c₁ = c₂
  · subst heq
    have huniq :
        (([c₁, c₁] : List ℕ).toFinset.filter
          (fun c => ([c₁, c₁] : List ℕ).count c = 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro c hc
      have hcc : c = c₁ := by simpa using hc
      subst hcc; simp
    have hmult :
        (([c₁, c₁] : List ℕ).toFinset.filter
          (fun c => 2 ≤ ([c₁, c₁] : List ℕ).count c)).card = 1 := by
      have hE : ([c₁, c₁] : List ℕ).toFinset.filter
          (fun c => 2 ≤ ([c₁, c₁] : List ℕ).count c) = {c₁} := by
        ext c
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
          or_self, Finset.mem_singleton]
        exact ⟨And.left, fun h => ⟨h, by subst h; simp⟩⟩
      rw [hE, Finset.card_singleton]
    by_cases hall1 : ∀ j : ι, (A j).card = 1
    · rw [Finset.filter_true_of_mem (fun j _ => hall1 j), Finset.card_univ]; exact hcard2
    · push Not at hall1; rcases hall1 with ⟨j, hj⟩
      have hge2 : 2 ≤ (A j).card := by have := (hne j).card_pos; omega
      by_contra hlt; push Not at hlt
      apply hno; apply exists_pcfRep A hne [c₁, c₁]
      right; refine ⟨j, ?_⟩
      rw [hmult, huniq]; omega
  · have huniq :
        (([c₁, c₂] : List ℕ).toFinset.filter
          (fun c => ([c₁, c₂] : List ℕ).count c = 1)).card = 2 := by
      have hE : ([c₁, c₂] : List ℕ).toFinset.filter
          (fun c => ([c₁, c₂] : List ℕ).count c = 1) = {c₁, c₂} := by
        ext c
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact And.left
        · rintro (rfl | rfl)
          · refine ⟨Or.inl rfl, ?_⟩
            simp [heq]
          · refine ⟨Or.inr rfl, ?_⟩
            simp [heq]
      rw [hE, Finset.card_pair heq]
    by_contra hlt; push Not at hlt
    apply hno; apply exists_pcfRep A hne [c₁, c₂]
    left; rw [huniq]; omega

/-- 若 `|P| ≥ 2`，则 `{α ∈ C | |P \ {α}| = 1}` 至多含 `2` 个元素；若恰有 `2` 个，则 `|P| = 2 ∧ P ⊆ C`。 -/
lemma card_filter_sdiff_singleton_eq_one_le (C P : Finset ℕ) (hP : 2 ≤ P.card) :
    (C.filter (fun α => (P \ {α}).card = 1)).card ≤ 2 ∧
    ((C.filter (fun α => (P \ {α}).card = 1)).card = 2 → P.card = 2 ∧ P ⊆ C) := by
  have hsub : C.filter (fun α => (P \ {α}).card = 1) ⊆ P := by
    intro α hα
    rw [Finset.mem_filter] at hα
    by_contra hnot
    have hEq : P \ {α} = P := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨And.left, fun hx => ⟨hx, fun h => hnot (h ▸ hx)⟩⟩
    rw [hEq] at hα; omega
  have hP2_of_mem : ∀ α ∈ C.filter (fun α => (P \ {α}).card = 1), P.card = 2 := by
    intro α hα
    have hαP : α ∈ P := hsub hα
    have h1 : (P \ {α}).card = 1 := (Finset.mem_filter.mp hα).2
    have h2 := Finset.card_sdiff_add_card_inter P {α}
    have h3 : P ∩ {α} = {α} := by ext z; simp [hαP]
    rw [h3, Finset.card_singleton] at h2; omega
  by_cases hne : (C.filter (fun α => (P \ {α}).card = 1)).Nonempty
  · rcases hne with ⟨α₀, hα₀⟩
    have hP2 : P.card = 2 := hP2_of_mem α₀ hα₀
    have hle : (C.filter (fun α => (P \ {α}).card = 1)).card ≤ 2 := by
      calc (C.filter (fun α => (P \ {α}).card = 1)).card ≤ P.card := Finset.card_le_card hsub
        _ = 2 := hP2
    refine ⟨hle, fun heq => ⟨hP2, ?_⟩⟩
    have hEq : C.filter (fun α => (P \ {α}).card = 1) = P :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← hEq]
    exact Finset.filter_subset _ C
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]
    exact ⟨by omega, fun h => by omega⟩

/-- 若 `|L| = 4` 且对每个 `α` 都有色 `c α`，则 `{α ∈ C | |L \ {α, c α, z}| = 1}` 至多含 `3` 个元素；
若恰有 `3` 个，则 `z ∈ L ∧ L \ {z} ⊆ C`。 -/
lemma card_filter_sdiff_triple_eq_one_le (C L : Finset ℕ) (hL : L.card = 4)
    (c : ℕ → ℕ) (z : ℕ) :
    (C.filter (fun α => (L \ {α, c α, z}).card = 1)).card ≤ 3 ∧
    ((C.filter (fun α => (L \ {α, c α, z}).card = 1)).card = 3 → z ∈ L ∧ L \ {z} ⊆ C) := by
  have hmem_z_and_sub : ∀ α ∈ C.filter (fun α => (L \ {α, c α, z}).card = 1),
      z ∈ L ∧ α ∈ L \ {z} := by
    intro α hα
    rw [Finset.mem_filter] at hα
    have h1 := hα.2
    have h2 := Finset.card_sdiff_add_card_inter L {α, c α, z}
    have hcard_inter : (L ∩ {α, c α, z}).card = 3 := by
      have hle : (L ∩ {α, c α, z}).card ≤ 3 :=
        le_trans (Finset.card_le_card (Finset.inter_subset_right (s₁ := L)))
          (card_triple_le α (c α) z)
      omega
    have hcard_tri : ({α, c α, z} : Finset ℕ).card = 3 := by
      have hle1 : (L ∩ {α, c α, z}).card ≤ ({α, c α, z} : Finset ℕ).card :=
        Finset.card_le_card Finset.inter_subset_right
      have hle2 := card_triple_le α (c α) z
      omega
    have hEq : L ∩ {α, c α, z} = {α, c α, z} :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hsub3 : ({α, c α, z} : Finset ℕ) ⊆ L := by
      intro x hx; rw [← hEq] at hx; exact (Finset.mem_inter.mp hx).1
    have hzL : z ∈ L := hsub3 (by simp)
    have hαL : α ∈ L := hsub3 (by simp)
    have hαz : α ≠ z := by
      intro heq; subst heq
      have : ({α, c α, α} : Finset ℕ) = {α, c α} := by ext x; simp; tauto
      rw [this] at hcard_tri
      have := Finset.card_le_two (a := α) (b := c α); omega
    exact ⟨hzL, Finset.mem_sdiff.mpr ⟨hαL, by simp [hαz]⟩⟩
  have hsub : C.filter (fun α => (L \ {α, c α, z}).card = 1) ⊆ L \ {z} :=
    fun α hα => (hmem_z_and_sub α hα).2
  by_cases hne : (C.filter (fun α => (L \ {α, c α, z}).card = 1)).Nonempty
  · rcases hne with ⟨α₀, hα₀⟩
    have hzL : z ∈ L := (hmem_z_and_sub α₀ hα₀).1
    have hLz3 : (L \ {z}).card = 3 := by
      have h := Finset.card_sdiff_add_card_inter L {z}
      have hi : L ∩ {z} = {z} := by ext x; simp [hzL]
      rw [hi, Finset.card_singleton] at h; omega
    have hle : (C.filter (fun α => (L \ {α, c α, z}).card = 1)).card ≤ 3 := by
      calc (C.filter (fun α => (L \ {α, c α, z}).card = 1)).card ≤ (L \ {z}).card :=
            Finset.card_le_card hsub
        _ = 3 := hLz3
    refine ⟨hle, fun heq => ⟨hzL, ?_⟩⟩
    have hEq : C.filter (fun α => (L \ {α, c α, z}).card = 1) = L \ {z} :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← hEq]
    exact Finset.filter_subset _ C
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]
    exact ⟨by omega, fun h => by omega⟩

/-- 若 `|L| = 4` 且 `η, θ` 固定，则 `{α ∈ C | |L \ {α, η, θ}| = 1}` 至多含 `2` 个元素；
若恰有 `2` 个，则 `η ≠ θ ∧ {η, θ} ⊆ L ∧ L \ {η, θ} ⊆ C`。 -/
lemma card_filter_sdiff_two_fixed_eq_one_le (C L : Finset ℕ) (hL : L.card = 4) (η θ : ℕ) :
    (C.filter (fun α => (L \ {α, η, θ}).card = 1)).card ≤ 2 ∧
    ((C.filter (fun α => (L \ {α, η, θ}).card = 1)).card = 2 →
      η ≠ θ ∧ η ∈ L ∧ θ ∈ L ∧ L \ {η, θ} ⊆ C) := by
  have hEq_sdiff : ∀ α, L \ {α, η, θ} = (L \ {η, θ}) \ {α} := by
    intro α; ext x; simp; tauto
  have hP2 : 2 ≤ (L \ {η, θ}).card := by
    have := card_sdiff_ge L {η, θ}
    have := Finset.card_le_two (a := η) (b := θ); omega
  have hcore := card_filter_sdiff_singleton_eq_one_le C (L \ {η, θ}) hP2
  have hfilt : C.filter (fun α => (L \ {α, η, θ}).card = 1) =
      C.filter (fun α => ((L \ {η, θ}) \ {α}).card = 1) := by
    congr 1; ext α; rw [hEq_sdiff]
  rw [hfilt]
  refine ⟨hcore.1, fun heq => ?_⟩
  rcases hcore.2 heq with ⟨hcard2, hsub⟩
  have hinter : (L ∩ {η, θ}).card = 2 := by
    have := Finset.card_sdiff_add_card_inter L {η, θ}; omega
  have hpair2 : ({η, θ} : Finset ℕ).card = 2 := by
    have h1 : (L ∩ {η, θ}).card ≤ ({η, θ} : Finset ℕ).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h2 := Finset.card_le_two (a := η) (b := θ); omega
  have hne : η ≠ θ := by
    intro h; subst h; simp at hpair2
  have hEqI : L ∩ {η, θ} = {η, θ} :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hsub2 : ({η, θ} : Finset ℕ) ⊆ L := by
    intro x hx; rw [← hEqI] at hx; exact (Finset.mem_inter.mp hx).1
  exact ⟨hne, hsub2 (by simp), hsub2 (by simp), hsub⟩

/-- 双计数交换求和：`∑ α ∈ C, (I.filter (P α)).card = ∑ i ∈ I, (C.filter (fun α => P α i)).card`。 -/
lemma sum_filter_card_comm {α β : Type*}
    (C : Finset α) (I : Finset β) (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    ∑ a ∈ C, (I.filter (fun b => P a b)).card =
      ∑ b ∈ I, (C.filter (fun a => P a b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

end LeanResearch.Proposal3
