/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BeyondDefs

/-!
# 线串顶点划分与整数放大 36 倍加权放电引擎（`ThreadPartition`）

本模块为 `mad(G) < 22/9` 的整数放大 36 倍放电论证建立全部线串分类与精确求和基础设施：
1. 定义 `2`-度点按所属线串长度的本征谓词 `IsOneThreadVert` 与 `IsTwoThreadVert`；
2. 定义 `anchoredTwoThreads` 与 `anchoredThreeThreads`，证明对任意 `3⁺`-度点 `u`，
   `anchoredDegTwo G u` 按线串长度恰好三分，三部分基数精确等于
   `|oneThreadNbrs G u|`、`2 * |twoThreadNbrs G u|` 与 `3 * |threeThreadNbrs G u|`；
3. 定义参数化线串转权函数 `wThread G P1 P2 u x : ℤ`（对 `1`-线串送 `6/8/10`，对 `2`-线串送
   `7/8/9`，对 `3`-线串送 `8`），证明任意 `2`-度点接收总量恒等于 `16`，并给出 `3⁺`-度点送出
   总量的通用上界 `10*n₁ + 18*n₂ + 24*n₃` 与精确三分拆解公式。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. `2`-度点的线串长度本征分类 -/

/-- `1`-线串内部点：`2`-度点，且其两个邻点均为 `3⁺`-度点。 -/
def IsOneThreadVert {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Prop :=
  G.degree x = 2 ∧ ∀ y, G.Adj x y → 3 ≤ G.degree y

/-- `2`-线串内部点：`2`-度点，恰邻接一个 `2`-度点 `y`（且 `x, y` 各自的另一邻点均为 `3⁺`-度点）。 -/
def IsTwoThreadVert {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Prop :=
  G.degree x = 2 ∧ ∃ y, G.Adj x y ∧ G.degree y = 2 ∧
    (∀ z, G.Adj x z → z ≠ y → 3 ≤ G.degree z) ∧
    (∀ w, G.Adj y w → w ≠ x → 3 ≤ G.degree w)

lemma isOneThreadVert_not_isTwoThreadVert {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V}
    (h1 : IsOneThreadVert G x) : ¬ IsTwoThreadVert G x := by
  rintro ⟨_, y, hxy, hdy, _, _⟩
  have := h1.2 y hxy; omega

lemma isTwoThreadVert_partner_unique {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y y' : V}
    (hxy' : G.Adj x y') (hdy' : G.degree y' = 2)
    (hother : ∀ z, G.Adj x z → z ≠ y → 3 ≤ G.degree z) : y' = y := by
  by_contra hne
  have := hother y' hxy' hne; omega

lemma isTwoThreadVert_symm {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hdx : G.degree x = 2) (hxy : G.Adj x y) (hdy : G.degree y = 2)
    (hx3 : ∀ z, G.Adj x z → z ≠ y → 3 ≤ G.degree z)
    (hy3 : ∀ w, G.Adj y w → w ≠ x → 3 ≤ G.degree w) :
    IsTwoThreadVert G y :=
  ⟨hdy, x, hxy.symm, hdx, hy3, hx3⟩

/-- `u` 锚定的 `1`-线串内部点集。 -/
noncomputable def anchoredOneThreads {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical exact (anchoredDegTwo G u).filter (IsOneThreadVert G)

/-- `u` 锚定的 `2`-线串内部点集。 -/
noncomputable def anchoredTwoThreads {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical exact (anchoredDegTwo G u).filter (IsTwoThreadVert G)

/-- `u` 锚定的 `3`-线串内部点集。 -/
noncomputable def anchoredThreeThreads {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact (anchoredDegTwo G u).filter (fun x => ¬ IsOneThreadVert G x ∧ ¬ IsTwoThreadVert G x)

lemma mem_anchoredOneThreads {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ anchoredOneThreads G u ↔ IsThreadAnchor G u x ∧ IsOneThreadVert G x := by
  classical
  simp only [anchoredOneThreads, Finset.mem_filter, mem_anchoredDegTwo]

lemma mem_anchoredTwoThreads {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ anchoredTwoThreads G u ↔ IsThreadAnchor G u x ∧ IsTwoThreadVert G x := by
  classical
  simp only [anchoredTwoThreads, Finset.mem_filter, mem_anchoredDegTwo]

lemma mem_anchoredThreeThreads {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V} :
    x ∈ anchoredThreeThreads G u ↔
      IsThreadAnchor G u x ∧ ¬ IsOneThreadVert G x ∧ ¬ IsTwoThreadVert G x := by
  classical
  simp only [anchoredThreeThreads, Finset.mem_filter, mem_anchoredDegTwo]

/-! ## 2. `anchoredDegTwo G u` 按 `1 / 2 / 3`-线串的精确三分计数 -/

/-- `3⁺`-度点 `u` 锚定的 `1`-线串点集恰好等于 `oneThreadNbrs G u`。 -/
lemma anchoredOneThreads_eq_oneThreadNbrs {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u : V} (hdu : 3 ≤ G.degree u) :
    anchoredOneThreads G u = oneThreadNbrs G u := by
  ext x
  rw [mem_anchoredOneThreads, mem_oneThreadNbrs]
  constructor
  · rintro ⟨⟨_, hdx, hux | ⟨v, hdv, _, hvx, _⟩ | ⟨_, w, _, hdw, _, _, hwx, _, _, _⟩⟩, h1⟩
    · rcases exists_other_neighbor_of_deg_two hdx hux.symm with ⟨v, hxv, hvu, _⟩
      exact ⟨hux, hdx, v, hxv, hvu, h1.2 v hxv⟩
    · have := h1.2 v hvx.symm; omega
    · have := h1.2 w hwx.symm; omega
  · rintro ⟨hux, hdx, v, hxv, hvu, hdv⟩
    refine ⟨⟨hdu, hdx, Or.inl hux⟩, hdx, fun y hxy => ?_⟩
    rcases exists_other_neighbor_of_deg_two hdx hux.symm with ⟨w, _, _, hall⟩
    rcases hall y hxy with rfl | hyw
    · exact hdu
    · have hvy : y = v := hyw.trans ((hall v hxv).resolve_left hvu).symm
      rw [hvy]; exact hdv

/-- 若 `v ∈ twoThreadNbrs G u`，则 `v` 与其 `2`-度邻点 `w` 均属于 `anchoredTwoThreads G u`，
且 `w ∉ twoThreadNbrs G u`。 -/
private lemma twoThreadNbr_mem_anchoredTwoThreads {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v : V} (hdu : 3 ≤ G.degree u)
    (hv : v ∈ twoThreadNbrs G u) :
    ∃ w : V, G.Adj v w ∧ G.degree w = 2 ∧
      v ∈ anchoredTwoThreads G u ∧ w ∈ anchoredTwoThreads G u ∧ w ∉ twoThreadNbrs G u ∧
      (∀ z, G.Adj v z → z ≠ w → 3 ≤ G.degree z) ∧
      (∀ z, G.Adj w z → z ≠ v → 3 ≤ G.degree z) := by
  rcases twoThreadNbr_other_endpoint hm hdu hv with
    ⟨w, z, huv, hdv, hvw, hwu, hdw, hwz, hzv, _, hdz, _, _, _⟩
  rcases exists_other_neighbor_of_deg_two hdv huv.symm with ⟨w', _, _, hallv⟩
  have hv3 : ∀ r, G.Adj v r → r ≠ w → 3 ≤ G.degree r := by
    intro r hvr hrw
    rcases hallv r hvr with rfl | hrw'
    · exact hdu
    · exact False.elim (hrw (hrw'.trans ((hallv w hvw).resolve_left hwu).symm))
  rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨z', _, _, hallw⟩
  have hw3 : ∀ r, G.Adj w r → r ≠ v → 3 ≤ G.degree r := by
    intro r hwr hrv
    rcases hallw r hwr with rfl | hrz'
    · exact False.elim (hrv rfl)
    · have : r = z := hrz'.trans ((hallw z hwz).resolve_left hzv).symm
      rw [this]; exact hdz
  have htv : IsTwoThreadVert G v := ⟨hdv, w, hvw, hdw, hv3, hw3⟩
  have htw : IsTwoThreadVert G w := isTwoThreadVert_symm hdv hvw hdw hv3 hw3
  have hwnot : w ∉ twoThreadNbrs G u := by
    intro hm2
    have huw : G.Adj u w := (mem_twoThreadNbrs.mp hm2).1
    exact no_two_thread_same_anchor hm hdu hdv hdw huv hvw huw.symm
  refine ⟨w, hvw, hdw, ?_, ?_, hwnot, hv3, hw3⟩
  · exact mem_anchoredTwoThreads.mpr ⟨⟨hdu, hdv, Or.inl huv⟩, htv⟩
  · exact mem_anchoredTwoThreads.mpr ⟨⟨hdu, hdw, Or.inr (Or.inl ⟨v, hdv, huv, hvw, hwu⟩)⟩, htw⟩

/-- `3⁺`-度点 `u` 锚定的 `2`-线串点集基数精确等于 `2 * |twoThreadNbrs G u|`。 -/
lemma card_anchoredTwoThreads {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : 3 ≤ G.degree u) :
    (anchoredTwoThreads G u).card = 2 * (twoThreadNbrs G u).card := by
  classical
  have hsub : twoThreadNbrs G u ⊆ anchoredTwoThreads G u := fun v hv =>
    (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv).choose_spec.2.2.1
  have hrest : (anchoredTwoThreads G u \ twoThreadNbrs G u).card = (twoThreadNbrs G u).card := by
    symm
    apply Finset.card_bij
      (fun v hv => (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv).choose)
    · intro v hv
      have hs := (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv).choose_spec
      exact Finset.mem_sdiff.mpr ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩
    · intro v₁ hv₁ v₂ hv₂ heq
      have hs1 := (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv₁).choose_spec
      have hs2 := (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv₂).choose_spec
      have hdv2 : G.degree v₂ = 2 := (mem_twoThreadNbrs.mp hv₂).2.1
      have hvw2 : G.Adj (twoThreadNbr_mem_anchoredTwoThreads hm hdu hv₁).choose v₂ := by
        rw [heq]; exact hs2.1.symm
      exact (isTwoThreadVert_partner_unique hvw2 hdv2 hs1.2.2.2.2.2.2).symm
    · intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxA2, hxnot⟩
      rcases mem_anchoredTwoThreads.mp hxA2 with
        ⟨⟨_, hdx, hpath⟩, ⟨_, y, hxy, hdy, hx3, hy3⟩⟩
      rcases hpath with hux | ⟨v, hdv, huv, hvx, hxu⟩ |
        ⟨v, w, hdv, hdw, _, hvw, hwx, _, hxv, _⟩
      · rcases exists_other_neighbor_of_deg_two hdy hxy.symm with ⟨z, hyz, hzx, _⟩
        have hyu : y ≠ u := fun h => by subst h; omega
        exact False.elim (hxnot (mem_twoThreadNbrs.mpr
          ⟨hux, hdx, y, z, hxy, hyu, hdy, hyz, hzx, hy3 z hyz hzx⟩))
      · have hvy : v = y := isTwoThreadVert_partner_unique hvx.symm hdv hx3
        subst hvy
        rcases exists_other_neighbor_of_deg_two hdx hxy with ⟨z, hxz, hzv, _⟩
        have hvm : v ∈ twoThreadNbrs G u :=
          mem_twoThreadNbrs.mpr ⟨huv, hdv, x, z, hvx, hxu, hdx, hxz, hzv, hx3 z hxz hzv⟩
        refine ⟨v, hvm, ?_⟩
        have hs := (twoThreadNbr_mem_anchoredTwoThreads hm hdu hvm).choose_spec
        exact isTwoThreadVert_partner_unique hs.1 hs.2.1 hy3
      · have hwy : w = y := isTwoThreadVert_partner_unique hwx.symm hdw hx3
        subst hwy
        have := hy3 v hvw.symm hxv; omega
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- `3⁺`-度点 `u` 锚定的 `3`-线串点集基数精确等于 `3 * |threeThreadNbrs G u|`。 -/
lemma card_anchoredThreeThreads {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : 3 ≤ G.degree u) :
    (anchoredThreeThreads G u).card = 3 * (threeThreadNbrs G u).card := by
  have h12 : Disjoint (anchoredOneThreads G u) (anchoredTwoThreads G u) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    exact isOneThreadVert_not_isTwoThreadVert
      (mem_anchoredOneThreads.mp h1).2 (mem_anchoredTwoThreads.mp h2).2
  have h12_3 :
      Disjoint (anchoredOneThreads G u ∪ anchoredTwoThreads G u) (anchoredThreeThreads G u) := by
    rw [Finset.disjoint_left]; intro x h12' h3
    have h3' := (mem_anchoredThreeThreads.mp h3).2
    rcases Finset.mem_union.mp h12' with h1 | h2
    · exact h3'.1 (mem_anchoredOneThreads.mp h1).2
    · exact h3'.2 (mem_anchoredTwoThreads.mp h2).2
  have hunion : anchoredDegTwo G u =
      (anchoredOneThreads G u ∪ anchoredTwoThreads G u) ∪ anchoredThreeThreads G u := by
    ext x
    simp only [Finset.mem_union, mem_anchoredDegTwo, mem_anchoredOneThreads,
      mem_anchoredTwoThreads, mem_anchoredThreeThreads]
    by_cases h1 : IsOneThreadVert G x <;> by_cases h2 : IsTwoThreadVert G x <;> tauto
  have htot : (anchoredDegTwo G u).card =
      (anchoredOneThreads G u).card + (anchoredTwoThreads G u).card +
        (anchoredThreeThreads G u).card := by
    rw [hunion, Finset.card_union_of_disjoint h12_3, Finset.card_union_of_disjoint h12]
  have hc1 : (anchoredOneThreads G u).card = (oneThreadNbrs G u).card := by
    rw [anchoredOneThreads_eq_oneThreadNbrs hdu]
  have hc2 : (anchoredTwoThreads G u).card = 2 * (twoThreadNbrs G u).card :=
    card_anchoredTwoThreads hm hdu
  have hcard := card_anchored_degTwo_eq hm hdu
  omega

/-- 若 `x ∈ oneThreadNbrs G u` 且 `w ≠ u` 亦为 `x` 的锚点，则 `HasOneThreadBetween G u w`。 -/
lemma oneThreadVert_other_anchor_hasOneThread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u x w : V} (hdu : 3 ≤ G.degree u)
    (hx : x ∈ oneThreadNbrs G u) (hwu : w ≠ u) (hwx : IsThreadAnchor G w x) :
    HasOneThreadBetween G u w := by
  rcases oneThreadNbr_other_endpoint hm hdu hx with ⟨v, _, _, _, h1, hanc⟩
  have hwm : w ∈ threadAnchors G x := mem_threadAnchors.mpr hwx
  rw [hanc, Finset.mem_insert, Finset.mem_singleton] at hwm
  rw [hwm.resolve_left hwu]
  exact h1

/-- 若 `x ∈ anchoredTwoThreads G u` 且 `w ≠ u` 亦为 `x` 的锚点，则 `HasTwoThreadBetween G u w`。 -/
lemma twoThreadVert_other_anchor_hasTwoThread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u x w : V} (hdu : 3 ≤ G.degree u)
    (hx : x ∈ anchoredTwoThreads G u) (hwu : w ≠ u) (hwx : IsThreadAnchor G w x) :
    HasTwoThreadBetween G u w := by
  rcases mem_anchoredTwoThreads.mp hx with ⟨⟨_, hdx, hpath⟩, ⟨_, y, hxy, hdy, hx3, hy3⟩⟩
  rcases hpath with hux | ⟨v, hdv, huv, hvx, hxu⟩ |
    ⟨v, t, hdv, hdt, _, hvt, htx, _, hxv, _⟩
  · rcases exists_other_neighbor_of_deg_two hdy hxy.symm with ⟨z, hyz, hzx, _⟩
    have hyu : y ≠ u := fun h => by subst h; omega
    have hxm : x ∈ twoThreadNbrs G u :=
      mem_twoThreadNbrs.mpr ⟨hux, hdx, y, z, hxy, hyu, hdy, hyz, hzx, hy3 z hyz hzx⟩
    rcases twoThreadNbr_other_endpoint hm hdu hxm with
      ⟨_, v', _, _, _, _, _, _, _, _, _, h2, hancx, _⟩
    have hwm : w ∈ threadAnchors G x := mem_threadAnchors.mpr hwx
    rw [hancx, Finset.mem_insert, Finset.mem_singleton] at hwm
    rw [hwm.resolve_left hwu]; exact h2
  · have hvy : v = y := isTwoThreadVert_partner_unique hvx.symm hdv hx3
    subst hvy
    rcases exists_other_neighbor_of_deg_two hdx hxy with ⟨z, hxz, hzv, _⟩
    have hvm : v ∈ twoThreadNbrs G u :=
      mem_twoThreadNbrs.mpr ⟨huv, hdv, x, z, hvx, hxu, hdx, hxz, hzv, hx3 z hxz hzv⟩
    rcases twoThreadNbr_other_endpoint hm hdu hvm with
      ⟨y', v', _, _, hvy', _, hdy', _, _, _, _, h2, _, hancy'⟩
    have hxy' : y' = x := isTwoThreadVert_partner_unique hvy' hdy' hy3
    subst hxy'
    have hwm : w ∈ threadAnchors G y' := mem_threadAnchors.mpr hwx
    rw [hancy', Finset.mem_insert, Finset.mem_singleton] at hwm
    rw [hwm.resolve_left hwu]; exact h2
  · have hty : t = y := isTwoThreadVert_partner_unique htx.symm hdt hx3
    subst hty
    have := hy3 v hvt.symm hxv; omega

/-! ## 3. 参数化 36 倍整数线串转权函数 `wThread` -/

/-- 参数化 36 倍整数线串转权函数：
- 若 `x` 为 `1`-线串点，在 `P1` 与 `¬ P1` 锚点之间按 `6 + 10 = 16` 非对称分配（同侧 `8 + 8 = 16`）；
- 若 `x` 为 `2`-线串点，在 `P2` 与 `¬ P2` 锚点之间按 `7 + 9 = 16` 非对称分配（同侧 `8 + 8 = 16`）；
- 若 `x` 为 `3`-线串点，两端锚点各送 `8`（`8 + 8 = 16`）。 -/
noncomputable def wThread {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P1 P2 : V → Prop) (u x : V) : ℤ := by
  classical
  exact if IsThreadAnchor G u x then
    if IsOneThreadVert G x then
      if P1 u then
        if (∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ P1 w) then 8 else 6
      else
        if (∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ P1 w) then 10 else 8
    else if IsTwoThreadVert G x then
      if P2 u then
        if (∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ P2 w) then 8 else 7
      else
        if (∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ P2 w) then 9 else 8
    else 8
  else 0

lemma wThread_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P1 P2 : V → Prop) (u x : V) :
    0 ≤ wThread G P1 P2 u x := by
  classical
  unfold wThread; split_ifs <;> omega

lemma wThread_eq_zero_of_not_anchor {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {P1 P2 : V → Prop} {u x : V}
    (h : ¬ IsThreadAnchor G u x) : wThread G P1 P2 u x = 0 := by
  classical
  unfold wThread; simp [h]

/-- 任意 `2`-度核心点 `x` 从两端锚点接收到的 `wThread` 总权值恒等于 `16`！ -/
lemma sum_wThread_in_deg_two {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (P1 P2 : V → Prop) {x : V} (hdx : G.degree x = 2) :
    ∑ u ∈ coreVerts G, wThread G P1 P2 u x = 16 := by
  classical
  have hsub : threadAnchors G x ⊆ coreVerts G := fun u hu =>
    mem_coreVerts.mpr (by have := (mem_threadAnchors.mp hu).1; omega)
  have hsum_eq : ∑ u ∈ coreVerts G, wThread G P1 P2 u x =
      ∑ u ∈ threadAnchors G x, wThread G P1 P2 u x := by
    symm
    apply Finset.sum_subset hsub
    intro u _ hu
    exact wThread_eq_zero_of_not_anchor (fun ha => hu (mem_threadAnchors.mpr ha))
  rw [hsum_eq]
  rcases Finset.card_eq_two.mp (card_threadAnchors_eq_two hm hdx) with ⟨u₁, u₂, hu12, hEq⟩
  rw [hEq, Finset.sum_pair hu12]
  have ha1 : IsThreadAnchor G u₁ x := mem_threadAnchors.mp (by rw [hEq]; simp)
  have ha2 : IsThreadAnchor G u₂ x := mem_threadAnchors.mp (by rw [hEq]; simp)
  have hiff1 : ∀ (P : V → Prop), (∃ w, w ≠ u₁ ∧ IsThreadAnchor G w x ∧ P w) ↔ P u₂ := by
    intro P; constructor
    · rintro ⟨w, hwu1, hwx, hPw⟩
      have hwm : w ∈ ({u₁, u₂} : Finset V) := by rw [← hEq]; exact mem_threadAnchors.mpr hwx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
      rw [← hwm.resolve_left hwu1]; exact hPw
    · intro hP; exact ⟨u₂, hu12.symm, ha2, hP⟩
  have hiff2 : ∀ (P : V → Prop), (∃ w, w ≠ u₂ ∧ IsThreadAnchor G w x ∧ P w) ↔ P u₁ := by
    intro P; constructor
    · rintro ⟨w, hwu2, hwx, hPw⟩
      have hwm : w ∈ ({u₁, u₂} : Finset V) := by rw [← hEq]; exact mem_threadAnchors.mpr hwx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
      rw [← hwm.resolve_right hwu2]; exact hPw
    · intro hP; exact ⟨u₁, hu12, ha1, hP⟩
  unfold wThread
  simp only [ha1, ha2, hiff1, hiff2, ite_true]
  by_cases h1 : IsOneThreadVert G x
  · simp only [h1, ite_true]
    by_cases hp1 : P1 u₁ <;> by_cases hp2 : P1 u₂ <;> simp [hp1, hp2]
  · simp only [h1, ite_false]
    by_cases h2 : IsTwoThreadVert G x
    · simp only [h2, ite_true]
      by_cases hp1 : P2 u₁ <;> by_cases hp2 : P2 u₂ <;> simp [hp1, hp2]
    · simp only [h2, ite_false]; omega

/-- `3⁺`-度点 `u` 通过 `wThread` 送出的总权值按 `1 / 2 / 3`-线串精确三分拆解。 -/
lemma sum_wThread_out_split {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (P1 P2 : V → Prop) {u : V} (hdu : 3 ≤ G.degree u) :
    ∑ x ∈ coreVerts G, wThread G P1 P2 u x =
      (∑ x ∈ oneThreadNbrs G u, wThread G P1 P2 u x) +
      (∑ x ∈ anchoredTwoThreads G u, wThread G P1 P2 u x) +
      (∑ x ∈ anchoredThreeThreads G u, wThread G P1 P2 u x) := by
  have hsub : anchoredDegTwo G u ⊆ coreVerts G := fun x hx =>
    mem_coreVerts.mpr (by have := (mem_anchoredDegTwo.mp hx).2.1; omega)
  have hsum_eq : ∑ x ∈ coreVerts G, wThread G P1 P2 u x =
      ∑ x ∈ anchoredDegTwo G u, wThread G P1 P2 u x := by
    symm
    apply Finset.sum_subset hsub
    intro x _ hx
    exact wThread_eq_zero_of_not_anchor (fun ha => hx (mem_anchoredDegTwo.mpr ha))
  rw [hsum_eq]
  have h12 : Disjoint (anchoredOneThreads G u) (anchoredTwoThreads G u) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    exact isOneThreadVert_not_isTwoThreadVert
      (mem_anchoredOneThreads.mp h1).2 (mem_anchoredTwoThreads.mp h2).2
  have h12_3 :
      Disjoint (anchoredOneThreads G u ∪ anchoredTwoThreads G u) (anchoredThreeThreads G u) := by
    rw [Finset.disjoint_left]; intro x h12' h3
    have h3' := (mem_anchoredThreeThreads.mp h3).2
    rcases Finset.mem_union.mp h12' with h1 | h2
    · exact h3'.1 (mem_anchoredOneThreads.mp h1).2
    · exact h3'.2 (mem_anchoredTwoThreads.mp h2).2
  have hunion : anchoredDegTwo G u =
      (anchoredOneThreads G u ∪ anchoredTwoThreads G u) ∪ anchoredThreeThreads G u := by
    ext x
    simp only [Finset.mem_union, mem_anchoredDegTwo, mem_anchoredOneThreads,
      mem_anchoredTwoThreads, mem_anchoredThreeThreads]
    by_cases h1 : IsOneThreadVert G x <;> by_cases h2 : IsTwoThreadVert G x <;> tauto
  rw [hunion, Finset.sum_union h12_3, Finset.sum_union h12,
    anchoredOneThreads_eq_oneThreadNbrs hdu]

/-- 通用上界：任意 `3⁺`-度点 `u` 通过 `wThread` 送出的总权值不超过
`10 * n₁ + 18 * n₂ + 24 * n₃`。 -/
lemma sum_wThread_out_le_general {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (P1 P2 : V → Prop) {u : V} (hdu : 3 ≤ G.degree u) :
    ∑ x ∈ coreVerts G, wThread G P1 P2 u x ≤
      10 * ((oneThreadNbrs G u).card : ℤ) +
      18 * ((twoThreadNbrs G u).card : ℤ) +
      24 * ((threeThreadNbrs G u).card : ℤ) := by
  classical
  rw [sum_wThread_out_split P1 P2 hdu]
  have h1 : ∑ x ∈ oneThreadNbrs G u, wThread G P1 P2 u x ≤
      10 * ((oneThreadNbrs G u).card : ℤ) := by
    calc ∑ x ∈ oneThreadNbrs G u, wThread G P1 P2 u x
        ≤ ∑ _x ∈ oneThreadNbrs G u, (10 : ℤ) := by
          apply Finset.sum_le_sum; intro x _
          unfold wThread; split_ifs <;> omega
      _ = 10 * ((oneThreadNbrs G u).card : ℤ) := by simp [mul_comm]
  have h2 : ∑ x ∈ anchoredTwoThreads G u, wThread G P1 P2 u x ≤
      18 * ((twoThreadNbrs G u).card : ℤ) := by
    have hc2 := card_anchoredTwoThreads hm hdu
    calc ∑ x ∈ anchoredTwoThreads G u, wThread G P1 P2 u x
        ≤ ∑ _x ∈ anchoredTwoThreads G u, (9 : ℤ) := by
          apply Finset.sum_le_sum; intro x hx
          have h2v := (mem_anchoredTwoThreads.mp hx).2
          have hnot1 : ¬ IsOneThreadVert G x := fun h1v =>
            isOneThreadVert_not_isTwoThreadVert h1v h2v
          unfold wThread; simp only [hnot1, ite_false]; split_ifs <;> omega
      _ = 9 * ((anchoredTwoThreads G u).card : ℤ) := by simp [mul_comm]
      _ = 18 * ((twoThreadNbrs G u).card : ℤ) := by rw [hc2]; push_cast; ring
  have h3 : ∑ x ∈ anchoredThreeThreads G u, wThread G P1 P2 u x ≤
      24 * ((threeThreadNbrs G u).card : ℤ) := by
    have hc3 := card_anchoredThreeThreads hm hdu
    calc ∑ x ∈ anchoredThreeThreads G u, wThread G P1 P2 u x
        ≤ ∑ _x ∈ anchoredThreeThreads G u, (8 : ℤ) := by
          apply Finset.sum_le_sum; intro x hx
          have hnot := (mem_anchoredThreeThreads.mp hx).2
          unfold wThread; simp only [hnot.1, hnot.2, ite_false]; split_ifs <;> omega
      _ = 8 * ((anchoredThreeThreads G u).card : ℤ) := by simp [mul_comm]
      _ = 24 * ((threeThreadNbrs G u).card : ℤ) := by rw [hc3]; push_cast; ring
  omega

end LeanResearch.Proposal3
