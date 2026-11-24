/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.Core3Ext
public import LeanResearch.Proposal3.Q4Ext
public import LeanResearch.Proposal3.BridgeExt
public import LeanResearch.Proposal3.T3Adjacency2
public import LeanResearch.Proposal3.ThreadPartition

/-!
# 里程碑 2：`mad(G) < 22/9` 恰当无冲突 `κ_G`-可选择性的放电法形式化证明（`Discharging22_9`）

本模块严格超越 Lu–Ying–Song（2026 年 8 月 SOTA，`mad(G) < 12/5`），在零辅助图核心子图
`K = G - X` 上整合新发现的五组可约构型引理（A–E），以整数放大 36 倍的精确放电规则完成
无 `sorry` 形式化证明：
- 若连通图 `G` 不是 `C₅` 且 `MadLt G 22 9`（即 `mad(G) < 22/9`），则 `IsPCFChoosable G (kappa G)`。
- 平面图推论：所有围长 `g ≥ 11` 的平面图均满足恰当无冲突 `κ_G`-可选择性（推进围长下界 `12 → 11`）。

## 放电规则（整数放大 36 倍）
- 初始权值：`ch(u) = 36 · d_K(u) - 88`（`u ∈ coreVerts G`）；
- 规则 R1（线串转权 `wThread G (IsPoor1Ext G) (IsT21 G)`）：
  - `1`-线串：在 `IsPoor1Ext = {L3, B3, T21, L4}` 与其补集之间按 `6 + 10 = 16` 非对称分配（同侧 `8 + 8`）；
  - `2`-线串：在 `IsT21` 与其补集之间按 `7 + 9 = 16` 非对称分配（同侧 `8 + 8`）；
  - `3`-线串：两端锚点各送 `8`（`8 + 8 = 16`）。
- 规则 R2（好点向坏点）：每个好核心顶点向每个相邻的坏核心顶点送出 `+8`；
- 规则 R3（好点向 `T3`）：每个好核心顶点向每个相邻的 `T3` 顶点送出 `+2`。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-- 内部辅助：好顶点 `u` 的 `1`-线串总转权（当 `IsPoor1Ext G u` 且所有 `1`-线串对端均不满足 `IsPoor1Ext`
时，每条 `1`-线串仅送 `6`）。 -/
private lemma sum_wThread_one_eq_six_mul {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u : V} (hdu : 3 ≤ G.degree u)
    (huP : IsPoor1Ext G u)
    (hno : ∀ w, HasOneThreadBetween G u w → ¬ IsPoor1Ext G w) :
    ∑ x ∈ oneThreadNbrs G u, wThread G (IsPoor1Ext G) (IsT21 G) u x =
      6 * ((oneThreadNbrs G u).card : ℤ) := by
  classical
  calc ∑ x ∈ oneThreadNbrs G u, wThread G (IsPoor1Ext G) (IsT21 G) u x
      = ∑ _x ∈ oneThreadNbrs G u, (6 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have h1m : x ∈ anchoredOneThreads G u := by
          rw [anchoredOneThreads_eq_oneThreadNbrs hdu]; exact hx
        rcases mem_anchoredOneThreads.mp h1m with ⟨hanc, h1v⟩
        have hnot_other : ¬ ∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ IsPoor1Ext G w := by
          rintro ⟨w, hwu, hwx, hwP⟩
          exact hno w (oneThreadVert_other_anchor_hasOneThread hm hdu hx hwu hwx) hwP
        unfold wThread
        simp only [hanc, h1v, huP, hnot_other, ite_true, ite_false]
    _ = 6 * ((oneThreadNbrs G u).card : ℤ) := by simp [mul_comm]

/-- 内部辅助：`IsT21 G u` 的 `2`-线串总转权精确等于 `14`（`2` 个内部点各送 `7`）。 -/
private lemma sum_wThread_two_eq_fourteen_of_T21 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (hu : IsT21 G u) :
    ∑ x ∈ anchoredTwoThreads G u, wThread G (IsPoor1Ext G) (IsT21 G) u x = 14 := by
  classical
  have hst := isT21_structure hm hpq hu
  have hdu3 : 3 ≤ G.degree u := by omega
  have hc2 : (anchoredTwoThreads G u).card = 2 := by
    rw [card_anchoredTwoThreads hm hdu3, hst.2.2.2.1]
  calc ∑ x ∈ anchoredTwoThreads G u, wThread G (IsPoor1Ext G) (IsT21 G) u x
      = ∑ _x ∈ anchoredTwoThreads G u, (7 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rcases mem_anchoredTwoThreads.mp hx with ⟨hanc, h2v⟩
        have hnot1 : ¬ IsOneThreadVert G x := fun h1v =>
          isOneThreadVert_not_isTwoThreadVert h1v h2v
        have hnot_other : ¬ ∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ IsT21 G w := by
          rintro ⟨w, hwu, hwx, hw21⟩
          exact no_T21_two_thread_T21 hm hpq hu hw21
            (twoThreadVert_other_anchor_hasTwoThread hm hdu3 hx hwu hwx)
        unfold wThread
        simp only [hanc, hnot1, h2v, hu, hnot_other, ite_true, ite_false]
    _ = 7 * ((anchoredTwoThreads G u).card : ℤ) := by simp [mul_comm]
    _ = 14 := by rw [hc2]; norm_num

/-- 内部辅助：`IsL3 G u` 的 `1`-线串总转权至多为 `20`（至多一条连 `L3` 送 `8`，其余均送 `6`）。 -/
private lemma sum_wThread_one_le_twenty_of_L3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 2 * p ≤ 5 * q) {u : V} (hu : IsL3 G u) :
    ∑ x ∈ oneThreadNbrs G u, wThread G (IsPoor1Ext G) (IsT21 G) u x ≤ 20 := by
  classical
  have hdu3 : 3 ≤ G.degree u := by have := hu.1; omega
  have huP : IsPoor1Ext G u := Or.inl hu
  let P1set : Finset V := (oneThreadNbrs G u).filter
    (fun x => ∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ IsPoor1Ext G w)
  have hP1_le : P1set.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a₁ ha1 a₂ ha2
    by_contra hne
    rcases Finset.mem_filter.mp ha1 with ⟨ha1_1, w₁, hw1u, hw1a1, hw1P⟩
    rcases Finset.mem_filter.mp ha2 with ⟨ha2_1, w₂, hw2u, hw2a2, hw2P⟩
    have hL_of_P : ∀ x w, x ∈ oneThreadNbrs G u → w ≠ u → IsThreadAnchor G w x →
        IsPoor1Ext G w → G.Adj x w ∧ IsL3 G w := by
      intro x w hx hwu hwx hwP
      rcases oneThreadNbr_other_endpoint hm hdu3 hx with ⟨v, hxv, hvu, _, h1, hanc⟩
      have hwm : w ∈ ({u, v} : Finset V) := by rw [← hanc]; exact mem_threadAnchors.mpr hwx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
      have hwv : w = v := hwm.resolve_left hwu
      subst hwv
      refine ⟨hxv, ?_⟩
      rcases hwP with hwL3 | hwB3 | hwT21 | hwL4
      · exact hwL3
      · exact False.elim (no_B3_one_thread_Poor1Ext hm hpq hwB3 huP (hasOneThreadBetween_symm h1))
      · exact False.elim (no_T21_one_thread_Poor1Ext hm hpq hwT21 huP (hasOneThreadBetween_symm h1))
      · exact False.elim (no_L4_one_thread_Poor1Ext hm hpq hwL4 huP (hasOneThreadBetween_symm h1))
    rcases hL_of_P a₁ w₁ ha1_1 hw1u hw1a1 hw1P with ⟨ha1w1, hw1L3⟩
    rcases hL_of_P a₂ w₂ ha2_1 hw2u hw2a2 hw2P with ⟨ha2w2, hw2L3⟩
    exact L3_at_most_one_L3_nbr hm hpq hu ha1_1 ha2_1 hne ha1w1 hw1u ha2w2 hw2u hw1L3 hw2L3
  have hsub : P1set ⊆ oneThreadNbrs G u := Finset.filter_subset _ _
  have hsplit : ∑ x ∈ oneThreadNbrs G u, wThread G (IsPoor1Ext G) (IsT21 G) u x =
      (∑ x ∈ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x) +
      (∑ x ∈ oneThreadNbrs G u \ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
  rw [hsplit]
  have hS1 : ∑ x ∈ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x = 8 * (P1set.card : ℤ) := by
    calc ∑ x ∈ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x
        = ∑ _x ∈ P1set, (8 : ℤ) := by
          apply Finset.sum_congr rfl; intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hx1, hother⟩
          have h1m : x ∈ anchoredOneThreads G u := by
            rw [anchoredOneThreads_eq_oneThreadNbrs hdu3]; exact hx1
          rcases mem_anchoredOneThreads.mp h1m with ⟨hanc, h1v⟩
          unfold wThread; simp only [hanc, h1v, huP, hother, ite_true]
      _ = 8 * (P1set.card : ℤ) := by simp [mul_comm]
  have hS2 : ∑ x ∈ oneThreadNbrs G u \ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x =
      6 * ((oneThreadNbrs G u \ P1set).card : ℤ) := by
    calc ∑ x ∈ oneThreadNbrs G u \ P1set, wThread G (IsPoor1Ext G) (IsT21 G) u x
        = ∑ _x ∈ oneThreadNbrs G u \ P1set, (6 : ℤ) := by
          apply Finset.sum_congr rfl; intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hx1, hxnot⟩
          have hnot_other : ¬ ∃ w, w ≠ u ∧ IsThreadAnchor G w x ∧ IsPoor1Ext G w := fun h =>
            hxnot (Finset.mem_filter.mpr ⟨hx1, h⟩)
          have h1m : x ∈ anchoredOneThreads G u := by
            rw [anchoredOneThreads_eq_oneThreadNbrs hdu3]; exact hx1
          rcases mem_anchoredOneThreads.mp h1m with ⟨hanc, h1v⟩
          unfold wThread; simp only [hanc, h1v, huP, hnot_other, ite_true, ite_false]
      _ = 6 * ((oneThreadNbrs G u \ P1set).card : ℤ) := by simp [mul_comm]
  have hcard_add := Finset.card_sdiff_add_card_eq_card hsub
  have hn1 : (oneThreadNbrs G u).card = 3 := hu.2
  rw [hS1, hS2]; omega

/-- 里程碑 2 核心反证定理：不存在满足 `MadLt G 22 9` 的极小反例！ -/
lemma no_minimal_counterexample_22_9 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample 22 9 G L) : False := by
  classical
  have hpq25 : 2 * 22 ≤ 5 * 9 := by omega
  have hpq22 : 9 * 22 ≤ 22 * 9 := by omega
  let K : Finset V := coreVerts G
  have hK_ne : K.Nonempty := coreVerts_nonempty hm
  let ch : V → ℤ := fun u => 36 * (coreDeg G u : ℤ) - 88
  let t : V → V → ℤ := fun u v =>
    wThread G (IsPoor1Ext G) (IsT21 G) u v +
    (if IsGood G u ∧ IsBad G v ∧ G.Adj u v then 8 else 0) +
    (if IsGood G u ∧ IsT3 G v ∧ G.Adj u v then 2 else 0)
  let ch' : V → ℤ := fun u => ch u - ∑ v ∈ K, t u v + ∑ v ∈ K, t v u
  -- 1. 密度严格上界：`∑ ch(u) < 0`
  have hsum_neg : ∑ u ∈ K, ch u < 0 := by
    have hlt : 9 * ∑ u ∈ K, coreDeg G u < 22 * K.card := mad_core_sum_lt hm.mad hK_ne
    have hltZ : (9 : ℤ) * (∑ u ∈ K, (coreDeg G u : ℤ)) < 22 * (K.card : ℤ) := by
      exact_mod_cast hlt
    have hch : ∑ u ∈ K, ch u = 36 * (∑ u ∈ K, (coreDeg G u : ℤ)) - 88 * (K.card : ℤ) := by
      simp only [ch, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    omega
  -- 2. 放电守恒：`∑ ch'(u) = ∑ ch(u)`
  have hsum_eq : ∑ u ∈ K, ch' u = ∑ u ∈ K, ch u := by
    have h1 : ∑ u ∈ K, ch' u =
        ∑ u ∈ K, ch u - ∑ u ∈ K, ∑ v ∈ K, t u v + ∑ u ∈ K, ∑ v ∈ K, t v u := by
      simp only [ch', Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [h1, Finset.sum_comm (s := K) (t := K) (f := fun u v => t v u)]
    ring
  -- 3. 拆分送出与接收权值
  have ht_nonneg : ∀ u v, 0 ≤ t u v := fun u v => by
    dsimp only [t]
    have h1 := wThread_nonneg G (IsPoor1Ext G) (IsT21 G) u v
    split_ifs <;> omega
  have hout_eq : ∀ u : V, ∑ v ∈ K, t u v =
      (∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v) +
      (if IsGood G u then
        8 * ((badNbrs G u).card : ℤ) + 2 * (((goodNbrs G u).filter (IsT3 G)).card : ℤ)
      else 0) := by
    intro u
    simp only [t, Finset.sum_add_distrib]
    rw [add_assoc]; congr 1
    by_cases hg : IsGood G u
    · simp only [hg, true_and, ite_true]
      have hb_eq : ∑ v ∈ K, (if IsBad G v ∧ G.Adj u v then (8 : ℤ) else 0) =
          8 * ((badNbrs G u).card : ℤ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hEq : K.filter (fun v => IsBad G v ∧ G.Adj u v) = badNbrs G u := by
          ext v; simp only [K, Finset.mem_filter, mem_coreVerts, mem_badNbrs]
          exact ⟨fun ⟨_, hbv, huv⟩ => ⟨huv, hbv⟩,
            fun ⟨huv, hbv⟩ => ⟨by have := hbv.1; omega, hbv, huv⟩⟩
        rw [hEq]; ring
      have ht3_eq : ∑ v ∈ K, (if IsT3 G v ∧ G.Adj u v then (2 : ℤ) else 0) =
          2 * (((goodNbrs G u).filter (IsT3 G)).card : ℤ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hEq : K.filter (fun v => IsT3 G v ∧ G.Adj u v) = (goodNbrs G u).filter (IsT3 G) := by
          ext v; simp only [K, Finset.mem_filter, mem_coreVerts, mem_goodNbrs]
          constructor
          · rintro ⟨_, hv3, huv⟩
            exact ⟨⟨huv, by unfold IsGood; have := hv3.1; omega⟩, hv3⟩
          · rintro ⟨⟨huv, hgv⟩, hv3⟩
            exact ⟨by have := coreDeg_le_degree G v; unfold IsGood at hgv; omega, hv3, huv⟩
        rw [hEq]; ring
      rw [hb_eq, ht3_eq]
    · simp [hg]
  have hin_ge_wThread : ∀ u : V,
      ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) v u ≤ ∑ v ∈ K, t v u := fun u => by
    apply Finset.sum_le_sum; intro v _
    dsimp only [t]; split_ifs <;> omega
  have hin_ge_bad : ∀ u : V, IsBad G u → 16 ≤ ∑ v ∈ K, t v u := by
    intro u hbad
    have hgood_eq : K.filter (fun v => IsGood G v ∧ G.Adj v u) = coreNbrs G u := by
      ext v; simp only [K, Finset.mem_filter, mem_coreVerts, mem_coreNbrs]
      constructor
      · rintro ⟨hdv, _, hvu⟩; exact ⟨hvu.symm, hdv⟩
      · rintro ⟨huv, hdv⟩
        have hv3 := bad_coreNbrs_deg_ge_three hm hpq25 hbad (mem_coreNbrs.mpr ⟨huv, hdv⟩)
        rcases good_or_bad_of_deg_ge_three hm hpq25 hv3 with hgv | hbv
        · exact ⟨hdv, hgv, huv.symm⟩
        · exact False.elim (no_adjacent_bad hm hpq25 hbad hbv huv)
    have hsub : ∑ v ∈ K, (if IsGood G v ∧ IsBad G u ∧ G.Adj v u then (8 : ℤ) else 0) ≤
        ∑ v ∈ K, t v u := by
      apply Finset.sum_le_sum; intro v _
      dsimp only [t]
      have h1 := wThread_nonneg G (IsPoor1Ext G) (IsT21 G) v u
      split_ifs <;> omega
    have hval : ∑ v ∈ K, (if IsGood G v ∧ IsBad G u ∧ G.Adj v u then (8 : ℤ) else 0) = 16 := by
      have hEq : (fun v => if IsGood G v ∧ IsBad G u ∧ G.Adj v u then (8 : ℤ) else 0) =
          (fun v => if IsGood G v ∧ G.Adj v u then (8 : ℤ) else 0) := by
        ext v; simp [hbad]
      have hbc2 : (coreNbrs G u).card = 2 := hbad.2
      rw [hEq, ← Finset.sum_filter, hgood_eq, Finset.sum_const, nsmul_eq_mul, hbc2]
      norm_num
    omega
  have hin_ge_T3 : ∀ u : V, IsT3 G u → 4 ≤ ∑ v ∈ K, t v u := by
    intro u huT3
    have hgood_eq : K.filter (fun v => IsGood G v ∧ G.Adj v u) = goodNbrs G u := by
      ext v; simp only [K, Finset.mem_filter, mem_coreVerts, mem_goodNbrs]
      exact ⟨fun ⟨_, hgv, hvu⟩ => ⟨hvu.symm, hgv⟩,
        fun ⟨huv, hgv⟩ => ⟨by have := coreDeg_le_degree G v; unfold IsGood at hgv; omega,
          hgv, huv.symm⟩⟩
    have hsub : ∑ v ∈ K, (if IsGood G v ∧ IsT3 G u ∧ G.Adj v u then (2 : ℤ) else 0) ≤
        ∑ v ∈ K, t v u := by
      apply Finset.sum_le_sum; intro v _
      dsimp only [t]
      have h1 := wThread_nonneg G (IsPoor1Ext G) (IsT21 G) v u
      split_ifs <;> omega
    have hval : ∑ v ∈ K, (if IsGood G v ∧ IsT3 G u ∧ G.Adj v u then (2 : ℤ) else 0) = 4 := by
      have hEq : (fun v => if IsGood G v ∧ IsT3 G u ∧ G.Adj v u then (2 : ℤ) else 0) =
          (fun v => if IsGood G v ∧ G.Adj v u then (2 : ℤ) else 0) := by
        ext v; simp [huT3]
      have hg2 : (goodNbrs G u).card = 2 := (isT3_structure hm hpq25 huT3).2.2.2.2.2
      rw [hEq, ← Finset.sum_filter, hgood_eq, Finset.sum_const, nsmul_eq_mul, hg2]
      norm_num
    omega
  -- 4. 逐类核验 `∀ u ∈ K, 0 ≤ ch' u`
  have hnonneg : ∀ u ∈ K, 0 ≤ ch' u := by
    intro u huK
    have hdu2 : 2 ≤ G.degree u := mem_coreVerts.mp huK
    have hin0 : 0 ≤ ∑ v ∈ K, t v u := Finset.sum_nonneg (fun v _ => ht_nonneg v u)
    dsimp only [ch', ch]
    rw [hout_eq u]
    by_cases hd2 : G.degree u = 2
    · -- 情形 1：`2`-度核心点：`ch = -16`，送出 `0`，接收 `16`
      have hc2 : coreDeg G u = 2 := by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hd2]
      have hng : ¬ IsGood G u := by unfold IsGood; omega
      have hout0 : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v = 0 := by
        apply Finset.sum_eq_zero; intro v _
        exact wThread_eq_zero_of_not_anchor (fun h => by have := h.1; omega)
      have hin16 : 16 ≤ ∑ v ∈ K, t v u := by
        have h16 : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) v u = 16 :=
          sum_wThread_in_deg_two hm (IsPoor1Ext G) (IsT21 G) hd2
        have := hin_ge_wThread u; omega
      simp only [hc2, hng, hout0, ite_false]; omega
    · have hdu3 : 3 ≤ G.degree u := by omega
      have hw_gen : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v ≤
          10 * ((oneThreadNbrs G u).card : ℤ) +
          18 * ((twoThreadNbrs G u).card : ℤ) +
          24 * ((threeThreadNbrs G u).card : ℤ) :=
        sum_wThread_out_le_general hm (IsPoor1Ext G) (IsT21 G) hdu3
      rcases good_or_bad_of_deg_ge_three hm hpq25 hdu3 with hgood | hbad
      · -- 情形 3：好核心顶点（`3 ≤ coreDeg G u`）
        simp only [hgood, ite_true]
        have hfive := coreDeg_eq_five_parts hm hpq25 u
        have ht3g_le : ((goodNbrs G u).filter (IsT3 G)).card ≤ (goodNbrs G u).card :=
          Finset.card_filter_le _ _
        have hlong_eq : (longThreadNbrs G u).card =
            (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
          rw [longThreadNbrs_eq_two_union_three hm u,
              Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
        by_cases hc5 : 5 ≤ coreDeg G u
        · -- 情形 3a：`q ≥ 5`
          have hll := leaf_plus_long_thread_le hm hpq25 hdu3
          have hadd := coreDeg_add_leafNbrs hm u
          omega
        · by_cases hc4 : coreDeg G u = 4
          · -- 情形 3b：`q = 4`（由引理 A `q4_three_thread_good_bound` 一次性关闭全部 8 个阻塞配置！）
            have hll := leaf_plus_long_thread_le hm hpq25 hdu3
            have hadd := coreDeg_add_leafNbrs hm u
            by_cases hblock : 1 ≤ (threeThreadNbrs G u).card ∧
                (twoThreadNbrs G u).card + (threeThreadNbrs G u).card = 2
            · have hg_ge := q4_three_thread_good_bound hm hpq22 hc4 hblock.1 hblock.2
              omega
            · omega
          · -- 情形 3c：`q = 3`
            have hc3 : coreDeg G u = 3 := by unfold IsGood at hgood; omega
            have hlong1 : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card ≤ 1 := by
              have := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq25 hc3; omega
            by_cases ht3 : (threeThreadNbrs G u).Nonempty
            · -- 3c-i：`IsT3 G u`（送 `24`、无 `T3` 邻点、收 `4`）
              have huT3 : IsT3 G u := ⟨hc3, ht3⟩
              have hst := isT3_structure hm hpq25 huT3
              have ht3g0 : ((goodNbrs G u).filter (IsT3 G)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro v hv hvT3
                exact no_T3_adj_T3 hm hpq22 huT3 hvT3 (mem_goodNbrs.mp hv).1
              have hin4 := hin_ge_T3 u huT3
              omega
            · rw [Finset.not_nonempty_iff_eq_empty] at ht3
              have ht3c : (threeThreadNbrs G u).card = 0 := by rw [ht3, Finset.card_empty]
              by_cases ht2 : (twoThreadNbrs G u).Nonempty
              · by_cases h1ne : (oneThreadNbrs G u).Nonempty
                · -- 3c-ii(a)：`IsT21 G u`（送 `6 + 14 = 20`，无 `T3` 邻点）
                  have huT21 : IsT21 G u := ⟨hc3, ht2, h1ne⟩
                  have hst := isT21_structure hm hpq25 huT21
                  have ht3g0 : ((goodNbrs G u).filter (IsT3 G)).card = 0 := by
                    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                    intro v hv hvT3
                    exact no_T3_adj_T21 hm hpq22 hvT3 huT21 (mem_goodNbrs.mp hv).1.symm
                  have hw_eq : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v = 20 := by
                    dsimp only [K]
                    rw [sum_wThread_out_split (IsPoor1Ext G) (IsT21 G) hdu3]
                    have h1 := sum_wThread_one_eq_six_mul hm hdu3 (Or.inr (Or.inr (Or.inl huT21)))
                      (fun w h1w hwP => no_T21_one_thread_Poor1Ext hm hpq25 huT21 hwP h1w)
                    have h2 := sum_wThread_two_eq_fourteen_of_T21 hm hpq25 huT21
                    have h3e : anchoredThreeThreads G u = ∅ := by
                      rw [← Finset.card_eq_zero, card_anchoredThreeThreads hm hdu3, ht3c]
                    rw [h1, h2, h3e, Finset.sum_empty, hst.2.2.2.2.1]; norm_num
                  omega
                · -- 3c-ii(b)：`IsT20 G u`（送 `≤ 18` 给 `2`-线串，至多 `1` 个 `T3` 邻点送 `≤ 2`）
                  rw [Finset.not_nonempty_iff_eq_empty] at h1ne
                  have huT20 : IsT20 G u := ⟨hc3, ht2, h1ne⟩
                  have hst := isT20_structure hm hpq25 huT20
                  have ht3g1 : ((goodNbrs G u).filter (IsT3 G)).card ≤ 1 := by
                    rw [Finset.card_le_one]
                    intro v₁ hv1 v₂ hv2
                    by_contra hne
                    rcases Finset.mem_filter.mp hv1 with ⟨hg1, hT1⟩
                    rcases Finset.mem_filter.mp hv2 with ⟨hg2, hT2⟩
                    exact no_T3_T20_T3 hm hpq22 huT20 hT1 hT2
                      (mem_goodNbrs.mp hg1).1 (mem_goodNbrs.mp hg2).1 hne
                  omega
              · -- 3c-iii：`n₂ = n₃ = 0`
                rw [Finset.not_nonempty_iff_eq_empty] at ht2
                have ht2c : (twoThreadNbrs G u).card = 0 := by rw [ht2, Finset.card_empty]
                have h2e : anchoredTwoThreads G u = ∅ := by
                  rw [← Finset.card_eq_zero, card_anchoredTwoThreads hm hdu3, ht2c]
                have h3e : anchoredThreeThreads G u = ∅ := by
                  rw [← Finset.card_eq_zero, card_anchoredThreeThreads hm hdu3, ht3c]
                by_cases hg0 : goodNbrs G u = ∅
                · have hgc : (goodNbrs G u).card = 0 := by rw [hg0, Finset.card_empty]
                  by_cases hdu4 : 4 ≤ G.degree u
                  · -- `IsL4 G u`（由引理 B 唯一存活，每条 `1`-线串仅送 `6`，总计 `18 ≤ 20`）
                    rcases no_leafy_coreDeg3_all_a_b_except_L4 hm hpq25 hc3 hdu4 ht2 ht3 hg0 with
                      ⟨hd4, hn1, hb0⟩
                    have huL4 : IsL4 G u := ⟨hd4, hc3, hn1⟩
                    have hw_eq : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v = 18 := by
                      dsimp only [K]
                      rw [sum_wThread_out_split (IsPoor1Ext G) (IsT21 G) hdu3, h2e, h3e,
                        Finset.sum_empty, add_zero, add_zero]
                      rw [sum_wThread_one_eq_six_mul hm hdu3 (Or.inr (Or.inr (Or.inr huL4)))
                        (fun w h1w hwP => no_L4_one_thread_Poor1Ext hm hpq25 huL4 hwP h1w), hn1]
                      norm_num
                    omega
                  · -- `G.degree u = 3, g = 0`（由引理 B 知 `b ≤ 1`，仅剩 `B3` 与 `L3`！）
                    have hdu_eq3 : G.degree u = 3 := by omega
                    have hble1 := deg_three_no_good_at_most_one_bad hm hpq25 hdu_eq3 hg0
                    by_cases hb1 : (badNbrs G u).card = 1
                    · -- `IsB3 G u`（两条 `1`-线串各送 `6`，坏邻点送 `8`，总计 `20`）
                      have hn1 : (oneThreadNbrs G u).card = 2 := by omega
                      have huB3 : IsB3 G u := ⟨hdu_eq3, hn1, hb1⟩
                      have hw_eq : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v = 12 := by
                        dsimp only [K]
                        rw [sum_wThread_out_split (IsPoor1Ext G) (IsT21 G) hdu3, h2e, h3e,
                          Finset.sum_empty, add_zero, add_zero]
                        rw [sum_wThread_one_eq_six_mul hm hdu3 (Or.inr (Or.inl huB3))
                          (fun w h1w hwP => no_B3_one_thread_Poor1Ext hm hpq25 huB3 hwP h1w), hn1]
                        norm_num
                      omega
                    · -- `IsL3 G u`（至多一条连 `L3` 送 `8`，其余送 `6`，总计 `≤ 20`）
                      have hb0 : (badNbrs G u).card = 0 := by omega
                      have hn1 : (oneThreadNbrs G u).card = 3 := by omega
                      have huL3 : IsL3 G u := ⟨hdu_eq3, hn1⟩
                      have hw_le : ∑ v ∈ K, wThread G (IsPoor1Ext G) (IsT21 G) u v ≤ 20 := by
                        dsimp only [K]
                        rw [sum_wThread_out_split (IsPoor1Ext G) (IsT21 G) hdu3, h2e, h3e,
                          Finset.sum_empty, add_zero, add_zero]
                        exact sum_wThread_one_le_twenty_of_L3 hm hpq25 huL3
                      omega
                · -- `1 ≤ g`
                  have hg_pos : 1 ≤ (goodNbrs G u).card :=
                    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hg0)
                  by_cases hg1 : (goodNbrs G u).card = 1
                  · by_cases hn1_2 : (oneThreadNbrs G u).card = 2
                    · -- `g = 1, n₁ = 2, b = 0`：由引理 E3，唯一好邻点非 `T3`！
                      have ht3g0 : ((goodNbrs G u).filter (IsT3 G)).card = 0 := by
                        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                        intro v hv hvT3
                        exact no_T3_adj_S3_2_a2 hm hpq22 hvT3 hc3 hn1_2
                          (mem_goodNbrs.mp hv).1.symm
                      omega
                    · omega
                  · omega
      · -- 情形 2：坏核心顶点 `IsBad G u`：`ch = -16`，送出 `0`，接收 `16`
        have hc2 : coreDeg G u = 2 := hbad.2
        have hng : ¬ IsGood G u := by unfold IsGood; omega
        have h1c : (oneThreadNbrs G u).card = 0 := by
          rw [bad_no_one_thread hm hbad, Finset.card_empty]
        have hlc : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card = 0 := by
          have : (longThreadNbrs G u).card = 0 := by
            rw [bad_no_long_thread hm hpq25 hbad, Finset.card_empty]
          rw [longThreadNbrs_eq_two_union_three hm u,
              Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)] at this
          exact this
        have hin16 := hin_ge_bad u hbad
        simp only [hc2, hng, ite_false]
        omega
  -- 5. 导出矛盾：`0 ≤ ∑ ch'(u) = ∑ ch(u) < 0`
  have hsum_nonneg : 0 ≤ ∑ u ∈ K, ch' u := Finset.sum_nonneg hnonneg
  omega

/-- 里程碑 2 主定理：`mad(G) < 22/9` 且非 `C₅` 的连通图是恰当无冲突 `κ_G`-可选择的。
严格超越 Lu–Ying–Song（2026 年 8 月）的 `mad(G) < 12/5` 纪录！ -/
theorem pcf_kappa_choosable_mad_22_9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hneC5 : ¬ IsC5 G) (hmad : MadLt G 22 9) :
    IsPCFChoosable G (kappa G) :=
  isPCFChoosable_of_no_minimal_counterexample 22 9
    (fun _ _ _ => no_minimal_counterexample_22_9) G hconn hneC5 hmad

/-- 与 `Proposals.lean` 原陈述格式逐字对齐的显式版本（直接展开 `IsC5` 定义）。 -/
theorem proposal3_pcf_kappa_choosable_22_9
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hneC5 : ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2))
    (hmad : MadLt G 22 9) :
    IsPCFChoosable G (kappa G) :=
  pcf_kappa_choosable_mad_22_9 G hconn hneC5 hmad

end LeanResearch.Proposal3
