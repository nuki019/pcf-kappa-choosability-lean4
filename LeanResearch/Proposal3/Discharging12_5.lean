/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.BadAndThreads2

/-!
# 里程碑 1：`mad(G) < 12/5` 恰当无冲突 `κ_G`-可选择性的放电法形式化证明（`Discharging12_5`）

本模块基于「零辅助图核心子图 `K = G - X`」范式，直接在原图核心顶点集 `coreVerts G` 上执行
整数化放电论证，完整形式化 Lu–Ying–Song（2026 年 8 月 SOTA）定理：
- 若连通图 `G` 不是 `C₅` 且 `MadLt G 12 5`（即 `mad(G) < 12/5`），则 `IsPCFChoosable G (kappa G)`。

## 放电规则（整数放大 5 倍）
- 初始权值：`ch(u) = 5 · d_K(u) - 12`（`u ∈ coreVerts G`）；
- 规则 R1：每个 `3⁺`-度点 `u` 向它锚定的每个 `2`-度点 `v`（即 `IsThreadAnchor G u v`）送出 `+1`；
- 规则 R2：每个好核心顶点 `u` 向每个相邻的坏核心顶点 `v` 送出 `+1`。

随后逐类核验 `ch'(u) ≥ 0`，与核心子图密度上界 `5 · ∑ d_K(u) < 12 · |V(K)|` 产生矛盾。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-- 好顶点的 `1`-线串、`2`-线串、`3`-线串与坏邻点两两不交，其基数之和不超过 `coreDeg G u`。 -/
lemma threads_and_bad_card_le_coreDeg {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (u : V) :
    (oneThreadNbrs G u).card + (twoThreadNbrs G u).card + (threeThreadNbrs G u).card +
      ((coreNbrs G u).filter (IsBad G)).card ≤ coreDeg G u := by
  classical
  have htwo_eq : (degTwoNbrs G u).card =
      (oneThreadNbrs G u).card + (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
    rw [degTwoNbrs_eq_one_union_long hm u,
        Finset.card_union_of_disjoint (oneThreadNbrs_disjoint_longThreadNbrs G u),
        longThreadNbrs_eq_two_union_three hm u,
        Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
    omega
  have hbad_sub : (coreNbrs G u).filter (IsBad G) ⊆ degThreePlusNbrs G u := by
    intro v hv
    simp only [Finset.mem_filter, mem_coreNbrs] at hv
    simp only [degThreePlusNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨hv.1.1, by have := hv.2.1; omega⟩
  have hbad_le : ((coreNbrs G u).filter (IsBad G)).card ≤ (degThreePlusNbrs G u).card :=
    Finset.card_le_card hbad_sub
  have hcore := coreDeg_eq_degTwo_add_degThreePlus G u
  omega

/-- 不存在满足 `MadLt G 12 5` 的极小反例。 -/
lemma no_minimal_counterexample_12_5 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample 12 5 G L) : False := by
  classical
  have hpq : 2 * 12 ≤ 5 * 5 := by omega
  let K : Finset V := coreVerts G
  have hK_ne : K.Nonempty := coreVerts_nonempty hm
  -- 初始权值 `ch(u) = 5 * coreDeg G u - 12` 与转移函数 `t(u, v)`
  let ch : V → ℤ := fun u => 5 * (coreDeg G u : ℤ) - 12
  let t : V → V → ℤ := fun u v =>
    (if IsThreadAnchor G u v then 1 else 0) +
    (if IsGood G u ∧ IsBad G v ∧ G.Adj u v then 1 else 0)
  let ch' : V → ℤ := fun u => ch u - ∑ v ∈ K, t u v + ∑ v ∈ K, t v u
  -- 1. 核心子图密度严格上界：`∑ ch(u) < 0`
  have hsum_neg : ∑ u ∈ K, ch u < 0 := by
    have hlt : 5 * ∑ u ∈ K, coreDeg G u < 12 * K.card := mad_core_sum_lt hm.mad hK_ne
    have hltZ : (5 : ℤ) * (∑ u ∈ K, (coreDeg G u : ℤ)) < 12 * (K.card : ℤ) := by
      exact_mod_cast hlt
    have hch : ∑ u ∈ K, ch u = 5 * (∑ u ∈ K, (coreDeg G u : ℤ)) - 12 * (K.card : ℤ) := by
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
  -- 3. 拆分每个顶点的送出权值与接收权值
  have hout_eq : ∀ u : V, ∑ v ∈ K, t u v =
      ((anchoredDegTwo G u).card : ℤ) +
      (if IsGood G u then (((coreNbrs G u).filter (IsBad G)).card : ℤ) else 0) := by
    intro u
    simp only [t, Finset.sum_add_distrib, Finset.sum_boole]
    congr 1
    · congr 1; congr 1
      ext v
      simp only [K, Finset.mem_filter, mem_coreVerts, mem_anchoredDegTwo]
      exact ⟨fun h => h.2, fun h => ⟨by have := h.2.1; omega, h⟩⟩
    · by_cases hg : IsGood G u
      · simp only [hg, true_and, ite_true]
        congr 1; congr 1
        ext v
        simp only [K, Finset.mem_filter, mem_coreVerts, mem_coreNbrs]
        exact ⟨fun ⟨hdv, hbv, huv⟩ => ⟨⟨huv, hdv⟩, hbv⟩,
          fun ⟨⟨huv, hdv⟩, hbv⟩ => ⟨hdv, hbv, huv⟩⟩
      · simp only [hg, false_and, ite_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
  have hin_eq : ∀ u : V, ∑ v ∈ K, t v u =
      ((threadAnchors G u).card : ℤ) +
      ((K.filter (fun v => IsGood G v ∧ IsBad G u ∧ G.Adj v u)).card : ℤ) := by
    intro u
    simp only [t, Finset.sum_add_distrib, Finset.sum_boole]
    congr 1; congr 1; congr 1
    ext v
    simp only [K, Finset.mem_filter, mem_coreVerts, mem_threadAnchors]
    exact ⟨fun h => h.2, fun h => ⟨by have := h.1; omega, h⟩⟩
  -- 4. 逐类核验 `∀ u ∈ K, 0 ≤ ch' u`
  have hnonneg : ∀ u ∈ K, 0 ≤ ch' u := by
    intro u huK
    have hdu2 : 2 ≤ G.degree u := mem_coreVerts.mp huK
    dsimp only [ch', ch]
    rw [hout_eq u, hin_eq u]
    by_cases hd2 : G.degree u = 2
    · -- 情形 1：`2`-度核心点：不送出，接收 2 个锚点各 +1
      have hc2 : coreDeg G u = 2 := by rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hd2]
      have hng : ¬ IsGood G u := by unfold IsGood; omega
      have hanc0 : (anchoredDegTwo G u).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv; rw [mem_anchoredDegTwo] at hv; have := hv.1; omega
      have hin2 : (threadAnchors G u).card = 2 := card_threadAnchors_eq_two hm hd2
      simp only [hng, ite_false, hc2, hanc0, hin2]
      omega
    · have hdu3 : 3 ≤ G.degree u := by omega
      have hanc_eq := card_anchored_degTwo_eq hm hdu3
      rcases good_or_bad_of_deg_ge_three hm hpq hdu3 with hgood | hbad
      · -- 情形 3/4：好顶点 `3 ≤ coreDeg G u`
        simp only [hgood, ite_true]
        have hsum_le := threads_and_bad_card_le_coreDeg hm u
        have hlong_eq : (longThreadNbrs G u).card =
            (twoThreadNbrs G u).card + (threeThreadNbrs G u).card := by
          rw [longThreadNbrs_eq_two_union_three hm u,
              Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)]
        by_cases hc4 : 4 ≤ coreDeg G u
        · -- 情形 3：`coreDeg G u ≥ 4`
          have hll := leaf_plus_long_thread_le hm hpq hdu3
          have hadd := coreDeg_add_leafNbrs hm u
          have hlong_le : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card ≤
              coreDeg G u - 2 := by omega
          omega
        · -- 情形 4：`coreDeg G u = 3`
          have hc3 : coreDeg G u = 3 := by unfold IsGood at hgood; omega
          have hlong1 : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card ≤ 1 := by
            have := longThreadNbrs_card_le_one_of_coreDeg_three hm hpq hc3; omega
          have hsum3 := good_coreDeg_three_long_thread_summary hm hpq hc3
          by_cases ht3 : (threeThreadNbrs G u).Nonempty
          · rcases hsum3.1 ht3 with ⟨h1e, hnobad⟩
            have h1c : (oneThreadNbrs G u).card = 0 := by rw [h1e, Finset.card_empty]
            have hbc : ((coreNbrs G u).filter (IsBad G)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              exact fun b hb => hnobad b hb
            have ht3_pos : 1 ≤ (threeThreadNbrs G u).card := ht3.card_pos
            omega
          · rw [Finset.not_nonempty_iff_eq_empty] at ht3
            have ht3c : (threeThreadNbrs G u).card = 0 := by rw [ht3, Finset.card_empty]
            by_cases ht2 : (twoThreadNbrs G u).Nonempty
            · rcases hsum3.2 ht2 with ⟨h1le, hnobad⟩
              have hbc : ((coreNbrs G u).filter (IsBad G)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                exact fun b hb => hnobad b hb
              omega
            · rw [Finset.not_nonempty_iff_eq_empty] at ht2
              have ht2c : (twoThreadNbrs G u).card = 0 := by rw [ht2, Finset.card_empty]
              omega
      · -- 情形 2：坏顶点 `IsBad G u`：不关联任何线串、不送出，恰接收 2 个好核心邻点各 +1
        have hc2 : coreDeg G u = 2 := hbad.2
        have hng : ¬ IsGood G u := by unfold IsGood; omega
        have h1e : oneThreadNbrs G u = ∅ := bad_no_one_thread hm hbad
        have hle : longThreadNbrs G u = ∅ := bad_no_long_thread hm hpq hbad
        have h1c : (oneThreadNbrs G u).card = 0 := by rw [h1e, Finset.card_empty]
        have hlc : (twoThreadNbrs G u).card + (threeThreadNbrs G u).card = 0 := by
          have : (longThreadNbrs G u).card = 0 := by rw [hle, Finset.card_empty]
          rw [longThreadNbrs_eq_two_union_three hm u,
              Finset.card_union_of_disjoint (twoThreadNbrs_disjoint_threeThreadNbrs G u)] at this
          exact this
        have hgood_nbrs :
            K.filter (fun v => IsGood G v ∧ IsBad G u ∧ G.Adj v u) = coreNbrs G u := by
          ext v
          simp only [K, Finset.mem_filter, mem_coreVerts, mem_coreNbrs]
          constructor
          · rintro ⟨hdv, _, _, hvu⟩; exact ⟨hvu.symm, hdv⟩
          · rintro ⟨huv, hdv⟩
            have hv3 := bad_coreNbrs_deg_ge_three hm hpq hbad (mem_coreNbrs.mpr ⟨huv, hdv⟩)
            rcases good_or_bad_of_deg_ge_three hm hpq hv3 with hgv | hbv
            · exact ⟨hdv, hgv, hbad, huv.symm⟩
            · exact False.elim (no_adjacent_bad hm hpq hbad hbv huv)
        have hgin2 : (K.filter (fun v => IsGood G v ∧ IsBad G u ∧ G.Adj v u)).card = 2 := by
          rw [hgood_nbrs]; exact hc2
        simp only [hng, ite_false]
        omega
  -- 5. 导出矛盾：`0 ≤ ∑ ch'(u) = ∑ ch(u) < 0`
  have hsum_nonneg : 0 ≤ ∑ u ∈ K, ch' u := Finset.sum_nonneg hnonneg
  omega

/-- 里程碑 1 主定理：`mad(G) < 12/5` 且非 `C₅` 的连通图是恰当无冲突 `κ_G`-可选择的。 -/
theorem pcf_kappa_choosable_mad_12_5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hneC5 : ¬ IsC5 G) (hmad : MadLt G 12 5) :
    IsPCFChoosable G (kappa G) :=
  isPCFChoosable_of_no_minimal_counterexample 12 5
    (fun _ _ _ => no_minimal_counterexample_12_5) G hconn hneC5 hmad

end LeanResearch.Proposal3
