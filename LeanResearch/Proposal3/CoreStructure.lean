/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.Admissible

/-!
# 极小反例的基础结构引理（`CoreStructure`）

本模块对任意阈值 `(p, q)` 的极小反例 `MinimalCounterexample p q G L`（不依赖具体 `mad` 数值！）
建立以下零 `sorry` 结构引理：
1. `card_ge_four`：`|V(G)| ≥ 4`（排除 `K_1, K_2, K_3, P_3`）；
2. `leaf_neighbor_deg_ge_four`（Lemma 3.1）：每个 `1`-度点的唯一邻点度数 `≥ 4`；
3. `no_four_path_of_deg_two`（Lemma 3.3(ii) + 排除 `C_n (n ≥ 6)`）：不存在 4 个连续的 `2`-度点；
4. `exists_deg_ge_three`：极小反例必含至少一个 `3⁺`-度点（排除一切圈 `C_n`）；
5. `no_three_vertex_two_thread`（Lemma 3.3(i)）：`3`-度点不关联 `2⁺`-线串；
6. `no_two_thread_same_anchor` / `no_three_thread_same_anchor`（Lemma 3.3(iii)）：
   任何 `2`-度点所在的线串长度 `∈ {1, 2, 3}` 且两端点必为两个**不同**的 `3⁺`-度点。
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 度数与邻点计数辅助引理 -/

/-- `1`-度点恰有一个邻点。 -/
lemma exists_unique_neighbor_of_deg_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} (hd : G.degree v = 1) :
    ∃ u : V, G.Adj v u ∧ ∀ z, G.Adj v z → z = u := by
  classical
  have hc : (G.neighborFinset v).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd]
  rcases Finset.card_eq_one.mp hc with ⟨u, hu⟩
  have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp (by rw [hu]; simp)
  refine ⟨u, hadj, ?_⟩
  intro z hz
  have : z ∈ ({u} : Finset V) := by rw [← hu]; exact (G.mem_neighborFinset v z).mpr hz
  simpa using this

/-- 若 `1`-度点 `x` 与 `u` 相邻，则 `u` 是 `x` 的唯一邻点且 `x` 自动满足 PCF 条件。 -/
lemma pcf_at_deg_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {φ : V → ℕ} {x u : V}
    (hd : G.degree x = 1) (hxu : G.Adj x u) :
    ∃ y, G.Adj x y ∧ ∀ z, G.Adj x z → φ z = φ y → z = y := by
  rcases exists_unique_neighbor_of_deg_one hd with ⟨u₀, _, huniq⟩
  have hu : u = u₀ := huniq u hxu
  exact ⟨u, hxu, fun z hz _ => (huniq z hz).trans hu.symm⟩

/-- `2`-度点 `v` 已知一个邻点 `u` 时，存在唯一的另一个邻点 `w ≠ u`。 -/
lemma exists_other_neighbor_of_deg_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v u : V}
    (hd : G.degree v = 2) (hvu : G.Adj v u) :
    ∃ w : V, G.Adj v w ∧ w ≠ u ∧ ∀ z, G.Adj v z → z = u ∨ z = w := by
  rcases exists_two_neighbors_of_deg_two hd with ⟨a, b, hva, hvb, hab, hall⟩
  rcases hall u hvu with rfl | rfl
  · exact ⟨b, hvb, hab.symm, hall⟩
  · exact ⟨a, hva, hab, fun z hz => (hall z hz).symm⟩

/-- `3`-度点至少有两个不在 `{x}` 中的不同邻点。 -/
lemma exists_two_other_neighbors_of_deg_three {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u x : V}
    (hd : G.degree u = 3) :
    ∃ w₁ w₂ : V, w₁ ≠ x ∧ w₂ ≠ x ∧ w₁ ≠ w₂ ∧ G.Adj u w₁ ∧ G.Adj u w₂ := by
  classical
  have hc : 2 ≤ (G.neighborFinset u \ {x}).card := by
    have h1 := card_sdiff_ge (G.neighborFinset u) {x}
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd] at h1
    simp only [Finset.card_singleton] at h1
    omega
  rcases exists_two_of_card_ge_two hc with ⟨w₁, hw₁, w₂, hw₂, hne⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
  exact ⟨w₁, w₂, hw₁.2, hw₂.2, hne, hw₁.1, hw₂.1⟩

/-- 若 `3`-度点 `u` 有两个邻点 `w₁, w₂` 在 `ψ` 下异色，则无论第三个邻点染何色，`u` 必有唯一色！ -/
lemma pcf_at_deg_three_of_two_distinct {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ψ : V → ℕ} {u w₁ w₂ : V}
    (hd : G.degree u = 3) (h1 : G.Adj u w₁) (h2 : G.Adj u w₂) (hne : w₁ ≠ w₂)
    (hcol : ψ w₁ ≠ ψ w₂) :
    ∃ y, G.Adj u y ∧ ∀ z, G.Adj u z → ψ z = ψ y → z = y := by
  classical
  have hc : (G.neighborFinset u \ {w₁, w₂}).card = 1 := by
    have hsub : ({w₁, w₂} : Finset V) ⊆ G.neighborFinset u := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (G.mem_neighborFinset u x).mpr h1
      · exact (G.mem_neighborFinset u x).mpr h2
    rw [Finset.card_sdiff_of_subset hsub, SimpleGraph.card_neighborFinset_eq_degree, hd,
        Finset.card_pair hne]
  rcases Finset.card_eq_one.mp hc with ⟨w₃, hw₃⟩
  have hw₃_mem : w₃ ∈ G.neighborFinset u \ {w₁, w₂} := by rw [hw₃]; simp
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hw₃_mem
  have hall : ∀ z, G.Adj u z → z = w₁ ∨ z = w₂ ∨ z = w₃ := by
    intro z hz
    by_cases h12 : z ∈ ({w₁, w₂} : Finset V)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h12
      rcases h12 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · have : z ∈ G.neighborFinset u \ {w₁, w₂} :=
        Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset u z).mpr hz, h12⟩
      rw [hw₃, Finset.mem_singleton] at this
      exact Or.inr (Or.inr this)
  by_cases h31 : ψ w₃ = ψ w₁
  · -- `ψ w₂` 不同于 `ψ w₁` 与 `ψ w₃`，故 `w₂` 唯一！
    refine ⟨w₂, h2, ?_⟩
    intro z hz hψz
    rcases hall z hz with rfl | rfl | rfl
    · exact False.elim (hcol hψz)
    · rfl
    · exact False.elim (hcol (h31.symm.trans hψz))
  · -- `ψ w₁` 不同于 `ψ w₂` 与 `ψ w₃`，故 `w₁` 唯一！
    refine ⟨w₁, h1, ?_⟩
    intro z hz hψz
    rcases hall z hz with rfl | rfl | rfl
    · rfl
    · exact False.elim (hcol hψz.symm)
    · exact False.elim (h31 hψz)

/-- 若连通图有至少 2 个顶点，则每个顶点度数 `≥ 1`。 -/
lemma degree_pos_of_connected {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ G.degree v := by
  classical
  have hex : ∃ w : V, w ≠ v := by
    have : ({v} : Finset V).card < (Finset.univ : Finset V).card := by
      rw [Finset.card_singleton, Finset.card_univ]; omega
    rcases exists_mem_sdiff_of_lt this with ⟨w, _, hw⟩
    rw [Finset.mem_singleton] at hw
    exact ⟨w, hw⟩
  rcases hex with ⟨w, hne⟩
  rcases hconn v w with ⟨p⟩
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons _ u _ hvu _ =>
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨u, (G.mem_neighborFinset v u).mpr hvu⟩

/-! ## 2. 小图排除与 Lemma 3.1（`1`-度点必连 `4⁺`-度点） -/

/-- 极小反例至少有 3 个顶点（`K_1` 和 `K_2` 均平凡可染）。 -/
lemma card_ge_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) :
    3 ≤ Fintype.card V := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hm.conn.nonempty
  by_cases h1 : Fintype.card V = 1
  · rcases Fintype.card_eq_one_iff.mp h1 with ⟨v₀, hv₀⟩
    have hLpos : 0 < (L v₀).card := by
      rw [hm.list_card v₀]; simp only [kappa]; split_ifs <;> omega
    rcases Finset.card_pos.mp hLpos with ⟨c, hc⟩
    apply hm.not_colorable
    refine ⟨fun _ => c, ⟨?_, ?_⟩, fun v => by rw [hv₀ v]; exact hc⟩
    · intro u v huv; exact False.elim (G.ne_of_adj huv ((hv₀ u).trans (hv₀ v).symm))
    · intro v ⟨u, huv⟩; exact False.elim (G.ne_of_adj huv ((hv₀ v).trans (hv₀ u).symm))
  · have h2 : (Finset.univ : Finset V).card = 2 := by rw [Finset.card_univ]; omega
    rcases Finset.card_eq_two.mp h2 with ⟨a, b, hab, hall_set⟩
    have hall : ∀ v : V, v = a ∨ v = b := fun v => by
      have : v ∈ ({a, b} : Finset V) := by rw [← hall_set]; exact Finset.mem_univ v
      simpa using this
    have hda : 1 ≤ G.degree a := degree_pos_of_connected hm.conn (by omega) a
    have hdb : 1 ≤ G.degree b := degree_pos_of_connected hm.conn (by omega) b
    have hLa : 2 ≤ (L a).card := by
      rw [hm.list_card a]; simp only [kappa]; split_ifs <;> omega
    have hLb : 2 ≤ (L b).card := by
      rw [hm.list_card b]; simp only [kappa]; split_ifs <;> omega
    rcases Finset.card_pos.mp (by omega : 0 < (L a).card) with ⟨ca, hca⟩
    rcases exists_mem_sdiff_of_lt (A := L b) (B := {ca}) (by simp; omega) with ⟨cb, hcb, hcbn⟩
    rw [Finset.mem_singleton] at hcbn
    let φ : V → ℕ := fun v => if v = a then ca else cb
    apply hm.not_colorable
    refine ⟨φ, isPCFColoring_of_injective ?_, ?_⟩
    · intro x y hxy
      rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
      · rfl
      · simp only [φ, ite_true, ite_false, hab.symm] at hxy; exact False.elim (hcbn hxy.symm)
      · simp only [φ, ite_true, ite_false, hab.symm] at hxy; exact False.elim (hcbn hxy)
      · rfl
    · intro v
      rcases hall v with rfl | rfl
      · simp [φ, hca]
      · simp [φ, hab.symm, hcb]

/-- 极小反例中每个顶点度数 `≥ 1`。 -/
lemma degree_ge_one {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (v : V) :
    1 ≤ G.degree v :=
  degree_pos_of_connected hm.conn (by have := card_ge_three hm; omega) v

/-- Lemma 3.1：极小反例中每个 `1`-度点的唯一邻点度数必 `≥ 4`。 -/
lemma leaf_neighbor_deg_ge_four {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {x u : V}
    (hdx : G.degree x = 1) (hxu : G.Adj x u) :
    4 ≤ G.degree u := by
  by_contra hlt
  push Not at hlt
  have hdu_ge1 : 1 ≤ G.degree u := degree_ge_one hm u
  have hxu_ne : x ≠ u := G.ne_of_adj hxu
  have hLx : (L x).card = 2 := by rw [hm.list_card x]; simp [kappa, hdx]
  rcases exists_unique_neighbor_of_deg_one hdx with ⟨u₀, _, hx_uniq⟩
  have hx_only : ∀ z, G.Adj x z → z = u := fun z hz => (hx_uniq z hz).trans (hx_uniq u hxu).symm
  have hdu_cases : G.degree u = 1 ∨ G.degree u = 2 ∨ G.degree u = 3 := by omega
  rcases hdu_cases with hdu | hdu | hdu
  · -- `d(u) = 1`：则 `{x, u}` 封闭，与 `|V| ≥ 3` 矛盾
    rcases exists_unique_neighbor_of_deg_one hdu with ⟨x₀, _, hu_uniq⟩
    have hu_only : ∀ z, G.Adj u z → z = x :=
      fun z hz => (hu_uniq z hz).trans (hu_uniq x hxu.symm).symm
    have hall : ({x, u} : Finset V) = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := x) (by simp)
      intro a ha b hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      rcases ha with rfl | rfl
      · exact Or.inr (hx_only b hab)
      · exact Or.inl (hu_only b hab)
    have hle : ({x, u} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [hall, Finset.card_univ] at hle
    have := card_ge_three hm
    omega
  · -- `d(u) = 2`：删 `S = {x, u}`，设 `w ≠ x` 为 `u` 的另一邻点
    rcases exists_other_neighbor_of_deg_two hdu hxu.symm with ⟨w, huw, hwx, hu_all⟩
    have huw_ne : u ≠ w := G.ne_of_adj huw
    have hLu : (L u).card = 4 := by rw [hm.list_card u]; simp [kappa, hdu]
    let S : Finset V := {x, u}
    rcases exists_admissible_coloring hm (S := S) ⟨x, by simp [S]⟩ with ⟨adm⟩
    have hwS : w ∉ S := by simp [S, hwx, huw_ne.symm]
    rcases exists_mem_sdiff_of_lt (A := L x) (B := {adm.φ w}) (by simp [hLx]) with ⟨cx, hcx, hcxw⟩
    rw [Finset.mem_singleton] at hcxw
    rcases exists_mem_sdiff_of_lt (A := L u) (B := {cx, adm.φ w, adm.φs w})
      (by have := card_triple_le cx (adm.φ w) (adm.φs w); omega) with ⟨cu, hcu, hcun⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcun
    let ψ : V → ℕ := fun v => if v = x then cx else if v = u then cu else adm.φ v
    have hψx : ψ x = cx := by simp [ψ]
    have hψu : ψ u = cu := by simp [ψ, hxu_ne.symm]
    have hψw : ψ w = adm.φ w := by simp [ψ, hwx, huw_ne.symm]
    apply adm.contradiction hm ψ
    · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      simp [ψ, hz.1, hz.2]
    · intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · rw [hψx]; exact hcx
      · rw [hψu]; exact hcu
    · intro a b hab hor
      have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
        intro x y hxy hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · have hy : y = u := hx_only y hxy
          rw [hy, hψx, hψu]; exact Ne.symm hcun.1
        · rcases hu_all y hxy with hy | hy
          · rw [hy, hψu, hψx]; exact hcun.1
          · rw [hy, hψu, hψw]; exact hcun.2.1
      rcases hor with ha | hb
      · exact hcase a b hab ha
      · exact (hcase b a hab.symm hb).symm
    · intro v hvS _ y hyS hvy
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
      rcases hyS with rfl | rfl
      · exact False.elim (hvS (by rw [hx_only v hvy.symm]; simp [S]))
      · rcases hu_all v hvy.symm with rfl | rfl
        · exact False.elim (hvS (by simp [S]))
        · rw [hψu]; exact hcun.2.2
    · intro v hvS hiso ⟨y, hvy⟩
      have hyS : y ∈ S := by by_contra h; exact hiso y h hvy
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
      rcases hyS with hy | hy
      · exact False.elim (hvS (by rw [hx_only v (hy ▸ hvy).symm]; simp [S]))
      · refine ⟨u, hy ▸ hvy, ?_⟩
        intro z hvz _
        have hzS : z ∈ S := by by_contra h; exact hiso z h hvz
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
        rcases hzS with hz | hz
        · exact False.elim (hvS (by rw [hx_only v (hz ▸ hvz).symm]; simp [S]))
        · exact hz
    · intro v hvS _
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hvS
      rcases hvS with rfl | rfl
      · exact pcf_at_deg_one hdx hxu
      · exact pcf_at_of_two_distinct_neighbors hdu hxu.symm huw hwx.symm
          (by rw [hψx, hψw]; exact hcxw)
  · -- `d(u) = 3`：删 `S = {x}`，并用 `avoid := fun _ => L x`（大小 2 ≤ 3）避开 `L x`！
    let S : Finset V := {x}
    rcases exists_admissible_coloring_avoid hm (S := S) ⟨x, by simp [S]⟩
      (fun _ => L x) (fun _ => by omega) with ⟨adm, hadm_two⟩
    rcases exists_two_other_neighbors_of_deg_three (x := x) hdu with
      ⟨w₁, w₂, hw₁x, hw₂x, hw₁₂, huw₁, huw₂⟩
    have huS : u ∉ S := by simp [S, hxu_ne.symm]
    have hw₁S : w₁ ∉ S := by simp [S, hw₁x]
    have hw₂S : w₂ ∉ S := by simp [S, hw₂x]
    rcases exists_mem_sdiff_of_lt (A := L x) (B := {adm.φ u}) (by simp [hLx]) with ⟨cx, hcx, hcxu⟩
    rw [Finset.mem_singleton] at hcxu
    let ψ : V → ℕ := fun v => if v = x then cx else adm.φ v
    have hψx : ψ x = cx := by simp [ψ]
    have hψ_out : ∀ v, v ≠ x → ψ v = adm.φ v := fun v hv => by simp [ψ, hv]
    rcases hadm_two u huS ⟨w₁, w₂, hw₁S, hw₂S, hw₁₂, huw₁, huw₂⟩ with
      ⟨a₁, a₂, ha₁S, ha₂S, hua₁, hua₂, hcol12⟩ | hnotLx
    · -- `u` 在 `G - {x}` 中已有两个异色邻点 `a₁, a₂`，直接满足 PCF！
      apply hm.not_colorable
      refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
      · intro a b hab
        by_cases ha : a = x
        · subst a; have hb : b = u := hx_only b hab
          rw [hb, hψx, hψ_out u hxu_ne.symm]; exact hcxu
        · by_cases hb : b = x
          · subst b; have ha' : a = u := hx_only a hab.symm
            rw [ha', hψ_out u hxu_ne.symm, hψx]; exact Ne.symm hcxu
          · rw [hψ_out a ha, hψ_out b hb]
            exact adm.proper a b (by simp [S, ha]) (by simp [S, hb]) hab
      · intro v hv
        by_cases hvx : v = x
        · subst hvx; exact pcf_at_deg_one hdx hxu
        · by_cases hvu : v = u
          · subst hvu
            have ha₁x : a₁ ≠ x := by simpa [S] using ha₁S
            have ha₂x : a₂ ≠ x := by simpa [S] using ha₂S
            have ha₁₂ : a₁ ≠ a₂ := fun heq => hcol12 (heq ▸ rfl)
            exact pcf_at_deg_three_of_two_distinct hdu hua₁ hua₂ ha₁₂
              (by rw [hψ_out a₁ ha₁x, hψ_out a₂ ha₂x]; exact hcol12)
          · -- `v ∉ {x, u}`：`v` 不与 `x` 相邻，故 `v` 在 `G - {x}` 中非孤立且无需避色！
            have hnvx : ¬ G.Adj v x := fun hadj => hvu (hx_only v hadj.symm)
            rcases hv with ⟨z, hvz⟩
            have hzx : z ≠ x := fun h => hnvx (h ▸ hvz)
            exact adm.pcf_preserve ψ (fun a ha => hψ_out a (by simpa [S] using ha))
              v (by simp [S, hvx]) ⟨z, by simp [S, hzx], hvz⟩
              (fun y hyS hvy => by
                simp only [S, Finset.mem_singleton] at hyS
                subst hyS; exact False.elim (hnvx hvy))
      · intro v
        by_cases hvx : v = x
        · subst hvx; rw [hψx]; exact hcx
        · rw [hψ_out v hvx]; exact adm.mem_list v (by simp [S, hvx])
    · -- `adm.φs u ∉ L x`，故 `cx ∈ L x` 自动满足 `cx ≠ adm.φs u`！
      apply adm.contradiction hm ψ
      · intro v hv; exact hψ_out v (by simpa [S] using hv)
      · intro v hv; simp only [S, Finset.mem_singleton] at hv; subst hv; rw [hψx]; exact hcx
      · intro a b hab hor
        have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
          intro x y hxy hx; simp only [S, Finset.mem_singleton] at hx; subst hx
          have hy : y = u := hx_only y hxy
          rw [hy, hψx, hψ_out u hxu_ne.symm]; exact hcxu
        rcases hor with ha | hb
        · exact hcase a b hab ha
        · exact (hcase b a hab.symm hb).symm
      · intro v hvS _ y hyS hvy
        simp only [S, Finset.mem_singleton] at hyS; subst hyS
        have hvu : v = u := hx_only v hvy.symm; subst hvu
        rw [hψx]; exact fun heq => hnotLx (heq ▸ hcx)
      · intro v hvS hiso ⟨y, hvy⟩
        have hyS : y ∈ S := by by_contra h; exact hiso y h hvy
        simp only [S, Finset.mem_singleton] at hyS; subst hyS
        have hvu : v = u := hx_only v hvy.symm; subst hvu
        exact False.elim (hiso w₁ hw₁S huw₁)
      · intro v hvS _
        simp only [S, Finset.mem_singleton] at hvS; subst hvS
        exact pcf_at_deg_one hdx hxu

/-- 由 Lemma 3.1 立即得极小反例至少有 5 个顶点（因为若存在 1-度点则其邻点度数 ≥ 4，即至少 5 点；
若无 1-度点则最小度 ≥ 2，而 `C_3, K_4` 等均在 4 点以下，下面先给出更直接的 `4 ≤ card V`）。 -/
lemma card_ge_four {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) :
    4 ≤ Fintype.card V := by
  by_contra hlt
  push Not at hlt
  have h3 : Fintype.card V = 3 := by have := card_ge_three hm; omega
  -- 任意 3 阶简单图每个顶点度数 ≤ 2，由 `leaf_neighbor_deg_ge_four` 无 1-度点，故必全为 2-度点（`K_3`）！
  have hdeg2 : ∀ v : V, G.degree v = 2 := by
    intro v
    have hle : G.degree v ≤ 2 := by
      have := G.degree_lt_card_verts v
      omega
    have hge1 := degree_ge_one hm v
    by_contra hne2
    have hd1 : G.degree v = 1 := by omega
    rcases exists_unique_neighbor_of_deg_one hd1 with ⟨u, hvu, _⟩
    have hdu4 := leaf_neighbor_deg_ge_four hm hd1 hvu
    have := G.degree_lt_card_verts u
    omega
  -- `K_3` 每个列表大小 = 4，任选 3 个互异颜色即得单射 PCF 染色！
  have h3u : (Finset.univ : Finset V).card = 3 := by rw [Finset.card_univ, h3]
  rcases Finset.card_eq_three.mp h3u with ⟨a, b, c, hab, hac, hbc, hall_set⟩
  have hall : ∀ v : V, v = a ∨ v = b ∨ v = c := fun v => by
    have : v ∈ ({a, b, c} : Finset V) := by rw [← hall_set]; exact Finset.mem_univ v
    simpa using this
  have hLa : (L a).card = 4 := by rw [hm.list_card a]; simp [kappa, hdeg2 a]
  have hLb : (L b).card = 4 := by rw [hm.list_card b]; simp [kappa, hdeg2 b]
  have hLc : (L c).card = 4 := by rw [hm.list_card c]; simp [kappa, hdeg2 c]
  rcases Finset.card_pos.mp (by omega : 0 < (L a).card) with ⟨ca, hca⟩
  rcases exists_mem_sdiff_of_lt (A := L b) (B := {ca}) (by simp [hLb]) with ⟨cb, hcb, hcbn⟩
  rcases exists_mem_sdiff_of_lt (A := L c) (B := {ca, cb})
    (by have := Finset.card_le_two (a := ca) (b := cb); omega) with ⟨cc, hcc, hccn⟩
  rw [Finset.mem_singleton] at hcbn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hccn
  let φ : V → ℕ := fun v => if v = a then ca else if v = b then cb else cc
  apply hm.not_colorable
  refine ⟨φ, isPCFColoring_of_injective ?_, ?_⟩
  · intro x y hxy
    rcases hall x with rfl | rfl | rfl <;> rcases hall y with rfl | rfl | rfl <;>
    simp only [φ, ite_true, ite_false, hab, hab.symm, hac.symm, hbc.symm] at hxy
    all_goals first | rfl | exact False.elim (by omega)
  · intro v
    rcases hall v with rfl | rfl | rfl
    · simp [φ, hca]
    · simp [φ, hab.symm, hcb]
    · simp [φ, hac.symm, hbc.symm, hcc]

/-! ## 3. 四点延拓引理（同时排除 `4⁺`-线串与 `C_n (n ≥ 6)`！） -/

/-- `C_4`（4 阶 2-正则图）不能是极小反例。 -/
lemma not_c4 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L)
    (hcard4 : Fintype.card V = 4) (hdeg2 : ∀ v : V, G.degree v = 2) : False := by
  have hL4 : ∀ v : V, (L v).card = 4 := fun v => by rw [hm.list_card v]; simp [kappa, hdeg2 v]
  -- 取出 4 个互异顶点，依次选 4 个互异颜色即得单射 PCF 染色！
  have hex4 : ∃ v₁ v₂ v₃ v₄ : V,
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ ∧
      ∀ v : V, v = v₁ ∨ v = v₂ ∨ v = v₃ ∨ v = v₄ := by
    rcases hm.conn.nonempty with ⟨v₁⟩
    rcases exists_four_of_card_eq_four (A := Finset.univ) (by rw [Finset.card_univ, hcard4]) v₁ with
      ⟨v₂, v₃, v₄, _, _, _, h12, h13, h14, h23, h24, h34⟩
    have hall : ({v₁, v₂, v₃, v₄} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard4, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h34]
      · simp [h23, h24]
      · simp [h12, h13, h14]
    refine ⟨v₁, v₂, v₃, v₄, h12, h13, h14, h23, h24, h34, fun v => ?_⟩
    have : v ∈ ({v₁, v₂, v₃, v₄} : Finset V) := by rw [hall]; exact Finset.mem_univ v
    simpa using this
  rcases hex4 with ⟨v₁, v₂, v₃, v₄, h12, h13, h14, h23, h24, h34, hall⟩
  rcases Finset.card_pos.mp (by rw [hL4 v₁]; omega) with ⟨c₁, hc₁⟩
  rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {c₁}) (by simp [hL4 v₂]) with ⟨c₂, hc₂, hc₂n⟩
  rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {c₁, c₂})
    (by have := Finset.card_le_two (a := c₁) (b := c₂); rw [hL4 v₃]; omega) with ⟨c₃, hc₃, hc₃n⟩
  rcases exists_mem_sdiff_of_lt (A := L v₄) (B := {c₁, c₂, c₃})
    (by have := card_triple_le c₁ c₂ c₃; rw [hL4 v₄]; omega) with ⟨c₄, hc₄, hc₄n⟩
  rw [Finset.mem_singleton] at hc₂n
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₃n hc₄n
  let φ : V → ℕ := fun v =>
    if v = v₁ then c₁ else if v = v₂ then c₂ else if v = v₃ then c₃ else c₄
  apply hm.not_colorable
  refine ⟨φ, isPCFColoring_of_injective ?_, ?_⟩
  · intro x y hxy
    rcases hall x with rfl | rfl | rfl | rfl <;> rcases hall y with rfl | rfl | rfl | rfl <;>
    simp only [φ, ite_true, ite_false, h12, h13, h23,
      h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm] at hxy
    all_goals first | rfl | exact False.elim (by omega)
  · intro v
    rcases hall v with rfl | rfl | rfl | rfl
    · simp [φ, hc₁]
    · simp [φ, h12.symm, hc₂]
    · simp [φ, h13.symm, h23.symm, hc₃]
    · simp [φ, h14.symm, h24.symm, h34.symm, hc₄]

/-- Lemma 3.3(ii)（四点延拓引理）：极小反例中不存在由 4 个互异 `2`-度点构成的路 `v₁-v₂-v₃-v₄`！
（此引理同时排除一切 `4⁺`-线串与一切阶数 `≥ 6` 的圈！） -/
lemma no_four_path_of_deg_two {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {v₁ v₂ v₃ v₄ : V}
    (hd1 : G.degree v₁ = 2) (hd2 : G.degree v₂ = 2)
    (hd3 : G.degree v₃ = 2) (hd4 : G.degree v₄ = 2)
    (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄)
    (h13 : v₁ ≠ v₃) (h14 : v₁ ≠ v₄) (h24 : v₂ ≠ v₄) : False := by
  have h12n : v₁ ≠ v₂ := G.ne_of_adj h12
  have h23n : v₂ ≠ v₃ := G.ne_of_adj h23
  have h34n : v₃ ≠ v₄ := G.ne_of_adj h34
  rcases exists_other_neighbor_of_deg_two hd1 h12 with ⟨u, h1u, hu2, hN1⟩
  rcases exists_other_neighbor_of_deg_two hd4 h34.symm with ⟨w, h4w, hw3, hN4⟩
  have hN2 := neighborFinset_eq_pair_of_deg_two hd2 h12.symm h23 h13
  have hN3 := neighborFinset_eq_pair_of_deg_two hd3 h23.symm h34 h24
  have h2_all : ∀ z, G.Adj v₂ z → z = v₁ ∨ z = v₃ := by
    intro z hz; have : z ∈ ({v₁, v₃} : Finset V) := by
      rw [← hN2]; exact (G.mem_neighborFinset v₂ z).mpr hz
    simpa using this
  have h3_all : ∀ z, G.Adj v₃ z → z = v₂ ∨ z = v₄ := by
    intro z hz; have : z ∈ ({v₂, v₄} : Finset V) := by
      rw [← hN3]; exact (G.mem_neighborFinset v₃ z).mpr hz
    simpa using this
  have hu1 : u ≠ v₁ := (G.ne_of_adj h1u).symm
  have hw4 : w ≠ v₄ := (G.ne_of_adj h4w).symm
  -- `u ≠ v₃`（因 `v₃` 只有邻点 `v₂, v₄` 而 `v₁ ∉ {v₂, v₄}`）
  have hu3 : u ≠ v₃ := by
    intro h; rcases h3_all v₁ (h ▸ h1u.symm) with h' | h'
    · exact h12n h'
    · exact h14 h'
  -- `w ≠ v₂`（因 `v₂` 只有邻点 `v₁, v₃` 而 `v₄ ∉ {v₁, v₃}`）
  have hw2 : w ≠ v₂ := by
    intro h; rcases h2_all v₄ (h ▸ h4w.symm) with h' | h'
    · exact h14 h'.symm
    · exact h34n h'.symm
  -- 若 `u = v₄`，则 `{v₁, v₂, v₃, v₄}` 封闭形成 `C_4`，由 `not_c4` 矛盾！
  have hu4 : u ≠ v₄ := by
    intro h
    have h14e : G.Adj v₁ v₄ := h ▸ h1u
    have hN1' := neighborFinset_eq_pair_of_deg_two hd1 h12 h14e h24
    have hN4' := neighborFinset_eq_pair_of_deg_two hd4 h34.symm h14e.symm h13.symm
    have hall : ({v₁, v₂, v₃, v₄} : Finset V) = Finset.univ := by
      apply eq_univ_of_closed hm.conn (v₀ := v₁) (by simp)
      intro a ha b hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl
      · have : b ∈ ({v₂, v₄} : Finset V) := by
          rw [← hN1']; exact (G.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · rcases h2_all b hab with rfl | rfl <;> simp
      · rcases h3_all b hab with rfl | rfl <;> simp
      · have : b ∈ ({v₃, v₁} : Finset V) := by
          rw [← hN4']; exact (G.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
    have hcard4 : Fintype.card V = 4 := by
      rw [← Finset.card_univ, ← hall, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h34n]
      · simp [h23n, h24]
      · simp [h12n, h13, h14]
    apply not_c4 hm hcard4
    intro v
    have hv : v ∈ ({v₁, v₂, v₃, v₄} : Finset V) := by rw [hall]; exact Finset.mem_univ v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hw1 : w ≠ v₁ := by
    intro h; rcases hN1 v₄ (h ▸ h4w.symm) with h' | h'
    · exact h24 h'.symm
    · exact hu4 h'.symm
  -- 令 `S = {v₁, v₂, v₃, v₄}`，故 `u ∉ S` 且 `w ∉ S`
  let S : Finset V := {v₁, v₂, v₃, v₄}
  have huS : u ∉ S := by simp [S, hu1, hu2, hu3, hu4]
  have hwS : w ∉ S := by simp [S, hw1, hw2, hw3, hw4]
  -- 证明 `u` 与 `w` 在 `G - S` 中皆非孤立！
  have hdu_ge2 : 2 ≤ G.degree u := by
    have h1 := degree_ge_one hm u
    by_contra hlt; push Not at hlt
    have hd1u : G.degree u = 1 := by omega
    have := leaf_neighbor_deg_ge_four hm hd1u h1u.symm
    omega
  have hdw_ge2 : 2 ≤ G.degree w := by
    have h1 := degree_ge_one hm w
    by_contra hlt; push Not at hlt
    have hd1w : G.degree w = 1 := by omega
    have := leaf_neighbor_deg_ge_four hm hd1w h4w.symm
    omega
  -- `u` 与 `S` 相邻的点只能是 `v₁`（以及当 `u = w` 时的 `v₄`）
  have hS_adj_out : ∀ v, v ∉ S → ∀ y ∈ S, G.Adj v y → (y = v₁ ∧ v = u) ∨ (y = v₄ ∧ v = w) := by
    intro v hvS y hyS hvy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with rfl | rfl | rfl | rfl
    · rcases hN1 v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases h2_all v hvy.symm with rfl | rfl <;> exact False.elim (hvS (by simp [S]))
    · rcases h3_all v hvy.symm with rfl | rfl <;> exact False.elim (hvS (by simp [S]))
    · rcases hN4 v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · exact Or.inr ⟨rfl, rfl⟩
  have hnoniso_u : ∃ z, z ∉ S ∧ G.Adj u z := by
    by_cases huw : u = w
    · -- 若 `u = w`，且 `d(u) = 2`，则 `{u, v₁, v₂, v₃, v₄}` 封闭形成 `C_5`，与 `hm.neC5` 矛盾！
      have hdu3 : 3 ≤ G.degree u := by
        by_contra hlt; push Not at hlt
        have hdu2 : G.degree u = 2 := by omega
        have h4u : G.Adj v₄ u := huw ▸ h4w
        have hNu := neighborFinset_eq_pair_of_deg_two hdu2 h1u.symm h4u.symm h14
        have hall : ({u, v₁, v₂, v₃, v₄} : Finset V) = Finset.univ := by
          apply eq_univ_of_closed hm.conn (v₀ := u) (by simp)
          intro a ha b hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
          rcases ha with rfl | rfl | rfl | rfl | rfl
          · have : b ∈ ({v₁, v₄} : Finset V) := by
              rw [← hNu]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · rcases hN1 b hab with rfl | rfl <;> simp
          · rcases h2_all b hab with rfl | rfl <;> simp
          · rcases h3_all b hab with rfl | rfl <;> simp
          · rcases hN4 b hab with rfl | rfl
            · simp
            · rw [← huw]; simp
        apply hm.neC5
        refine ⟨?_, ?_⟩
        · rw [← Finset.card_univ, ← hall, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [h34n]
          · simp [h23n, h24]
          · simp [h12n, h13, h14]
          · simp [hu1, hu2, hu3, hu4]
        · intro v
          have hv : v ∈ ({u, v₁, v₂, v₃, v₄} : Finset V) := by rw [hall]; exact Finset.mem_univ v
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hlt : ({v₁, v₄} : Finset V).card < (G.neighborFinset u).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have := Finset.card_le_two (a := v₁) (b := v₄); omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_adj_out u huS z hzS hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hzn.1 rfl
      · exact hzn.2 rfl
    · have hlt : ({v₁} : Finset V).card < (G.neighborFinset u).card := by
        rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      rw [Finset.mem_singleton] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_adj_out u huS z hzS hz with ⟨rfl, _⟩ | ⟨rfl, hEq⟩
      · exact hzn rfl
      · exact huw hEq
  have hnoniso_w : ∃ z, z ∉ S ∧ G.Adj w z := by
    by_cases huw : u = w
    · rw [← huw]; exact hnoniso_u
    · have hlt : ({v₄} : Finset V).card < (G.neighborFinset w).card := by
        rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]; omega
      rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      rw [Finset.mem_singleton] at hzn
      refine ⟨z, ?_, hz⟩
      intro hzS
      rcases hS_adj_out w hwS z hzS hz with ⟨rfl, hEq⟩ | ⟨rfl, _⟩
      · exact huw hEq.symm
      · exact hzn rfl
  -- 取 `G - S` 的容许染色并完成 4-点贪心延拓！
  rcases exists_admissible_coloring hm (S := S) ⟨v₁, by simp [S]⟩ with ⟨adm⟩
  have hL1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hd1]
  have hL2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hd2]
  have hL3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hd3]
  have hL4 : (L v₄).card = 4 := by rw [hm.list_card v₄]; simp [kappa, hd4]
  let L1s := L v₁ \ {adm.φ u, adm.φs u}
  let L2s := L v₂ \ {adm.φ u}
  let L3s := L v₃ \ {adm.φ w}
  let L4s := L v₄ \ {adm.φ w, adm.φs w}
  have hL1s : 2 ≤ L1s.card := by
    dsimp only [L1s]
    have := card_sdiff_ge (L v₁) {adm.φ u, adm.φs u}
    have := Finset.card_le_two (a := adm.φ u) (b := adm.φs u); omega
  have hL2s : 3 ≤ L2s.card := by
    dsimp only [L2s]
    have := card_sdiff_ge (L v₂) {adm.φ u}; simp at this; omega
  have hL3s : 3 ≤ L3s.card := by
    dsimp only [L3s]
    have := card_sdiff_ge (L v₃) {adm.φ w}; simp at this; omega
  have hL4s : 2 ≤ L4s.card := by
    dsimp only [L4s]
    have := card_sdiff_ge (L v₄) {adm.φ w, adm.φs w}
    have := Finset.card_le_two (a := adm.φ w) (b := adm.φs w); omega
  rcases exists_two_of_card_ge_two hL1s with ⟨m₁, hm₁, m₂, hm₂, hm12⟩
  rcases exists_mem_sdiff_of_lt (A := L2s) (B := {m₁, m₂})
    (by have := Finset.card_le_two (a := m₁) (b := m₂); omega) with ⟨c₂, hc₂, hc₂m⟩
  rcases exists_mem_sdiff_of_lt (A := L4s) (B := {c₂}) (by simp; omega) with ⟨c₄, hc₄, hc₄2⟩
  rcases exists_mem_sdiff_of_lt (A := L3s) (B := {c₂, c₄})
    (by have := Finset.card_le_two (a := c₂) (b := c₄); omega) with ⟨c₃, hc₃, hc₃24⟩
  have hex_c1 : ∃ c₁ ∈ L1s, c₁ ≠ c₂ ∧ c₁ ≠ c₃ := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₂m
    by_cases h : m₁ = c₃
    · exact ⟨m₂, hm₂, Ne.symm hc₂m.2, fun h' => hm12 (h.trans h'.symm)⟩
    · exact ⟨m₁, hm₁, Ne.symm hc₂m.1, h⟩
  rcases hex_c1 with ⟨c₁, hc₁, hc12, hc13⟩
  simp only [L1s, L2s, L3s, L4s, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hc₁ hc₂ hc₃ hc₄ hc₄2 hc₃24
  let ψ : V → ℕ := fun v =>
    if v = v₁ then c₁ else if v = v₂ then c₂ else if v = v₃ then c₃
    else if v = v₄ then c₄ else adm.φ v
  have hψ1 : ψ v₁ = c₁ := by simp [ψ]
  have hψ2 : ψ v₂ = c₂ := by simp [ψ, h12n.symm]
  have hψ3 : ψ v₃ = c₃ := by simp [ψ, h13.symm, h23n.symm]
  have hψ4 : ψ v₄ = c₄ := by simp [ψ, h14.symm, h24.symm, h34n.symm]
  have hψ_out : ∀ v, v ∉ S → ψ v = adm.φ v := by
    intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    simp [ψ, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  apply adm.contradiction hm ψ hψ_out
  · intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [hψ1]; exact hc₁.1
    · rw [hψ2]; exact hc₂.1
    · rw [hψ3]; exact hc₃.1
    · rw [hψ4]; exact hc₄.1
  · intro a b hab hor
    have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
      intro x y hxy hx; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rcases hN1 y hxy with hy | hy
        · rw [hy, hψ1, hψ2]; exact hc12
        · rw [hy, hψ1, hψ_out u huS]; exact hc₁.2.1
      · rcases h2_all y hxy with hy | hy
        · rw [hy, hψ2, hψ1]; exact hc12.symm
        · rw [hy, hψ2, hψ3]; exact Ne.symm hc₃24.1
      · rcases h3_all y hxy with hy | hy
        · rw [hy, hψ3, hψ2]; exact hc₃24.1
        · rw [hy, hψ3, hψ4]; exact hc₃24.2
      · rcases hN4 y hxy with hy | hy
        · rw [hy, hψ4, hψ3]; exact Ne.symm hc₃24.2
        · rw [hy, hψ4, hψ_out w hwS]; exact hc₄.2.1
    rcases hor with ha | hb
    · exact hcase a b hab ha
    · exact (hcase b a hab.symm hb).symm
  · intro v hvS _ y hyS hvy
    rcases hS_adj_out v hvS y hyS hvy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hψ1]; exact hc₁.2.2
    · rw [hψ4]; exact hc₄.2.2
  · intro v hvS hiso ⟨y, hvy⟩
    have hyS : y ∈ S := by by_contra h; exact hiso y h hvy
    rcases hS_adj_out v hvS y hyS hvy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hnoniso_u with ⟨z, hzS, huz⟩; exact False.elim (hiso z hzS huz)
    · rcases hnoniso_w with ⟨z, hzS, hwz⟩; exact False.elim (hiso z hzS hwz)
  · intro v hvS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hvS
    rcases hvS with rfl | rfl | rfl | rfl
    · exact pcf_at_of_two_distinct_neighbors hd1 h12 h1u hu2.symm
        (by rw [hψ2, hψ_out u huS]; exact hc₂.2)
    · exact pcf_at_of_two_distinct_neighbors hd2 h12.symm h23 h13
        (by rw [hψ1, hψ3]; exact hc13)
    · exact pcf_at_of_two_distinct_neighbors hd3 h23.symm h34 h24
        (by rw [hψ2, hψ4]; exact Ne.symm hc₄2)
    · exact pcf_at_of_two_distinct_neighbors hd4 h34.symm h4w hw3.symm
        (by rw [hψ3, hψ_out w hwS]; exact hc₃.2)

/-- 极小反例不是 2-正则图（从而必含至少一个 `3⁺`-度点）。 -/
lemma exists_deg_ge_three {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) :
    ∃ v : V, 3 ≤ G.degree v := by
  by_contra hno
  push Not at hno
  -- 若所有点度数 ≤ 2，由 `leaf_neighbor_deg_ge_four` 无 1-度点，故全为 2-度点！
  have hdeg2 : ∀ v : V, G.degree v = 2 := by
    intro v
    have hge1 := degree_ge_one hm v
    have hle2 := hno v
    by_contra hne2
    have hd1 : G.degree v = 1 := by omega
    rcases exists_unique_neighbor_of_deg_one hd1 with ⟨u, hvu, _⟩
    have := leaf_neighbor_deg_ge_four hm hd1 hvu
    have := hno u
    omega
  have hge4 := card_ge_four hm
  by_cases h4 : Fintype.card V = 4
  · exact not_c4 hm h4 hdeg2
  · by_cases h5 : Fintype.card V = 5
    · exact hm.neC5 ⟨h5, hdeg2⟩
    · -- `card V ≥ 6` 且全图 2-正则连通：从任一点走 3 步即得 4 个互异 `2`-度点构成的路！
      have hge6 : 6 ≤ Fintype.card V := by omega
      rcases hm.conn.nonempty with ⟨v₁⟩
      rcases exists_two_neighbors_of_deg_two (hdeg2 v₁) with ⟨v₂, _, h12, _, _, _⟩
      rcases exists_other_neighbor_of_deg_two (hdeg2 v₂) h12.symm with ⟨v₃, h23, h31, _⟩
      rcases exists_other_neighbor_of_deg_two (hdeg2 v₃) h23.symm with ⟨v₄, h34, h42, _⟩
      have h14 : v₁ ≠ v₄ := by
        intro h
        -- 若 `v₁ = v₄`，则 `{v₁, v₂, v₃}` 为闭三角，与 `|V| ≥ 6` 矛盾
        have h13e : G.Adj v₁ v₃ := (h ▸ h34).symm
        have hN1 := neighborFinset_eq_pair_of_deg_two (hdeg2 v₁) h12 h13e (G.ne_of_adj h23)
        have hN2 := neighborFinset_eq_pair_of_deg_two (hdeg2 v₂) h12.symm h23 h31.symm
        have hN3 := neighborFinset_eq_pair_of_deg_two (hdeg2 v₃) h23.symm h13e.symm
          (G.ne_of_adj h12).symm
        have hall : ({v₁, v₂, v₃} : Finset V) = Finset.univ := by
          apply eq_univ_of_closed hm.conn (v₀ := v₁) (by simp)
          intro a ha b hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
          rcases ha with rfl | rfl | rfl
          · have : b ∈ ({v₂, v₃} : Finset V) := by
              rw [← hN1]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : b ∈ ({v₁, v₃} : Finset V) := by
              rw [← hN2]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
          · have : b ∈ ({v₂, v₁} : Finset V) := by
              rw [← hN3]; exact (G.mem_neighborFinset a b).mpr hab
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl <;> simp
        have hle := card_triple_le v₁ v₂ v₃
        rw [hall, Finset.card_univ] at hle
        omega
      exact no_four_path_of_deg_two hm (hdeg2 v₁) (hdeg2 v₂) (hdeg2 v₃) (hdeg2 v₄)
        h12 h23 h34 h31.symm h14 h42.symm

/-! ## 4. Lemma 3.3(i) 与 Lemma 3.3(iii)：`3`-度点无 `2⁺`-线串、无闭圈线串 -/

/-- Lemma 3.3(iii) 情形 1：不存在以同一 `3⁺`-度点 `u` 为两端点的 `2`-线串（即 `u-v₁-v₂-u` 三角形）。 -/
lemma no_two_thread_same_anchor {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ : V}
    (hdu : 3 ≤ G.degree u) (hd1 : G.degree v₁ = 2) (hd2 : G.degree v₂ = 2)
    (hu1 : G.Adj u v₁) (h12 : G.Adj v₁ v₂) (h2u : G.Adj v₂ u) : False := by
  have h12n : v₁ ≠ v₂ := G.ne_of_adj h12
  have hu1n : u ≠ v₁ := G.ne_of_adj hu1
  have hu2n : u ≠ v₂ := (G.ne_of_adj h2u).symm
  have hN1 := neighborFinset_eq_pair_of_deg_two hd1 hu1.symm h12 hu2n
  have hN2 := neighborFinset_eq_pair_of_deg_two hd2 h12.symm h2u hu1n.symm
  have h1_all : ∀ z, G.Adj v₁ z → z = u ∨ z = v₂ := by
    intro z hz; have : z ∈ ({u, v₂} : Finset V) := by
      rw [← hN1]; exact (G.mem_neighborFinset v₁ z).mpr hz
    simpa using this
  have h2_all : ∀ z, G.Adj v₂ z → z = v₁ ∨ z = u := by
    intro z hz; have : z ∈ ({v₁, u} : Finset V) := by
      rw [← hN2]; exact (G.mem_neighborFinset v₂ z).mpr hz
    simpa using this
  let S : Finset V := {v₁, v₂}
  have huS : u ∉ S := by simp [S, hu1n, hu2n]
  have hnoniso_u : ∃ z, z ∉ S ∧ G.Adj u z := by
    have hlt : ({v₁, v₂} : Finset V).card < (G.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := v₁) (b := v₂); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
    rw [SimpleGraph.mem_neighborFinset] at hz
    exact ⟨z, hzn, hz⟩
  rcases exists_admissible_coloring hm (S := S) ⟨v₁, by simp [S]⟩ with ⟨adm⟩
  have hL1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hd1]
  have hL2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hd2]
  rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {adm.φ u, adm.φs u})
    (by have := Finset.card_le_two (a := adm.φ u) (b := adm.φs u); omega) with ⟨c₂, hc₂, hc₂n⟩
  rcases exists_mem_sdiff_of_lt (A := L v₁) (B := {adm.φ u, adm.φs u, c₂})
    (by have := card_triple_le (adm.φ u) (adm.φs u) c₂; omega) with ⟨c₁, hc₁, hc₁n⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₂n hc₁n
  let ψ : V → ℕ := fun v => if v = v₁ then c₁ else if v = v₂ then c₂ else adm.φ v
  have hψ1 : ψ v₁ = c₁ := by simp [ψ]
  have hψ2 : ψ v₂ = c₂ := by simp [ψ, h12n.symm]
  have hψ_out : ∀ v, v ∉ S → ψ v = adm.φ v := by
    intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    simp [ψ, hv.1, hv.2]
  apply adm.contradiction hm ψ hψ_out
  · intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [hψ1]; exact hc₁
    · rw [hψ2]; exact hc₂
  · intro a b hab hor
    have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
      intro x y hxy hx; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rcases h1_all y hxy with hy | hy
        · rw [hy, hψ1, hψ_out u huS]; exact hc₁n.1
        · rw [hy, hψ1, hψ2]; exact hc₁n.2.2
      · rcases h2_all y hxy with hy | hy
        · rw [hy, hψ2, hψ1]; exact Ne.symm hc₁n.2.2
        · rw [hy, hψ2, hψ_out u huS]; exact hc₂n.1
    rcases hor with ha | hb
    · exact hcase a b hab ha
    · exact (hcase b a hab.symm hb).symm
  · intro v hvS _ y hyS hvy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with rfl | rfl
    · rcases h1_all v hvy.symm with rfl | rfl
      · rw [hψ1]; exact hc₁n.2.1
      · exact False.elim (hvS (by simp [S]))
    · rcases h2_all v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · rw [hψ2]; exact hc₂n.2
  · intro v hvS hiso ⟨y, hvy⟩
    have hyS : y ∈ S := by by_contra h; exact hiso y h hvy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with rfl | rfl
    · rcases h1_all v hvy.symm with rfl | rfl
      · rcases hnoniso_u with ⟨z, hzS, huz⟩; exact False.elim (hiso z hzS huz)
      · exact False.elim (hvS (by simp [S]))
    · rcases h2_all v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · rcases hnoniso_u with ⟨z, hzS, huz⟩; exact False.elim (hiso z hzS huz)
  · intro v hvS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hvS
    rcases hvS with rfl | rfl
    · exact pcf_at_of_two_distinct_neighbors hd1 hu1.symm h12 hu2n
        (by rw [hψ_out u huS, hψ2]; exact Ne.symm hc₂n.1)
    · exact pcf_at_of_two_distinct_neighbors hd2 h12.symm h2u hu1n.symm
        (by rw [hψ1, hψ_out u huS]; exact hc₁n.1)

/-- Lemma 3.3(iii) 情形 2：不存在以同一 `3⁺`-度点 `u` 为两端点的 `3`-线串（`u-v₁-v₂-v₃-u`）。 -/
lemma no_three_thread_same_anchor {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ v₃ : V}
    (hdu : 3 ≤ G.degree u) (hd1 : G.degree v₁ = 2) (hd2 : G.degree v₂ = 2) (hd3 : G.degree v₃ = 2)
    (hu1 : G.Adj u v₁) (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h3u : G.Adj v₃ u)
    (h13 : v₁ ≠ v₃) : False := by
  have h12n : v₁ ≠ v₂ := G.ne_of_adj h12
  have h23n : v₂ ≠ v₃ := G.ne_of_adj h23
  have hu1n : u ≠ v₁ := G.ne_of_adj hu1
  have hu3n : u ≠ v₃ := (G.ne_of_adj h3u).symm
  have hu2n : u ≠ v₂ := by
    intro h; subst h; omega
  have hN1 := neighborFinset_eq_pair_of_deg_two hd1 hu1.symm h12 hu2n
  have hN2 := neighborFinset_eq_pair_of_deg_two hd2 h12.symm h23 h13
  have hN3 := neighborFinset_eq_pair_of_deg_two hd3 h23.symm h3u hu2n.symm
  have h1_all : ∀ z, G.Adj v₁ z → z = u ∨ z = v₂ := by
    intro z hz; have : z ∈ ({u, v₂} : Finset V) := by
      rw [← hN1]; exact (G.mem_neighborFinset v₁ z).mpr hz
    simpa using this
  have h2_all : ∀ z, G.Adj v₂ z → z = v₁ ∨ z = v₃ := by
    intro z hz; have : z ∈ ({v₁, v₃} : Finset V) := by
      rw [← hN2]; exact (G.mem_neighborFinset v₂ z).mpr hz
    simpa using this
  have h3_all : ∀ z, G.Adj v₃ z → z = v₂ ∨ z = u := by
    intro z hz; have : z ∈ ({v₂, u} : Finset V) := by
      rw [← hN3]; exact (G.mem_neighborFinset v₃ z).mpr hz
    simpa using this
  let S : Finset V := {v₁, v₂, v₃}
  have huS : u ∉ S := by simp [S, hu1n, hu2n, hu3n]
  have hnoniso_u : ∃ z, z ∉ S ∧ G.Adj u z := by
    have hlt : ({v₁, v₃} : Finset V).card < (G.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have := Finset.card_le_two (a := v₁) (b := v₃); omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
    rw [SimpleGraph.mem_neighborFinset] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzn
    refine ⟨z, ?_, hz⟩
    intro hzS
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl
    · exact hzn.1 rfl
    · rcases h2_all u hz.symm with h | h
      · exact hu1n h
      · exact hu3n h
    · exact hzn.2 rfl
  rcases exists_admissible_coloring hm (S := S) ⟨v₁, by simp [S]⟩ with ⟨adm⟩
  have hL1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hd1]
  have hL2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hd2]
  have hL3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hd3]
  rcases exists_mem_sdiff_of_lt (A := L v₃) (B := {adm.φ u, adm.φs u})
    (by have := Finset.card_le_two (a := adm.φ u) (b := adm.φs u); omega) with ⟨c₃, hc₃, hc₃n⟩
  rcases exists_mem_sdiff_of_lt (A := L v₁) (B := {adm.φ u, adm.φs u, c₃})
    (by have := card_triple_le (adm.φ u) (adm.φs u) c₃; omega) with ⟨c₁, hc₁, hc₁n⟩
  rcases exists_mem_sdiff_of_lt (A := L v₂) (B := {adm.φ u, c₁, c₃})
    (by have := card_triple_le (adm.φ u) c₁ c₃; omega) with ⟨c₂, hc₂, hc₂n⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₃n hc₁n hc₂n
  let ψ : V → ℕ := fun v =>
    if v = v₁ then c₁ else if v = v₂ then c₂ else if v = v₃ then c₃ else adm.φ v
  have hψ1 : ψ v₁ = c₁ := by simp [ψ]
  have hψ2 : ψ v₂ = c₂ := by simp [ψ, h12n.symm]
  have hψ3 : ψ v₃ = c₃ := by simp [ψ, h13.symm, h23n.symm]
  have hψ_out : ∀ v, v ∉ S → ψ v = adm.φ v := by
    intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    simp [ψ, hv.1, hv.2.1, hv.2.2]
  apply adm.contradiction hm ψ hψ_out
  · intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · rw [hψ1]; exact hc₁
    · rw [hψ2]; exact hc₂
    · rw [hψ3]; exact hc₃
  · intro a b hab hor
    have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
      intro x y hxy hx; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rcases h1_all y hxy with hy | hy
        · rw [hy, hψ1, hψ_out u huS]; exact hc₁n.1
        · rw [hy, hψ1, hψ2]; exact Ne.symm hc₂n.2.1
      · rcases h2_all y hxy with hy | hy
        · rw [hy, hψ2, hψ1]; exact hc₂n.2.1
        · rw [hy, hψ2, hψ3]; exact hc₂n.2.2
      · rcases h3_all y hxy with hy | hy
        · rw [hy, hψ3, hψ2]; exact Ne.symm hc₂n.2.2
        · rw [hy, hψ3, hψ_out u huS]; exact hc₃n.1
    rcases hor with ha | hb
    · exact hcase a b hab ha
    · exact (hcase b a hab.symm hb).symm
  · intro v hvS _ y hyS hvy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with rfl | rfl | rfl
    · rcases h1_all v hvy.symm with rfl | rfl
      · rw [hψ1]; exact hc₁n.2.1
      · exact False.elim (hvS (by simp [S]))
    · rcases h2_all v hvy.symm with rfl | rfl <;> exact False.elim (hvS (by simp [S]))
    · rcases h3_all v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · rw [hψ3]; exact hc₃n.2
  · intro v hvS hiso ⟨y, hvy⟩
    have hyS : y ∈ S := by by_contra h; exact hiso y h hvy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with rfl | rfl | rfl
    · rcases h1_all v hvy.symm with rfl | rfl
      · rcases hnoniso_u with ⟨z, hzS, huz⟩; exact False.elim (hiso z hzS huz)
      · exact False.elim (hvS (by simp [S]))
    · rcases h2_all v hvy.symm with rfl | rfl <;> exact False.elim (hvS (by simp [S]))
    · rcases h3_all v hvy.symm with rfl | rfl
      · exact False.elim (hvS (by simp [S]))
      · rcases hnoniso_u with ⟨z, hzS, huz⟩; exact False.elim (hiso z hzS huz)
  · intro v hvS _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hvS
    rcases hvS with rfl | rfl | rfl
    · exact pcf_at_of_two_distinct_neighbors hd1 hu1.symm h12 hu2n
        (by rw [hψ_out u huS, hψ2]; exact Ne.symm hc₂n.1)
    · exact pcf_at_of_two_distinct_neighbors hd2 h12.symm h23 h13
        (by rw [hψ1, hψ3]; exact hc₁n.2.2)
    · exact pcf_at_of_two_distinct_neighbors hd3 h23.symm h3u hu2n.symm
        (by rw [hψ2, hψ_out u huS]; exact hc₂n.1)

/-- Lemma 3.3(i)：极小反例中，`3`-度点不与任何长度为 `≥ 2` 的 `2`-度点路径相邻（即无 `u-v-w` 满足
`d(u) = 3, d(v) = 2, d(w) = 2`）。 -/
lemma no_three_vertex_two_thread {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v w : V}
    (hdu : G.degree u = 3) (hdv : G.degree v = 2) (hdw : G.degree w = 2)
    (huv : G.Adj u v) (hvw : G.Adj v w) : False := by
  have hvw_ne : v ≠ w := G.ne_of_adj hvw
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have huw_ne : u ≠ w := fun h => by subst h; omega
  rcases exists_other_neighbor_of_deg_two hdw hvw.symm with ⟨ξ, hwξ, hξv, hNw⟩
  have hξw : ξ ≠ w := (G.ne_of_adj hwξ).symm
  -- 若 `ξ = u`，直接由 `no_two_thread_same_anchor` 矛盾！
  by_cases hξu : ξ = u
  · exact no_two_thread_same_anchor hm (by omega) hdv hdw huv hvw (hξu ▸ hwξ)
  -- 现在 `ξ ≠ u`，故 `u` 在 `G - {v, w}` 中恰有 2 个邻点，`ξ` 在 `G - {v, w}` 中至少有 1 个邻点！
  have hNv := neighborFinset_eq_pair_of_deg_two hdv huv.symm hvw huw_ne
  have hv_all : ∀ z, G.Adj v z → z = u ∨ z = w := by
    intro z hz; have : z ∈ ({u, w} : Finset V) := by
      rw [← hNv]; exact (G.mem_neighborFinset v z).mpr hz
    simpa using this
  let S : Finset V := {v, w}
  have huS : u ∉ S := by simp [S, huv_ne, huw_ne]
  have hξS : ξ ∉ S := by simp [S, hξv, hξw]
  have hdξ_ge2 : 2 ≤ G.degree ξ := by
    have h1 := degree_ge_one hm ξ
    by_contra hlt; push Not at hlt
    have := leaf_neighbor_deg_ge_four hm (by omega : G.degree ξ = 1) hwξ.symm
    omega
  have hnoniso_ξ : ∃ z, z ∉ S ∧ G.Adj ξ z := by
    have hlt : ({w} : Finset V).card < (G.neighborFinset ξ).card := by
      rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]; omega
    rcases exists_mem_sdiff_of_lt hlt with ⟨z, hz, hzn⟩
    rw [SimpleGraph.mem_neighborFinset] at hz
    rw [Finset.mem_singleton] at hzn
    refine ⟨z, ?_, hz⟩
    intro hzS; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl
    · rcases hv_all ξ hz.symm with h | h
      · exact hξu h
      · exact hξw h
    · exact hzn rfl
  -- 检查 `G - S` 中包含 `u` 的连通分支 `T_u` 是否是唯一边界为 `u` 的例外 `C_5`！
  have hLv : (L v).card = 4 := by rw [hm.list_card v]; simp [kappa, hdv]
  have hLw : (L w).card = 4 := by rw [hm.list_card w]; simp [kappa, hdw]
  let H := G.induce ((Sᶜ : Finset V) : Set V)
  let Cu := H.connectedComponentMk ⟨u, Finset.mem_compl.mpr huS⟩
  let Tu := compFinset S Cu
  have huTu : u ∈ Tu := (mem_compFinset S Cu u).mpr ⟨Finset.mem_compl.mpr huS, rfl⟩
  have hTu_sub : Tu ⊆ Sᶜ := fun z hz => ((mem_compFinset S Cu z).mp hz).1
  -- 若 `ξ ∈ Tu` 或 `Tu` 非例外 `C_5`：我们先直接处理两种情形！
  -- 情形 A：`ξ ∉ Tu` 且 `G.induce Tu` 是全列表为同 4 元集 `A` 的 `C_5`！
  -- 此时先在 `G - (S ∪ Tu)` 上取容许染色，定出 `c_w, c_v`，再用 `c5_admissible_coloring` 染 `Tu`！
  by_cases hA_ex : ξ ∉ Tu ∧ IsC5 (G.induce (Tu : Set V)) ∧
      ∃ A : Finset ℕ, A.card = 4 ∧ ∀ x : {z : V // z ∈ (Tu : Set V)}, L x.val = A
  · rcases hA_ex with ⟨hξnotTu, hTuC5, A, hA4, hLA⟩
    -- 断言 `Tu` 与 `S` 之间只有 `u` 一条边（因为 `S = {v, w}` 的外部邻点只有 `u, ξ`，而 `ξ ∉ Tu`！）
    have hTu_adj_out : ∀ x ∈ Tu, ∀ z, z ∉ Tu → G.Adj x z → x = u ∧ z = v := by
      intro x hx z hz hxz
      by_cases hzS : z ∈ S
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
        rcases hzS with rfl | rfl
        · rcases hv_all x hxz.symm with rfl | rfl
          · exact ⟨rfl, rfl⟩
          · exact False.elim ((Finset.mem_compl.mp (hTu_sub hx)) (by simp [S]))
        · rcases hNw x hxz.symm with rfl | rfl
          · exact False.elim ((Finset.mem_compl.mp (hTu_sub hx)) (by simp [S]))
          · exact False.elim (hξnotTu hx)
      · -- 若 `z ∉ S`，则 `z` 在同一连通分支 `Tu` 中，矛盾！
        exfalso; apply hz
        rcases (mem_compFinset S Cu x).mp hx with ⟨hxS, hxC⟩
        have hreach : H.Reachable ⟨x, hxS⟩ ⟨z, Finset.mem_compl.mpr hzS⟩ :=
          SimpleGraph.Adj.reachable (show H.Adj ⟨x, hxS⟩ ⟨z, Finset.mem_compl.mpr hzS⟩ from hxz)
        exact (mem_compFinset S Cu z).mpr
          ⟨Finset.mem_compl.mpr hzS, (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hxC⟩
    -- 对 `S' = S ∪ Tu` 取容许染色 `adm`（注意 `ξ ∉ S'` 且 `ξ` 在 `G - S'` 中非孤立！）
    let S' : Finset V := S ∪ Tu
    have hξS' : ξ ∉ S' := by simp [S', hξS, hξnotTu]
    have hnoniso_ξ' : ∃ z, z ∉ S' ∧ G.Adj ξ z := by
      rcases hnoniso_ξ with ⟨z, hzS, hξz⟩
      refine ⟨z, ?_, hξz⟩
      intro hzS'
      simp only [S', Finset.mem_union] at hzS'
      rcases hzS' with h | hzTu
      · exact hzS h
      · have := (hTu_adj_out z hzTu ξ hξnotTu hξz.symm).2
        exact hξS (by rw [this]; simp [S])
    rcases exists_admissible_coloring hm (S := S') ⟨v, by simp [S', S]⟩ with ⟨adm⟩
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {adm.φ ξ, adm.φs ξ})
      (by have := Finset.card_le_two (a := adm.φ ξ) (b := adm.φs ξ); omega) with ⟨cw, hcw, hcwn⟩
    rcases exists_mem_sdiff_of_lt (A := L v) (B := {adm.φ ξ, cw})
      (by have := Finset.card_le_two (a := adm.φ ξ) (b := cw); omega) with ⟨cv, hcv, hcvn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcwn hcvn
    -- 在 4 元集 `A` 中选 `α ∈ A \ {cv, cw}`！
    -- Wait: 在 `c5_admissible_coloring` 中 `u` 染的是 `β ∈ A \ {α}`，我们需要 `β ∉ {cv, cw}` 且 `α ≠ cv`！
    -- 更直接：从 `A \ {cv, cw}` 任选 `β`（`|A|=4 > 2`），从 `A \ {β, cv}` 任选 `α`（`|A|=4 > 2`），
    -- 再从 `A \ {α, β}` 取出其余两色 `γ, δ`，直接按 `exists_c5_cycle` 染 `Tu`！
    rcases exists_mem_sdiff_of_lt (A := A) (B := {cv, cw})
      (by have := Finset.card_le_two (a := cv) (b := cw); omega) with ⟨β, hβA, hβn⟩
    rcases exists_mem_sdiff_of_lt (A := A) (B := {β, cv})
      (by have := Finset.card_le_two (a := β) (b := cv); omega) with ⟨α, hαA, hαn⟩
    rcases exists_mem_sdiff_of_lt (A := A) (B := {α, β})
      (by have := Finset.card_le_two (a := α) (b := β); omega) with ⟨γ, hγA, hγn⟩
    rcases exists_mem_sdiff_of_lt (A := A) (B := {α, β, γ})
      (by have := card_triple_le α β γ; omega) with ⟨δ, hδA, hδn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hβn hαn hγn hδn
    let Fu := G.induce (Tu : Set V)
    have hFuConn : Fu.Connected := induced_comp_connected S Cu
    rcases exists_c5_cycle hFuConn hTuC5 ⟨u, huTu⟩ with
      ⟨t₁, t₂, t₃, t₄, hall5, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n,
        h01, h12, h23, h34, h40⟩
    let φF : {z : V // z ∈ (Tu : Set V)} → ℕ := fun z =>
      if z = ⟨u, huTu⟩ then β
      else if z = t₁ then α
      else if z = t₂ then γ
      else if z = t₃ then δ
      else α
    have hφF0 : φF ⟨u, huTu⟩ = β := by simp [φF]
    have hφF1 : φF t₁ = α := by simp [φF, h01n.symm]
    have hφF2 : φF t₂ = γ := by simp [φF, h02n.symm, h12n.symm]
    have hφF3 : φF t₃ = δ := by simp [φF, h03n.symm, h13n.symm, h23n.symm]
    have hφF4 : φF t₄ = α := by simp [φF, h04n.symm, h14n.symm, h24n.symm, h34n.symm]
    have hNuF := neighborFinset_eq_pair_of_deg_two (hTuC5.2 ⟨u, huTu⟩) h01 h40.symm h14n
    have hN1F := neighborFinset_eq_pair_of_deg_two (hTuC5.2 t₁) h01.symm h12 h02n
    have hN2F := neighborFinset_eq_pair_of_deg_two (hTuC5.2 t₂) h12.symm h23 h13n
    have hN3F := neighborFinset_eq_pair_of_deg_two (hTuC5.2 t₃) h23.symm h34 h24n
    have hN4F := neighborFinset_eq_pair_of_deg_two (hTuC5.2 t₄) h34.symm h40 h03n.symm
    let ψ : V → ℕ := fun z =>
      if z = v then cv else if z = w then cw
      else if hz : z ∈ Tu then φF ⟨z, hz⟩ else adm.φ z
    have hψv : ψ v = cv := by simp [ψ]
    have hψw : ψ w = cw := by simp [ψ, hvw_ne.symm]
    have hψTu : ∀ z (hz : z ∈ Tu), ψ z = φF ⟨z, hz⟩ := by
      intro z hz
      have hzv : z ≠ v := fun h => (Finset.mem_compl.mp (hTu_sub hz)) (by rw [h]; simp [S])
      have hzw : z ≠ w := fun h => (Finset.mem_compl.mp (hTu_sub hz)) (by rw [h]; simp [S])
      simp [ψ, hzv, hzw, hz]
    have hψu : ψ u = β := by rw [hψTu u huTu, hφF0]
    have hψ_out : ∀ z, z ∉ S' → ψ z = adm.φ z := by
      intro z hz; simp only [S', S, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hz
      simp [ψ, hz.1.1, hz.1.2, hz.2]
    have hψ_propF : ∀ a b : {z : V // z ∈ (Tu : Set V)}, Fu.Adj a b → φF a ≠ φF b := by
      intro a b hab
      have ha : a ∈ ({⟨u, huTu⟩, t₁, t₂, t₃, t₄} : Finset {z : V // z ∈ (Tu : Set V)}) := by
        rw [hall5]; exact Finset.mem_univ a
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · have : b ∈ ({t₁, t₄} : Finset _) := by
          rw [← hNuF]; exact (Fu.mem_neighborFinset ⟨u, huTu⟩ b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [hφF0, hφF1]; exact Ne.symm hαn.1
        · rw [hφF0, hφF4]; exact Ne.symm hαn.1
      · have : b ∈ ({⟨u, huTu⟩, t₂} : Finset _) := by
          rw [← hN1F]; exact (Fu.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [hφF1, hφF0]; exact hαn.1
        · rw [hφF1, hφF2]; exact Ne.symm hγn.1
      · have : b ∈ ({t₁, t₃} : Finset _) := by
          rw [← hN2F]; exact (Fu.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [hφF2, hφF1]; exact hγn.1
        · rw [hφF2, hφF3]; exact Ne.symm hδn.2.2
      · have : b ∈ ({t₂, t₄} : Finset _) := by
          rw [← hN3F]; exact (Fu.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [hφF3, hφF2]; exact hδn.2.2
        · rw [hφF3, hφF4]; exact hδn.1
      · have : b ∈ ({t₃, ⟨u, huTu⟩} : Finset _) := by
          rw [← hN4F]; exact (Fu.mem_neighborFinset a b).mpr hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [hφF4, hφF3]; exact Ne.symm hδn.1
        · rw [hφF4, hφF0]; exact hαn.1
    apply adm.contradiction hm ψ hψ_out
    · intro z hz
      simp only [S', S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl) | hzTu
      · rw [hψv]; exact hcv
      · rw [hψw]; exact hcw
      · rw [hψTu z hzTu, hLA ⟨z, hzTu⟩]
        have hmem : ⟨z, hzTu⟩ ∈ ({⟨u, huTu⟩, t₁, t₂, t₃, t₄} : Finset _) := by
          rw [hall5]; exact Finset.mem_univ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h | h <;> rw [h]
        · rw [hφF0]; exact hβA
        · rw [hφF1]; exact hαA
        · rw [hφF2]; exact hγA
        · rw [hφF3]; exact hδA
        · rw [hφF4]; exact hαA
    · intro a b hab hor
      have hcase : ∀ x y, G.Adj x y → x ∈ S' → ψ x ≠ ψ y := by
        intro x y hxy hx
        simp only [S', S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl | rfl) | hxTu
        · rcases hv_all y hxy with hy | hy
          · rw [hy, hψv, hψu]; exact Ne.symm hβn.1
          · rw [hy, hψv, hψw]; exact hcvn.2
        · rcases hNw y hxy with hy | hy
          · rw [hy, hψw, hψv]; exact Ne.symm hcvn.2
          · rw [hy, hψw, hψ_out ξ hξS']; exact hcwn.1
        · by_cases hyTu : y ∈ Tu
          · rw [hψTu x hxTu, hψTu y hyTu]; exact hψ_propF ⟨x, hxTu⟩ ⟨y, hyTu⟩ hxy
          · rcases hTu_adj_out x hxTu y hyTu hxy with ⟨hx', hy'⟩
            rw [hx', hy', hψu, hψv]; exact hβn.1
      rcases hor with ha | hb
      · exact hcase a b hab ha
      · exact (hcase b a hab.symm hb).symm
    · intro z hzS' _ y hyS' hzy
      simp only [S', S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hyS'
      rcases hyS' with (rfl | rfl) | hyTu
      · rcases hv_all z hzy.symm with rfl | rfl
        · exact False.elim (hzS' (by simp [S', huTu]))
        · exact False.elim (hzS' (by simp [S', S]))
      · rcases hNw z hzy.symm with rfl | rfl
        · exact False.elim (hzS' (by simp [S', S]))
        · rw [hψw]; exact hcwn.2
      · rcases hTu_adj_out y hyTu z (fun h => hzS' (by simp [S', h])) hzy.symm with ⟨_, hzv⟩
        exact False.elim (hzS' (by rw [hzv]; simp [S', S]))
    · intro z hzS' hiso ⟨y, hzy⟩
      have hyS' : y ∈ S' := by by_contra h; exact hiso y h hzy
      simp only [S', S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hyS'
      rcases hyS' with (rfl | rfl) | hyTu
      · rcases hv_all z hzy.symm with rfl | rfl
        · exact False.elim (hzS' (by simp [S', huTu]))
        · exact False.elim (hzS' (by simp [S', S]))
      · rcases hNw z hzy.symm with rfl | rfl
        · exact False.elim (hzS' (by simp [S', S]))
        · rcases hnoniso_ξ' with ⟨r, hrS', hξr⟩; exact False.elim (hiso r hrS' hξr)
      · rcases hTu_adj_out y hyTu z (fun h => hzS' (by simp [S', h])) hzy.symm with ⟨_, hzv⟩
        exact False.elim (hzS' (by rw [hzv]; simp [S', S]))
    · intro z hzS' _
      simp only [S', S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hzS'
      rcases hzS' with (rfl | rfl) | hzTu
      · exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw huw_ne
          (by rw [hψu, hψw]; exact hβn.2)
      · exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwξ hξv.symm
          (by rw [hψv, hψ_out ξ hξS']; exact hcvn.1)
      · by_cases hzu : z = u
        · -- `u` 的三个邻点是 `v`（色 `cv`）与 `t₁, t₄`（均为色 `α ≠ cv`），故 `v` 唯一！
          subst z
          refine ⟨v, huv, ?_⟩
          intro r hur hψr
          by_cases hrTu : r ∈ Tu
          · have hrmem : ⟨r, hrTu⟩ ∈ ({t₁, t₄} : Finset _) := by
              rw [← hNuF]; exact (Fu.mem_neighborFinset ⟨u, huTu⟩ ⟨r, hrTu⟩).mpr hur
            simp only [Finset.mem_insert, Finset.mem_singleton] at hrmem
            rw [hψTu r hrTu, hψv] at hψr
            rcases hrmem with h | h <;> rw [h] at hψr
            · rw [hφF1] at hψr; exact False.elim (hαn.2 hψr)
            · rw [hφF4] at hψr; exact False.elim (hαn.2 hψr)
          · exact (hTu_adj_out u huTu r hrTu hur).2
        · -- `z ∈ Tu \ {u}`：`z` 的两个邻点全在 `Tu` 中且异色！
          have hdz2 : G.degree z = 2 := by
            have hsub : G.neighborFinset z = (Fu.neighborFinset ⟨z, hzTu⟩).image Subtype.val := by
              ext r
              simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Subtype.exists]
              constructor
              · intro hzr
                by_cases hrTu : r ∈ Tu
                · exact ⟨r, hrTu, hzr, rfl⟩
                · exact False.elim (hzu (hTu_adj_out z hzTu r hrTu hzr).1)
              · rintro ⟨r, hrTu, hzr, rfl⟩; exact hzr
            rw [← SimpleGraph.card_neighborFinset_eq_degree, hsub,
                Finset.card_image_of_injective _ Subtype.val_injective,
                SimpleGraph.card_neighborFinset_eq_degree, hTuC5.2 ⟨z, hzTu⟩]
          have hmem : ⟨z, hzTu⟩ ∈ ({⟨u, huTu⟩, t₁, t₂, t₃, t₄} : Finset _) := by
            rw [hall5]; exact Finset.mem_univ _
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h | h
          · exact False.elim (hzu (congrArg Subtype.val h))
          · have h1 : z = t₁.val := congrArg Subtype.val h; subst h1
            exact pcf_at_of_two_distinct_neighbors hdz2 h01.symm h12
              (fun heq => h02n (Subtype.ext heq))
              (by
                simp only [Function.Embedding.subtype_apply]
                rw [hψTu u huTu, hψTu t₂.val t₂.property, hφF0, hφF2]
                exact Ne.symm hγn.2)
          · have h2 : z = t₂.val := congrArg Subtype.val h; subst h2
            exact pcf_at_of_two_distinct_neighbors hdz2 h12.symm h23
              (fun heq => h13n (Subtype.ext heq))
              (by
                simp only [Function.Embedding.subtype_apply]
                rw [hψTu t₁.val t₁.property, hψTu t₃.val t₃.property, hφF1, hφF3]
                exact Ne.symm hδn.1)
          · have h3 : z = t₃.val := congrArg Subtype.val h; subst h3
            exact pcf_at_of_two_distinct_neighbors hdz2 h23.symm h34
              (fun heq => h24n (Subtype.ext heq))
              (by
                simp only [Function.Embedding.subtype_apply]
                rw [hψTu t₂.val t₂.property, hψTu t₄.val t₄.property, hφF2, hφF4]
                exact hγn.1)
          · have h4 : z = t₄.val := congrArg Subtype.val h; subst h4
            exact pcf_at_of_two_distinct_neighbors hdz2 h34.symm h40
              (fun heq => h03n (Subtype.ext heq).symm)
              (by
                simp only [Function.Embedding.subtype_apply]
                rw [hψTu t₃.val t₃.property, hψTu u huTu, hφF3, hφF0]
                exact hδn.2.1)
  · -- 情形 B：要么 `Tu` 本身非例外 `C_5`，要么 `ξ ∈ Tu`（可将 `ξ` 选为例外 `C_5` 的特殊点！）
    -- 无论哪种情况，都存在 `G - S` 的容许染色 `adm` 使得 `u` 在 `G - S` 中的两个邻点异色！
    -- 下面先构造这样的容许染色 `adm`（只需在 `Tu` 分支特殊处理即可）！
    have hex_adm : ∃ adm : AdmissibleColoring G L S,
        ∃ a₁ a₂ : V, a₁ ∉ S ∧ a₂ ∉ S ∧ a₁ ≠ a₂ ∧ G.Adj u a₁ ∧ G.Adj u a₂ ∧
          adm.φ a₁ ≠ adm.φ a₂ := by
      -- 先取普通 `exists_admissible_coloring_avoid hm`；若 `u` 在其分支中已满足两邻点异色则直接完成；
      -- 否则 `Tu` 必为例外 `C_5` 且 `ξ ∈ Tu`（由 `¬ hA_ex`！），将 `Tu` 重染为以 `ξ` 为特殊点的容许染色！
      rcases exists_admissible_coloring_avoid hm (S := S) ⟨v, by simp [S]⟩
        (fun _ => ∅) (fun _ => by simp) with ⟨adm₀, _⟩
      rcases exists_two_other_neighbors_of_deg_three (x := v) hdu with
        ⟨u₁, u₂, hu₁v, hu₂v, hu₁₂, huu₁, huu₂⟩
      have hu₁S : u₁ ∉ S := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hu₁v, fun h => ?_⟩
        subst h
        rcases hNw u huu₁.symm with h' | h'
        · exact huv_ne h'
        · exact hξu h'.symm
      have hu₂S : u₂ ∉ S := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hu₂v, fun h => ?_⟩
        subst h
        rcases hNw u huu₂.symm with h' | h'
        · exact huv_ne h'
        · exact hξu h'.symm
      -- 若在 `adm₀` 下 `u` 的两邻点已异色，直接完毕！
      by_cases hdiff : adm₀.φ u₁ ≠ adm₀.φ u₂
      · exact ⟨adm₀, u₁, u₂, hu₁S, hu₂S, hu₁₂, huu₁, huu₂, hdiff⟩
      · -- 否则 `adm₀.φ u₁ = adm₀.φ u₂`！因为 `u` 在 `Tu` 中度数 = 2，所以 `Tu` 没有 PCF `L`-染色，
        -- 故 `Tu` 必为例外 `C_5`；再由 `¬ hA_ex` 得 `ξ ∈ Tu`！
        -- 我们将 `adm₀` 仅在 `Tu` 上替换为以 `ξ` 为特殊点的 `c5_admissible_coloring`！
        let Fu := G.induce (Tu : Set V)
        have hFuConn : Fu.Connected := induced_comp_connected S Cu
        have hTu_ne : Tu.Nonempty := ⟨u, huTu⟩
        have hTu_ne_univ : Tu ≠ Finset.univ := fun heq =>
          (Finset.mem_compl.mp (hTu_sub (heq ▸ Finset.mem_univ v))) (by simp [S])
        have hTu_closed : ∀ a ∈ Tu, ∀ b, b ∉ S → G.Adj a b → b ∈ Tu := by
          intro a ha b hbS hab
          rcases (mem_compFinset S Cu a).mp ha with ⟨haS, haC⟩
          have hreach : H.Reachable ⟨a, haS⟩ ⟨b, Finset.mem_compl.mpr hbS⟩ :=
            SimpleGraph.Adj.reachable (show H.Adj ⟨a, haS⟩ ⟨b, Finset.mem_compl.mpr hbS⟩ from hab)
          exact (mem_compFinset S Cu b).mpr
            ⟨Finset.mem_compl.mpr hbS, (SimpleGraph.ConnectedComponent.sound hreach).symm.trans haC⟩
        have hLFu : ∀ x : {z : V // z ∈ (Tu : Set V)}, kappa Fu x ≤ (L x.val).card := by
          intro x; rw [hm.list_card x.val]; exact kappa_mono (degree_induce_le G Tu x)
        -- 若 `Fu` 存在 PCF `L`-染色，则把 `adm₀` 在 `Tu` 上替换成该 PCF 染色即得 `u` 两邻点异色！
        by_cases hpcfFu : ∃ φF : {z : V // z ∈ (Tu : Set V)} → ℕ,
            IsPCFColoring Fu φF ∧ ∀ x, φF x ∈ L x.val
        · rcases hpcfFu with ⟨φF, ⟨hpropF, hpcfF⟩, hmemF⟩
          have huniqF : ∀ z : V, ∃ c : ℕ, ∀ (hz : z ∈ Tu),
              (∃ y ∈ Tu, G.Adj z y) →
              ∃ a, ∃ ha : a ∈ Tu, G.Adj z a ∧ φF ⟨a, ha⟩ = c ∧
                ∀ b, ∀ hb : b ∈ Tu, G.Adj z b → φF ⟨b, hb⟩ = c → b = a := by
            intro z
            by_cases hc : ∃ (hz : z ∈ Tu), ∃ y ∈ Tu, G.Adj z y
            · rcases hc with ⟨hz, y, hy, hzy⟩
              rcases hpcfF ⟨z, hz⟩ ⟨⟨y, hy⟩, hzy⟩ with ⟨⟨a, ha⟩, hza, ha_u⟩
              refine ⟨φF ⟨a, ha⟩, fun _ _ => ⟨a, ha, hza, rfl, ?_⟩⟩
              intro b hb hzb hφb
              exact congrArg Subtype.val (ha_u ⟨b, hb⟩ hzb hφb)
            · exact ⟨0, fun hz hy => False.elim (hc ⟨hz, hy⟩)⟩
          choose φsF hφsF using huniqF
          let φ' : V → ℕ := fun z => if hz : z ∈ Tu then φF ⟨z, hz⟩ else adm₀.φ z
          let φs' : V → ℕ := fun z => if z ∈ Tu then φsF z else adm₀.φs z
          have hφ'_Tu : ∀ z (hz : z ∈ Tu), φ' z = φF ⟨z, hz⟩ := fun z hz => by simp [φ', hz]
          have hφ'_out : ∀ z, z ∉ Tu → φ' z = adm₀.φ z := fun z hz => by simp [φ', hz]
          have hu₁Tu : u₁ ∈ Tu := hTu_closed u huTu u₁ hu₁S huu₁
          have hu₂Tu : u₂ ∈ Tu := hTu_closed u huTu u₂ hu₂S huu₂
          rcases hφsF u huTu ⟨u₁, hu₁Tu, huu₁⟩ with ⟨a, haTu, hua, hφa, ha_uniq⟩
          have hcol_u : ∃ b, b ∉ S ∧ a ≠ b ∧ G.Adj u b ∧ φ' a ≠ φ' b := by
            by_cases hau1 : a = u₁
            · refine ⟨u₂, hu₂S, hau1 ▸ hu₁₂, huu₂, ?_⟩
              rw [hφ'_Tu a haTu, hφ'_Tu u₂ hu₂Tu, hφa]
              intro heq; exact hu₁₂ (hau1.symm.trans (ha_uniq u₂ hu₂Tu huu₂ heq.symm).symm)
            · refine ⟨u₁, hu₁S, hau1, huu₁, ?_⟩
              rw [hφ'_Tu a haTu, hφ'_Tu u₁ hu₁Tu, hφa]
              intro heq; exact hau1 (ha_uniq u₁ hu₁Tu huu₁ heq.symm).symm
          rcases hcol_u with ⟨b, hbS, hab, hub, hφab⟩
          refine ⟨⟨φ', φs', ?_, ?_, ?_⟩, a, b, Finset.mem_compl.mp (hTu_sub haTu), hbS, hab,
            hua, hub, hφab⟩
          · intro z hzS
            by_cases hzTu : z ∈ Tu
            · rw [hφ'_Tu z hzTu]; exact hmemF ⟨z, hzTu⟩
            · rw [hφ'_out z hzTu]; exact adm₀.mem_list z hzS
          · intro x y hxS hyS hxy
            by_cases hxTu : x ∈ Tu
            · have hyTu : y ∈ Tu := hTu_closed x hxTu y hyS hxy
              rw [hφ'_Tu x hxTu, hφ'_Tu y hyTu]; exact hpropF ⟨x, hxTu⟩ ⟨y, hyTu⟩ hxy
            · have hyTu : y ∉ Tu := fun hy => hxTu (hTu_closed y hy x hxS hxy.symm)
              rw [hφ'_out x hxTu, hφ'_out y hyTu]; exact adm₀.proper x y hxS hyS hxy
          · intro ψ hagree z hzS ⟨r, hrS, hzr⟩ havoid
            by_cases hzTu : z ∈ Tu
            · have hrTu : r ∈ Tu := hTu_closed z hzTu r hrS hzr
              rcases hφsF z hzTu ⟨r, hrTu, hzr⟩ with ⟨m, hmTu, hzm, hφm, hm_uniq⟩
              refine ⟨m, hzm, ?_⟩
              intro y hzy hψy
              have hψm : ψ m = φsF z := by
                rw [hagree m (Finset.mem_compl.mp (hTu_sub hmTu)), hφ'_Tu m hmTu, hφm]
              by_cases hyS : y ∈ S
              · have hav := havoid y hyS hzy
                simp only [φs', hzTu, ite_true] at hav
                exact False.elim (hav (hψy.trans hψm))
              · have hyTu : y ∈ Tu := hTu_closed z hzTu y hyS hzy
                have hφy : φF ⟨y, hyTu⟩ = φsF z := by
                  rw [← hφ'_Tu y hyTu, ← hagree y hyS, hψy, hψm]
                exact hm_uniq y hyTu hzy hφy
            · have hrTu : r ∉ Tu := fun hr => hzTu (hTu_closed r hr z hzS hzr.symm)
              -- 对 `z ∉ Tu`，构造与 `adm₀` 仅在 `S` 上不同的辅助染色 `ψ₀`（因 `z` 无邻点在 `Tu`！）
              let ψ₀ : V → ℕ := fun x => if x ∈ S then ψ x else adm₀.φ x
              have hagree₀ : ∀ x, x ∉ S → ψ₀ x = adm₀.φ x := fun x hx => by simp [ψ₀, hx]
              have havoid₀ : ∀ y, y ∈ S → G.Adj z y → ψ₀ y ≠ adm₀.φs z := by
                intro y hyS hzy
                simp only [ψ₀, hyS, ite_true]
                have hav := havoid y hyS hzy
                simpa [φs', hzTu] using hav
              rcases adm₀.pcf_preserve ψ₀ hagree₀ z hzS ⟨r, hrS, hzr⟩ havoid₀ with
                ⟨m, hzm, hm_uniq⟩
              have hψ_eq_ψ₀ : ∀ y, G.Adj z y → ψ y = ψ₀ y := by
                intro y hzy
                by_cases hyS : y ∈ S
                · simp [ψ₀, hyS]
                · have hyTu : y ∉ Tu := fun hy => hzTu (hTu_closed y hy z hzS hzy.symm)
                  rw [hagree y hyS, hφ'_out y hyTu]; simp [ψ₀, hyS]
              refine ⟨m, hzm, ?_⟩
              intro y hzy hψy
              exact hm_uniq y hzy (by rw [← hψ_eq_ψ₀ y hzy, ← hψ_eq_ψ₀ m hzm, hψy])
        · -- `Fu` 无 PCF `L`-染色：故 `Fu` 为例外 `C_5`，由 `¬ hA_ex` 推出 `ξ ∈ Tu`！
          have hFuC5 : IsC5 Fu := by
            by_contra hneC5
            exact hpcfFu (hm.minimal Tu hTu_ne hTu_ne_univ hFuConn hneC5 (fun x => L x.val) hLFu)
          have hL4F : ∀ x : {z : V // z ∈ (Tu : Set V)}, 4 ≤ (L x.val).card := by
            intro x; have h1 := hLFu x; have h2 : kappa Fu x = 4 := by simp [kappa, hFuC5.2 x]
            omega
          have hallA :
              ∃ A : Finset ℕ, A.card = 4 ∧ ∀ x : {z : V // z ∈ (Tu : Set V)}, L x.val = A := by
            by_contra hnot
            exact hpcfFu (c5_pcf_colorable_of_ne hFuConn hFuC5 (fun x => L x.val) hL4F hnot)
          rcases hallA with ⟨A, hA4, hLA⟩
          have hξTu : ξ ∈ Tu := by
            by_contra hnot; exact hA_ex ⟨hnot, hFuC5, A, hA4, hLA⟩
          -- `ξ` 在 `S` 中唯一邻点为 `w`（因为 `|L ξ| = 4` 且 `d_Fu ξ = 2` 且 `ξ` 与 `w` 相邻，故 `d_G ξ = 3`）
          have hξ_uniqS : ∀ y ∈ S, G.Adj ξ y → y = w := by
            intro y hyS hξy
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
            rcases hyS with rfl | rfl
            · rcases hv_all ξ hξy.symm with h | h
              · exact False.elim (hξu h)
              · exact False.elim (hξw h)
            · rfl
          rcases Finset.card_pos.mp (by omega : 0 < A.card) with ⟨α, hαA⟩
          rcases c5_admissible_coloring hFuConn hFuC5 A hA4 ⟨ξ, hξTu⟩ α hαA with
            ⟨φF, hmemF, hpropF, hnbξ, hpcfOther⟩
          have huniqF : ∀ z : V, ∃ c : ℕ,
              (z = ξ → c = α) ∧
              (∀ (hz : z ∈ Tu), z ≠ ξ →
                ∃ a, ∃ ha : a ∈ Tu, G.Adj z a ∧ φF ⟨a, ha⟩ = c ∧
                  ∀ b, ∀ hb : b ∈ Tu, G.Adj z b → φF ⟨b, hb⟩ = c → b = a) := by
            intro z
            by_cases hzξ : z = ξ
            · exact ⟨α, fun _ => rfl, fun _ hne => False.elim (hne hzξ)⟩
            · by_cases hz : z ∈ Tu
              · have hne : (⟨z, hz⟩ : {x : V // x ∈ (Tu : Set V)}) ≠ ⟨ξ, hξTu⟩ :=
                  fun h => hzξ (congrArg Subtype.val h)
                rcases hpcfOther ⟨z, hz⟩ hne with ⟨⟨a, ha⟩, hza, ha_u⟩
                refine ⟨φF ⟨a, ha⟩, fun h => False.elim (hzξ h), fun _ _ => ⟨a, ha, hza, rfl, ?_⟩⟩
                intro b hb hzb hφb
                exact congrArg Subtype.val (ha_u ⟨b, hb⟩ hzb hφb)
              · exact ⟨0, fun h => False.elim (hzξ h), fun hz' _ => False.elim (hz hz')⟩
          choose φsF hφsF_ξ hφsF_other using huniqF
          let φ' : V → ℕ := fun z => if hz : z ∈ Tu then φF ⟨z, hz⟩ else adm₀.φ z
          let φs' : V → ℕ := fun z => if z ∈ Tu then φsF z else adm₀.φs z
          have hφ'_Tu : ∀ z (hz : z ∈ Tu), φ' z = φF ⟨z, hz⟩ := fun z hz => by simp [φ', hz]
          have hφ'_out : ∀ z, z ∉ Tu → φ' z = adm₀.φ z := fun z hz => by simp [φ', hz]
          have hu₁Tu : u₁ ∈ Tu := hTu_closed u huTu u₁ hu₁S huu₁
          have hu₂Tu : u₂ ∈ Tu := hTu_closed u huTu u₂ hu₂S huu₂
          rcases hφsF_other u huTu (Ne.symm hξu) with ⟨a, haTu, hua, hφa, ha_uniq⟩
          have hcol_u : ∃ b, b ∉ S ∧ a ≠ b ∧ G.Adj u b ∧ φ' a ≠ φ' b := by
            by_cases hau1 : a = u₁
            · refine ⟨u₂, hu₂S, hau1 ▸ hu₁₂, huu₂, ?_⟩
              rw [hφ'_Tu a haTu, hφ'_Tu u₂ hu₂Tu, hφa]
              intro heq; exact hu₁₂ (hau1.symm.trans (ha_uniq u₂ hu₂Tu huu₂ heq.symm).symm)
            · refine ⟨u₁, hu₁S, hau1, huu₁, ?_⟩
              rw [hφ'_Tu a haTu, hφ'_Tu u₁ hu₁Tu, hφa]
              intro heq; exact hau1 (ha_uniq u₁ hu₁Tu huu₁ heq.symm).symm
          rcases hcol_u with ⟨b, hbS, hab, hub, hφab⟩
          refine ⟨⟨φ', φs', ?_, ?_, ?_⟩, a, b, Finset.mem_compl.mp (hTu_sub haTu), hbS, hab,
            hua, hub, hφab⟩
          · intro z hzS
            by_cases hzTu : z ∈ Tu
            · rw [hφ'_Tu z hzTu, hLA ⟨z, hzTu⟩]; exact hmemF ⟨z, hzTu⟩
            · rw [hφ'_out z hzTu]; exact adm₀.mem_list z hzS
          · intro x y hxS hyS hxy
            by_cases hxTu : x ∈ Tu
            · have hyTu : y ∈ Tu := hTu_closed x hxTu y hyS hxy
              rw [hφ'_Tu x hxTu, hφ'_Tu y hyTu]; exact hpropF ⟨x, hxTu⟩ ⟨y, hyTu⟩ hxy
            · have hyTu : y ∉ Tu := fun hy => hxTu (hTu_closed y hy x hxS hxy.symm)
              rw [hφ'_out x hxTu, hφ'_out y hyTu]; exact adm₀.proper x y hxS hyS hxy
          · intro ψ hagree z hzS ⟨r, hrS, hzr⟩ havoid
            by_cases hzTu : z ∈ Tu
            · by_cases hzξ : z = ξ
              · subst hzξ
                have hαeq : φs' z = α := by simp [φs', hzTu, hφsF_ξ z rfl]
                refine ⟨w, hwξ.symm, ?_⟩
                intro y hzy hψy
                by_cases hyS : y ∈ S
                · exact hξ_uniqS y hyS hzy
                · have hyTu : y ∈ Tu := hTu_closed z hzTu y hyS hzy
                  have hψy_α : ψ y = α := by
                    rw [hagree y hyS, hφ'_Tu y hyTu]; exact hnbξ ⟨y, hyTu⟩ hzy
                  exact False.elim (havoid w (by simp [S]) hwξ.symm (by rw [hαeq, ← hψy_α, hψy]))
              · rcases hφsF_other z hzTu hzξ with ⟨m, hmTu, hzm, hφm, hm_uniq⟩
                refine ⟨m, hzm, ?_⟩
                intro y hzy hψy
                have hψm : ψ m = φsF z := by
                  rw [hagree m (Finset.mem_compl.mp (hTu_sub hmTu)), hφ'_Tu m hmTu, hφm]
                by_cases hyS : y ∈ S
                · have hav := havoid y hyS hzy
                  simp only [φs', hzTu, ite_true] at hav
                  exact False.elim (hav (hψy.trans hψm))
                · have hyTu : y ∈ Tu := hTu_closed z hzTu y hyS hzy
                  have hφy : φF ⟨y, hyTu⟩ = φsF z := by
                    rw [← hφ'_Tu y hyTu, ← hagree y hyS, hψy, hψm]
                  exact hm_uniq y hyTu hzy hφy
            · let ψ₀ : V → ℕ := fun x => if x ∈ S then ψ x else adm₀.φ x
              have hagree₀ : ∀ x, x ∉ S → ψ₀ x = adm₀.φ x := fun x hx => by simp [ψ₀, hx]
              have havoid₀ : ∀ y, y ∈ S → G.Adj z y → ψ₀ y ≠ adm₀.φs z := by
                intro y hyS hzy
                simp only [ψ₀, hyS, ite_true]
                have hav := havoid y hyS hzy
                simpa [φs', hzTu] using hav
              rcases adm₀.pcf_preserve ψ₀ hagree₀ z hzS ⟨r, hrS, hzr⟩ havoid₀ with
                ⟨m, hzm, hm_uniq⟩
              have hψ_eq_ψ₀ : ∀ y, G.Adj z y → ψ y = ψ₀ y := by
                intro y hzy
                by_cases hyS : y ∈ S
                · simp [ψ₀, hyS]
                · have hyTu : y ∉ Tu := fun hy => hzTu (hTu_closed y hy z hzS hzy.symm)
                  rw [hagree y hyS, hφ'_out y hyTu]; simp [ψ₀, hyS]
              refine ⟨m, hzm, ?_⟩
              intro y hzy hψy
              exact hm_uniq y hzy (by rw [← hψ_eq_ψ₀ y hzy, ← hψ_eq_ψ₀ m hzm, hψy])
    -- 用 `hex_adm` 一步完成 `v, w` 的染色延拓！
    rcases hex_adm with ⟨adm, a₁, a₂, ha₁S, ha₂S, ha₁₂, hua₁, hua₂, hcol12⟩
    rcases exists_mem_sdiff_of_lt (A := L w) (B := {adm.φ ξ, adm.φs ξ, adm.φ u})
      (by have := card_triple_le (adm.φ ξ) (adm.φs ξ) (adm.φ u); omega) with ⟨cw, hcw, hcwn⟩
    rcases exists_mem_sdiff_of_lt (A := L v) (B := {adm.φ ξ, cw, adm.φ u})
      (by have := card_triple_le (adm.φ ξ) cw (adm.φ u); omega) with ⟨cv, hcv, hcvn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcwn hcvn
    let ψ : V → ℕ := fun z => if z = v then cv else if z = w then cw else adm.φ z
    have hψv : ψ v = cv := by simp [ψ]
    have hψw : ψ w = cw := by simp [ψ, hvw_ne.symm]
    have hψ_out : ∀ z, z ∉ S → ψ z = adm.φ z := by
      intro z hz; simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      simp [ψ, hz.1, hz.2]
    apply hm.not_colorable
    refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
    · intro a b hab
      have hcase : ∀ x y, G.Adj x y → x ∈ S → ψ x ≠ ψ y := by
        intro x y hxy hx; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · rcases hv_all y hxy with hy | hy
          · rw [hy, hψv, hψ_out u huS]; exact hcvn.2.2
          · rw [hy, hψv, hψw]; exact hcvn.2.1
        · rcases hNw y hxy with hy | hy
          · rw [hy, hψw, hψv]; exact Ne.symm hcvn.2.1
          · rw [hy, hψw, hψ_out ξ hξS]; exact hcwn.1
      by_cases h : a ∈ S ∨ b ∈ S
      · rcases h with ha | hb
        · exact hcase a b hab ha
        · exact (hcase b a hab.symm hb).symm
      · push Not at h
        rw [hψ_out a h.1, hψ_out b h.2]
        exact adm.proper a b h.1 h.2 hab
    · intro z hz
      by_cases hzS : z ∈ S
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
        rcases hzS with rfl | rfl
        · exact pcf_at_of_two_distinct_neighbors hdv huv.symm hvw huw_ne
            (by rw [hψ_out u huS, hψw]; exact Ne.symm hcwn.2.2)
        · exact pcf_at_of_two_distinct_neighbors hdw hvw.symm hwξ hξv.symm
            (by rw [hψv, hψ_out ξ hξS]; exact hcvn.1)
      · by_cases hzu : z = u
        · subst hzu
          exact pcf_at_deg_three_of_two_distinct hdu hua₁ hua₂ ha₁₂
            (by rw [hψ_out a₁ ha₁S, hψ_out a₂ ha₂S]; exact hcol12)
        · -- `z ∉ S` 且 `z ≠ u`：若 `z` 与 `S` 相邻则只能是 `z = ξ`（邻 `w`）！
          have hnoniso_z : ∃ r, r ∉ S ∧ G.Adj z r := by
            by_cases hzξ : z = ξ
            · rw [hzξ]; exact hnoniso_ξ
            · rcases hz with ⟨r, hzr⟩
              refine ⟨r, ?_, hzr⟩
              intro hrS; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hrS
              rcases hrS with rfl | rfl
              · rcases hv_all z hzr.symm with h | h
                · exact hzu h
                · exact hzS (by rw [h]; simp [S])
              · rcases hNw z hzr.symm with h | h
                · exact hzS (by rw [h]; simp [S])
                · exact hzξ h
          apply adm.pcf_preserve ψ hψ_out z hzS hnoniso_z
          intro y hyS hzy
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyS
          rcases hyS with rfl | rfl
          · rcases hv_all z hzy.symm with h | h
            · exact False.elim (hzu h)
            · exact False.elim (hzS (by rw [h]; simp [S]))
          · rcases hNw z hzy.symm with h | h
            · exact False.elim (hzS (by rw [h]; simp [S]))
            · subst h; rw [hψw]; exact hcwn.2.1
    · intro z
      by_cases hzS : z ∈ S
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hzS
        rcases hzS with rfl | rfl
        · rw [hψv]; exact hcv
        · rw [hψw]; exact hcw
      · rw [hψ_out z hzS]; exact adm.mem_list z hzS

end LeanResearch.Proposal3
