/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.ThreeThreadExt

/-!
# 引理 E1：变参定色延拓与 `no_T3_adj_T3`（`T3Adjacency`）

本模块基于 `ThreeThreadExt` 的纯组合定色延拓引擎，形式化变参定色延拓助手（`t3_fun_color_extension`、
`t20_fun_color_extension`）及第一条 `T3` 邻接限制：
- `no_T3_adj_T3`：在 `9 * p ≤ 22 * q` 下，任意两个 `T3` 顶点不相邻。

（其余 3 条邻接限制 `no_T3_adj_T21`、`no_T3_adj_S3_2_a2` 与 `no_T3_T20_T3` 见 `T3Adjacency2`。）
-/

@[expose] public section

namespace LeanResearch.Proposal3

/-! ## 1. 变参定色延拓与通用密度/不交辅助引理 -/

/-- `t3_fixed_color_extension` 的变参版本：第二好邻点颜色 `δ α` 允许依赖于 `α`！ -/
lemma t3_fun_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {L₁ L₂ Z₃ C_u : Finset ℕ} {φy φz : ℕ} (δ : ℕ → ℕ)
    (hY1 : 1 ≤ Y.card) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hL1 : L₁.card = 4) (hL2' : L₂.card = 4) (hZ3 : 2 ≤ Z₃.card)
    (hCu : Y.card + 1 ≤ C_u.card) :
    ∃ α ∈ C_u, ∃ c₁ ∈ threeThreadGoodCols L₁ L₂ Z₃ φz α,
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([c₁, φy, δ α] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → Option {r : V // r ∈ Y} → Finset ℕ := fun α o =>
    match o with
    | none => threeThreadGoodCols L₁ L₂ Z₃ φz α
    | some r => L r.val \ {α}
  have hA_ne : ∀ α o, (A α o).Nonempty := by
    intro α o; cases o with
    | none => exact threeThreadGoodCols_nonempty hL1 hL2' (Finset.card_pos.mp (by omega))
    | some r =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}; have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C_u, ¬ ∃ f, IsPCFRep (A α) [φy, δ α] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (some ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (some ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt_eq : (Y.filter (fun r => aY r = γ)).card +
        ([f none, φy, δ α] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ)).card =
          (if f none = γ then 1 else 0) + (Y.filter (fun r => aY r = γ)).card := by
        rw [Finset.card_filter, Fintype.sum_option]
        congr 1
        rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
        apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
      have hlist : ([f none, φy, δ α] : List ℕ).count γ =
          (if f none = γ then 1 else 0) + ([φy, δ α] : List ℕ).count γ := by
        simp only [List.count_cons, beq_iff_eq]; split_ifs <;> omega
      omega
    exact hno α hα (f none) (hf_mem none) aY haY γ hcnt_eq
  have hlower : 2 * C_u.card ≤
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card := by
    calc 2 * C_u.card = ∑ _α ∈ C_u, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        no_pcfRep_pair_ge_two (hA_ne α) (by rw [Fintype.card_option, Fintype.card_coe]; omega)
          (hno_rep α hα)
  have hupper :
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card ≤
        1 + 2 * Y.card := by
    rw [sum_filter_card_comm, Fintype.sum_option]
    have h1 := threeThreadGoodCols_card_one_le_one C_u (φz := φz) hL1 hL2' hZ3
    have hsumY : ∑ r : {r // r ∈ Y}, (C_u.filter (fun α => (A α (some r)).card = 1)).card =
        ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [← Finset.sum_attach Y (fun r => (C_u.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
    rw [hsumY]
    have h2 : ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card ≤ 2 * Y.card := by
      calc ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C_u (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    dsimp only [A] at *; omega
  omega

/-- `T20` 变参定色延拓引理：给定两个好邻点颜色函数 `δ₁, δ₂ : ℕ → ℕ` 与 `2`-线串 `cFun`，
只要 `|C_u| ≥ |Y| + 2`，总存在合法延拓使 `u` 满足 PCF（`2 * (h + 2) ≤ 3 + 2 * h` 矛盾）！ -/
lemma t20_fun_color_extension {V : Type*}
    {L : V → Finset ℕ} {Y : Finset V} {Lv C_u : Finset ℕ} (cFun δ₁ δ₂ : ℕ → ℕ) {φz : ℕ}
    (hY1 : 1 ≤ Y.card) (hL2 : ∀ r ∈ Y, (L r).card = 2)
    (hLv : Lv.card = 4) (hCu : Y.card + 2 ≤ C_u.card) :
    ∃ α ∈ C_u, ∃ cv ∈ Lv \ {α, cFun α, φz},
    ∃ aY : V → ℕ, (∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α) ∧
    ∃ γ : ℕ, (Y.filter (fun r => aY r = γ)).card + ([cv, δ₁ α, δ₂ α] : List ℕ).count γ = 1 := by
  classical
  by_contra hno
  push Not at hno
  let A : ℕ → Option {r : V // r ∈ Y} → Finset ℕ := fun α o =>
    match o with
    | none => Lv \ {α, cFun α, φz}
    | some r => L r.val \ {α}
  have hA_ne : ∀ α o, (A α o).Nonempty := by
    intro α o; cases o with
    | none =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge Lv {α, cFun α, φz}; have h2 := card_triple_le α (cFun α) φz; omega
    | some r =>
      dsimp only [A]; rw [← Finset.card_pos]
      have h1 := card_sdiff_ge (L r.val) {α}; have h2 := hL2 r.val r.property
      simp only [Finset.card_singleton] at h1; omega
  have hno_rep : ∀ α ∈ C_u, ¬ ∃ f, IsPCFRep (A α) [δ₁ α, δ₂ α] f := by
    intro α hα ⟨f, hf_mem, γ, hγ⟩
    let aY : V → ℕ := fun r => if hr : r ∈ Y then f (some ⟨r, hr⟩) else 0
    have haY : ∀ r ∈ Y, aY r ∈ L r ∧ aY r ≠ α := by
      intro r hr; simp only [aY, hr, dite_true]
      have hm := hf_mem (some ⟨r, hr⟩)
      simp only [A, Finset.mem_sdiff, Finset.mem_singleton] at hm; exact hm
    have hcnt_eq : (Y.filter (fun r => aY r = γ)).card +
        ([f none, δ₁ α, δ₂ α] : List ℕ).count γ = 1 := by
      have hsplit : (Finset.univ.filter (fun o : Option {r // r ∈ Y} => f o = γ)).card =
          (if f none = γ then 1 else 0) + (Y.filter (fun r => aY r = γ)).card := by
        rw [Finset.card_filter, Fintype.sum_option]
        congr 1
        rw [Finset.card_filter, ← Finset.sum_attach Y (fun r => if aY r = γ then 1 else 0)]
        apply Finset.sum_congr rfl; intro r _; simp only [aY, r.property, dite_true]
      have hlist : ([f none, δ₁ α, δ₂ α] : List ℕ).count γ =
          (if f none = γ then 1 else 0) + ([δ₁ α, δ₂ α] : List ℕ).count γ := by
        simp only [List.count_cons, beq_iff_eq]; split_ifs <;> omega
      omega
    exact hno α hα (f none) (hf_mem none) aY haY γ hcnt_eq
  have hlower : 2 * C_u.card ≤
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card := by
    calc 2 * C_u.card = ∑ _α ∈ C_u, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α hα =>
        no_pcfRep_pair_ge_two (hA_ne α) (by rw [Fintype.card_option, Fintype.card_coe]; omega)
          (hno_rep α hα)
  have hupper :
      ∑ α ∈ C_u, (Finset.univ.filter (fun o : Option {r // r ∈ Y} => (A α o).card = 1)).card ≤
        3 + 2 * Y.card := by
    rw [sum_filter_card_comm, Fintype.sum_option]
    have h1 := (card_filter_sdiff_triple_eq_one_le C_u Lv hLv cFun φz).1
    have hsumY : ∑ r : {r // r ∈ Y}, (C_u.filter (fun α => (A α (some r)).card = 1)).card =
        ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card := by
      rw [← Finset.sum_attach Y (fun r => (C_u.filter (fun α => (L r \ {α}).card = 1)).card)]; rfl
    rw [hsumY]
    have h2 : ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card ≤ 2 * Y.card := by
      calc ∑ r ∈ Y, (C_u.filter (fun α => (L r \ {α}).card = 1)).card
          ≤ ∑ _r ∈ Y, 2 := Finset.sum_le_sum fun r hr =>
            (card_filter_sdiff_singleton_eq_one_le C_u (L r) (by have := hL2 r hr; omega)).1
        _ = 2 * Y.card := by simp [mul_comm]
    dsimp only [A] at *; omega
  omega

/-- 若有限核心子图 `K` 恰有 `n` 个顶点且核心度之和为 `s`，当 `9 * p ≤ 22 * q` 且 `22 * n ≤ 9 * s`
时直接与 `MadLt G p q` 矛盾！ -/
lemma mad_22_9_contra {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {n s : ℕ}
    (hcard : (coreVerts G).card = n) (hsum : ∑ u ∈ coreVerts G, coreDeg G u = s)
    (hviol : 22 * n ≤ 9 * s) : False := by
  have hlt : q * ∑ u ∈ coreVerts G, coreDeg G u < p * (coreVerts G).card :=
    mad_core_sum_lt hm.mad (coreVerts_nonempty hm)
  rw [hcard, hsum] at hlt
  have h1 : 9 * (q * s) < 9 * (p * n) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  have h2 : 9 * (p * n) ≤ 22 * q * n := by
    calc 9 * (p * n) = (9 * p) * n := by ring
      _ ≤ (22 * q) * n := Nat.mul_le_mul_right n hpq
      _ = 22 * q * n := by ring
  have h3 : 22 * q * n ≤ 9 * (q * s) := by
    calc 22 * q * n = q * (22 * n) := by ring
      _ ≤ q * (9 * s) := Nat.mul_le_mul_left q hviol
      _ = 9 * (q * s) := by ring
  omega

/-- `3`-线串内部三个 `2`-度点的锚点集均等于 `{u, z}`！ -/
lemma threeThread_anchors_eq {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) {u v₁ v₂ v₃ z : V}
    (hdu : 3 ≤ G.degree u) (hdz : 3 ≤ G.degree z) (huz : u ≠ z)
    (hd1 : G.degree v₁ = 2) (hd2 : G.degree v₂ = 2) (hd3 : G.degree v₃ = 2)
    (hu1 : G.Adj u v₁) (h12 : G.Adj v₁ v₂) (hv2u : v₂ ≠ u)
    (h23 : G.Adj v₂ v₃) (hv31 : v₃ ≠ v₁) (h3z : G.Adj v₃ z) (hzv2 : z ≠ v₂) :
    threadAnchors G v₁ = {u, z} ∧ threadAnchors G v₂ = {u, z} ∧ threadAnchors G v₃ = {u, z} := by
  have hv3u : v₃ ≠ u := fun h => by subst h; omega
  have hv1z : v₁ ≠ z := fun h => by subst h; omega
  have hmk : ∀ x, G.degree x = 2 → IsThreadAnchor G u x → IsThreadAnchor G z x →
      threadAnchors G x = {u, z} := by
    intro x hdx ha1 ha2
    have hsub : ({u, z} : Finset V) ⊆ threadAnchors G x := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_threadAnchors]
      rcases ht with rfl | rfl
      · exact ha1
      · exact ha2
    symm
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [card_threadAnchors_eq_two hm hdx, Finset.card_pair huz])
  refine ⟨hmk v₁ hd1 ⟨hdu, hd1, Or.inl hu1⟩
    ⟨hdz, hd1, Or.inr (Or.inr ⟨v₃, v₂, hd3, hd2, h3z.symm, h23.symm, h12.symm,
      hzv2, hv31, hv1z.symm⟩)⟩,
    hmk v₂ hd2 ⟨hdu, hd2, Or.inr (Or.inl ⟨v₁, hd1, hu1, h12, hv2u⟩)⟩
    ⟨hdz, hd2, Or.inr (Or.inl ⟨v₃, hd3, h3z.symm, h23.symm, hzv2.symm⟩)⟩,
    hmk v₃ hd3 ⟨hdu, hd3, Or.inr (Or.inr ⟨v₁, v₂, hd1, hd2, hu1, h12, h23,
      hv2u.symm, hv31.symm, hv3u.symm⟩)⟩
    ⟨hdz, hd3, Or.inl h3z.symm⟩⟩

/-! ## 2. 引理 E1：`no_T3_adj_T3`（任意两个 `T3` 顶点不相邻） -/

/-- 引理 E1：在 `9 * p ≤ 22 * q` 下，两个 `T3` 顶点不能相邻！ -/
lemma no_T3_adj_T3 {p q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset ℕ}
    (hm : MinimalCounterexample p q G L) (hpq : 9 * p ≤ 22 * q) {u₁ u₂ : V}
    (hu1 : IsT3 G u₁) (hu2 : IsT3 G u₂) (hadj : G.Adj u₁ u₂) : False := by
  classical
  have hpq25 : 2 * p ≤ 5 * q := by omega
  have hu12 : u₁ ≠ u₂ := G.ne_of_adj hadj
  rcases isT3_unpack hm hpq25 hu1 with
    ⟨v₁, v₂, v₃, z₁, x₁, y₁', huv₁, hdv₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, hdz1,
      hz1u1, hx₁, hy₁', hxy₁, hcore1, hY1_pos, hY1_card, hall_u1', hall_v1, hall_v2, hall_v3⟩
  rcases isT3_unpack hm hpq25 hu2 with
    ⟨w₁, w₂, w₃, z₂, x₂, y₂', huw₁, hdw₁, hw12, hw2u2, hdw₂, hw23, hw31, hdw₃, hw3z2, hzw2, hdz2,
      hz2u2, hx₂, hy₂', hxy₂, hcore2, hY2_pos, hY2_card, hall_u2', hall_w1, hall_w2, hall_w3⟩
  have hdu1 : 4 ≤ G.degree u₁ := (isT3_structure hm hpq25 hu1).1
  have hdu2 : 4 ≤ G.degree u₂ := (isT3_structure hm hpq25 hu2).1
  -- 提取 `u₁` 异于 `u₂` 的好邻点 `y₁`，与 `u₂` 异于 `u₁` 的好邻点 `y₂`
  have hu2_core1 : u₂ ∈ coreNbrs G u₁ := mem_coreNbrs.mpr ⟨hadj, by omega⟩
  rw [hcore1] at hu2_core1; simp only [Finset.mem_insert, Finset.mem_singleton] at hu2_core1
  have hex_y1 : ∃ y₁, y₁ ∈ goodNbrs G u₁ ∧ y₁ ≠ u₂ ∧
      ∀ r, G.Adj u₁ r → r = v₁ ∨ r = u₂ ∨ r = y₁ ∨ r ∈ leafNbrs G u₁ := by
    rcases hu2_core1 with h | h | h
    · exact False.elim (by rw [h] at hdu2; omega)
    · exact ⟨y₁', hy₁', h ▸ hxy₁.symm, fun r hr => by rw [h]; exact hall_u1' r hr⟩
    · exact ⟨x₁, hx₁, h ▸ hxy₁, fun r hr => by
        rcases hall_u1' r hr with h1 | h2 | h3 | h4
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inl (h3.trans h.symm))
        · exact Or.inr (Or.inr (Or.inr h4))⟩
  rcases hex_y1 with ⟨y₁, hy₁, hy1u2, hu1_all⟩
  have hu1_core2 : u₁ ∈ coreNbrs G u₂ := mem_coreNbrs.mpr ⟨hadj.symm, by omega⟩
  rw [hcore2] at hu1_core2; simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_core2
  have hex_y2 : ∃ y₂, y₂ ∈ goodNbrs G u₂ ∧ y₂ ≠ u₁ ∧
      ∀ r, G.Adj u₂ r → r = w₁ ∨ r = u₁ ∨ r = y₂ ∨ r ∈ leafNbrs G u₂ := by
    rcases hu1_core2 with h | h | h
    · exact False.elim (by rw [h] at hdu1; omega)
    · exact ⟨y₂', hy₂', h ▸ hxy₂.symm, fun r hr => by rw [h]; exact hall_u2' r hr⟩
    · exact ⟨x₂, hx₂, h ▸ hxy₂, fun r hr => by
        rcases hall_u2' r hr with h1 | h2 | h3 | h4
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inl (h3.trans h.symm))
        · exact Or.inr (Or.inr (Or.inr h4))⟩
  rcases hex_y2 with ⟨y₂, hy₂, hy2u1, hu2_all⟩
  have hu1y1 : G.Adj u₁ y₁ := (mem_goodNbrs.mp hy₁).1
  have hu2y2 : G.Adj u₂ y₂ := (mem_goodNbrs.mp hy₂).1
  have hdy1 : 3 ≤ G.degree y₁ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy₁).2
  have hdy2 : 3 ≤ G.degree y₂ := deg_ge_three_of_isGood (mem_goodNbrs.mp hy₂).2
  let Y₁ := leafNbrs G u₁
  let Y₂ := leafNbrs G u₂
  have hY_disj : Disjoint Y₁ Y₂ := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    have h1 := mem_leafNbrs.mp hr1; have h2 := mem_leafNbrs.mp hr2
    rcases exists_unique_neighbor_of_deg_one h1.2 with ⟨t, _, huniq⟩
    exact hu12 ((huniq u₁ h1.1.symm).trans (huniq u₂ h2.1.symm).symm)
  have hLu1 : (L u₁).card = G.degree u₁ + 1 := by
    rw [hm.list_card u₁]; simp [kappa, (show G.degree u₁ ≠ 2 by omega)]
  have hLu2 : (L u₂).card = G.degree u₂ + 1 := by
    rw [hm.list_card u₂]; simp [kappa, (show G.degree u₂ ≠ 2 by omega)]
  have hLv1 : (L v₁).card = 4 := by rw [hm.list_card v₁]; simp [kappa, hdv₁]
  have hLv2 : (L v₂).card = 4 := by rw [hm.list_card v₂]; simp [kappa, hdv₂]
  have hLv3 : (L v₃).card = 4 := by rw [hm.list_card v₃]; simp [kappa, hdv₃]
  have hY1_L2 : ∀ r ∈ Y₁, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  have hY2_L2 : ∀ r ∈ Y₂, (L r).card = 2 := fun r hr => by
    rw [hm.list_card r]; simp [kappa, (mem_leafNbrs.mp hr).2]
  -- 分两种几何情形：`z₁ = u₂`（共享同一条 `3`-线串）与 `z₁ ≠ u₂`（两条 `3`-线串完全不交）！
  by_cases hshared : z₁ = u₂
  · -- 情形 A：`z₁ = u₂`，即 `u₁ - v₁ - v₂ - v₃ - u₂` 是共用 `3`-线串！
    subst z₁
    have hw1_eq_v3 : w₁ = v₃ := by
      have hv3_mem : v₃ ∈ threeThreadNbrs G u₂ := by
        rw [mem_threeThreadNbrs]
        exact ⟨hv3z1.symm, hdv₃, v₂, v₁, u₁, hv23.symm, hzv2.symm, hdv₂, hv12.symm, hv31.symm,
          hdv₁, huv₁.symm, hv2u1.symm, by omega⟩
      have hw1_mem : w₁ ∈ threeThreadNbrs G u₂ := by
        rw [mem_threeThreadNbrs]
        exact ⟨huw₁, hdw₁, w₂, w₃, z₂, hw12, hw2u2, hdw₂, hw23, hw31, hdw₃, hw3z2, hzw2, by omega⟩
      have hcard1 := (isT3_structure hm hpq25 hu2).2.1
      exact Finset.card_le_one.mp (by rw [hcard1]) w₁ hw1_mem v₃ hv3_mem
    let S : Finset V := insert u₁ (insert u₂ (insert v₁ (insert v₂ (insert v₃ (Y₁ ∪ Y₂)))))
    have hu1S : u₁ ∈ S := Finset.mem_insert_self u₁ _
    have hv3u1 : v₃ ≠ u₁ := fun h => by subst h; omega
    have hv1u2 : v₁ ≠ u₂ := fun h => by subst h; omega
    have hv2u2 : v₂ ≠ u₂ := fun h => by subst h; omega
    have hy1_not_S : y₁ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨(G.ne_of_adj hu1y1).symm, hy1u2, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hy2_not_S : y₂ ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨hy2u1, (G.ne_of_adj hu2y2).symm, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega, fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r → (r = u₁ ∧ s = y₁) ∨ (r = u₂ ∧ s = y₂) := by
      intro s hsS r hrS hsr
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | hrY1 | hrY2
      · rcases hu1_all s hsr.symm with rfl | rfl | rfl | hsY
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hsS (by
            simp only [S, Y₁, Finset.mem_insert, Finset.mem_union]
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsY)))))))
      · rcases hu2_all s hsr.symm with hw | rfl | rfl | hsY
        · rw [hw1_eq_v3] at hw; exact False.elim (hsS (by rw [hw]; simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hsS (by
            simp only [S, Y₂, Finset.mem_insert, Finset.mem_union]
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsY)))))))
      · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v3 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · have hrL := mem_leafNbrs.mp hrY1
        rcases exists_unique_neighbor_of_deg_one hrL.2 with ⟨t, _, huniq⟩
        have hsu : s = u₁ := (huniq s hsr.symm).trans (huniq u₁ hrL.1.symm).symm
        exact False.elim (hsS (hsu ▸ hu1S))
      · have hrL := mem_leafNbrs.mp hrY2
        rcases exists_unique_neighbor_of_deg_one hrL.2 with ⟨t, _, huniq⟩
        have hsu : s = u₂ := (huniq s hsr.symm).trans (huniq u₂ hrL.1.symm).symm
        exact False.elim (hsS (by rw [hsu]; simp [S]))
    have hnoniso : ∀ s ∉ S, 3 ≤ G.degree s → ∃ r ∉ S, G.Adj s r := by
      intro s hsS hds3; by_contra hiso; push Not at hiso
      have hsub : G.neighborFinset s ⊆ {u₁, u₂} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hiso r h hr
        rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      have h1 := Finset.card_le_card hsub; rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 := Finset.card_le_two (a := u₁) (b := u₂); omega
    rcases exists_admissible_coloring hm ⟨u₁, hu1S⟩ with ⟨adm⟩
    let C₁ : Finset ℕ := L u₁ \ {adm.φ y₁, adm.φs y₁}
    let C₂ : Finset ℕ := L u₂ \ {adm.φ y₂, adm.φs y₂}
    have hC1 : Y₁.card + 2 ≤ C₁.card := by
      dsimp only [C₁, Y₁]; have := card_sdiff_ge (L u₁) {adm.φ y₁, adm.φs y₁}
      have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φs y₁); omega
    have hC2 : Y₂.card + 2 ≤ C₂.card := by
      dsimp only [C₂, Y₂]; have := card_sdiff_ge (L u₂) {adm.φ y₂, adm.φs y₂}
      have := Finset.card_le_two (a := adm.φ y₂) (b := adm.φs y₂); omega
    -- 通用冲突闭合器：只要找到满足条件的 `(α₁, α₂, c₁, c₂, c₃, aY₁, aY₂, γ₁, γ₂)` 即导出矛盾！
    have hfinish : ∀ (α₁ α₂ c₁ c₂ c₃ : ℕ) (aY₁ aY₂ : V → ℕ),
        α₁ ∈ C₁ → α₂ ∈ C₂ → α₁ ≠ α₂ →
        c₁ ∈ L v₁ → c₁ ≠ α₁ → c₂ ∈ L v₂ → c₂ ≠ α₁ → c₂ ≠ c₁ → c₂ ≠ c₃ → c₂ ≠ α₂ →
        c₃ ∈ L v₃ → c₃ ≠ α₂ → c₃ ≠ c₁ →
        (∀ r ∈ Y₁, aY₁ r ∈ L r ∧ aY₁ r ≠ α₁) →
        (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) →
        (∃ γ₁, (Y₁.filter (fun r => aY₁ r = γ₁)).card +
          ([c₁, adm.φ y₁, α₂] : List ℕ).count γ₁ = 1) →
        (∃ γ₂, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
          ([c₃, adm.φ y₂, α₁] : List ℕ).count γ₂ = 1) → False := by
      intro α₁ α₂ c₁ c₂ c₃ aY₁ aY₂ hα1C hα2C h12 hc1L hc1α1 hc2L hc2α1 hc21 hc23 hc2α2
        hc3L hc3α2 hc31 haY1 haY2 ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
      simp only [C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1C
      simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
      have hv1u1 : v₁ ≠ u₁ := (G.ne_of_adj huv₁).symm
      have hv21 : v₂ ≠ v₁ := (G.ne_of_adj hv12).symm
      have hv32 : v₃ ≠ v₂ := (G.ne_of_adj hv23).symm
      let ψ : V → ℕ := fun r =>
        if r = u₁ then α₁ else if r = u₂ then α₂ else if r = v₁ then c₁
        else if r = v₂ then c₂ else if r = v₃ then c₃
        else if r ∈ Y₁ then aY₁ r else if r ∈ Y₂ then aY₂ r else adm.φ r
      have hψu1 : ψ u₁ = α₁ := by simp [ψ]
      have hψu2 : ψ u₂ = α₂ := by simp [ψ, hu12.symm]
      have hψv1 : ψ v₁ = c₁ := by simp [ψ, hv1u1, hv1u2]
      have hψv2 : ψ v₂ = c₂ := by simp [ψ, hv2u1, hv2u2, hv21]
      have hψv3 : ψ v₃ = c₃ := by simp [ψ, hv3u1, (G.ne_of_adj hv3z1), hv31, hv32]
      have hψY1 : ∀ r ∈ Y₁, ψ r = aY₁ r := by
        intro r hr
        have h1 : r ≠ u₁ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h2 : r ≠ u₂ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h3 : r ≠ v₁ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h4 : r ≠ v₂ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h5 : r ≠ v₃ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        simp [ψ, h1, h2, h3, h4, h5, hr]
      have hψY2 : ∀ r ∈ Y₂, ψ r = aY₂ r := by
        intro r hr
        have h1 : r ≠ u₁ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h2 : r ≠ u₂ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h3 : r ≠ v₁ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h4 : r ≠ v₂ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h5 : r ≠ v₃ := fun h => by subst h; rw [mem_leafNbrs] at hr; omega
        have h6 : r ∉ Y₁ := fun h => Finset.disjoint_left.mp hY_disj h hr
        simp [ψ, h1, h2, h3, h4, h5, h6, hr]
      have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
        intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
        simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
      apply adm.contradiction hm ψ hψ_out
      · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | hr1 | hr2
        · rw [hψu1]; exact hα1C.1
        · rw [hψu2]; exact hα2C.1
        · rw [hψv1]; exact hc1L
        · rw [hψv2]; exact hc2L
        · rw [hψv3]; exact hc3L
        · rw [hψY1 r hr1]; exact (haY1 r hr1).1
        · rw [hψY2 r hr2]; exact (haY2 r hr2).1
      · intro r₁ r₂ hradj hor
        have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
          intro a' b' hab ha'
          simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
          rcases ha' with ha | ha | ha | ha | ha | ha1 | ha2
          · subst a'
            rcases hu1_all b' hab with hb | hb | hb | hbY
            · rw [hb, hψu1, hψv1]; exact Ne.symm hc1α1
            · rw [hb, hψu1, hψu2]; exact h12
            · rw [hb, hψu1, hψ_out y₁ hy1_not_S]; exact hα1C.2.1
            · rw [hψu1, hψY1 b' hbY]; exact (haY1 b' hbY).2.symm
          · subst a'
            rcases hu2_all b' hab with hb | hb | hb | hbY
            · rw [hw1_eq_v3] at hb; rw [hb, hψu2, hψv3]; exact Ne.symm hc3α2
            · rw [hb, hψu2, hψu1]; exact h12.symm
            · rw [hb, hψu2, hψ_out y₂ hy2_not_S]; exact hα2C.2.1
            · rw [hψu2, hψY2 b' hbY]; exact (haY2 b' hbY).2.symm
          · subst a'
            rcases hall_v1 b' hab with hb | hb
            · rw [hb, hψv1, hψu1]; exact hc1α1
            · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
          · subst a'
            rcases hall_v2 b' hab with hb | hb
            · rw [hb, hψv2, hψv1]; exact hc21
            · rw [hb, hψv2, hψv3]; exact hc23
          · subst a'
            rcases hall_v3 b' hab with hb | hb
            · rw [hb, hψv3, hψv2]; exact Ne.symm hc23
            · rw [hb, hψv3, hψu2]; exact hc3α2
          · have haL := mem_leafNbrs.mp ha1
            rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
            have hbu : b' = u₁ := (huniq b' hab).trans (huniq u₁ haL.1.symm).symm
            rw [hbu, hψY1 a' ha1, hψu1]; exact (haY1 a' ha1).2
          · have haL := mem_leafNbrs.mp ha2
            rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
            have hbu : b' = u₂ := (huniq b' hab).trans (huniq u₂ haL.1.symm).symm
            rw [hbu, hψY2 a' ha2, hψu2]; exact (haY2 a' ha2).2
        rcases hor with h1 | h2
        · exact hcase r₁ r₂ hradj h1
        · exact (hcase r₂ r₁ hradj.symm h2).symm
      · intro s hsS _ r hrS hsr
        rcases hS_out s hsS r hrS hsr with ⟨hr, hs⟩ | ⟨hr, hs⟩
        · rw [hr, hs, hψu1]; exact hα1C.2.2
        · rw [hr, hs, hψu2]; exact hα2C.2.2
      · intro s hsS hiso ⟨r, hsr⟩
        have hrS : r ∈ S := by by_contra h; exact hiso r h hsr
        rcases hS_out s hsS r hrS hsr with ⟨_, hs⟩ | ⟨_, hs⟩
        · rcases hnoniso y₁ hy1_not_S hdy1 with ⟨w, hwS, hyw⟩
          exact False.elim (hiso w hwS (hs ▸ hyw))
        · rcases hnoniso y₂ hy2_not_S hdy2 with ⟨w, hwS, hyw⟩
          exact False.elim (hiso w hwS (hs ▸ hyw))
      · intro r hrS _
        simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
        rcases hrS with hr | hr | hr | hr | hr | hr1 | hr2
        · subst r
          exact pcf_from_leaf_and_three huv₁ hu1y1 hadj (fun h => by subst h; omega)
            hv1u2 hy1u2 (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun t ht => (mem_leafNbrs.mp ht).1) hψY1
            (fun t ht => by
              rcases hu1_all t ht with h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr h)))
            (by rw [hψv1, hψ_out y₁ hy1_not_S, hψu2]; exact hγ₁)
        · subst r
          exact pcf_from_leaf_and_three hv3z1.symm hu2y2 hadj.symm (fun h => by subst h; omega)
            hv3u1 hy2u1 (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun h => by rw [mem_leafNbrs] at h; omega)
            (fun t ht => (mem_leafNbrs.mp ht).1) hψY2
            (fun t ht => by
              rcases hu2_all t ht with h | h | h | h
              · exact Or.inl (hw1_eq_v3 ▸ h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr h)))
            (by rw [hψv3, hψ_out y₂ hy2_not_S, hψu1]; exact hγ₂)
        · subst r
          exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
            (by rw [hψu1, hψv2]; exact Ne.symm hc2α1)
        · subst r
          exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
            (by rw [hψv1, hψv3]; exact Ne.symm hc31)
        · subst r
          exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
            (by rw [hψv2, hψu2]; exact hc2α2)
        · exact pcf_at_deg_one (mem_leafNbrs.mp hr1).2 (mem_leafNbrs.mp hr1).1.symm
        · exact pcf_at_deg_one (mem_leafNbrs.mp hr2).2 (mem_leafNbrs.mp hr2).1.symm
    -- 四行绝杀：先在 `u₂` 取 `(α₂, aY₂)` 避开 `adm.φ y₂`！
    rcases exists_color_leaves_avoid (L := L) (Y := Y₂) (C := C₂) (β := adm.φ y₂)
      hY2_L2 (by omega) with ⟨α₂, hα2C, haY2_ex⟩
    choose aY₂ haY2_spec using haY2_ex
    let aY₂' : V → ℕ := fun r => if hr : r ∈ Y₂ then aY₂ r hr else 0
    have haY2' : ∀ r ∈ Y₂, aY₂' r ∈ L r ∧ aY₂' r ≠ α₂ ∧ aY₂' r ≠ adm.φ y₂ := fun r hr => by
      simp only [aY₂', hr, dite_true]; exact haY2_spec r hr
    let Z₃ : Finset ℕ := L v₃ \ {α₂, adm.φ y₂}
    have hZ3 : 2 ≤ Z₃.card := by
      dsimp only [Z₃]; have := card_sdiff_ge (L v₃) {α₂, adm.φ y₂}
      have := Finset.card_le_two (a := α₂) (b := adm.φ y₂); omega
    let C₁' : Finset ℕ := C₁ \ {α₂, adm.φ y₂}
    by_cases hC1' : Y₁.card + 1 ≤ C₁'.card
    · rcases t3_fixed_color_extension (L := L) (Y := Y₁) (L₁ := L v₁) (L₂ := L v₂) (Z₃ := Z₃)
        (C_u := C₁') (φy := adm.φ y₁) (φz := α₂) (δ := α₂)
        hY1_pos hY1_L2 hLv1 hLv2 hZ3 hC1' with ⟨α₁, hα1', c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
      simp only [C₁', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1'
      rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁
      rcases hc₁ with ⟨⟨hc1L, hc1α1⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
      simp only [Z₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2B
      have hγ₂ : (Y₂.filter (fun r => aY₂' r = adm.φ y₂)).card +
          ([c₃, adm.φ y₂, α₁] : List ℕ).count (adm.φ y₂) = 1 := by
        have hzero : (Y₂.filter (fun r => aY₂' r = adm.φ y₂)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          exact fun r hr => (haY2' r hr).2.2
        rw [hzero, zero_add]
        simp only [List.count_cons, List.count_nil, beq_iff_eq, hc3Z.2.2, hα1'.2.2,
          ite_true, ite_false]
      exact hfinish α₁ α₂ c₁ c₂ c₃ aY₁ aY₂' hα1'.1 hα2C hα1'.2.1 hc1L hc1α1 hc2B.1 hc2B.2.1 hc21
        hc2B.2.2.1 hc2B.2.2.2 hc3Z.1 hc3Z.2.1 hc31 haY₁
        (fun r hr => ⟨(haY2' r hr).1, (haY2' r hr).2.1⟩) ⟨γ₁, hγ₁⟩ ⟨adm.φ y₂, hγ₂⟩
    · -- `|C₁'| = Y₁.card`：故 `adm.φ y₂ ∈ C₁` 且 `C₁'` 大小恰为 `Y₁.card`！
      have hC1'_ge : Y₁.card ≤ C₁'.card := by
        dsimp only [C₁']; have := card_sdiff_ge C₁ {α₂, adm.φ y₂}
        have := Finset.card_le_two (a := α₂) (b := adm.φ y₂); omega
      have hφy2_C1 : adm.φ y₂ ∈ C₁ := by
        by_contra hnot
        have hEq : C₁' = C₁ \ {α₂} := by
          ext t; simp only [C₁', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun ⟨ht, h1, _⟩ => ⟨ht, h1⟩, fun ⟨ht, h1⟩ => ⟨ht, h1, fun h => hnot (h ▸ ht)⟩⟩
        have := card_sdiff_ge C₁ {α₂}; simp only [Finset.card_singleton] at this
        rw [hEq] at hC1'; omega
      by_cases hex_leaf : ∃ r₀ ∈ Y₁, L r₀ = {adm.φ y₂, adm.φ y₁}
      · -- 子情形 2b：存在 `r₀ ∈ Y₁` 满足 `L r₀ = {adm.φ y₂, adm.φ y₁}` → `Disjoint (L r₀) C₁'`！
        rcases hex_leaf with ⟨r₀, hr0, hLr0⟩
        have hdisj : Disjoint (L r₀) C₁' := by
          rw [Finset.disjoint_left]; intro t ht1 ht2
          rw [hLr0, Finset.mem_insert, Finset.mem_singleton] at ht1
          simp only [C₁', C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
            not_or] at ht2
          rcases ht1 with rfl | rfl
          · exact ht2.2.2 rfl
          · exact ht2.1.2.1 rfl
        rcases t3_fixed_color_extension_disj_leaf (L := L) (Y := Y₁) (L₁ := L v₁) (L₂ := L v₂)
          (Z₃ := Z₃) (C_u := C₁') (φy := adm.φ y₁) (φz := α₂) (δ := α₂)
          hr0 hdisj hY1_L2 hLv1 hLv2 hZ3 hC1'_ge with ⟨α₁, hα1', c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
        simp only [C₁', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1'
        rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁
        rcases hc₁ with ⟨⟨hc1L, hc1α1⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
        simp only [Z₃, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2B
        have hγ₂ : (Y₂.filter (fun r => aY₂' r = adm.φ y₂)).card +
            ([c₃, adm.φ y₂, α₁] : List ℕ).count (adm.φ y₂) = 1 := by
          have hzero : (Y₂.filter (fun r => aY₂' r = adm.φ y₂)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            exact fun r hr => (haY2' r hr).2.2
          rw [hzero, zero_add]
          simp only [List.count_cons, List.count_nil, beq_iff_eq, hc3Z.2.2, hα1'.2.2,
            ite_true, ite_false]
        exact hfinish α₁ α₂ c₁ c₂ c₃ aY₁ aY₂' hα1'.1 hα2C hα1'.2.1 hc1L hc1α1 hc2B.1 hc2B.2.1 hc21
          hc2B.2.2.1 hc2B.2.2.2 hc3Z.1 hc3Z.2.1 hc31 haY₁
          (fun r hr => ⟨(haY2' r hr).1, (haY2' r hr).2.1⟩) ⟨γ₁, hγ₁⟩ ⟨adm.φ y₂, hγ₂⟩
      · -- 子情形 2a：在 `u₁` 取 `α₁ = adm.φ y₂ ∉ C₂` 且 `Y₁` 避开 `adm.φ y₁`，反向延拓 `u₂`！
        push Not at hex_leaf
        have haY1_ex : ∀ r ∈ Y₁, ∃ a ∈ L r, a ≠ adm.φ y₂ ∧ a ≠ adm.φ y₁ := by
          intro r hr
          have hsub : ¬ L r ⊆ {adm.φ y₂, adm.φ y₁} := by
            intro hs
            have := Finset.card_le_two (a := adm.φ y₂) (b := adm.φ y₁)
            have := hY1_L2 r hr
            exact hex_leaf r hr (Finset.eq_of_subset_of_card_le hs (by omega))
          rw [Finset.not_subset] at hsub
          rcases hsub with ⟨a, haL, hanot⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hanot
          exact ⟨a, haL, hanot.1, hanot.2⟩
        choose aY₁ haY1_spec using haY1_ex
        let aY₁' : V → ℕ := fun r => if hr : r ∈ Y₁ then aY₁ r hr else 0
        have haY1' : ∀ r ∈ Y₁, aY₁' r ∈ L r ∧ aY₁' r ≠ adm.φ y₂ ∧ aY₁' r ≠ adm.φ y₁ := by
          intro r hr; simp only [aY₁', hr, dite_true]; exact haY1_spec r hr
        let Z₁ : Finset ℕ := L v₁ \ {adm.φ y₂, adm.φ y₁}
        have hZ1 : 2 ≤ Z₁.card := by
          dsimp only [Z₁]; have := card_sdiff_ge (L v₁) {adm.φ y₂, adm.φ y₁}
          have := Finset.card_le_two (a := adm.φ y₂) (b := adm.φ y₁); omega
        let C₂' : Finset ℕ := C₂ \ {adm.φ y₁}
        have hC2' : Y₂.card + 1 ≤ C₂'.card := by
          dsimp only [C₂']; have := card_sdiff_ge C₂ {adm.φ y₁}
          simp only [Finset.card_singleton] at this; omega
        rcases t3_fixed_color_extension (L := L) (Y := Y₂) (L₁ := L v₃) (L₂ := L v₂) (Z₃ := Z₁)
          (C_u := C₂') (φy := adm.φ y₂) (φz := adm.φ y₂) (δ := adm.φ y₂)
          hY2_pos hY2_L2 hLv3 hLv2 hZ1 hC2' with ⟨α₂', hα2', c₃, hc₃, aY₂_rev, haY₂_rev, γ₂, hγ₂⟩
        simp only [C₂', Finset.mem_sdiff, Finset.mem_singleton] at hα2'
        rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₃
        rcases hc₃ with ⟨⟨hc3L, hc3α2⟩, c₁, hc1Z, hc13, c₂, hc2B, hc23⟩
        simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc1Z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2B
        have h12_ne : adm.φ y₂ ≠ α₂' := by
          have hmem := hα2'.1
          simp only [C₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
          exact Ne.symm hmem.2.1
        have hγ₁ : (Y₁.filter (fun r => aY₁' r = adm.φ y₁)).card +
            ([c₁, adm.φ y₁, α₂'] : List ℕ).count (adm.φ y₁) = 1 := by
          have hzero : (Y₁.filter (fun r => aY₁' r = adm.φ y₁)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            exact fun r hr => (haY1' r hr).2.2
          rw [hzero, zero_add]
          simp only [List.count_cons, List.count_nil, beq_iff_eq, hc1Z.2.2, hα2'.2,
            ite_true, ite_false]
        exact hfinish (adm.φ y₂) α₂' c₁ c₂ c₃ aY₁' aY₂_rev hφy2_C1 hα2'.1 h12_ne hc1Z.1 hc1Z.2.1
          hc2B.1 hc2B.2.2.2 hc2B.2.2.1 hc23 hc2B.2.1 hc3L hc3α2 (Ne.symm hc13)
          (fun r hr => ⟨(haY1' r hr).1, (haY1' r hr).2.1⟩) haY₂_rev ⟨adm.φ y₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
  · -- 情形 B：`z₁ ≠ u₂`（两条 `3`-线串完全不交！）
    have hz2u1 : z₂ ≠ u₁ := by
      intro h; subst z₂
      have hw3_mem : w₃ ∈ threeThreadNbrs G u₁ := by
        rw [mem_threeThreadNbrs]
        exact ⟨hw3z2.symm, hdw₃, w₂, w₁, u₂, hw23.symm, hzw2.symm, hdw₂, hw12.symm, hw31.symm,
          hdw₁, huw₁.symm, hw2u2.symm, by omega⟩
      have hv1_mem : v₁ ∈ threeThreadNbrs G u₁ := by
        rw [mem_threeThreadNbrs]
        exact ⟨huv₁, hdv₁, v₂, v₃, z₁, hv12, hv2u1, hdv₂, hv23, hv31, hdv₃, hv3z1, hzv2, by omega⟩
      have hcard1 := (isT3_structure hm hpq25 hu1).2.1
      have hw3_eq : w₃ = v₁ := Finset.card_le_one.mp (by rw [hcard1]) w₃ hw3_mem v₁ hv1_mem
      have ha_v := (threeThread_anchors_eq hm (by omega) (by omega) hz1u1.symm
        hdv₁ hdv₂ hdv₃ huv₁ hv12 hv2u1 hv23 hv31 hv3z1 hzv2).1
      have ha_w := (threeThread_anchors_eq hm (by omega) (by omega) hz2u2.symm
        hdw₁ hdw₂ hdw₃ huw₁ hw12 hw2u2 hw23 hw31 hw3z2 hzw2).2.2
      rw [hw3_eq] at ha_w
      have hpair : ({u₁, z₁} : Finset V) = {u₂, u₁} := ha_v.symm.trans ha_w
      have hz_in : z₁ ∈ ({u₂, u₁} : Finset V) := by rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz_in
      exact hz_in.elim hshared hz1u1
    have ha_v := threeThread_anchors_eq hm (by omega) (by omega) hz1u1.symm
      hdv₁ hdv₂ hdv₃ huv₁ hv12 hv2u1 hv23 hv31 hv3z1 hzv2
    have ha_w := threeThread_anchors_eq hm (by omega) (by omega) hz2u2.symm
      hdw₁ hdw₂ hdw₃ huw₁ hw12 hw2u2 hw23 hw31 hw3z2 hzw2
    have hvw_disj : Disjoint ({v₁, v₂, v₃} : Finset V) {w₁, w₂, w₃} := by
      rw [Finset.disjoint_left]; intro r hr1 hr2
      have h1 : threadAnchors G r = {u₁, z₁} := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr1
        rcases hr1 with rfl | rfl | rfl
        · exact ha_v.1
        · exact ha_v.2.1
        · exact ha_v.2.2
      have h2 : threadAnchors G r = {u₂, z₂} := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr2
        rcases hr2 with rfl | rfl | rfl
        · exact ha_w.1
        · exact ha_w.2.1
        · exact ha_w.2.2
      have hpair : ({u₁, z₁} : Finset V) = {u₂, z₂} := h1.symm.trans h2
      have hu2_in : u₂ ∈ ({u₁, z₁} : Finset V) := by rw [hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu2_in
      exact hu2_in.elim hu12.symm (fun h => hshared h.symm)
    let S : Finset V :=
      insert u₁ (insert u₂ (insert v₁ (insert v₂ (insert v₃
        (insert w₁ (insert w₂ (insert w₃ (Y₁ ∪ Y₂))))))))
    have hu1S : u₁ ∈ S := Finset.mem_insert_self u₁ _
    have hnot_S_of_ge3 : ∀ s : V, 3 ≤ G.degree s → s ≠ u₁ → s ≠ u₂ → s ∉ S := by
      intro s hds hs1 hs2
      simp only [S, Finset.mem_insert, Finset.mem_union, not_or]
      refine ⟨hs1, hs2, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by rw [mem_leafNbrs] at h; omega,
        fun h => by rw [mem_leafNbrs] at h; omega⟩
    have hy1_not_S : y₁ ∉ S := hnot_S_of_ge3 y₁ hdy1 (G.ne_of_adj hu1y1).symm hy1u2
    have hy2_not_S : y₂ ∉ S := hnot_S_of_ge3 y₂ hdy2 hy2u1 (G.ne_of_adj hu2y2).symm
    have hz1_not_S : z₁ ∉ S := hnot_S_of_ge3 z₁ (by omega) hz1u1 hshared
    have hz2_not_S : z₂ ∉ S := hnot_S_of_ge3 z₂ (by omega) hz2u1 hz2u2
    have hS_out : ∀ s ∉ S, ∀ r ∈ S, G.Adj s r →
        (r = u₁ ∧ s = y₁) ∨ (r = u₂ ∧ s = y₂) ∨ (r = v₃ ∧ s = z₁) ∨ (r = w₃ ∧ s = z₂) := by
      have hY1_subS : Y₁ ⊆ S := fun t ht => by
        simp only [S, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))))))
      have hY2_subS : Y₂ ⊆ S := fun t ht => by
        simp only [S, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))))))
      intro s hsS r hrS hsr
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hr1 | hr2
      · rcases hu1_all s hsr.symm with rfl | rfl | rfl | hsY
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inl ⟨rfl, rfl⟩
        · exact False.elim (hsS (hY1_subS hsY))
      · rcases hu2_all s hsr.symm with rfl | rfl | rfl | hsY
        · exact False.elim (hsS (by simp [S]))
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact False.elim (hsS (hY2_subS hsY))
      · rcases hall_v1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_v3 s hsr.symm with rfl | rfl
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · rcases hall_w1 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_w2 s hsr.symm with rfl | rfl <;> exact False.elim (hsS (by simp [S]))
      · rcases hall_w3 s hsr.symm with rfl | rfl
        · exact False.elim (hsS (by simp [S]))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · have hrL := mem_leafNbrs.mp hr1
        rcases exists_unique_neighbor_of_deg_one hrL.2 with ⟨t, _, huniq⟩
        have hsu : s = u₁ := (huniq s hsr.symm).trans (huniq u₁ hrL.1.symm).symm
        exact False.elim (hsS (hsu ▸ hu1S))
      · have hrL := mem_leafNbrs.mp hr2
        rcases exists_unique_neighbor_of_deg_one hrL.2 with ⟨t, _, huniq⟩
        have hsu : s = u₂ := (huniq s hsr.symm).trans (huniq u₂ hrL.1.symm).symm
        exact False.elim (hsS (by rw [hsu]; simp [S]))
    -- 孤立点检查：任何孤立点 `s ∉ S` 必有 `d(s) = 4` 且吸收全部 4 条割边 → 9 个核心点度数和 22，与 `9p ≤ 22q` 矛盾！
    have hnoniso : ∀ s ∉ S, (∃ r ∈ S, G.Adj s r) → ∃ r ∉ S, G.Adj s r := by
      intro s hsS ⟨r₀, hr0S, hsr0⟩
      by_contra hiso; push Not at hiso
      have hds3 : 3 ≤ G.degree s := by
        rcases hS_out s hsS r₀ hr0S hsr0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      have hsub : G.neighborFinset s ⊆ {u₁, u₂, v₃, w₃} := by
        intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
        have hrS : r ∈ S := by by_contra h; exact hiso r h hr
        rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      -- 若 `s` 不邻接 `v₃` 且不邻接 `w₃`，则 `N(s) ⊆ {u₁, u₂}` 矛盾 `3 ≤ d(s)`！
      have hds4 : 4 ≤ G.degree s := by
        by_cases h1 : G.Adj s v₃
        · rcases hS_out s hsS v₃ (by simp [S]) h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact False.elim (by rw [h] at hdv₃; omega)
          · exact hdz1
          · exact False.elim
              (Finset.disjoint_left.mp hvw_disj (show v₃ ∈ ({v₁, v₂, v₃} : Finset V) by simp)
                (by rw [h]; simp))
        · by_cases h2 : G.Adj s w₃
          · rcases hS_out s hsS w₃ (by simp [S]) h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
            · exact False.elim (by rw [h] at hdw₃; omega)
            · exact False.elim (by rw [h] at hdw₃; omega)
            · exact False.elim
                (Finset.disjoint_left.mp hvw_disj (by rw [h]; simp)
                  (show w₃ ∈ ({w₁, w₂, w₃} : Finset V) by simp))
            · exact hdz2
          · have hsub2 : G.neighborFinset s ⊆ {u₁, u₂} := by
              intro r hr; rw [SimpleGraph.mem_neighborFinset] at hr
              have hrS : r ∈ S := by by_contra h; exact hiso r h hr
              rcases hS_out s hsS r hrS hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
              · simp
              · simp
              · exact False.elim (h1 hr)
              · exact False.elim (h2 hr)
            have hc := Finset.card_le_card hsub2
            rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
            have := Finset.card_le_two (a := u₁) (b := u₂); omega
      have h4_le : ({u₁, u₂, v₃, w₃} : Finset V).card ≤ 4 := card_quad_le u₁ u₂ v₃ w₃
      have hcard_eq : G.neighborFinset s = {u₁, u₂, v₃, w₃} :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
      have hds_eq4 : G.degree s = 4 := by
        have hc := congrArg Finset.card hcard_eq
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hc; omega
      -- 于是 `s = y₁ = y₂ = z₁ = z₂`，从而 `insert s S = Finset.univ`！
      have hs_y1 : s = y₁ := by
        have had : G.Adj s u₁ := (G.mem_neighborFinset s u₁).mp (by rw [hcard_eq]; simp)
        rcases hS_out s hsS u₁ hu1S had with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact False.elim (hu12 h)
        · exact False.elim (by rw [h] at hdu1; omega)
        · exact False.elim (by rw [h] at hdu1; omega)
      have hs_y2 : s = y₂ := by
        have had : G.Adj s u₂ := (G.mem_neighborFinset s u₂).mp (by rw [hcard_eq]; simp)
        rcases hS_out s hsS u₂ (by simp [S]) had with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact False.elim (hu12 h.symm)
        · exact h
        · exact False.elim (by rw [h] at hdu2; omega)
        · exact False.elim (by rw [h] at hdu2; omega)
      have hs_z1 : s = z₁ := by
        have had : G.Adj s v₃ := (G.mem_neighborFinset s v₃).mp (by rw [hcard_eq]; simp)
        rcases hS_out s hsS v₃ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
        · exact False.elim (by rw [h] at hdv₃; omega)
        · exact False.elim (by rw [h] at hdv₃; omega)
        · exact h
        · exact False.elim
            (Finset.disjoint_left.mp hvw_disj (show v₃ ∈ ({v₁, v₂, v₃} : Finset V) by simp)
              (by rw [h]; simp))
      have hs_z2 : s = z₂ := by
        have had : G.Adj s w₃ := (G.mem_neighborFinset s w₃).mp (by rw [hcard_eq]; simp)
        rcases hS_out s hsS w₃ (by simp [S]) had with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · exact False.elim (by rw [h] at hdw₃; omega)
        · exact False.elim (by rw [h] at hdw₃; omega)
        · exact False.elim
            (Finset.disjoint_left.mp hvw_disj (by rw [h]; simp)
              (show w₃ ∈ ({w₁, w₂, w₃} : Finset V) by simp))
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
            · exact Or.inl hs_y2.symm
            · exact Or.inl hs_z1.symm
            · exact Or.inl hs_z2.symm
      have hK_eq : coreVerts G = {s, u₁, u₂, v₁, v₂, v₃, w₁, w₂, w₃} := by
        ext r; simp only [mem_coreVerts, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hr2
          have hrU : r ∈ insert s S := by rw [hall_univ]; exact Finset.mem_univ r
          simp only [S, Finset.mem_insert, Finset.mem_union] at hrU
          rcases hrU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hY1 | hY2
          · simp
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
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
      have hsu1 : s ≠ u₁ := fun h => hsS (h ▸ hu1S)
      have hsu2 : s ≠ u₂ := fun h => hsS (by rw [h]; simp [S])
      have hv_ne_w : ∀ a ∈ ({v₁, v₂, v₃} : Finset V), ∀ b ∈ ({w₁, w₂, w₃} : Finset V), a ≠ b :=
        fun a ha b hb h => Finset.disjoint_left.mp hvw_disj ha (h ▸ hb)
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
            hv_ne_w v₁ (by simp) w₂ (by simp), hv_ne_w v₁ (by simp) w₃ (by simp)⟩)]
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨G.ne_of_adj hv23, hv_ne_w v₂ (by simp) w₁ (by simp),
            hv_ne_w v₂ (by simp) w₂ (by simp), hv_ne_w v₂ (by simp) w₃ (by simp)⟩)]
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hv_ne_w v₃ (by simp) w₁ (by simp), hv_ne_w v₃ (by simp) w₂ (by simp),
            hv_ne_w v₃ (by simp) w₃ (by simp)⟩)]
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨G.ne_of_adj hw12, hw31.symm⟩)]
        rw [Finset.card_pair (G.ne_of_adj hw23)]
      have hcs4 : coreDeg G s = 4 := by
        have hEq : coreNbrs G s = G.neighborFinset s := by
          ext r; simp only [mem_coreNbrs, SimpleGraph.mem_neighborFinset]
          exact ⟨And.left, fun hr => ⟨hr, by
            have : r ∈ ({u₁, u₂, v₃, w₃} : Finset V) := by
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
            hv_ne_w v₁ (by simp) w₂ (by simp), hv_ne_w v₁ (by simp) w₃ (by simp)⟩)]
        rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨G.ne_of_adj hv23, hv_ne_w v₂ (by simp) w₁ (by simp),
            hv_ne_w v₂ (by simp) w₂ (by simp), hv_ne_w v₂ (by simp) w₃ (by simp)⟩)]
        rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hv_ne_w v₃ (by simp) w₁ (by simp), hv_ne_w v₃ (by simp) w₂ (by simp),
            hv_ne_w v₃ (by simp) w₃ (by simp)⟩)]
        rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨G.ne_of_adj hw12, hw31.symm⟩)]
        rw [Finset.sum_pair (G.ne_of_adj hw23)]
        have hc_v1 : coreDeg G v₁ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₁]
        have hc_v2 : coreDeg G v₂ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₂]
        have hc_v3 : coreDeg G v₃ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdv₃]
        have hc_w1 : coreDeg G w₁ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw₁]
        have hc_w2 : coreDeg G w₂ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw₂]
        have hc_w3 : coreDeg G w₃ = 2 := by
          rw [coreDeg_eq_degree_of_deg_le_three hm (by omega), hdw₃]
        rw [hcs4, hu1.1, hu2.1, hc_v1, hc_v2, hc_v3, hc_w1, hc_w2, hc_w3]
        rfl
      exact mad_22_9_contra hm hpq hK9 hKsum (by omega)
    -- 非孤立主情形：先对每个 `α₁` 用 `t3_fixed_color_extension` 延拓 `u₂`，再对 `u₁` 用 `t3_fun_color_extension`！
    rcases exists_admissible_coloring hm ⟨u₁, hu1S⟩ with ⟨adm⟩
    have hLw1 : (L w₁).card = 4 := by rw [hm.list_card w₁]; simp [kappa, hdw₁]
    have hLw2 : (L w₂).card = 4 := by rw [hm.list_card w₂]; simp [kappa, hdw₂]
    have hLw3 : (L w₃).card = 4 := by rw [hm.list_card w₃]; simp [kappa, hdw₃]
    let Z₁ : Finset ℕ := L v₃ \ {adm.φ z₁, adm.φs z₁}
    let Z₂ : Finset ℕ := L w₃ \ {adm.φ z₂, adm.φs z₂}
    have hZ1 : 2 ≤ Z₁.card := by
      dsimp only [Z₁]; have := card_sdiff_ge (L v₃) {adm.φ z₁, adm.φs z₁}
      have := Finset.card_le_two (a := adm.φ z₁) (b := adm.φs z₁); omega
    have hZ2 : 2 ≤ Z₂.card := by
      dsimp only [Z₂]; have := card_sdiff_ge (L w₃) {adm.φ z₂, adm.φs z₂}
      have := Finset.card_le_two (a := adm.φ z₂) (b := adm.φs z₂); omega
    have hu2_ext : ∀ α₁ : ℕ, ∃ α₂ ∈ L u₂ \ {adm.φ y₂, adm.φs y₂, α₁},
        ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
        ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
        ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
          ([d₁, adm.φ y₂, α₁] : List ℕ).count γ₂ = 1 := by
      intro α₁
      have hC2 : Y₂.card + 1 ≤ (L u₂ \ {adm.φ y₂, adm.φs y₂, α₁}).card := by
        dsimp only [Y₂]; have := card_sdiff_ge (L u₂) {adm.φ y₂, adm.φs y₂, α₁}
        have := card_triple_le (adm.φ y₂) (adm.φs y₂) α₁; omega
      exact t3_fixed_color_extension hY2_pos hY2_L2 hLw1 hLw2 hZ2 hC2
    let f₂ : ℕ → ℕ := fun α₁ => (hu2_ext α₁).choose
    let C₁ : Finset ℕ := L u₁ \ {adm.φ y₁, adm.φs y₁}
    have hC1 : Y₁.card + 1 ≤ C₁.card := by
      dsimp only [C₁, Y₁]; have := card_sdiff_ge (L u₁) {adm.φ y₁, adm.φs y₁}
      have := Finset.card_le_two (a := adm.φ y₁) (b := adm.φs y₁); omega
    rcases t3_fun_color_extension (L := L) (Y := Y₁) (L₁ := L v₁) (L₂ := L v₂) (Z₃ := Z₁)
      (C_u := C₁) (φy := adm.φ y₁) (φz := adm.φ z₁) f₂ hY1_pos hY1_L2 hLv1 hLv2 hZ1 hC1 with
      ⟨α₁, hα1C, c₁, hc₁, aY₁, haY₁, γ₁, hγ₁⟩
    let α₂ : ℕ := f₂ α₁
    have hα2_spec := (hu2_ext α₁).choose_spec
    change α₂ ∈ L u₂ \ {adm.φ y₂, adm.φs y₂, α₁} ∧
        ∃ d₁ ∈ threeThreadGoodCols (L w₁) (L w₂) Z₂ (adm.φ z₂) α₂,
        ∃ aY₂ : V → ℕ, (∀ r ∈ Y₂, aY₂ r ∈ L r ∧ aY₂ r ≠ α₂) ∧
        ∃ γ₂ : ℕ, (Y₂.filter (fun r => aY₂ r = γ₂)).card +
          ([d₁, adm.φ y₂, α₁] : List ℕ).count γ₂ = 1 at hα2_spec
    rcases hα2_spec with ⟨hα2C, d₁, hd₁, aY₂, haY₂, γ₂, hγ₂⟩
    simp only [C₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα1C
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hα2C
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc₁
    rcases hc₁ with ⟨⟨hc1L, hc1α1⟩, c₃, hc3Z, hc31, c₂, hc2B, hc21⟩
    simp only [Z₁, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc3Z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc2B
    rw [threeThreadGoodCols, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hd₁
    rcases hd₁ with ⟨⟨hd1L, hd1α2⟩, d₃, hd3Z, hd31, d₂, hd2B, hd21⟩
    simp only [Z₂, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd3Z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd2B
    have hv_ne_w : ∀ a ∈ ({v₁, v₂, v₃} : Finset V), ∀ b ∈ ({w₁, w₂, w₃} : Finset V), a ≠ b :=
      fun a ha b hb h => Finset.disjoint_left.mp hvw_disj ha (h ▸ hb)
    let ψ : V → ℕ := fun r =>
      if r = u₁ then α₁ else if r = u₂ then α₂
      else if r = v₁ then c₁ else if r = v₂ then c₂ else if r = v₃ then c₃
      else if r = w₁ then d₁ else if r = w₂ then d₂ else if r = w₃ then d₃
      else if r ∈ Y₁ then aY₁ r else if r ∈ Y₂ then aY₂ r else adm.φ r
    have hψu1 : ψ u₁ = α₁ := by simp [ψ]
    have hψu2 : ψ u₂ = α₂ := by simp [ψ, hu12.symm]
    have hψv1 : ψ v₁ = c₁ := by
      simp [ψ, (G.ne_of_adj huv₁).symm, (show v₁ ≠ u₂ by intro h; subst h; omega)]
    have hψv2 : ψ v₂ = c₂ := by
      simp [ψ, hv2u1, (show v₂ ≠ u₂ by intro h; subst h; omega), (G.ne_of_adj hv12).symm]
    have hψv3 : ψ v₃ = c₃ := by
      simp [ψ, (show v₃ ≠ u₁ by intro h; subst h; omega),
        (show v₃ ≠ u₂ by intro h; subst h; omega), hv31, (G.ne_of_adj hv23).symm]
    have hψw1 : ψ w₁ = d₁ := by
      simp [ψ, (show w₁ ≠ u₁ by intro h; subst h; omega), (G.ne_of_adj huw₁).symm,
        (hv_ne_w v₁ (by simp) w₁ (by simp)).symm, (hv_ne_w v₂ (by simp) w₁ (by simp)).symm,
        (hv_ne_w v₃ (by simp) w₁ (by simp)).symm]
    have hψw2 : ψ w₂ = d₂ := by
      simp [ψ, (show w₂ ≠ u₁ by intro h; subst h; omega), hw2u2,
        (hv_ne_w v₁ (by simp) w₂ (by simp)).symm, (hv_ne_w v₂ (by simp) w₂ (by simp)).symm,
        (hv_ne_w v₃ (by simp) w₂ (by simp)).symm, (G.ne_of_adj hw12).symm]
    have hψw3 : ψ w₃ = d₃ := by
      simp [ψ, (show w₃ ≠ u₁ by intro h; subst h; omega),
        (show w₃ ≠ u₂ by intro h; subst h; omega),
        (hv_ne_w v₁ (by simp) w₃ (by simp)).symm, (hv_ne_w v₂ (by simp) w₃ (by simp)).symm,
        (hv_ne_w v₃ (by simp) w₃ (by simp)).symm, hw31, (G.ne_of_adj hw23).symm]
    have hψY1 : ∀ r ∈ Y₁, ψ r = aY₁ r := by
      intro r hr; simp [ψ, (show r ≠ u₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ u₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₃ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₃ by intro h; subst h; rw [mem_leafNbrs] at hr; omega), hr]
    have hψY2 : ∀ r ∈ Y₂, ψ r = aY₂ r := by
      intro r hr
      have hnot1 : r ∉ Y₁ := fun h => Finset.disjoint_left.mp hY_disj h hr
      simp [ψ, (show r ≠ u₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ u₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ v₃ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₁ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₂ by intro h; subst h; rw [mem_leafNbrs] at hr; omega),
        (show r ≠ w₃ by intro h; subst h; rw [mem_leafNbrs] at hr; omega), hnot1, hr]
    have hψ_out : ∀ r, r ∉ S → ψ r = adm.φ r := by
      intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union, not_or] at hr
      simp [ψ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]
    apply adm.contradiction hm ψ hψ_out
    · intro r hr; simp only [S, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hr1 | hr2
      · rw [hψu1]; exact hα1C.1
      · rw [hψu2]; exact hα2C.1
      · rw [hψv1]; exact hc1L
      · rw [hψv2]; exact hc2B.1
      · rw [hψv3]; exact hc3Z.1
      · rw [hψw1]; exact hd1L
      · rw [hψw2]; exact hd2B.1
      · rw [hψw3]; exact hd3Z.1
      · rw [hψY1 r hr1]; exact (haY₁ r hr1).1
      · rw [hψY2 r hr2]; exact (haY₂ r hr2).1
    · intro r₁ r₂ hradj hor
      have hcase : ∀ a' b', G.Adj a' b' → a' ∈ S → ψ a' ≠ ψ b' := by
        intro a' b' hab ha'
        simp only [S, Finset.mem_insert, Finset.mem_union] at ha'
        rcases ha' with ha | ha | ha | ha | ha | ha | ha | ha | ha1 | ha2
        · subst a'
          rcases hu1_all b' hab with hb | hb | hb | hbY
          · rw [hb, hψu1, hψv1]; exact Ne.symm hc1α1
          · rw [hb, hψu1, hψu2]; exact Ne.symm hα2C.2.2.2
          · rw [hb, hψu1, hψ_out y₁ hy1_not_S]; exact hα1C.2.1
          · rw [hψu1, hψY1 b' hbY]; exact (haY₁ b' hbY).2.symm
        · subst a'
          rcases hu2_all b' hab with hb | hb | hb | hbY
          · rw [hb, hψu2, hψw1]; exact Ne.symm hd1α2
          · rw [hb, hψu2, hψu1]; exact hα2C.2.2.2
          · rw [hb, hψu2, hψ_out y₂ hy2_not_S]; exact hα2C.2.1
          · rw [hψu2, hψY2 b' hbY]; exact (haY₂ b' hbY).2.symm
        · subst a'
          rcases hall_v1 b' hab with hb | hb
          · rw [hb, hψv1, hψu1]; exact hc1α1
          · rw [hb, hψv1, hψv2]; exact Ne.symm hc21
        · subst a'
          rcases hall_v2 b' hab with hb | hb
          · rw [hb, hψv2, hψv1]; exact hc21
          · rw [hb, hψv2, hψv3]; exact hc2B.2.2.1
        · subst a'
          rcases hall_v3 b' hab with hb | hb
          · rw [hb, hψv3, hψv2]; exact Ne.symm hc2B.2.2.1
          · rw [hb, hψv3, hψ_out z₁ hz1_not_S]; exact hc3Z.2.1
        · subst a'
          rcases hall_w1 b' hab with hb | hb
          · rw [hb, hψw1, hψu2]; exact hd1α2
          · rw [hb, hψw1, hψw2]; exact Ne.symm hd21
        · subst a'
          rcases hall_w2 b' hab with hb | hb
          · rw [hb, hψw2, hψw1]; exact hd21
          · rw [hb, hψw2, hψw3]; exact hd2B.2.2.1
        · subst a'
          rcases hall_w3 b' hab with hb | hb
          · rw [hb, hψw3, hψw2]; exact Ne.symm hd2B.2.2.1
          · rw [hb, hψw3, hψ_out z₂ hz2_not_S]; exact hd3Z.2.1
        · have haL := mem_leafNbrs.mp ha1
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
          have hbu : b' = u₁ := (huniq b' hab).trans (huniq u₁ haL.1.symm).symm
          rw [hbu, hψY1 a' ha1, hψu1]; exact (haY₁ a' ha1).2
        · have haL := mem_leafNbrs.mp ha2
          rcases exists_unique_neighbor_of_deg_one haL.2 with ⟨t, _, huniq⟩
          have hbu : b' = u₂ := (huniq b' hab).trans (huniq u₂ haL.1.symm).symm
          rw [hbu, hψY2 a' ha2, hψu2]; exact (haY₂ a' ha2).2
      rcases hor with h1 | h2
      · exact hcase r₁ r₂ hradj h1
      · exact (hcase r₂ r₁ hradj.symm h2).symm
    · intro s hsS _ r hrS hsr
      rcases hS_out s hsS r hrS hsr with ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩
      · rw [hr, hs, hψu1]; exact hα1C.2.2
      · rw [hr, hs, hψu2]; exact hα2C.2.2.1
      · rw [hr, hs, hψv3]; exact hc3Z.2.2
      · rw [hr, hs, hψw3]; exact hd3Z.2.2
    · intro s hsS hiso ⟨r, hsr⟩
      have hrS : r ∈ S := by by_contra h; exact hiso r h hsr
      rcases hnoniso s hsS ⟨r, hrS, hsr⟩ with ⟨w, hwS, hsw⟩
      exact False.elim (hiso w hwS hsw)
    · intro r hrS _
      simp only [S, Finset.mem_insert, Finset.mem_union] at hrS
      rcases hrS with hr | hr | hr | hr | hr | hr | hr | hr | hr1 | hr2
      · subst r
        exact pcf_from_leaf_and_three huv₁ hu1y1 hadj (fun h => by subst h; omega)
          (fun h => by subst h; omega) hy1u2 (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun t ht => (mem_leafNbrs.mp ht).1) hψY1
          (fun t ht => by
            rcases hu1_all t ht with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h)))
          (by rw [hψv1, hψ_out y₁ hy1_not_S, hψu2]; exact hγ₁)
      · subst r
        exact pcf_from_leaf_and_three huw₁ hu2y2 hadj.symm (fun h => by subst h; omega)
          (fun h => by subst h; omega) hy2u1 (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun h => by rw [mem_leafNbrs] at h; omega) (fun h => by rw [mem_leafNbrs] at h; omega)
          (fun t ht => (mem_leafNbrs.mp ht).1) hψY2
          (fun t ht => by
            rcases hu2_all t ht with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h)))
          (by rw [hψw1, hψ_out y₂ hy2_not_S, hψu1]; exact hγ₂)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₁ huv₁.symm hv12 hv2u1.symm
          (by rw [hψu1, hψv2]; exact Ne.symm hc2B.2.1)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₂ hv12.symm hv23 hv31.symm
          (by rw [hψv1, hψv3]; exact Ne.symm hc31)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdv₃ hv23.symm hv3z1 hzv2.symm
          (by rw [hψv2, hψ_out z₁ hz1_not_S]; exact hc2B.2.2.2)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw₁ huw₁.symm hw12 hw2u2.symm
          (by rw [hψu2, hψw2]; exact Ne.symm hd2B.2.1)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw₂ hw12.symm hw23 hw31.symm
          (by rw [hψw1, hψw3]; exact Ne.symm hd31)
      · subst r
        exact pcf_at_of_two_distinct_neighbors hdw₃ hw23.symm hw3z2 hzw2.symm
          (by rw [hψw2, hψ_out z₂ hz2_not_S]; exact hd2B.2.2.2)
      · exact pcf_at_deg_one (mem_leafNbrs.mp hr1).2 (mem_leafNbrs.mp hr1).1.symm
      · exact pcf_at_deg_one (mem_leafNbrs.mp hr2).2 (mem_leafNbrs.mp hr2).1.symm

end LeanResearch.Proposal3
