/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import LeanResearch.Proposal3.Discharging12_5
public import LeanResearch.Proposal3.Discharging22_9

/-!
# 课题 3 主入口模块（`LeanResearch.Main`）

本模块统一导出课题 3（稀疏图的恰当无冲突 `κ_G`-可选择性）的无 `sorry` 形式化主定理与标准等价桥梁，
全部基于 `LeanResearch.Proposals` 中未经修改的原始核心定义
（`MadLt`、`IsPCFColoring`、`IsPCFChoosable`、`kappa`），零附加假设、零自定义公理：

1. `proposal3_baseline_12_5`（里程碑 1 基线）：复现并内核核验 Lu–Ying–Song（2026 年 8 月 SOTA）的
   `mad(G) < 12/5`（平面图围长 `≥ 12` 推论）定理；
2. `proposal3_main_theorem`（里程碑 2 突破）：将界严格推进至 **`mad(G) < 22/9`**
   （平面图围长下界推进至 **`≥ 11`** 推论）；
3. `madLt_iff_edgeFinset` 与 `proposal3_main_theorem_any_color`：
   显式证得 `MadLt` 与教科书定义 `2|E(G[S])| / |S| < p / q` 严格等价，并将主定理推广至**任意颜色类型 `α`**。
-/

@[expose] public section

namespace LeanResearch.Main

open LeanResearch.Proposal3

/-- 里程碑 1 基线定理（Lu–Ying–Song, Aug 2026 SOTA）：
若连通图 `G` 不是 `C₅` 且 `MadLt G 12 5`（`mad(G) < 12/5`），则 `IsPCFChoosable G (kappa G)`。 -/
theorem proposal3_baseline_12_5
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hneC5 : ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2))
    (hmad : MadLt G 12 5) :
    IsPCFChoosable G (kappa G) :=
  pcf_kappa_choosable_mad_12_5 G hconn hneC5 hmad

/-- 里程碑 2 突破主定理（严格超越 Aug 2026 SOTA `12/5`）：
若连通图 `G` 不是 `C₅` 且 `MadLt G 22 9`（`mad(G) < 22/9`），则 `IsPCFChoosable G (kappa G)`。 -/
theorem proposal3_main_theorem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hneC5 : ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2))
    (hmad : MadLt G 22 9) :
    IsPCFChoosable G (kappa G) :=
  proposal3_pcf_kappa_choosable_22_9 G hconn hneC5 hmad

/-- 诱导子图有序相邻对数恒等于 `2 * |E(G[S])|`（教科书 `mad` 定义桥梁）。 -/
lemma ordered_adj_card_eq_two_mul_edgeFinset_card
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card =
      2 * (G.induce (S : Set V)).edgeFinset.card := by
  classical
  have hhs := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  rw [← hhs]
  have h1 : ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card =
      ∑ u ∈ S, (S.filter (fun v => G.Adj u v)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h1, ← Finset.sum_coe_sort S (fun u => (S.filter (fun v => G.Adj u v)).card)]
  apply Finset.sum_congr rfl
  intro u _
  change (S.filter (fun v => G.Adj u.1 v)).card =
    ((G.induce (S : Set V)).neighborFinset u).card
  refine Finset.card_bij
    (fun v hv => (⟨v, (Finset.mem_filter.mp hv).1⟩ : {x // x ∈ S})) ?_ ?_ ?_
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset]
    exact (Finset.mem_filter.mp hv).2
  · intro v₁ _ v₂ _ h
    exact congrArg Subtype.val h
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact ⟨w.1, Finset.mem_filter.mpr ⟨w.2, hw⟩, Subtype.ext rfl⟩

/-- `MadLt G p q` 与教科书标准定义 `∀ S ≠ ∅, q * (2 * |E(G[S])|) < p * |S|` 严格等价。 -/
theorem madLt_iff_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) :
    MadLt G p q ↔
      ∀ S : Finset V, S.Nonempty →
        q * (2 * (G.induce (S : Set V)).edgeFinset.card) < p * S.card := by
  constructor
  · intro h S hS
    rw [← ordered_adj_card_eq_two_mul_edgeFinset_card G S]
    exact h S hS
  · intro h S hS
    rw [ordered_adj_card_eq_two_mul_edgeFinset_card G S]
    exact h S hS

/-- 里程碑 2 主定理的任意颜色类型与教科书 `2|E(G[S])|` 密度版本：
对任意颜色类型 `α` 与任意满足 `|L(v)| ≥ κ_G(v)` 的列表赋值 `L : V → Finset α`，
均存在恰当无冲突 `L`-染色 `φ : V → α`。 -/
theorem proposal3_main_theorem_any_color
    {V α : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hneC5 : ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2))
    (hmad : ∀ S : Finset V, S.Nonempty →
      9 * (2 * (G.induce (S : Set V)).edgeFinset.card) < 22 * S.card)
    (L : V → Finset α)
    (hL : ∀ v, kappa G v ≤ (L v).card) :
    ∃ φ : V → α, IsPCFColoring G φ ∧ ∀ v, φ v ∈ L v := by
  classical
  have hmad' : MadLt G 22 9 := (madLt_iff_edgeFinset G 22 9).mpr hmad
  have hnat : IsPCFChoosable G (kappa G) :=
    proposal3_main_theorem G hconn hneC5 hmad'
  let U : Finset α := Finset.univ.biUnion L
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let enc : α → ℕ := fun a => if ha : a ∈ U then (e ⟨a, ha⟩).val else 0
  have henc_inj : ∀ {a b : α}, a ∈ U → b ∈ U → enc a = enc b → a = b := by
    intro a b ha hb heq
    have heq' : (e ⟨a, ha⟩).val = (e ⟨b, hb⟩).val := by
      simpa [enc, ha, hb] using heq
    exact congrArg Subtype.val (e.injective (Fin.ext heq'))
  let L' : V → Finset ℕ := fun v => (L v).image enc
  have hL' : ∀ v, kappa G v ≤ (L' v).card := by
    intro v
    have hcard : (L' v).card = (L v).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      exact henc_inj (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, ha⟩)
        (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hb⟩) hab
    rw [hcard]
    exact hL v
  rcases hnat L' hL' with ⟨φ', hpcf', hmem'⟩
  have hchoose : ∀ v, ∃ a ∈ L v, enc a = φ' v := fun v => Finset.mem_image.mp (hmem' v)
  choose φ hφmem hφenc using hchoose
  refine ⟨φ, ⟨?_, ?_⟩, hφmem⟩
  · intro u v huv heq
    apply hpcf'.1 u v huv
    rw [← hφenc u, ← hφenc v, heq]
  · intro v hv
    rcases hpcf'.2 v hv with ⟨u, hvu, huniq⟩
    refine ⟨u, hvu, fun w hvw heq => huniq w hvw ?_⟩
    rw [← hφenc w, ← hφenc u, heq]

end LeanResearch.Main
