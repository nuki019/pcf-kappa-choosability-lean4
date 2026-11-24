/-
Copyright (c) 2026 Lean Research Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI + Lean 4 Research Team
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# AI + Lean 4 候选科研课题核心形式化定义与主定理声明

本文件包含 `PROPOSALS.md` 中三个候选课题的极简核心定义与命题陈述（课题 3 的完整形式化证明见 `LeanResearch.Main`）：
1. `LeanResearch.Proposal1`: De Morgan 公式的有限深度局部语法收缩指数
   （目标：突破 Paterson–Zwick 1993 的 `(5 - √3) / 2` 与确定性 `#SAT` 的 `n^{2.63}` 门槛）。
2. `LeanResearch.Proposal2`: 确定性抢占式加权 FIFO 缓冲区管理（QoS 交换机）
   （目标：突破 Englert–Westermann 2009 的 `√3` 确定性竞争比上界）。
3. `LeanResearch.Proposal3`: 稀疏图的恰当无冲突 `κ_G`-可选择性（放电法）
   （目标：将 Lu–Ying–Song 2026 年 8 月的 `mad(G) < 12/5` 推进至 `mad(G) < 5/2`）。
-/

@[expose] public section

namespace LeanResearch

/-! ## 课题 1：De Morgan 公式局部语法收缩指数 -/

namespace Proposal1

/-- `n` 个布尔变量上的 De Morgan 公式（否定仅出现在叶节点文字上）。 -/
inductive DeMorganFormula (n : ℕ) where
  | const : Bool → DeMorganFormula n
  | lit : Fin n → Bool → DeMorganFormula n
  | and : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  | or : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  deriving DecidableEq

/-- 公式在布尔赋值 `x` 下的语义求值。 -/
def DeMorganFormula.eval {n : ℕ} : DeMorganFormula n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .lit i s, x => if s then x i else !(x i)
  | .and f g, x => f.eval x && g.eval x
  | .or f g, x => f.eval x || g.eval x

/-- 二元逻辑门总数（常量与单文字记为 `0`，自然规避 `L = 1` 退化情形）。 -/
def DeMorganFormula.gateSize {n : ℕ} : DeMorganFormula n → ℕ
  | .const _ => 0
  | .lit _ _ => 0
  | .and f g => f.gateSize + g.gateSize + 1
  | .or f g => f.gateSize + g.gateSize + 1

/-- 单变量赋值限制 `F|_{x_i = b}`。 -/
def DeMorganFormula.restrict {n : ℕ} (i : Fin n) (b : Bool) :
    DeMorganFormula n → DeMorganFormula n
  | .const c => .const c
  | .lit j s => if j = i then .const (if s then b else !b) else .lit j s
  | .and f g => .and (f.restrict i b) (g.restrict i b)
  | .or f g => .or (f.restrict i b) (g.restrict i b)

/-- 局部合取化简（常量传播、同胞幂等/互补与直接吸收律）。 -/
def mkAnd {n : ℕ} : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  | .const false, _ | _, .const false => .const false
  | .const true, g => g
  | f, .const true => f
  | .lit i s, .lit j t =>
    if i = j then (if s = t then .lit i s else .const false)
    else .and (.lit i s) (.lit j t)
  | .lit i s, .or g₁ g₂ =>
    if g₁ = .lit i s ∨ g₂ = .lit i s then .lit i s else .and (.lit i s) (.or g₁ g₂)
  | .or g₁ g₂, .lit i s =>
    if g₁ = .lit i s ∨ g₂ = .lit i s then .lit i s else .and (.or g₁ g₂) (.lit i s)
  | f, g => .and f g

/-- 局部析取化简（与 `mkAnd` 对偶）。 -/
def mkOr {n : ℕ} : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  | .const true, _ | _, .const true => .const true
  | .const false, g => g
  | f, .const false => f
  | .lit i s, .lit j t =>
    if i = j then (if s = t then .lit i s else .const true)
    else .or (.lit i s) (.lit j t)
  | .lit i s, .and g₁ g₂ =>
    if g₁ = .lit i s ∨ g₂ = .lit i s then .lit i s else .or (.lit i s) (.and g₁ g₂)
  | .and g₁ g₂, .lit i s =>
    if g₁ = .lit i s ∨ g₂ = .lit i s then .lit i s else .or (.and g₁ g₂) (.lit i s)
  | f, g => .or f g

/-- 自底向上的局部语法化简算子。 -/
def DeMorganFormula.simplify {n : ℕ} : DeMorganFormula n → DeMorganFormula n
  | .const c => .const c
  | .lit i s => .lit i s
  | .and f g => mkAnd f.simplify g.simplify
  | .or f g => mkOr f.simplify g.simplify

/-- 局部最简公式谓词。 -/
def DeMorganFormula.IsReduced {n : ℕ} (F : DeMorganFormula n) : Prop :=
  F.simplify = F

/-- 深度截断为 `d`、忽略变量名的局部子树模式（确保势函数严格局部可计算）。 -/
inductive LocalShape : ℕ → Type where
  | cut : LocalShape 0
  | const : {d : ℕ} → LocalShape (d + 1)
  | lit : {d : ℕ} → LocalShape (d + 1)
  | and : {d : ℕ} → LocalShape d → LocalShape d → LocalShape (d + 1)
  | or : {d : ℕ} → LocalShape d → LocalShape d → LocalShape (d + 1)

/-- 提取公式在根节点处截断至深度 `d` 的局部树形。 -/
def DeMorganFormula.shapeOf {n : ℕ} : (d : ℕ) → DeMorganFormula n → LocalShape d
  | 0, _ => .cut
  | _ + 1, .const _ => .const
  | _ + 1, .lit _ _ => .lit
  | d + 1, .and f g => .and (f.shapeOf d) (g.shapeOf d)
  | d + 1, .or f g => .or (f.shapeOf d) (g.shapeOf d)

/-- 由有限深度模式权重表 `w` 诱导的线性局部语法势函数。 -/
def localPotential {n k : ℕ} (w : LocalShape k → ℚ) : DeMorganFormula n → ℚ
  | f@(.const _) => w (f.shapeOf k)
  | f@(.lit _ _) => w (f.shapeOf k)
  | f@(.and a b) => w (f.shapeOf k) + localPotential w a + localPotential w b
  | f@(.or a b) => w (f.shapeOf k) + localPotential w a + localPotential w b

/-- 课题 1 命题陈述（未选定候选课题）：存在有限深度局部语法势函数使单步平均收缩指数 `γ` 严格突破
Paterson–Zwick (1993) 的 `(5 - √3) / 2 ≈ 1.63397`。 -/
def Proposal1Statement : Prop :=
    ∃ (k : ℕ) (w : LocalShape k → ℚ) (c₁ c₂ : ℚ) (γ : ℝ),
      0 < c₁ ∧
      (5 - Real.sqrt 3) / 2 < γ ∧
      (∀ (n : ℕ) (F : DeMorganFormula n), F.IsReduced →
        c₁ * (F.gateSize : ℚ) ≤ localPotential w F ∧
        localPotential w F ≤ c₂ * (F.gateSize : ℚ)) ∧
      (∀ (n : ℕ) (F : DeMorganFormula n), F.IsReduced →
        2 * γ * (localPotential w F : ℝ) ≤
          ∑ i : Fin n, ∑ b : Bool,
            ((localPotential w F - localPotential w (F.restrict i b).simplify : ℚ) : ℝ))

end Proposal1

/-! ## 课题 2：确定性抢占式加权 FIFO 缓冲区管理（势函数法） -/

namespace Proposal2

/-- QoS FIFO 缓冲区在线事件流：非负权重数据包到达，或队头数据包发出。 -/
inductive PacketEvent where
  | arrive (w : ℚ) (hw : 0 ≤ w)
  | deliver

/-- 容量为 `B` 的抢占式 FIFO 缓冲区单步合法转移与瞬时吞吐收益。 -/
def ValidStep (B : ℕ) (q : List ℚ) (e : PacketEvent) (q' : List ℚ) (gain : ℚ) : Prop :=
  match e with
  | .arrive w _ => q'.Sublist (q ++ [w]) ∧ q'.length ≤ B ∧ gain = 0
  | .deliver =>
      match q with
      | [] => q' = [] ∧ gain = 0
      | h :: t => q' = t ∧ gain = h

/-- 离线调度从初始队列 `q` 出发在事件序列上取得总收益 `totalGain` 的合法执行轨迹。 -/
inductive ValidTrace (B : ℕ) : List ℚ → List PacketEvent → ℚ → Prop where
  | nil (q : List ℚ) : ValidTrace B q [] 0
  | cons {q q' : List ℚ} {e : PacketEvent} {es : List PacketEvent} {g rest : ℚ} :
      ValidStep B q e q' g → ValidTrace B q' es rest → ValidTrace B q (e :: es) (g + rest)

/-- 容量为 `B`、内部状态类型为 `S` 的确定性在线 FIFO 算法。 -/
structure OnlineFIFOAlg (B : ℕ) (S : Type) where
  init : S
  buf : S → List ℚ
  init_empty : buf init = []
  step : S → PacketEvent → S × ℚ
  step_valid : ∀ s e, ValidStep B (buf s) e (buf (step s e).1) (step s e).2

/-- 沿事件序列运行在线算法并累计吞吐收益。 -/
def OnlineFIFOAlg.runFrom {B : ℕ} {S : Type} (alg : OnlineFIFOAlg B S) :
    S → List PacketEvent → ℚ
  | _, [] => 0
  | s, e :: es =>
      let (s', g) := alg.step s e
      g + alg.runFrom s' es

/-- 从空缓冲区出发运行在线算法得到的总吞吐收益。 -/
def OnlineFIFOAlg.runGain {B : ℕ} {S : Type} (alg : OnlineFIFOAlg B S)
    (events : List PacketEvent) : ℚ :=
  alg.runFrom alg.init events

/-- 课题 2 命题陈述（未选定候选课题）：存在严格优于 Englert–Westermann (2009) `√3 ≈ 1.73205` 上界的
确定性抢占式 FIFO 在线算法（对所有缓冲区容量 `B ≥ 1` 一致成立）。 -/
def Proposal2Statement : Prop :=
    ∃ c : ℝ, 1 ≤ c ∧ c < Real.sqrt 3 ∧
      ∀ (B : ℕ), 1 ≤ B →
        ∃ (S : Type) (alg : OnlineFIFOAlg B S),
          ∀ (events : List PacketEvent) (optGain : ℚ),
            ValidTrace B [] events optGain →
            (optGain : ℝ) ≤ c * (alg.runGain events : ℝ)

end Proposal2

/-! ## 课题 3：稀疏图的恰当无冲突 `κ_G`-可选择性（放电法） -/

namespace Proposal3

/-- 纯整数化的最大平均度上界条件：`mad(G) < p / q`，等价于对一切非空子集 `S ⊆ V`，
有 `2q · |E(G[S])| < p · |S|`（无向图有序相邻对数恰等于 `2|E(G[S])|`）。 -/
def MadLt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    q * ((S ×ˢ S).filter (fun e => G.Adj e.1 e.2)).card < p * S.card

/-- 恰当无冲突染色（Proper Conflict-Free Coloring）：恰当点染色，且每个非孤立点 `v` 的
开邻域中至少存在一种颜色恰好出现一次。 -/
def IsPCFColoring {V α : Type*} (G : SimpleGraph V) (φ : V → α) : Prop :=
  (∀ u v, G.Adj u v → φ u ≠ φ v) ∧
  (∀ v, (∃ u, G.Adj v u) →
    ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → φ w = φ u → w = u)

/-- 恰当无冲突 `f`-可选择性：对任意满足 `|L(v)| ≥ f(v)` 的列表赋值 `L : V → Finset ℕ`，
均存在满足 `φ(v) ∈ L(v)` 的恰当无冲突染色 `φ`（有限图上与任意颜色类型等价）。 -/
def IsPCFChoosable {V : Type*} (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ L : V → Finset ℕ,
    (∀ v, f v ≤ (L v).card) →
    ∃ φ : V → ℕ, IsPCFColoring G φ ∧ ∀ v, φ v ∈ L v

/-- Kashima–Škrekovski–Xu (2025/2026) 度列表函数 `κ_G(v)`：
2-度点取 `4`，其余顶点取 `d_G(v) + 1`。 -/
def kappa {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  if G.degree v = 2 then 4 else G.degree v + 1

/-- 课题 3 远景猜想陈述（`mad(G) < 5/2`，平面图围长 `≥ 10`）；
已无 `sorry` 形式化证明的严格突破定理 `MadLt G 22 9`（平面图围长 `≥ 11`，超越 2026 年 8 月 SOTA `12/5`）
及基线定理 `MadLt G 12 5` 详见 `LeanResearch.Main`。 -/
def Proposal3Conjecture5_2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected →
    ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2) →
    MadLt G 5 2 →
    IsPCFChoosable G (kappa G)

end Proposal3

end LeanResearch
