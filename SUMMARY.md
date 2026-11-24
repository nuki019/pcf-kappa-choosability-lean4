# 课题 3 研究总结报告（`SUMMARY.md`）：稀疏图的恰当无冲突 $\kappa_G$-可选择性

> **项目路径**：`C:\Users\wfy\.gemini\antigravity\scratch\lean_research`
> **工具链**：Lean `v4.36.0` + Mathlib `v4.36.0`
> **核心主入口**：`LeanResearch/Main.lean`（基于 `LeanResearch/Proposals.lean` 中未经修改的原始核心定义 `MadLt`、`IsPCFColoring`、`IsPCFChoosable`、`kappa`）
> **形式化规模**：19 个 Lean 4 源文件，共 **28,141 行**，全项目 **0 错误、0 警告、0 `sorry`、0 `admit`、0 自定义 `axiom`**，并通过独立内核重验器 `leanchecker LeanResearch.Main`。

---

## 一、核心科研成果与突破阈值

在课题 3（`LeanResearch.Proposal3`）的阶梯攻坚中，我们在 Lean 4 内核中无 `sorry` 完成了两座里程碑定理及其标准定义等价桥梁的机器证明：

| 里程碑 | 主定理标识符 | 证明的最大平均度阈值 | 数值 | 平面图围长推论（纸面欧拉公式） | 学术定位 |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **里程碑 1（基线）** | `LeanResearch.Main.proposal3_baseline_12_5` | `MadLt G 12 5`（$\operatorname{mad}(G) < \frac{12}{5}$） | $2.4000$ | $g \ge 12$ | 完整复现并形式化核验 Lu–Ying–Song（Aug 2026, `arXiv:2608.29375`）SOTA |
| **里程碑 2（突破）** | `LeanResearch.Main.proposal3_main_theorem` | **`MadLt G 22 9`**（$\operatorname{mad}(G) < \frac{22}{9}$） | **$2.4444\dots$** | **$g \ge 11$** | **严格超越 2026 年 8 月 SOTA $\frac{12}{5}$，将平面图围长下界推进 1 档（$12 \to 11$）** |
| **标准定义桥梁** | `LeanResearch.Main.madLt_iff_edgeFinset` & `proposal3_main_theorem_any_color` | `9 * (2 * \|E(G[S])\|) < 22 * \|S\|` | $2.4444\dots$ | 同上 | 机器认证 `MadLt` 与 `2 * edgeFinset.card` 等价，并将主定理推广至**任意颜色类型 `α`** |

> **注**：平面图围长推论由经典欧拉公式 $\operatorname{mad}(G) < \frac{2g}{g-2}$（$g=11$ 时恰为 $\frac{22}{9}$）及连通分支分解直接得出，未在 Lean 中形式化平面拓扑。

**主定理精确陈述**（零隐藏假设，直接复用 `LeanResearch.Proposals` 原始定义）：

```lean
theorem LeanResearch.Main.proposal3_main_theorem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hneC5 : ¬ (Fintype.card V = 5 ∧ ∀ v : V, G.degree v = 2))
    (hmad : MadLt G 22 9) :
    IsPCFChoosable G (kappa G)
```

---

## 二、核心方法创新：零辅助图核心子图归约（$K$）

已有文献（Lu–Ying–Song 2026）为处理 1-度叶节点构造了受限于特殊分数 $2 + \frac{2}{r}$ 的 $r$-叶环辅助图 $H_r(G)$。本研究发现并形式化了一套**完全不依赖任何辅助图**的等价核心归约（`LeanResearch/Proposal3/Basic.lean`、`ThreadDefs.lean`）：

- 定义核心顶点集 $K = \mathtt{coreVerts}\ G = \{v \in V(G) \mid d_G(v) \ge 2\}$（在无孤立点图中恰等于删去全体 $1$-度叶点集合 $X = \{v \mid d_G(v) = 1\}$ 后的 $V(G) \setminus X$），核心度 $d_K(u) = \mathtt{coreDeg}\ G\ u = |N_G(u) \cap K|$。
- 对任意极小反例 $G$（连通且 $|V(G)| \ge 4$），$K$ 必非空；直接将 `MadLt G p q` 应用于 $K$ 即得纯整数核心度上界（`mad_core_sum_lt`）：
  $$q \sum_{u \in K} d_K(u) < p \cdot |K|.$$
- 该归约彻底消除辅助图构造与叶环 `mad` 保持证明，使放电法天然适用于任意一般有理分数 $\frac{p}{q}$（如 $\frac{12}{5}, \frac{22}{9}, \frac{5}{2}$），且里程碑 1（`Discharging12_5.lean`）与里程碑 2（`Discharging22_9.lean`）在模块依赖上**完全解耦**。

> **记号约定**：下文统一用 $p / q$ 表示 `MadLt G p q` 的有理阈值分子与分母，用 $d_K(u)$ 表示顶点 $u$ 的核心度，用 $n_{\text{leaf}}(u)$ 表示叶邻点数，用 $n_1, n_2, n_3$ 分别表示 $u$ 关联的 $1$-/$2$-/$3$-线串数，用 $b, g$ 分别表示坏/好核心邻点数（满足核心度五分恒等式 $d_K = n_1 + n_2 + n_3 + b + g$）。

---

## 三、已通过 Lean 4 内核核验的可约构型引理清单

### 3.1 通用基础引擎与基线结构引理

前 4 个基础模块对**任意**阈值 $(p, q)$ 的极小反例均成立；`BadAndThreads1` 与 `BadAndThreads2` 对一切 $\operatorname{mad}(G) < \frac{5}{2}$（即 $2p \le 5q$）均成立：

| 模块 | 行数 | 适用范围 | 核心已核验引理 | 数学含义 |
| :--- | ---: | :---: | :--- | :--- |
| `Basic.lean` | 360 | 任意 $(p,q)$ | `mad_core_sum_lt`, `exists_pcfRep` | 核心子图密度上界；PCF 代表系充分定理（Lemma 2.1） |
| `Admissible.lean` | 1,010 | 任意 $(p,q)$ | `c5_pcf_colorable_of_ne`, `isPCFChoosable_of_no_minimal_counterexample`, `exists_admissible_coloring_avoid` | $C_5$ 的 4-列表可染充分条件（Lemma 2.3）；极小反例强归纳；通用容许染色延拓引擎 `AdmissibleColoring` |
| `CoreStructure.lean` | 1,621 | 任意 $(p,q)$ | `leaf_neighbor_deg_ge_four`, `no_four_path_of_deg_two`, `no_two_thread_same_anchor`, `no_three_thread_same_anchor`, `no_three_vertex_two_thread` | 叶邻点度数 $\ge 4$；无 $4^+$-线串；线串两端锚点必互异；$3$-度点不连 $2^+$-线串 |
| `ThreadDefs.lean` | 1,048 | 任意 $(p,q)$ | `card_threadAnchors_eq_two`, `card_anchored_degTwo_eq`, `no_pcfRep_nil_bounds`, `no_pcfRep_single_bounds`, `no_pcfRep_pair_ge_two` | 好/坏核心顶点及其可判定性；每个 $2$-度点恰有 2 个锚点；锚定计数恒等式 $|\mathtt{anchoredDegTwo}\ u| = n_1 + 2n_2 + 3n_3$；PCF 代表系双计数下界引擎 |
| `BadAndThreads1.lean` | 2,412 | $2p \le 5q$ | `leaf_plus_long_thread_le`, `good_or_bad_of_deg_ge_three`, `bad_no_long_thread`, `bad_no_one_thread`, `bad_two_color_extension`, `bad_fixed_color_extension`, `no_adjacent_bad` | 升级版 Lemma 3.5（摆脱 $12/5$ 依赖：$n_{\text{leaf}} + n_2 + n_3 \le d_G - 2$）；坏点无任何线串、不相邻，且支持双色/定色延拓 |
| `BadAndThreads2.lean` | 2,853 | $2p \le 5q$ | `thread_reduction`, `one_thread_unique_of_two_thread`, `no_bad_nbr_of_two_and_one_thread`, `no_one_thread_bad_neighbor`, `good_coreDeg_three_long_thread_summary` | 好 $d_K=3$ 顶点含长线串的完整结构约束（Lemmas 3.9–3.10, Corollary 3.11） |
| `Discharging12_5.lean` | 206 | $(12, 5)$ | `no_minimal_counterexample_12_5`, `pcf_kappa_choosable_mad_12_5` | 整数放大 5 倍放电证明 **$\operatorname{mad}(G) < \frac{12}{5}$**（里程碑 1） |

### 3.2 突破 $\frac{12}{5} \to \frac{22}{9}$ 的五组全新可约构型引理（引理 A–E）

| 引理族 | 模块 | 行数 | 核心已核验引理 | 数学内容与作用 |
| :--- | :--- | ---: | :--- | :--- |
| **基础定义** | `BeyondDefs.lean` | 288 | `coreDeg_eq_five_parts`, `isT3_structure`, `isT21_structure`, `isT20_structure` | $d_K = n_1 + n_2 + n_3 + b + g$ 五分恒等式；`T3` / `T21` / `T20` 结构刻画与 `L3` / `B3` 定义；1-/2-线串对端提取 |
| **引理 A 核心 & E0** | `ThreeThreadExt.lean` | 1,360 | `threeThreadGoodCols_card_one_le_one`, `threeThreadGoodCols_avoid_card_one_le_three`, `t3_fixed_color_extension`, `t21_fixed_color_extension`, `s32_a2_fixed_color_extension`, `no_T3_adj_deg_three` | **3-线串单点计数精确压紧至 $\le 1$**（原论文粗估为 3）；纯组合定色延拓引擎；证明 `T3` 无任何 $3$-度邻点 |
| **引理 A（$d_K = 4$ 排除）** | `Q4Ext.lean` | 2,344 | `q4_three_thread_good_bound` | 在 $9p \le 22q$ 下，若 $d_K(u)=4, n_3 \ge 1, n_2+n_3=2$，则 $n_3 \le g$，一次性消灭全部 8 个高代价 $d_K=4$ 阻塞配置 |
| **引理 B（$d_K = 3, g = 0$ 排除）** | `Core3Ext.lean` | 1,577 | `no_leafy_coreDeg3_all_a_b_except_L4`, `deg_three_no_good_at_most_one_bad` | 含叶 $d_K=3, n_2=n_3=g=0$ 顶点除 `L4`（$d_G=4, 1$ 叶 $+ 3$ 条 $1$-线串）外全部可约；$3$-度且 $g=0$ 顶点至多有 $1$ 个坏核心邻点（仅剩 `L3` 与 `B3`） |
| **引理 C & D（弱点桥接禁用）** | `BridgeExt.lean` | 7,670 | `IsL4`, `IsPoor1Ext`, `L3_at_most_one_L3_nbr`, `no_B3_one_thread_Poor1Ext`, `no_T21_one_thread_Poor1Ext`, `no_L4_one_thread_Poor1Ext`, `no_T21_two_thread_T21` | 令 `IsPoor1Ext` $= \{L3, B3, T21, L4\}$：每个 `L3` 至多通过 $1$-线串连 1 个 `L3`；`B3`/`T21`/`L4` 不经 $1$-线串连向任何 `IsPoor1Ext` 顶点；任意两 `T21` 不经 $2$-线串相连 |
| **引理 E1–E4（`T3` 邻接限制）** | `T3Adjacency.lean` + `T3Adjacency2.lean` | 4,102 | `no_T3_adj_T3`, `no_T3_adj_T21`, `no_T3_adj_S3_2_a2`, `no_T3_T20_T3` | 在 $9p \le 22q$ 下：任意两 `T3` 不相邻；`T3` 不邻接 `T21`；`T3` 不邻接 $(d_K=3, n_1=2, g=1)$ 顶点；每个 `T20` 至多邻接 $1$ 个 `T3` |
| **线串划分 & 主放电** | `ThreadPartition.lean` + `Discharging22_9.lean` | 901 | `sum_wThread_in_deg_two`, `sum_wThread_out_le_general`, `no_minimal_counterexample_22_9`, `pcf_kappa_choosable_mad_22_9` | `anchoredDegTwo` 精确三分计数；参数化线串转权 `wThread`；整数放大 36 倍放电证明 **$\operatorname{mad}(G) < \frac{22}{9}$** |

---

## 四、整数放大 36 倍放电规则与全度数最终权值核验表

在核心子图 $K = \mathtt{coreVerts}\ G$ 上，设每个顶点 $u \in K$ 的初始权值为：
$$\mathrm{ch}(u) = 36 \cdot d_K(u) - 88.$$
由 `MadLt G 22 9`（`mad_core_sum_lt`）知 $\sum_{u \in K} \mathrm{ch}(u) = 36 \sum_{u \in K} d_K(u) - 88|K| < 0$。

### 4.1 放电规则（全整数化，零分母）
记 $\mathcal{P}_1 = \mathtt{IsPoor1Ext} = \{L3, B3, T21, L4\}$：
- **规则 R1（线串转权 `wThread`）**：对任意 $2$-度点 $x$ 及其双锚点 $\{u, w\}$（`card_threadAnchors_eq_two`）：
  - 若 $x$ 属于 $1$-线串：若 $u \in \mathcal{P}_1, w \notin \mathcal{P}_1$，则 $u \to x$ 送 $6$、$w \to x$ 送 $10$；若同属或同不属 $\mathcal{P}_1$，两端各送 $8$（总计恒为 $16$）。
  - 若 $x$ 属于 $2$-线串：若 $u \in T21, w \notin T21$，则 $u \to x$ 送 $7$、$w \to x$ 送 $9$；否则各送 $8$（总计恒为 $16$）。
  - 若 $x$ 属于 $3$-线串：两端锚点各向 $x$ 送 $8$（总计恒为 $16$）。
- **规则 R2（好 $\to$ 坏）**：每个好核心顶点向每个相邻坏核心顶点送出 $+8$。
- **规则 R3（好 $\to T3$）**：每个好核心顶点向每个相邻的 $T3$ 顶点送出 $+2$。

### 4.2 各类核心顶点的最终权值 $\mathrm{ch}'(u)$ 完备核验

| 顶点类别 | 初始权值 $\mathrm{ch}(u)$ | 送出上界 | 接收下界 | 最终权值 $\mathrm{ch}'(u)$ | 依赖的可约构型引理 |
| :--- | :---: | :---: | :---: | :---: | :--- |
| $2$-度核心点 | $-16$ | $0$ | $+16$ | $= 0$ | `sum_wThread_in_deg_two` |
| 坏核心点（$d_G \ge 4, d_K=2$） | $-16$ | $0$ | $8 \times 2 = +16$ | $= 0$ | `bad_no_one_thread`, `bad_no_long_thread`, `no_adjacent_bad` |
| 好点 $d_K \ge 5$ | $36 d_K - 88$ | $\le 10 d_K + 14(n_2+n_3) \le 24 d_K - 28$ | $\ge 0$ | $\ge 12 d_K - 60 \ge 0$ | `leaf_plus_long_thread_le` |
| 好点 $d_K = 4$ | $+56$ | $\le 10n_1 + 18n_2 + 24n_3 + 8b + 2g \le 56$ | $\ge 0$ | $\ge 0$ | `leaf_plus_long_thread_le`, **`q4_three_thread_good_bound`** |
| $d_K=3$：`T3`（$n_3=1, g=2$） | $+20$ | $24 + 0 = 24$ | $2 \times 2 = +4$ | $= 0$ | `isT3_structure`, **`no_T3_adj_T3`** |
| $d_K=3$：`T21`（$n_2=1, n_1=1, g=1$） | $+20$ | $14 + 6 + 0 = 20$ | $\ge 0$ | $\ge 0$ | **`no_T21_two_thread_T21`**, **`no_T21_one_thread_Poor1Ext`**, **`no_T3_adj_T21`** |
| $d_K=3$：`T20`（$n_2=1, n_1=0, g=2$） | $+20$ | $\le 18 + 2 = 20$ | $\ge 0$ | $\ge 0$ | `isT20_structure`, **`no_T3_T20_T3`** |
| $d_K=3, n_2=n_3=g=0, d_G \ge 4$（`L4`） | $+20$ | $6 \times 3 = 18$ | $\ge 0$ | $\ge +2$ | **`no_leafy_coreDeg3_all_a_b_except_L4`**, **`no_L4_one_thread_Poor1Ext`** |
| $d_K=3, n_2=n_3=g=0, d_G=3, b=1$（`B3`） | $+20$ | $6 \times 2 + 8 = 20$ | $\ge 0$ | $\ge 0$ | **`deg_three_no_good_at_most_one_bad`**, **`no_B3_one_thread_Poor1Ext`** |
| $d_K=3, n_2=n_3=g=0, d_G=3, b=0$（`L3`） | $+20$ | $\le 8 + 6 + 6 = 20$ | $\ge 0$ | $\ge 0$ | **`L3_at_most_one_L3_nbr`**, **`no_{B3,T21,L4}_one_thread_Poor1Ext`** |
| $d_K=3, n_2=n_3=0, g=1, n_1=2$ | $+20$ | $\le 10 \times 2 + 0 = 20$ | $\ge 0$ | $\ge 0$ | **`no_T3_adj_S3_2_a2`** |
| $d_K=3, n_2=n_3=0, g=1, n_1 \le 1$ | $+20$ | $\le 10 + 8 + 2 = 20$ | $\ge 0$ | $\ge 0$ | `sum_wThread_out_le_general` |
| $d_K=3, n_2=n_3=0, g \ge 2$ | $+20$ | $\le 10(n_1+b) + 2g \le 14$ | $\ge 0$ | $\ge +6$ | `sum_wThread_out_le_general` |

由此 $0 \le \sum_{u \in K} \mathrm{ch}'(u) = \sum_{u \in K} \mathrm{ch}(u) < 0$，导出矛盾！

---

## 五、内核编译与公理审计结果

- **全项目构建**：`lake build` 退出码 `0`，全项目 **0 错误、0 警告、0 `sorry`**。
- **独立内核重验**：`lake env leanchecker LeanResearch.Main` 退出码 `0`，对传递闭包中全部 `.olean` 声明完成二次内核复核。
- **静态扫描**：全项目代码区零 `sorry`、零 `admit`、零自定义 `axiom`、零 `native_decide` / `unsafe` / `partial` / `set_option`。
- **内核公理审计（`#print axioms`）**：
  - `LeanResearch.Main.proposal3_baseline_12_5`、`proposal3_main_theorem`、`madLt_iff_edgeFinset`、`proposal3_main_theorem_any_color` 均仅依赖 Lean 标准公理 `{propext, Classical.choice, Quot.sound}`。
- **定义完好性**：`LeanResearch/Proposals.lean` 中已审计的 `MadLt`、`IsPCFColoring`、`IsPCFChoosable`、`kappa` 保持原样未改动。

---

## 六、结论的边界与局限性：为什么局域放电法止步于 $\frac{5}{2}$ 下方？

在探索 $\operatorname{mad}(G) < \frac{5}{2}$（平面图围长 $g \ge 10$）的过程中，我们通过精确局部配置枚举、显式列表阻塞反例构造与 LP 对偶分析，定位了三处清晰的**局域放电本质障碍**。

> **本节专用顶点简写**：
> - `G32`：无叶的 $(d_G = 3, d_K = 3, n_1 = 2, g = 1)$ 顶点；
> - `S3_2`：含叶的 $(d_G \ge 4, d_K = 3, n_1 = 2, g = 1)$ 顶点；
> - 括号标注原图度数 $d_G$，如 `T3(d_G=4)`、`T20(d_G=4)`。

1. **$\frac{22}{9} \approx 2.4444$ 处的耦合墙**：
   - 将 `T3`、`T20`、`T21`、`G32` 按配比 `1:2:2:1` 闭合为 27 个核心点、核心度和 66 的周期核网络（含 2 个由 $3$-线串相连的 `T3`、4 个 `T20`、4 个 `T21`、2 个 `G32` 以及 `T3 -- T20 -- 2-thread -- T21 -- 1-thread -- G32` 耦合路径），其核心平均度恰好为 $\frac{66}{27} = \frac{22}{9}$，且在 36 倍放电下每个顶点最终权值均为 $0$；其中 `T21 -- 2-thread -- T20(d_G=4)` 存在显式局部列表阻塞反例，无法仅凭单对局部约化突破。
   - 此外，`L4`（$d_G=4, 1$ 叶 $+ 3$ 条 $1$-线串）本身存在单点列表阻塞反例（$|L(u)|=5$，三个外部色互异落在 $L(u)$ 中且 $L(y)=A_1=A_2=A_3=C$），因此无法作为单点可约构型消除，只能纳入 `IsPoor1Ext` 集合由邻居分摊权值。
2. **$\frac{32}{13} \approx 2.4615 < \frac{5}{2}$ 处的第二堵墙**：
   - 一对通过 $3$-线串相连的 $4$-度 `T3` 顶点（`T3(d_G=4) -- 3-thread -- T3(d_G=4)`）存在显式局部列表阻塞反例（$C_1=\{5\}, C_2=\{6\}, M_1=M_3=\{7,8\}, L(v_2)=\{5,6,7,8\}$）；与 4 个 `T20`（两两连 2 条 $2$-线串，好边构成 6-圈）组成 13 个核心点、核心度和 32 的周期核结构，核心平均度为 $\frac{32}{13}$。
3. **$\frac{52}{21} \approx 2.4762 < \frac{5}{2}$ 处的第三堵墙**：
   - 将不可局部约化的 `L3 -- 1-thread -- L3` 对接入 4 个 `G32` 与 4 个含叶 `S3_2` 顶点，可构造出 21 个核心点（10 个 $d_K=3$ 点 $+ 11$ 个 $2$-度点）、核心度和 52 的周期核结构，核心平均度为 $\frac{52}{21}$。

> **重要澄清**：上述阻塞构造均为**局部列表染色延拓障碍**（说明有限半径局域放电法难以直接跨过 $\frac{32}{13} / \frac{52}{21}$ 抵达 $\frac{5}{2}$），并不构成 $\operatorname{mad}(G) < \frac{5}{2}$ 猜想的全局反例图；原猜想（已在 `LeanResearch/Proposals.lean` 中保留为 `Proposal3Conjecture5_2`）在图论界仍被普遍认为成立，若要进一步逼近 $\frac{5}{2}$ 需引入更长程的链式/全局结构约化或非局部势函数技术。
