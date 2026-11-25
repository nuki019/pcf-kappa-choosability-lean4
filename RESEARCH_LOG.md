# 课题 3 研究日志（`RESEARCH_LOG.md`）：稀疏图恰当无冲突 $\kappa_G$-可选择性

> **核心定义**：严格复用 `LeanResearch/Proposals.lean` 中已审计的 `MadLt`、`IsPCFColoring`、`IsPCFChoosable`、`kappa`（零修改）。
> **阶梯目标**：优先探索 $\mathrm{mad}(G) < \frac{5}{2}$；如在 $\frac{5}{2}$ 处发现局部放电本质障碍，则先完整跑通已知 SOTA $\mathrm{mad}(G) < \frac{12}{5}$（Lu–Ying–Song, Aug 2026, `arXiv:2608.29375`）作为零 `sorry` 基线，再向 $\frac{17}{7}$ / $\frac{22}{9}$ 等更紧阈值递进突破。

---

## 一、阶段 A：理论分析与 LP 放电探索（2026-11-24）

### 1.1 关键结构简化：零辅助图核心子图归约（ $K = G - X$ ）
Lu–Ying–Song (`arXiv:2608.29375`) 为处理 1-度叶节点引入了复杂的 $r$-叶环辅助图 $H_r(G)$，并证明 $\mathrm{mad}(G) < 2 + \frac{2}{r} \implies \mathrm{mad}(H_r(G)) < 2 + \frac{2}{r}$。
我们发现了更简洁且更一般的直接等价归约：
- 令 $X = \lbrace x \in V(G) \mid d_G(x) = 1\rbrace$， $K = G[V(G) \setminus X]$。
- 只要 $G$ 连通且 $|V(G)| \ge 3$， $V(K) = \lbrace v \in V(G) \mid d_G(v) \ge 2\rbrace  = V(G) \setminus X$ 非空，且对每个核心点 $u \in V(K)$，有

  $$d_K(u) = d_G(u) - n_{\text{leaf}}(u).$$

- 对任意有理阈值 $p/q$，直接将 `MadLt G p q` 应用于非空子集 $V(K)$，立刻得：

  $$q \sum_{u \in V(K)} d_K(u) = q \cdot |\{(u,v) \in V(K)^2 \mid G.\mathrm{Adj}\ u\ v\}| < p \cdot |V(K)|.$$

- **优势**：① 彻底省去 $H_r(G)$ 辅助图与叶环 `mad` 保持定理形式化；② 阈值不再受限于 $2 + 2/r$，适用于任意有理分数 $\frac{12}{5}, \frac{17}{7}, \frac{22}{9}, \frac{5}{2}$。

### 1.2 $\mathrm{mad}(G) < \frac{5}{2}$ 的本质瓶颈诊断（为什么纯局部放电法被卡在 $5/2$ 以下）
通过精确枚举 $q \ge 3$ 的全部核心顶点的局部配置、手工构造列表阻塞反例以及 HiGHS LP 对偶诊断，我们定位了 $\frac{12}{5} \to \frac{5}{2}$ 之间的全部障碍：

1. **原论文 $12/5$ 的第一堵墙——全细分 3-正则结构（密度 $= \frac{12}{5}$ ）**：
   - 单个 $3_3$-顶点（3-度点连 3 条 1-线串）及一对由 1-线串相连的 $3_3$-顶点（`L3 -- 1-thread -- L3`）均存在显式 4-列表局部阻塞反例：
     - 单个 $3_3$： $\varphi(y_1)=1,\varphi(y_2)=2,\varphi(y_3)=3$， $\varphi^{\ast}(y_1)=2,\varphi^{\ast}(y_2)=3,\varphi^{\ast}(y_3)=1$， $L(u)=\lbrace 1,2,3,4\rbrace$， $L(x_i)=\lbrace \varphi(y_i),\varphi^{\ast}(y_i),4,5\rbrace$，迫使 $u=4, x_1=x_2=x_3=5$。
     - 一对 `L3 -- 1-thread -- L3`： $C_1=\lbrace 1,2\rbrace , C_2=\lbrace 3,4\rbrace , L(x_0)=\lbrace 1,2,3,4\rbrace$，对任意 $(\alpha_1,\alpha_2)\in C_1\times C_2$，外部 2-度点被迫染成 $C_i\setminus\lbrace \alpha_i\rbrace$，导致 $x_0$ 的 4 个颜色全部被禁。
2. **$\frac{5}{2}$ 下方的第二堵墙——`T3(k=4) -- 3-thread -- T3(m=4)` 局部不可约化（密度 $\frac{32}{13} \approx 2.4615 < \frac{5}{2}$ ）**：
   - 对两个通过 3-线串 $v_1 v_2 v_3$ 相连的 4-度 `T3` 顶点（各含 1 叶、2 个好 4⁺-邻点）：当 $C_1=\lbrace 5\rbrace , C_2=\lbrace 6\rbrace$，外部邻点与叶迫使 $M_1 = M_3 = \lbrace 7,8\rbrace$ 且 $L(v_2)=\lbrace 5,6,7,8\rbrace$ 时， $v_1 \neq v_3$ 迫使 $\lbrace v_1,v_3\rbrace =\lbrace 7,8\rbrace$，令 $v_2$ 无色可染。
   - 将不可局部约化的 `T3 -- 3-thread -- T3` 对接入 `T20 -- 2-thread -- T20` 网络，可构造出局部平均度为 $\frac{32}{13} \approx 2.4615 < \frac{5}{2}$ 的周期核结构。
3. **$\frac{5}{2}$ 下方的第三堵墙——`L3` 对接入 `G32 + S3_2`（密度 $\frac{52}{21} \approx 2.4762 < \frac{5}{2}$ ）**：
   - 即便排除了 `L3` 有两个 `L3` 邻点、并排除 `G32 -- 3-v` 连 `L3` 以及 `L3 -- S3_2`，将 `L3` 对接入 `G32` 再接入 `S3_2` 仍形成密度 $\frac{52}{21} \approx 2.4762 < \frac{5}{2}$ 的周期核结构。
4. **$\frac{22}{9}$ 处的耦合墙**：
   - 将 `T3`、`T20`、`T21`、`G32`（无叶 $d_G=3, n_1=2, g=1$ ）按配比 `1:2:2:1` 闭合为 27 个核心点、核心度和 66 的周期核网络（含 `T3 -- T20 -- 2-thread -- T21 -- 1-thread -- G32` 耦合链，其中 `T21 -- 2-thread -- T20(d_G=4)` 存在局部列表阻塞反例），其核心平均度恰好为 $\frac{66}{27} = \frac{22}{9} \approx 2.4444$。

> **符号注记**：本节中 $d_K(u)$ 记核心度， $n_1$ 记 1-线串数，`G32` 记无叶的 $(d_G=3, n_1=2, g=1)$ 顶点，`S3_2` 记含叶的 $(d_G \ge 4, d_K=3, n_1=2, g=1)$ 顶点；`T3(k=4)` / `T20(d_G=4)` 中括号标注原图度数 $d_G$。
> **结论**：上述局部阻塞反例仅说明**有限半径局域放电法无法直接跨过 $\frac{32}{13} / \frac{52}{21}$ 抵达 $\frac{5}{2}$**（并不意味着 $\mathrm{mad}(G) < \frac{5}{2}$ 存在全局反例图；原猜想仍被认为对一切连通 $G \not\cong C_5$ 成立）。

### 1.3 新发现的可约构型族（支撑严格突破 $\frac{12}{5} \to \frac{22}{9}$ ）
我们在 `arXiv:2608.29375` 的 8 个结构引理基础上，探索出以下候选可约构型族（注：下方为阶段 A 的初筛笔记；最终 36 倍整数放电只需其中最小充分子集，完整形式化清单见 `SUMMARY.md`）：
1. **升级版 `Lemma 3.5`（消除 `12/5` 依赖）**：在 `lem:structure-4` 中， $\varepsilon=1$ 在 $\mathrm{mad} < 5/2$ 下已给 $m \le 2$； $\varepsilon=0$ 孤立点 $z$（ $d_G(z)=m \ge 4$ ）可通过删 $S'=\lbrace z,v_1,w_1,\dots,v_m,w_m\rbrace$ 与 `Lemma 2.1` 双计数直接推出 $4m \le 4|B_z| \le \sum_{\beta\in B_z} q_\beta \le 3m$ 矛盾（见 `BadAndThreads1.lean` `no_isolated_two_thread_hub`），完全摆脱 `12/5` 限制。
2. **新引理 A（3-线串单点计数 $\le 1$ ）**：对任意 3-线串 $u v_1 v_2 v_3 z$，枚举 $v_3$ 的 2 个合法颜色 $\zeta_1 \neq \zeta_2$，可得 $v_1$ 的可达色集 $M_\alpha(v_1)$ 至多对 **1** 个 $\alpha$ 为单点集（原论文粗估为 3）。推论：
   - 彻底消灭 $d_K=4$ 的全部 8 个高代价阻塞构型（在最终 36 倍放电中 $d_K \ge 5$ 已由 `leaf_plus_long_thread_le` 直接关闭）；
   - 消灭所有 $h \ge 2, a+b=3, g=0$ 以及 $h=1, a+b=3, b \ge 1, g=0$ 构型（仅余 `L4`）；
   - 证明任何 `T3` 顶点（ $d_K=3, t_3=1$ ）均无 3-度邻点。
3. **新引理 B（`BadFixedColorExtension` 推论）**：任何 3-度且 $g=0$ 的顶点不能有 $\ge 2$ 个坏核心邻点（消灭 `a=0,b=3` 与 `a=1,b=2`，见 `Core3Ext.lean`）；注：早期笔记提及的通用 `B3 -- bad -- B3` 在最终 36 倍放电中无需使用，仅在 `BridgeExt.lean` 中形式化了带公共 1-线串的 `no_B3_B3_shared_bad_with_oneThread`。
4. **新引理 C（轻 3-度点 `L3` 双色约化）**：每个 `L3` 顶点至多通过 1-线串连接 1 个 `L3` 顶点（见 `BridgeExt.lean`；早期笔记提及的 `G32 -- L3` 与 `S3_2 -- L3` 在最终 36 倍放电中无需使用，未做形式化）。
5. **新引理 D（通用桥接引理 `OneThreadBridge` / `BridgeTo33` / `TwoThreadBridge`）**：
   - 任何两个桥灵活顶点（`B3`、`T21`、`L4`）之间不能以 1-线串相连，也不能以 1-线串连向 `L3`；
   - 任何两个 `T21` 顶点之间不能以 2-线串相连。
6. **新引理 E（`T3` 邻接限制）**：无相邻 `T3 -- T3`、无 `T3 -- T21`、无 `T3 -- S3_2`、且每个 `T20` 至多相邻 1 个 `T3`。

**LP 验证结果**：仅用上述 100% 证明的引理，在核心子图 $K = G - X$ 上存在精确有理放电规则将阈值从 **$\frac{12}{5} = 2.4000$** 严格推进至 **$\frac{22}{9} \approx 2.4444$**（推论：所有围长 $\ge 11$ 的平面图均满足 PCF $\kappa_G$-可选择性，比 2026.08 论文的围长 $\ge 12$ 严格推进 1 档）。

---

## 二、阶段 B：Lean 4 模块化形式化进度记录

### 初始模块规划（早期设计草稿；实际拆分后的最终目录结构见 `README.md` 与 `SUMMARY.md`）
- `LeanResearch/Proposal3/Basic.lean`：核心子图 `MadLt` 求和不等式、`PCFRepSystem`（Lemma 2.1）、`C5Characterization`（Lemma 2.3）、`MinimalCounterexample` 与通用 `AdmissibleColoring` 扩展引擎。
- `LeanResearch/Proposal3/CoreStructure.lean`：小图情形、1-度点邻点 $\ge 4$、4-点延拓（同时排除 $4^+$-线串与 $\ge 6$ 圈）、线串端点相异、坏点存在 $3^+$-核心邻点、核心度计数 $n_1 + n_{2^+} \le k - 2$。
- `LeanResearch/Proposal3/BadAndThreads.lean`：坏点无 1-线串、坏点双色延拓与定色延拓、无相邻坏点、好 $q=3$ 含 $2^+$-线串的完整结构约束（Corollary 3.9）。
- `LeanResearch/Proposal3/Discharging12_5.lean`：基线定理 `MadLt G 12 5` 在 $K = G - X$ 上的完整无 `sorry` 放电证明。
- `LeanResearch/Proposal3/Beyond12_5.lean`：新引理 A–E 与精确有理放电规则，证明突破性定理 `MadLt G 22 9`。
- `LeanResearch/Main.lean`：总入口与公理核验（`#print axioms`）。

### 编译验证流水日志
- **[2026-11-24 18:05]** `LeanResearch/Proposal3/Basic.lean` 编译通过（0 错误、0 告警、0 `sorry`）：完成 `MadLt.induce`、`mad_core_sum_lt`、`MadLt.mono` 与 `exists_pcfRep`（Lemma 2.1 充分方向）。
- **[2026-11-24 18:12]** `LeanResearch/Proposal3/Admissible.lean` 编译通过（0 错误、0 告警、0 `sorry`）：完成 `exists_c5_cycle`、`c5_pcf_colorable_of_ne`（Lemma 2.3）、`c5_admissible_coloring`、`MinimalCounterexample` 强归纳及 `exists_admissible_coloring_avoid`。
- **[2026-11-24 18:13]** 开始编写 `LeanResearch/Proposal3/CoreStructure.lean`。

- **[2026-11-24 18:23]** `LeanResearch/Proposal3/CoreStructure.lean`（1621 行）通过 `lake build`（0 错误、0 警告、0 `sorry`）：完成 `card_ge_four`、Lemma 3.1 (`leaf_neighbor_deg_ge_four`)、`no_four_path_of_deg_two`、`exists_deg_ge_three`、`no_two_thread_same_anchor`、`no_three_thread_same_anchor` 与 Lemma 3.3(i) (`no_three_vertex_two_thread`)。
- **[2026-11-24 18:28]** 编写 `LeanResearch/Proposal3/ThreadDefs.lean`：在零辅助图核心子图 `K = G - X` 上建立 `coreVerts`/`coreDeg`/`IsBad`/`IsGood`、`1-/2-/3-`线串起点划分、线串锚点二元关系 `IsThreadAnchor` 及其精确双计数恒等式（`card_threadAnchors_eq_two`、`card_anchored_degTwo_eq`），以及 `exists_pcfRep` 通用单点下界与双计数引擎。
- **[2026-11-24 18:51]** `LeanResearch/Proposal3/ThreadDefs.lean` 与 `LeanResearch/Proposal3/BadAndThreads1.lean`（2400 行）双双零错误、零警告、零 `sorry` 通过 `lake build`！已内核核验 Lemmas 3.4–3.8（含全域 `mad < 5/2` 升级版 Lemma 3.5 及可复用 `bad_fixed_color_extension`）。
- **[2026-11-24 19:21]** 🎉 **里程碑 1 达成**：`LeanResearch/Proposal3/BadAndThreads2.lean`（2850 行，Lemmas 3.9–3.10 与 Corollary 3.11）及 `LeanResearch/Proposal3/Discharging12_5.lean`（214 行，零辅助图整数放电主定理 `pcf_kappa_choosable_mad_12_5`）双双以 **0 错误、0 警告、0 `sorry`** 通过 Lean 4 内核编译！已完整形式化 2026 年 8 月 SOTA $\mathrm{mad}(G) < \frac{12}{5}$。
- **[2026-11-24 19:22]** 启动 **里程碑 2（突破 $\frac{12}{5} \to \frac{22}{9}$，平面图围长 $12 \to 11$ ）**：经 `verify_22_9_minimal.py` 穷举验证，放大 36 倍的整数放电规则仅需 5 组极简新引理（A：`3`-线串单点 $\le 1$ 消灭 8 个 $q=4$ 配置；B：含叶 $a+b=3$ 消灭与 $3$-度点至多 $1$ 个坏邻点；C：`L3` 至多 $1$ 个 `L3` 邻点；D：`B3`/`T21` 的 `1`-线串与 `2`-线串桥接排除；E：`t3_fixed_color_extension` 一举消灭 `T3--T3`、`T3--T21`、`T3--(q=3,a=2,g=1)` 与 `T3--T20--T3`）。开始模块化编写 `ThreeThreadExt.lean`、`Core3Ext.lean`、`BridgeExt.lean` 与 `Discharging22_9.lean`。
- **[2026-11-24 19:48]** 里程碑 2 并行推进捷报：
  - `LeanResearch/Proposal3/BeyondDefs.lean`（293 行）0 错误、0 警告、0 `sorry` 通过 `lake build`；
  - `LeanResearch/Proposal3/Core3Ext.lean`（1,577 行，引理 B：`no_leafy_coreDeg3_all_a_b_except_L4` 与 `deg_three_no_good_at_most_one_bad`）0 错误、0 警告、0 `sorry` 通过 `lake build`；
  - `LeanResearch/Proposal3/ThreeThreadExt.lean`（1,360 行，纯组合 `threeThreadGoodCols`、`t3_fixed_color_extension`、`t21_fixed_color_extension`、`s32_a2_fixed_color_extension` 及引理 E0 `no_T3_adj_deg_three`）0 错误、0 警告、0 `sorry` 通过 `lake build`。
- **[2026-11-24 20:09]** `LeanResearch/Proposal3/Q4Ext.lean`（2,344 行，引理 A 推论 `q4_three_thread_good_bound`，一次性消灭全部 8 个 $q=4$ 高代价阻塞配置）0 错误、0 警告、0 `sorry` 通过 `lake build`。
- **[2026-11-24 20:45]** `LeanResearch/Proposal3/T3Adjacency.lean`（1,153 行，引理 E1 `no_T3_adj_T3`）与 `LeanResearch/Proposal3/T3Adjacency2.lean`（2,949 行，引理 E2–E4：`no_T3_adj_T21`、`no_T3_adj_S3_2_a2`、`no_T3_T20_T3`）双双以 **0 错误、0 警告、0 `sorry`** 通过 `lake build`。
- **[2026-11-24 20:55]** `LeanResearch/Proposal3/ThreadPartition.lean`（436 行，线串三分计数与 36 倍参数化转权 `wThread`）与 `LeanResearch/Proposal3/BridgeExt.lean`（7,670 行，引入 `IsL4` 与 `IsPoor1Ext = {L3, B3, T21, L4}`，完成引理 C & D 全部 5 条桥接禁令 `L3_at_most_one_L3_nbr`、`no_B3_one_thread_Poor1Ext`、`no_T21_one_thread_Poor1Ext`、`no_L4_one_thread_Poor1Ext`、`no_T21_two_thread_T21`）双双以 **0 错误、0 警告、0 `sorry`** 通过 `lake build`。
- **[2026-11-24 21:01]** 🎉🎉 **里程碑 2 全面达成**：`LeanResearch/Proposal3/Discharging22_9.lean`（466 行）与总入口 `LeanResearch/Main.lean`（52 行）以 **0 错误、0 警告、0 `sorry`** 通过 Lean 4 内核编译！正式完成 **`MadLt G 22 9`（ $\mathrm{mad}(G) < \frac{22}{9}$，平面图围长下界推进至 $g \ge 11$ ）** 的完整机器形式化证明，全项目 20 个 `.lean` 文件共计 **28,073 行**。
- **[2026-11-24 21:09]** **全项目构建与公理终审通过**：
  - `lake build`（3,318 jobs）退出码 `0`，全项目 **0 错误、0 警告、0 `sorry`**；
  - 静态扫描全项目代码区 0 处 `sorry` / `admit` / 自定义 `axiom`；
  - `#print axioms` 内核实测输出：
    - `'LeanResearch.Main.proposal3_baseline_12_5' depends on axioms: [propext, Classical.choice, Quot.sound]`
    - `'LeanResearch.Main.proposal3_main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`
    - `'LeanResearch.Proposal3.pcf_kappa_choosable_mad_12_5' depends on axioms: [propext, Classical.choice, Quot.sound]`
    - `'LeanResearch.Proposal3.pcf_kappa_choosable_mad_22_9' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - 已生成最终研究总结报告 `SUMMARY.md`。
- **[2026-11-24 21:50]** **独立审查与仓库收尾清理完成**：
  - 删除默认模板残留 `LeanResearch/Basic.lean` 及 4 处全项目零引用死代码（`listMult`、`degTwoNbrs_card_eq`、`longThreadNbrs_card_eq`、`IsPoor1`），清理 `CoreStructure.lean:1312` 未使用变量绑定；
  - 将 `instDecidablePredIsBad` / `instDecidablePredIsGood` 下沉至 `ThreadDefs.lean`，使里程碑 2（`BeyondDefs.lean` → `Discharging22_9.lean`）与里程碑 1（`Discharging12_5.lean`）在依赖图上彻底解耦；
  - 在 `LeanResearch/Main.lean` 增补教科书密度等价桥梁 `madLt_iff_edgeFinset` 与任意颜色类型主定理 `proposal3_main_theorem_any_color`；
  - 全面同步 8 处源码 docstring、`README.md`、`SUMMARY.md`、`PROPOSALS.md` 与 `RESEARCH_LOG.md`（统一 $d_K$ / $n_{\text{leaf}}$ / `G32` / `S3_2` 记号）；
  - 全量验证通过：`lake build`（3,316 jobs，19 文件 28,141 行）0 错误 0 警告、`lake env leanchecker LeanResearch.Main` 退出码 `0`、全部 4 个导出定理 `#print axioms` 均仅依赖 `[propext, Classical.choice, Quot.sound]`，并完成首次干净的 `git commit`。
