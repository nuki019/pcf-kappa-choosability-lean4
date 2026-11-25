# `lean_research`：稀疏图恰当无冲突 $\kappa_G$-可选择性的 Lean 4 形式化证明

本项目基于 **Lean `v4.36.0`** 与 **Mathlib `v4.36.0`**，对稀疏图的**恰当无冲突（Proper Conflict-Free, PCF）$\kappa_G$-可选择性**完成了零 `sorry`、零自定义公理的机器形式化证明，将最大平均度（Maximum Average Degree, $\operatorname{mad}$）阈值从 2026 年 8 月文献记录 **$\operatorname{mad}(G) < \frac{12}{5}$**（Lu–Ying–Song, `arXiv:2608.29375`）严格推进至 **$\operatorname{mad}(G) < \frac{22}{9}$**。

---

## 核心主定理（`LeanResearch/Main.lean`）

对有限简单图 $G$，定义 Kashima–Škrekovski–Xu（`arXiv:2508.20521`）的列表长度函数：

$$\kappa_G(v) = \begin{cases} 4, & d_G(v) = 2, \\ d_G(v) + 1, & d_G(v) \neq 2. \end{cases}$$

本项目在 [`LeanResearch/Main.lean`](LeanResearch/Main.lean) 中导出以下全部通过 Lean 4 内核与 `leanchecker` 认证的定理：

| 定理标识符 | 内容说明 | 学术定位 |
| :--- | :--- | :--- |
| `LeanResearch.Main.proposal3_baseline_12_5` | 连通图 $G \not\cong C_5$ 且 `MadLt G 12 5`（$\operatorname{mad}(G) < \frac{12}{5}$）$\implies$ `IsPCFChoosable G (kappa G)` | 复现 Lu–Ying–Song（Aug 2026, `arXiv:2608.29375`）SOTA |
| `LeanResearch.Main.proposal3_main_theorem` | 连通图 $G \not\cong C_5$ 且 `MadLt G 22 9`（$\operatorname{mad}(G) < \frac{22}{9}$）$\implies$ `IsPCFChoosable G (kappa G)` | **严格超越 $\frac{12}{5}$，推进至 $\frac{22}{9} \approx 2.4444$** |
| `LeanResearch.Main.madLt_iff_edgeFinset` | 证明 `MadLt G p q` 与教科书标准定义 $\forall S \neq \emptyset,\; q \cdot 2|E(G[S])| < p \cdot |S|$ 严格等价 | 定义忠实度桥梁 |
| `LeanResearch.Main.proposal3_main_theorem_any_color` | 基于 `2 * (G.induce S).edgeFinset.card` 与**任意颜色类型 `α`** 的主定理等价陈述 | 面向审稿人的通用陈述 |

> **平面图推论（纸面标准推论，未形式化平面拓扑）**：由欧拉公式，任意围长 $g \ge 11$ 的平面图满足 $\operatorname{mad}(G) < \frac{2g}{g-2} = \frac{22}{9}$ 且不含 $C_5$ 分支，从而对每个连通分支应用 `proposal3_main_theorem` 即得「**所有围长 $\ge 11$ 的平面图均是 PCF $\kappa_G$-可选择的**」（将原围长下界 $12$ 推进至 $11$）。

---

## 快速构建与零信任复核

需先安装 [elan](https://github.com/leanprover/elan)（自动匹配 `lean-toolchain` 中的 `leanprover/lean4:v4.36.0`）：

```bash
# 1. 下载 Mathlib 预编译缓存（首次克隆可选，大幅加速）
lake exe cache get

# 2. 全项目构建（0 错误、0 警告、0 sorry）
lake build

# 3. 独立内核全量重验（验证 .olean 传递闭包中每一条声明）
lake env leanchecker LeanResearch.Main

# 4. 独立核验公理依赖（应仅输出 [propext, Classical.choice, Quot.sound]）
lake env lean --stdin <<'EOF'
import LeanResearch.Main
#print axioms LeanResearch.Main.proposal3_baseline_12_5
#print axioms LeanResearch.Main.proposal3_main_theorem
#print axioms LeanResearch.Main.proposal3_main_theorem_any_color
EOF
```

---

## 目录结构

```text
lean_research/
├── LeanResearch.lean                      # 顶层导入入口
├── LeanResearch/
│   ├── Proposals.lean                     # 核心已审计定义（MadLt / IsPCFColoring / IsPCFChoosable / kappa）及候选课题陈述
│   ├── Main.lean                          # 主定理出口（12/5 基线、22/9 突破、2|E(G[S])| 与任意颜色类型 α 桥梁）
│   └── Proposal3/
│       ├── Basic.lean                     # IsC5、核心子图密度上界 mad_core_sum_lt、PCF 代表系（Lemma 2.1）
│       ├── Admissible.lean                # C_5 充分引理（Lemma 2.3）、MinimalCounterexample 强归纳与容许染色引擎
│       ├── CoreStructure.lean             # 小图排除、叶邻点 ≥ 4、无 4⁺-线串、锚点互异、3-度点无 2⁺-线串
│       ├── ThreadDefs.lean                # 核心顶点 K = {d ≥ 2}、好/坏点及其可判定性、双锚点计数与双计数引擎
│       ├── BadAndThreads1.lean            # 全域 2p ≤ 5q 升级版 Lemma 3.5、坏点性质与双色/定色延拓
│       ├── BadAndThreads2.lean            # 好 d_K=3 含长线串结构约束（Lemmas 3.9–3.10, Corollary 3.11）
│       ├── Discharging12_5.lean           # 里程碑 1：5 倍整数放电证明 mad(G) < 12/5（独立于里程碑 2）
│       ├── BeyondDefs.lean                # 里程碑 2 公共谓词（T3/T21/T20/L3/B3）、五分恒等式与 1-/2-线串对端提取
│       ├── ThreeThreadExt.lean            # 引理 A 核心（3-线串单点计数 ≤ 1）、定色延拓引擎与引理 E0
│       ├── Q4Ext.lean                     # 引理 A 推论：消灭全部 8 个 d_K=4 阻塞配置（9p ≤ 22q）
│       ├── Core3Ext.lean                  # 引理 B：含叶 d_K=3 分类（仅余 L4）与 3-度 g=0 坏邻点 ≤ 1（仅余 L3/B3）
│       ├── T3Adjacency.lean               # 引理 E1：变参定色延拓与 no_T3_adj_T3
│       ├── T3Adjacency2.lean              # 引理 E2–E4：no_T3_adj_T21、no_T3_adj_S3_2_a2、no_T3_T20_T3
│       ├── BridgeExt.lean                 # 引理 C & D：IsL4 / IsPoor1Ext 与全部 5 条 1-/2-线串桥接禁令
│       ├── ThreadPartition.lean           # anchoredDegTwo 三分计数与 36 倍参数化线串转权 wThread
│       └── Discharging22_9.lean           # 里程碑 2：36 倍整数放电证明 mad(G) < 22/9（与 Discharging12_5 完全解耦）
├── paper/
│   ├── main.tex                           # 英文学术论文 LaTeX 源码（面向 arXiv math.CO / Discrete Mathematics）
│   ├── references.bib                     # 已核验的 BibTeX 文献库（14 篇文献）
│   └── main.pdf                           # 零错误零告警编译成品（24 页，含 3 张 TikZ 图与 4 张三线表）
├── SUMMARY.md                             # 完整研究总结、36 倍放电核验表与局部障碍诊断
├── RESEARCH_LOG.md                        # 全流程研究探索与编译核验日志
└── PROPOSALS.md                           # 初始三候选课题调研与选型对比
```

---

## 文档导航

- **完整研究报告与放电核验表**：[`SUMMARY.md`](SUMMARY.md)
- **探索过程与编译审计日志**：[`RESEARCH_LOG.md`](RESEARCH_LOG.md)
- **初始候选课题对比**：[`PROPOSALS.md`](PROPOSALS.md)

---

## 开源协议（License）

本项目采用 [Apache License 2.0](LICENSE) 开源协议（与 Lean 4 / Mathlib 生态一致）。
