# AI + Lean 4 自主攻关候选课题提案（PROPOSALS）

本文档围绕「**布尔函数/电路局部收缩**」「**在线算法竞争比（势函数法）**」「**极值图论（放电法）**」三个方向，在核验截至 **2026 年 11 月** 的最新文献进展与开放状态后，各遴选出 **1 个**最适合「AI 搜索（LP / 势函数 / 放电规则 / 有限情形自动化）+ Lean 4 形式化零信任验证」的候选课题。所有三个课题的核心模型均控制在 **30–48 行 Lean 4 代码** 内（对应命题定义见 [`LeanResearch/Proposals.lean`](LeanResearch/Proposals.lean)），不依赖庞大前置理论。

> **执行结果注记**：最终选定 **课题 3** 完成攻关，已在 [`LeanResearch/Main.lean`](LeanResearch/Main.lean) 中零 `sorry` 证得基线定理 $\operatorname{mad}(G) < \frac{12}{5}$（`proposal3_baseline_12_5`）与突破主定理 $\operatorname{mad}(G) < \frac{22}{9}$（`proposal3_main_theorem`）；未选定的课题 1、课题 2 以及课题 3 的远景猜想 $\operatorname{mad}(G) < \frac{5}{2}$ 在 `Proposals.lean` 中以纯 `Prop` 定义保留。

---

## 一、三课题横向对比总览

| 维度 | 课题 1：De Morgan 公式局部语法收缩指数 | 课题 2：确定性抢占式加权 FIFO 缓冲区管理 | 课题 3：稀疏图恰当无冲突 $\kappa_G$-可选择性 |
| :--- | :--- | :--- | :--- |
| **所属方向** | 布尔函数 / 电路局部收缩 | 在线算法竞争比（势函数法） | 极值图论（放电法） |
| **Lean 4 模型行数** | ~46 行（诱导公式树 + 截断局部形状） | ~34 行（`List ℚ` + `List.Sublist`） | ~28 行（`SimpleGraph V` + 纯整数 `mad`） |
| **当前 SOTA** | $\gamma = \frac{5-\sqrt{3}}{2} \approx 1.63397$（Paterson–Zwick 1993；对应确定性 `#SAT` 规模 $n^{2.63}$，Chen–Kabanets–Saurabh 2016） | 确定性竞争比上界 $\sqrt{3} \approx 1.73205$（Englert–Westermann, *Algorithmica* 2009）；下界 $1.419$（Kesselman et al. 2005） | $\operatorname{mad}(G) < \frac{12}{5} (= 2.4)$（Lu–Ying–Song, Aug 2026, `arXiv:2608.29375`） |
| **预期目标定理** | 证得有限深度局部势函数满足 $\gamma > \frac{5-\sqrt{3}}{2}$（目标 $\gamma \ge 1.66\text{–}1.72$） | 证得新确定性在线算法满足竞争比 $c < \sqrt{3}$（阶段目标 $c \le 1.725$，冲击 $c \le 1.70$） | 将 $\kappa_G$-可选择性阈值推至 $\operatorname{mad}(G) < \frac{5}{2} (= 2.5)$（进阶 $\frac{18}{7}$） |
| **理论安全边际** | **极高**：真实收缩上界已知为 $\Gamma = 2$（Håstad 1998; Tal 2014），必然存在上升空间 | **高**：即使经典的 $\text{PG}_\beta$ 算法族自身下界也仅为 $1+\frac{1}{\sqrt{2}} \approx 1.7071 < \sqrt{3}$ | **极高**：猜想断言对一切连通 $G \not\cong C_5$ 均成立（无高 `mad` 反例墙） |
| **AI 探索核心引擎** | 深度 3–4 局部子树模式枚举 + LP 最大化漂移率 $\gamma$ | 保序匹配势函数参数化 + LP / CEGIS 联合搜索阈值与势能权重 | 局域低度可约构型搜索 + LP 自动求解有理放电规则 |
| **Lean 4 证明主力** | 有限局部邻域迁移分情况 + `linarith` / `decide` | 步进摊还不等式 $\text{opt}(t)+\Delta\Phi \le c\cdot\text{alg}(t)$ + `linarith` | `Finset` 局部计数 + Hall / 列表补色 + `omega` / `linarith` |
| **代表性学术产出** | 打破保持 11+ 年的 De Morgan 精确确定性 `#SAT` $n^{2.63}$ 瓶颈 | 打破保持 17 年的 QoS FIFO 确定性竞争比 $\sqrt{3}$ 纪录 | 刷新 2026.08 最新预印本纪录，直接导出围长 $\ge 10$ 平面图新推论 |

---

## 二、课题详述

### 课题 1：De Morgan 公式的有限深度局部语法收缩指数

- **Lean 4 命题定义**：`LeanResearch.Proposal1.Proposal1Statement`（未选定）

#### 1. 研究背景与 SOTA
在布尔公式复杂度与去随机化算法中，单变量随机限制下 De Morgan 公式的收缩行为（Shrinkage）是核心枢纽：
- **全局平均收缩（已闭合为 $\Gamma = 2$）**：Subbotovskaya (1961) 给出 $\gamma = 1.5$；Impagliazzo & Nisan (1993) 改进至 $\frac{21-\sqrt{73}}{8} \approx 1.5570$；**Paterson & Zwick (1993)**（*Random Structures & Algorithms*）引入叶节点与 **twig（双叶兄弟门）** 的加权局部势函数 $\Phi(F) = G(F) + (\sqrt{3}-1)\,T(F)$，证明了单步局部语法收缩指数 **$\gamma = \frac{5-\sqrt{3}}{2} \approx 1.63397$**。此后 Håstad (1998) 与 Tal (2014) 借助非局部子公式分解证明了全局期望收缩指数恰好为 $\Gamma = 2$。
- **局部语法收缩与精确确定性 `#SAT`（停滞于 $1.63397 \to n^{2.63}$）**：**Chen, Kabanets & Saurabh** (*ECCC TR13-150 / MFCS 2014 / Algorithmica 2016*) 将 Paterson–Zwick 的局部 twig 势函数构造化与集中化，得到了规模 $n^{1+\frac{5-\sqrt{3}}{2}-o(1)} \approx n^{2.63}$ 的 De Morgan 公式 $2^{n-n^{\Omega(1)}}$ 时间**精确确定性 `#SAT` 算法**，并在论文中显式提出核心公开问题：能否引入超越 twig 的更一般有限深度局部模式势函数以突破 $1.63397$？
- **2026 年现状**：Hatami–Hoza–Tal–Tell (*FOCS 2021*) 的 PRG 仅支持加性误差 $1/\operatorname{poly}(n)$ 的*近似*计数；**精确确定性 `#SAT` 的 $n^{2.63}$ 门槛与有限深度局部语法收缩常数 $\frac{5-\sqrt{3}}{2}$ 截至 2026 年仍未被突破**。

#### 2. 极简模型与防作弊设计（~46 行 Lean 4）
- 模型仅需递归定义的 `DeMorganFormula n`、语义求值 `eval`、二元门计数 `gateSize`（使常量和单文字均为 `0`，自然消除 $L=1$ 退化边界）、单变量限制 `restrict` 与局部自底向上语法化简 `simplify`（常量传播 + 同胞幂等/互补 + 直接吸收律）。
- **严格局部性约束**：为防止使用 Håstad 非局部全局期望“作弊”，定义了深度截断、抹除变量名的 `LocalShape d` 与 `shapeOf d`，要求势函数 `localPotential w F` 必须是各子树深度 $k$ 形状权重 `w (shapeOf k S)` 的线性求和，且与 `gateSize` 常数等价（$c_1 \cdot \text{gateSize}(F) \le \Phi(F) \le c_2 \cdot \text{gateSize}(F)$）。

#### 3. 核心难点与 AI + Lean 4 攻关路径
- **为什么 Paterson–Zwick 卡在 $\frac{5-\sqrt{3}}{2}$**：其势函数仅区分「叶」与「2-叶 twig」，在「完全二叉树（全由 twig 构成）」与「3-叶樱桃树 $((x_1 \land x_2)\lor x_3)$」之间达到精确鞍点 $\alpha = \sqrt{3}-1$。当 $x_1 = 1$ 时樱桃坍缩为新 twig，导致仅靠 1 个参数无法继续提高比率。
- **攻关路线**：将截断深度扩至 $k = 3$ 或 $4$（追踪樱桃、同型/异型父门、4-叶平衡树与梳状结构），在外部用 Python/LP 构建局部邻域转移矩阵并最大化单步平均势能降幅 $\gamma$，导出精确有理权重表 `w : LocalShape k → ℚ`；再针对重复变量同时赋值引发的耦合化简，在 Lean 4 中完成结构归纳 + 有限分情况验证。

#### 4. 预期结论与学术价值
- **预期结论**：给出显式有限深度权重表 `w`（$k \le 4$），在 Lean 4 中机器认证 $\gamma > \frac{5-\sqrt{3}}{2}$（务实目标 $\gamma \ge 1.66\text{–}1.72$）。
- **学术价值**：直接对接 Chen–Kabanets–Saurabh (2016) 的集中化去随机化框架，刷新保持十余年的精确确定性 De Morgan `#SAT` 规模纪录（$n^{2.63} \to n^{1+\gamma-o(1)}$），同时产出首个可机器复现的局部收缩势函数框架。

---

### 课题 2：确定性抢占式加权 FIFO 缓冲区管理（QoS 交换机）

- **Lean 4 命题定义**：`LeanResearch.Proposal2.Proposal2Statement`（未选定）

#### 1. 研究背景与 SOTA
网络 QoS 交换机中的抢占式加权 FIFO 缓冲区管理是最经典的纯离散在线算法问题之一：容量为 $B$ 的队列在线接收非负权重数据包 `arrive w`（满队列或任意到达时刻可按 FIFO 顺序丢弃/抢占已有包以维持长度 $\le B$），在发出事件 `deliver` 时弹出队头包并获得其权重收益，目标是最大化总吞吐收益。
- **当前最优确定性上界**：**$\sqrt{3} \approx 1.73205$**，由 **Matthias Englert & Matthias Westermann** (*ESA 2006 / Algorithmica 53(4): 523–548, 2009*) 证明。他们分析了简洁的参数化抢占贪心算法 $\text{PG}_\beta$（超越 Bansal et al., *SODA 2004* 的 $1.75$），并同时证明 $\text{PG}$ 算法族自身存在下界 **$1 + \frac{1}{\sqrt{2}} \approx 1.7071$**。
- **当前最优一般确定性下界**：**$\approx 1.419$**，由 **Alex Kesselman, Yishay Mansour & Rob van Stee** (*ESA 2003 / Algorithmica 43(1–2): 63–80, 2005*) 建立。
- **2026 年现状**：经典纯对抗确定性模型的 **$[1.419,\; \sqrt{3} \approx 1.73205]$** 区间保持 17 年未破，甚至 $\text{PG}_\beta$ 自身的 $[1.7071, 1.73205]$ 分析缝隙也未闭合。

#### 2. 极简模型（~34 行 Lean 4）
- 零度量空间、零实分析、零概率测度：缓冲区仅是 `List ℚ`，到达步的抢占规则精确等价于 `q'.Sublist (q ++ [w]) ∧ q'.length ≤ B`（天然保持 FIFO 相对次序且允许任意抢占），发送步严格弹出队头。
- 离线最优轨迹由归纳谓词 `ValidTrace B [] events optGain` 刻画；确定性在线算法 `OnlineFIFOAlg B S` 仅能依赖内部状态 `s : S` 与当前单个事件 `e` 做转移，杜绝偷看未来输入。

#### 3. 核心难点与 AI + Lean 4 攻关路径
- **核心难点**：Englert–Westermann 采用复杂的全局事件映射记账法（charging scheme），难以手工微调出超越 $\text{PG}_\beta$ 或更精细的多级抢占策略；而势函数法要求设计显式非负状态势能 $\Phi(s_A, Q_O) \ge 0$ 使每步严格满足
  $$\operatorname{gain}_{\text{OPT}}(t) + \Phi(s'_A, Q'_O) - \Phi(s_A, Q_O) \le c \cdot \operatorname{gain}_{\text{ALG}}(t).$$
- **攻关路线**：
  1. **第一阶段（算法级紧化）**：保持 $\text{PG}_\beta$ 规则，将传统 charging 记账转化为显式的保序匹配加权势函数 $\Phi(Q_A, Q_O)$，借助外部 LP / 反例驱动合成（CEGIS）在小容量 $B=2,3,4$ 与任意 $B$ 的符号不变量上同步优化参数 $\beta$ 与势能系数，争取先将 $\text{PG}_\beta$ 压至 $c \le 1.725$（逼近 $1.7071$）。
  2. **第二阶段（超越 $\text{PG}$ 家族）**：引入轻量内部状态（如队列位置感知或两级抢占阈值），通过 AI 联合搜索「策略参数 + 分段线性势函数」，冲击 $c \le 1.70$，实质突破 $\text{PG}$ 家族下界。
  3. **Lean 4 闭环**：每步摊还不等式展开后为有限个有理数大小比较分支，极易由 `linarith` / `nlinarith` 批量验证。

#### 4. 预期结论与学术价值
- **预期结论**：给出首个在 Lean 4 中完全形式化的确定性抢占式 FIFO 竞争比定理，严格改进 $\sqrt{3}$ 常数上界（对所有 $B \ge 1$ 一致成立）。
- **学术价值**：打破 2009 年以来的确定性 QoS 缓冲区管理 SOTA 纪录，并树立「AI 自动发现势函数 + Lean 4 机械认证在线算法竞争比」的标杆工作流。

---

### 课题 3：稀疏图的恰当无冲突 $\kappa_G$-可选择性（放电法）

- **Lean 4 入口**：远景猜想定义见 `LeanResearch.Proposal3.Proposal3Conjecture5_2`；已完成无 `sorry` 形式化证明的主定理见 `LeanResearch.Main.proposal3_baseline_12_5`（$\frac{12}{5}$）与 `LeanResearch.Main.proposal3_main_theorem`（$\frac{22}{9}$）

#### 1. 研究背景与 SOTA
恰当无冲突染色（Proper Conflict-Free Coloring, 简称 PCF 染色，Fabrici et al., 2023）要求在恰当点染色的基础上，每个非孤立顶点的开邻域中至少有一种颜色**恰好出现一次**。**Kashima, Škrekovski & Xu** (*Discrete Mathematics* 2026, `arXiv:2508.20521`) 提出了精准的列表长度函数：
$$\kappa_G(v) = \begin{cases} 4, & d_G(v) = 2, \\ d_G(v) + 1, & d_G(v) \neq 2, \end{cases}$$
并猜想：**除 5-圈 $C_5$ 外，一切连通图都是 PCF $\kappa_G$-可选择的**（以及稍弱的 $(\operatorname{degree}+2)$-可选择猜想）。

这是 **2026 年极值图论放电法最活跃的前沿竞速赛道**：
- **Kashima–Škrekovski–Xu** (Jan 2026, `arXiv:2601.15611`)：证得 $\operatorname{mad}(G) < \frac{18}{7}$ 保证 PCF $(\operatorname{degree}+2)$-可选择，$\operatorname{mad}(G) < \frac{10}{3}$ 保证 PCF $(\operatorname{degree}+3)$-可选择。
- **Zhijun Lu, Qirui Ying & Huimin Song** (Aug 2026, `arXiv:2608.29375`)：证得任意连通图 $G \not\cong C_5$ 若满足 **$\operatorname{mad}(G) < \frac{12}{5} (= 2.4)$**（或 $\Delta(G) \le 3$），则 $G$ 是 **PCF $\kappa_G$-可选择的**（推论：围长 $\ge 12$ 平面图成立）。
- **Huijuan Xu** (Oct/Nov 2026, `arXiv:2610.41668`)：将较弱的 PCF $(\operatorname{degree}+2)$-可选择性推进至 $\operatorname{mad}(G) < \frac{8}{3}$，同时凸显了 2-度点迫使列表大小为 4 的本质，使得 $\kappa_G$ 成为最紧致、最核心的度函数。
- **确认开放间隙**：PCF $\kappa_G$-可选择性的已知阈值停留在 **$\operatorname{mad}(G) < \frac{12}{5} (= 2.4)$**，且猜想在全图类成立（无高 `mad` 反例天花板）。

#### 2. 极简模型（~28 行 Lean 4，零平面拓扑前置）
- 完全建立在 Mathlib 现成的 `SimpleGraph V` 上，**不需要任何平面图嵌入或 Jordan 曲线定理**。
- `MadLt G p q` 采用纯自然数不等式 `q * |{(u,v) ∈ S×S | G.Adj u v}| < p * |S|` 精确刻画 $\operatorname{mad}(G) < p/q$（因为无向图有序相邻对数恒等于 $2|E(G[S])|$）。
- 利用「有限连通 2-正则 5 阶简单图唯一同构于 $C_5$」，排除 $C_5$ 仅需 1 行谓词 `¬ (Fintype.card V = 5 ∧ ∀ v, G.degree v = 2)`。
- 列表颜色域取 `Finset ℕ`（对有限图与任意类型 `α` 数学等价，避免宇宙多态噪音）。

#### 3. 核心难点与 AI + Lean 4 攻关路径
- **核心难点**：从 $\frac{12}{5} (= 2.4)$ 推进至 **$\frac{5}{2} (= 2.5)$** 时，初始电荷变为 $\operatorname{ch}(v) = 2 d(v) - 5$：1-度点电荷 $-3$、2-度点电荷 $-1$，而 3-度点电荷已为正值 $+1$。需要系统刻画极小反例中禁止出现的低度局部构型（例如特定长度的 2-度链、带多个 1-/2-度邻点的 3-/4-度蜘蛛构型等），同时避免诱导子图约化后误入例外图 $C_5$。
- **攻关路线**：
  1. **可约构型与约化补色自动化**：AI 枚举极小反例候选局部邻域，结合局部列表补色 / Hall 定理 / 辅助边收缩（保持 `mad` 不增的 Lu–Ying–Song 技巧）验证可约性，自动筛出最小充分禁用构型集。
  2. **LP 求解精确有理放电权值**：在禁用上述构型的前提下，把所有合法顶点度-邻域组合写成线性约束，用 LP 求解器秒级找出使所有顶点最终电荷 $\ge 0$ 的整数/有理放电规则（进而直接矛盾于 $\sum_v \operatorname{ch}(v) < 0$）。
  3. **Lean 4 机械验证**：将禁用构型逐条写成独立小引理，最终由 `Finset.sum` 电荷守恒恒等式 + `omega` / `linarith` 一步闭合矛盾。

#### 4. 预期结论与学术价值
- **预期结论**：形式化证明任意连通图 $G \not\cong C_5$ 只要满足 $\operatorname{mad}(G) < \frac{5}{2}$，即是 PCF $\kappa_G$-可选择的（进阶目标可继续冲击 $\frac{18}{7} \approx 2.571$，或在同一框架下顺势推进 $(\operatorname{degree}+2)$-可选择性从 $\frac{8}{3}$ 到 $\frac{14}{5}$）。
- **学术价值**：直接刷新 2026 年 8 月最新 arXiv 成果（$\frac{12}{5} \to \frac{5}{2}$）；由欧拉公式推论（围长 $\ge g$ 平面图满足 $\operatorname{mad}(G) < \frac{2g}{g-2}$），无需形式化平面拓扑即可直接得出**「所有围长 $\ge 10$ 的平面图均是 PCF $\kappa_G$-可选择的」**（原最好结果为围长 $\ge 12$），具备极高的离散数学期刊发表价值。

---

## 三、选型建议（供审计参考）

- **若优先追求“数学结构最稳 + 确定性存在上升空间 + 算法复杂度顶级背书”**：推荐 **课题 1（De Morgan 局部语法收缩）**，距离真实上界 $\Gamma = 2$ 有超过 $0.36$ 的安全空间，且直接改写 11 年未动的 `#SAT` 常数。
- **若优先追求“最纯粹的势函数摊还 + 贴近经典在线算法社区”**：推荐 **课题 2（抢占式加权 FIFO 缓冲区管理）**，模型极简（仅 `List ℚ`），天然支持「CEGIS + LP 联合合成算法与势函数」。
- **若优先追求“2026 最前沿热题 + 最低 Lean 4 工程阻力 + 最快产出可发表定理”**：推荐 **课题 3（PCF $\kappa_G$-可选择性放电法）**，Lean 模型仅 28 行、零实数、纯 `SimpleGraph` + `Finset`，且从 $\frac{12}{5}$ 到 $\frac{5}{2}$ 处于 3-度点仍带正电荷的黄金区间，极易率先拿下一血。
