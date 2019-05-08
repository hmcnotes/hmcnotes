## 第一章 模型检测介绍
**摘要** 模型检测通过状态迁移来建模动态系统从而提供一种能够使用计算机进行辅助分析的方法。模型检测的研究涉及了数理逻辑、程序语言、硬件设计以及计算机理论方面，目前工业界广泛地使用模型检测进行软硬件的验证。本章主要提供模型检测的一个简短介绍。一方面给出本书各章的线索，同时提供给尚不熟悉模型检测的读者一些必要的模型检测知识。

#### 1.1 计算机辅助验证的经验

早先Dikjstra认为每个计算机程序需要通过手工数学证明的方式来确保正确性[1]，随后的研究虽然提供了一些形式化验证方法（如McCarthy、Floyd、Hoare等的工作），但是其主要问题在于很难应用于实际当中。其实，追述到图灵的工作开始，以自动化的方式进行验证的想法就已经出现，但长期以来不被看好。图灵停机问题(Turing's halting problem)[2]以及莱斯理论(Rice's Theorem)[3]已经向人们阐释了，一般意义上通过计算机辅助方式进行验证实际是一个不可解问题。随着模型检测的出现，使得实用化的以逻辑方式进行的错误发现变为可能。此时，通过一种证伪而非直接证明正确的方式进行验证，使得验证速度有效提高，进而得以在工业界的软硬件验证中使用。模型检测通常包括以下几个组成部分：
- **建模(Modeling):** 通过状态迁移图对有限状态系统进行形式化描述。
- **规格说明(Specification):** 通过时序逻辑框架对状态迁移系统的关乎正确性的属性进行描述。
- **算法(Algorithms):** 通过决策过程确定有限状态迁移结构满足时序逻辑公式描述的模型。

假如一个系统迁移图(Kripke结构)用 $K$ 表示，规格说明通过时序逻辑公式 $\varphi$ 表示，决策过程即模型检测器（Model Checker）确定是否有 $K\models\varphi$即结构$K$是公式 $\varphi$ 表示的模型。如果 $K\nvDash\varphi$ 则模型检测其会输出一个反例作为K违反 $\varphi$ 的证据。在实际应用中，反例的生成往往比证明的过程要快很多。在具体使用模型检测方法过程中， 还需要解决以下方面的挑战：
- **算法挑战:** 需要确保模型检测算法能够扩展到实际问题的规模，即有效解决状态爆炸问题(state-explosion problem)。在实际当中，状态空间甚至可能并不是有限的。
- **建模挑战:** 所需要的模型检测框架可能超越了Kripke结构以及时序逻辑范畴 （例如无界迭代以及递归、无界数据类型、实时系统、物联网系统等等）。

#### 1.2 时序逻辑的模型检测简述
##### 1.2.1 Kripke 结构
Kripke结构是一个有限有向图，其中的顶点代表状态，边代表状态迁移，每个顶点会进行标记(label)，标记代表原子命题(atomic proposition)。通过将原子命题集 $A$ 作用在一个Kripke结构上，可以形成一个三元组的表示即 $K=\langle S,R,L \rangle$，其中S代表有限状态集，$R \subseteq S\times S$ 表示状态转移的集合，标记函数 $L: S \rightarrow 2^{A}$ 可以将每个状态关联到一个原子命题集。一个系统中的动态行为可以通过Kripke结构中图的一条路径进行表示。该路径可以是一个有限或无穷序列 $\pi=s_{0},s_{1},s_{2},...$, 其中 $(s_{i},s_{i+1})\in R (i\geq0)$，由于全序关系的保证，使得任何有限长度路径可以扩展为无穷长路径。给定一个无限长路径 $\pi$，可以用 $L(\pi)=L(s_{0}),L(s_{1}),L(s_{1}),...$ 表示原子命题集的一个无穷序列。用 $\pi^{i}=s_{i},s_{i+1},s_{i+2},...$ 表示 $\pi$ 在去除掉前 $i$ 个状态后的无限长路径。

##### 1.2.2 时序逻辑 $CTL^{*}$
$CTL^{*}$ [4]是具有路径量词的命题模态逻辑，可通过状态和时序操作进行解释，其中时序操作可以通过路径进行解释。
路径量词包括：
- $\textbf{A}$：表示从一个状态开始的每个无限长路径。
- $\textbf{E}$：表示从一个状态开始存在一个无限长路径。

时序操作符包括： (对于原子命题 *p* 以及 *q*)
- $\textbf{X}p$：*p* 在下一个状态成立。
- $\textbf{F}p$：*p* 未来在某个状态成立。
- $\textbf{G}q$：*q* 在未来的每个状态成立。
- $q\textbf{U}p$：*p* 未来在某个状态成立，在此之前 *q* 于每个状态都成立。

例如，$\textbf{F}p$ 对于路径 $\pi$ 成立当且仅当 $\pi$ 包含一个被 *p* 标记的状态，$\textbf{A}\varphi$ 在状态 $s$ 成立当且仅当 $\varphi$ 对于所有从 $s$ 开始的无限长路径都成立。

给定原子命题集 $A$ ，$CTL^{*}$ 的语法可以采用如下递归定义：
- 如果 $p \in A$ ，则 $p$ 是 $CTL^{*}$ 中的一个公式。
- 如果 $\varphi$ 以及 $\psi$ 是 $CTL^{*}$ 中的公式，则 $\varphi \vee \phi$、$\varphi \wedge \phi$、$\neg \varphi$ 、 $\textbf{A}\varphi$、$\textbf{E}\varphi$、$\textbf{X}\varphi$、$\textbf{F}\varphi$、$\textbf{G}\varphi$以及 $\psi\textbf{U}\phi$ 均为$CTL^{*}$ 中的公式。

为了进一步区分路径量词以及时序操作符，采用一个称为**状态公式**(state formulas)的 $CTL^{*}$ 专门语法子集。状态公式是原子命题与 $CTL^{*}$ 公式中以路径量词作最外层限定的公式的布尔组合。例如通过 $\textbf{A}\varphi$ 形成的状态公式，可以确认该状态公式在Kripke结构的一个状态下是否为真。对于非状态公式的其它 $CTL^{*}$ 公式则需要通过一个路径来确定真值情况。

给定一个Kripke结构 $K$、状态 $s$以及状态公式 $f$，模型检测是对于 $K$ 的决策过程，判断 $K$上的状态 $s$是否是$f$表示的模型，即$s\models f$。对于Kripke结构 $K$，如果$s\nvDash f$，模型检测算法一般会给出不满足的情况。$CTL^{*}$ 的语法如表1所示。

 **表 1 $CTL^{*}$ 语法** （$K$为Kripke结构、$\pi$为路径、$s$为一个状态、$p$是一个原子命题、$f$ 和 $g$ 为状态公式、$\phi$和 $\psi$为 $CTL^{*}$ 公式）
 |表达式|成立条件|
 |:-|:-|
 | $K,s\models p$ | 当且仅当 $p \in L(s)$ |
 | $K,s\models \neg f$ | 当且仅当 $K,s\nvDash f$ |
 | $K,s\models f \vee g$ | 当且仅当 $K,s\models f$ 或 $K,s\models g$ |
 | $K,s\models f \wedge g$ | 当且仅当 $K,s\models f$ 且 $K,s\models g$ |
 | $K,s\models\textbf{E}\varphi$ | 当且仅当存在一条开始于 $s$ 的无限长路径 $\pi$有 $K,s\models \varphi$ |
 | $K,s\models\textbf{A}\varphi$ | 当且仅当任意一条开始于 $s$ 的无限长路径 $\pi$有 $K,s\models \varphi$ |
 |  $K,\pi\models f$ | 当且仅当对于路径 $\pi$的首个状态 $s$有 $K,s\models f$ |
 | $K,\pi\models \neg \varphi$ | 当且仅当 $K,\pi\nvDash \varphi$ |
 | $K,\pi\models \varphi \vee \psi$ | 当且仅当$K,\pi\models \varphi$ 或 $K,\pi\models \psi$ |
 | $K,\pi\models \varphi \wedge \psi$ | 当且仅当$K,\pi\models \varphi$ 且 $K,\pi\models \psi$ |
 | $K,\pi\models\textbf{X}\varphi$ | 当且仅当$K,\pi^{1}\models \varphi$ |
 | $K,\pi\models\textbf{F}\varphi$ | 当且仅当存在$i \ge 0$ 使得$K,\pi^{i}\models \varphi$ |
 | $K,\pi\models\textbf{G}\psi$ | 当且仅当对于任意$i \ge 0$ 使得$K,\pi^{i}\models \psi$ |
 | $K,\pi \models \psi\textbf{U}\varphi$ | 当且仅当存在$i \ge 0$ 使得$K,\pi^{i}\models \varphi$，并且对于任意 $0\le j \lt i$ 使得$K,\pi^{j}\models \psi$ |

##### 1.2.3 时序逻辑 $CTL$
$CTL$[5]可以认为是 $CTL^{*}$ 的语法片段，其要求每个路径量词后必须紧跟一个时序操作符，给定原子命题集 $A$ ，$CTL$ 的具体定义如下：
- 如果 $p \in A$，那么$p$是一个 $CTL$公式。
- 如果  $\varphi$ 以及 $\psi$ 是 $CTL^{*}$ 中的公式，则 $\varphi \vee \phi$、$\varphi \wedge \phi$、$\neg \varphi$ 、 $\textbf{AX}\varphi$、$\textbf{EX}\varphi$、$\textbf{AF}\varphi$、$\textbf{EF}\varphi$、$\textbf{AG}\varphi$、$\textbf{EG}\varphi$、$\textbf{A}\psi\textbf{U}\phi$ 以及  $\textbf{E}\psi\textbf{U}\phi$ 均为$CTL$ 中的公式。

CTL可认为是基于合成操作符 $\textbf{AX}$、$\textbf{EX}$、$\textbf{AF}$、$\textbf{EF}$、$\textbf{AG}$、$\textbf{EG}$、$\textbf{AU}$ 以及 $\textbf{EU}$ 的命题模态逻辑。从而，$CTL$ 的每个公式以及子公式也可以认为是前述的状态公式。给定Kripke结构 $K$ 和一个 $CTL$ 公式 $\varphi$，可以通过递归的方法形成满足 $\varphi$ 的状态集 $[[\varphi]]_{k}=\lbrace s:K,s\models\varphi\rbrace$，即通过计算 $\varphi$ 的所有子公式 $\psi$的状态集合 $[[\psi]]_{k}$ 来构造。

**定理 1** [6] 存在一个 $CTL$ 模型检测算法其运行时间与Kripke结构的大小以及 $CTL$ 公式的长度线性相关 (如果其它参量是固定的)。

在$CTL$ 的标记算法中，状态集 $T=[[\textbf{EF} \varphi]]$ 可以使用如下归纳定义：
- 如果 $K,s\models \varphi$，则$s \in T$。
- 如果 $s \in T$ 并且存在一个状态 $s'\in S$ 使得 $(s',s)\in R$，则$s \in T$。
- 直到没有状态可以加入 $T$。

此时所生成的 $T$ 为通过 $\varphi$ 进行标记的最小状态集，并且对于操作符 $\textbf{EX}$ 来说可形成闭环，即 $\textbf{EF}\varphi=\lbrace \mu T: \varphi \vee\textbf{EX} T \rbrace$。

##### 1.2.4 时序逻辑 $LTL$

LTL(Linear-time Temporal Logic)[7]也可以认为是 $CTL^{*}$ 的语法片段，只是不包含路径量词 $\textbf{E}$。具体定义如下：
- 如果 $p \in A$ ，则 $p$ 是 $LTL^{-}$ 中的一个公式。
- 如果 $\varphi$ 以及 $\psi$ 是 $LTL^{-}$ 中的公式，则 $\varphi \vee \phi$、$\varphi \wedge \phi$、$\neg \varphi$ 、 $\textbf{A}\varphi$、$\textbf{E}\varphi$、$\textbf{X}\varphi$、$\textbf{F}\varphi$、$\textbf{G}\varphi$以及 $\psi\textbf{U}\phi$ 均为$LTL^{-}$ 中的公式。
- 如果 $\varphi$ 是$LTL^{-}$ 中的公式，则 $\textbf{A}\varphi$ 是$LTL^{-}$ 中的公式。

$LTL^{-}$ 中的公式 $\psi$可以用来表示一个安全属性当且仅当对于每个Kripke结构$K$有一个包含有限长度路径的集合 $\Pi_{K}(\varphi)$ 使得 $K$ 在 $\varphi$约束下的反例可以通过无限扩展 $\Pi_{K}(\varphi)$ 中的路径获得。多数 $LTL$ 会通过安全属性的组合形成活性属性（*liveness property*）[8]，并有可能需要通过无限长路径来描述反例。例如，若 $LTL$ 公式 $\textbf{GF}f$ 表示有一条无限长路径，并且状态属性 $f$ 成立无限多次，则此时用来描述反例的路径就可能不是有限长的。

**定理 2** [9] 存在一个 $LTL$ 模型检测算法其运行时间与Kripke结构的大小线性相关和 $LTL$ 公式的长度指数相关。


##### 参考文献
[1] Dijkstra, E.W.:The humble programmer. Commun. ACM15(10), 859–866(1972). </br>
[2] Turing, A.:On computable numbers, with an application to the Entscheidungsproblem. Proc. Lond. Math. Soc. 42, 230–265 (1937). </br>
[3] Rice, H.G.: Classes of recursively enumerable sets and their decision problems. Trans. Am. Math. Soc. 74, 358–366 (1953). </br>
[4] Emerson, E.A., Halpern, J.Y.: “Sometimes” and “not never” revisited: on branching versus linear-time temporal logic. J. ACM 33(1), 151–178 (1986). </br>
[5] Clarke, E.M., Emerson, E.A.: Design and synthesis of synchronization skeletons using branching-time temporal logic. In: Kozen, D. (ed.) Proceedings, Logics of Programs, York- town Heights, NY, USA, May 1981. LNCS, vol. 131, pp. 52–71. Springer, Heidelberg (1981). </br>
[6] Clarke, E.M., Emerson, E.A., Sistla, A.P.: Automatic verification of finite state concurrent systems using temporal logic specifications: a practical approach. In: Wright, J.R., Landweber, L., Demers, A.J., Teitelbaum, T. (eds.) Proceedings, Principles of Programming Languages, POPL, Austin, TX, USA, January 1983, pp. 117–126. ACM, New York (1983). </br>
[7] Pnueli, A.: The temporal logic of programs. In: Proceedings, Foundations of Computer Sci- ence, FOCS, Providence, RI, USA, October 31–November 1, 1977, pp. 46–57. IEEE, Piscat-
away (1977). </br>
[8] Alpern,B.,Schneider,F.B.:Definingliveness.Inf.Process.Lett.21(4),181–185(1985). </br>
[9]  Lichtenstein,O.,Pnueli,A.:Checkingthatfinite-stateconcurrentprogramssatisfytheirlinear
specification. In: Van Deusen, M.S., Galil, Z., Reid, B.K. (eds.) Principles of Programming Languages, POPL, New Orleans, LA, USA, January 1985, pp. 97–107. ACM, New York (1985). </br>
