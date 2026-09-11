# 选择公理推出一般良序定理

本文归纳已经完成的本地证明，解释数学构造，不列证明助手操作。
目标是：对任意集合 \(A\)，存在关系 \(R\)，使 \((A,R)\) 成为良序集。
构造路线是固定选择关系，收集所有按它选择元素的部分良序，证明这些良序按初段相容，
然后取并集；若并集尚未覆盖 \(A\)，就能继续扩张，从而产生矛盾。

## 1. 非严格关系与严格前驱

脚本中的 \(\operatorname{Rel}(x,r,y)\) 表示 \((x,y)\in r\)，下文记作 \(x\le_r y\)。
这里的 \(r\) 是**非严格**关系：在其定义域 \(s\) 上自反、反对称、传递且任意两点可比。
\(\operatorname{WellOrder}(s,r)\) 还要求每个非空子集 \(B\subseteq s\) 都有最小元，
即存在 \(m\in B\)，对所有 \(b\in B\) 有 \(m\le_r b\)。
构造中另外要求 \(r\subseteq s\times s\)，排除定义域以外的多余关系对。

对 \(x\in s\)，定义其**严格前驱集合**
\[
P_{s,r}(x)=\{u\in s:u\le_r x\ \land\ u\ne x\}.
\]
记 \(u<_r x\) 为 \(u\le_r x\land u\ne x\)；所以 \(x\notin P_{s,r}(x)\)，而含端点的初段是 \(P_{s,r}(x)\cup\{x\}\)。
不能直接把 \(\{u\in s:u\le_r x\}\) 当作选择步骤中已经选走的集合，否则会误删 \(x\) 自身。
脚本在分离谓词中使用的无关存在量词包装不改变上述集合的数学含义。

称 \(d\subseteq s\) 向下封闭，是指 \(x\in d,\ y\in s,\ y\le_r x\) 蕴含 \(y\in d\)。
本文的“初段”允许是空集或整个定义域，不专指真初段。

## 2. 一次固定选择关系

将选择公理应用于 \(\operatorname{Pow}(A)\)，得到对 \(A\) 的所有非空子集统一作选择的见证。
本地脚本先由该公理取得一个集合 \(Y\)，使每个非空 \(B\subseteq A\) 恰有一个元素满足
\[
Q_Y(u,B)\quad\Longleftrightarrow\quad
\exists t\,\bigl((u\in B\land B\in t)\land(u\in t\land t\in Y)\bigr).
\]
再用分离构造实际的关系图
\[
c=\{(B,u)\in\operatorname{Pow}(A)\times A:Q_Y(u,B)\}.
\]
由于 \(Q_Y(u,B)\) 蕴含 \(u\in B\)，图的取值确实属于被选择的集合。
由公理见证的唯一性可得：对每个非空 \(B\subseteq A\)，存在 \(v\in B\)，满足
\[
\forall u\quad
\bigl[(u\in B\land\operatorname{Rel}(B,c,u))\ \Longleftrightarrow\ u=v\bigr].
\]
这就是已证明的 `xChoiceRelation`，不是额外假设一个选择函数公理。
下文用 \(c(B)\) 简写这个唯一值；实际形式化使用的是关系 \(c\)，没有引入新的函数符号。
不定义也不使用 \(c(\varnothing)\)。

此后始终固定同一个 \(c\)。不同部分良序之间的比较依赖于这一点：
如果两次面对同一个剩余集合，就必须选中同一个元素。

## 3. 有界的选择相容良序族

称 \((s,r)\) 与 \(c\) 相容，当它满足以下四项：

1. \(s\subseteq A\)；
2. \(r\subseteq s\times s\)；
3. \(\operatorname{WellOrder}(s,r)\)；
4. 对每个 \(x\in s\)，有 \(\operatorname{Rel}(A\setminus P_{s,r}(x),c,x)\)。

第四项表示：排在 \(x\) 前面的元素全部移除后，固定的选择关系恰好选中 \(x\)。
这里 \(x\in A\setminus P_{s,r}(x)\)，所以被选择的集合非空，唯一性条件可以合法使用。
剩余集合取自整个 \(A\)，不是仅从当前定义域 \(s\) 中取差集。

令
\[
\mathcal F=\{(s,r)\in\operatorname{Pow}(A)\times\operatorname{Pow}(A\times A):
                 (s,r)\text{ 满足上述四项}\}.
\]
因为 \(r\subseteq s\times s\subseteq A\times A\)，这个界包含全部所需候选。
因此 \(\mathcal F\) 由幂集、笛卡尔积和分离得到，是一个集合；
没有使用无界的“所有良序的类”，也没有预先假设存在 \(A\) 上的良序。

空关系在空集上是良序：序的条件真空成立，而空集没有非空子集。
相容条件也真空成立，所以 \((\varnothing,\varnothing)\in\mathcal F\)。
这给出族的起点，并保证构造不需要先选出 \(A\) 的某个元素。

## 4. 在末端添加一个新元素

设 \((s,r)\in\mathcal F\)，且 \(A\setminus s\ne\varnothing\)。
取 \(z=c(A\setminus s)\)，于是 \(z\in A\) 且 \(z\notin s\)，定义
\[
s^+=s\cup\{z\},\qquad r^+=r\cup(s^+\times\{z\}).
\]
在关系图有界的前提下，这正是脚本的 \(\operatorname{ordadd}(s,r,z)\)。
它保留旧关系，使每个旧元素小于新点，并包含 \((z,z)\)；
没有从 \(z\) 指向旧元素的关系对。

因此全序性保持：旧点之间沿用原序；新点是最大元；
传递性在终点为 \(z\) 时直接成立，终点为旧点时则全部退回原序。
对非空 \(B\subseteq s^+\)，若 \(B\cap s\ne\varnothing\)，取其原序最小元，
它也小于可能出现的 \(z\)；否则 \(B=\{z\}\)，最小元就是 \(z\)。
所以 \(r^+\) 确实是良序，而非仅仅一个全序。

更重要的是，直接由关系定义可得
\[
P_{s^+,r^+}(x)=P_{s,r}(x)\quad(x\in s),\qquad P_{s^+,r^+}(z)=s.
\]
旧点的选择条件不变，新点的选择条件恰是 \(\operatorname{Rel}(A\setminus s,c,z)\)。
同时 \(s^+\subseteq A,\ r^+\subseteq s^+\times s^+\)，故 \((s^+,r^+)\in\mathcal F\)。
这说明每个尚未覆盖 \(A\) 的族成员都可扩张。

## 5. 两个相容良序为何必按初段比较

取 \((s,r),(t,q)\in\mathcal F\)。要证明的是：其中一个定义域是另一个的向下封闭子集，
而且两种关系在较小定义域上完全一致，不只是存在一个抽象的序同构。
同一良序内部的前驱集合可比，不能替代这里的跨良序论证。

### 5.1 用完整前驱历史定义共同部分

依实际比较脚本，定义
\[
D=\{x\in s:\ \forall v\in s,
 v\le_r x\Rightarrow
 (v\in t\land P_{s,r}(v)=P_{t,q}(v))\}.
\]
这个定义在书写上偏向 \(s\)，但下面会证明它在两边都是初段。
它检查从开头到 \(x\) 的**每个点**，包括 \(x\) 自身，而不是只检查 \(x\) 的前驱集合。
单独知道两个端点有同一个前驱集合，并不能说明这个集合内部的排列相同；
完整历史正是防止遗漏关系一致性的条件。

首先，\(D\subseteq s\)；若 \(x\in D\)，由 \(x\le_r x\) 可得
\[
x\in t,\qquad P_{s,r}(x)=P_{t,q}(x).
\]
所以也有 \(D\subseteq t\)。再逐项验证：

1. **在 \(s\) 中向下封闭。** 若 \(x\in D,\ y\le_r x\)，则每个 \(v\le_r y\)
   都由传递性满足 \(v\le_r x\)，从而继承 \(x\) 的历史条件，故 \(y\in D\)。
2. **在 \(t\) 中向下封闭。** 若 \(x\in D,\ y\in t,\ y\le_q x\)，
   当 \(y=x\) 时结论直接成立；否则 \(y\in P_{t,q}(x)=P_{s,r}(x)\)，
   转回第一项即可得到 \(y\in D\)。
3. **关系在 \(D\) 上一致。** 对 \(u,v\in D\)，若 \(u\ne v\)，则
   \(u\le_r v\) 等价于 \(u\in P_{s,r}(v)\)，再等价于 \(u\in P_{t,q}(v)\)，
   即 \(u\le_q v\)；若 \(u=v\)，两边都由自反性成立。

### 5.2 若两边都有剩余，下一点只能相同

反设 \(s\setminus D\) 与 \(t\setminus D\) 均非空。
由各自的良序性，取它们的最小元 \(x\) 与 \(y\)。证明
\[
P_{s,r}(x)=D=P_{t,q}(y).
\]
以左侧为例，两个包含关系都需要论证：

- 若 \(u<_r x\) 但 \(u\notin D\)，则 \(u\in s\setminus D\)；
  \(x\) 的最小性给出 \(x\le_r u\)，与 \(u<_r x\) 及反对称性矛盾。
- 若 \(d\in D\)，则 \(d\ne x\)。全序性保证 \(d\le_r x\) 或 \(x\le_r d\)；
  后者会由向下封闭性推出 \(x\in D\)，矛盾，故 \(d<_r x\)。

右侧完全同理。于是相容性使 \(x,y\) 都被 \(c\) 从同一个集合 \(A\setminus D\) 选出。
它们确实都属于此集合，因此固定选择的唯一性给出 \(x=y\)，记这个共同点为 \(m\)。

现在不是假设存在一个“更大的最大共同初段”，而是直接检查定义，推出 \(m\in D\)：
对任意 \(v\in s\) 且 \(v\le_r m\)，若 \(v=m\)，它属于 \(t\)，且两边前驱都等于 \(D\)；
若 \(v\ne m\)，则 \(v\in P_{s,r}(m)=D\)，由 \(v\in D\) 已知 \(v\in t\) 且两边的严格前驱集合相等。
所以 \(m\) 满足 \(D\) 的全部定义条件，与 \(m\in s\setminus D\) 矛盾。

因此至少一个补集为空，即 \(D=s\) 或 \(D=t\)。
结合向下封闭性与关系一致性，得到所需初段比较；
若 \(s=t\)，再由关系图有界性得到 \(r=q\)。
这对应 `xCompatibleInitialComparison`，并未调用一个未经证明的良序比较定理。

## 6. 取并集：关系一致、良序与前驱保持

收集族成员的定义域与关系图，并令
\[
U=\bigcup_{(s,r)\in\mathcal F}s,\qquad
R=\bigcup_{(s,r)\in\mathcal F}r.
\]
这些都是集合；也可先在 \(\operatorname{Pow}(A)\) 和 \(\operatorname{Pow}(A\times A)\)
中分离出相应分量再取并集。显然 \(U\subseteq A,\ R\subseteq U\times U\)。

### 6.1 已进入某个成员的点不会获得新的前驱

固定 \((s,r)\in\mathcal F\) 与 \(y\in s\)。若 \(x\le_R y\)，
则有某个 \((t,q)\in\mathcal F\) 见证 \(x\le_q y\)，且图有界性保证 \(x,y\in t\)。
比较这两个成员：

- 若 \(s\) 是 \(t\) 的初段，因 \(y\in s\)，向下封闭性给出 \(x\in s\)，再由关系一致性得 \(x\le_r y\)。
- 若 \(t\) 是 \(s\) 的初段，则 \(x,y\in t\subseteq s\)，同样由关系一致性得 \(x\le_r y\)。

反向由 \(r\subseteq R\) 立即成立。因此对 \(y\in s\)，
\[
x\le_R y\ \Longleftrightarrow\ x\le_r y,\qquad
P_{U,R}(y)=P_{s,r}(y).
\]
特别地，\(R\) 限制到 \(s\times s\) 恰好是 \(r\)，且 \(s\) 在并集中向下封闭。
这里证明了“不新增前驱”，比仅仅保留旧关系更强。

### 6.2 并集是全序

任取 \(x,y\in U\)，分别找包含它们的成员；初段比较保证较大成员同时包含两点。
该成员中的可比性和自反性传入 \(R\)，反对称性也由上面的限制一致性退回该成员证明。
若 \(x\le_R y\le_R z\)，取一个包含 \(z\) 的成员，
连续两次使用“不新增前驱”，把 \(y,x\) 和两条关系都拉回该成员。
原序的传递性给出 \(x\le_R z\)。故 \(R\) 是 \(U\) 上的全序。

### 6.3 每个非空子集都有最小元

取任意非空 \(B\subseteq U\)。取一个 \(b\in B\)，再取包含 \(b\) 的成员 \((s,r)\)。
于是 \(B\cap s\ne\varnothing\)，可在原良序中取其最小元 \(m\)。
对任意 \(n\in B\)，若 \(n\in s\)，原最小性给出 \(m\le_R n\)。
若 \(n\notin s\)，并集全序性给出 \(m\le_R n\) 或 \(n\le_R m\)；
后者因 \(m\in s\) 和“不新增前驱”而推出 \(n\in s\)，矛盾。
所以 \(m\) 是整个 \(B\) 的最小元，得到 \(\operatorname{WellOrder}(U,R)\)。
这里没有假设 \(B\) 整体包含于某个成员，也没有对任意良序族直接断言其并仍是良序。

### 6.4 选择相容性也传到并集

对任意 \(x\in U\)，取包含 \(x\) 的成员 \((s,r)\)。前驱保持给出
\[
A\setminus P_{U,R}(x)=A\setminus P_{s,r}(x),
\]
故该成员的选择条件正是并集的选择条件。
结合定义域界、关系图界和良序性，四项条件全部成立，即 \((U,R)\in\mathcal F\)。
相关结论包括 `xChainUnionWellOrder` 和 `xChainUnionPredecessorSet`。

## 7. 扩张反证：并集必须穷尽 \(A\)

若 \(U\ne A\)，由 \(U\subseteq A\) 得 \(A\setminus U\ne\varnothing\)。
使用此前固定的 \(c\) 取 \(z=c(A\setminus U)\)，有 \(z\in A\setminus U\)。
由于已经独立证明 \((U,R)\in\mathcal F\)，第 4 节的扩张结论适用，得到
\[
\bigl(U\cup\{z\},\operatorname{ordadd}(U,R,z)\bigr)\in\mathcal F.
\]
可是 \(U\) 按定义包含每个族成员的定义域，因此 \(z\in U\)，与 \(z\notin U\) 矛盾。
所以 \(U=A\)，并集关系 \(R\) 就是所求的 \(A\) 上良序。

若 \(A=\varnothing\)，直接取 \(R=\varnothing\) 即可；上述统一构造也给出
\(\mathcal F=\{(\varnothing,\varnothing)\}\) 和 \(U=R=\varnothing\)，从不向空集要求选择值。
整个论证不需要佐恩引理、预先给定的超限枚举，或未经证明的最大良序存在性。
“并集是族成员”先于扩张反证得到，故也没有以穷尽结论反过来证明并集相容的循环。

## 8. 本地证明对应

- [选择关系](../work/zfc-choice-function.mjs)：由选择公理见证分离出关系图。
- [末端扩张](../work/zfc-wellorder-extension.mjs)：扩张良序性与新旧点的严格前驱。
- [相容族条件](../work/zfc-wellorder-family.mjs)：有界性、空成员和扩张保持。
- [共同历史比较](../work/zfc-wellorder-comparison.mjs)：有界族定义与跨良序初段比较。
- [并集与穷尽](../work/zfc-wellorder-union.mjs)：并集良序、前驱保持及最后的反证。
- [完成记录](../work/zfc-wellorder-continuation.md)：各阶段已在实际 UI 验证并通过 `vwo` 门；
  最终 `xWellOrderingTheorem` 为 `Vx:Er:WellOrder(x,r)`，对应 bigpack p54。
