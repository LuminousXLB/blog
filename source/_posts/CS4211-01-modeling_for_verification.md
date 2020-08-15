---
title: Modeling for Verification
category: MComp
tags: CS4211
abbrlink: bccaa338
date: 2020-08-15 11:33:29
---

1. Main issues in modeling systems for verification
2. A simple modeling language, SML
3. Key steps in model creation using SML with illustrative examples
4. Map SML to standard formalisms such as Kripke structures


> Seshia S.A., Sharygina N., Tripakis S. (2018) Modeling for Verification. In: Clarke E., Henzinger T., Veith H., Bloem R. (eds) Handbook of Model Checking. Springer, Cham. https://doi.org/10.1007/978-3-319-10575-8_3

<!-- more -->


## Introduction

**模型：**
虚拟的、理论上的系统，与真实的系统相对（汽车、Java程序）

- 分类
  - models：已有系统的模型
  - specifications / designs：准备构建的系统的模型
- formal  / informal
- 很少描述整个系统（因为太复杂），通常只关注某些部分或者特定的方面

**主要问题：**
1. 选择或者设计一个建模语言 (modeling language) ， 以及建模步骤
2. 介绍一种简单的建模语言 SML
   - 基于抽象的状态机
   - 简化不同的实际语言和形式化描述的联系
3. 通过例子展示使用 SML 建模的步骤，覆盖硬件，软件和网络物理系统


## Major Considerations in System Modeling

模型只是用于实现某个特定目标的工具。一个模型的好坏应当围绕一个特定的目标来评价。

根据不同的目标选择正确的 formalism, languages and tools.

***Formalisms*** are mathematical objects consisting of an abstract syntax and a formal semantics.
***Languages*** are concrete implementations of formalisms.

### Selecting a Modeling Formalism and Language

- Type of System
  - 离散时间系统（有限状态机、下推自动机……
  - 连续时间系统（常微分方程ODE，微分代数方程DAE
  - 并发过程
  - compositional modeling
  - 数据流系统
  - 面向场景的（消息序列图、实时序列图
  - timed and hybrid systems
  - discrete-event formalisms
  - 上述模型的概率变体（马尔可夫链
  - 博弈论、成本论变体
- Type of Property
  - 实时性？
  - 布尔性质（例如是否存在死锁）
  - ……
- Modeling the Environment
- Level of Abstraction
  - State explosion
  - 隐藏不必要的信息（理解哪些信息是真的不必要的
- Clarity and Modularity
  - 模型通常是给人看的，考虑可读性
  - 模块化
- Form of Composition
  - 系统通过组合和修改既有的模块构成
  - 这些成分之间如何交互可能决定了选择什么样的 formalism
  - 例：硬件共享一个时钟信号（同步）；分布式系统（异步）
- Computational Engines
  - 有没有合适的、可扩展的计算引擎来为这种模型驱动验证工具
  - 有限状态机：Binary Decision Diagrams (BDDs)，Boolean satisfiability (SAT) solvers
  - model-checking software and highlevel models of hardware：satisfiability modulo theories (SMT) solvers
- Practical Ease of Modeling and Expressiveness


### Modeling Languages

- Hardware description languages (HDL): Verilog, VHDL, SystemSC
- General-purpose modeling languages: UML, SysML
- Architecture Description Languages (ADL): AADL
- Simulation-oriented languages and tools: Matlab-Simulink
- Reactive programming languages
- Verification languages

### Challenges in Modeling

- 很难不出错
- 选择建模语言是一门艺术
- 即使建立好了模型也难以对模型做出评价（好、完全、一致）
- 因为模型可能是错的，要小心处理验证结果（是系统错了还是模型错了）
- 对环境建模特别枯燥易错


## Modeling Basics

SML stands for *Simple Modeling Language*

### Syntax

- SML program := \[module definition\]
- Module definition := module name + module body
- Module body := \[input : i\] + \[output : o\] + \[state : v\] + \[shared : u\] + behaviour

### Dynamics

Symbolic transition system: a tuple $(I,O,V,U, \alpha , \delta )$
- $ I,O,V,U $：输入、输出、状态、共享变量（带类型）
- $ \alpha $：初值状态谓词 $ V \cup U \rightarrow \\{0,1\\} $
- $ \delta $：状态转移关系 $ I \cup O \cup V \cup U \cup V' \cup U' \rightarrow \\{0,1\\} $
  - $V' = \\{ s' \\mid  s \in V \\}$：next-state variables
  - $U'$ 与 $V'$ 相似

- M is primitive, $(I,O,V, \phi , \alpha , \delta )$
- M is composite ...

### Modeling Concepts

#### Open and Closed Systems
- 封闭系统没有输入，开放系统有输入
- 如果有输入，就把环境做成一个和系统交互的模块，然后整体作为封闭系统进行验证。

#### Safety and Liveness
- Safety：如果对于系统的任意无限执行路径，该路径不满足$\phi$当且仅当存在一个该路径的有限前缀，该前缀不能扩展成一个满足$\phi$的无限路径，则称$\phi$是一个安全性质
  - 用模型的转换关系定义，一个违背安全性质的行为可以视为一个错误的转换
- Liveness：如果每一个有限长度的执行路径都可以被扩展成一个满足$\phi$的无限长执行路径，则称$\phi$是一个活跃性质。
  - 表示为模型中无限执行路径上的公平性条件

#### Fairness
并发系统中没有被忽视的模块，每一个模块都能有进展。
- Weak Fairness：模块执行中的一步如果不能被移出就不能**永远**启用
- Strong Fairness：模块执行中的一步如果不能被移出就不能**无限频繁**地启用

定义：如果所有模块都无限频繁地进行，那么这个复合系统的执行是**公平**的。

#### Encapsulation
模块接口包括输入输出，即在与环境交流的时候更新更新输入和输出变量。一个好的模型会把所有（且仅有）应该被环境访问的内部状态暴露出来。


#### Moore and Mealy machines
- Moore: 输出$\bigwedge_{j=1}^{m} o_j = f_j(V)$
- Moore: 输出$\bigwedge_{j=1}^{m} o_j = f_j(V, I)$


## Example

### Synchronous Circuits

数字电路：简单的芯片多处理器路由器

#### Router Design

Main function
- Direct incoming packets to correct output port

Main modules (see Fig. 3)
- Input controller根据flit的头部的目的地址请求访问输出端口
- Arbiter（仲裁者）轮询，公平地授权访问输出端口
- 当arbiter授权访问某个特定的输出端口时，发送一个信号给input controller，把flits从缓存中释放
- 同时，向encoder发送一个分配信号，encoder配置crossbar将flits路由给合适的输出端口

#### Simplifications and SML Model

简化 (see Fig. 4)
- 假设packet中的每一个flit都向arbiter发起一个请求，而不只是head flit
  - 避免跟踪flit的类别
- 假设目的地址只有2 bits（指示flit流向的输出端口）
  - 01 输出端口0
  - 10 输出端口1
  - 00 缺少请求
- 取消Encoder模块，直接用alloc信号把flits通过crossbar路由到路由器的输出端口

......


## Kripke Structures

### Transition Systems

- 有向图
  - 节点 - 状态
  - 边 - 过渡、状态转换
- 状态
  - 封装了某个时刻系统的信息
- 过渡
  - 封装了在每一个执行步骤中系统参数的变化
-

Kripke structures
- 以原子命题为结构

定义：$AP$ 是一个源自命题的非空集合。一个Kripke structure是一个用四元组 $M = (S; S_0; R; L)$定义的Transition System。
- $S$ 是状态的有限集合
- $S_0$ 是初始状态的有限集合
- $R \subseteq S \times S$ 是转换关系
  - $\forall s \in S : \exists s' \in S : (s; s') \in R$
- $L : S \rightarrow 2^{AP}$ 是标记函数，标记了每个状态中满足的原子命题

- A path of the Kripke structure
- The word on the path
- The program semantics
- describing the behavior of the modeled system in a modeling-language-independent manner

