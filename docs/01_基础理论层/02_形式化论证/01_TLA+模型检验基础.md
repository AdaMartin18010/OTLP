---
title: TLA+模型检验基础
description: TLA+形式化验证基础，包含TLA+语言、TLC模型检验器、PlusCal算法语言
version: OTLP v1.10.0
date: 2026-03-17
category: 理论基础
tags:
  - formal-verification
  - tla+
  - model-checking
  - pluscal
status: published
---

# TLA+模型检验基础

> **学习难度**: ⭐⭐⭐⭐⭐ (专家级)  
> **前置知识**: 离散数学、逻辑学、分布式系统  
> **最后更新**: 2026-03-17  

---

## 1. TLA+简介

### 1.1 什么是TLA+

**TLA+** (Temporal Logic of Actions) 是由Leslie Lamport开发的形式化规约语言，用于描述和验证并发和分布式系统。

```
┌─────────────────────────────────────────────────────────────────┐
│                     TLA+核心概念                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  TLA+ = 时序逻辑 (Temporal Logic) + 行为逻辑 (Logic of Actions)  │
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│  │   数学公式    │    │   状态机     │    │   不变式     │      │
│  │  (Formulas)  │ +  │  (State     │ +  │(Invariants) │      │
│  │              │    │   Machine)   │    │              │      │
│  └──────────────┘    └──────────────┘    └──────────────┘      │
│                                                                 │
│  用途:                                                          │
│  • 精确描述系统设计                                             │
│  • 形式化验证正确性                                             │
│  • 发现边界条件和竞争条件                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 TLA+工具链

| 工具 | 用途 | 状态 |
|------|------|------|
| **SANY** | 语法检查器 | 稳定 |
| **TLC** | 模型检验器 | 稳定 |
| **TLAPS** | 定理证明器 | 开发中 |
| **PlusCal** | 算法语言 | 稳定 |

---

## 2. TLA+基础语法

### 2.1 基本运算符

```tla
---- MODULE BasicOperators ----
EXTENDS Integers, Sequences, FiniteSets

(* 逻辑运算符 *)
LogicalOperators ==
  /\ TRUE  /\ FALSE = FALSE    (* 与 *)
  \/ TRUE  \/ FALSE = TRUE     (* 或 *)
  ~ TRUE = FALSE               (* 非 *)
  TRUE => FALSE = FALSE        (* 蕴含 *)
  TRUE <=> TRUE = TRUE         (* 等价 *)

(* 集合运算符 *)
SetOperators ==
  {1, 2, 3} \union {3, 4, 5}   (* 并集: {1, 2, 3, 4, 5} *)
  {1, 2, 3} \intersect {2, 3}  (* 交集: {2, 3} *)
  {1, 2, 3} \\ {2}             (* 差集: {1, 3} *)
  2 \in {1, 2, 3}              (* 属于: TRUE *)
  {x \in 1..10 : x % 2 = 0}    (* 集合构造: 偶数 *)

(* 时序运算符 *)
TemporalOperators ==
  [] P       (* 总是P - Globally *)
  <> P       (* 最终P - Finally *)
  P ~> Q     (* P导致Q - Leads to *)
  []<> P     (* 无限经常P *)
  <>[] P     (* 最终总是P *)

====
```

### 2.2 状态机定义

```tla
---- MODULE SimpleCounter ----
EXTENDS Integers

(* 常量 *)
CONSTANTS MinValue, MaxValue

(* 变量 *)
VARIABLE counter

(* 类型不变式 *)
TypeInvariant == counter \in MinValue..MaxValue

(* 初始状态 *)
Init == counter = MinValue

(* 行为: 增加 *)
Increment ==
  /\ counter < MaxValue
  /\ counter' = counter + 1

(* 行为: 减少 *)
Decrement ==
  /\ counter > MinValue
  /\ counter' = counter - 1

(* 下一步关系 *)
Next ==
  \/ Increment
  \/ Decrement
  \/ UNCHANGED counter  (* 不变化 *)

(* 完整规约 *)
Spec == Init /\ [][Next]_counter

(* 不变式: 计数器始终在范围内 *)
Invariant == counter \in MinValue..MaxValue

(* 活性属性: 最终可以达到最大值 *)
Liveness == <>(counter = MaxValue)

====
```

---

## 3. PlusCal算法语言

### 3.1 PlusCal简介

**PlusCal**是TLA+的伪代码语言，更容易学习和使用，然后自动转换为TLA+。

### 3.2 PlusCal示例: 互斥锁

```pluscal
---- MODULE Mutex ----
EXTENDS Integers, TLC

(* --algorithm Mutex
variables
  flag = [i \in {0, 1} |-> FALSE],  (* 两个进程的flag *)
  turn = 0;                           (* 轮到哪个进程 *)

process Proc \in {0, 1}
variable other;
begin
  Start:
    other := 1 - self;                (* 另一个进程 *)
  
  L1:                                  (* 尝试进入临界区 *)
    flag[self] := TRUE;
  
  L2:                                  (* 设置turn *)
    turn := other;
  
  L3:                                  (* 等待 *)
    await flag[other] = FALSE \/ turn = self;
  
  CS:                                  (* 临界区 *)
    skip;  (* 临界区代码 *)
  
  L4:                                  (* 退出临界区 *)
    flag[self] := FALSE;
  
  goto Start;
end process;

end algorithm; *)

(* 不变式: 两个进程不能同时在临界区 *)
MutexInvariant == 
  ~(/\ pc[0] = "CS"
    /\ pc[1] = "CS")

====
```

### 3.3 PlusCal到TLA+转换

```
PlusCal代码                    TLA+规约
───────────                    ────────
algorithm                      MODULE + 变量 + 进程
variables                      VARIABLES
process                        process实例化
begin...end                    标签定义
x := y                         x' = y
await P                        P /
if/then/else                   / 分支
while                          递归Next
```

---

## 4. TLC模型检验器

### 4.1 TLC工作原理

```
┌─────────────────────────────────────────────────────────────────┐
│                    TLC模型检验流程                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 状态生成                                                    │
│     └── 从初始状态开始                                          │
│     └── 应用Next关系生成后继状态                                │
│     └── 使用哈希表去重                                          │
│                                                                 │
│  2. 不变式检查                                                  │
│     └── 每个状态检查不变式                                      │
│     └── 失败则报告反例                                          │
│                                                                 │
│  3. 活性检查                                                    │
│     └── 检查时序属性                                            │
│     └── 使用Büchi自动机                                         │
│                                                                 │
│  4. 结果输出                                                    │
│     └── 成功: 状态数、直径等统计                                │
│     └── 失败: 错误轨迹 (trace)                                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 TLC配置

```tla
(* TLC配置文件: Mutex.cfg *)
CONSTANTS
  MinValue = 0
  MaxValue = 5

INIT Init
NEXT Next

INVARIANTS
  TypeInvariant
  MutexInvariant

PROPERTIES
  Liveness

CHECK_DEADLOCK
  TRUE

CONSTRAINT
  StateConstraint  (* 状态空间约束 *)
```

### 4.3 TLC运行命令

```bash
# 基本运行
tlc SimpleCounter.tla

# 指定配置文件
tlc -config SimpleCounter.cfg SimpleCounter.tla

# 增加内存
tlc -workers 4 -maxheap 8g SimpleCounter.tla

# 生成状态图
tlc -dump dot,actionlabels,colorize SimpleCounter.tla

# 检查特定不变式
tlc -checkpoint 0 -deadlock SimpleCounter.tla
```

---

## 5. OTLP协议的形式化规约

### 5.1 Span状态机规约

```tla
---- MODULE OTLPSpan ----
EXTENDS Integers, Sequences, TLC

(* Span状态 *)
CONSTANTS 
  SPAN_STARTING,
  SPAN_STARTED,
  SPAN_ENDED,
  SPAN_EXPORTED

(* Span变量 *)
VARIABLES 
  spanState,      (* 当前状态 *)
  spanStartTime,  (* 开始时间 *)
  spanEndTime,    (* 结束时间 *)
  spanEvents,     (* 事件列表 *)
  spanAttributes  (* 属性映射 *)

(* 类型不变式 *)
TypeInvariant ==
  /\ spanState \in {SPAN_STARTING, SPAN_STARTED, SPAN_ENDED, SPAN_EXPORTED}
  /\ spanStartTime \in Nat
  /\ spanEndTime \in Nat
  /\ spanEvents \in Seq(STRING)

(* 初始状态 *)
Init ==
  /\ spanState = SPAN_STARTING
  /\ spanStartTime = 0
  /\ spanEndTime = 0
  /\ spanEvents = <<>>
  /\ spanAttributes = [k \in {} |-> ""]

(* StartSpan操作 *)
StartSpan ==
  /\ spanState = SPAN_STARTING
  /\ spanState' = SPAN_STARTED
  /\ spanStartTime' = TLCGet("time")
  /\ UNCHANGED <<spanEndTime, spanEvents, spanAttributes>>

(* AddEvent操作 *)
AddEvent ==
  /\ spanState = SPAN_STARTED
  /\ spanEvents' = Append(spanEvents, "event_" \o ToString(Len(spanEvents)))
  /\ UNCHANGED <<spanState, spanStartTime, spanEndTime, spanAttributes>>

(* EndSpan操作 *)
EndSpan ==
  /\ spanState = SPAN_STARTED
  /\ spanState' = SPAN_ENDED
  /\ spanEndTime' = TLCGet("time")
  /\ UNCHANGED <<spanStartTime, spanEvents, spanAttributes>>

(* Export操作 *)
ExportSpan ==
  /\ spanState = SPAN_ENDED
  /\ spanState' = SPAN_EXPORTED
  /\ UNCHANGED <<spanStartTime, spanEndTime, spanEvents, spanAttributes>>

(* 下一步关系 *)
Next ==
  \/ StartSpan
  \/ AddEvent
  \/ EndSpan
  \/ ExportSpan

(* 完整规约 *)
Spec == Init /\ [][Next]_<<spanState, spanStartTime, spanEndTime, spanEvents, spanAttributes>>

(* 关键不变式 *)

(* 1. 状态机正确性 *)
StateMachineInvariant ==
  spanState = SPAN_STARTING => 
    (spanStartTime = 0 /\ spanEndTime = 0)
  
  /\ spanState = SPAN_STARTED =>
    (spanStartTime > 0 /\ spanEndTime = 0)
  
  /\ spanState = SPAN_ENDED =>
    (spanStartTime > 0 /\ spanEndTime > spanStartTime)
  
  /\ spanState = SPAN_EXPORTED =>
    (spanStartTime > 0 /\ spanEndTime > spanStartTime)

(* 2. 事件顺序: 只能在STARTED状态添加事件 *)
EventOrderInvariant ==
  Len(spanEvents) > 0 => spanState \in {SPAN_STARTED, SPAN_ENDED, SPAN_EXPORTED}

(* 活性属性: 最终应该被导出 *)
LivenessProperty == <>(spanState = SPAN_EXPORTED)

(* 公平性: 必须能结束和导出 *)
Fairness ==
  /\ SF_<<spanState>>(EndSpan)
  /\ SF_<<spanState>>(ExportSpan)

====
```

### 5.2 分布式追踪因果一致性规约

```tla
---- MODULE DistributedTracing ----
EXTENDS Integers, Sequences, FiniteSets, TLC

(* 常量 *)
CONSTANTS 
  Services,           (* 服务集合 *)
  MaxSpanId           (* 最大Span ID *)

ASSUME IsFiniteSet(Services)

(* 变量 *)
VARIABLES
  spans,              (* Span集合 *)
  parentRelations,    (* 父子关系 *)
  happensBefore       (* Happens-Before关系 *)

(* Span类型 *)
Span == [id: 1..MaxSpanId, service: Services, startTime: Nat, endTime: Nat]

(* 辅助函数: 获取Span时间 *)
SpanStart(s) == s.startTime
SpanEnd(s) == s.endTime

(* 初始状态 *)
Init ==
  /\ spans = {}
  /\ parentRelations = {}
  /\ happensBefore = {}

(* 创建Span *)
CreateSpan(s) ==
  /\ s \notin spans
  /\ s.startTime > 0
  /\ s.endTime > s.startTime
  /\ spans' = spans \union {s}
  /\ UNCHANGED <<parentRelations, happensBefore>>

(* 建立父子关系 *)
SetParent(child, parent) ==
  /\ child \in spans
  /\ parent \in spans
  /\ child.id # parent.id
  /\ parent.endTime < child.startTime  (* 父必须在子开始前结束 *)
  /\ parentRelations' = parentRelations \union {<<child, parent>>}
  /\ happensBefore' = happensBefore \union {<<parent, child>>}
  /\ UNCHANGED spans

(* Happens-Before传递性 *)
HappensBeforeTransitive ==
  /\ happensBefore' = 
      happensBefore \union
      {<<a, c>> \in spans \X spans : 
        \E b \in spans : <<a, b>> \in happensBefore /\ <<b, c>> \in happensBefore}
  /\ UNCHANGED <<spans, parentRelations>>

(* 下一步 *)
Next ==
  \/ \E s \in Span : CreateSpan(s)
  \/ \E child, parent \in spans : SetParent(child, parent)
  \/ HappensBeforeTransitive

(* 规约 *)
Spec == Init /\ [][Next]_<<spans, parentRelations, happensBefore>>

(* 关键不变式 *)

(* 1. 无循环: 父子关系无环 *)
NoCycles ==
  ~\E s \in spans : <<s, s>> \in parentRelations

(* 2. 时间一致性: 如果a Happens-Before b，则a.endTime < b.startTime *)
TimeConsistency ==
  \A a, b \in spans :
    <<a, b>> \in happensBefore => a.endTime < b.startTime

(* 3. 偏序性: Happens-Before是偏序 *)
PartialOrder ==
  /\ \A s \in spans : <<s, s>> \notin happensBefore           (* 非自反 *)
  /\ \A a, b, c \in spans :                                    (* 传递 *)
       (<<a, b>> \in happensBefore /\ <<b, c>> \in happensBefore)
       => <<a, c>> \in happensBefore

(* 活性: 可以创建完整的Trace *)
CompleteTrace ==
  <>(\E root \in spans :
       \A s \in spans : s # root => <<s, root>> \in parentRelations)

====
```

---

## 6. 模型检验实践

### 6.1 死锁检测

```tla
(* 检测OTLP导出死锁 *)
DeadlockFree ==
  ~\E s \in spans :
    s.state = "ENDING" /\
    \A exporter \in Exporters : exporter.busy = TRUE
```

### 6.2 竞态条件检测

```tla
(* 检测Span并发修改 *)
NoRaceCondition ==
  \A s \in spans :
    Cardinality({t \in Threads : t.modifyingSpan = s.id}) <= 1
```

### 6.3 活性验证

```tla
(* 验证所有Span最终都被导出 *)
AllSpansExported ==
  <>(\A s \in spans : s.state = "EXPORTED")
```

---

## 7. 学习资源

### 7.1 官方资源

| 资源 | 链接 |
|------|------|
| TLA+主页 | https://lamport.azurewebsites.net/tla/tla.html |
| PlusCal手册 | https://lamport.azurewebsites.net/tla/pluscal.html |
| Learn TLA+ | https://learntla.com/ |
| Hillel Wayne's Blog | https://www.hillelwayne.com/ |

### 7.2 推荐书籍

| 书名 | 作者 | 难度 |
|------|------|------|
| Specifying Systems | Leslie Lamport | 入门 |
| Practical TLA+ | Hillel Wayne | 实践 |
| Concurrent and Distributed Systems | 多作者 | 进阶 |

---

## 8. 总结

### 8.1 TLA+在OTLP中的应用

| 应用场景 | 验证目标 | 复杂度 |
|----------|----------|--------|
| Span生命周期 | 状态机正确性 | ⭐⭐⭐ |
| 分布式追踪 | 因果一致性 | ⭐⭐⭐⭐ |
| Collector Pipeline | 数据流正确性 | ⭐⭐⭐⭐⭐ |
| 采样策略 | 统计正确性 | ⭐⭐⭐⭐ |

### 8.2 形式化验证的价值

```
┌─────────────────────────────────────────────────────────────────┐
│                  形式化验证的价值                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  传统测试                    形式化验证                         │
│  ─────────                   ───────────                        │
│  • 检查具体输入            • 检查所有可能状态                   │
│  • 可能遗漏边界条件        • 覆盖所有边界条件                   │
│  • 无法证明无Bug           • 可证明正确性                       │
│                                                                 │
│  OTLP中的应用场景:                                              │
│  ✅ Span状态机无死锁                                            │
│  ✅ 分布式追踪因果关系正确                                      │
│  ✅ 采样算法统计性质满足                                        │
│  ✅ Collector数据流无丢失                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

**最后更新**: 2026-03-17  
**维护者**: OTLP理论研究团队  
**状态**: Published
