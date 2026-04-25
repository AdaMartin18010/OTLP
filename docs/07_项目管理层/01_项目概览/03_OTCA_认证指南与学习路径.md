# OTCA 认证指南与学习路径

> **标准来源**: CNCF / Linux Foundation — OpenTelemetry Certified Associate (OTCA)
> **核心目标**: 介绍 OTCA 认证体系，并基于本项目知识库设计高效的学习路径

---

## 一、OTCA 概述

### 1.1 什么是 OTCA？

OTCA（OpenTelemetry Certified Associate）是由 CNCF 与 Linux Foundation 联合推出的官方职业认证，验证持证者在 OpenTelemetry 核心技术方面的专业能力。

```text
OTCA 基本信息:
├── 主办机构: Cloud Native Computing Foundation (CNCF)
├── 考试平台: Linux Foundation Training & Certification
├── 考试形式: 在线监考，选择题
├── 考试时长: 90 分钟
├── 题目数量: 约 60 题
├── 通过标准: 通常 70-75%（具体以官方公布为准）
├── 有效期: 2 年（需重新认证）
├── 考试费用: 约 $250-395（视促销活动而定）
└── 重考政策: 首次未通过，可免费重考一次
```

### 1.2 认证价值

| 维度 | 价值 |
|------|------|
| **个人** | 证明 OpenTelemetry 专业能力，提升职业竞争力 |
| **企业** | 作为招聘和技能评估的标准 |
| **社区** | 扩大 OpenTelemetry 专业人才池 |
| **生态** | 推动标准化知识的普及 |

---

## 二、考试大纲

### 2.1 知识域分布（基于公开信息推测）

```text
OTCA 考试知识域:

1. OpenTelemetry 基础概念 (15-20%)
   ├── 三大支柱（Traces、Metrics、Logs）和统一模型
   ├── 核心组件：API、SDK、OTLP、Collector
   ├── 关键术语：Span、Metric、Resource、Attribute、Context
   └── 架构原理：无侵入插桩、自动与手动 Instrumentation

2. 追踪 (Traces) (20-25%)
   ├── Span 生命周期：创建、属性、事件、链接、状态
   ├── 上下文传播：W3C Trace Context、Baggage
   ├── 采样策略：Head-based、Tail-based、概率采样
   └── 分布式追踪的实践应用

3. 指标 (Metrics) (15-20%)
   ├── 指标类型：Counter、Gauge、Histogram、Summary
   ├── 聚合 temporality：Delta vs Cumulative
   ├── 视图（View）与聚合配置
   └── Exponential Histograms 概念

4. 日志 (Logs) (10-15%)
   ├── Logs Bridge API 概念
   ├── 日志与追踪的关联（Trace Context in Logs）
   └── OTLP Logs 信号

5. OTLP 协议 (10-15%)
   ├── 协议基础：gRPC、HTTP/Protobuf、HTTP/JSON
   ├── 信号传输：Traces/Metrics/Logs over OTLP
   └── 压缩、重试、背压机制

6. Collector (10-15%)
   ├── 架构：Receiver、Processor、Exporter、Pipeline
   ├── 部署模式：Agent、Gateway、Sidecar
   └── 基本配置

7. 语义约定 (10-15%)
   ├── Semantic Conventions 概念
   ├── HTTP、Database、Messaging 核心约定
   └── Resource 属性标准

8. 最佳实践 (5-10%)
   ├── 性能考虑
   ├── 安全基础
   └── 采样配置建议
```

---

## 三、基于本项目知识库的学习路径

### 3.1 初级路径（2-3 周）

```text
目标: 建立全面基础，适合初学者

第1周: 基础概念
├── 阅读: docs/00_参考资料/01_基础概念.md
├── 阅读: docs/01_基础理论层/00_可观测性基础/01_三大支柱对比与统一模型.md
├── 实践: examples/go/hello_trace.go 或 examples/python/hello_trace.py
└── 测验: 能否解释 Span 与 Trace 的关系？

第2周: 核心协议与实现
├── 阅读: docs/02_核心协议层/01_协议基础/01_协议概述.md
├── 阅读: docs/03_核心实现层/01_SDK实现/01_SDK概述.md
├── 阅读: docs/02_核心协议层/11_Traces数据模型/01_Span结构.md
├── 实践: 运行 docker-compose.yml 启动 Collector + Jaeger
└── 测验: 能否配置一个简单的 Collector pipeline？

第3周: Collector 与语义约定
├── 阅读: docs/03_核心实现层/01_SDK实现/02_Collector架构.md
├── 阅读: docs/02_核心协议层/21_语义约定/00_语义约定总览.md
├── 阅读: docs/03_核心实现层/21_采样策略/01_采样策略.md
├── 实践: 配置一个 tail-sampling Collector
└── 模拟题: 完成 30 道选择题自测
```

### 3.2 中级路径（1-2 周，有基础者）

```text
目标: 强化重点，查漏补缺

第1周: 深化协议与实现
├── 阅读: docs/02_核心协议层/12_Metrics数据模型/02_Metrics子类型详解.md
├── 阅读: docs/02_核心协议层/01_协议基础/02_传输层_gRPC.md
├── 阅读: docs/03_核心实现层/01_SDK实现/03_SDK最佳实践.md
└── 测验: Metrics 的 Delta 和 Cumulative 有什么区别？

第2周: 实践与综合
├── 阅读: docs/04_部署运维层/01_部署指南/01_部署_大规模Collector生产部署架构指南.md
├── 阅读: docs/02_核心协议层/15_共享概念/01_Baggage详解.md
├── 实践: 配置一个多后端 Collector（Jaeger + Prometheus）
└── 模拟考试: 完成 60 题限时自测
```

### 3.3 冲刺路径（3-5 天，经验丰富者）

```text
目标: 快速复习，聚焦易错点

Day 1: 概念速查
├── 阅读: docs/00_参考资料/01_OTLP协议速查手册.md
├── 阅读: docs/00_参考资料/02_Semantic_Conventions速查手册.md
└── 重点: W3C Trace Context 格式、SpanKind 类型

Day 2: 协议与采样
├── 阅读: docs/02_核心协议层/11_OTLP协议/02_OTLP_v1.10.0_新特性解析.md
├── 阅读: docs/03_核心实现层/21_采样策略/01_采样策略.md
└── 重点: OTLP/gRPC vs OTLP/HTTP、Head-based vs Tail-based

Day 3: Collector 与部署
├── 阅读: docs/03_核心实现层/01_SDK实现/06_Collector生产环境完整配置示例.md
└── 重点: Pipeline 结构、Processor 类型、部署模式

Day 4-5: 模拟与查漏补缺
├── 自测: 100 道选择题
├── 错题分析: 针对薄弱环节回读文档
└── 实践: 快速搭建端到端 demo
```

---

## 四、模拟题示例

### 4.1 样题与解析

**题目1**: 在 OpenTelemetry 中，哪种 SpanKind 表示服务接收外部请求？

- A. CLIENT
- B. SERVER
- C. PRODUCER
- D. INTERNAL

**答案**: B. SERVER — SERVER kind 表示服务作为请求的服务端。

**题目2**: OTLP 的默认 gRPC 端口是多少？

- A. 4316
- B. 4317
- C. 4318
- D. 55680

**答案**: B. 4317 — OTLP/gRPC 默认端口为 4317，OTLP/HTTP 为 4318。

**题目3**: 以下哪种采样策略需要等待整个 Trace 完成才能做决策？

- A. AlwaysOnSampler
- B. ParentBasedSampler
- C. TraceIdRatioBasedSampler
- D. Tail-based Sampling

**答案**: D. Tail-based Sampling — 尾采样需要收集所有 Span 后根据规则决策。

**题目4**: OpenTelemetry Metrics 中，哪种类型适合记录当前队列中的消息数量？

- A. Counter
- B. UpDownCounter
- C. Histogram
- D. ObservableCounter

**答案**: B. UpDownCounter — 队列长度可增可减，适合 UpDownCounter。

---

## 五、备考资源

### 5.1 官方资源

| 资源 | 链接 | 说明 |
|------|------|------|
| OTCA 考试页面 | cncf.io/certification/otca | 官方认证信息 |
| OpenTelemetry 文档 | opentelemetry.io/docs | 核心学习材料 |
| OpenTelemetry 规范 | opentelemetry.io/docs/specs | 深度参考 |

### 5.2 本项目资源

| 资源 | 路径 | 说明 |
|------|------|------|
| 协议速查手册 | docs/00_参考资料/01_OTLP协议速查手册.md | 快速复习 |
| 语义约定速查 | docs/00_参考资料/02_Semantic_Conventions速查手册.md | 属性速查 |
| Collector 配置参考 | docs/00_参考资料/01_速查手册/03_Collector配置参考.md | 配置速查 |
| 术语表 | knowledge/00_知识中心/05_术语表/ | 中文术语学习 |
| 代码示例 | examples/ | 动手实践 |

---

## 六、检查清单

备考 OTCA 前，确认已掌握：

- [ ] 能画出 OpenTelemetry 架构图（API → SDK → OTLP → Collector → Backend）
- [ ] 能解释 Trace Context 在 HTTP 头中的格式
- [ ] 能区分四种 SpanKind 的使用场景
- [ ] 能列出至少三种采样策略及其适用场景
- [ ] 能区分 Counter、Gauge、Histogram 的用法
- [ ] 能解释 Delta 和 Cumulative 的区别
- [ ] 能配置一个基本的 Collector pipeline
- [ ] 熟悉核心 Semantic Conventions（HTTP、DB、Messaging）
- [ ] 了解 Baggage 和 Attributes 的区别
- [ ] 理解 Resource 的作用和常见属性

---

## 七、参考资源

- CNCF Certification: OpenTelemetry Certified Associate
- Linux Foundation Training Portal
- OpenTelemetry Documentation

---

> **总结**: OTCA 是验证 OpenTelemetry 核心能力的权威认证。本项目知识库（50万+字中文文档、630+代码示例、完整术语表）为备考提供了系统化的学习材料。建议按照初级/中级/冲刺路径，结合文档阅读和动手实践，高效备考。
