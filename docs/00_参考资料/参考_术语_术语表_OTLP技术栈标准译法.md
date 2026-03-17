---
title: 术语表 - OTLP 技术栈标准译法
description: 术语表 - OTLP 技术栈标准译法 详细指南和最佳实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 参考资料
tags:
  - otlp
  - observability
  - ebpf
  - performance
  - optimization
  - sampling
  - deployment
  - kubernetes
  - docker
status: published
---
# 术语表 - OTLP 技术栈标准译法

> **版本**: v1.0
> **创建日期**: 2025年10月9日
> **适用范围**: 本项目所有技术文档
> **维护原则**: 优先采用 OpenTelemetry 官方中文文档译法

---

## 核心原则

1. **一致性优先**: 同一术语在所有文档中使用统一译法
2. **官方优先**: 优先采用 OpenTelemetry / CNCF 官方译法
3. **行业惯例**: 参考 Google / AWS / 阿里云等技术文档
4. **保留原文**: 对于无明确译法的术语,保留英文
5. **避免生僻词**: 使用通俗易懂的表达

---

## A-Z 术语表

### A

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Activity** | Activity (不译) | Temporal 工作流中的具体操作 | ExecuteActivity() |
| **Agent** | Agent (代理) | 轻量级数据采集程序 | Parca Agent, eBPF Agent |
| **AIOps** | AIOps (智能运维) | AI for IT Operations 的缩写 | AIOps Platform |
| **Alert** | 告警 | 监控系统的异常通知 | Alert Manager, Alert Rules |
| **Alerting** | 告警 | 告警的行为和过程 | Alerting Strategy |
| **Anomaly** | 异常 | 偏离正常行为的数据点 | Anomaly Detection (异常检测) |
| **Annotation** | 注解 | 代码中的元数据标记 | Java Annotation, Python Decorator |
| **API** | API (不译) | Application Programming Interface | REST API, gRPC API |
| **Architecture** | 架构 | 系统的整体设计 | Microservices Architecture (微服务架构) |
| **Attribute** | 属性 | OTLP 数据的键值对元数据 | Span Attributes, Resource Attributes |
| **Auto-instrumentation** | 自动插桩 | 无需代码修改的追踪注入 | OpenTelemetry Auto-instrumentation |

### B

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Backend** | 后端 | 服务器端系统 | Observability Backend |
| **Backpressure** | 背压 | 下游处理不过来时的反向压力 | Kafka Backpressure |
| **Baggage** | Baggage (不译) | W3C 标准的上下文传播键值对 | Baggage Propagation |
| **Batch** | 批次 | 批量处理的数据组 | Batch Exporter, Batch Processor |
| **Benchmark** | 基准测试 | 性能测试标准 | CPU Benchmark |
| **BPF** | BPF (不译) | Berkeley Packet Filter | eBPF, BPF Verifier |
| **Bucket** | 桶 | 数据分组单元 | Histogram Buckets, S3 Bucket |

### C

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Cache** | 缓存 | 临时存储层 | Redis Cache, CDN Cache |
| **Canary** | 金丝雀 | 渐进式发布策略 | Canary Deployment (金丝雀发布) |
| **Cardinality** | 基数 | 唯一值的数量 | High-cardinality Labels (高基数标签) |
| **Checkpoint** | 检查点 | 状态持久化点 | Flink Checkpoint, Temporal Checkpoint |
| **Circuit Breaker** | 熔断器 | 故障隔离机制 | Istio Circuit Breaker |
| **Collector** | 收集器 | 数据采集组件 | OpenTelemetry Collector (✅ 不使用"采集器") |
| **Compression** | 压缩 | 数据压缩 | gRPC Compression |
| **Concurrency** | 并发 | 同时执行多个任务 | Concurrent Execution |
| **Context** | 上下文 | 请求的关联信息 | Trace Context, Context Propagation (上下文传播) |
| **CO-RE** | CO-RE (不译) | Compile Once - Run Everywhere | libbpf CO-RE |
| **CPU Profiling** | CPU 性能剖析 | CPU 使用分析 | Go pprof CPU Profiling (✅ 不使用"性能分析") |
| **CRD** | CRD (不译) | Custom Resource Definition | Kubernetes CRD |

### D

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Dashboard** | 仪表板 | 可视化面板 | Grafana Dashboard |
| **DaemonSet** | DaemonSet (不译) | Kubernetes 每节点一实例的工作负载 | eBPF Agent DaemonSet |
| **Data Pipeline** | 数据管道 | 数据处理流程 | Flink Pipeline (✅ 不使用"流水线") |
| **Deployment** | Deployment (部署) | Kubernetes 工作负载类型 | Kubernetes Deployment |
| **Descriptor** | 描述符 | 资源的唯一标识 | File Descriptor, Metric Descriptor |
| **Deterministic** | 确定性 | 相同输入总是产生相同输出 | Temporal Workflow Deterministic Execution |
| **Distributed Tracing** | 分布式追踪 | 跨服务的请求追踪 | Distributed Tracing System (✅ 不使用"跟踪") |
| **Drift** | 漂移 | 数据分布的变化 | Data Drift, Model Drift (模型漂移) |

### E

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **eBPF** | eBPF (不译) | extended Berkeley Packet Filter | eBPF Program |
| **Embedding** | 向量嵌入 | 文本到向量的转换 | OpenAI Embeddings |
| **Endpoint** | 端点 | 服务的网络地址 | OTLP Endpoint |
| **Enrichment** | 增强/富化 | 添加额外的元数据 | Log Enrichment (日志富化) |
| **Envoy** | Envoy (不译) | 服务网格的 Sidecar 代理 | Envoy Proxy, Envoy Filter |
| **Event** | 事件 | 离散的时间点记录 | eBPF Event, Kubernetes Event |
| **Exemplar** | Exemplar (不译) | 指标到追踪的关联点 | Prometheus Exemplars |
| **Exporter** | 导出器 | 数据导出组件 | OTLP Exporter (✅ 不使用"输出器") |

### F

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Failover** | 故障转移 | 主备切换 | Database Failover |
| **Fault Injection** | 故障注入 | 混沌工程测试 | Istio Fault Injection |
| **Feature** | 特征 | 机器学习的输入变量 | Feature Engineering (特征工程) |
| **Filter** | 过滤器 | 数据筛选组件 | Envoy Filter, Log Filter |
| **Flame Graph** | 火焰图 | 性能剖析可视化 | CPU Flame Graph |
| **Frontend** | 前端 | 客户端应用 | Web Frontend |

### G

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Gateway** | 网关 | 流量入口 | API Gateway, Istio Gateway |
| **GNN** | GNN (图神经网络) | Graph Neural Network | GNN for RCA |
| **Goroutine** | Goroutine (不译) | Go 语言的轻量级线程 | Goroutine Leak (Goroutine 泄漏) |
| **gRPC** | gRPC (不译) | Google RPC 框架 | gRPC Protocol |

### H

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Head Sampling** | 头部采样 | 请求起点的采样决策 | Head-based Sampling |
| **Health Check** | 健康检查 | 服务可用性检测 | Kubernetes Health Check |
| **Heap** | 堆 | 内存分配区域 | Heap Profiling (堆内存剖析) |
| **Histogram** | 直方图 | 数值分布统计 | Latency Histogram |
| **Hook** | 钩子 | 代码注入点 | eBPF Hook Point, Git Hook |
| **HPA** | HPA (不译) | Horizontal Pod Autoscaler | Kubernetes HPA |

### I

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Idempotent** | 幂等 | 多次执行结果一致 | Idempotent Operation |
| **Ingest** | 摄取 | 数据接收过程 | Log Ingest Rate |
| **Instrumentation** | 插桩 | 代码注入追踪逻辑 | Auto-instrumentation (自动插桩) |
| **Interceptor** | 拦截器 | 请求/响应拦截组件 | gRPC Interceptor, Temporal Interceptor |
| **Invariant** | 不变量 | 系统始终满足的条件 | TLA+ Invariant |
| **Istio** | Istio (不译) | 开源服务网格 | Istio Service Mesh |

### J

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Jaeger** | Jaeger (不译) | 分布式追踪系统 | Jaeger UI |
| **JFR** | JFR (不译) | Java Flight Recorder | JFR Profiling |

### K

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Kafka** | Kafka (不译) | 消息队列 | Apache Kafka |
| **Kernel** | 内核 | 操作系统核心 | Linux Kernel |
| **Kprobe** | Kprobe (不译) | 内核探针 | eBPF Kprobe |
| **Kubernetes** | Kubernetes (不译) | 容器编排平台 | Kubernetes Cluster |

### L

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Label** | 标签 | 键值对元数据 | Prometheus Label, Kubernetes Label |
| **Latency** | 延迟 | 请求响应时间 | P99 Latency (P99 延迟) |
| **Leak** | 泄漏 | 资源未释放 | Memory Leak (内存泄漏) |
| **Library** | 库 | 代码依赖 | Go Library, Python Library |
| **Linkerd** | Linkerd (不译) | 轻量级服务网格 | Linkerd Service Mesh |
| **LLM** | LLM (大语言模型) | Large Language Model | GPT-4, Claude 3 |
| **Load Balancer** | 负载均衡器 | 流量分发器 | Istio Load Balancer |
| **Log** | 日志 | 文本格式的事件记录 | Application Log, System Log |
| **LRU** | LRU (不译) | Least Recently Used | LRU Cache, BPF_MAP_TYPE_LRU_HASH |

### M

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Map** | Map (映射) | eBPF 的数据结构 | BPF Map, Hash Map |
| **Metadata** | 元数据 | 描述数据的数据 | Span Metadata |
| **Metric** | 指标 | 数值型时间序列数据 | Prometheus Metrics, OTLP Metrics |
| **Microservices** | 微服务 | 分布式架构模式 | Microservices Architecture (微服务架构) |
| **Middleware** | 中间件 | 请求处理链中的组件 | HTTP Middleware |
| **MLOps** | MLOps (不译) | 机器学习运维 | MLOps Platform |
| **Model** | 模型 | 机器学习/数据模型 | ML Model, Data Model (数据模型) |
| **Monitoring** | 监控 | 系统状态观测 | System Monitoring (系统监控) |
| **MTTD** | MTTD (不译) | Mean Time To Detect (平均检测时间) | MTTD < 2 min |
| **MTTR** | MTTR (不译) | Mean Time To Repair (平均修复时间) | MTTR < 10 min |
| **Mutex** | Mutex (互斥锁) | 并发控制原语 | Mutex Profiling (互斥锁剖析) |

### N

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Namespace** | 命名空间 | 资源隔离单元 | Kubernetes Namespace |
| **Neo4j** | Neo4j (不译) | 图数据库 | Neo4j Knowledge Graph |
| **Node** | 节点 | 服务器或图的顶点 | Kubernetes Node, Graph Node (图节点) |

### O

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Observability** | 可观测性 | 系统内部状态可见性 | Three Pillars of Observability (可观测性三支柱) |
| **Operator** | Operator (不译) | Kubernetes 控制器模式 | Prometheus Operator |
| **OTLP** | OTLP (不译) | OpenTelemetry Protocol | OTLP/gRPC, OTLP/HTTP |
| **Overhead** | 开销 | 性能影响 | CPU Overhead (CPU 开销) |

### P

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Payload** | 负载/有效载荷 | 数据包的实际内容 | HTTP Payload |
| **Performance** | 性能 | 系统的执行效率 | Performance Optimization (性能优化) |
| **Pipeline** | 管道 | 数据处理流程 | OTLP Collector Pipeline (✅ 不使用"流水线") |
| **Pod** | Pod (不译) | Kubernetes 最小部署单元 | Kubernetes Pod |
| **Polling** | 轮询 | 周期性查询 | Event Polling |
| **pprof** | pprof (不译) | Go 性能剖析工具 | Go pprof |
| **Processor** | 处理器 | 数据处理组件 | OTLP Batch Processor |
| **Profiles** | Profiles (性能剖析数据) | OTLP 第四信号 | OTLP Profiles Signal |
| **Profiling** | 性能剖析 | 运行时性能分析 | Continuous Profiling (连续性能剖析) (✅ 不使用"性能分析") |
| **Prometheus** | Prometheus (不译) | 指标监控系统 | Prometheus Metrics |
| **Propagation** | 传播 | 上下文在分布式系统中的传递 | Context Propagation (上下文传播) |
| **Protocol** | 协议 | 通信规范 | OTLP Protocol, HTTP Protocol |
| **Proxy** | 代理 | 中间转发组件 | Envoy Proxy, HTTP Proxy |
| **py-spy** | py-spy (不译) | Python 性能剖析工具 | Python py-spy |

### Q

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Query** | 查询 | 数据检索操作 | SQL Query, Prometheus Query |
| **Queue** | 队列 | 先进先出的数据结构 | Task Queue, Message Queue (消息队列) |

### R

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Rate Limiting** | 速率限制 | 流量控制 | API Rate Limiting |
| **RCA** | RCA (根因分析) | Root Cause Analysis | AI-driven RCA |
| **Receiver** | 接收器 | 数据接收组件 | OTLP Receiver |
| **Redis** | Redis (不译) | 内存数据库 | Redis Cache |
| **Replica** | 副本 | 冗余实例 | Database Replica |
| **Resource** | 资源 | OTLP 的资源元数据 | Resource Attributes |
| **Retry** | 重试 | 失败后重新尝试 | Retry Policy (重试策略) |
| **Ring Buffer** | Ring Buffer (环形缓冲区) | eBPF 数据传输机制 | BPF Ring Buffer |
| **Rollback** | 回滚 | 回到之前的版本 | Deployment Rollback (部署回滚) |
| **Root Span** | 根 Span | 追踪的起始节点 | Root Span (不译 Span) |
| **Router** | 路由器 | 流量路由组件 | Istio Router |

### S

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Saga** | Saga (不译) | 分布式事务模式 | Saga Pattern |
| **Sampling** | 采样 | 数据抽样策略 | Trace Sampling (追踪采样) (✅ 不使用"取样") |
| **Sampling Rate** | 采样率 | 采样比例 | 10% Sampling Rate |
| **Schema** | 模式 | 数据结构定义 | Database Schema |
| **SDK** | SDK (不译) | Software Development Kit | OpenTelemetry SDK |
| **Secret** | Secret (密钥) | Kubernetes 敏感数据 | Kubernetes Secret |
| **SemConv** | SemConv (不译) | Semantic Conventions (语义约定) | OpenTelemetry SemConv |
| **Service** | 服务 | 独立的业务单元 | Microservice, Kubernetes Service |
| **Service Mesh** | 服务网格 | 微服务通信基础设施 | Istio Service Mesh (✅ 不译为"服务网") |
| **Shard** | 分片 | 数据水平分割 | Database Shard |
| **Sidecar** | Sidecar (边车) | 与主容器并行的辅助容器 | Envoy Sidecar |
| **Signal** | 信号 | OTLP 数据类型 | Traces/Metrics/Logs/Profiles Signals |
| **Span** | Span (不译) | 追踪的基本单元 | Root Span, Child Span |
| **SpanID** | SpanID (不译) | Span 的唯一标识 | 16-hex SpanID |
| **Stack Trace** | 堆栈追踪 | 函数调用链 | Stack Trace (不译为"栈追踪") |
| **StatefulSet** | StatefulSet (不译) | Kubernetes 有状态工作负载 | Kafka StatefulSet |
| **Stream** | 流 | 持续的数据序列 | Stream Processing (流处理) |

### T

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Tail Sampling** | 尾部采样 | 请求结束后的采样决策 | Tail-based Sampling |
| **Task Queue** | 任务队列 | Temporal 的任务调度队列 | Temporal Task Queue |
| **Telemetry** | 遥测 | 远程数据采集 | Telemetry Data (遥测数据) |
| **Temporal** | Temporal (不译) | 工作流编排引擎 | Temporal.io |
| **Threshold** | 阈值 | 触发条件的边界值 | Alert Threshold (告警阈值) |
| **Throughput** | 吞吐量 | 单位时间的处理量 | QPS Throughput |
| **TimescaleDB** | TimescaleDB (不译) | 时序数据库 | TimescaleDB Hypertable |
| **Timeout** | 超时 | 等待时间上限 | Request Timeout (请求超时) |
| **TLA+** | TLA+ (不译) | 形式化规范语言 | TLA+ Model Checking |
| **TLC** | TLC (不译) | TLA+ Model Checker | TLC Verifier |
| **Token** | Token (令牌) | LLM 的基本单元 | GPT-4 Tokens |
| **Topology** | 拓扑 | 系统组件的连接关系 | Service Topology (服务拓扑) |
| **Trace** | Trace (追踪) | 完整的请求链路 | Distributed Trace (分布式追踪) |
| **TraceID** | TraceID (不译) | 追踪的唯一标识 | 32-hex TraceID |
| **Tracestate** | Tracestate (不译) | W3C 追踪状态 | Tracestate Header |
| **Tracing** | 追踪 | 链路追踪行为 | Distributed Tracing (分布式追踪) (✅ 不使用"跟踪") |
| **Traffic** | 流量 | 网络数据传输 | Network Traffic (网络流量) |

### U

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Uprobe** | Uprobe (不译) | 用户空间探针 | eBPF Uprobe |

### V

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **Vector Database** | 向量数据库 | 存储向量嵌入的数据库 | ChromaDB, Pinecone |
| **Verifier** | 验证器 | 正确性检查器 | BPF Verifier, TLA+ Verifier |
| **VirtualService** | VirtualService (不译) | Istio 流量路由规则 | Istio VirtualService |

### W

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **W3C** | W3C (不译) | World Wide Web Consortium | W3C Trace Context |
| **Wasm** | Wasm (不译) | WebAssembly | Envoy Wasm Filter |
| **Workflow** | 工作流 | 业务流程编排 | Temporal Workflow |
| **Worker** | Worker (工作节点) | 执行任务的进程 | Temporal Worker, Flink Worker |

### X-Z

| 英文 | 中文 | 说明 | 示例 |
|------|------|------|------|
| **XDP** | XDP (不译) | eXpress Data Path | eBPF XDP |
| **YAML** | YAML (不译) | 配置文件格式 | Kubernetes YAML |

---

## 特殊约定

### 1. 不翻译的术语 (保留英文)

以下术语在技术文档中通常保留英文,不进行翻译:

- **技术品牌名**: Kubernetes, Prometheus, Grafana, Istio, Linkerd, Kafka, Redis, Neo4j
- **协议/标准**: OTLP, gRPC, HTTP, TCP, W3C, JSON, YAML
- **技术缩写**: SDK, API, CPU, GPU, RAM, QPS, TPS, SLA, SLO, SLI
- **编程概念**: Span, SpanID, TraceID, Baggage, Exemplar
- **工具名称**: pprof, py-spy, bpftool, kubectl, istioctl
- **数据结构**: Map, Queue, Stack, Heap

### 2. 优先使用的表达

| ❌ 避免使用 | ✅ 推荐使用 | 原因 |
|------------|------------|------|
| 跟踪 | 追踪 | "追踪"更常用于技术文档 |
| 采集器 | 收集器 | OpenTelemetry 官方译法 |
| 性能分析 | 性能剖析 | Profiling 专业术语 |
| 流水线 | 管道 | Pipeline 更简洁的表达 |
| 取样 | 采样 | Sampling 标准译法 |
| 服务网 | 服务网格 | Service Mesh 完整表达 |
| 栈追踪 | 堆栈追踪 | Stack Trace 标准译法 |
| 输出器 | 导出器 | Exporter 官方译法 |

### 3. 上下文相关的翻译

某些术语根据上下文有不同译法:

| 英文 | 软件工程 | 网络/基础设施 | 机器学习 |
|------|----------|---------------|----------|
| **Model** | 数据模型 | 网络模型 | (机器学习)模型 |
| **Feature** | 功能 | 特性 | 特征 |
| **Agent** | 代理 | 代理 | Agent (不译) |
| **Pipeline** | 管道 | 管道 | 管道 |

### 4. 复合术语的处理

| 英文 | 译法 | 说明 |
|------|------|------|
| **Distributed Tracing** | 分布式追踪 | 整体翻译 |
| **Service Mesh** | 服务网格 | 整体翻译 |
| **Root Cause Analysis** | 根因分析 | 整体翻译 |
| **Continuous Profiling** | 连续性能剖析 | 整体翻译 |
| **Auto-instrumentation** | 自动插桩 | 整体翻译 |
| **Head Sampling** | 头部采样 | 整体翻译 |
| **Tail Sampling** | 尾部采样 | 整体翻译 |

---

## 使用规范

### 正确示例

```markdown
# 正确
- 使用 **OTLP 收集器** 采集分布式追踪数据
- 通过 **性能剖析** 发现 CPU 热点
- 配置 Prometheus **指标** 采样率为 10%
- Istio **服务网格** 提供自动追踪注入
```

### ❌ 错误示例

```markdown
# 错误
- 使用 **OTLP 采集器** 采集分布式跟踪数据  ❌ (应为"收集器"和"追踪")
- 通过 **性能分析** 发现 CPU 热点  ❌ (应为"性能剖析")
- 配置 Prometheus **指标** 取样率为 10%  ❌ (应为"采样率")
- Istio **服务网** 提供自动追踪注入  ❌ (应为"服务网格")
```

---

## 参考资源

1. **OpenTelemetry 官方中文文档**: <https://opentelemetry.io/docs/>
2. **CNCF 中文术语表**: <https://glossary.cncf.io/zh-cn/>
3. **Kubernetes 中文文档**: <https://kubernetes.io/zh-cn/docs/>
4. **Google 开发者中文风格指南**: <https://developers.google.cn/style/>
5. **微软中文风格指南**: <https://docs.microsoft.com/zh-cn/style-guide/>

---

## 维护说明

### 更新流程

1. 发现新术语 → 查阅官方文档 → 添加到术语表
2. 发现译法不一致 → 讨论并选择最佳译法 → 更新术语表
3. 每月复审一次,确保与最新标准保持一致

### 贡献指南

如需添加或修改术语,请:

1. 提供官方参考链接
2. 说明选择该译法的理由
3. 提供使用示例

---

**维护者**: AI Assistant
**最后更新**: 2025年10月9日
**版本**: v1.0
