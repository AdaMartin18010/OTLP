# English-Chinese Glossary

> **Purpose**: Consistent terminology for translations  
> **Last Updated**: October 17, 2025

[中文版](./术语表.md) | **English Version**

---

## Core Concepts

| English | Chinese | Abbreviation | Definition |
|---------|---------|--------------|------------|
| OpenTelemetry | OpenTelemetry | OTel | Open-source observability framework |
| Observability | 可观测性 | o11y | Ability to understand system state from outputs |
| Telemetry | 遥测 | - | Automated measurement and data collection |
| Distributed Tracing | 分布式追踪 | - | Tracking requests across services |
| Signal | 信号 | - | Type of telemetry data (traces/metrics/logs) |

---

## OTLP Protocol

| English | Chinese | Abbreviation | Notes |
|---------|---------|--------------|-------|
| OTLP | OpenTelemetry协议 | - | OpenTelemetry Protocol |
| Protocol Buffers | Protocol Buffers | protobuf | Binary serialization format |
| gRPC | gRPC | - | RPC framework |
| HTTP/JSON | HTTP/JSON | - | Alternative transport |
| Collector | 收集器 | - | OTLP data aggregation service |
| Exporter | 导出器 | - | Sends data to backends |
| Receiver | 接收器 | - | Accepts data from sources |
| Processor | 处理器 | - | Transforms data |

---

## Traces

| English | Chinese | Abbreviation | Definition |
|---------|---------|--------------|------------|
| Trace | 追踪/跟踪 | - | Single request journey |
| Span | Span/跨度 | - | Single operation in trace |
| Root Span | 根Span | - | First span in trace |
| Child Span | 子Span | - | Nested span |
| Parent Span | 父Span | - | Span containing children |
| Trace ID | 追踪ID | - | Unique trace identifier |
| Span ID | Span ID | - | Unique span identifier |
| Span Context | Span上下文 | - | Propagated trace information |
| Trace Context | 追踪上下文 | - | W3C standard for propagation |
| Baggage | Baggage/行李 | - | Custom context propagation |

### Span Attributes

| English | Chinese | Definition |
|---------|---------|------------|
| Span Kind | Span类型 | SERVER, CLIENT, PRODUCER, CONSUMER, INTERNAL |
| Span Status | Span状态 | OK, ERROR, UNSET |
| Span Event | Span事件 | Point-in-time occurrence |
| Span Link | Span链接 | Connection between spans |
| Span Attribute | Span属性 | Key-value metadata |

---

## Metrics

| English | Chinese | Definition |
|---------|---------|------------|
| Metric | 指标 | Quantitative measurement |
| Counter | 计数器 | Monotonically increasing value |
| Gauge | 仪表盘/测量仪 | Current value at point in time |
| Histogram | 直方图 | Distribution of values |
| Summary | 摘要 | Statistical summary |
| UpDownCounter | 上下计数器 | Can increase or decrease |
| Meter | 测量器 | Metric instrument factory |
| Measurement | 测量值 | Single data point |
| Aggregation | 聚合 | Combining measurements |
| Temporality | 时间性 | Cumulative vs delta |

---

## Logs

| English | Chinese | Definition |
|---------|---------|------------|
| Log | 日志 | Record of event |
| Log Record | 日志记录 | Single log entry |
| Structured Logging | 结构化日志 | Key-value format |
| Log Level | 日志级别 | DEBUG, INFO, WARN, ERROR, FATAL |
| Log Correlation | 日志关联 | Linking logs to traces |
| Logger | 日志记录器 | Log creation interface |

---

## Semantic Conventions

| English | Chinese | Abbreviation |
|---------|---------|--------------|
| Semantic Convention | 语义约定 | semconv |
| Resource Attribute | 资源属性 | - |
| Span Attribute | Span属性 | - |
| Metric Attribute | 指标属性 | - |
| Service Name | 服务名称 | service.name |
| Service Version | 服务版本 | service.version |
| Deployment Environment | 部署环境 | deployment.environment |

### Common Attributes

| Attribute | Chinese | Example |
|-----------|---------|---------|
| http.method | HTTP方法 | GET, POST |
| http.status_code | HTTP状态码 | 200, 404 |
| db.system | 数据库系统 | postgresql, mongodb |
| db.operation | 数据库操作 | SELECT, INSERT |
| messaging.system | 消息系统 | kafka, rabbitmq |
| rpc.system | RPC系统 | grpc, dubbo |

---

## Sampling

| English | Chinese | Definition |
|---------|---------|------------|
| Sampling | 采样 | Selecting subset of traces |
| Sample Rate | 采样率 | Percentage of traces kept |
| Head-based Sampling | 头部采样 | Decision at trace start |
| Tail-based Sampling | 尾部采样 | Decision after trace completes |
| Sampler | 采样器 | Sampling decision maker |
| Always On | 始终开启 | 100% sampling |
| Always Off | 始终关闭 | 0% sampling |
| Trace ID Ratio | 追踪ID比率 | Probabilistic sampling |
| Parent Based | 基于父级 | Use parent's decision |

### Advanced Sampling (2025)

| English | Chinese | Definition |
|---------|---------|------------|
| Tracezip | Tracezip | Trace compression technique |
| Autoscope | Autoscope | Intelligent span-level sampling |
| Span Retrieval Tree | Span检索树 | SRT compression structure |
| Compression Ratio | 压缩率 | Data size reduction percentage |
| Fault Coverage | 故障覆盖率 | Percentage of errors captured |

---

## SDK & Instrumentation

| English | Chinese | Abbreviation |
|---------|---------|--------------|
| SDK | 软件开发工具包 | SDK |
| Instrumentation | 埋点/仪器化 | - |
| Auto-instrumentation | 自动埋点 | - |
| Manual Instrumentation | 手动埋点 | - |
| Tracer | 追踪器 | - |
| Tracer Provider | 追踪器提供者 | - |
| Context Propagation | 上下文传播 | - |
| Context Manager | 上下文管理器 | - |

---

## Advanced Concepts

### Formal Verification

| English | Chinese | Definition |
|---------|---------|------------|
| Formal Semantics | 形式化语义 | Mathematical definition |
| Type System | 类型系统 | Type rules and constraints |
| Operational Semantics | 操作语义 | Execution rules |
| Denotational Semantics | 指称语义 | Mathematical interpretation |
| Algebraic Structure | 代数结构 | Mathematical structure |
| Monoid | 幺半群 | Associative binary operation with identity |
| Semilattice | 半格 | Partial order with join/meet |
| Lattice | 格 | Complete partial order |
| Category Theory | 范畴论 | Abstract mathematical structures |

### Flow Analysis

| English | Chinese | Definition |
|---------|---------|------------|
| Control Flow | 控制流 | Program execution path |
| Data Flow | 数据流 | Data movement through program |
| Execution Flow | 执行流 | Runtime trace of operations |
| Control Flow Graph | 控制流图 | CFG representation |
| Data Flow Analysis | 数据流分析 | DFA techniques |
| Reaching Definitions | 到达定义 | Variable definition analysis |
| Liveness Analysis | 活性分析 | Variable usage analysis |
| Critical Path | 关键路径 | Longest latency path |

### Temporal Logic

| English | Chinese | Definition |
|---------|---------|------------|
| Temporal Logic | 时序逻辑 | Logic over time |
| LTL | 线性时序逻辑 | Linear Temporal Logic |
| CTL | 计算树逻辑 | Computation Tree Logic |
| Safety Property | 安全性属性 | "Bad things don't happen" |
| Liveness Property | 活性属性 | "Good things eventually happen" |

### Self-Aware Systems

| English | Chinese | Definition |
|---------|---------|------------|
| Self-Aware | 自我感知 | System knows its own state |
| Self-Ops | 自我运维 | Autonomous operations |
| Perception Layer | 感知层 | Data collection layer |
| Cognitive Intelligence | 认知智能 | Pattern recognition and analysis |
| Closed-Loop Control | 闭环控制 | Feedback-based automation |
| OODA Loop | OODA循环 | Observe-Orient-Decide-Act |
| MAPE-K | MAPE-K | Monitor-Analyze-Plan-Execute-Knowledge |

---

## OTLP Arrow (2025)

| English | Chinese | Definition |
|---------|---------|------------|
| OTLP Arrow | OTLP Arrow | Columnar OTLP encoding |
| Apache Arrow | Apache Arrow | In-memory columnar format |
| Columnar Encoding | 列式编码 | Column-oriented storage |
| Row-based Encoding | 行式编码 | Row-oriented storage |
| Dictionary Encoding | 字典编码 | String compression technique |
| Delta Encoding | 增量编码 | Timestamp compression |
| Zero-Copy | 零拷贝 | Direct memory access |
| Batch Processing | 批处理 | Group operations |

---

## Deployment & Operations

| English | Chinese | Definition |
|---------|---------|------------|
| Production | 生产环境 | Live system |
| Development | 开发环境 | Dev system |
| Staging | 预发布环境 | Pre-production |
| Canary Deployment | 金丝雀部署 | Gradual rollout |
| Blue-Green Deployment | 蓝绿部署 | Zero-downtime deployment |
| Health Check | 健康检查 | Service status verification |
| Circuit Breaker | 熔断器 | Failure prevention |
| Rate Limiting | 限流 | Request throttling |
| Load Balancing | 负载均衡 | Traffic distribution |

---

## Performance & Optimization

| English | Chinese | Definition |
|---------|---------|------------|
| Latency | 延迟 | Response time |
| Throughput | 吞吐量 | Requests per second |
| Bandwidth | 带宽 | Data transfer capacity |
| Overhead | 开销 | Additional resource cost |
| Bottleneck | 瓶颈 | Performance limitation |
| Hot Spot | 热点 | Frequently accessed resource |
| Cache | 缓存 | Temporary data storage |
| Compression | 压缩 | Data size reduction |

---

## Community & Contribution

| English | Chinese | Definition |
|---------|---------|------------|
| Contributor | 贡献者 | Project participant |
| Maintainer | 维护者 | Core team member |
| Pull Request | 拉取请求 | PR, code contribution |
| Issue | Issue/问题 | Bug or feature request |
| Discussion | 讨论 | Community conversation |
| Code Review | 代码审查 | PR evaluation |
| Merge | 合并 | Integrating code |
| Fork | Fork/分支 | Repository copy |

---

## Usage Guidelines

### Translation Best Practices

1. **Consistency**: Always use the same translation for a term
2. **Context**: Some terms may need different translations based on context
3. **Keep English**: For well-known terms (SDK, API, HTTP), keep English
4. **Abbreviations**: Use both full name and abbreviation on first use
5. **Examples**: Provide examples when meaning might be unclear

### When to Keep English

- Well-established technical terms (SDK, API, REST, JSON, HTTP, gRPC)
- Product names (Jaeger, Zipkin, Prometheus, Grafana)
- Acronyms that are universally known (OTLP, SLA, SLO, SLI)
- Terms with no good Chinese equivalent

### Recommended Format

When introducing a new term:
```
OpenTelemetry Protocol (OTLP, OpenTelemetry协议)
```

Subsequent uses:
```
OTLP
```

---

## Contributing to Glossary

To add or modify terms:
1. Create an issue or PR
2. Provide English term, Chinese translation, and definition
3. Include usage examples if helpful
4. Wait for maintainer review

---

**Last Updated**: October 17, 2025  
**Maintainer**: OTLP Project Team  
**Version**: 1.0.0

