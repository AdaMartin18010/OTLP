# OpenCensus 迁移完整指南

> **标准来源**: OpenTelemetry Specification v1.56.0 — Compatibility / OpenCensus
> **目标读者**: 仍在使用 OpenCensus 的遗留系统维护者、平台工程师
> **核心目标**: 提供从 OpenCensus 到 OpenTelemetry 的完整迁移路径，确保数据连续性和最小业务影响

---

## 一、背景：为什么需要迁移？

### 1.1 OpenCensus 项目状态

OpenCensus 已于 **2020 年正式进入维护模式**，官方社区强烈推荐所有用户迁移到 OpenTelemetry：

```text
┌─────────────────────────────────────────────────────────────┐
│  OpenCensus 现状                                             │
├─────────────────────────────────────────────────────────────┤
│  • 不再接受新功能开发                                         │
│  • 仅修复关键安全漏洞                                         │
│  • 社区支持逐渐减弱                                           │
│  • 云厂商后端逐步减少对 OpenCensus 协议的原生支持             │
│  • 新兴语言（如 Rust）无 OpenCensus SDK                       │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 迁移的核心收益

| 维度 | OpenCensus | OpenTelemetry |
|------|-----------|---------------|
| 信号统一 | Traces 和 Metrics 分离（OpenCensus + OpenCensus Agent） | Traces、Metrics、Logs、Profiles 统一框架 |
| 协议标准 | 各厂商实现差异大 | OTLP 厂商中立标准协议 |
| 生态集成 | 有限 | Prometheus、Jaeger、Grafana、云厂商原生支持 |
| 社区活跃度 | 维护模式 | CNCF Incubating（申请 Graduation）|
| 语言覆盖 | 主流语言 | 10+ 语言，包括新兴语言 |
| 长期支持 | 无保障 | 长期演进保障 |

---

## 二、迁移策略总览

### 2.1 三种迁移模式

```text
模式一：全量迁移（Big Bang）
├── 适用：小型服务、新系统、有充足测试窗口
├── 步骤：一次性替换所有 OpenCensus 代码为 OpenTelemetry
├── 风险：较高，需要全面的回归测试
└── 周期：1-4 周

模式二：桥接渐进迁移（Bridge & Incremental）⭐ 推荐
├── 适用：中大型服务、核心系统、无法停机
├── 步骤：
│   1. 引入 OpenTelemetry Bridge
│   2. 让 OpenCensus 数据通过 Bridge 流入 OTel Pipeline
│   3. 逐步将业务代码从 OpenCensus API 替换为 OTel API
│   4. 完全移除 OpenCensus 依赖
├── 风险：低，数据不丢失，可逐步验证
└── 周期：2-6 个月

模式三：Collector 侧兼容（Collector Compatibility）
├── 适用：后端已迁移到 OTel Collector，但应用仍用 OpenCensus
├── 步骤：
│   1. 部署 OpenTelemetry Collector
│   2. 配置 Collector 接收 OpenCensus 协议数据
│   3. Collector 将数据转换为 OTLP 并转发到新后端
│   4. 应用侧可保留 OpenCensus 更长时间
├── 风险：最低，应用代码完全不变
└── 周期：1-2 周（基础设施层）
```

### 2.2 推荐的迁移路线图

```text
阶段 0：评估与准备（1-2 周）
├── 盘点所有使用 OpenCensus 的服务和组件
├── 确认各语言的 OpenTelemetry SDK 成熟度
├── 评估 OpenCensus Collector / Agent 的替代方案
└── 制定回滚计划

阶段 1：基础设施迁移（2-4 周）
├── 部署 OpenTelemetry Collector
├── 配置 OpenCensus Receiver（兼容旧数据流入）
├── 验证 OTLP 导出到现有后端（或新后端）
└── 建立双轨运行（OpenCensus + OTel Collector 并行）

阶段 2：应用桥接（4-8 周）
├── 在应用中引入 OpenCensus Bridge
├── 让 OpenCensus Span 和 Metric 通过 Bridge 进入 OTel SDK
├── 验证数据完整性和性能影响
└── 开始新业务代码直接使用 OTel API

阶段 3：代码替换（8-16 周）
├── 按模块/服务逐个替换 OpenCensus API 调用
├── 更新自动化测试和集成测试
├── 更新监控告警规则（指标名称可能变化）
└── 逐步下线 OpenCensus 相关组件

阶段 4：清理与优化（2-4 周）
├── 移除所有 OpenCensus 依赖和 Bridge
├── 优化 OTel 配置（采样、批处理、Resource 属性）
├── 全面性能基准对比
└── 团队知识转移和文档更新
```

---

## 三、概念映射：OpenCensus → OpenTelemetry

### 3.1 核心概念对照表

| OpenCensus 概念 | OpenTelemetry 对应概念 | 说明 |
|----------------|----------------------|------|
| `Span` | `Span` | 直接对应，API 略有差异 |
| `SpanContext` | `SpanContext` | 字段结构基本一致（trace_id, span_id, trace_flags）|
| `Annotation` | `Span Event` / `LogRecord` | OpenTelemetry 推荐使用 Event 或 Logs |
| `MessageEvent` | `Span Event` (with semantic conventions) | 使用 `messaging.*` 语义约定属性 |
| `Link` | `Link` | 直接对应 |
| `Status` | `Status` | OpenCensus 的 `Status.CanonicalCode` 映射到 OTel 的 `StatusCode` |
| `Measure` | `Instrument` (Counter, Histogram, etc.) | 数据模型变化较大，需要重新设计 |
| `View` | `View` (Metrics SDK) | OpenTelemetry 的 View 用于聚合配置 |
| `Exporter` | `Exporter` | 概念一致，接口不同 |
| `Sampler` | `Sampler` | 概念一致，接口和默认实现不同 |
| `Propagator` | `TextMapPropagator` | 功能一致，API 不同 |
| `Tag` / `TagMap` | `Attribute` / `Baggage` | Tag 映射到 Attribute（Span 级别）或 Baggage（跨 Span 传播）|
| `Resource` | `Resource` | 直接对应，属性命名遵循 Semantic Conventions |

### 3.2 关键差异点

#### Span 创建与结束

```java
// OpenCensus (Java)
Span span = tracer.spanBuilder("processOrder").startSpan();
try (Scope scope = tracer.withSpan(span)) {
    // 业务逻辑
} catch (Exception e) {
    span.setStatus(StatusCanonicalCode.ERROR, e.getMessage());
    throw e;
} finally {
    span.end();
}

// OpenTelemetry (Java)
Span span = tracer.spanBuilder("processOrder").startSpan();
try (Scope scope = span.makeCurrent()) {  // API 差异：makeCurrent() 在 Span 上
    // 业务逻辑
} catch (Exception e) {
    span.setStatus(StatusCode.ERROR, e.getMessage());
    span.recordException(e);  // OTel 推荐显式记录异常
    throw e;
} finally {
    span.end();
}
```

#### 属性设置

```java
// OpenCensus
span.putAttribute("user.id", AttributeValue.stringAttributeValue("12345"));
span.putAttribute("order.amount", AttributeValue.doubleAttributeValue(199.99));

// OpenTelemetry
span.setAttribute("user.id", "12345");
span.setAttribute("order.amount", 199.99);
// OTel 自动推断类型，无需显式包装
```

#### 指标（最大差异）

```java
// OpenCensus: Measure + View + Aggregation 模型
MeasureLong measure = MeasureLong.create("request_count", "请求数", "1");
View view = View.create(
    View.Name.create("request_count_total"),
    "总请求数",
    measure,
    Aggregation.Count.create(),
    Arrays.asList(TagKey.create("method"))
);
Stats.getViewManager().registerView(view);

// OpenTelemetry: Instrument + Collector Pipeline 模型
LongCounter counter = meter.counterBuilder("request_count")
    .setDescription("请求数")
    .setUnit("1")
    .build();

counter.add(1, Attributes.of(AttributeKey.stringKey("method"), "GET"));
// View 在 SDK 层配置，用于聚合和过滤
```

---

## 四、Bridge 模式详解

### 4.1 什么是 OpenCensus Bridge？

OpenCensus Bridge 是一个**兼容层**，它：

- 在应用侧拦截 OpenCensus API 调用
- 将 OpenCensus 的 Span、Metric、Resource 转换为 OpenTelemetry 格式
- 通过 OpenTelemetry SDK 的 Exporter 导出数据

这样，应用在完全替换代码之前，数据已经可以流入 OTel Pipeline。

### 4.2 Java 桥接配置

```java
// 1. 首先初始化 OpenTelemetry SDK（常规方式）
OpenTelemetrySdk otelSdk = OpenTelemetrySdk.builder()
    .setTracerProvider(SdkTracerProvider.builder()
        .addSpanProcessor(BatchSpanProcessor.builder(
            OtlpGrpcSpanExporter.builder().build()
        ).build())
        .build())
    .buildAndRegisterGlobal();

// 2. 注册 OpenCensus Bridge
// 将 OpenCensus 的 Traces 和 Metrics 桥接到 OTel
OpenCensusTraceBridge.create().register(otelSdk.getTracerProvider());
OpenCensusMetricBridge.create().register(otelSdk.getMeterProvider());

// 3. 后续代码可以继续使用 OpenCensus API
// 这些数据会自动通过 OTel SDK 导出
Tracer ocTracer = io.opencensus.trace.Tracing.getTracer();
Span ocSpan = ocTracer.spanBuilder("legacyOperation").startSpan();
// ... OpenCensus 代码不变
```

### 4.3 Go 桥接配置

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/bridge/opencensus"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// 1. 初始化 OTel SDK
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(otlptracegrpc.NewClient()),
)
otel.SetTracerProvider(tp)

// 2. 安装 Bridge
// 将 OpenCensus DefaultTracer 桥接到 OTel
tracer := tp.Tracer("opencensus-bridge")
opencensus.InstallTraceBridge(tracer)

// 3. OpenCensus 代码继续工作
// ctx, span := opencensus.StartSpan(ctx, "legacy")
```

### 4.4 Python 桥接配置

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.shim.opencensus import install_shim

# 1. 初始化 OTel SDK
provider = TracerProvider()
provider.add_span_processor(BatchSpanProcessor(OTLPSpanExporter()))
trace.set_tracer_provider(provider)

# 2. 安装 Shim
# 这会拦截 OpenCensus 的 trace 调用，转发到 OTel
shim = install_shim(provider)

# 3. 继续使用 OpenCensus API
from opencensus.trace.tracer import Tracer as OcTracer
oc_tracer = OcTracer()
with oc_tracer.span("legacy_operation"):
    pass
```

### 4.5 Bridge 的性能影响

| 指标 | 无 Bridge | 有 Bridge | 说明 |
|------|----------|----------|------|
| Span 创建开销 | 基准 | +10~30% | 额外的一层转换 |
| 内存占用 | 基准 | +5~15% | Bridge 缓存和映射结构 |
| 导出延迟 | 基准 | 基本一致 | 最终走同一 Exporter |

**建议**: Bridge 是临时方案，不应长期运行于生产环境。完成代码迁移后应立即移除。

---

## 五、Collector 侧兼容方案

如果应用侧暂时无法改动，可通过 OpenTelemetry Collector 接收 OpenCensus 数据：

### 5.1 Collector 配置

```yaml
# collector-config.yaml
receivers:
  opencensus:
    endpoint: 0.0.0.0:55678
    # OpenCensus Agent 默认端口
    transport: grpc

  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  otlp/new-backend:
    endpoint: otel-backend:4317

  prometheusremotewrite:
    endpoint: http://prometheus:9090/api/v1/write

service:
  pipelines:
    traces:
      receivers: [opencensus, otlp]
      processors: [batch]
      exporters: [otlp/new-backend]
    metrics:
      receivers: [opencensus, otlp]
      processors: [batch]
      exporters: [prometheusremotewrite]
```

### 5.2 应用侧修改（最小改动）

仅需将 OpenCensus Exporter 的导出目标从原后端改为 Collector：

```java
// 原来直接导出到后端
// OcAgentTraceExporter.create("old-backend", 55678);

// 改为导出到本地 Collector
OcAgentTraceExporter.create("localhost", 55678);
```

---

## 六、数据模型差异与处理

### 6.1 Trace 数据映射

| OpenCensus 字段 | OTLP 对应字段 | 处理方式 |
|----------------|--------------|---------|
| `trace_id` (16 bytes) | `trace_id` (16 bytes) | 直接透传 |
| `span_id` (8 bytes) | `span_id` (8 bytes) | 直接透传 |
| `parent_span_id` | `parent_span_id` | 直接透传 |
| `name` | `name` | 直接透传 |
| `kind` | `kind` | 枚举值映射（SERVER/CLIENT/PRODUCER/CONSUMER/INTERNAL）|
| `start_time` | `start_time_unix_nano` | 时间戳格式转换 |
| `end_time` | `end_time_unix_nano` | 时间戳格式转换 |
| `status.code` | `status.code` | OK → UNSET, CANCELLED/UNKNOWN/etc. → ERROR |
| `status.message` | `status.message` | 直接透传 |
| `attributes` | `attributes` | 类型转换（OC AttributeValue → OTel AnyValue）|
| `time_events` | `events` | 名称和时间戳映射 |
| `links` | `links` | 直接透传 |
| `tracestate` | `tracestate` | 直接透传（如有）|

### 6.2 Metric 数据映射

OpenCensus 的 Metric 模型与 OpenTelemetry 差异较大：

```text
OpenCensus Metric 模型:
Measure → Record → View → Aggregation → Exporter
            ↑
         Tags (维度)

OpenTelemetry Metric 模型:
Instrument → Add/Record/Observe → Aggregation (View) → MetricReader → Exporter
                ↑
            Attributes (维度)
```

**关键差异**:

- OpenCensus 的 `Measure` 是抽象概念，实际数据通过 `View` 定义聚合方式
- OpenTelemetry 的 `Instrument` 直接定义聚合类型（Counter、Histogram、Gauge、Observable）
- `Tag` → `Attribute` 的语义基本一致，但属性命名需遵循 Semantic Conventions

**迁移建议**: Metrics 不建议使用 Bridge 长期运行，因为聚合语义可能存在差异。建议在应用代码中直接重写 Metric 部分。

---

## 七、常见陷阱与解决方案

### 7.1 采样不一致

**问题**: OpenCensus Sampler 和 OpenTelemetry Sampler 的决策可能不一致，导致 Trace 片段断裂。

**解决**:

- 迁移期间统一使用 `AlwaysOn` Sampler，确保数据完整
- 或配置一致的采样策略（如都使用概率采样且比率相同）
- 使用 ParentBased Sampler，让根节点决定采样

### 7.2 传播格式兼容性

**问题**: 如果部分服务用 OpenCensus（B3 格式），部分用 OpenTelemetry（W3C Trace Context），传播会断裂。

**解决**:

- 在 OpenTelemetry 中同时启用 W3C 和 B3 传播器：

  ```
  OTEL_PROPAGATORS=tracecontext,baggage,b3
  ```

- 逐步将所有服务统一到 W3C Trace Context

### 7.3 指标名称变化

**问题**: 迁移后指标名称改变，导致现有监控告警和仪表盘失效。

**解决**:

- 使用 OpenTelemetry Collector 的 `metricstransform` processor 重命名指标
- 或更新 Grafana/Prometheus 中的查询语句
- 建立指标名称映射文档

### 7.4 Resource 属性缺失

**问题**: OpenCensus 中部分资源属性在 OpenTelemetry 中命名不同或缺失。

**解决**:

- 对照 Semantic Conventions 更新 Resource 属性键名
- 常见映射：`host.name`（相同）、`service.name`（相同）、`process.pid`（相同）

---

## 八、检查清单

### 迁移前

- [ ] 盘点所有使用 OpenCensus 的服务、库和脚本
- [ ] 确认目标语言的 OpenTelemetry SDK 和 Bridge 可用
- [ ] 评估指标和追踪数据量，规划 Collector 资源
- [ ] 准备回滚方案

### 迁移中

- [ ] Collector 侧配置 OpenCensus Receiver
- [ ] 应用侧引入 Bridge（如采用渐进模式）
- [ ] 验证 Trace 完整性（端到端链路不断裂）
- [ ] 验证 Metric 准确性（关键指标数值一致）
- [ ] 性能测试对比（CPU、内存、延迟）

### 迁移后

- [ ] 所有 OpenCensus API 调用已替换为 OTel API
- [ ] 移除 OpenCensus 依赖和 Bridge
- [ ] 更新监控告警规则
- [ ] 更新运维文档和 Runbook
- [ ] 团队培训完成

---

## 九、参考资源

- OpenTelemetry Specification: Compatibility / OpenCensus
- OpenTelemetry OpenCensus Bridge（各语言 SDK 文档）
- OpenTelemetry Collector: OpenCensus Receiver
- OpenCensus 官方归档文档

---

> **总结**: OpenCensus 迁移不是一蹴而就的过程。推荐的**桥接渐进迁移**模式可以在保障数据连续性的前提下，逐步完成技术栈升级。关键成功因素是：先在基础设施层部署 OpenTelemetry Collector 建立兼容通道，然后利用 Bridge 让应用侧平滑过渡，最后逐模块完成代码替换。
