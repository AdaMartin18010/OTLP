# OpenTracing 迁移完整指南

> **标准来源**: OpenTelemetry Specification v1.56.0 — Compatibility / OpenTracing
> **目标读者**: 仍在使用 OpenTracing 的遗留系统维护者、框架开发者
> **核心目标**: 提供从 OpenTracing 到 OpenTelemetry 的完整迁移路径

---

## 一、背景

### 1.1 OpenTracing 项目状态

OpenTracing 已于 **2019 年与 OpenCensus 合并为 OpenTelemetry**，进入归档状态：

```text
┌─────────────────────────────────────────────────────────────┐
│  OpenTracing 现状                                            │
├─────────────────────────────────────────────────────────────┤
│  • 2019 年：与 OpenCensus 合并，形成 OpenTelemetry           │
│  • 不再接受任何新功能或修复                                   │
│  • 部分语言绑定（如 C++）的维护已完全停止                     │
│  • 后端支持逐步转向 OTLP 原生接收                            │
│  • 新兴工具和框架不再提供 OpenTracing 集成                    │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 为什么 OpenTracing 用户需要特别关注迁移？

相比 OpenCensus，OpenTracing 的迁移有其特殊性：

- **API 哲学差异更大**: OpenTracing 是"接口优先"的抽象规范，无官方实现；OpenTelemetry 是"实现优先"的完整框架
- **Shim/Bridge 更成熟**: 由于 OpenTracing 的接口抽象性，OTel 提供了更完善的 Shim 层
- **数据模型差异**: OpenTracing 的 `Log` 概念在 OTel 中分裂为 `Span Event` 和 `LogRecord`

---

## 二、核心概念映射

### 2.1 概念对照表

| OpenTracing 概念 | OpenTelemetry 对应概念 | 差异说明 |
|----------------|----------------------|---------|
| `Tracer` | `Tracer` | 直接对应，创建方式略有不同 |
| `Span` | `Span` | 直接对应 |
| `SpanContext` | `SpanContext` | OTel 增加了 `trace_flags` 字段（采样标志）|
| `References` (ChildOf/FollowsFrom) | `Links` + Span 父子关系 | ChildOf → 父子关系；FollowsFrom → Link |
| `Baggage` | `Baggage` | 概念一致，OTel 遵循 W3C 标准格式 |
| `Tags` | `Attributes` | 名称变化，OTel 属性类型更丰富 |
| `Logs` | `Span Events` / `LogRecords` | OTel 区分了 Span 内事件和独立日志 |
| `Span.finish()` | `Span.end()` | 方法名变化 |
| `Span.setTag()` | `Span.setAttribute()` | 方法名变化 |
| `Span.log()` | `Span.addEvent()` / `Span.recordException()` | 语义拆分 |
| `Format.Builtin.HTTP_HEADERS` | `TextMapPropagator` | 传播器概念一致，API 不同 |

### 2.2 关键 API 差异

#### Span 创建

```java
// OpenTracing (Java)
Tracer tracer = GlobalTracer.get();
Span span = tracer.buildSpan("processOrder")
    .withTag("order.id", "12345")
    .withTag(Tags.SPAN_KIND.getKey(), Tags.SPAN_KIND_SERVER)
    .start();

// OpenTelemetry (Java)
Tracer tracer = GlobalOpenTelemetry.getTracer("my-app", "1.0.0");
Span span = tracer.spanBuilder("processOrder")
    .setAttribute("order.id", "12345")
    .setSpanKind(SpanKind.SERVER)
    .startSpan();
```

#### Span 结束与异常

```java
// OpenTracing
span.finish();

// 异常记录
span.log(ImmutableMap.of(
    "event", "error",
    "error.object", exception
));

// OpenTelemetry
span.end();

// 异常记录（推荐方式）
span.recordException(exception);
span.setStatus(StatusCode.ERROR, exception.getMessage());
```

#### 上下文传播

```java
// OpenTracing: 注入
tracer.inject(
    span.context(),
    Format.Builtin.HTTP_HEADERS,
    new RequestBuilderCarrier(requestBuilder)
);

// OpenTelemetry: 注入
OpenTelemetry.getPropagators()
    .getTextMapPropagator()
    .inject(Context.current(), request, setter);

// OpenTracing: 提取
SpanContext parentSpanCtx = tracer.extract(
    Format.Builtin.HTTP_HEADERS,
    new TextMapExtractAdapter(headers)
);

// OpenTelemetry: 提取
Context context = OpenTelemetry.getPropagators()
    .getTextMapPropagator()
    .extract(Context.current(), headers, getter);
```

---

## 三、Shim 模式详解

### 3.1 OpenTracing Shim 原理

OpenTracing Shim 是一个**适配层**，它将 OpenTracing API 调用翻译为 OpenTelemetry API 调用：

```text
应用代码（OpenTracing API）
    │
    ▼
┌─────────────────────┐
│ OpenTracing Shim    │  ← 拦截 OT API 调用
│ (Tracer, Span, etc.)│
└─────────────────────┘
    │
    ▼
OpenTelemetry SDK
    │
    ▼
OTLP Exporter
```

与 OpenCensus Bridge 不同，Shim 通常在**API 层**完成转换，而非在 SDK 层。

### 3.2 Java Shim 配置

```java
// 1. 初始化 OpenTelemetry SDK（标准方式）
OpenTelemetrySdk openTelemetry = OpenTelemetrySdk.builder()
    .setTracerProvider(SdkTracerProvider.builder()
        .addSpanProcessor(BatchSpanProcessor.builder(
            OtlpGrpcSpanExporter.builder().build()
        ).build())
        .build())
    .buildAndRegisterGlobal();

// 2. 创建 OpenTracing Shim
// 将 OpenTracing GlobalTracer 桥接到 OTel
io.opentelemetry.opentracingshim.OpenTracingShim shim =
    new io.opentelemetry.opentracingshim.OpenTracingShim(openTelemetry);

tracer = shim.tracer("shimmed-tracer");

// 3. 设置到 OpenTracing GlobalTracer
// 这样现有的 OpenTracing 代码无需修改即可工作
io.opentracing.util.GlobalTracer.register(tracer);
```

### 3.3 Go Shim 配置

```go
import (
    "github.com/opentracing/opentracing-go"
    "go.opentelemetry.io/otel"
    otelshim "go.opentelemetry.io/otel/bridge/opentracing"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// 1. 初始化 OTel SDK
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(otlptracegrpc.NewClient()),
)
otel.SetTracerProvider(tp)

// 2. 创建 Shim，包装 OTel TracerProvider
shim := otelshim.NewTracerProvider(tp, otelshim.WithPropagators(
    propagation.TraceContext{},
    propagation.Baggage{},
))

// 3. 设置为全局 OpenTracing Tracer
opentracing.SetGlobalTracer(shim.Tracer("shim"))

// 4. 现有 OpenTracing 代码继续工作
// span := opentracing.StartSpan("legacy-operation")
```

### 3.4 Python Shim 配置

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.shim.opentracing_shim import create_tracer

# 1. 初始化 OTel SDK
provider = TracerProvider()
trace.set_tracer_provider(provider)

# 2. 创建 Shim Tracer
shim_tracer = create_tracer(provider, "shim")

# 3. 替换现有代码中的 OpenTracing tracer
# 原有: import opentracing; tracer = opentracing.tracer
# 改为: tracer = shim_tracer
```

### 3.5 JavaScript/Node.js Shim

```javascript
const { NodeSDK } = require('@opentelemetry/sdk-node');
const { OpenTracingShim } = require('@opentelemetry/shim-opentracing');

// 1. 初始化 OTel SDK
const sdk = new NodeSDK({
  traceExporter: new OTLPTraceExporter(),
});
sdk.start();

// 2. 创建 Shim
const shim = new OpenTracingShim(sdk.getTracerProvider());

// 3. 现有 OpenTracing 代码使用 shim tracer
// const span = shim.startSpan('legacy-operation');
```

---

## 四、数据模型差异处理

### 4.1 References → Links 映射

OpenTracing 的 `References` 有两种类型，在 OTel 中的处理方式：

```java
// OpenTracing
Span parent = tracer.buildSpan("parent").start();
Span child = tracer.buildSpan("child")
    .asChildOf(parent)          // ChildOf Reference
    .addReference(
        References.FOLLOWS_FROM,
        someOtherSpan.context()  // FollowsFrom Reference
    )
    .start();

// OpenTelemetry 等价写法
// ChildOf → 通过 Context 传递父子关系
Context parentCtx = Context.current().with(parentSpan);
Span child = tracer.spanBuilder("child")
    .setParent(parentCtx)
    .startSpan();

// FollowsFrom → 使用 Link
Span followsFrom = tracer.spanBuilder("follows-from")
    .addLink(otherSpan.getSpanContext(), Attributes.builder()
        .put(AttributeKey.stringKey("link.type"), "follows_from")
        .build())
    .startSpan();
```

### 4.2 Logs → Events 映射

OpenTracing 的 `Span.log()` 在 OTel 中映射为 `Span.addEvent()`：

```java
// OpenTracing
span.log(ImmutableMap.of(
    "event", "cache_miss",
    "cache.key", "user:12345",
    "duration_ms", 15
));

// OpenTelemetry
span.addEvent("cache_miss", Attributes.builder()
    .put("cache.key", "user:12345")
    .put("duration_ms", 15)
    .build());
```

**特殊处理**: OpenTracing 中 `event: "error"` 的日志通常表示异常，在 OTel 中应使用 `recordException()`：

```java
// OpenTracing 的错误日志
span.log(ImmutableMap.of(
    "event", "error",
    "error.kind", "TimeoutException",
    "message", "Connection timed out"
));

// OpenTelemetry 推荐
span.recordException(new TimeoutException("Connection timed out"));
span.setStatus(StatusCode.ERROR, "Connection timed out");
```

### 4.3 Tags → Attributes 命名规范

OpenTracing 的 Tag 命名较为自由，迁移到 OTel 时建议遵循 Semantic Conventions：

| OpenTracing Tag | OpenTelemetry Semantic Convention |
|----------------|-----------------------------------|
| `http.method` | `http.request.method` |
| `http.url` | `url.full` |
| `http.status_code` | `http.response.status_code` |
| `db.type` | `db.system` |
| `db.instance` | `db.name` |
| `peer.service` | `peer.service`（相同）|
| `span.kind` | `SpanKind`（结构字段，非属性）|
| `sampling.priority` | 通过 `trace_flags` 和 Sampler 实现 |

---

## 五、传播器兼容性

### 5.1 OpenTracing 传播格式

OpenTracing 本身不强制传播格式，但常见实现使用：

- **Jaeger 格式**: `uber-trace-id` HTTP 头
- **B3 格式**: `X-B3-TraceId`, `X-B3-SpanId` 等（Zipkin 生态）
- **自定义格式**: 部分厂商自定义

### 5.2 迁移期间的传播策略

在混合环境（部分服务 OT，部分服务 OTel）中，Collector 应配置多传播器支持：

```yaml
# Collector 配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
    # 自动识别多种传播格式

processors:
  # 可选：将 Jaeger/B3 格式统一转换为 W3C

exporters:
  otlp:
    endpoint: backend:4317
```

应用侧配置：

```bash
# OpenTelemetry SDK 同时启用多种传播器
OTEL_PROPAGATORS=tracecontext,baggage,jaeger,b3
```

---

## 六、渐进式迁移路线图

### 6.1 推荐路线

```text
阶段 1：基础设施准备（1-2 周）
├── 部署 OpenTelemetry Collector
├── 配置 Jaeger Receiver（如原使用 Jaeger 后端）
└── 验证数据流入新 Pipeline

阶段 2：Shim 引入（1-2 周）
├── 在不修改业务代码的情况下引入 OpenTracing Shim
├── 将 GlobalTracer 替换为 Shim Tracer
├── 验证 Trace 完整性和后端兼容性
└── 更新 CI/CD 中的依赖

阶段 3：代码替换（4-8 周）
├── 新功能直接使用 OpenTelemetry API
├── 逐步重写核心模块的 OpenTracing 代码
│   ├── 优先替换手动 Span 创建逻辑
│   ├── 然后替换自动插桩（Instrumentation）
│   └── 最后替换自定义传播逻辑
├── 每替换一个模块，运行集成测试验证
└── 更新单元测试中的 Mock/Stub

阶段 4：清理（2-4 周）
├── 移除 OpenTracing 依赖
├── 移除 Shim
├── 优化 OTel 配置
└── 文档更新
```

### 6.2 代码替换优先级

| 优先级 | 组件类型 | 原因 |
|--------|---------|------|
| P0 | 手动创建的 Span（业务逻辑中）| 影响数据完整性最直接 |
| P1 | 自动插桩（HTTP/DB 客户端）| 可由 OTel Instrumentation 替代 |
| P2 | 自定义传播器 | 通常可用标准传播器替代 |
| P3 | Baggage 操作 | API 差异小，替换简单 |
| P4 | 测试代码中的 Mock Tracer | 最后处理，不影响生产 |

---

## 七、检查清单

### 迁移前评估

- [ ] 统计代码中 OpenTracing API 的调用点数量
- [ ] 确认使用的传播格式（Jaeger / B3 / 自定义）
- [ ] 确认是否使用了 OpenTracing Contrib 的 Instrumentation
- [ ] 评估 Shim 引入对性能的影响

### Shim 阶段

- [ ] OpenTracing Shim 正确初始化并注册为 GlobalTracer
- [ ] Trace 端到端完整性验证（跨服务链路不断裂）
- [ ] Baggage 传播验证
- [ ] 性能基准对比（Shim 引入前后的 CPU/内存/延迟）

### 代码替换阶段

- [ ] `buildSpan()` → `spanBuilder()`
- [ ] `finish()` → `end()`
- [ ] `setTag()` → `setAttribute()`
- [ ] `log()` → `addEvent()` / `recordException()`
- [ ] `asChildOf()` → `setParent()`
- [ ] `addReference(FOLLOWS_FROM)` → `addLink()`
- [ ] 传播器代码更新为 `TextMapPropagator`

### 清理阶段

- [ ] 移除 `opentracing-api` 依赖
- [ ] 移除 OpenTracing Instrumentation 依赖
- [ ] 移除 Shim 依赖
- [ ] 更新导入语句（`io.opentracing.*` → `io.opentelemetry.*`）

---

## 八、参考资源

- OpenTelemetry Specification: Compatibility / OpenTracing
- OpenTelemetry OpenTracing Shim（各语言 SDK 文档）
- OpenTracing 官方归档仓库（github.com/opentracing）
- Jaeger 客户端迁移指南（Jaeger 官方文档）

---

> **总结**: OpenTracing 到 OpenTelemetry 的迁移相对平滑，主要得益于成熟的 Shim 层。核心建议是：先通过 Shim 让现有代码在 OTel Pipeline 上运行起来，然后按"手动 Span → 自动插桩 → 传播器"的顺序逐步替换代码。特别注意 `log()` 到 `addEvent()`/`recordException()` 的语义拆分，以及 `References` 到 `Links` 的映射。
