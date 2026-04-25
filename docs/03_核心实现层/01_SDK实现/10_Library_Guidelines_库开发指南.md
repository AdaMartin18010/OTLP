# Library Guidelines / 库开发指南

> **标准来源**: OpenTelemetry Specification v1.56.0 — Library Guidelines
> **适用对象**: 框架开发者、库作者、平台工程师
> **核心目标**: 帮助第三方库以无侵入、低耦合的方式集成 OpenTelemetry，确保最终应用可自由选择是否启用可观测性

---

## 一、核心原则

### 1.1 API 与实现的严格分离

**必须**将 OpenTelemetry API 与 SDK 实现作为独立的制品（artifact）提供。这是整个生态的基石。

```
┌─────────────────────────────────────────────┐
│           第三方库 / 框架                      │
│  ┌─────────────────────────────────────┐    │
│  │  仅依赖 opentelemetry-api           │    │
│  │  (api-trace, api-metrics, api-logs) │    │
│  └─────────────────────────────────────┘    │
└─────────────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────┐
│           最终应用 (End-User App)            │
│  ┌─────────────────────────────────────┐    │
│  │  决定是否引入 opentelemetry-sdk     │    │
│  │  并配置 Exporter、Sampler 等插件   │    │
│  └─────────────────────────────────────┘    │
└─────────────────────────────────────────────┘
```

**关键约束**:

- 库代码**不得**直接依赖任何 SDK 实现包
- 库代码**不得**假设 SDK 已安装
- 如果 SDK 未安装，API 调用必须是**空操作（no-op）**，且开销趋近于零

### 1.2 最小实现（Minimal Implementation）的自给自足性

当应用中仅有 API 包而无 SDK 包时，API 包内部的最小实现**必须**满足：

| 要求 | 说明 |
|------|------|
| 不抛异常 | 所有 API 方法在任何情况下都不得抛出异常 |
| 返回有效对象 | `TracerProvider.getTracer()` 必须返回非空 Tracer；`Tracer.startSpan()` 必须返回非空 Span |
| 零性能损耗 | 空操作实现的开销应尽可能接近直接返回常量对象 |
| 无需调用者判断 | 调用方不需要检查"是否启用了 OTel"，直接调用即可 |

### 1.3 最终应用的配置自主权

最终应用开发者**必须**能够：

- 自由选择是否安装 SDK
- 自由选择使用哪个厂商的 Exporter
- 自由配置采样策略、批处理参数、资源属性
- 在不修改第三方库源码的情况下，开启或关闭可观测性

---

## 二、包结构规范

### 2.1 推荐的包/模块命名

按信号类型拆分包结构是推荐做法，但不是强制要求。关键在于**API 制品与 SDK 制品必须物理分离**。

```
# Java/Maven 风格示例
opentelemetry-api              # 核心 API（上下文、 baggage）
opentelemetry-api-trace        # Tracing API
opentelemetry-api-metrics      # Metrics API
opentelemetry-api-logs         # Logs Bridge API
opentelemetry-sdk              # SDK 核心
opentelemetry-sdk-trace        # Tracing SDK
opentelemetry-sdk-metrics      # Metrics SDK
opentelemetry-sdk-logs         # Logs SDK
opentelemetry-sdk-common      # 共享组件（Resource、ID Generator 等）
```

```
# JavaScript/npm 风格示例
@opentelemetry/api
@opentelemetry/api-logs
@opentelemetry/sdk-trace-base
@opentelemetry/sdk-metrics
```

### 2.2 语义约定包

建议将语义约定（Semantic Conventions）单独打包，供库和应用共同使用：

```
opentelemetry-semantic-conventions
```

此包仅包含属性名称常量、枚举值等，**不得**包含 API 或 SDK 逻辑。

---

## 三、错误处理规范

### 3.1 全局原则

第三方库中的 OpenTelemetry 集成代码**必须**遵循"快速失败但不传播"的原则：

- **不得**因为可观测性代码的问题导致业务逻辑失败
- **不得**在 API 调用链上抛出可观测性相关的异常
- **应该**在内部捕获并记录（静默丢弃）可观测性错误

### 3.2 典型场景处理

| 场景 | 推荐做法 |
|------|---------|
| 获取 Tracer 失败 | 返回一个 no-op Tracer，业务逻辑继续 |
| Span 创建失败 | 返回一个 no-op Span，后续所有 Span 操作安全忽略 |
| Exporter 导出失败 | 由 SDK 层处理重试/丢弃，库代码不感知 |
| 属性设置失败（类型不匹配） | 丢弃该属性，继续处理其他属性 |
| Context 传播失败 | 回退到不传播，业务调用继续 |

### 3.3 诊断机制

虽然错误应该被静默处理，但库**可以**提供可选的诊断日志（通过标准日志框架或回调接口），帮助开发者在调试时发现配置问题。这些诊断机制**必须**默认关闭。

---

## 四、库的插桩模式

### 4.1 手动插桩（Manual Instrumentation）

适用于库作者希望精确控制追踪粒度的场景。

```java
// Java 示例：HTTP 客户端库的插桩
public class MyHttpClient {
    private final Tracer tracer;

    public MyHttpClient() {
        // 通过全局 TracerProvider 获取 Tracer
        // 如果 SDK 未安装，这会自动返回 no-op 实现
        this.tracer = GlobalOpenTelemetry.getTracer("my-http-client", "1.0.0");
    }

    public Response execute(Request request) {
        // 从当前 Context 中提取父 Span
        Span parentSpan = Span.current();

        // 创建子 Span
        Span span = tracer.spanBuilder("HTTP " + request.getMethod())
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute(SemanticAttributes.HTTP_REQUEST_METHOD, request.getMethod())
            .setAttribute(SemanticAttributes.URL_FULL, request.getUrl())
            .startSpan();

        // 将 Span 注入 Context，供下游传播
        try (Scope scope = span.makeCurrent()) {
            // 注入传播头到 HTTP 请求
            OpenTelemetry.getPropagators()
                .getTextMapPropagator()
                .inject(Context.current(), request, RequestSetter.INSTANCE);

            Response response = doExecute(request);

            // 记录响应属性
            span.setAttribute(SemanticAttributes.HTTP_RESPONSE_STATUS_CODE, response.getStatusCode());
            if (response.getStatusCode() >= 400) {
                span.setStatus(StatusCode.ERROR);
            }
            return response;
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }
}
```

### 4.2 自动/包装器插桩（Wrapper/Interceptor Pattern）

适用于库提供拦截点或中间件机制的场景。

```javascript
// Node.js 示例：Express 中间件风格的包装器
function createTelemetryMiddleware(tracerName) {
  const tracer = opentelemetry.trace.getTracer(tracerName);

  return function telemetryMiddleware(req, res, next) {
    const span = tracer.startSpan(`${req.method} ${req.route}`, {
      kind: SpanKind.SERVER,
      attributes: {
        'http.request.method': req.method,
        'url.path': req.path,
      }
    });

    // 绑定上下文
    const ctx = opentelemetry.trace.setSpan(opentelemetry.context.active(), span);

    // 使用上下文执行后续逻辑
    opentelemetry.context.with(ctx, () => {
      res.on('finish', () => {
        span.setAttribute('http.response.status_code', res.statusCode);
        span.end();
      });
      next();
    });
  };
}
```

### 4.3 无侵入插桩建议

如果库无法直接修改源码添加插桩，**应该**提供：

- 清晰的扩展点（如拦截器接口、生命周期回调）
- 独立的 instrumentation 包（可选插件）
- 使用说明文档，指导最终应用如何启用

---

## 五、上下文传播规范

### 5.1 传播器使用

库在跨进程调用时**必须**使用 OpenTelemetry 的 TextMapPropagator 进行上下文传播：

```java
// 注入端（客户端/调用方）
TextMapPropagator propagator = openTelemetry.getPropagators().getTextMapPropagator();
propagator.inject(context, carrier, setter);

// 提取端（服务端/被调用方）
Context context = propagator.extract(Context.current(), carrier, getter);
```

### 5.2 支持的传播格式

默认**必须**支持 W3C Trace Context 和 W3C Baggage。可以额外支持其他格式（如 B3、Jaeger），但**不得**作为默认行为。

### 5.3 消息队列与异步场景

在消息队列（Kafka、RabbitMQ 等）场景中，上下文**应该**被序列化到消息元数据（headers/attributes）中：

```python
# Python 示例：Kafka Producer 注入
from opentelemetry.propagate import inject

headers = {}
inject(headers)
producer.send('topic', value=data, headers=list(headers.items()))

# Kafka Consumer 提取
from opentelemetry.propagate import extract

carrier = {k: v for k, v in msg.headers}
context = extract(carrier)
```

---

## 六、资源检测（Resource Detection）

### 6.1 库的角色

库**不应该**主动创建或修改 Resource。Resource 是最终应用级别的概念，由应用或 SDK 在初始化时配置。

### 6.2 例外情况

如果库代表一个明确的服务边界（如一个独立的 sidecar 代理、插件系统中的一个插件），**可以**提供辅助函数帮助检测该组件的资源属性，但这些函数**必须**：

- 放在独立的包中（不污染核心 API 依赖）
- 由最终应用显式调用
- 遵循 Semantic Conventions 的命名规范

---

## 七、性能要求

### 7.1 对库作者的要求

| 场景 | 要求 |
|------|------|
| API 调用开销 | 当 SDK 未安装时，单次 API 调用耗时 < 10ns 量级（返回常量对象） |
| Context 传播 | 不得触发额外的堆分配或锁竞争（在 no-op 路径上） |
| 属性设置 | 字符串/原始类型属性设置应为 O(1) 操作 |
| Span 创建 | 即使创建了 Span，如果未被采样，后续操作应尽量轻量 |

### 7.2 批量与异步

库代码**不应该**自行实现批处理、队列或重试逻辑。这些复杂性由 SDK 的 Exporter 层统一处理。库只需同步调用 API 即可。

---

## 八、版本与兼容性

### 8.1 语义化版本

API 包和 SDK 包的版本**必须**独立遵循语义化版本（SemVer）。库作者只需声明对 `opentelemetry-api` 的版本依赖范围。

### 8.2 兼容性策略

| 层级 | 兼容性承诺 |
|------|-----------|
| API 包 | 稳定后保持向后兼容，废弃 API 保留至少一个主版本周期 |
| SDK 包 | 允许在次要版本间增加功能，主版本可引入破坏性变更 |
| Semantic Conventions | 属性稳定后不变更，实验性属性可能变化 |

---

## 九、检查清单

在发布一个集成 OpenTelemetry 的库之前，请确认：

- [ ] 库仅依赖 `opentelemetry-api`，不依赖任何 SDK 包
- [ ] 无 SDK 时，所有 API 调用安全且不抛异常
- [ ] 提供了 no-op 路径的性能基准测试，确认开销可忽略
- [ ] 跨进程调用使用了标准的 TextMapPropagator 注入/提取
- [ ] 遵循了 Semantic Conventions 的命名规范
- [ ] 错误处理遵循"静默失败、不影响业务"原则
- [ ] 文档说明了最终用户如何启用/配置可观测性
- [ ] 提供了集成测试示例，展示 SDK 安装前后的行为差异

---

## 十、参考资源

- OpenTelemetry Specification: Library Guidelines
- OpenTelemetry Specification: Performance
- OpenTelemetry Specification: Error Handling
- Semantic Conventions: General Guidelines

---

> **总结**: 第三方库的 OpenTelemetry 集成核心哲学是"**只依赖 API，不假设 SDK 存在，零侵入，零副作用**"。遵循本指南可确保您的库既能提供丰富的可观测性能力，又不会给不使用的用户带来任何负担。
