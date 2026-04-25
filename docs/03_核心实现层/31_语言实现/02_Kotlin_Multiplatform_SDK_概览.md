# Kotlin Multiplatform SDK 概览

> **标准来源**: OpenTelemetry Kotlin Multiplatform SDK (活跃开发, 2026-03)
> **核心目标**: 介绍 OpenTelemetry Kotlin Multiplatform SDK 的架构、状态、与现有 SDK 的关系

---

## 一、背景

### 1.1 为什么需要 Kotlin Multiplatform SDK？

Kotlin Multiplatform (KMP) 允许开发者使用 Kotlin 编写跨平台代码，同时编译为：

```text
Kotlin Multiplatform 目标平台:
├── JVM（服务端、Android）
├── Android Native（NDK）
├── iOS（通过 Kotlin/Native）
├── macOS、watchOS、tvOS（通过 Kotlin/Native）
├── JavaScript / TypeScript（浏览器、Node.js）
├── WebAssembly（Wasm）
└── 未来: 更多原生平台

价值:
├── 一套代码覆盖移动端（Android + iOS）
├── 与现有 Kotlin 生态（Ktor、 kotlinx.coroutines）无缝集成
├── 减少跨平台可观测性实现的分裂
└── 特别适合 Kotlin-first 的团队
```

### 1.2 与现有 SDK 的关系

| 场景 | 推荐 SDK | 说明 |
|------|---------|------|
| 纯 Android 应用 | OpenTelemetry Android SDK | 功能最完整，与 Android 生命周期深度集成 |
| 纯 iOS 应用 | OpenTelemetry Swift SDK | 功能最完整，与 iOS 生命周期深度集成 |
| Kotlin Multiplatform 共享模块 | **Kotlin Multiplatform SDK** | 共享业务逻辑中的可观测性代码 |
| 纯服务端（JVM）| OpenTelemetry Java SDK | 最成熟，生态最丰富 |

**注意**: Kotlin Multiplatform SDK 定位为**共享模块层**的可观测性，不是 Android/iOS 平台特定功能的替代品。

---

## 二、架构设计

### 2.1 分层架构

```text
Kotlin Multiplatform SDK 架构:

共享层 (Common Kotlin)
├── API: Tracer、Span、Baggage、Context
├── SDK Core: Sampler、Resource、ID Generator
└── 平台无关的数据模型

平台层 (Platform-specific)
├── JVM
│   ├── 使用 Java SDK 底层实现
│   └── 网络导出使用 OkHttp / Ktor Client
├── Android
│   ├── 集成 Android 生命周期（Activity、Fragment）
│   └── 使用 WorkManager 进行后台导出
├── iOS / Native
│   ├── 使用 Kotlin/Native 与 Objective-C/Swift 互操作
│   └── 网络导出使用 NSURLSession
├── JS / Wasm
│   ├── 使用 Kotlin/JS 运行时
│   └── 网络导出使用 Fetch API
└── 平台特定的 Propagator 实现
```

### 2.2 与 kotlinx.coroutines 集成

```kotlin
// Kotlin: 与协程上下文集成
import io.opentelemetry.kotlin.api.trace.Tracer
import io.opentelemetry.kotlin.extension.kotlin.asContextElement
import kotlinx.coroutines.withContext

suspend fun processOrder(orderId: String) {
    val span = tracer.spanBuilder("processOrder")
        .setAttribute("order.id", orderId)
        .startSpan()

    // 将 Span 上下文注入协程上下文
    withContext(span.asContextElement()) {
        // 此协程作用域内的所有 Span 自动关联
        validateOrder(orderId)
        chargePayment(orderId)
        fulfillOrder(orderId)
    }

    span.end()
}
```

---

## 三、当前状态（2026-04）

### 3.1 功能成熟度

| 功能 | 状态 | 说明 |
|------|------|------|
| **Tracing API** | 🟡 Alpha | 核心 API 可用，接口可能微调 |
| **Tracing SDK** | 🟡 Alpha | Span 处理、导出基础实现 |
| **Metrics API** | 🔴 开发中 | 初步设计完成 |
| **Metrics SDK** | 🔴 未开始 | 等待 Metrics API 稳定 |
| **Logs API** | 🔴 未开始 | 低优先级 |
| **Context Propagation** | 🟡 Alpha | W3C Trace Context 基本实现 |
| **Baggage** | 🟡 Alpha | 基础实现 |
| **Resource** | 🟢 Beta | 基本稳定 |
| **OTLP Exporter** | 🟡 Alpha | JVM/Android 可用，Native 开发中 |

### 3.2 已知限制

```text
当前限制:
├── iOS 导出器性能待优化（Kotlin/Native 与 NSURLSession 桥接开销）
├── JS 目标平台的 Bundle 体积较大
├── 缺少平台特定的自动 Instrumentation（如 Ktor Client/Server）
├── 文档和示例不足
└── 与 OpenTelemetry Java SDK 的共存策略待明确
```

---

## 四、使用示例

### 4.1 Ktor 服务端集成

```kotlin
// Ktor Server: 手动插桩
fun Application.module() {
    val tracer = OpenTelemetry.getTracer("ktor-server")

    intercept(ApplicationCallPipeline.Monitoring) {
        val span = tracer.spanBuilder("${call.request.httpMethod.value} ${call.request.path()}")
            .setSpanKind(SpanKind.SERVER)
            .startSpan()

        try {
            withContext(span.asContextElement()) {
                proceed()
            }
            span.setAttribute("http.status_code", call.response.status()?.value)
        } catch (e: Exception) {
            span.recordException(e)
            span.setStatus(StatusCode.ERROR)
            throw e
        } finally {
            span.end()
        }
    }
}
```

### 4.2 Ktor 客户端集成

```kotlin
// Ktor Client: 出站请求插桩
val client = HttpClient {
    install(HttpRequestInterceptor) {
        intercept { request ->
            val span = tracer.spanBuilder("HTTP ${request.method.value}")
                .setSpanKind(SpanKind.CLIENT)
                .startSpan()

            // 注入传播头
            propagator.inject(Context.current(), request.headers) { carrier, key, value ->
                carrier.append(key, value)
            }

            try {
                val response = execute(request)
                span.setAttribute("http.response.status_code", response.status.value)
                response
            } catch (e: Exception) {
                span.recordException(e)
                span.setStatus(StatusCode.ERROR)
                throw e
            } finally {
                span.end()
            }
        }
    }
}
```

---

## 五、参与贡献

### 5.1 项目信息

| 项目 | 链接 |
|------|------|
| GitHub 仓库 | github.com/open-telemetry/opentelemetry-kotlin |
| Slack 频道 | #otel-kotlin (CNCF Slack) |
| SIG 会议 | 每两周一次，时间见社区日历 |

### 5.2 贡献方向

- [ ] Ktor Client/Server 自动 Instrumentation
- [ ] kotlinx.serialization 集成
- [ ] Android 特定优化（电池、内存）
- [ ] iOS 性能优化
- [ ] 文档和示例补充
- [ ] 与 OpenTelemetry Java SDK 的互操作测试

---

## 六、参考资源

- OpenTelemetry Kotlin Multiplatform SDK Repository
- Kotlin Multiplatform Documentation (kotlinlang.org)
- OpenTelemetry Mobile SIG Meeting Notes

---

> **总结**: Kotlin Multiplatform SDK 是 OpenTelemetry 在跨平台移动开发领域的重要布局。当前处于 Alpha 阶段，核心 Tracing 功能可用，但 Metrics 和平台特定优化仍在开发中。对于 Kotlin-first 的团队，值得在共享业务逻辑模块中试用，但生产环境的关键路径仍建议使用平台原生 SDK（Android/Java SDK 或 iOS/Swift SDK）。
