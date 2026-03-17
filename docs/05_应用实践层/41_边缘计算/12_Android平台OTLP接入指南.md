---
title: Android平台OTLP接入指南
description: Android应用集成OpenTelemetry OTLP协议的完整实践指南，包含Java/Kotlin SDK、性能优化和最佳实践
version: OTLP v1.9.0 / OpenTelemetry Android v0.9.0
date: 2026-03-17
author: OTLP项目团队
category: 移动端可观测性
tags:
  - android
  - kotlin
  - java
  - mobile
  - otlp
status: published
---

# Android平台OTLP接入指南

> **版本**: OTLP v1.10.0 / OpenTelemetry Android v0.9.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约20分钟

---

## 1. 概述

### 1.1 Android可观测性特点

Android平台的可观测性面临独特挑战：

| 挑战 | 描述 | 解决方案 |
|------|------|----------|
| 碎片化 | 设备型号、OS版本众多 | 统一抽象层、兼容性测试 |
| 电量敏感 | 后台执行受限 | WorkManager批处理、省电策略 |
| 存储限制 | 应用存储空间受限 | 循环缓冲区、压缩存储 |
| ANR监控 | 主线程阻塞检测 | 自动ANR检测Span |
| 生命周期复杂 | Activity/Fragment生命周期 | 自动生命周期追踪 |

### 1.2 OpenTelemetry Android架构

```
┌──────────────────────────────────────────────────────────────┐
│                     Android Application                      │
├──────────────────────────────────────────────────────────────┤
│  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌──────────┐  │
│  │  Activity │  │  Fragment │  │  Service  │  │ ViewModel│  │
│  └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └────┬─────┘  │
│        │              │              │             │         │
│        └──────────────┴──────────────┴─────────────┘         │
│                         │                                    │
│              ┌──────────▼──────────┐                        │
│              │   Auto-Instrumentation                        │
│              │   (Lifecycle, Network, etc.)                 │
│              └──────────┬──────────┘                        │
│                         │                                    │
│       ┌─────────────────┼─────────────────┐                 │
│       ▼                 ▼                 ▼                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐              │
│  │  Traces  │    │  Metrics │    │   Logs   │              │
│  │  (Spans) │    │ (Meters) │    │(Loggers) │              │
│  └────┬─────┘    └────┬─────┘    └────┬─────┘              │
│       │               │               │                      │
│       └───────────────┼───────────────┘                      │
│                       │                                      │
│            ┌──────────▼──────────┐                          │
│            │  BatchSpanProcessor │                          │
│            │  (Buffer + Export)  │                          │
│            └──────────┬──────────┘                          │
│                       │                                      │
│       ┌───────────────┼───────────────┐                     │
│       ▼               ▼               ▼                     │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                 │
│  │  Disk   │    │  Cache  │    │ Network │                 │
│  │ Storage │    │ (Memory)│    │ Export  │                 │
│  └─────────┘    └─────────┘    └─────────┘                 │
└──────────────────────────────────────────────────────────────┘
```

---

## 2. 环境准备

### 2.1 Gradle依赖配置

```groovy
// build.gradle (Module: app)
dependencies {
    // OpenTelemetry核心
    implementation 'io.opentelemetry:opentelemetry-api:1.46.0'
    implementation 'io.opentelemetry:opentelemetry-sdk:1.46.0'

    // OTLP导出器
    implementation 'io.opentelemetry:opentelemetry-exporter-otlp:1.46.0'

    // Android特定SDK
    implementation 'io.opentelemetry.android:android-agent:0.9.0-alpha'

    // 自动插桩
    implementation 'io.opentelemetry.android:instrumentation-okhttp:0.9.0-alpha'
    implementation 'io.opentelemetry.android:instrumentation-lifecycle:0.9.0-alpha'

    // 可选：网络库
    implementation 'io.opentelemetry.instrumentation:opentelemetry-okhttp-3.0:2.12.0-alpha'
}
```

### 2.2 AndroidManifest配置

```xml
<manifest>
    <!-- 网络权限 -->
    <uses-permission android:name="android.permission.INTERNET" />
    <uses-permission android:name="android.permission.ACCESS_NETWORK_STATE" />

    <!-- 后台执行权限 (Android 12+) -->
    <uses-permission android:name="android.permission.RECEIVE_BOOT_COMPLETED" />

    <application
        android:name=".MyApplication"
        android:label="@string/app_name">

        <!-- WorkManager配置 -->
        <provider
            android:name="androidx.startup.InitializationProvider"
            android:authorities="${applicationId}.androidx-startup"
            android:exported="false"
            tools:node="merge">
            <meta-data
                android:name="androidx.work.WorkManagerInitializer"
                android:value="androidx.startup" />
        </provider>

    </application>
</manifest>
```

---

## 3. 基础集成

### 3.1 Application初始化

```kotlin
// MyApplication.kt
import android.app.Application
import io.opentelemetry.android.OpenTelemetryRum
import io.opentelemetry.android.config.OtelRumConfig
import io.opentelemetry.android.features.diskbuffering.DiskBufferingConfiguration
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor
import java.time.Duration

class MyApplication : Application() {

    lateinit var openTelemetryRum: OpenTelemetryRum
        private set

    override fun onCreate() {
        super.onCreate()

        initializeOpenTelemetry()
    }

    private fun initializeOpenTelemetry() {
        // 配置磁盘缓冲（离线支持）
        val diskBufferConfig = DiskBufferingConfiguration.builder()
            .setMaxCacheSize(10 * 1024 * 1024)  // 10MB
            .setMaxFileAge(Duration.ofHours(24))
            .build()

        // 主配置
        val config = OtelRumConfig()
            .setSlowRenderingDetectionPollInterval(Duration.ofSeconds(1))
            .setDiskBufferingConfiguration(diskBufferConfig)

        // 创建OTLP导出器
        val spanExporter = OtlpHttpSpanExporter.builder()
            .setEndpoint("https://your-collector.example.com:4318/v1/traces")
            .setTimeout(30, java.util.concurrent.TimeUnit.SECONDS)
            .build()

        // 构建OpenTelemetryRum
        openTelemetryRum = OpenTelemetryRum.builder(this, config)
            .addTracerProviderCustomizer { tracerProviderBuilder, _ ->
                tracerProviderBuilder.addSpanProcessor(
                    BatchSpanProcessor.builder(spanExporter)
                        .setScheduleDelay(5000)  // 5秒
                        .setMaxQueueSize(2048)
                        .setMaxExportBatchSize(512)
                        .build()
                )
            }
            .setResourceCustomizer { resourceBuilder ->
                resourceBuilder
                    .put("service.name", "MyAndroidApp")
                    .put("service.version", BuildConfig.VERSION_NAME)
                    .put("device.model", Build.MODEL)
                    .put("device.manufacturer", Build.MANUFACTURER)
                    .put("os.version", Build.VERSION.RELEASE)
                    .put("os.api_level", Build.VERSION.SDK_INT.toString())
            }
            .build()

        // 启用自动插桩
        enableAutoInstrumentation()
    }

    private fun enableAutoInstrumentation() {
        // Activity生命周期追踪
        openTelemetryRum.instrumentationScope.add(
            LifecycleInstrumentation.builder()
                .setScreenNameExtractor { activity ->
                    activity::class.java.simpleName
                }
                .build()
        )

        // 网络请求追踪
        openTelemetryRum.instrumentationScope.add(
            OkHttpInstrumentation.builder()
                .setCapturedRequestHeaders(listOf("X-Request-ID"))
                .setCapturedResponseHeaders(listOf("X-Trace-ID"))
                .build()
        )

        // ANR检测
        openTelemetryRum.instrumentationScope.add(AnrInstrumentation())

        // 慢渲染检测
        openTelemetryRum.instrumentationScope.add(SlowRenderingInstrumentation())
    }
}

// 全局访问
val Application.openTelemetry: OpenTelemetryRum
    get() = (this as MyApplication).openTelemetryRum
```

---

## 4. 手动追踪

### 4.1 基础Span创建

```kotlin
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.context.Context

class UserRepository(private val openTelemetry: OpenTelemetryRum) {

    private val tracer: Tracer = openTelemetry
        .openTelemetry
        .getTracer("UserRepository", "1.0.0")

    suspend fun fetchUser(userId: String): User {
        // 创建Span
        val span = tracer.spanBuilder("fetchUser")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("user.id", userId)
            .startSpan()

        try {
            // 使用use确保span结束
            span.makeCurrent().use { scope ->
                val user = apiService.getUser(userId)

                span.setAttribute("user.name", user.name)
                span.setStatus(StatusCode.OK)

                return user
            }
        } catch (e: Exception) {
            span.recordException(e)
            span.setStatus(StatusCode.ERROR, e.message ?: "Unknown error")
            throw e
        } finally {
            span.end()
        }
    }

    // 带子Span的复杂操作
    suspend fun processOrder(orderId: String) {
        val parentSpan = tracer.spanBuilder("processOrder")
            .setSpanKind(SpanKind.SERVER)
            .setAttribute("order.id", orderId)
            .startSpan()

        try {
            parentSpan.makeCurrent().use {
                // 验证订单
                tracer.spanBuilder("validateOrder")
                    .setParent(Context.current().with(parentSpan))
                    .startSpan()
                    .use { validateSpan ->
                        validateOrderInternal(orderId)
                    }

                // 处理支付
                tracer.spanBuilder("processPayment")
                    .setParent(Context.current().with(parentSpan))
                    .startSpan()
                    .use { paymentSpan ->
                        processPaymentInternal(orderId)
                    }

                // 更新库存
                tracer.spanBuilder("updateInventory")
                    .setParent(Context.current().with(parentSpan))
                    .startSpan()
                    .use { inventorySpan ->
                        updateInventoryInternal(orderId)
                    }

                parentSpan.setStatus(StatusCode.OK)
            }
        } catch (e: Exception) {
            parentSpan.recordException(e)
            parentSpan.setStatus(StatusCode.ERROR, e.message ?: "Failed")
            throw e
        } finally {
            parentSpan.end()
        }
    }
}
```

### 4.2 Coroutine上下文传播

```kotlin
import io.opentelemetry.context.Context
import io.opentelemetry.extension.kotlin.asContextElement
import kotlinx.coroutines.withContext

class CoroutineTelemetry {

    private val tracer: Tracer = // ...

    suspend fun tracedCoroutineOperation() {
        val span = tracer.spanBuilder("coroutineOperation").startSpan()

        // 将OpenTelemetry Context传入Coroutine
        withContext(Context.current().with(span).asContextElement()) {
            // 此处的Span会自动传播到子Coroutine
            asyncTask1()
            asyncTask2()
        }

        span.end()
    }

    suspend fun asyncTask1() {
        // 自动继承父Span的Context
        val span = tracer.spanBuilder("asyncTask1").startSpan()
        // ...
        span.end()
    }
}
```

---

## 5. 自动插桩

### 5.1 OkHttp集成

```kotlin
import io.opentelemetry.instrumentation.okhttp.v3_0.OkHttpTelemetry
import okhttp3.OkHttpClient

object HttpClientProvider {

    fun createClient(openTelemetry: OpenTelemetry): OkHttpClient {
        val telemetry = OkHttpTelemetry.builder(openTelemetry)
            .setCapturedRequestHeaders(setOf("X-Request-ID", "Authorization"))
            .setCapturedResponseHeaders(setOf("X-Trace-ID", "X-Request-Duration"))
            .build()

        return OkHttpClient.Builder()
            .addInterceptor(telemetry.newInterceptor())
            .connectTimeout(30, TimeUnit.SECONDS)
            .readTimeout(30, TimeUnit.SECONDS)
            .build()
    }
}
```

### 5.2 Room数据库追踪

```kotlin
import androidx.room.RoomDatabase
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.context.Context

@Database(entities = [User::class, Order::class], version = 1)
abstract class AppDatabase : RoomDatabase() {
    abstract fun userDao(): UserDao
    abstract fun orderDao(): OrderDao
}

// 带追踪的DAO包装
class TracedUserDao(
    private val dao: UserDao,
    private val tracer: Tracer
) {

    suspend fun getUser(userId: String): User? {
        val span = tracer.spanBuilder("db.query")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("db.system", "sqlite")
            .setAttribute("db.operation", "SELECT")
            .setAttribute("db.sql.table", "users")
            .startSpan()

        return try {
            span.makeCurrent().use {
                val user = dao.getUser(userId)
                span.setAttribute("db.response.returned_rows", if (user != null) 1 else 0)
                span.setStatus(StatusCode.OK)
                user
            }
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

---

## 6. 性能与优化

### 6.1 采样配置

```kotlin
import io.opentelemetry.sdk.trace.samplers.Sampler
import io.opentelemetry.sdk.trace.samplers.SamplingResult

// 头部采样
val sampler = Sampler.parentBased(
    Sampler.traceIdRatioBased(0.1)  // 10%采样
)

// 自定义采样规则
class CustomSampler : Sampler {
    override fun shouldSample(
        parentContext: Context,
        traceId: String,
        name: String,
        spanKind: SpanKind,
        attributes: Attributes,
        parentLinks: List<LinkData>
    ): SamplingResult {
        // 错误总是采样
        if (name.contains("error", ignoreCase = true)) {
            return SamplingResult.recordAndSample()
        }

        // 关键业务路径全量采样
        if (name in listOf("checkout", "payment", "login")) {
            return SamplingResult.recordAndSample()
        }

        // 其他按比率
        return Sampler.traceIdRatioBased(0.1).shouldSample(
            parentContext, traceId, name, spanKind, attributes, parentLinks
        )
    }

    override fun getDescription(): String = "CustomSampler"
}
```

### 6.2 WorkManager后台导出

```kotlin
import android.content.Context
import androidx.work.CoroutineWorker
import androidx.work.WorkerParameters
import androidx.work.Constraints
import androidx.work.NetworkType
import androidx.work.PeriodicWorkRequestBuilder
import androidx.work.WorkManager
import java.util.concurrent.TimeUnit

class TelemetryExportWorker(
    context: Context,
    params: WorkerParameters
) : CoroutineWorker(context, params) {

    override suspend fun doWork(): Result {
        val app = applicationContext as MyApplication

        return try {
            // 强制导出缓存的Span
            app.openTelemetryRum.flush()
            Result.success()
        } catch (e: Exception) {
            Result.retry()
        }
    }
}

// 调度导出任务
fun scheduleTelemetryExport(context: Context) {
    val constraints = Constraints.Builder()
        .setRequiredNetworkType(NetworkType.CONNECTED)
        .setRequiresBatteryNotLow(true)
        .build()

    val exportWorkRequest = PeriodicWorkRequestBuilder<TelemetryExportWorker>(
        15, TimeUnit.MINUTES  // 每15分钟
    )
        .setConstraints(constraints)
        .build()

    WorkManager.getInstance(context).enqueueUniquePeriodicWork(
        "telemetry_export",
        ExistingPeriodicWorkPolicy.KEEP,
        exportWorkRequest
    )
}
```

### 6.3 内存与存储优化

```kotlin
// 配置优化
val optimizedConfig = OtelRumConfig()
    // 限制内存队列
    .setMaxQueueSize(1024)

    // 磁盘缓冲限制
    .setDiskBufferingConfiguration(
        DiskBufferingConfiguration.builder()
            .setMaxCacheSize(5 * 1024 * 1024)  // 5MB
            .setMaxFileAge(Duration.ofHours(12))
            .build()
    )

    // 批处理优化
    .setBatchTimeout(Duration.ofSeconds(30))

    // 压缩
    .setCompressionEnabled(true)
```

---

## 7. 自定义指标

```kotlin
import io.opentelemetry.api.metrics.LongCounter
import io.opentelemetry.api.metrics.LongHistogram
import io.opentelemetry.api.metrics.Meter

class AppMetrics(openTelemetry: OpenTelemetryRum) {

    private val meter: Meter = openTelemetry
        .openTelemetry
        .meterProvider
        .get("AppMetrics")

    // 计数器
    private val screenViewCounter: LongCounter = meter
        .counterBuilder("app.screen_views")
        .setDescription("Number of screen views")
        .build()

    // 直方图
    private val clickLatency: LongHistogram = meter
        .histogramBuilder("app.click_latency")
        .setDescription("Button click response time")
        .setUnit("ms")
        .ofLongs()
        .build()

    // 可观察Gauge
    private val memoryUsage = meter
        .gaugeBuilder("app.memory_usage")
        .setDescription("Current memory usage")
        .setUnit("By")
        .ofLongs()
        .buildWithCallback { result ->
            val runtime = Runtime.getRuntime()
            val usedMemory = runtime.totalMemory() - runtime.freeMemory()
            result.record(usedMemory, Attributes.empty())
        }

    fun recordScreenView(screenName: String) {
        screenViewCounter.add(
            1,
            Attributes.builder()
                .put("screen.name", screenName)
                .build()
        )
    }

    fun recordClickLatency(durationMs: Long, buttonName: String) {
        clickLatency.record(
            durationMs,
            Attributes.builder()
                .put("button.name", buttonName)
                .build()
        )
    }
}
```

---

## 8. 最佳实践

### 8.1 检查清单

| 检查项 | 建议 | 说明 |
|--------|------|------|
| 采样率 | 5-15% | 根据应用规模调整 |
| 批处理延迟 | 5-30秒 | 平衡实时性和电量 |
| 磁盘缓冲 | 5-10MB | 防止存储溢出 |
| 网络超时 | 10-30秒 | 避免ANR |
| 后台导出间隔 | 15-30分钟 | WorkManager限制 |

### 8.2 隐私保护

```kotlin
// 敏感数据过滤
class PrivacyAttributeFilter : SpanProcessor {

    private val sensitiveKeys = setOf(
        "password", "token", "authorization",
        "credit_card", "ssn", "phone", "email"
    )

    override fun onStart(parentContext: Context, span: ReadWriteSpan) {
        // 在Span开始时过滤属性
        span.setAttribute("user.email", "[REDACTED]")
    }

    override fun onEnd(span: ReadableSpan) {}
    override fun shutdown() {}
    override fun forceFlush(): Boolean = true
}
```

### 8.3 错误处理

```kotlin
// 自定义错误处理器
class TelemetryErrorHandler : Consumer<Throwable> {
    override fun accept(t: Throwable) {
        // 记录到本地日志，不崩溃
        Log.e("Telemetry", "Telemetry error", t)

        // 上报到崩溃分析（排除遥测错误本身）
        if (t !is TelemetryException) {
            FirebaseCrashlytics.getInstance().recordException(t)
        }
    }
}

// 配置中使用
OpenTelemetryRum.builder(context, config)
    .setErrorHandler(TelemetryErrorHandler())
    .build()
```

---

## 9. 调试工具

```kotlin
// Debug模式配置
if (BuildConfig.DEBUG) {
    // 使用LoggingSpanExporter查看Span
    val loggingExporter = LoggingSpanExporter.create()

    OpenTelemetryRum.builder(context, config)
        .addTracerProviderCustomizer { builder, _ ->
            builder.addSpanProcessor(
                SimpleSpanProcessor.create(loggingExporter)
            )
        }
        .build()
}
```

---

## 总结

Android平台OTLP集成核心要点：

1. **使用OpenTelemetry Android SDK**: 专为移动端优化的SDK
2. **启用磁盘缓冲**: 确保离线数据不丢失
3. **WorkManager导出**: 符合Android后台执行规范
4. **自动插桩优先**: 减少手动追踪工作量
5. **采样控制**: 平衡数据完整性和性能开销

---

**参考资源**:

- [OpenTelemetry Android](https://github.com/open-telemetry/opentelemetry-android)
- [Android WorkManager](https://developer.android.com/topic/libraries/architecture/workmanager)
- [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17

