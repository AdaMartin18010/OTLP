# Span Event API 弃用与 Logs API 迁移指南

> **标准来源**: OpenTelemetry Community News (2026-03) + Specification Evolution
> **核心目标**: 解读 Span Event API 弃用的背景、影响，以及向 Logs API 迁移的实践路径

---

## 一、背景

### 1.1 弃用公告

2026 年 3 月，OpenTelemetry 社区正式宣布：**Span Event API 进入弃用流程**，推荐使用 **Logs API** 替代。

```text
弃用时间线:
├── 2026-03: 社区宣布弃用计划
├── 2026-H2: 规范标记 Span Event 为 Deprecated
├── 2027:    SDK 实现添加弃用警告
├── 2028+:   考虑从规范中移除（视社区反馈而定）
└── 注意: 这是一个长期过程，现有代码不会立即失效
```

### 1.2 为什么弃用 Span Event？

```text
Span Event 的设计问题:

1. 语义重叠
   ├── Span Event: 时间戳 + 名称 + 属性
   ├── LogRecord: 时间戳 + 严重级别 + 正文 + 属性
   └── 两者在概念上高度重叠

2. 功能限制
   ├── Span Event 无严重级别（Severity）概念
   ├── Span Event 的生命周期与 Span 绑定
   │   └── 如果 Span 未被采样，Event 也丢失
   └── 无法独立于 Span 进行过滤和路由

3. 后端处理复杂性
   ├── 后端需要同时支持两种事件模型
   ├── Span Event 的查询和存储优化困难
   └── 统一到 Logs 后，后端实现更简单

4. 与 Logs Bridge 的整合需求
   ├── 应用日志（如 log4j、winston）通过 Logs Bridge 进入 OTel
   ├── 这些日志天然带有严重级别
   └── 统一到 Logs 模型后，应用日志和追踪事件可以统一处理
```

---

## 二、Span Event vs Logs API 对比

### 2.1 概念对比

| 维度 | Span Event | Logs API (LogRecord) |
|------|-----------|---------------------|
| **生命周期** | 与父 Span 绑定 | 独立，可单独存在 |
| **严重级别** | 无 | 有（TRACE, DEBUG, INFO, WARN, ERROR, FATAL）|
| **采样影响** | 父 Span 未采样则丢失 | 独立的采样决策 |
| **时间戳** | 相对 Span 开始时间的偏移 | 绝对时间戳 |
| **属性** | 支持 | 支持 |
| **Trace 关联** | 自动关联到父 Span | 通过 trace_id/span_id 显式关联 |
| **后端路由** | 随 Span 一起路由 | 可独立路由到日志后端 |
| **过滤能力** | 弱 | 强（可按严重级别过滤）|

### 2.2 使用场景映射

| 原 Span Event 场景 | 推荐的 Logs API 替代方案 |
|-------------------|------------------------|
| 记录处理里程碑 | LogRecord with severity=INFO |
| 记录异常详情 | LogRecord with severity=ERROR + exception 属性 |
| 记录缓存命中/未命中 | LogRecord with severity=DEBUG + cache 属性 |
| 记录数据库查询详情 | LogRecord with severity=DEBUG + db 属性 |
| 记录业务事件 | LogRecord with severity=INFO + 业务属性 |

---

## 三、迁移指南

### 3.1 代码迁移示例

#### Java

```java
// 旧: Span Event
span.addEvent("cache_miss", Attributes.builder()
    .put("cache.key", userId)
    .put("cache.ttl", 300)
    .build());

// 新: Logs API
Logger logger = GlobalOpenTelemetry.getLogsBridge().get("my-app");

LogRecordBuilder log = logger.logRecordBuilder()
    .setSeverity(Severity.DEBUG)
    .setBody("Cache miss for user")
    .setAttribute(AttributeKey.stringKey("cache.key"), userId)
    .setAttribute(AttributeKey.longKey("cache.ttl"), 300);

// 自动关联到当前 Span 的 Trace Context
log.emit();
```

#### Python

```python
# 旧: Span Event
from opentelemetry.trace import get_current_span

get_current_span().add_event(
    "cache_miss",
    attributes={"cache.key": user_id, "cache.ttl": 300}
)

# 新: Logs API
from opentelemetry._logs import get_logger

logger = get_logger(__name__)

logger.emit(
    severity_number=SeverityNumber.DEBUG,
    body="Cache miss for user",
    attributes={"cache.key": user_id, "cache.ttl": 300}
)
# trace_id 和 span_id 自动从当前上下文提取
```

#### JavaScript/Node.js

```javascript
// 旧: Span Event
span.addEvent('cache_miss', {
  'cache.key': userId,
  'cache.ttl': 300,
});

// 新: Logs API
const logger = logs.getLogger('my-app');

logger.emit({
  severityNumber: SeverityNumber.DEBUG,
  body: 'Cache miss for user',
  attributes: {
    'cache.key': userId,
    'cache.ttl': 300,
  },
});
```

### 3.2 保留 Trace 关联

迁移到 Logs API 后，确保 LogRecord 仍与 Trace 关联：

```text
关联机制:
├── Logs API 自动从当前 Context 提取 trace_id 和 span_id
├── LogRecord 包含 trace_id、span_id、trace_flags 字段
├── 后端通过 trace_id 将 LogRecord 与 Span 关联
└── 查询时: "找到 trace_id=xxx 的所有 Span 和 LogRecord"
```

```java
// Java: 确保 LogRecord 与 Span 关联
Span span = tracer.spanBuilder("processOrder").startSpan();
try (Scope scope = span.makeCurrent()) {
    // 此处的 logger.emit() 会自动关联到 span
    logger.logRecordBuilder()
        .setSeverity(Severity.INFO)
        .setBody("Order processing started")
        .emit();

    // ... 业务逻辑 ...

    logger.logRecordBuilder()
        .setSeverity(Severity.INFO)
        .setBody("Order processing completed")
        .emit();
} finally {
    span.end();
}
```

### 3.3 后端配置调整

```yaml
# Collector 配置: 确保 Logs 和 Traces 路由到可关联的后端
receivers:
  otlp:
    protocols:
      grpc:
      http:

processors:
  batch:

exporters:
  jaeger:
    endpoint: jaeger:14250
    # 接收 Traces

  loki:
    endpoint: http://loki:3100/loki/api/v1/push
    # 接收 Logs
    # Loki 会自动索引 trace_id 标签

  otlphttp/logs:
    endpoint: http://log-backend:4318
    # 通用 OTLP Logs 接收端

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
    logs:
      receivers: [otlp]
      processors: [batch]
      exporters: [loki]
```

---

## 四、混合策略

### 4.1 渐进式迁移

```text
迁移策略:

阶段1: 双轨运行（立即开始）
├── 新代码使用 Logs API
├── 现有 Span Event 代码保持不变
└── 后端同时接收两种数据

阶段2: 存量迁移（6-12 个月）
├── 逐步将核心模块的 Span Event 替换为 Logs API
├── 每替换一个模块，验证追踪-日志关联正常
└── 更新团队编码规范，禁止新增 Span Event

阶段3: 清理（1-2 年后）
├── 移除所有 Span Event 代码
├── 后端停止处理 Span Event
└── 升级 SDK 到不再支持 Span Event 的版本
```

### 4.2 向后兼容

```text
向后兼容保证:
├── 2026-2028: SDK 继续支持 Span Event，但标记为 Deprecated
├── 2028+: SDK 可能移除 Span Event API
│   └── 但已有数据（已导出的 Span Event）不受影响
├── OTLP Protocol: 继续支持 Span Event 字段
│   └── 协议层面的支持比 API 层面更持久
└── 后端: 建议继续支持 Span Event 的接收和查询
```

---

## 五、检查清单

- [ ] 新代码使用 Logs API 而非 Span Event
- [ ] LogRecord 包含适当的 Severity 级别
- [ ] Logs API 调用处于正确的 Span Context 中，确保自动关联
- [ ] 后端（Collector + 存储）支持 Logs 信号的接收和查询
- [ ] Grafana/Loki 或等效工具配置了 trace_id 关联查询
- [ ] 团队编码规范已更新，明确推荐 Logs API
- [ ] 制定了存量 Span Event 代码的迁移计划

---

## 六、参考资源

- OpenTelemetry News: March 2026 Edition
- OpenTelemetry Logs API Specification
- OpenTelemetry Specification: Span Events (Deprecated)
- Loki: Trace to Logs 关联查询文档

---

> **总结**: Span Event 的弃用是 OpenTelemetry 向统一信号模型演进的重要一步。Logs API 提供了更丰富的语义（严重级别）、更灵活的采样和更统一的后端处理。建议新代码立即采用 Logs API，存量代码制定渐进式迁移计划。关键是确保 LogRecord 与 Trace 的关联不丢失，维持"从日志到追踪"和"从追踪到日志"的双向导航能力。
