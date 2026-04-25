# 非 OTLP 日志格式中的 Trace Context

> **标准来源**: OpenTelemetry Specification v1.56.0 — Compatibility / Trace Context in non-OTLP Log Formats
> **核心目标**: 在结构化日志、文件日志、syslog 等非 OTLP 日志格式中嵌入分布式追踪上下文，实现日志与追踪的关联

---

## 一、背景

### 1.1 问题场景

许多系统使用非 OTLP 格式记录日志：

```text
常见非 OTLP 日志场景:
├── 应用文件日志（JSON Lines、Logfmt）
├── 系统日志（syslog、journald）
├── 云厂商日志服务（AWS CloudWatch Logs、Azure Monitor Logs）
├── 遗留系统的自定义日志格式
├── 第三方软件的日志输出
└── 基础设施组件日志（Nginx、Kubernetes、数据库）

核心需求:
├── 当排查问题时，能从日志行跳转到对应的分布式追踪
├── 能从追踪查看关联的所有日志事件
└── 统一查询："找到 trace-id=xxx 的所有日志和 Span"
```

### 1.2 为什么需要标准化？

在没有标准化之前，各系统以不同方式嵌入追踪上下文：

```text
系统A: {"message": "User login", "trace_id": "abc123", "span_id": "def456"}
系统B: [2026-04-26T10:00:00Z] trace=abc123 span=def456 User login
系统C: {"msg": "User login", "traceId": "abc123", "spanId": "def456"}
系统D: {"msg": "User login", "dd.trace_id": "abc123"}  ← Datadog 格式

问题:
├── 字段命名不一致（trace_id / traceId / trace / dd.trace_id）
├── 十六进制编码 vs 十进制编码（Datadog 使用十进制 trace_id）
├── 大小写不一致
└── 后端查询时无法统一关联
```

OpenTelemetry 规范为此提供了标准化的嵌入建议。

---

## 二、标准化嵌入格式

### 2.1 推荐的字段命名

在非 OTLP 日志格式中嵌入 Trace Context 时，**应该**使用以下字段名：

| 字段名 | 类型 | 说明 | 示例 |
|--------|------|------|------|
| `trace_id` | string (hex) | 追踪 ID，32 位十六进制小写 | `0af7651916cd43dd8448eb211c80319c` |
| `span_id` | string (hex) | 跨度 ID，16 位十六进制小写 | `b7ad6b7169203331` |
| `trace_flags` | string (hex) | 追踪标志，2 位十六进制 | `01` |

### 2.2 完整的 Trace Context 字符串

可选地，可以将完整的 W3C traceparent 字符串作为一个字段：

| 字段名 | 说明 | 示例 |
|--------|------|------|
| `traceparent` | 完整的 W3C traceparent | `00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01` |

### 2.3 十六进制格式规范

```text
格式要求:
├── trace_id: 32 个十六进制字符，小写
│   └── 示例: 0af7651916cd43dd8448eb211c80319c
│   └── 无效: 0AF7651916CD43DD8448EB211C80319C（大写不推荐）
│   └── 无效: 0af7651916cd43dd8448eb211c80319（31位，长度不足）
│
├── span_id: 16 个十六进制字符，小写
│   └── 示例: b7ad6b7169203331
│   └── 注意: 某些系统（如 Jaeger）使用 16 字符十六进制
│       而 Zipkin 使用 16 字符十六进制（相同格式）
│
└── trace_flags: 2 个十六进制字符
    └── 示例: 01（表示已采样）
    └── 示例: 00（表示未采样）
```

### 2.4 与 Datadog 格式的兼容性

Datadog 使用**十进制**字符串表示 trace_id，这在混合环境中需要转换：

```text
Datadog 格式:
├── dd.trace_id: "1234567890123456789"（十进制）
├── dd.span_id: "9876543210987654321"（十进制）
└── 注意: 这与 W3C / OpenTelemetry 的十六进制格式不同

转换:
├── W3C trace_id (hex) → Datadog trace_id (dec):
│   dec = hex_to_dec(trace_id[16:32])  ← 取低 64 位
│   示例: trace_id 0af7651916cd43dd8448eb211c80319c
│         低 64 位: 8448eb211c80319c
│         十进制: 9523945026261237148
│
└── Datadog trace_id (dec) → W3C trace_id (hex):
    需要额外信息（高 64 位），通常无法反向转换
```

**建议**: 在统一日志平台中，同时保留十六进制和十进制两种格式，或建立索引时自动转换。

---

## 三、各日志格式的嵌入示例

### 3.1 JSON 格式

```json
{
  "timestamp": "2026-04-26T10:00:00.123Z",
  "level": "INFO",
  "logger": "com.example.UserService",
  "message": "User login successful",
  "trace_id": "0af7651916cd43dd8448eb211c80319c",
  "span_id": "b7ad6b7169203331",
  "trace_flags": "01",
  "service.name": "auth-service",
  "user.id": "12345"
}
```

### 3.2 Logfmt 格式

```
timestamp=2026-04-26T10:00:00.123Z level=INFO logger=com.example.UserService msg="User login successful" trace_id=0af7651916cd43dd8448eb211c80319c span_id=b7ad6b7169203331 trace_flags=01 service=auth-service
```

### 3.3 结构化文件日志（CSV/TSV）

```csv
timestamp,level,logger,message,trace_id,span_id
2026-04-26T10:00:00.123Z,INFO,com.example.UserService,"User login successful",0af7651916cd43dd8448eb211c80319c,b7ad6b7169203331
```

### 3.4 Syslog 格式

```
<134>1 2026-04-26T10:00:00.123Z web-server app - - [otel@32473 trace_id="0af7651916cd43dd8448eb211c80319c" span_id="b7ad6b7169203331"] User login successful
```

使用 syslog 的 **structured-data（RFC 5424）** 字段携带 Trace Context，以 `otel@32473` 作为 enterprise ID。

### 3.5 Nginx 访问日志

```nginx
# nginx.conf
log_format json_combined escape=json '{'
  '"timestamp":"$time_iso8601",'
  '"request_method":"$request_method",'
  '"request_uri":"$request_uri",'
  '"status":$status,'
  '"trace_id":"$opentelemetry_trace_id",'
  '"span_id":"$opentelemetry_span_id"'
'}';

access_log /var/log/nginx/access.log json_combined;
```

**注意**: Nginx 原生不支持 OpenTelemetry 变量，需要通过 Nginx OTel 模块或 Lua 脚本注入。

---

## 四、实现模式

### 4.1 应用日志自动注入

大多数语言的日志框架支持通过 MDC（Mapped Diagnostic Context）或类似机制自动注入 Trace Context：

#### Java (Logback/SLF4J)

```java
// 配置 logback.xml 自动包含 trace_id 和 span_id
<appender name="JSON" class="ch.qos.logback.core.ConsoleAppender">
    <encoder class="net.logstash.logback.encoder.LogstashEncoder">
        <includeMdcKeyName>trace_id</includeMdcKeyName>
        <includeMdcKeyName>span_id</includeMdcKeyName>
    </encoder>
</appender>

// 在 OpenTelemetry Context 变化时自动更新 MDC
public class OtelMdcInjector implements SpanProcessor {
    @Override
    public void onStart(Context parentContext, ReadWriteSpan span) {
        SpanContext spanContext = span.getSpanContext();
        if (spanContext.isValid()) {
            MDC.put("trace_id", spanContext.getTraceId());
            MDC.put("span_id", spanContext.getSpanId());
            MDC.put("trace_flags", String.format("%02x", spanContext.getTraceFlags()));
        }
    }

    @Override
    public void onEnd(ReadableSpan span) {
        MDC.remove("trace_id");
        MDC.remove("span_id");
        MDC.remove("trace_flags");
    }
}
```

#### Python (structlog/logging)

```python
import structlog
from opentelemetry import trace

def add_trace_info(logger, method_name, event_dict):
    """structlog 处理器：自动注入 Trace Context"""
    span = trace.get_current_span()
    span_context = span.get_span_context()

    if span_context.is_valid:
        event_dict["trace_id"] = format(span_context.trace_id, '032x')
        event_dict["span_id"] = format(span_context.span_id, '016x')
        event_dict["trace_flags"] = format(span_context.trace_flags, '02x')

    return event_dict

structlog.configure(
    processors=[
        add_trace_info,
        structlog.processors.JSONRenderer()
    ]
)
```

#### Node.js (Pino/Winston)

```javascript
const pino = require('pino');
const { trace } = require('@opentelemetry/api');

const logger = pino({
  mixin() {
    const span = trace.getActiveSpan();
    if (span) {
      const ctx = span.spanContext();
      return {
        trace_id: ctx.traceId,
        span_id: ctx.spanId,
        trace_flags: ctx.traceFlags.toString(16).padStart(2, '0'),
      };
    }
    return {};
  }
});
```

### 4.2 日志后端关联查询

在 Elasticsearch、Loki、CloudWatch Logs Insights 等后端中，使用 Trace ID 统一查询：

```text
Elasticsearch Query:
{
  "query": {
    "term": {
      "trace_id": "0af7651916cd43dd8448eb211c80319c"
    }
  }
}

Loki LogQL:
{app="auth-service"} |= "trace_id=0af7651916cd43dd8448eb211c80319c"

CloudWatch Logs Insights:
fields @timestamp, @message
| filter trace_id = '0af7651916cd43dd8448eb211c80319c'
| sort @timestamp desc
```

---

## 五、与 OTLP Logs 的关系

| 特性 | OTLP Logs | 非 OTLP 日志（本规范） |
|------|-----------|----------------------|
| **传输协议** | OTLP/gRPC 或 OTLP/HTTP | 文件、syslog、HTTP JSON 等 |
| **Trace Context 位置** | LogRecord 的 `trace_id` / `span_id` 字段 | 日志体中的自定义字段 |
| **结构化程度** | 强 Schema（Protobuf） | 依赖具体格式 |
| **采集方式** | OTLP Exporter 直接发送 | 需通过 Filelog Receiver、Fluentd 等采集 |
| **适用场景** | 新系统、原生 OpenTelemetry 应用 | 遗留系统、基础设施组件、第三方软件 |

**建议策略**:

- 新开发的应用：优先使用 OTLP Logs API 直接导出
- 遗留系统或基础设施：在非 OTLP 日志中嵌入 Trace Context，通过 Collector 采集转换

---

## 六、检查清单

在实现非 OTLP 日志的 Trace Context 嵌入时，确认：

- [ ] 使用小写十六进制格式（32 字符 trace_id，16 字符 span_id）
- [ ] 字段名统一为 `trace_id`、`span_id`、`trace_flags`
- [ ] 在日志框架中通过 MDC/Context 自动注入，避免业务代码手动设置
- [ ] 异步线程/协程切换时正确传递 Trace Context
- [ ] 日志后端支持按 `trace_id` 字段索引和查询
- [ ] 与 OTLP Trace 数据能通过相同 trace_id 关联
- [ ] 在混合环境（Datadog、Jaeger、Zipkin）中考虑 ID 格式转换

---

## 七、参考资源

- OpenTelemetry Specification: Trace Context in non-OTLP Log Formats
- OpenTelemetry Logs API / Logs SDK
- W3C Trace Context Specification
- RFC 5424: The Syslog Protocol

---

> **总结**: 在非 OTLP 日志格式中标准化嵌入 Trace Context，是打通"日志"与"追踪"两大可观测性支柱的关键。通过统一的 `trace_id` / `span_id` 字段命名和十六进制格式，可以实现从任意日志行一键跳转到对应的分布式追踪，大幅提升故障排查效率。
