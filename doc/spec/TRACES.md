# OpenTelemetry Traces 规范

## 概述

分布式追踪（Distributed Tracing）是OpenTelemetry的核心功能之一，用于跟踪请求在分布式系统中的完整执行路径。

## 核心概念

### Trace

- **定义**: 表示一个完整的请求处理过程
- **标识**: 通过TraceId全局唯一标识
- **生命周期**: 从请求开始到响应结束

### Span

- **定义**: 表示一个操作单元
- **标识**: 通过SpanId唯一标识
- **关系**: 通过ParentSpanId建立父子关系

### SpanKind

```protobuf
enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}
```

## 数据模型

### Span结构

```protobuf
message Span {
  bytes trace_id = 1;                    // 16字节TraceId
  bytes span_id = 2;                     // 8字节SpanId
  string trace_state = 3;                // W3C TraceState
  bytes parent_span_id = 4;              // 父SpanId
  string name = 5;                       // Span名称
  SpanKind kind = 6;                     // Span类型
  fixed64 start_time_unix_nano = 7;      // 开始时间
  fixed64 end_time_unix_nano = 8;        // 结束时间
  repeated KeyValue attributes = 9;      // 属性
  uint32 dropped_attributes_count = 10;  // 丢弃的属性数量
  repeated StatusEvent events = 11;      // 事件
  uint32 dropped_events_count = 12;      // 丢弃的事件数量
  repeated SpanLink links = 13;          // 链接
  uint32 dropped_links_count = 14;       // 丢弃的链接数量
  Status status = 15;                    // 状态
}
```

### 时间戳

- **精度**: 纳秒级精度
- **格式**: Unix时间戳（纳秒）
- **时区**: UTC时间

### 属性

```protobuf
message KeyValue {
  string key = 1;
  AnyValue value = 2;
}

message AnyValue {
  oneof value {
    string string_value = 1;
    bool bool_value = 2;
    int64 int_value = 3;
    double double_value = 4;
    ArrayValue array_value = 5;
    KeyValueList kvlist_value = 6;
    bytes bytes_value = 7;
  }
}
```

## 语义约定

### HTTP语义约定

```go
// 必需属性
attribute.String("http.method", "POST")
attribute.String("http.url", "https://api.example.com/users")
attribute.Int("http.status_code", 201)

// 可选属性
attribute.String("http.target", "/users")
attribute.String("http.host", "api.example.com")
attribute.String("http.scheme", "https")
attribute.String("http.user_agent", "Mozilla/5.0...")
attribute.Int("http.request_content_length", 1024)
attribute.Int("http.response_content_length", 512)
attribute.String("http.route", "/users/{id}")
```

### 数据库语义约定

```go
// 必需属性
attribute.String("db.system", "postgresql")

// 可选属性
attribute.String("db.connection_string", "postgresql://...")
attribute.String("db.statement", "SELECT * FROM users WHERE id = ?")
attribute.String("db.operation", "SELECT")
attribute.String("db.sql.table", "users")
```

### RPC语义约定

```go
// 必需属性
attribute.String("rpc.system", "grpc")

// 可选属性
attribute.String("rpc.service", "user.UserService")
attribute.String("rpc.method", "GetUser")
attribute.Int("rpc.grpc.status_code", 0)
```

## 采样策略

### 采样决策

```go
type SamplingDecision int

const (
    SamplingDecisionUnspecified SamplingDecision = iota
    SamplingDecisionDrop
    SamplingDecisionRecord
    SamplingDecisionRecordAndSample
)
```

### 采样器类型

#### AlwaysOn

```go
sampler := trace.AlwaysOn()
```

#### AlwaysOff

```go
sampler := trace.AlwaysOff()
```

#### TraceIdRatioBased

```go
sampler := trace.TraceIDRatioBased(0.01) // 1%采样率
```

#### ParentBased

```go
sampler := trace.ParentBased(
    trace.TraceIDRatioBased(0.01),
    trace.WithRemoteParentSampled(trace.AlwaysOn()),
    trace.WithRemoteParentNotSampled(trace.AlwaysOff()),
    trace.WithLocalParentSampled(trace.AlwaysOn()),
    trace.WithLocalParentNotSampled(trace.AlwaysOff()),
)
```

## 上下文传播

### W3C TraceContext

```go
// 设置传播器
otel.SetTextMapPropagator(propagation.TraceContext{})

// 从HTTP头提取上下文
ctx := propagation.TraceContext{}.Extract(
    ctx,
    propagation.HeaderCarrier(r.Header),
)

// 注入上下文到HTTP头
propagation.TraceContext{}.Inject(
    ctx,
    propagation.HeaderCarrier(w.Header()),
)
```

### Baggage传播

```go
// 设置Baggage传播器
otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
    propagation.TraceContext{},
    propagation.Baggage{},
))

// 设置Baggage
baggage.Set(ctx, "user.id", "12345")
baggage.Set(ctx, "tenant.id", "acme")

// 获取Baggage
userID := baggage.Value(ctx, "user.id")
tenantID := baggage.Value(ctx, "tenant.id")
```

## 事件和链接

### 事件

```go
// 添加事件
span.AddEvent("user.login", trace.WithAttributes(
    attribute.String("user.id", "12345"),
    attribute.String("login.method", "oauth"),
))

// 添加带时间戳的事件
span.AddEvent("cache.miss", trace.WithTimestamp(time.Now()))
```

### 链接

```go
// 创建链接
link := trace.Link{
    SpanContext: spanContext,
    Attributes: []attribute.KeyValue{
        attribute.String("link.type", "follows_from"),
    },
}

// 创建带链接的Span
ctx, span := tracer.Start(ctx, "operation", trace.WithLinks(link))
```

## 状态管理

### Span状态

```go
// 设置成功状态
span.SetStatus(codes.Ok, "success")

// 设置错误状态
span.SetStatus(codes.Error, "database connection failed")

// 记录错误
span.RecordError(err)
```

### 状态码

```go
const (
    StatusCodeUnset = 0
    StatusCodeOk    = 1
    StatusCodeError = 2
)
```

## 性能优化

### 异步处理

```go
// 使用批处理导出器
exporter, err := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("localhost:4317"),
    otlptracegrpc.WithInsecure(),
)

tracerProvider := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter, sdktrace.WithBatchTimeout(time.Second)),
    sdktrace.WithResource(resource),
)
```

### 内存限制

```go
tracerProvider := sdktrace.NewTracerProvider(
    sdktrace.WithSpanLimits(sdktrace.SpanLimits{
        AttributeCountLimit:         128,
        EventCountLimit:             128,
        LinkCountLimit:              128,
        AttributeValueLengthLimit:   1024,
        EventAttributeCountLimit:    128,
        LinkAttributeCountLimit:     128,
    }),
)
```

## 最佳实践

### 1. Span命名

```go
// 好的命名
span := tracer.Start(ctx, "http.request")
span := tracer.Start(ctx, "db.query")
span := tracer.Start(ctx, "cache.get")

// 避免的命名
span := tracer.Start(ctx, "operation")
span := tracer.Start(ctx, "function")
span := tracer.Start(ctx, "method")
```

### 2. 属性设计

```go
// 好的属性设计
span.SetAttributes(
    attribute.String("http.method", "POST"),
    attribute.String("http.url", "https://api.example.com/users"),
    attribute.Int("http.status_code", 201),
    attribute.String("user.id", "12345"),
)

// 避免的属性设计
span.SetAttributes(
    attribute.String("method", "POST"),           // 缺少命名空间
    attribute.String("HTTP_METHOD", "POST"),      // 大写命名
    attribute.String("url", "https://..."),       // 缺少命名空间
)
```

### 3. 错误处理

```go
func handleRequest(ctx context.Context, req *Request) error {
    ctx, span := tracer.Start(ctx, "handleRequest")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("request.id", req.ID),
        attribute.String("request.type", req.Type),
    )
    
    err := processRequest(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "success")
    return nil
}
```

## 故障排除

### 常见问题

1. **Span丢失**: 检查采样配置
2. **上下文丢失**: 检查传播器配置
3. **性能问题**: 检查批处理配置
4. **内存泄漏**: 检查Span限制

### 调试工具

```go
// 启用调试日志
import "go.opentelemetry.io/otel/sdk/trace"

tracerProvider := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(trace.AlwaysOn()),
    sdktrace.WithSpanProcessor(trace.NewSimpleSpanProcessor(exporter)),
)
```

## 总结

OpenTelemetry Traces提供了强大的分布式追踪能力，通过合理的配置和使用，可以实现：

- **完整的请求跟踪**: 从入口到出口的完整路径
- **性能分析**: 识别性能瓶颈和优化点
- **错误诊断**: 快速定位和解决问题
- **系统理解**: 理解系统架构和依赖关系

遵循语义约定、合理配置采样策略、正确使用上下文传播，是成功实施分布式追踪的关键。
