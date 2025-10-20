# 🛒 E-commerce Order Tracking Example (Go)

> **目的**: 展示如何使用OpenTelemetry追踪电商订单处理流程  
> **语言**: Go 1.21+  
> **协议**: OTLP (OpenTelemetry Protocol)  
> **配套文档**: [数据模型与语义转换完整指南](../../📊_数据模型与语义转换完整指南_2025_10_20.md)

---

## 📋 功能特性

### 1. 自定义业务属性（vendor前缀）

本示例展示如何正确使用vendor前缀定义自定义属性：

```go
// ✅ 正确: 使用 myshop. 前缀
attribute.String("myshop.order.id", order.ID)
attribute.String("myshop.order.status", string(order.Status))
attribute.Float64("myshop.order.total_amount", order.TotalAmount)
attribute.Int("myshop.order.item_count", order.ItemCount)
attribute.String("myshop.user.tier", string(order.UserTier))

// ✅ 条件属性: 仅当有促销时添加
if order.PromotionCode != "" {
    span.SetAttributes(
        attribute.String("myshop.promotion.code", order.PromotionCode),
        attribute.Float64("myshop.promotion.discount_percent", 20.0),
    )
}
```

### 2. 标准语义约定

同时使用标准语义约定（Semantic Conventions v1.29.0）：

```go
// HTTP属性
semconv.HTTPMethod("POST")
semconv.HTTPRoute("/api/orders")
semconv.HTTPStatusCode(201)

// Database属性
semconv.DBSystem("postgresql")
semconv.DBName("myshop")
semconv.DBOperation("UPDATE")
semconv.DBSQLTable("inventory")

// Messaging属性
semconv.MessagingSystem("kafka")
semconv.MessagingDestinationName("order-notifications")
semconv.MessagingOperation("publish")
```

### 3. 完整的Span层次结构

```text
process_order (root span)
├─ validate_order
├─ process_payment
│   └─ call_payment_gateway (client span)
├─ update_inventory
│   └─ db.update (client span)
└─ send_notification
    └─ publish_to_kafka (producer span)
```

### 4. 事件和错误处理

```go
// 记录事件
span.AddEvent("order_created", trace.WithAttributes(
    attribute.String("myshop.order.id", order.ID),
    attribute.Int("myshop.order.item_count", order.ItemCount),
))

// 错误处理
if err := validateOrder(ctx, order); err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, "Order validation failed")
    return err
}
```

---

## 🚀 快速开始

### 前置条件

1. **Go 1.21+**

   ```bash
   go version
   ```

2. **OTLP Collector** (运行在localhost:4317)

   使用Docker快速启动:

   ```bash
   docker run -d --name jaeger \
     -e COLLECTOR_OTLP_ENABLED=true \
     -p 16686:16686 \
     -p 4317:4317 \
     -p 4318:4318 \
     jaegertracing/all-in-one:latest
   ```

### 运行步骤

1. **安装依赖**

   ```bash
   cd examples/e-commerce-order-tracking
   go mod download
   ```

2. **运行示例**

   ```bash
   go run main.go
   ```

   输出示例:

   ```text
   🛒 E-commerce Order Tracking Example Started
   📊 Sending order processing traces to OTLP Collector...
   🔗 Connect to http://localhost:16686 to view traces (Jaeger UI)

   Processing Order 1: ID=ORDER-2024-000001, Amount=$125.50, User=gold
   Processing Order 2: ID=ORDER-2024-000002, Amount=$45.99, User=silver
   Processing Order 3: ID=ORDER-2024-000003, Amount=$299.00, User=platinum
   Processing Order 4: ID=ORDER-2024-000004, Amount=$15.50, User=free
   Processing Order 5: ID=ORDER-2024-000005, Amount=$89.99, User=gold

   ✅ All orders processed successfully!
   📊 Check Jaeger UI to see the traces
   ```

3. **查看追踪**

   打开浏览器访问 [http://localhost:16686](http://localhost:16686)

   在Jaeger UI中:
   - Service: 选择 `order-service`
   - Operation: 选择 `process_order`
   - 点击 "Find Traces"

---

## 📊 追踪数据展示

### Jaeger UI中的Trace视图

```text
process_order [201ms]
  service.name: order-service
  service.version: 1.2.3
  deployment.environment: production
  http.method: POST
  http.route: /api/orders
  http.status_code: 201
  myshop.order.id: ORDER-2024-000001
  myshop.order.status: paid
  myshop.order.total_amount: 125.50
  myshop.user.tier: gold
  myshop.promotion.code: SUMMER2024
  
  ├─ validate_order [50ms]
  │    myshop.order.id: ORDER-2024-000001
  │    validation.result: success
  │
  ├─ process_payment [250ms]
  │    myshop.payment.amount: 125.50
  │    myshop.payment.method: credit_card
  │    │
  │    └─ call_payment_gateway [150ms]
  │         http.method: POST
  │         http.host: payment-gateway.example.com
  │         http.status_code: 200
  │
  ├─ update_inventory [80ms]
  │    myshop.order.item_count: 3
  │    │
  │    └─ db.update [80ms]
  │         db.system: postgresql
  │         db.name: myshop
  │         db.operation: UPDATE
  │         db.sql.table: inventory
  │
  └─ send_notification [30ms]
       myshop.notification.type: order_confirmation
       │
       └─ publish_to_kafka [30ms]
            messaging.system: kafka
            messaging.destination.name: order-notifications
            kafka.partition: 3
```

---

## 🎯 数据模型设计

### 自定义语义约定定义

参考[数据模型指南第2部分](../../📊_数据模型与语义转换完整指南_2025_10_20.md#第二部分自定义数据模型设计)

```yaml
namespace: myshop.order

attributes:
  # 订单基本信息
  myshop.order.id:
    type: string
    requirement: required
    description: 订单唯一标识
    example: "ORDER-2024-001234"
    
  myshop.order.status:
    type: enum
    requirement: required
    values: ["pending", "paid", "shipped", "delivered", "cancelled"]
    description: 订单状态
    
  myshop.order.total_amount:
    type: double
    requirement: required
    description: 订单总金额(USD)
    example: 99.99
    
  myshop.order.item_count:
    type: int
    requirement: recommended
    description: 订单商品数量
    example: 3
    
  # 用户信息
  myshop.user.tier:
    type: enum
    requirement: recommended
    values: ["free", "silver", "gold", "platinum"]
    description: 用户等级
    
  # 促销信息
  myshop.promotion.code:
    type: string
    requirement: optional
    description: 促销码
    example: "SUMMER2024"
    
  myshop.promotion.discount_percent:
    type: double
    requirement: conditional
    description: 折扣百分比
    example: 20.0
```

---

## 🔍 关键代码说明

### 1. OpenTelemetry初始化

```go
func initTracer(ctx context.Context) (func(context.Context) error, error) {
    // 1. 创建OTLP exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    
    // 2. 创建Resource（服务级别属性）
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("order-service"),
            semconv.ServiceVersion("1.2.3"),
            semconv.DeploymentEnvironment("production"),
        ),
    )
    
    // 3. 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )
    
    // 4. 设置为全局Provider
    otel.SetTracerProvider(tp)
    
    return tp.Shutdown, nil
}
```

### 2. Span创建和属性设置

```go
func processOrder(ctx context.Context, order *Order) error {
    // 创建root span
    ctx, span := tracer.Start(ctx, "process_order",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            // 标准属性
            semconv.HTTPMethod("POST"),
            semconv.HTTPRoute("/api/orders"),
            
            // 自定义属性 (vendor前缀)
            attribute.String("myshop.order.id", order.ID),
            attribute.Float64("myshop.order.total_amount", order.TotalAmount),
        ),
    )
    defer span.End()
    
    // 后续处理...
}
```

### 3. 条件属性设置

```go
// 仅当有促销码时添加促销相关属性
if order.PromotionCode != "" {
    span.SetAttributes(
        attribute.String("myshop.promotion.code", order.PromotionCode),
        attribute.Float64("myshop.promotion.discount_percent", 20.0),
    )
}
```

### 4. 事件记录

```go
// 记录关键事件
span.AddEvent("order_created", trace.WithAttributes(
    attribute.String("myshop.order.id", order.ID),
    attribute.Int("myshop.order.item_count", order.ItemCount),
))

span.AddEvent("order_completed", trace.WithAttributes(
    attribute.String("myshop.order.id", order.ID),
    attribute.String("myshop.order.status", string(order.Status)),
))
```

### 5. 错误处理

```go
if err := validateOrder(ctx, order); err != nil {
    // 记录错误
    span.RecordError(err)
    
    // 设置状态为Error
    span.SetStatus(codes.Error, "Order validation failed")
    
    return fmt.Errorf("validation failed: %w", err)
}

// 成功时设置状态为Ok
span.SetStatus(codes.Ok, "Order processed successfully")
```

---

## 📈 实际应用场景

### 场景1: 按用户等级分析订单处理延迟

在Jaeger UI中查询:

```text
Service: order-service
Operation: process_order
Tags: myshop.user.tier=gold
```

可以分析金卡用户的订单处理性能。

### 场景2: 追踪促销活动效果

查询使用特定促销码的订单:

```text
Tags: myshop.promotion.code=SUMMER2024
```

### 场景3: 错误追踪

查询失败的订单:

```text
Tags: error=true
```

查看哪个步骤失败（validate_order / process_payment / update_inventory）

---

## 🔗 相关资源

### 配套文档

| 文档 | 链接 |
|------|------|
| **数据模型指南** | [📊_数据模型与语义转换完整指南_2025_10_20.md](../../📊_数据模型与语义转换完整指南_2025_10_20.md) |
| **对标分析报告** | [📊_OTLP项目2025年10月20日全面对标分析报告.md](../../📊_OTLP项目2025年10月20日全面对标分析报告.md) |
| **可视化图表** | [📊_OTLP数据生命周期可视化图表_2025_10_20.md](../../📊_OTLP数据生命周期可视化图表_2025_10_20.md) |

### OpenTelemetry官方文档

- [Go SDK文档](https://opentelemetry.io/docs/instrumentation/go/)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)
- [语义约定](https://opentelemetry.io/docs/specs/semconv/)

---

## 🎓 学习要点

### ✅ DO (推荐做法)

1. **使用vendor前缀**

   ```go
   attribute.String("myshop.order.id", order.ID) // ✅ 好
   ```

2. **标准属性+自定义属性混合**

   ```go
   semconv.HTTPMethod("POST"),              // 标准
   attribute.String("myshop.order.id", ...) // 自定义
   ```

3. **合理控制基数**

   ```go
   attribute.String("myshop.user.tier", "gold")     // ✅ 低基数 (4-5个值)
   attribute.String("myshop.order.status", "paid")  // ✅ 低基数 (5个值)
   ```

4. **记录关键事件**

   ```go
   span.AddEvent("payment_authorized", ...)
   span.AddEvent("inventory_updated", ...)
   ```

### ❌ DON'T (避免做法)

1. ❌ 不使用vendor前缀

   ```go
   attribute.String("order.id", order.ID) // ❌ 可能与标准冲突
   ```

2. ❌ 高基数属性

   ```go
   attribute.String("user.email", "user@example.com") // ❌ 百万级基数
   attribute.String("order.id", order.ID)              // ❌ 无限基数
   ```

3. ❌ 敏感数据明文

   ```go
   attribute.String("credit_card.number", "1234-5678-9012-3456") // ❌ 安全风险
   ```

---

## 🛠️ 故障排查

### 问题1: 连接OTLP Collector失败

**错误信息**:

```text
failed to create OTLP trace exporter: context deadline exceeded
```

**解决方案**:

1. 检查Collector是否运行:

   ```bash
   docker ps | grep jaeger
   ```

2. 检查端口是否正确: 默认gRPC端口为4317

3. 检查防火墙设置

---

### 问题2: Jaeger UI中看不到traces

**解决方案**:

1. 检查Service名称是否正确: `order-service`
2. 等待15-30秒（数据有延迟）
3. 检查时间范围设置
4. 查看Collector日志:

   ```bash
   docker logs jaeger
   ```

---

## 📊 性能建议

### 1. 批处理

默认已启用批处理（`WithBatcher`），性能优化：

- 批量大小: 512 spans
- 超时: 1秒

### 2. 采样

生产环境建议使用采样：

```go
// 生产环境: 1%采样
sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.01))

// 但保留所有错误trace (需要Collector的tail_sampling)
```

### 3. 异步导出

已使用`WithBatcher`，不阻塞业务逻辑。

---

**创建时间**: 2025年10月20日  
**作者**: OTLP项目团队  
**版本**: v1.0.0  
**Go版本**: 1.21+  
**OpenTelemetry SDK**: v1.21.0

---

**🛒 Happy Tracing!** ✨
