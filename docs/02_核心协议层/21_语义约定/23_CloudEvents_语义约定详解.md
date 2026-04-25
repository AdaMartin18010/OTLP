# CloudEvents 语义约定详解

> **标准来源**: OpenTelemetry Semantic Conventions v1.40.0 — CloudEvents
> **稳定性状态**: 实验性 (Experimental)
> **核心目标**: 统一 CloudEvents 规范事件在 OpenTelemetry 中的可观测性语义

---

## 一、背景

### 1.1 CloudEvents 简介

CloudEvents 是由 CNCF 托管的**云原生事件数据规范**，旨在以标准化方式描述事件数据：

```text
CloudEvents 核心目标:
├── 统一事件格式，跨服务、跨平台互操作
├── 定义一组必需的上下文属性（如事件源、类型、ID、时间）
└── 支持多种传输协议（HTTP、AMQP、MQTT、Kafka、NATS）

典型 CloudEvents 结构:
{
  "specversion": "1.0",
  "type": "com.example.order.created",
  "source": "https://example.com/orders",
  "id": "a89b-42af",
  "time": "2026-04-26T10:00:00Z",
  "datacontenttype": "application/json",
  "data": { "orderId": "12345", "amount": 99.99 }
}
```

### 1.2 为什么需要 CloudEvents 语义约定？

在云原生事件驱动架构（EDA）中：

- 事件通过消息队列（Kafka、RabbitMQ、EventBridge）传播
- 事件可能被多个消费者处理
- 事件的来源和目标需要被追踪以理解系统行为

OpenTelemetry 的 CloudEvents 语义约定将 CloudEvents 的标准属性映射到追踪、指标和日志中，实现事件流的可观测性。

---

## 二、核心属性定义

### 2.1 CloudEvents 核心属性映射

以下属性将 CloudEvents 规范中的核心上下文属性映射到 OpenTelemetry：

| 属性键 | 类型 | 对应 CloudEvents 字段 | 说明 | 必需性 |
|--------|------|----------------------|------|--------|
| `cloudevents.event.id` | string | `id` | 事件唯一标识 | 必须 |
| `cloudevents.event.source` | string | `source` | 事件来源标识符 | 必须 |
| `cloudevents.event.type` | string | `type` | 事件类型（反向域名格式）| 必须 |
| `cloudevents.event.spec_version` | string | `specversion` | CloudEvents 规范版本 | 推荐 |
| `cloudevents.event.subject` | string | `subject` | 事件主题（资源路径）| 可选 |
| `cloudevents.event.time` | string | `time` | 事件产生时间（ISO 8601）| 推荐 |
| `cloudevents.event.data_content_type` | string | `datacontenttype` | 数据内容类型 | 可选 |

### 2.2 传输协议属性

当 CloudEvents 通过特定协议传输时，记录额外的协议属性：

| 属性键 | 类型 | 说明 | 适用协议 |
|--------|------|------|---------|
| `messaging.system` | string | 消息系统名称：`kafka`、`rabbitmq`、`nats`、`eventbridge` | 所有消息协议 |
| `messaging.destination.name` | string | 主题/队列名称 | 所有消息协议 |
| `messaging.message.id` | string | 传输层消息 ID（可能与 CloudEvents ID 不同）| 所有消息协议 |
| `messaging.operation.type` | string | `publish` 或 `process` | 所有消息协议 |
| `messaging.message.body.size` | int | 消息体大小（字节）| 所有消息协议 |

---

## 三、Span 建模

### 3.1 事件发布（Producer）

```text
Span: publish com.example.order.created (Span, PRODUCER kind)
├── 属性: cloudevents.event.id=a89b-42af
├── 属性: cloudevents.event.source=https://example.com/orders
├── 属性: cloudevents.event.type=com.example.order.created
├── 属性: cloudevents.event.spec_version=1.0
├── 属性: cloudevents.event.time=2026-04-26T10:00:00Z
├── 属性: messaging.system=kafka
├── 属性: messaging.destination.name=orders-events
├── 属性: messaging.operation.type=publish
└── 传播: 将 traceparent 注入 CloudEvents 扩展属性 (traceparent)
```

### 3.2 事件消费（Consumer）

```text
Span: process com.example.order.created (Span, CONSUMER kind)
├── 属性: cloudevents.event.id=a89b-42af
├── 属性: cloudevents.event.source=https://example.com/orders
├── 属性: cloudevents.event.type=com.example.order.created
├── 属性: cloudevents.event.spec_version=1.0
├── 属性: cloudevents.event.time=2026-04-26T10:00:00Z
├── 属性: messaging.system=kafka
├── 属性: messaging.destination.name=orders-events
├── 属性: messaging.operation.type=process
├── 属性: messaging.message.id=kafka-offset-10245
└── 链接: 通过 Link 关联到 Producer Span
```

### 3.3 端到端事件流

```text
Trace: order-created-event-flow
├── Span: publish com.example.order.created (PRODUCER)
│   ├── 服务: order-service
│   └── 时间: 10:00:00
│
├── Span: process com.example.order.created (CONSUMER)
│   ├── 服务: inventory-service
│   ├── 时间: 10:00:01
│   └── Link → publish Span
│
├── Span: process com.example.order.created (CONSUMER)
│   ├── 服务: notification-service
│   ├── 时间: 10:00:02
│   └── Link → publish Span
│
└── Span: process com.example.order.created (CONSUMER)
    ├── 服务: analytics-service
    ├── 时间: 10:00:05
    └── Link → publish Span
```

**注意**: 在事件驱动架构中，一个生产者可能对应多个消费者。官方推荐使用 **Link** 而非父子 Span 关系来建模，因为消费者之间通常没有直接的父子关系。

---

## 四、上下文传播

### 4.1 CloudEvents 中的追踪上下文

CloudEvents 规范支持通过**扩展属性**（Extension Attributes）携带追踪上下文：

```json
{
  "specversion": "1.0",
  "type": "com.example.order.created",
  "source": "https://example.com/orders",
  "id": "a89b-42af",
  "traceparent": "00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01",
  "tracestate": "congo=tucorr",
  "data": { ... }
}
```

### 4.2 传播实现

```java
// Java: 在发布 CloudEvents 时注入追踪上下文
CloudEvent event = CloudEventBuilder.v1()
    .withId(UUID.randomUUID().toString())
    .withSource(URI.create("https://example.com/orders"))
    .withType("com.example.order.created")
    .withData(contentType, data)
    // 注入 W3C Trace Context
    .withExtension("traceparent", W3CTraceContextPropagator.getTraceParent(context))
    .withExtension("tracestate", W3CTraceContextPropagator.getTraceState(context))
    .build();

// 在消费 CloudEvents 时提取追踪上下文
String traceparent = event.getExtension("traceparent");
Context context = W3CTraceContextPropagator.extract(traceparent);
```

---

## 五、与 Messaging 语义约定的关系

CloudEvents 经常通过消息系统传输，因此 CloudEvents 属性与 Messaging 语义约定存在重叠：

| 场景 | 主要属性集 | 说明 |
|------|----------|------|
| CloudEvents over Kafka | `cloudevents.*` + `messaging.*` | 同时记录两种属性 |
| CloudEvents over HTTP | `cloudevents.*` + `http.*` | 通过 Webhook 传输时 |
| 原生消息（非 CloudEvents）| `messaging.*` | 不使用 CloudEvents 包装时 |

**推荐做法**: 当消息体是 CloudEvents 格式时，同时提取并记录 `cloudevents.*` 和 `messaging.*` 属性，以便在不同维度上查询分析。

---

## 六、检查清单

- [ ] 发布事件时记录了完整的 `cloudevents.event.id`、`source`、`type`
- [ ] 通过扩展属性注入了 `traceparent` 和 `tracestate`
- [ ] 消费事件时从扩展属性中提取了追踪上下文
- [ ] 消费者 Span 使用 CONSUMER kind，生产者 Span 使用 PRODUCER kind
- [ ] 多消费者场景使用 Link 关联到生产者 Span（而非强制父子关系）
- [ ] 传输层属性（`messaging.*` 或 `http.*`）与 CloudEvents 属性同时记录
- [ ] 事件处理失败时正确记录 Span 状态为 ERROR

---

## 七、参考资源

- OpenTelemetry Semantic Conventions: CloudEvents
- OpenTelemetry Semantic Conventions: Messaging
- CloudEvents Specification: github.com/cloudevents/spec
- CNCF CloudEvents: cloudevents.io

---

> **总结**: CloudEvents 语义约定将标准化的云原生事件格式与 OpenTelemetry 的可观测性框架连接起来。通过在追踪中记录 `cloudevents.event.*` 属性，并在事件传播中注入 W3C Trace Context，团队可以完整观测事件从产生到被多个消费者处理的全生命周期，实现事件驱动架构的透明化。
