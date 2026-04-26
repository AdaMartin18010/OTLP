# W3C Trace Context: AMQP 协议绑定规范

> **标准来源**: W3C Trace Context: AMQP protocol binding — Working Draft
> **发布机构**: W3C Distributed Tracing Working Group
> **核心目标**: 解读 W3C Trace Context 在 AMQP（Advanced Message Queuing Protocol）消息协议中的传播机制

---

## 一、背景

### 1.1 为什么 AMQP 需要 Trace Context？

AMQP 是企业级消息队列的核心协议，被 RabbitMQ、Azure Service Bus、ActiveMQ 等广泛采用。在微服务架构中，消息队列常作为异步通信的骨干：

```text
同步调用:                    异步消息:
服务A → HTTP → 服务B        服务A → AMQP → 队列 → 服务B
   │                            │
   └── traceparent 头            └── 需要消息属性传播 traceparent
```

没有标准化的 Trace Context 传播，异步链路的追踪会断裂。

### 1.2 标准状态

W3C Trace Context: AMQP protocol binding 目前处于 **Working Draft** 阶段，尚未进入候选推荐标准。这意味着：

- 规范内容可能发生变化
- 各实现商的实现可能存在差异
- 但核心方向已明确，可以提前了解和应用

---

## 二、AMQP 协议概述

### 2.1 AMQP 0-9-1 与 AMQP 1.0

| 版本 | 主要实现 | 特性 |
|------|---------|------|
| **AMQP 0-9-1** | RabbitMQ | 简单，生态最广泛 |
| **AMQP 1.0** | Azure Service Bus, ActiveMQ, Qpid | 标准化 ISO/IEC 19464，支持更广泛 |

W3C 规范主要基于 **AMQP 1.0** 设计，但原则也适用于 0-9-1。

### 2.2 AMQP 消息结构

```text
AMQP 1.0 消息结构:

Message
├── Properties (系统属性)
│   ├── message_id
│   ├── user_id
│   ├── to
│   ├── subject
│   ├── reply_to
│   ├── correlation_id
│   ├── content_type
│   ├── content_encoding
│   ├── absolute_expiry_time
│   ├── creation_time
│   ├── group_id
│   ├── group_sequence
│   └── reply_to_group_id
│
├── Application Properties (应用自定义属性)
│   └── 键值对，用于传递业务属性和追踪上下文
│
├── Delivery Annotations (投递注解)
│   └── 由中间件添加，如路由信息
│
├── Message Annotations (消息注解)
│   └── 端到端传递的注解
│
├── Header (AMQP 0-9-1)
│   └── 包含 delivery_mode, priority, correlation_id 等
│
└── Body (消息体)
```

---

## 三、Trace Context 在 AMQP 中的映射

### 3.1 属性映射规则

W3C 规范定义将 `traceparent` 和 `tracestate` 映射到 AMQP 的 **Application Properties**：

| W3C 字段 | AMQP 属性键 | 说明 |
|---------|------------|------|
| traceparent | `traceparent` | 标准追踪上下文 |
| tracestate | `tracestate` | 厂商扩展上下文 |

```text
AMQP 1.0 消息示例:

{
  "properties": {
    "message_id": "msg-001",
    "content_type": "application/json"
  },
  "application_properties": {
    "traceparent": "00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01",
    "tracestate": "congo=tucorr"
  },
  "body": {
    "order_id": "12345",
    "amount": 99.99
  }
}
```

### 3.2 AMQP 0-9-1 (RabbitMQ) 映射

在 AMQP 0-9-1 中，使用 **headers** 属性表传递：

```text
AMQP 0-9-1 消息示例:

BasicProperties
├── headers:
│   ├── traceparent: "00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01"
│   └── tracestate: "congo=tucorr"
├── content_type: "application/json"
└── delivery_mode: 2
```

---

## 四、实现示例

### 4.1 Java (RabbitMQ Client)

```java
// 生产者：注入 Trace Context
import com.rabbitmq.client.AMQP;
import com.rabbitmq.client.Channel;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.propagation.TextMapPropagator;

public void sendMessage(Channel channel, String exchange, String routingKey, byte[] body) {
    // 从当前 Span 获取 Context
    Context context = Context.current();

    // 构建 headers
    Map<String, Object> headers = new HashMap<>();

    // 注入 traceparent 和 tracestate
    TextMapPropagator propagator = openTelemetry.getPropagators().getTextMapPropagator();
    propagator.inject(context, headers, (carrier, key, value) -> carrier.put(key, value));

    AMQP.BasicProperties props = new AMQP.BasicProperties.Builder()
        .contentType("application/json")
        .headers(headers)  // 包含 traceparent
        .deliveryMode(2)   // 持久化
        .build();

    channel.basicPublish(exchange, routingKey, props, body);
}

// 消费者：提取 Trace Context
public void consumeMessage(Channel channel, String queue) throws IOException {
    channel.basicConsume(queue, false, (consumerTag, delivery) -> {
        Map<String, Object> headers = delivery.getProperties().getHeaders();

        // 从 headers 提取 traceparent
        Context context = propagator.extract(
            Context.current(),
            headers,
            (carrier, key) -> {
                Object value = carrier.get(key);
                return value != null ? value.toString() : null;
            }
        );

        // 在提取的上下文中创建消费者 Span
        try (Scope scope = context.makeCurrent()) {
            Span span = tracer.spanBuilder("process-message")
                .setSpanKind(SpanKind.CONSUMER)
                .setAttribute("messaging.system", "rabbitmq")
                .setAttribute("messaging.destination.name", queue)
                .startSpan();

            try {
                processMessage(delivery.getBody());
                channel.basicAck(delivery.getEnvelope().getDeliveryTag(), false);
            } catch (Exception e) {
                span.recordException(e);
                channel.basicNack(delivery.getEnvelope().getDeliveryTag(), false, true);
            } finally {
                span.end();
            }
        }
    }, consumerTag -> {});
}
```

### 4.2 Python (RabbitMQ / Pika)

```python
import pika
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind

def send_message(channel, exchange, routing_key, body):
    # 注入追踪上下文到 headers
    headers = {}
    propagate.inject(headers)

    channel.basic_publish(
        exchange=exchange,
        routing_key=routing_key,
        body=body,
        properties=pika.BasicProperties(
            content_type='application/json',
            headers=headers,
            delivery_mode=2
        )
    )

def consume_message(channel, queue):
    def callback(ch, method, properties, body):
        # 从 headers 提取上下文
        context = propagate.extract(properties.headers or {})

        with trace.get_tracer(__name__).start_as_current_span(
            "process-message",
            kind=SpanKind.CONSUMER,
            context=context,
            attributes={
                "messaging.system": "rabbitmq",
                "messaging.destination.name": queue,
            }
        ):
            process_message(body)
            ch.basic_ack(delivery_tag=method.delivery_tag)

    channel.basic_consume(queue=queue, on_message_callback=callback)
```

### 4.3 .NET (Azure Service Bus)

```csharp
// 发送消息时注入
var message = new ServiceBusMessage(body);

// 使用 OpenTelemetry 的 propagator 注入
var propagator = Propagators.DefaultTextMapPropagator;
var context = PropagationContext.Current;

propagator.Inject(context, message.ApplicationProperties,
    (props, key, value) => props[key] = value);

await sender.SendMessageAsync(message);

// 接收消息时提取
var receivedMessage = await receiver.ReceiveMessageAsync();
var parentContext = propagator.Extract(
    default,
    receivedMessage.ApplicationProperties,
    (props, key) => props.TryGetValue(key, out var value) ? new[] { value.ToString() } : null
);

using var activity = activitySource.StartActivity("ProcessMessage",
    ActivityKind.Consumer, parentContext.ActivityContext);
```

---

## 五、与 OpenTelemetry Messaging 语义约定的关系

### 5.1 统一的消息可观测性模型

AMQP 的 Trace Context 传播应与 OpenTelemetry Messaging Semantic Conventions 结合使用：

```text
生产者 Span (PRODUCER kind):
├── messaging.system = "rabbitmq"
├── messaging.destination.name = "orders-queue"
├── messaging.operation.type = "publish"
└── traceparent 注入消息 headers

消费者 Span (CONSUMER kind):
├── messaging.system = "rabbitmq"
├── messaging.destination.name = "orders-queue"
├── messaging.operation.type = "process"
├── messaging.message.id = "msg-001"
└── Link → 生产者 Span
```

### 5.2 批处理消息的特殊处理

当消费者一次处理多条消息时：

```text
场景: 消费者从队列批量拉取 10 条消息

处理方式:
├── 方案A: 为每条消息创建独立 Span
│   └── 优点: 精确追踪每条消息的处理
│   └── 缺点: Span 数量多
│
├── 方案B: 创建一个"batch-process" Span，用 Link 关联所有消息
│   └── 优点: Span 数量可控
│   └── 缺点: 单条消息处理细节丢失
│
└── 推荐: 方案A（如果消息数量 < 100），否则方案B
```

---

## 六、常见问题

### 6.1 中间件是否会剥离 headers？

| 中间件 | 行为 | 建议 |
|--------|------|------|
| **RabbitMQ** | 默认保留所有 headers | 无需特殊配置 |
| **Azure Service Bus** | 保留 Application Properties | 使用 Application Properties |
| **ActiveMQ** | 保留 headers | 无需特殊配置 |
| **企业级代理** | 可能过滤未知属性 | 将 traceparent 加入白名单 |

### 6.2 消息大小限制

AMQP 消息属性有大小限制，但 `traceparent`（约 55 字节）和 `tracestate`（通常 < 512 字节）不会构成问题。

---

## 七、检查清单

- [ ] 生产者将 `traceparent` 注入 AMQP headers / application_properties
- [ ] 消费者从 headers / application_properties 提取 `traceparent`
- [ ] 消费者 Span 使用 `CONSUMER` kind，生产者 Span 使用 `PRODUCER` kind
- [ ] 遵循 Messaging Semantic Conventions（`messaging.system`, `messaging.destination.name`）
- [ ] 批处理场景选择合适的 Span 建模策略
- [ ] 确认中间件不会过滤追踪属性
- [ ] 异常消息处理（Nack/Requeue）时正确记录 Span 状态

---

## 八、参考资源

- W3C Trace Context: AMQP protocol binding (Working Draft)
- OpenTelemetry Semantic Conventions: Messaging
- RabbitMQ Documentation: Message Properties
- Azure Service Bus: Application Properties

---

> **总结**: W3C Trace Context 在 AMQP 中的绑定相对简单，核心是将 `traceparent` 和 `tracestate` 放入消息的应用属性（AMQP 1.0）或 headers（AMQP 0-9-1）中。虽然规范仍处于 Working Draft，但实现模式已明确，可在生产环境中应用。关键是与 OpenTelemetry Messaging Semantic Conventions 结合，确保跨消息队列的追踪完整性。
