---
title: NATS语义约定详解
description: NATS语义约定详解 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 标准规范
tags:
  - otlp
  - observability
  - performance
  - optimization
status: published
---
# NATS语义约定详解

> **云原生消息系统**: NATS Tracing与Metrics完整规范
> **最后更新**: 2025年10月8日

---

## 目录

- [NATS语义约定详解](#nats语义约定详解)
  - [目录](#目录)
  - [1. NATS概述](#1-nats概述)
    - [1.1 NATS特点](#11-nats特点)
    - [1.2 NATS消息模式](#12-nats消息模式)
  - [2. NATS通用属性](#2-nats通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. NATS Producer属性](#3-nats-producer属性)
    - [3.1 基本属性](#31-基本属性)
    - [3.2 JetStream属性](#32-jetstream属性)
  - [4. NATS Consumer属性](#4-nats-consumer属性)
    - [4.1 订阅属性](#41-订阅属性)
    - [4.2 JetStream Consumer属性](#42-jetstream-consumer属性)
  - [5. Context传播](#5-context传播)
    - [5.1 Core NATS传播](#51-core-nats传播)
    - [5.2 JetStream传播](#52-jetstream传播)
  - [6. Go实现示例](#6-go实现示例)
    - [6.1 Core NATS Publisher](#61-core-nats-publisher)
    - [6.2 Core NATS Subscriber](#62-core-nats-subscriber)
    - [6.3 JetStream Publisher](#63-jetstream-publisher)
    - [6.4 JetStream Consumer](#64-jetstream-consumer)
  - [7. Python实现示例](#7-python实现示例)
    - [7.1 Core NATS](#71-core-nats)
    - [7.2 JetStream](#72-jetstream)
  - [8. Metrics定义](#8-metrics定义)
    - [8.1 Producer Metrics](#81-producer-metrics)
    - [8.2 Consumer Metrics](#82-consumer-metrics)
    - [8.3 JetStream Metrics](#83-jetstream-metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 错误处理](#92-错误处理)
    - [9.3 监控建议](#93-监控建议)
  - [10. 完整示例](#10-完整示例)
    - [10.1 请求-响应模式](#101-请求-响应模式)
    - [10.2 Queue Group模式](#102-queue-group模式)

---

## 1. NATS概述

### 1.1 NATS特点

```text
NATS (Neural Autonomic Transport System)

核心特性:
✅ 高性能 (百万级消息/秒)
✅ 简单易用 (极简API)
✅ 云原生 (Kubernetes友好)
✅ 多语言支持 (40+ 客户端库)
✅ 零依赖 (单一二进制)

消息模式:
1. Publish-Subscribe (发布-订阅)
2. Request-Reply (请求-响应)
3. Queue Groups (队列组/负载均衡)

JetStream (持久化):
✅ At-least-once delivery
✅ Exactly-once semantics
✅ Message replay
✅ Stream persistence
✅ Consumer groups
```

### 1.2 NATS消息模式

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Core NATS (Fire-and-Forget)

   Publisher → [NATS Server] → Subscribers

   特点:
   - 无持久化
   - At-most-once
   - 超高性能
   - 零消息顺序保证

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

2. JetStream (Persistent)

   Publisher → [Stream] → Consumer

   特点:
   - 消息持久化
   - At-least-once
   - 消息重放
   - 顺序保证
   - Exactly-once (with deduplication)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. NATS通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"nats"` |
| `messaging.destination.name` | string | Subject名称 | `"orders.created"` |
| `messaging.operation` | string | 操作类型 | `"publish"`, `"receive"` |
| `net.peer.name` | string | NATS服务器地址 | `"nats.example.com"` |
| `net.peer.port` | int | NATS服务器端口 | `4222` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.nats.cluster.name` | string | 集群名称 | `"prod-cluster"` |
| `messaging.nats.server.id` | string | 服务器ID | `"NATS-SERVER-123"` |
| `messaging.nats.server.name` | string | 服务器名称 | `"nats-1"` |
| `messaging.nats.server.version` | string | 服务器版本 | `"2.10.0"` |
| `messaging.message.id` | string | 消息ID (JetStream) | `"msg-123456"` |
| `messaging.message.body.size` | int | 消息体大小(字节) | `1024` |

---

## 3. NATS Producer属性

### 3.1 基本属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Core NATS Publisher:

必需属性:
✅ messaging.system = "nats"
✅ messaging.destination.name (Subject)
✅ messaging.operation = "publish"
✅ net.peer.name (服务器地址)
✅ net.peer.port (服务器端口)

推荐属性:
📋 messaging.message.body.size
📋 messaging.nats.subject (完整subject)
📋 messaging.nats.reply_to (reply subject)

示例:
    ```go
    span.SetAttributes(
        semconv.MessagingSystemKey.String("nats"),
        semconv.MessagingDestinationNameKey.String("orders.created"),
        semconv.MessagingOperationKey.String("publish"),
        semconv.NetPeerNameKey.String("nats.prod.local"),
        semconv.NetPeerPortKey.Int(4222),
        attribute.Int("messaging.message.body.size", len(data)),
    )
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 3.2 JetStream属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.nats.jetstream.stream` | string | Stream名称 | `"ORDERS"` |
| `messaging.nats.jetstream.subject` | string | Stream Subject | `"orders.*"` |
| `messaging.message.id` | string | 消息ID | `"166242418000000001"` |
| `messaging.nats.jetstream.sequence` | int | 序列号 | `123456` |
| `messaging.nats.jetstream.expected_stream` | string | 预期Stream | `"ORDERS"` |
| `messaging.nats.jetstream.duplicate_window` | string | 去重窗口 | `"2m"` |

```go
// JetStream Publish示例
span.SetAttributes(
    semconv.MessagingSystemKey.String("nats"),
    semconv.MessagingDestinationNameKey.String("orders.created"),
    semconv.MessagingOperationKey.String("publish"),
    attribute.String("messaging.nats.jetstream.stream", "ORDERS"),
    attribute.String("messaging.message.id", msgID),
    attribute.Int64("messaging.nats.jetstream.sequence", pubAck.Sequence),
    attribute.String("messaging.nats.jetstream.duplicate",
        fmt.Sprintf("%v", pubAck.Duplicate)),
)
```

---

## 4. NATS Consumer属性

### 4.1 订阅属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Core NATS Subscriber:

必需属性:
✅ messaging.system = "nats"
✅ messaging.destination.name (Subject)
✅ messaging.operation = "receive"
✅ net.peer.name
✅ net.peer.port

推荐属性:
📋 messaging.nats.queue_group (队列组名称)
📋 messaging.nats.pending_messages (待处理消息数)
📋 messaging.nats.subscription.subject (订阅subject)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.nats.subscription.id` | string | 订阅ID | `"sub-123"` |
| `messaging.nats.queue_group` | string | 队列组名称 | `"workers"` |
| `messaging.nats.pending_messages` | int | 待处理消息数 | `10` |
| `messaging.nats.delivered_messages` | int | 已投递消息数 | `1000` |
| `messaging.nats.dropped_messages` | int | 丢弃消息数 | `5` |

### 4.2 JetStream Consumer属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.nats.jetstream.consumer` | string | Consumer名称 | `"order-processor"` |
| `messaging.nats.jetstream.stream` | string | Stream名称 | `"ORDERS"` |
| `messaging.nats.jetstream.deliver_subject` | string | 投递Subject | `"deliver.orders"` |
| `messaging.nats.jetstream.ack_policy` | string | ACK策略 | `"explicit"`, `"none"`, `"all"` |
| `messaging.nats.jetstream.replay_policy` | string | 重放策略 | `"instant"`, `"original"` |
| `messaging.nats.jetstream.pending` | int | 待ACK消息数 | `5` |
| `messaging.message.id` | string | 消息ID | `"msg-123"` |
| `messaging.nats.jetstream.sequence` | int | Stream序列号 | `123456` |
| `messaging.nats.jetstream.num_delivered` | int | 投递次数 | `1` |
| `messaging.nats.jetstream.num_pending` | int | 待投递数 | `100` |

```go
// JetStream Consumer示例
span.SetAttributes(
    semconv.MessagingSystemKey.String("nats"),
    semconv.MessagingOperationKey.String("receive"),
    attribute.String("messaging.nats.jetstream.consumer", "order-processor"),
    attribute.String("messaging.nats.jetstream.stream", "ORDERS"),
    attribute.String("messaging.destination.name", msg.Subject),
    attribute.Int64("messaging.nats.jetstream.sequence",
        meta.Sequence.Stream),
    attribute.Int("messaging.nats.jetstream.num_delivered",
        meta.NumDelivered),
    attribute.Int("messaging.nats.jetstream.num_pending",
        meta.NumPending),
)
```

---

## 5. Context传播

### 5.1 Core NATS传播

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Core NATS不支持消息Headers，需要通过消息体传播:

方案1: JSON封装
{
    "traceparent": "00-abc123...-span001-01",
    "tracestate": "vendor=value",
    "data": { ... }
}

方案2: Protobuf封装
message NATSMessage {
    map<string, string> headers = 1;
    bytes data = 2;
}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 JetStream传播

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

JetStream支持Headers (NATS v2.2.0+):

Headers:
- Nats-Msg-Id: <message-id>
- traceparent: <w3c-trace-context>
- tracestate: <vendor-state>
- Custom-Header: <value>

优点:
✅ 原生Header支持
✅ 不影响消息体
✅ 自动传播
✅ 标准兼容

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 6. Go实现示例

### 6.1 Core NATS Publisher

```go
package main

import (
    "context"
    "encoding/json"

    "github.com/nats-io/nats.go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

type MessageWithContext struct {
    TraceParent string                 `json:"traceparent"`
    TraceState  string                 `json:"tracestate,omitempty"`
    Data        map[string]interface{} `json:"data"`
}

func PublishWithTracing(
    ctx context.Context,
    nc *nats.Conn,
    subject string,
    data map[string]interface{},
) error {
    tracer := otel.Tracer("nats-publisher")

    // 创建Span
    ctx, span := tracer.Start(ctx, "nats.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("nats"),
            semconv.MessagingDestinationNameKey.String(subject),
            semconv.MessagingOperationKey.String("publish"),
            semconv.NetPeerNameKey.String(nc.ConnectedUrl()),
        ),
    )
    defer span.End()

    // 注入Trace Context到消息
    msg := MessageWithContext{
        Data: data,
    }

    // 使用MapCarrier提取context
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)

    msg.TraceParent = carrier["traceparent"]
    msg.TraceState = carrier["tracestate"]

    // 序列化消息
    payload, err := json.Marshal(msg)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "marshal failed")
        return err
    }

    // 添加消息大小属性
    span.SetAttributes(
        attribute.Int("messaging.message.body.size", len(payload)),
    )

    // 发布消息
    if err := nc.Publish(subject, payload); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }

    span.SetStatus(codes.Ok, "published")
    return nil
}
```

### 6.2 Core NATS Subscriber

```go
func SubscribeWithTracing(
    nc *nats.Conn,
    subject string,
    queueGroup string,
    handler func(context.Context, map[string]interface{}) error,
) (*nats.Subscription, error) {
    tracer := otel.Tracer("nats-subscriber")

    _, err := nc.QueueSubscribe(subject, queueGroup, func(m *nats.Msg) {
        // 解析消息
        var msg MessageWithContext
        if err := json.Unmarshal(m.Data, &msg); err != nil {
            // 错误处理
            return
        }

        // 提取Trace Context
        carrier := propagation.MapCarrier{
            "traceparent": msg.TraceParent,
            "tracestate":  msg.TraceState,
        }

        ctx := otel.GetTextMapPropagator().Extract(
            context.Background(),
            carrier,
        )

        // 创建Consumer Span
        ctx, span := tracer.Start(ctx, "nats.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("nats"),
                semconv.MessagingDestinationNameKey.String(m.Subject),
                semconv.MessagingOperationKey.String("receive"),
                attribute.String("messaging.nats.queue_group", queueGroup),
                attribute.Int("messaging.message.body.size", len(m.Data)),
            ),
        )
        defer span.End()

        // 处理消息
        if err := handler(ctx, msg.Data); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            return
        }

        span.SetStatus(codes.Ok, "processed")
    })

    return nil, err
}
```

### 6.3 JetStream Publisher

```go
func PublishJetStreamWithTracing(
    ctx context.Context,
    js nats.JetStreamContext,
    subject string,
    data []byte,
) error {
    tracer := otel.Tracer("jetstream-publisher")

    ctx, span := tracer.Start(ctx, "jetstream.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("nats"),
            semconv.MessagingDestinationNameKey.String(subject),
            semconv.MessagingOperationKey.String("publish"),
        ),
    )
    defer span.End()

    // 创建消息
    msg := nats.NewMsg(subject)
    msg.Data = data

    // JetStream支持Headers，直接注入
    if msg.Header == nil {
        msg.Header = nats.Header{}
    }

    // 注入Trace Context到Headers
    otel.GetTextMapPropagator().Inject(ctx,
        propagation.HeaderCarrier(msg.Header))

    // 发布消息
    pubAck, err := js.PublishMsg(msg)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }

    // 记录JetStream属性
    span.SetAttributes(
        attribute.String("messaging.nats.jetstream.stream", pubAck.Stream),
        attribute.Int64("messaging.nats.jetstream.sequence",
            int64(pubAck.Sequence)),
        attribute.Bool("messaging.nats.jetstream.duplicate",
            pubAck.Duplicate),
        attribute.Int("messaging.message.body.size", len(data)),
    )

    span.SetStatus(codes.Ok, "published")
    return nil
}
```

### 6.4 JetStream Consumer

```go
func ConsumeJetStreamWithTracing(
    js nats.JetStreamContext,
    streamName, consumerName string,
    handler func(context.Context, *nats.Msg) error,
) error {
    tracer := otel.Tracer("jetstream-consumer")

    // 订阅
    sub, err := js.PullSubscribe("", consumerName,
        nats.BindStream(streamName))
    if err != nil {
        return err
    }

    // 消费循环
    for {
        msgs, err := sub.Fetch(10, nats.MaxWait(5*time.Second))
        if err != nil {
            continue
        }

        for _, msg := range msgs {
            // 提取Trace Context
            ctx := otel.GetTextMapPropagator().Extract(
                context.Background(),
                propagation.HeaderCarrier(msg.Header),
            )

            // 获取元数据
            meta, _ := msg.Metadata()

            // 创建Span
            ctx, span := tracer.Start(ctx, "jetstream.receive",
                trace.WithSpanKind(trace.SpanKindConsumer),
                trace.WithAttributes(
                    semconv.MessagingSystemKey.String("nats"),
                    semconv.MessagingOperationKey.String("receive"),
                    semconv.MessagingDestinationNameKey.String(msg.Subject),
                    attribute.String("messaging.nats.jetstream.consumer",
                        consumerName),
                    attribute.String("messaging.nats.jetstream.stream",
                        streamName),
                    attribute.Int64("messaging.nats.jetstream.sequence",
                        int64(meta.Sequence.Stream)),
                    attribute.Int("messaging.nats.jetstream.num_delivered",
                        int(meta.NumDelivered)),
                    attribute.Int("messaging.nats.jetstream.num_pending",
                        int(meta.NumPending)),
                    attribute.Int("messaging.message.body.size",
                        len(msg.Data)),
                ),
            )

            // 处理消息
            if err := handler(ctx, msg); err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, "handler failed")
                msg.Nak() // Negative ACK
            } else {
                span.SetStatus(codes.Ok, "processed")
                msg.Ack() // ACK
            }

            span.End()
        }
    }

    return nil
}
```

---

## 7. Python实现示例

### 7.1 Core NATS

```python
import asyncio
import json
from typing import Dict, Any

import nats
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

async def publish_with_tracing(
    nc: nats.NATS,
    subject: str,
    data: Dict[str, Any]
):
    """Core NATS发布with tracing"""
    with tracer.start_as_current_span(
        "nats.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "nats",
            SpanAttributes.MESSAGING_DESTINATION_NAME: subject,
            SpanAttributes.MESSAGING_OPERATION: "publish",
            SpanAttributes.NET_PEER_NAME: nc.connected_url.hostname,
            SpanAttributes.NET_PEER_PORT: nc.connected_url.port,
        }
    ) as span:
        # 注入trace context
        carrier = {}
        propagate.inject(carrier)

        # 封装消息
        message = {
            "traceparent": carrier.get("traceparent"),
            "tracestate": carrier.get("tracestate"),
            "data": data
        }

        # 序列化
        payload = json.dumps(message).encode()

        # 添加消息大小
        span.set_attribute("messaging.message.body.size", len(payload))

        try:
            # 发布
            await nc.publish(subject, payload)
            span.set_status(Status(StatusCode.OK))
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

async def subscribe_with_tracing(
    nc: nats.NATS,
    subject: str,
    queue: str,
    handler
):
    """Core NATS订阅with tracing"""
    async def message_handler(msg):
        # 解析消息
        message = json.loads(msg.data.decode())

        # 提取trace context
        carrier = {
            "traceparent": message.get("traceparent"),
            "tracestate": message.get("tracestate")
        }
        ctx = propagate.extract(carrier)

        # 创建span
        with tracer.start_as_current_span(
            "nats.receive",
            context=ctx,
            kind=SpanKind.CONSUMER,
            attributes={
                SpanAttributes.MESSAGING_SYSTEM: "nats",
                SpanAttributes.MESSAGING_DESTINATION_NAME: msg.subject,
                SpanAttributes.MESSAGING_OPERATION: "receive",
                "messaging.nats.queue_group": queue,
                "messaging.message.body.size": len(msg.data),
            }
        ) as span:
            try:
                # 处理消息
                await handler(message["data"])
                span.set_status(Status(StatusCode.OK))
            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR))

    await nc.subscribe(subject, queue=queue, cb=message_handler)
```

### 7.2 JetStream

```python
async def publish_jetstream_with_tracing(
    js: nats.JetStream,
    subject: str,
    data: bytes
):
    """JetStream发布with tracing"""
    with tracer.start_as_current_span(
        "jetstream.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "nats",
            SpanAttributes.MESSAGING_DESTINATION_NAME: subject,
            SpanAttributes.MESSAGING_OPERATION: "publish",
        }
    ) as span:
        # JetStream支持headers
        headers = {}
        propagate.inject(headers)

        try:
            # 发布消息
            ack = await js.publish(subject, data, headers=headers)

            # 记录JetStream属性
            span.set_attributes({
                "messaging.nats.jetstream.stream": ack.stream,
                "messaging.nats.jetstream.sequence": ack.seq,
                "messaging.nats.jetstream.duplicate": ack.duplicate,
                "messaging.message.body.size": len(data),
            })

            span.set_status(Status(StatusCode.OK))
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

async def consume_jetstream_with_tracing(
    js: nats.JetStream,
    stream_name: str,
    consumer_name: str,
    handler
):
    """JetStream消费with tracing"""
    # 创建pull consumer
    psub = await js.pull_subscribe("", consumer_name, stream=stream_name)

    while True:
        try:
            # 拉取消息
            msgs = await psub.fetch(10, timeout=5.0)

            for msg in msgs:
                # 提取trace context
                ctx = propagate.extract(msg.headers or {})

                # 获取元数据
                meta = msg.metadata

                # 创建span
                with tracer.start_as_current_span(
                    "jetstream.receive",
                    context=ctx,
                    kind=SpanKind.CONSUMER,
                    attributes={
                        SpanAttributes.MESSAGING_SYSTEM: "nats",
                        SpanAttributes.MESSAGING_OPERATION: "receive",
                        SpanAttributes.MESSAGING_DESTINATION_NAME: msg.subject,
                        "messaging.nats.jetstream.consumer": consumer_name,
                        "messaging.nats.jetstream.stream": stream_name,
                        "messaging.nats.jetstream.sequence": meta.sequence.stream,
                        "messaging.nats.jetstream.num_delivered": meta.num_delivered,
                        "messaging.nats.jetstream.num_pending": meta.num_pending,
                        "messaging.message.body.size": len(msg.data),
                    }
                ) as span:
                    try:
                        # 处理消息
                        await handler(msg.data)
                        await msg.ack()
                        span.set_status(Status(StatusCode.OK))
                    except Exception as e:
                        span.record_exception(e)
                        span.set_status(Status(StatusCode.ERROR))
                        await msg.nak()

        except asyncio.TimeoutError:
            continue
```

---

## 8. Metrics定义

### 8.1 Producer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.nats.publish.duration` | Histogram | ms | 发布延迟 |
| `messaging.nats.publish.messages` | Counter | messages | 发布消息数 |
| `messaging.nats.publish.bytes` | Counter | bytes | 发布字节数 |
| `messaging.nats.publish.errors` | Counter | errors | 发布错误数 |

### 8.2 Consumer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.nats.receive.duration` | Histogram | ms | 消费延迟 |
| `messaging.nats.receive.messages` | Counter | messages | 接收消息数 |
| `messaging.nats.receive.bytes` | Counter | bytes | 接收字节数 |
| `messaging.nats.pending.messages` | Gauge | messages | 待处理消息数 |
| `messaging.nats.dropped.messages` | Counter | messages | 丢弃消息数 |

### 8.3 JetStream Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.nats.jetstream.stream.messages` | Gauge | messages | Stream消息总数 |
| `messaging.nats.jetstream.stream.bytes` | Gauge | bytes | Stream字节总数 |
| `messaging.nats.jetstream.consumer.pending` | Gauge | messages | Consumer待ACK数 |
| `messaging.nats.jetstream.consumer.redelivered` | Counter | messages | 重投递消息数 |
| `messaging.nats.jetstream.ack.duration` | Histogram | ms | ACK延迟 |

```go
// Metrics示例
var (
    publishDuration = meter.Float64Histogram(
        "messaging.nats.publish.duration",
        metric.WithUnit("ms"),
        metric.WithDescription("NATS publish latency"),
    )

    publishMessages = meter.Int64Counter(
        "messaging.nats.publish.messages",
        metric.WithUnit("messages"),
        metric.WithDescription("Number of published messages"),
    )

    pendingMessages = meter.Int64ObservableGauge(
        "messaging.nats.pending.messages",
        metric.WithUnit("messages"),
        metric.WithDescription("Number of pending messages"),
    )
)

// 使用
func publish(nc *nats.Conn, subject string, data []byte) error {
    start := time.Now()

    err := nc.Publish(subject, data)

    duration := time.Since(start).Milliseconds()
    publishDuration.Record(ctx, float64(duration),
        attribute.String("subject", subject),
        attribute.String("result", status(err)),
    )

    if err == nil {
        publishMessages.Add(ctx, 1,
            attribute.String("subject", subject),
        )
    }

    return err
}
```

---

## 9. 最佳实践

### 9.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 连接池 ⭐⭐⭐⭐⭐
   - 复用连接
   - 避免频繁连接
   - 配置连接池大小

2. 批量发送 ⭐⭐⭐⭐
   - 使用PublishAsync
   - 批量处理消息
   - 减少网络往返

3. 异步处理 ⭐⭐⭐⭐⭐
   - 非阻塞订阅
   - 异步ACK
   - 并发处理

4. Queue Groups ⭐⭐⭐⭐
   - 负载均衡
   - 水平扩展
   - 提高吞吐量

5. JetStream优化 ⭐⭐⭐⭐
   - 合理设置MaxDeliver
   - 使用AckWait
   - 配置MaxAckPending

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 错误处理

```go
// 重连机制
nc, err := nats.Connect(url,
    nats.MaxReconnects(-1),
    nats.ReconnectWait(2*time.Second),
    nats.DisconnectErrHandler(func(nc *nats.Conn, err error) {
        log.Printf("Disconnected: %v", err)
    }),
    nats.ReconnectHandler(func(nc *nats.Conn) {
        log.Printf("Reconnected to %v", nc.ConnectedUrl())
    }),
)

// JetStream错误处理
_, err = js.Publish(subject, data)
if err != nil {
    if errors.Is(err, nats.ErrTimeout) {
        // 超时重试
        return retry(ctx, func() error {
            return js.Publish(subject, data)
        })
    }
    if errors.Is(err, nats.ErrNoStreamResponse) {
        // Stream不存在
        return createStreamAndRetry()
    }
}
```

### 9.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键指标监控:

1. 连接状态
   - 连接数
   - 重连次数
   - 断连时长

2. 消息指标
   - 发布/接收速率
   - 消息延迟
   - 待处理消息数

3. JetStream
   - Stream大小
   - Consumer lag
   - 重投递次数

4. 错误率
   - 发布失败率
   - 消费失败率
   - 超时错误

告警规则:
- 连接断开 > 1分钟
- 消息延迟 > 5秒
- 待处理消息 > 10000
- 错误率 > 1%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 10. 完整示例

### 10.1 请求-响应模式

```go
// Request-Reply模式with tracing
func RequestReplyWithTracing(
    ctx context.Context,
    nc *nats.Conn,
    subject string,
    data []byte,
) ([]byte, error) {
    tracer := otel.Tracer("nats-request-reply")

    ctx, span := tracer.Start(ctx, "nats.request",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("nats"),
            semconv.MessagingDestinationNameKey.String(subject),
            semconv.MessagingOperationKey.String("request"),
        ),
    )
    defer span.End()

    // 创建消息with trace context
    msg := MessageWithContext{Data: make(map[string]interface{})}
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
    msg.TraceParent = carrier["traceparent"]
    msg.TraceState = carrier["tracestate"]

    payload, _ := json.Marshal(msg)

    // 发送请求
    resp, err := nc.Request(subject, payload, 5*time.Second)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "request failed")
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("messaging.response.body.size", len(resp.Data)),
    )
    span.SetStatus(codes.Ok, "success")

    return resp.Data, nil
}

// Reply handler
func ReplyHandlerWithTracing(
    nc *nats.Conn,
    subject string,
    handler func(context.Context, map[string]interface{}) (interface{}, error),
) error {
    tracer := otel.Tracer("nats-reply-handler")

    _, err := nc.Subscribe(subject, func(m *nats.Msg) {
        // 解析请求
        var msg MessageWithContext
        json.Unmarshal(m.Data, &msg)

        // 提取context
        carrier := propagation.MapCarrier{
            "traceparent": msg.TraceParent,
            "tracestate":  msg.TraceState,
        }
        ctx := otel.GetTextMapPropagator().Extract(
            context.Background(), carrier,
        )

        // 创建span
        ctx, span := tracer.Start(ctx, "nats.reply",
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("nats"),
                semconv.MessagingDestinationNameKey.String(m.Subject),
                semconv.MessagingOperationKey.String("reply"),
                attribute.String("messaging.nats.reply_to", m.Reply),
            ),
        )
        defer span.End()

        // 处理请求
        result, err := handler(ctx, msg.Data)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            m.Respond([]byte("error"))
            return
        }

        // 发送响应
        response, _ := json.Marshal(result)
        m.Respond(response)

        span.SetStatus(codes.Ok, "replied")
    })

    return err
}
```

### 10.2 Queue Group模式

```go
// Worker Pool with Queue Group
func StartWorkerPool(
    nc *nats.Conn,
    subject string,
    queueGroup string,
    numWorkers int,
    handler func(context.Context, []byte) error,
) error {
    tracer := otel.Tracer("nats-worker")

    for i := 0; i < numWorkers; i++ {
        workerID := i

        _, err := nc.QueueSubscribe(subject, queueGroup, func(m *nats.Msg) {
            // 提取context (假设使用JetStream with headers)
            ctx := otel.GetTextMapPropagator().Extract(
                context.Background(),
                propagation.HeaderCarrier(m.Header),
            )

            ctx, span := tracer.Start(ctx, "nats.worker.process",
                trace.WithSpanKind(trace.SpanKindConsumer),
                trace.WithAttributes(
                    semconv.MessagingSystemKey.String("nats"),
                    semconv.MessagingDestinationNameKey.String(m.Subject),
                    semconv.MessagingOperationKey.String("receive"),
                    attribute.String("messaging.nats.queue_group", queueGroup),
                    attribute.Int("messaging.nats.worker.id", workerID),
                    attribute.Int("messaging.message.body.size", len(m.Data)),
                ),
            )

            // 处理消息
            if err := handler(ctx, m.Data); err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, "processing failed")
            } else {
                span.SetStatus(codes.Ok, "processed")
            }

            span.End()
        })

        if err != nil {
            return err
        }
    }

    return nil
}
```

---

**文档状态**: ✅ 完成
**NATS版本**: v2.10.0+
**JetStream**: v2.2.0+
**适用场景**: 微服务、事件驱动、实时通信

**关键特性**:

- ✅ Core NATS追踪 (JSON封装传播)
- ✅ JetStream追踪 (原生Headers支持)
- ✅ Request-Reply模式
- ✅ Queue Groups负载均衡
- ✅ 完整Metrics定义
- ✅ Go/Python示例
