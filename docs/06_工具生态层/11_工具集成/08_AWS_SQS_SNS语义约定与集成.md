---
title: AWS SQS/SNS语义约定详解
description: AWS SQS/SNS语义约定详解 详细指南和最佳实践
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
# AWS SQS/SNS语义约定详解

> **云原生消息服务**: AWS SQS与SNS Tracing与Metrics完整规范
> **最后更新**: 2025年10月8日

---

## 目录

- [AWS SQS/SNS语义约定详解](#aws-sqssns语义约定详解)
  - [目录](#目录)
  - [1. AWS消息服务概述](#1-aws消息服务概述)
    - [1.1 SQS vs SNS](#11-sqs-vs-sns)
    - [1.2 架构对比](#12-架构对比)
  - [2. SQS通用属性](#2-sqs通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 SQS特有属性](#22-sqs特有属性)
  - [3. SNS通用属性](#3-sns通用属性)
    - [3.1 必需属性](#31-必需属性)
    - [3.2 SNS特有属性](#32-sns特有属性)
  - [4. SQS Producer属性](#4-sqs-producer属性)
    - [4.1 发送消息](#41-发送消息)
    - [4.2 批量发送](#42-批量发送)
  - [5. SQS Consumer属性](#5-sqs-consumer属性)
    - [5.1 接收消息](#51-接收消息)
    - [5.2 长轮询](#52-长轮询)
  - [6. SNS Publisher属性](#6-sns-publisher属性)
    - [6.1 发布消息](#61-发布消息)
    - [6.2 消息属性](#62-消息属性)
  - [7. Context传播](#7-context传播)
    - [7.1 SQS消息属性](#71-sqs消息属性)
    - [7.2 SNS消息属性](#72-sns消息属性)
  - [8. Go实现示例](#8-go实现示例)
    - [8.1 SQS Producer](#81-sqs-producer)
    - [8.2 SQS Consumer](#82-sqs-consumer)
    - [8.3 SNS Publisher](#83-sns-publisher)
  - [9. Python实现示例](#9-python实现示例)
    - [9.1 SQS with Boto3](#91-sqs-with-boto3)
    - [9.2 SNS with Boto3](#92-sns-with-boto3)
  - [10. Metrics定义](#10-metrics定义)
    - [10.1 SQS Metrics](#101-sqs-metrics)
    - [10.2 SNS Metrics](#102-sns-metrics)
  - [11. 高级模式](#11-高级模式)
    - [11.1 SNS + SQS Fanout](#111-sns--sqs-fanout)
    - [11.2 SQS DLQ](#112-sqs-dlq)
    - [11.3 FIFO Queue](#113-fifo-queue)
  - [12. 最佳实践](#12-最佳实践)
    - [12.1 性能优化](#121-性能优化)
    - [12.2 成本优化](#122-成本优化)
    - [12.3 监控建议](#123-监控建议)

---

## 1. AWS消息服务概述

### 1.1 SQS vs SNS

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AWS SQS vs SNS:

┌─────────────────────────────────────────────────────────┐
│                        SQS                              │
│              (Simple Queue Service)                     │
│                                                         │
│  模式:      点对点 (Queue)                              │
│  Pull/Push: Pull-based (Consumer主动拉取)              │
│  持久化:    Yes (最长14天)                              │
│  顺序:      FIFO可保证顺序                              │
│  重复消费:  No (At-least-once)                          │
│  用途:      异步处理、任务队列、削峰填谷                │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│                        SNS                              │
│           (Simple Notification Service)                 │
│                                                         │
│  模式:      发布订阅 (Pub/Sub)                          │
│  Pull/Push: Push-based (主动推送到订阅者)              │
│  持久化:    No (即时投递)                               │
│  顺序:      不保证                                      │
│  扇出:      1对多 (多个订阅者)                          │
│  用途:      事件通知、广播消息、扇出架构                │
└─────────────────────────────────────────────────────────┘

常见组合:
SNS → SQS → Consumer (扇出 + 持久化)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 架构对比

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS架构:

Producer 1 ──┐
Producer 2 ──┤──► [SQS Queue] ──► Consumer 1
Producer 3 ──┘                └─► Consumer 2

特点:
- Consumer竞争消费
- 每条消息只被消费1次
- 支持VisibilityTimeout

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SNS架构:

                      ┌──► Subscriber 1 (Email)
                      │
Publisher ──► [SNS Topic] ──► Subscriber 2 (Lambda)
                      │
                      └──► Subscriber 3 (SQS)

特点:
- 所有订阅者都收到消息
- 支持多种协议 (HTTP, Email, Lambda, SQS, SMS)
- 即时推送

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. SQS通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"aws_sqs"` |
| `messaging.destination.name` | string | 队列名称 | `"my-queue"` |
| `messaging.operation` | string | 操作类型 | `"publish"`, `"receive"` |
| `messaging.aws.sqs.queue_url` | string | 队列URL | `"https://sqs.us-east-1.amazonaws.com/123456789012/my-queue"` |

### 2.2 SQS特有属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.aws.sqs.message_id` | string | 消息ID | `"1234-5678-abcd"` |
| `messaging.aws.sqs.receipt_handle` | string | 接收句柄 | `"AQEBw..."` |
| `messaging.aws.sqs.approximate_receive_count` | int | 接收次数 | `1` |
| `messaging.aws.sqs.queue_type` | string | 队列类型 | `"standard"`, `"fifo"` |
| `messaging.aws.sqs.message_group_id` | string | 消息组ID (FIFO) | `"group-1"` |
| `messaging.aws.sqs.message_deduplication_id` | string | 去重ID (FIFO) | `"dedup-1"` |
| `cloud.region` | string | AWS区域 | `"us-east-1"` |
| `cloud.account.id` | string | AWS账号ID | `"123456789012"` |

---

## 3. SNS通用属性

### 3.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"aws_sns"` |
| `messaging.destination.name` | string | Topic名称 | `"my-topic"` |
| `messaging.operation` | string | 操作类型 | `"publish"` |
| `messaging.aws.sns.topic_arn` | string | Topic ARN | `"arn:aws:sns:us-east-1:123456789012:my-topic"` |

### 3.2 SNS特有属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.aws.sns.message_id` | string | 消息ID | `"abcd-1234"` |
| `messaging.aws.sns.target_arn` | string | 目标ARN (Endpoint发布) | `"arn:aws:sns:us-east-1:123456789012:endpoint/..."` |
| `messaging.aws.sns.phone_number` | string | 手机号 (SMS) | `"+1234567890"` |
| `messaging.aws.sns.subscription_protocol` | string | 订阅协议 | `"sqs"`, `"lambda"`, `"email"`, `"http"`, `"https"` |
| `cloud.region` | string | AWS区域 | `"us-east-1"` |

---

## 4. SQS Producer属性

### 4.1 发送消息

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS SendMessage属性:

必需:
✅ messaging.system = "aws_sqs"
✅ messaging.destination.name (队列名称)
✅ messaging.operation = "publish"
✅ messaging.aws.sqs.queue_url

推荐:
📋 messaging.aws.sqs.message_id (发送后)
📋 messaging.message.body.size
📋 cloud.region
📋 cloud.account.id

FIFO额外:
📋 messaging.aws.sqs.message_group_id
📋 messaging.aws.sqs.message_deduplication_id

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.2 批量发送

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.operation` | string | 操作类型 | `"publish_batch"` |
| `messaging.batch.message_count` | int | 批量消息数 | `10` |
| `messaging.aws.sqs.batch.success_count` | int | 成功数 | `9` |
| `messaging.aws.sqs.batch.failed_count` | int | 失败数 | `1` |

---

## 5. SQS Consumer属性

### 5.1 接收消息

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS ReceiveMessage属性:

必需:
✅ messaging.system = "aws_sqs"
✅ messaging.destination.name
✅ messaging.operation = "receive"
✅ messaging.aws.sqs.queue_url

推荐:
📋 messaging.aws.sqs.message_id
📋 messaging.aws.sqs.receipt_handle
📋 messaging.aws.sqs.approximate_receive_count
📋 messaging.message.body.size

处理后:
📋 messaging.operation = "delete" (删除消息)
📋 messaging.operation = "change_visibility" (延长超时)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 长轮询

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.aws.sqs.wait_time_seconds` | int | 等待时间 | `20` |
| `messaging.aws.sqs.max_number_of_messages` | int | 最大消息数 | `10` |
| `messaging.aws.sqs.visibility_timeout` | int | 可见性超时(秒) | `30` |

---

## 6. SNS Publisher属性

### 6.1 发布消息

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SNS Publish属性:

必需:
✅ messaging.system = "aws_sns"
✅ messaging.destination.name (Topic名称)
✅ messaging.operation = "publish"
✅ messaging.aws.sns.topic_arn

推荐:
📋 messaging.aws.sns.message_id (发布后)
📋 messaging.message.body.size
📋 cloud.region

目标发布:
📋 messaging.aws.sns.target_arn (Endpoint/Phone)
📋 messaging.aws.sns.phone_number (SMS)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 6.2 消息属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.aws.sns.subject` | string | 消息主题 | `"Order Created"` |
| `messaging.aws.sns.message_structure` | string | 消息结构 | `"json"` |
| `messaging.aws.sns.filter_policy` | string | 过滤策略 | `"{\"event\": [\"order\"]}"` |

---

## 7. Context传播

### 7.1 SQS消息属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS消息属性 (Message Attributes):

SQS支持自定义消息属性 (最多10个):

MessageAttributes: {
  "traceparent": {
    DataType: "String",
    StringValue: "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
  },
  "tracestate": {
    DataType: "String",
    StringValue: "vendor=value"
  }
}

限制:
- 最多10个属性
- 名称最长256字符
- 值最长256KB
- 支持String/Number/Binary

注意:
⚠️  消息体不变，属性独立存储

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 7.2 SNS消息属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SNS消息属性 (Message Attributes):

SNS同样支持消息属性:

MessageAttributes: {
  "traceparent": {
    DataType: "String",
    StringValue: "00-..."
  },
  "event_type": {
    DataType: "String",
    StringValue: "order_created"
  }
}

过滤订阅:
SNS支持基于属性的过滤策略

FilterPolicy: {
  "event_type": ["order_created", "order_updated"]
}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 8. Go实现示例

### 8.1 SQS Producer

```go
package main

import (
    "context"

    "github.com/aws/aws-sdk-go-v2/aws"
    "github.com/aws/aws-sdk-go-v2/service/sqs"
    "github.com/aws/aws-sdk-go-v2/service/sqs/types"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func SendMessageWithTracing(
    ctx context.Context,
    sqsClient *sqs.Client,
    queueURL string,
    message string,
) error {
    tracer := otel.Tracer("sqs-producer")

    // 创建Producer Span
    ctx, span := tracer.Start(ctx, "sqs.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("aws_sqs"),
            semconv.MessagingDestinationNameKey.String(
                getQueueName(queueURL)),
            semconv.MessagingOperationKey.String("publish"),
            attribute.String("messaging.aws.sqs.queue_url", queueURL),
            attribute.Int("messaging.message.body.size", len(message)),
        ),
    )
    defer span.End()

    // 创建消息属性
    messageAttributes := make(map[string]types.MessageAttributeValue)

    // 注入Trace Context
    carrier := NewSQSAttributeCarrier(messageAttributes)
    otel.GetTextMapPropagator().Inject(ctx, carrier)

    // 发送消息
    output, err := sqsClient.SendMessage(ctx, &sqs.SendMessageInput{
        QueueUrl:          aws.String(queueURL),
        MessageBody:       aws.String(message),
        MessageAttributes: messageAttributes,
    })

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "send failed")
        return err
    }

    // 记录消息ID
    span.SetAttributes(
        attribute.String("messaging.aws.sqs.message_id",
            *output.MessageId),
    )

    span.SetStatus(codes.Ok, "sent")
    return nil
}

// SQS Message Attribute Carrier
type SQSAttributeCarrier struct {
    attributes map[string]types.MessageAttributeValue
}

func NewSQSAttributeCarrier(
    attrs map[string]types.MessageAttributeValue,
) *SQSAttributeCarrier {
    return &SQSAttributeCarrier{attributes: attrs}
}

func (c *SQSAttributeCarrier) Get(key string) string {
    if attr, ok := c.attributes[key]; ok {
        if attr.StringValue != nil {
            return *attr.StringValue
        }
    }
    return ""
}

func (c *SQSAttributeCarrier) Set(key, value string) {
    c.attributes[key] = types.MessageAttributeValue{
        DataType:    aws.String("String"),
        StringValue: aws.String(value),
    }
}

func (c *SQSAttributeCarrier) Keys() []string {
    keys := make([]string, 0, len(c.attributes))
    for k := range c.attributes {
        keys = append(keys, k)
    }
    return keys
}

// 批量发送
func SendMessageBatchWithTracing(
    ctx context.Context,
    sqsClient *sqs.Client,
    queueURL string,
    messages []string,
) error {
    tracer := otel.Tracer("sqs-producer")

    ctx, span := tracer.Start(ctx, "sqs.publish_batch",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("aws_sqs"),
            attribute.String("messaging.aws.sqs.queue_url", queueURL),
            attribute.Int("messaging.batch.message_count", len(messages)),
        ),
    )
    defer span.End()

    // 构建批量消息
    entries := make([]types.SendMessageBatchRequestEntry, len(messages))
    for i, msg := range messages {
        messageAttributes := make(map[string]types.MessageAttributeValue)
        carrier := NewSQSAttributeCarrier(messageAttributes)
        otel.GetTextMapPropagator().Inject(ctx, carrier)

        entries[i] = types.SendMessageBatchRequestEntry{
            Id:                aws.String(fmt.Sprintf("msg-%d", i)),
            MessageBody:       aws.String(msg),
            MessageAttributes: messageAttributes,
        }
    }

    // 批量发送
    output, err := sqsClient.SendMessageBatch(ctx,
        &sqs.SendMessageBatchInput{
            QueueUrl: aws.String(queueURL),
            Entries:  entries,
        })

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "batch send failed")
        return err
    }

    // 记录成功/失败数量
    span.SetAttributes(
        attribute.Int("messaging.aws.sqs.batch.success_count",
            len(output.Successful)),
        attribute.Int("messaging.aws.sqs.batch.failed_count",
            len(output.Failed)),
    )

    span.SetStatus(codes.Ok, "sent")
    return nil
}
```

### 8.2 SQS Consumer

```go
func ReceiveMessageWithTracing(
    ctx context.Context,
    sqsClient *sqs.Client,
    queueURL string,
    handler func(context.Context, string) error,
) error {
    tracer := otel.Tracer("sqs-consumer")

    for {
        // 接收消息 (长轮询)
        output, err := sqsClient.ReceiveMessage(ctx,
            &sqs.ReceiveMessageInput{
                QueueUrl:            aws.String(queueURL),
                MaxNumberOfMessages: 10,
                WaitTimeSeconds:     20, // 长轮询
                VisibilityTimeout:   30,
                MessageAttributeNames: []string{"All"},
            })

        if err != nil {
            return err
        }

        // 处理每条消息
        for _, msg := range output.Messages {
            // 提取Trace Context
            carrier := NewSQSAttributeCarrier(msg.MessageAttributes)
            msgCtx := otel.GetTextMapPropagator().Extract(ctx, carrier)

            // 创建Consumer Span
            msgCtx, span := tracer.Start(msgCtx, "sqs.receive",
                trace.WithSpanKind(trace.SpanKindConsumer),
                trace.WithAttributes(
                    semconv.MessagingSystemKey.String("aws_sqs"),
                    semconv.MessagingDestinationNameKey.String(
                        getQueueName(queueURL)),
                    semconv.MessagingOperationKey.String("receive"),
                    attribute.String("messaging.aws.sqs.message_id",
                        *msg.MessageId),
                    attribute.String("messaging.aws.sqs.receipt_handle",
                        *msg.ReceiptHandle),
                    attribute.Int("messaging.message.body.size",
                        len(*msg.Body)),
                ),
            )

            // 处理消息
            err := handler(msgCtx, *msg.Body)

            if err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, "handler failed")

                // 可以选择删除消息或让它重新可见
                // (这里选择让它自动重新可见)
            } else {
                span.SetStatus(codes.Ok, "processed")

                // 删除消息
                _, delErr := sqsClient.DeleteMessage(msgCtx,
                    &sqs.DeleteMessageInput{
                        QueueUrl:      aws.String(queueURL),
                        ReceiptHandle: msg.ReceiptHandle,
                    })

                if delErr != nil {
                    span.RecordError(delErr)
                }
            }

            span.End()
        }
    }
}
```

### 8.3 SNS Publisher

```go
func PublishWithTracing(
    ctx context.Context,
    snsClient *sns.Client,
    topicARN string,
    message string,
) error {
    tracer := otel.Tracer("sns-publisher")

    // 创建Publisher Span
    ctx, span := tracer.Start(ctx, "sns.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("aws_sns"),
            semconv.MessagingDestinationNameKey.String(
                getTopicName(topicARN)),
            semconv.MessagingOperationKey.String("publish"),
            attribute.String("messaging.aws.sns.topic_arn", topicARN),
            attribute.Int("messaging.message.body.size", len(message)),
        ),
    )
    defer span.End()

    // 创建消息属性
    messageAttributes := make(map[string]types.MessageAttributeValue)

    // 注入Trace Context
    carrier := NewSNSAttributeCarrier(messageAttributes)
    otel.GetTextMapPropagator().Inject(ctx, carrier)

    // 发布消息
    output, err := snsClient.Publish(ctx, &sns.PublishInput{
        TopicArn:          aws.String(topicARN),
        Message:           aws.String(message),
        MessageAttributes: messageAttributes,
    })

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }

    // 记录消息ID
    span.SetAttributes(
        attribute.String("messaging.aws.sns.message_id",
            *output.MessageId),
    )

    span.SetStatus(codes.Ok, "published")
    return nil
}

// SNS Message Attribute Carrier (类似SQS)
type SNSAttributeCarrier struct {
    attributes map[string]types.MessageAttributeValue
}

// 实现同SQS
```

---

## 9. Python实现示例

### 9.1 SQS with Boto3

```python
import boto3
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

sqs = boto3.client('sqs')
tracer = trace.get_tracer(__name__)

def send_message_with_tracing(queue_url: str, message: str):
    """发送SQS消息with tracing"""
    with tracer.start_as_current_span(
        "sqs.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "aws_sqs",
            SpanAttributes.MESSAGING_DESTINATION_NAME: get_queue_name(queue_url),
            SpanAttributes.MESSAGING_OPERATION: "publish",
            "messaging.aws.sqs.queue_url": queue_url,
            "messaging.message.body.size": len(message),
        }
    ) as span:
        # 注入trace context
        message_attributes = {}
        propagate.inject(message_attributes,
                        setter=lambda d, k, v: d.update({
                            k: {'StringValue': v, 'DataType': 'String'}
                        }))

        try:
            # 发送消息
            response = sqs.send_message(
                QueueUrl=queue_url,
                MessageBody=message,
                MessageAttributes=message_attributes
            )

            # 记录消息ID
            span.set_attribute("messaging.aws.sqs.message_id",
                             response['MessageId'])
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def receive_message_with_tracing(queue_url: str, handler):
    """接收SQS消息with tracing"""
    while True:
        # 长轮询接收
        response = sqs.receive_message(
            QueueUrl=queue_url,
            MaxNumberOfMessages=10,
            WaitTimeSeconds=20,
            MessageAttributeNames=['All']
        )

        for msg in response.get('Messages', []):
            # 提取trace context
            message_attributes = msg.get('MessageAttributes', {})
            ctx = propagate.extract(message_attributes,
                                   getter=lambda d, k: d.get(k, {}).get('StringValue', ''))

            # 创建span
            with tracer.start_as_current_span(
                "sqs.receive",
                context=ctx,
                kind=SpanKind.CONSUMER,
                attributes={
                    SpanAttributes.MESSAGING_SYSTEM: "aws_sqs",
                    SpanAttributes.MESSAGING_DESTINATION_NAME: get_queue_name(queue_url),
                    SpanAttributes.MESSAGING_OPERATION: "receive",
                    "messaging.aws.sqs.message_id": msg['MessageId'],
                    "messaging.aws.sqs.receipt_handle": msg['ReceiptHandle'],
                }
            ) as span:
                try:
                    # 处理消息
                    handler(msg['Body'])

                    # 删除消息
                    sqs.delete_message(
                        QueueUrl=queue_url,
                        ReceiptHandle=msg['ReceiptHandle']
                    )
                    span.set_status(Status(StatusCode.OK))

                except Exception as e:
                    span.record_exception(e)
                    span.set_status(Status(StatusCode.ERROR))
```

### 9.2 SNS with Boto3

```python
sns = boto3.client('sns')

def publish_with_tracing(topic_arn: str, message: str):
    """发布SNS消息with tracing"""
    with tracer.start_as_current_span(
        "sns.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "aws_sns",
            SpanAttributes.MESSAGING_DESTINATION_NAME: get_topic_name(topic_arn),
            SpanAttributes.MESSAGING_OPERATION: "publish",
            "messaging.aws.sns.topic_arn": topic_arn,
        }
    ) as span:
        # 注入trace context
        message_attributes = {}
        propagate.inject(message_attributes,
                        setter=lambda d, k, v: d.update({
                            k: {'StringValue': v, 'DataType': 'String'}
                        }))

        try:
            # 发布消息
            response = sns.publish(
                TopicArn=topic_arn,
                Message=message,
                MessageAttributes=message_attributes
            )

            span.set_attribute("messaging.aws.sns.message_id",
                             response['MessageId'])
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

---

## 10. Metrics定义

### 10.1 SQS Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.aws.sqs.send.duration` | Histogram | ms | 发送延迟 |
| `messaging.aws.sqs.send.messages` | Counter | messages | 发送消息数 |
| `messaging.aws.sqs.send.errors` | Counter | errors | 发送错误数 |
| `messaging.aws.sqs.receive.duration` | Histogram | ms | 接收延迟 |
| `messaging.aws.sqs.receive.messages` | Counter | messages | 接收消息数 |
| `messaging.aws.sqs.delete.messages` | Counter | messages | 删除消息数 |
| `messaging.aws.sqs.visible.messages` | Gauge | messages | 可见消息数 |
| `messaging.aws.sqs.inflight.messages` | Gauge | messages | 处理中消息数 |
| `messaging.aws.sqs.delayed.messages` | Gauge | messages | 延迟消息数 |

### 10.2 SNS Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.aws.sns.publish.duration` | Histogram | ms | 发布延迟 |
| `messaging.aws.sns.publish.messages` | Counter | messages | 发布消息数 |
| `messaging.aws.sns.publish.errors` | Counter | errors | 发布错误数 |
| `messaging.aws.sns.delivery.success` | Counter | deliveries | 投递成功数 |
| `messaging.aws.sns.delivery.failed` | Counter | deliveries | 投递失败数 |

---

## 11. 高级模式

### 11.1 SNS + SQS Fanout

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SNS + SQS扇出模式:

                        ┌──► SQS Queue 1 ──► Service A
                        │
Publisher ──► SNS Topic ├──► SQS Queue 2 ──► Service B
                        │
                        └──► SQS Queue 3 ──► Service C

优点:
✅ 解耦服务
✅ 独立消费速度
✅ 持久化保证
✅ 重试机制

追踪:
1. Publisher发布到SNS (Producer Span)
2. SNS推送到SQS (自动传播traceparent)
3. Consumer从SQS接收 (Consumer Span继承)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.2 SQS DLQ

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS死信队列 (DLQ):

           ┌──────────────┐
           │  Main Queue  │
           └──────┬───────┘
                  │
          处理失败 (超过最大接收次数)
                  │
                  ▼
           ┌──────────────┐
           │  DLQ Queue   │
           └──────────────┘

配置:
RedrivePolicy: {
  "deadLetterTargetArn": "arn:aws:sqs:...:dlq",
  "maxReceiveCount": 3
}

追踪:
span.SetAttributes(
    attribute.String("messaging.aws.sqs.dead_letter_queue", "true"),
    attribute.Int("messaging.aws.sqs.approximate_receive_count", count),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.3 FIFO Queue

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS FIFO队列:

Queue名称: my-queue.fifo (必须以.fifo结尾)

特性:
✅ 严格顺序
✅ 精确一次处理
✅ 消息去重
✅ 消息分组

限制:
⚠️  300 TPS (标准模式)
⚠️  3000 TPS (批处理模式)

追踪属性:
span.SetAttributes(
    attribute.String("messaging.aws.sqs.queue_type", "fifo"),
    attribute.String("messaging.aws.sqs.message_group_id", "group-1"),
    attribute.String("messaging.aws.sqs.message_deduplication_id", "dedup-1"),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 12. 最佳实践

### 12.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化建议:

1. SQS长轮询 ⭐⭐⭐⭐⭐
   WaitTimeSeconds: 20 (减少空轮询)

2. 批量发送/接收 ⭐⭐⭐⭐⭐
   SendMessageBatch (最多10条)
   ReceiveMessage (MaxNumberOfMessages: 10)

3. VisibilityTimeout调优 ⭐⭐⭐⭐
   根据处理时间设置 (避免重复处理)

4. 消息大小优化 ⭐⭐⭐⭐
   消息体 < 256KB
   大文件用S3 + 引用

5. 并发Consumer ⭐⭐⭐⭐⭐
   多个Consumer并发处理

6. 连接复用 ⭐⭐⭐⭐
   复用SQS/SNS Client

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 12.2 成本优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

成本优化:

1. 长轮询 vs 短轮询
   长轮询: 减少请求次数，降低成本

2. 批量操作
   批量发送/接收: 减少API调用

3. 消息保留时间
   根据需要设置 (默认4天，最长14天)

4. DLQ策略
   及时处理DLQ消息，避免长期保留

5. SNS过滤策略
   避免不必要的投递

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 12.3 监控建议

```go
// 关键监控指标
监控指标:

SQS:
- ApproximateNumberOfMessages (队列深度)
- ApproximateAgeOfOldestMessage (最老消息年龄)
- NumberOfMessagesSent
- NumberOfMessagesReceived
- NumberOfMessagesDeleted

SNS:
- NumberOfMessagesPublished
- NumberOfNotificationsDelivered
- NumberOfNotificationsFailed

告警规则:
- 队列深度 > 10000
- 最老消息 > 1小时
- 投递失败率 > 1%
- DLQ消息数 > 0
```

---

**文档状态**: ✅ 完成
**AWS SDK版本**: v2 (Go) / boto3 (Python)
**适用场景**: AWS云原生架构、微服务解耦、事件驱动

**关键特性**:

- ✅ SQS标准/FIFO队列
- ✅ SNS Pub/Sub模式
- ✅ SNS+SQS扇出架构
- ✅ DLQ死信队列
- ✅ 消息属性传播
- ✅ Go/Python完整示例
- ✅ 成本优化策略

