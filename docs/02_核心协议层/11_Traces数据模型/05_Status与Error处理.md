---
title: Span Status与Error处理规范
description: OTLP Span状态码定义、错误处理机制、异常记录最佳实践与实现指南
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 数据模型
tags:
  - span-status
  - error-handling
  - exception
  - status-code
  - otlp
status: published
---

# Span Status与Error处理规范

> **版本**: OTLP v1.10.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约20分钟

---

## 1. Span Status概述

### 1.1 什么是Span Status

Span Status表示Span执行的结果状态，用于快速判断操作是否成功：

```
┌─────────────────────────────────────────────────────────────────┐
│                    Span Status模型                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Status (必需字段)                                               │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ Code    │ Description                                   │   │
│  ├─────────┼───────────────────────────────────────────────┤   │
│  │ UNSET   │ 默认值，状态未设置                            │   │
│  │ OK      │ 操作成功完成                                  │   │
│  │ ERROR   │ 操作失败，包含错误描述                        │   │
│  └─────────┴───────────────────────────────────────────────┘   │
│                                                                 │
│  Description (可选字段)                                          │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ 当Code=ERROR时，提供人类可读的错误描述                    │   │
│  │ 示例: "connection refused", "timeout after 30s"          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Status Code定义

| Code | 数值 | 含义 | 使用场景 |
|------|------|------|----------|
| **UNSET** | 0 | 未设置 | Span创建时的默认值 |
| **OK** | 1 | 成功 | 操作成功完成 |
| **ERROR** | 2 | 错误 | 操作失败 |

---

## 2. Status使用规范

### 2.1 何时设置Status

```go
// 场景1: HTTP客户端调用
func HTTPClientCall(ctx context.Context, url string) error {
    ctx, span := tracer.Start(ctx, "HTTP GET")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.url", url),
        attribute.String("http.method", "GET"),
    )

    resp, err := http.Get(url)
    if err != nil {
        // 网络错误，设置ERROR状态
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return err
    }
    defer resp.Body.Close()

    span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))

    if resp.StatusCode >= 400 {
        // HTTP错误，设置ERROR状态
        span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", resp.StatusCode))
        return fmt.Errorf("http error: %d", resp.StatusCode)
    }

    // 成功，设置OK状态
    span.SetStatus(codes.Ok, "")
    return nil
}

// 场景2: 数据库操作
func DatabaseQuery(ctx context.Context, query string) error {
    ctx, span := tracer.Start(ctx, "DB Query")
    defer span.End()

    span.SetAttributes(
        attribute.String("db.system", "mysql"),
        attribute.String("db.statement", query),
    )

    rows, err := db.QueryContext(ctx, query)
    if err != nil {
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return err
    }
    defer rows.Close()

    span.SetStatus(codes.Ok, "")
    return nil
}

// 场景3: 异步处理
func ProcessMessage(ctx context.Context, msg Message) error {
    ctx, span := tracer.Start(ctx, "Process Message")
    defer span.End()

    span.SetAttributes(
        attribute.String("messaging.system", "kafka"),
        attribute.String("messaging.destination", msg.Topic),
    )

    if err := validateMessage(msg); err != nil {
        span.SetStatus(codes.Error, "validation failed")
        span.RecordError(err)
        return err
    }

    if err := processBusinessLogic(msg); err != nil {
        span.SetStatus(codes.Error, "processing failed")
        span.RecordError(err)
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}
```

### 2.2 Status设置原则

```markdown
## 应该设置Status=ERROR的情况:

1. 网络错误
   - 连接超时
   - 连接被拒绝
   - DNS解析失败

2. HTTP错误
   - 4xx客户端错误
   - 5xx服务器错误

3. 业务错误
   - 数据库约束违反
   - 验证失败
   - 资源不足

4. 超时
   - 操作超过截止时间
   - 上下文取消

## 不应该设置Status=ERROR的情况:

1. 预期内的结果
   - HTTP 404 (资源不存在可能是正常情况)
   - 验证失败 (如果这是正常流程)

2. 重试前的失败
   - 如果会重试，第一次失败不标记为ERROR
   - 只有最终失败才标记

3. 取消操作
   - 用户主动取消
   - 但应该记录取消原因
```

---

## 3. Error记录机制

### 3.1 RecordError vs SetStatus

```go
// RecordError: 记录详细的异常信息
// SetStatus: 设置Span的整体状态

// 最佳实践: 两者配合使用
func Example(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "example")
    defer span.End()

    err := doSomething()
    if err != nil {
        // 记录错误详情
        span.RecordError(err,
            trace.WithAttributes(
                attribute.String("error.type", "ValidationError"),
                attribute.String("error.detail", "invalid input format"),
            ),
        )

        // 设置Span状态
        span.SetStatus(codes.Error, err.Error())

        return err
    }

    return nil
}
```

### 3.2 异常属性规范

```yaml
# 标准错误属性

exception.type:
  类型: string
  说明: 异常类型，完全限定类名
  示例: "java.net.ConnectException", "TypeError"

exception.message:
  类型: string
  说明: 异常消息
  示例: "Connection refused", "Cannot read property of undefined"

exception.stacktrace:
  类型: string
  说明: 异常堆栈跟踪
  示例: |
    java.net.ConnectException: Connection refused
        at java.net.PlainSocketImpl.socketConnect(Native Method)
        at java.net.AbstractPlainSocketImpl.doConnect(AbstractPlainSocketImpl.java:476)

exception.escaped:
  类型: boolean
  说明: 异常是否逃逸到调用方
  示例: true (如果异常被抛出), false (如果异常被捕获处理)
```

### 3.3 不同语言的异常记录

```go
// Go语言
import "go.opentelemetry.io/otel/codes"

func handleError(ctx context.Context, err error) {
    span := trace.SpanFromContext(ctx)

    // 记录错误
    span.RecordError(err)

    // 设置状态
    span.SetStatus(codes.Error, err.Error())

    // 添加错误属性
    span.SetAttributes(
        attribute.String("error.type", reflect.TypeOf(err).String()),
        attribute.Bool("error.recovered", false),
    )
}
```

```java
// Java语言
import io.opentelemetry.api.trace.StatusCode;

public void handleError(Throwable throwable) {
    Span span = Span.current();

    // 记录异常
    span.recordException(throwable,
        Attributes.builder()
            .put("exception.escaped", true)
            .put("thread.id", Thread.currentThread().getId())
            .build()
    );

    // 设置状态
    span.setStatus(StatusCode.ERROR, throwable.getMessage());
}
```

```python
# Python语言
from opentelemetry.trace import Status, StatusCode

def handle_error(exception):
    current_span = trace.get_current_span()

    # 记录异常
    current_span.record_exception(exception)

    # 设置状态
    current_span.set_status(
        Status(StatusCode.ERROR, description=str(exception))
    )
```

---

## 4. HTTP状态码映射

### 4.1 HTTP客户端Status映射

```yaml
# HTTP客户端Span的Status映射

1xx (Informational):
  Span.Status: UNSET 或 OK
  说明: 继续处理中

2xx (Success):
  Span.Status: OK
  说明: 请求成功

3xx (Redirection):
  Span.Status: UNSET 或 OK
  说明: 重定向，通常是正常行为

4xx (Client Error):
  Span.Status: ERROR
  说明: 客户端错误
  注意: 如果是预期行为(如404表示资源不存在)，可能不需要标记为ERROR

5xx (Server Error):
  Span.Status: ERROR
  说明: 服务器错误
```

### 4.2 实现示例

```go
func MapHTTPStatusToSpanStatus(statusCode int) codes.Code {
    switch {
    case statusCode >= 100 && statusCode < 300:
        return codes.Ok
    case statusCode >= 300 && statusCode < 400:
        return codes.Unset
    case statusCode >= 400 && statusCode < 500:
        // 根据业务场景决定是否标记为ERROR
        if statusCode == 404 || statusCode == 401 || statusCode == 403 {
            // 这些可能是正常业务流程
            return codes.Unset
        }
        return codes.Error
    case statusCode >= 500:
        return codes.Error
    default:
        return codes.Unset
    }
}

// 使用
resp, err := httpClient.Do(req)
if err != nil {
    span.SetStatus(codes.Error, err.Error())
    return
}

span.SetStatus(MapHTTPStatusToSpanStatus(resp.StatusCode), "")
span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))
```

---

## 5. 错误分类与处理

### 5.1 错误类型分类

```
┌─────────────────────────────────────────────────────────────────┐
│                    错误类型分类体系                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 系统错误 (System Errors)                                     │
│     ┌─────────────────────────────────────────────────────────┐│
│     │ • 网络不可达                                              ││
│     │ • DNS解析失败                                             ││
│     │ • 连接超时                                                ││
│     │ • TLS握手失败                                             ││
│     │                                                           ││
│     │ Status: ERROR                                             ││
│     │ 处理: 通常需要重试或告警                                  ││
│     └─────────────────────────────────────────────────────────┘│
│                                                                 │
│  2. 应用错误 (Application Errors)                                │
│     ┌─────────────────────────────────────────────────────────┐│
│     │ • 数据库约束违反                                          ││
│     │ • 业务规则验证失败                                        ││
│     │ • 并发冲突                                                ││
│     │ • 资源耗尽                                                ││
│     │                                                           ││
│     │ Status: ERROR (通常)                                      ││
│     │ 处理: 根据业务逻辑决定                                    ││
│     └─────────────────────────────────────────────────────────┘│
│                                                                 │
│  3. 客户端错误 (Client Errors)                                   │
│     ┌─────────────────────────────────────────────────────────┐│
│     │ • 无效的请求参数                                          ││
│     │ • 缺少必需的字段                                          ││
│     │ • 格式错误                                                ││
│     │ • 认证/授权失败                                           ││
│     │                                                           ││
│     │ Status: ERROR 或 UNSET (取决于是否预期)                   ││
│     │ 处理: 通常是正常业务流程                                  ││
│     └─────────────────────────────────────────────────────────┘│
│                                                                 │
│  4. 超时/取消 (Timeout/Cancellation)                             │
│     ┌─────────────────────────────────────────────────────────┐│
│     │ • 上下文取消                                              ││
│     │ • 截止时间超过                                            ││
│     │ • 用户中断                                                ││
│     │                                                           ││
│     │ Status: ERROR                                             ││
│     │ 处理: 记录原因，可能需要回滚                              ││
│     └─────────────────────────────────────────────────────────┘│
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 错误处理决策树

```
                    ┌─────────────────┐
                    │ 操作是否成功?   │
                    └────────┬────────┘
                             │
              ┌──────────────┴──────────────┐
              │ 是                           │ 否
              ▼                              ▼
        ┌─────────────┐              ┌─────────────────┐
        │ Status = OK │              │ 错误类型是什么? │
        └─────────────┘              └────────┬────────┘
                                              │
                    ┌────────────────────────┼────────────────────────┐
                    │                        │                        │
                    ▼                        ▼                        ▼
            ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
            │ 系统错误    │          │ 业务错误    │          │ 预期错误    │
            │ (网络/DB)   │          │ (验证/约束) │          │ (404/取消)  │
            └──────┬──────┘          └──────┬──────┘          └──────┬──────┘
                   │                        │                        │
                   ▼                        ▼                        ▼
         ┌─────────────────┐      ┌─────────────────┐      ┌─────────────────┐
         │ Status = ERROR  │      │ Status = ERROR  │      │ Status = UNSET  │
         │ 记录详细错误    │      │ 记录业务详情    │      │ 或 ERROR(可选)  │
         │ 触发告警        │      │ 返回错误信息    │      │ 记录上下文      │
         │ 考虑重试        │      │ 不回滚(可选)    │      │ 正常流程        │
         └─────────────────┘      └─────────────────┘      └─────────────────┘
```

---

## 6. 最佳实践

### 6.1 Status设置检查清单

```markdown
## Span结束前检查:

- [ ] 是否调用了SetStatus?
- [ ] Status是否与操作结果一致?
- [ ] ERROR状态是否有描述信息?
- [ ] 是否记录了异常详情(如果是ERROR)?
- [ ] 错误属性是否完整?

## 常见错误:

❌ 忘记设置Status (保持UNSET)
❌ 所有错误都标记为ERROR(包括预期错误)
❌ 只设置Status不记录Error详情
❌ Status描述信息太简略
❌ 不区分错误类型
```

### 6.2 错误采样策略

```go
// 基于错误状态的采样
func ErrorBasedSampler(threshold float64) sdktrace.Sampler {
    return sdktrace.TraceIDRatioBased(threshold)
}

// 错误Span总是采样
type ErrorBasedSampler struct {
    baseSampler sdktrace.Sampler
}

func (s *ErrorBasedSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 如果父Span是ERROR，总是采样
    if p.ParentContext.IsValid() {
        parentSpan := trace.SpanFromContext(p.ParentContext)
        if parentSpan.SpanContext().IsValid() {
            // 检查父Span状态
            // 注意: OpenTelemetry API不直接暴露父Span状态
            // 实际实现可能需要自定义传播
        }
    }

    // 否则使用基础采样率
    return s.baseSampler.ShouldSample(p)
}
```

---

## 7. 参考规范

### 7.1 OTLP Status protobuf定义

```protobuf
// opentelemetry/proto/trace/v1/trace.proto

// Span的冻结状态码
enum StatusCode {
  // 默认状态，状态码未设置
  STATUS_CODE_UNSET = 0;

  // Span已成功完成
  STATUS_CODE_OK = 1;

  // Span包含错误
  STATUS_CODE_ERROR = 2;
}

// Status是Span操作结果的状态
message Status {
  // 状态码
  StatusCode code = 1;

  // 描述，仅当code==ERROR时使用
  string message = 2;
}
```

---

**参考资源**:

- [OpenTelemetry Span Status](https://opentelemetry.io/docs/concepts/signals/traces/#span-status)
- [OTLP Trace Protocol](https://opentelemetry.io/docs/specs/otlp/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
