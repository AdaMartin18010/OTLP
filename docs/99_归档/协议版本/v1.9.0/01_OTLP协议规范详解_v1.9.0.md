---
title: OTLP协议规范详解 v1.9.0
description: OpenTelemetry Protocol v1.9.0完整规范解析，包括Protobuf定义、gRPC/HTTP传输、编码细节和实现要求
version: OTLP v1.10.0
category: 核心协议
tags:
  - otlp
  - protocol
  - protobuf
status: published
date: 2026-03-17
---

# OTLP协议规范详解 v1.9.0

> **协议版本**: v1.9.0
> **规范状态**: Stable
> **最后更新**: 2026-03-17

---

## 1. 协议概述

### 1.1 OTLP设计目标

- 传输无关性: 支持gRPC和HTTP/Protobuf
- 向后兼容: 版本升级不影响现有实现
- 高效编码: Protocol Buffers二进制编码
- 流式支持: 支持长连接和流式传输

### 1.2 协议栈

```
应用层: Traces, Metrics, Logs, Profiles
传输层: gRPC(4317), HTTP/Protobuf(4318)
编码层: Protocol Buffers 3
```

---

## 2. Protobuf消息定义

### 2.1 Trace消息

```protobuf
message TracesData {
  repeated ResourceSpans resource_spans = 1;
}

message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  bytes parent_span_id = 4;
  string name = 5;
  SpanKind kind = 6;
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
}
```

---

**最后更新**: 2026-03-17
**状态**: Published
