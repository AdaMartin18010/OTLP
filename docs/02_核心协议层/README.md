---
title: 02_核心协议层
description: OTLP核心协议层 - 协议基础、数据模型、语义约定
category: 核心协议
version: OTLP v1.10.0
spec_version: v1.55.0
semconv_version: v1.40.0
date: 2026-03-17
status: published
---

# 02_核心协议层

> **层定位**: OTLP协议规范的核心定义，包含协议细节、数据模型、语义约定  
> **文档数量**: 50篇  
> **最后更新**: 2026-03-17  

---

## 目录结构

```
02_核心协议层/
├── 01_协议基础/              # 6篇
│   ├── 01_协议概述.md
│   ├── 02_传输层_gRPC.md
│   ├── 03_传输层_HTTP.md
│   ├── 04_Protocol_Buffers编码.md
│   ├── 05_HTTP_JSON编码详解.md
│   └── 91_版本_OTLP_v1.9.0更新说明.md
│
├── 11_Traces数据模型/        # 3篇
│   ├── 01_Span结构.md
│   ├── 02_SpanContext.md
│   └── 03_SpanKind.md
│
├── 12_Metrics数据模型/       # 3篇
│   ├── 01_Metrics概述.md
│   ├── 02_Metrics子类型详解.md
│   └── 03_Pre-aggregation与Prometheus_StatsD映射.md
│
├── 13_Logs数据模型/          # 3篇
│   ├── 01_Logs概述.md
│   ├── 02_Logs字段与严重性详解.md
│   └── 03_统一结构与多格式映射.md
│
├── 14_Profiles数据模型/      # 2篇 (新增)
│   ├── README.md
│   └── 01_Profiles概述.md
│
├── 15_共享概念/              # 2篇
│   ├── 01_Resource模型.md
│   └── 01_Baggage详解.md
│
└── 21_语义约定/              # 32篇
    ├── 00_语义约定总览.md
    ├── HTTP/gRPC/RPC语义约定
    ├── 数据库语义约定 (SQL/NoSQL)
    ├── 消息队列语义约定 (Kafka/RabbitMQ等)
    ├── FaaS语义约定 (AWS/Azure/GCP Lambda)
    └── ... (更多)
```

---

## 四大信号类型

| 信号 | 状态 | 核心文档 |
|------|------|----------|
| **Traces** | ✅ Stable | [11_Traces数据模型](11_Traces数据模型/) |
| **Metrics** | ✅ Stable | [12_Metrics数据模型](12_Metrics数据模型/) |
| **Logs** | ✅ Stable | [13_Logs数据模型](13_Logs数据模型/) |
| **Profiles** | 🚧 Development | [14_Profiles数据模型](14_Profiles数据模型/) |

---

## 协议基础

### 传输协议

| 协议 | 端口 | 特点 | 适用场景 |
|------|------|------|----------|
| gRPC | 4317 | 高性能、流式 | 生产环境推荐 |
| HTTP/1.1 | 4318 | 兼容性好 | Web/防火墙环境 |
| HTTP/2 | 4318 | 多路复用 | 现代Web环境 |

### 编码格式

| 格式 | 压缩率 | 解析速度 | 适用场景 |
|------|--------|----------|----------|
| Protobuf | 高 | 快 | 生产环境 |
| JSON | 中 | 中 | 调试/开发 |

---

## 语义约定 (v1.40.0)

### 稳定领域

- ✅ HTTP Spans
- ✅ Database
- ✅ RPC
- ✅ Messaging

### 新增语义约定

- GenAI (大语言模型)
- CloudEvents
- Feature Flags

### 迁移指南

- [95_迁移指南_新旧语义约定迁移](21_语义约定/95_迁移指南_新旧语义约定迁移.md)

---

## 学习路径

### 入门

1. [01_协议概述](01_协议基础/01_协议概述.md)
2. [00_语义约定总览](21_语义约定/00_语义约定总览.md)

### 进阶

3. [02_传输层_gRPC](01_协议基础/02_传输层_gRPC.md)
4. [01_Span结构](11_Traces数据模型/01_Span结构.md)
5. [01_Metrics概述](12_Metrics数据模型/01_Metrics概述.md)

### 专家

6. 完整阅读语义约定
7. [01_Profiles概述](14_Profiles数据模型/01_Profiles概述.md)

---

**维护者**: OTLP核心协议团队  
**规范版本**: v1.55.0 / v1.40.0
