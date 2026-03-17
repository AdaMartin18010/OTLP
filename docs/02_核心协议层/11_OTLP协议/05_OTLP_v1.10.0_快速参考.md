---
title: OTLP v1.10.0 快速参考
description: OTLP v1.10.0完整速查手册，包含所有信号定义、字段说明和版本对比
version: OTLP v1.10.0
category: 核心协议
tags:
  - otlp
  - v1.10.0
  - quick-reference
  - cheat-sheet
status: published
date: 2026-03-17
---

# OTLP v1.10.0 快速参考

> **协议版本**: v1.10.0 (2026-03-09)  
> **规范状态**: Stable (Traces/Metrics/Logs), Development (Profiles)  
> **最后更新**: 2026-03-17  

---

## 版本信息

| 组件 | 版本 | 状态 | 发布日期 |
|------|------|------|----------|
| OTLP Protocol | v1.10.0 | Stable | 2026-03-09 |
| Traces | v1.10.0 | Stable | - |
| Metrics | v1.10.0 | Stable | - |
| Logs | v1.10.0 | Stable | - |
| Profiles | v1.10.0 | Development | - |

---

## v1.10.0 关键变更

### 新增特性
- ✅ Profiles引用属性机制 ([#733](https://github.com/open-telemetry/opentelemetry-proto/pull/733))
- ✅ 字段命名规范化 (ref → strindex) ([#768](https://github.com/open-telemetry/opentelemetry-proto/pull/768))
- ✅ severity_number可选性澄清 ([#736](https://github.com/open-telemetry/opentelemetry-proto/pull/736))

### 破坏性变更
⚠️ Profiles字段重命名 (仅影响Development阶段的Profiles信号)

---

## 协议端点

| 传输协议 | Traces | Metrics | Logs | Profiles |
|----------|--------|---------|------|----------|
| gRPC | `:4317` | `:4317` | `:4317` | `:4317` |
| HTTP | `:4318/v1/traces` | `:4318/v1/metrics` | `:4318/v1/logs` | `:4318/v1/profiles` |

---

## Proto文件列表

```
opentelemetry/proto/
├── common/v1/common.proto
├── resource/v1/resource.proto
├── trace/v1/trace.proto
├── metrics/v1/metrics.proto
├── logs/v1/logs.proto
├── profiles/v1/profiles.proto (v1.10.0更新)
├── profiles/v1/alternatives/ (实验性)
└── collector/
    ├── trace/v1/trace_service.proto
    ├── metrics/v1/metrics_service.proto
    ├── logs/v1/logs_service.proto
    └── profiles/v1/profiles_service.proto
```

---

## 参考链接

- [GitHub Release](https://github.com/open-telemetry/opentelemetry-proto/releases/tag/v1.10.0)
- [CHANGELOG](https://github.com/open-telemetry/opentelemetry-proto/blob/main/CHANGELOG.md)
- [官方文档](https://opentelemetry.io/docs/specs/otlp/)

---

**最后更新**: 2026-03-17  
**状态**: Published
