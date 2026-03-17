---
title: OpenTelemetry与Prometheus集成
description: OpenTelemetry和Prometheus深度集成方案
category: 工具生态
tags:
  - prometheus
  - integration
version: Prometheus 2.55+, OTLP v1.10.0
date: 2026-03-17
status: published
---

# OpenTelemetry与Prometheus集成

> **Prometheus版本**: 2.55+  
> **最后更新**: 2026-03-17  

---

## 1. 集成方式

- Remote Write (推荐)
- OTLP接收
- 抓取模式

## 2. Remote Write配置

```yaml
remote_write:
  - url: "http://otel-collector:4318/v1/metrics"
```

---

**最后更新**: 2026-03-17  
**状态**: Published
