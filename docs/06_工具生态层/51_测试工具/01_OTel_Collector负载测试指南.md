---
title: OTel Collector负载测试指南
description: OpenTelemetry Collector性能测试方法和工具
category: 工具生态
tags:
  - testing
  - load-testing
  - performance
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# OTel Collector负载测试指南

> **测试工具**: telemetrygen
> **最后更新**: 2026-03-17

---

## 1. telemetrygen使用

```bash
# Trace负载测试
docker run otel/opentelemetry-collector-contrib:0.147.0 \
  telemetrygen traces \
  --otlp-endpoint=collector:4317 \
  --rate=1000 \
  --duration=60s
```

---

**最后更新**: 2026-03-17
**状态**: Published
