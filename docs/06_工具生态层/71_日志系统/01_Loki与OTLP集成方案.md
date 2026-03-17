---
title: Loki与OTLP集成方案
description: Grafana Loki与OpenTelemetry的深度集成方案
category: 工具生态
tags:
  - loki
  - grafana
  - logs
version: Loki 3.x, OTLP v1.10.0
date: 2026-03-17
status: published
---

# Loki与OTLP集成方案

> **Loki版本**: 3.x
> **最后更新**: 2026-03-17

---

## 1. 集成方式

- Collector推送到Loki
- Loki直接接收OTLP

## 2. Collector配置

```yaml
exporters:
  loki:
    endpoint: http://loki:3100/loki/api/v1/push
    labels:
      attributes:
        service.name: "service"
```

## 3. TraceID关联

```go
// 日志中注入TraceID
logger.Info(message,
    zap.String("trace_id", traceID),
    zap.String("span_id", spanID),
)
```

---

**最后更新**: 2026-03-17
**状态**: Published
