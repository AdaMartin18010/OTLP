---
title: Grafana OTLP可视化方案
description: 使用Grafana可视化OpenTelemetry数据，包括Dashboard配置、数据源设置和告警规则
category: 工具生态
tags:
  - grafana
  - visualization
  - dashboard
  - observability
version: Grafana 10.x
date: 2026-03-17
status: published
---

# Grafana OTLP可视化方案

> **Grafana版本**: 10.x
> **技术深度**: ⭐⭐⭐ (中级)
> **最后更新**: 2026-03-17

---

## 1. 数据源配置

### 1.1 Tempo (Trace)

```yaml
# datasources.yaml
apiVersion: 1
datasources:
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    jsonData:
      httpMethod: GET
      serviceMap:
        datasourceUid: prometheus
```

### 1.2 Prometheus (Metrics)

```yaml
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    jsonData:
      timeInterval: 5s
      httpMethod: POST
      manageAlerts: true
      prometheusType: Prometheus
```

### 1.3 Loki (Logs)

```yaml
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    jsonData:
      maxLines: 1000
      derivedFields:
        - name: TraceID
          matcherRegex: '"trace_id":"(\w+)"'
          url: '$${__value.raw}'
          datasourceUid: tempo
```

---

## 2. Dashboard配置

### 2.1 应用性能Dashboard

```json
{
  "dashboard": {
    "title": "Application Observability",
    "panels": [
      {
        "title": "Request Rate",
        "type": "timeseries",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total[5m])) by (service)",
            "legendFormat": "{{service}}"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "stat",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total{status=~\"5..\"}[5m])) / sum(rate(http_requests_total[5m]))",
            "instant": true
          }
        ]
      }
    ]
  }
}
```

---

**最后更新**: 2026-03-17
**状态**: Published
