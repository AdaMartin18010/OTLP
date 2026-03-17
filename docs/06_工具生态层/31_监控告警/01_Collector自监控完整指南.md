---
title: Collector自监控完整指南
description: 全面掌握OpenTelemetry Collector自身可观测性，包括指标采集、健康检查、性能分析和故障诊断
category: 工具生态
tags:
  - collector
  - monitoring
  - metrics
  - health
  - troubleshooting
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# Collector自监控完整指南

> **目标读者**: Collector运维人员、SRE工程师
> **技术深度**: ⭐⭐⭐⭐ (高级)
> **最后更新**: 2026-03-17

---

## 1. 为什么需要自监控

### 1.1 Collector自身也是关键组件

```
Collector作为可观测性基础设施的核心:
├── 如果Collector挂掉 → 所有监控数据丢失 → 系统"失明"
├── 如果Collector变慢 → 数据延迟 → 告警误报/漏报
├── 如果Collector丢数据 → 监控盲区 → 无法发现问题
└── 如果Collector资源耗尽 → 级联故障 → 影响业务

自监控的目的:
✓ 确保Collector自身的健康
✓ 及时发现性能瓶颈
✓ 预防数据丢失
✓ 支持容量规划
```

### 1.2 自监控的关键指标

```
┌──────────────────────────────────────────────────────────────┐
│                    Collector自监控指标分类                     │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  接收层 (Receiver)                                           │
│  ├── 接收速率 (spans/metrics/logs per second)                │
│  ├── 接收拒绝率 (rate limited/refused)                       │
│  └── 连接数 (active connections)                             │
│                                                              │
│  处理层 (Processor)                                          │
│  ├── 处理延迟 (processing latency)                           │
│  ├── 队列深度 (queue depth)                                  │
│  ├── 批次大小 (batch size distribution)                      │
│  └──  dropped数据 (filtering/sampling drops)                 │
│                                                              │
│  导出层 (Exporter)                                           │
│  ├── 导出速率 (export rate)                                  │
│  ├── 导出成功率 (success/failure ratio)                      │
│  ├── 导出延迟 (export latency)                               │
│  ├── 重试次数 (retry count)                                  │
│  └── 队列使用情况 (queue utilization)                        │
│                                                              │
│  资源使用                                                    │
│  ├── CPU使用率                                               │
│  ├── 内存使用量 (RSS/Heap)                                   │
│  ├── Goroutine数量                                           │
│  ├── GC频率和暂停时间                                        │
│  └── 文件描述符使用                                          │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

---

## 2. 启用Collector自监控

### 2.1 基础自监控配置

```yaml
# 在Collector配置中启用自监控
service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]

  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888

    logs:
      level: info
      sampling:
        initial: 2
        thereafter: 500
```

---

## 3. 核心指标详解

### 3.1 接收层指标

```promql
# 接收速率
sum(rate(otelcol_receiver_accepted_spans[5m])) by (receiver)

# 拒绝率
sum(rate(otelcol_receiver_refused_spans[5m])) by (receiver)
```

### 3.2 导出层指标

```promql
# 导出成功率
(
  sum(rate(otelcol_exporter_sent_spans[5m]))
  /
  (
    sum(rate(otelcol_exporter_sent_spans[5m]))
    +
    sum(rate(otelcol_exporter_send_failed_spans[5m]))
  )
) * 100

# 队列使用率
(otelcol_exporter_queue_size / otelcol_exporter_queue_capacity) * 100
```

---

## 4. 告警规则

```yaml
groups:
  - name: collector-critical
    rules:
      - alert: CollectorQueueNearFull
        expr: |
          (otelcol_exporter_queue_size / otelcol_exporter_queue_capacity) > 0.9
        for: 2m
        labels:
          severity: critical
```

---

**最后更新**: 2026-03-17
**状态**: Published
