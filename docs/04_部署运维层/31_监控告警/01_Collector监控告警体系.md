---
title: Collector监控告警体系
description: OpenTelemetry Collector完整监控告警方案
category: 运维实践
tags:
  - monitoring
  - alerting
  - sre
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# Collector监控告警体系

> **目标**: 99.9%可用性保障
> **最后更新**: 2026-03-17

---

## 1. 四层监控模型

- 业务监控
- 性能监控
- 资源监控
- 健康监控

## 2. 关键告警

| 告警 | 级别 | 阈值 |
|------|------|------|
| 数据丢失 | P0 | >1% |
| 队列满 | P0 | >95% |
| 高内存 | P1 | >3GB |

---

**最后更新**: 2026-03-17
**状态**: Published
