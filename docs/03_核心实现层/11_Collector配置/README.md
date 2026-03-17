---
title: 11_Collector配置
description: OTLP Collector详细配置指南 - Receiver, Processor, Exporter
category: 核心实现
version: OTLP v1.9.0
collector_version: v0.147.0
date: 2026-03-17
status: published
---

# 11_Collector配置

> **目录状态**: 📚 持续完善中  
> **定位**: OpenTelemetry Collector的详细配置指南  
> **最后更新**: 2026-03-17  

---

## 目录结构

本目录包含Collector各组件的详细配置文档：

### Receiver配置
- [04_Collector_Receiver配置详解](../01_SDK实现/04_Collector_Receiver配置详解.md)
- OTLP Receiver
- Prometheus Receiver
- Kafka Receiver
- 其他Receivers

### Processor配置
- [03_Collector_Processor配置详解](../01_SDK实现/03_Collector_Processor配置详解.md)
- Batch Processor
- Memory Limiter
- Attributes Processor
- Resource Processor
- Tail Sampling Processor

### Exporter配置
- [05_Collector_Exporter配置详解](../01_SDK实现/05_Collector_Exporter配置详解.md)
- OTLP Exporter
- Prometheus Exporter
- Kafka Exporter
- Elasticsearch Exporter

---

## 快速导航

| 组件 | 配置文档 | 用途 |
|------|---------|------|
| Receiver | 04_Collector_Receiver配置详解.md | 数据接收端配置 |
| Processor | 03_Collector_Processor配置详解.md | 数据处理配置 |
| Exporter | 05_Collector_Exporter配置详解.md | 数据导出配置 |

---

## 完整配置示例

- [06_Collector生产环境完整配置示例](../01_SDK实现/06_Collector生产环境完整配置示例.md)

---

**维护者**: OTLP核心实现团队
