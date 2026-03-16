---
title: Zipkin Exporter 弃用说明与迁移指南
description: Zipkin Exporter 弃用说明与迁移指南 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 标准规范
tags:
  - otlp
  - observability
  - performance
  - optimization
status: published
---
# Zipkin Exporter 弃用说明与迁移指南

> **发布日期**: 2025年12月1日
> **影响版本**: 所有使用Zipkin Exporter的版本
> **迁移期限**: 建议立即开始迁移
> **替代方案**: 使用Zipkin的OTLP接收端或直接切换到OTLP

---

## � 弃用公告

OpenTelemetry项目已于**2025年12月1日**正式宣布弃用Zipkin Exporter Specification。

### 弃用原因

1. **Zipkin原生支持OTLP**: Zipkin已添加对OpenTelemetry Protocol (OTLP)的原生支持
2. **减少维护负担**: 避免维护多个导出器实现
3. **推动标准化**: 鼓励使用统一的OTLP协议
4. **社区趋势**: Zipkin社区已转向OTLP作为主要接收协议

---

## 迁移方案

### 方案一: 使用Zipkin的OTLP接收端 (推荐)

**适用场景**: 需要继续将数据发送到Zipkin后端

**配置步骤**:

1. **更新Collector配置**

`yaml

# 旧配置 (已弃用)

exporters:
  zipkin:
    endpoint: "<http://zipkin:9411/api/v2/spans>"

# 新配置 (推荐)

exporters:
  otlp/zipkin:
    endpoint: "<http://zipkin:9411/api/v2/otlp>"  # Zipkin OTLP端点
    tls:
      insecure: true
`

1. **更新Pipeline**

`yaml
service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/zipkin]  # 使用OTLP替代zipkin
`

### 方案二: 直接切换到OTLP后端

**适用场景**: 可以更换后端或同时使用多个后端

**配置示例**:

`yaml
exporters:
  otlp/jaeger:
    endpoint: "jaeger:4317"
    tls:
      insecure: true

  otlp/tempo:
    endpoint: "tempo:4317"
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/jaeger, otlp/tempo]
`

---

## ⚠ 注意事项

### 数据格式差异

| 特性 | Zipkin Exporter | OTLP |
|------|----------------|------|
| 协议 | HTTP JSON | gRPC/HTTP Protobuf |
| 性能 | 较低 | 高 |
| 功能 | 基础 | 完整(Metrics/Logs/Traces) |
| 维护 | 停止 | 持续 |

### 标签/属性映射

OTLP和Zipkin的标签映射大部分自动处理，但以下字段需要特别注意:

`yaml

# Zipkin标签在OTLP中的等价表示

zipkin.tag.http.method -> http.request.method
zipkin.tag.http.status_code -> http.response.status_code
zipkin.tag.http.url -> url.full
zipkin.tag.error -> error.type
`

---

## 迁移检查清单

- [ ] 识别所有使用Zipkin Exporter的Collector配置
- [ ] 更新Collector配置文件
- [ ] 验证Zipkin后端支持OTLP (版本>=2.24.0)
- [ ] 测试数据接收和展示
- [ ] 更新文档和运维手册
- [ ] 通知团队成员
- [ ] 监控迁移后的系统稳定性

---

## 参考资源

- [OpenTelemetry弃用公告](https://opentelemetry.io/blog/2025/zipkin-exporter-deprecation/)
- [Zipkin OTLP支持文档](https://zipkin.io/pages/otlp)
- [OTLP协议规范](https://opentelemetry.io/docs/specs/otlp/)

---

**最后更新**: 2026年3月17日
**维护团队**: OTLP项目团队
