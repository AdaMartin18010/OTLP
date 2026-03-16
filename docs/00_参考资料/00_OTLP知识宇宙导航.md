---
title: OTLP知识宇宙 - 主题导航
description: OTLP知识宇宙 - 主题导航 详细指南
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 参考资料
tags:
  - otlp
  - observability
status: published
---
# OTLP知识宇宙 - 主题导航

> **项目版本**: v3.0
> **最后更新**: 2026年3月16日
> **对齐标准**: OpenTelemetry最新权威版本

---

## 8层主题架构

`
OTLP知识宇宙
├── 01_基础理论/          # L1: 数学基础、形式化方法
├── 02_标准规范/          # L2: 协议规范、语义约定 ⭐v1.40.0
├── 03_核心实现/          # L3: Collector、SDK ⭐v0.147.0
├── 04_部署运维/          # L4: Docker、K8s
├── 05_前沿技术/          # L5: GenAI、eBPF、Arrow ⭐
├── 06_行业实战/          # L6: 案例研究
├── 07_工具生态/          # L7: 平台集成
└── 08_学术资源/          # L8: 论文、证明
`

---

## 版本对齐状态

| 组件/规范 | 项目版本 | 最新版本 | 状态 | 文档 |
|:----------|:--------:|:--------:|:----:|:-----|
| **OTLP Protocol** | v1.9.0 | **v1.9.0** | ✅ | [01_OTLP核心协议/](docs/01_OTLP核心协议/) |
| **Semantic Conventions** | v1.40.0 | **v1.40.0** | ✅ | [02_标准规范/](docs/02_标准规范/) |
| **Collector** | v0.147.0 | **v0.147.0** | ✅ | [03_核心实现/](docs/03_核心实现/) |
| **GenAI Conventions** | Development | **Development** | ✅ | [05_前沿技术/](docs/05_前沿技术/) |

---

## 主题目录导航

### L1 - 基础理论

- [01_基础理论/](docs/01_基础理论/) - 数学基础、形式化方法

### L2 - 标准规范 ⭐

- [02_标准规范/](docs/02_标准规范/) - 协议规范、语义约定
  - [v1.40.0更新摘要](docs/02_标准规范/Semantic_Conventions_v1.40.0_更新.md)
  - [v1.40.0完整变更日志](docs/02_标准规范/Semantic_Conventions_v1.40.0_完整变更日志.md)

### L3 - 核心实现 ⭐

- [03_核心实现/](docs/03_核心实现/) - Collector、SDK
  - [v0.147.0更新摘要](docs/03_核心实现/OTel_Collector_v0.147.0_更新.md)
  - [v0.147.0完整变更日志](docs/03_核心实现/Collector_v0.147.0_完整变更日志.md)

### L4 - 部署运维

- [04_部署运维/](docs/04_部署运维/) - Docker、Kubernetes

### L5 - 前沿技术 ⭐

- [05_前沿技术/](docs/05_前沿技术/) - GenAI、eBPF、Arrow
  - [GenAI语义约定完整实现示例](docs/05_前沿技术/GenAI语义约定完整实现示例.md)

### L6 - 行业实战

- [06_行业实战/](docs/06_行业实战/) - 案例研究

### L7 - 工具生态

- [07_工具生态/](docs/07_工具生态/) - 平台集成

### L8 - 学术资源

- [08_学术资源/](docs/08_学术资源/) - 论文、证明

---

## 关键更新亮点

### Semantic Conventions v1.40.0

- **Agent语义约定**: Draft状态，新增Agent Span类型
- **成本追踪**: gen_ai.cost.currency, gen_ai.cost.amount
- **数据库扩展**: OpenSearch、CockroachDB、Neo4j

### Collector v0.147.0

- **声明式配置 GA**: Stable (v1.0.0)
- **组件升级**: filelog、hostmetrics、k8sattributes → Stable
- **OTTL增强**: 上下文推断功能

### GenAI语义约定

- **完整Python实现**: 包含LLM、Agent、Embedding示例
- **Agent追踪**: 支持多Agent协作编排
- **成本追踪**: 自动计算API调用成本

---

## 参考资源

- [OpenTelemetry官方文档](https://opentelemetry.io/docs/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)

---

**维护者**: OTLP项目团队
**项目状态**: ✅ 100% 对齐完成
