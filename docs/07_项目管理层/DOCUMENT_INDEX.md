# 📚 OTLP项目文档索引 - 按主题组织

> **更新日期**: 2025年10月27日
> **组织方式**: 按十二大子主题分类
> **版本**: v2.0.0

---

## 🎯 快速入口

| 角色 | 推荐入口 |
|:---|:---|
| 👤 **新用户** | [🎯 5分钟快速入门](./🎯_5分钟快速入门指南.md) → [💻 代码示例](./examples/README.md) |
| 👨‍💻 **开发者** | [📖 标准深度梳理](./docs/README.md) → [💻 代码示例](./examples/README.md) |
| 📚 **研究人员** | [📚 知识中心](./00_知识中心/README.md) → [📐 理论基础](./docs/01_理论基础/) |
| 🏢 **运维人员** | [🐳 Docker部署](./🐳_Docker部署完整指南.md) → [☸️ K8s部署](./☸️_Kubernetes部署完整指南.md) |
| 📊 **管理者** | [📊 项目仪表板](./PROJECT_DASHBOARD.md) → [📊 批判性评价报告](./📊_OTLP项目全面批判性评价与改进建议报告_2025_10_27.md) |

---

## 📋 十二大主题索引

---

### T1 理论基础

> 数学基础、形式化验证、证明策略

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| 数学基础 | `docs/01_理论基础/` | 集合论、图论、信息论在可观测性中的应用 |
| 形式化验证框架 | `docs/02_THEORETICAL_FRAMEWORK/` | TLA+、Coq、Isabelle/HOL验证框架 |
| 分布式系统理论 | `docs/02_THEORETICAL_FRAMEWORK/DISTRIBUTED_SYSTEMS_THEORY.md` | 分布式系统理论基础 |

---

### T2 标准规范

> OTLP协议、语义约定、国际标准对齐

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| OTLP协议概述 | `docs/01_OTLP核心协议/01_协议概述.md` | OTLP协议核心概念 |
| 传输层gRPC | `docs/01_OTLP核心协议/02_传输层_gRPC.md` | gRPC传输详解 |
| 传输层HTTP | `docs/01_OTLP核心协议/03_传输层_HTTP.md` | HTTP传输详解 |
| Protocol Buffers编码 | `docs/01_OTLP核心协议/04_Protocol_Buffers编码.md` | Protobuf编码规范 |
| HTTP JSON编码 | `docs/01_OTLP核心协议/05_HTTP_JSON编码详解.md` | JSON编码规范 |
| 语义约定总览 | `docs/02_Semantic_Conventions/00_语义约定总览.md` | Semantic Conventions概览 |
| HTTP语义属性 | `docs/02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | HTTP追踪属性 |
| gRPC语义属性 | `docs/02_Semantic_Conventions/02_追踪属性/02_gRPC.md` | gRPC追踪属性 |
| 数据库语义属性 | `docs/02_Semantic_Conventions/02_追踪属性/03_数据库.md` | 数据库追踪属性 |

---

### T3 数据模型

> Traces、Metrics、Logs、Baggage、Resource

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| Span结构 | `docs/03_数据模型/01_Traces数据模型/01_Span结构.md` | Span核心结构 |
| SpanContext | `docs/03_数据模型/01_Traces数据模型/02_SpanContext.md` | 上下文传播 |
| SpanKind | `docs/03_数据模型/01_Traces数据模型/03_SpanKind.md` | Span类型 |
| Metrics概述 | `docs/03_数据模型/02_Metrics数据模型/01_Metrics概述.md` | 指标模型 |
| Metrics子类型 | `docs/03_数据模型/02_Metrics数据模型/02_Metrics子类型详解.md` | 指标类型详解 |
| Logs概述 | `docs/03_数据模型/03_Logs数据模型/01_Logs概述.md` | 日志模型 |
| Resource模型 | `docs/03_数据模型/04_Resource/01_Resource模型.md` | 资源模型 |
| Baggage详解 | `docs/03_数据模型/05_Baggage/01_Baggage详解.md` | Baggage上下文 |

---

### T4 传输协议

> Protocol Buffers、gRPC、HTTP、编码与压缩

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| Protocol Buffers编码 | `docs/01_OTLP核心协议/04_Protocol_Buffers编码.md` | Protobuf序列化 |
| HTTP JSON编码 | `docs/01_OTLP核心协议/05_HTTP_JSON编码详解.md` | JSON序列化 |
| 数据流优化策略 | `docs/03_数据模型/13_数据流优化策略_增量传输与压缩.md` | 传输优化 |

---

### T5 核心组件

> SDK、Collector、Receiver/Processor/Exporter

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| SDK概述 | `docs/04_核心组件/01_SDK概述.md` | SDK架构 |
| SDK最佳实践 | `docs/04_核心组件/03_SDK最佳实践.md` | 最佳实践指南 |
| Collector架构 | `docs/04_核心组件/02_Collector架构.md` | Collector架构 |
| Receiver配置 | `docs/04_核心组件/04_Collector_Receiver配置详解.md` | Receiver详解 |
| Processor配置 | `docs/04_核心组件/03_Collector_Processor配置详解.md` | Processor详解 |
| Exporter配置 | `docs/04_核心组件/05_Collector_Exporter配置详解.md` | Exporter详解 |
| 生产环境配置 | `docs/04_核心组件/06_Collector生产环境完整配置示例.md` | 生产配置示例 |
| Context Propagation | `docs/04_核心组件/04_Context_Propagation详解.md` | 上下文传播 |
| OpAMP协议 | `docs/04_核心组件/07_OpAMP管理协议完整指南.md` | 管理协议 |

---

### T6 采样与性能

> 采样策略、性能优化、压缩技术

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| 采样策略 | `docs/05_采样与性能/01_采样策略.md` | 采样算法 |
| 性能优化实践 | `docs/05_采样与性能/02_性能优化实践.md` | 性能调优 |
| Trace压缩技术 | `docs/05_采样与性能/04_Tracezip压缩技术_2025.md` | 2025压缩技术 |
| 前沿采样技术 | `docs/05_采样与性能/04_前沿采样技术_2025.md` | 2025采样技术 |
| Autoscope智能采样 | `docs/05_采样与性能/05_Autoscope智能采样_2025.md` | 智能采样 |

---

### T7 部署运维 ⭐ 生产就绪

> Docker、K8s、安全、监控、故障排查、性能优化

| 文档 | 路径 | 描述 | 优先级 |
|:---|:---|:---|:---:|
| **5分钟快速入门** | [🎯_5分钟快速入门指南.md](./🎯_5分钟快速入门指南.md) | 零基础快速上手 | ⭐⭐⭐⭐⭐ |
| **Docker部署** | [🐳_Docker部署完整指南.md](./🐳_Docker部署完整指南.md) | 容器化部署 | ⭐⭐⭐⭐⭐ |
| **Kubernetes部署** | [☸️_Kubernetes部署完整指南.md](./☸️_Kubernetes部署完整指南.md) | K8s生产级部署 | ⭐⭐⭐⭐⭐ |
| **安全最佳实践** | [🔒_安全最佳实践指南.md](./🔒_安全最佳实践指南.md) | 6大安全领域 | ⭐⭐⭐⭐⭐ |
| **监控告警** | [📊_监控告警完整指南.md](./📊_监控告警完整指南.md) | Prometheus+Grafana | ⭐⭐⭐⭐⭐ |
| **故障排查** | [🔧_故障排查完整手册.md](./🔧_故障排查完整手册.md) | 8类问题30+方案 | ⭐⭐⭐⭐⭐ |
| **性能优化** | [⚡_性能优化完整指南.md](./⚡_性能优化完整指南.md) | 6领域40+技巧 | ⭐⭐⭐⭐⭐ |

---

### T8 实战案例

> 微服务追踪、分布式事务、多行业案例

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| 微服务追踪实战 | `docs/06_实战案例/01_微服务追踪实战.md` | 微服务场景 |
| 分布式事务追踪 | `docs/06_实战案例/02_分布式事务追踪.md` | 事务追踪 |
| eBPF自动追踪 | `docs/06_实战案例/03_eBPF自动追踪.md` | eBPF技术 |
| 生产环境最佳实践 | `docs/06_实战案例/04_生产环境最佳实践.md` | 最佳实践 |
| 大规模电商系统 | `docs/06_实战案例/05_大规模电商系统可观测性实战.md` | 电商案例 |
| 金融核心系统 | `docs/06_实战案例/06_金融行业核心系统可观测性实战.md` | 金融案例 |
| 智能制造 | `docs/06_实战案例/07_智能制造可观测性实战.md` | 制造案例 |
| 智慧物流 | `docs/06_实战案例/08_智慧物流可观测性实战.md` | 物流案例 |
| 医疗健康系统 | `docs/06_实战案例/09_医疗健康系统可观测性实战.md` | 医疗案例 |
| 教育平台 | `docs/06_实战案例/10_教育平台可观测性实战.md` | 教育案例 |

---

### T9 学术研究

> 论文框架、形式化证明、案例研究

| 文档 | 路径 | 状态 |
|:---|:---|:---:|
| 论文框架 | `academic.rar` (解压后) | ✅ 完成 |
| 形式化证明 | `academic.rar` (解压后) | ✅ 完成 |
| 案例研究 | `academic.rar` (解压后) | ✅ 完成 |
| 参考文献 | `academic.rar` (解压后) | ✅ 完成 |

> **注意**: 学术材料已打包为 `academic.rar`，包含ICSE 2026论文完整材料

---

### T10 前沿技术

> eBPF、GenAI、Wasm、Arrow、边缘计算

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| OTLP Arrow | `docs/12_前沿技术/04_OTLP_Arrow完整指南_2025.md` | Arrow格式 |
| GenAI可观测性 | `docs/12_前沿技术/02_GenAI_Observability.md` | AI可观测性 |
| AgentSight | `docs/12_前沿技术/06_AgentSight_AI驱动智能监控_2025.md` | AI驱动监控 |
| Go编译时Instrumentation | `docs/12_前沿技术/07_Go编译时instrumentation完整指南_2025.md` | 编译时插桩 |
| Wasm插件生态 | `docs/12_前沿技术/08_Wasm插件生态完整指南_2025.md` | WebAssembly |
| 边缘可观测性 | `docs/12_前沿技术/09_边缘可观测性完整指南_2025.md` | 边缘计算 |
| 预测性维护 | `docs/12_前沿技术/10_预测性维护完整指南_2025.md` | AIOps |
| eBPF可观测性 | `docs/🐝_eBPF可观测性深度技术指南_零侵入式追踪.md` | eBPF深度指南 |

---

### T11 知识中心 ⭐⭐⭐⭐⭐

> 概念索引、知识图谱、矩阵对比、思维导图、术语表

| 子系统 | 路径 | 内容 |
|:---|:---|:---|
| **概念索引** | [00_知识中心/01_概念索引/](./00_知识中心/01_概念索引/) | 150+概念定义和关系 |
| **知识图谱** | [00_知识中心/02_知识图谱/](./00_知识中心/02_知识图谱/) | 30+可视化知识图谱 |
| **矩阵对比** | [00_知识中心/03_矩阵对比/](./00_知识中心/03_矩阵对比/) | 50+对比分析矩阵 |
| **思维导图** | [00_知识中心/04_思维导图/](./00_知识中心/04_思维导图/) | 25+学习路径导图 |
| **术语表** | [00_知识中心/05_术语表/](./00_知识中心/05_术语表/) | 300+术语中英对照 |
| **FAQ** | [00_知识中心/❓_常见问题FAQ.md](./00_知识中心/❓_常见问题FAQ.md) | 常见问题解答 |
| **故障排查** | [00_知识中心/🔧_故障排查指南.md](./00_知识中心/🔧_故障排查指南.md) | 快速排查指南 |

---

### T12 工具链

> 配置生成器、文档管理、质量检查、自动化脚本

| 工具 | 路径 | 描述 |
|:---|:---|:---|
| 配置生成器 | `docs/工具/config-generator/` | OTLP Collector配置向导 |
| 文档管理 | `scripts/` | 文档管理自动化脚本 |
| 工具集 | `tools/` | 开发和维护工具 |

---

## 📊 项目状态文档

| 文档 | 路径 | 描述 |
|:---|:---|:---|
| 项目仪表板 | [PROJECT_DASHBOARD.md](./PROJECT_DASHBOARD.md) | 实时项目状态 |
| 批判性评价报告 | [📊_OTLP项目全面批判性评价与改进建议报告_2025_10_27.md](./📊_OTLP项目全面批判性评价与改进建议报告_2025_10_27.md) | 最新评价报告 |
| 国际对标报告 | [📊_OTLP项目全面梳理与国际对标报告_2025_10_26.md](./📊_OTLP项目全面梳理与国际对标报告_2025_10_26.md) | 对标分析报告 |
| 行动计划 | [🎯_OTLP项目行动计划_2025Q4-2026_ROADMAP.md](./🎯_OTLP项目行动计划_2025Q4-2026_ROADMAP.md) | 2025-2026路线图 |
| 改进计划 | [🚀_P1短期改进持续推进计划_2025_10_27.md](./🚀_P1短期改进持续推进计划_2025_10_27.md) | P1改进计划 |
| 执行状态 | [📋_P1短期改进执行状态_2025_10_27.md](./📋_P1短期改进执行状态_2025_10_27.md) | 执行状态跟踪 |

---

## 🌍 国际化文档

| 文档 | 路径 | 覆盖率 |
|:---|:---|:---:|
| 英文README | `docs_en/README_EN.md` | 核心20% |
| 英文索引 | `docs_en/INDEX.md` | 核心20% |
| 术语表 | `docs_en/GLOSSARY.md` | 150+术语 |
| 贡献指南 | `CONTRIBUTING.md` | 双语 |

---

## 📦 历史归档

| 目录 | 内容 |
|:---|:---|
| [archive/reports/completion/](./archive/reports/completion/) | 阶段完成报告 (11个) |
| [archive/reports/cleanup/](./archive/reports/cleanup/) | 文档清理报告 (11个) |
| [archive/reports/structure/](./archive/reports/structure/) | 结构修复报告 (5个) |
| [archive/reports/progress/](./archive/reports/progress/) | 进展报告 (4个) |
| [archive/reports/summaries/](./archive/reports/summaries/) | 总结报告 (5个) |
| [archive/reports/evaluation/](./archive/reports/evaluation/) | 评价报告 (3个) |
| [archive/reports/plans/](./archive/reports/plans/) | 历史计划 (2个) |
| [archive/reports/milestones/](./archive/reports/milestones/) | 里程碑报告 (2个) |
| [archive/obsolete/](./archive/obsolete/) | 废弃文档 (1个) |

> **总计**: 44个历史文档已归档

---

## 📈 文档统计

| 维度 | 数量 | 说明 |
|:---|:---:|:---|
| **核心文档** | 22个 | 根目录保留的核心文档 |
| **知识中心** | 31篇 | 概念/图谱/矩阵/导图/术语 |
| **标准文档** | 89篇 | 标准深度梳理文档 |
| **部署指南** | 7篇 | 完整部署运维体系 |
| **代码示例** | 630+ | 4种语言可运行示例 |
| **归档文档** | 44个 | 历史报告归档 |
| **总文档数** | 119+ | 持续更新中 |

---

## 💡 使用建议

1. **首次访问**: 从 [🎯 5分钟快速入门](./🎯_5分钟快速入门指南.md) 开始
2. **快速上手**: 查看 [💻 代码示例](./examples/README.md)
3. **深度研究**: 访问 [📚 知识中心](./00_知识中心/README.md)
4. **生产部署**: 查看 [T7 部署运维](#t7-部署运维-生产就绪)
5. **学术研究**: 解压 `academic.rar` 查看论文材料

---

**最后更新**: 2025年10月27日
**维护者**: OTLP项目团队
**版本**: v2.0.0 (按十二大子主题重新组织)
