# 02_标准规范

> **层级**: L2 - 标准规范层
> **描述**: OpenTelemetry官方标准、协议规范、语义约定
> **维护状态**: ✅ 已对齐至最新版本

---

## 目录结构

`
02_标准规范/
├── README.md                              # 本文件
├── Semantic_Conventions_v1.40.0_更新.md     ⭐ 最新
├── Semantic_Conventions_v1.40.0_完整变更日志.md ⭐ 最新
└── [其他规范文档]
`

---

## 规范版本状态

| 规范 | 当前版本 | 最新版本 | 状态 |
|:-----|:--------:|:--------:|:----:|
| OTLP Protocol | v1.9.0 | **v1.9.0** | ✅ 已对齐 |
| Semantic Conventions | v1.40.0 | **v1.40.0** | ✅ 已对齐 |
| GenAI Conventions | Development | **Development** | ✅ 已对齐 |

---

## 关键文档

### Semantic Conventions

| 文档 | 描述 | 状态 |
|:-----|:-----|:----:|
| [v1.40.0更新摘要](Semantic_Conventions_v1.40.0_更新.md) | 快速了解v1.40变更 | ✅ |
| [v1.40.0完整变更日志](91_变更日志_Semantic_Conventions_v1.40.0完整变更日志.md) | 详细变更记录 | ✅ |

### GenAI语义约定

- **状态**: Development (LLM Spans) / Draft (Agent Spans)
- **位置**: docs/13_GenAI可观测性/
- **关键更新**:
  - Agent语义约定 (v1.40 Draft)
  - 成本追踪属性 (gen_ai.cost.*)
  - Agent工具调用追踪

---

## 规范稳定性级别

| 级别 | 含义 | 使用建议 |
|:-----|:-----|:---------|
| **Stable** | 稳定版，向后兼容 | ✅ 生产环境 |
| **Beta** | 功能完整，可能微调 | ⚠️ 评估后使用 |
| **Alpha** | 实验性质，可能变更 | ⚠️ 测试环境 |
| **Development** | 快速迭代，频繁变更 | ⚠️ 关注更新 |
| **Draft** | 草案阶段，非正式 | ⚠️ 参考性质 |

---

## 参考资源

- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)
- [GenAI Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)

---

**维护者**: OTLP项目团队
**最后更新**: 2026年3月16日

