# 05_前沿技术

> **层级**: L5 - 前沿技术层  
> **描述**: GenAI可观测性、eBPF自动插桩、OTLP Arrow等前沿技术  
> **维护状态**: ✅ 持续更新

---

## 目录结构

`
05_前沿技术/
├── README.md                              # 本文件
├── GenAI语义约定完整实现示例.md            ⭐ 最新
└── [其他前沿技术文档]
`

---

## 技术领域

### GenAI可观测性

| 规范 | 状态 | 说明 |
|:-----|:----:|:-----|
| LLM Spans | Development | GenAI核心追踪 |
| Agent Spans | Draft | AI Agent追踪 (v1.40新增) |
| Embeddings | Development | 向量化追踪 |
| Cost Tracking | Development | 成本追踪 |

**关键更新 (v1.40)**:
- Agent语义约定草案
- 成本追踪属性: gen_ai.cost.currency, gen_ai.cost.amount
- Agent工具调用追踪

### eBPF自动插桩

- **状态**: 快速发展
- **应用**: 无侵入式可观测性
- **场景**: 内核级性能分析

### OTLP Arrow

- **状态**: Experimental
- **特性**: 列式存储、有状态协议
- **优势**: 高吞吐数据传输

---

## 关键文档

| 文档 | 技术领域 | 状态 |
|:-----|:---------|:----:|
| [GenAI语义约定完整实现示例](GenAI语义约定完整实现示例.md) | GenAI | ✅ |

---

## 参考资源

- [GenAI Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)
- [eBPF Foundation](https://ebpf.foundation/)
- [Apache Arrow](https://arrow.apache.org/)

---

**维护者**: OTLP项目团队  
**最后更新**: 2026年3月16日
