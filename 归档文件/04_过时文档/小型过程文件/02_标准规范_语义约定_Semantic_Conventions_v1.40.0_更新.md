# Semantic Conventions v1.40.0 更新摘要

> **状态**: 内容对齐中
> **目标版本**: v1.40.0 (2026年2月发布)
> **当前项目版本**: v1.39.0 → v1.40.0

## 版本跨度

本次更新: **v1.39.0 → v1.40.0**

## 关键更新内容

### 1. GenAI语义约定 - Agent Span (Draft)

- **状态**: Draft (草案阶段)
- **新增属性**:
  - gen_ai.agent.id
  - gen_ai.agent.name
  - gen_ai.agent.version
  - gen_ai.agent.system
  - gen_ai.agent.invocation.id

### 2. GenAI成本追踪 (Development)

- **新增属性**:
  - gen_ai.cost.currency
  - gen_ai.cost.amount

### 3. 数据库语义约定扩展

- **新增**: OpenSearch、CockroachDB、Neo4j
- **状态**: Experimental

### 4. 移动端语义约定

- **新增**: 设备信息属性
- **新增**: 网络类型属性
- **状态**: Experimental

## 状态变更

| 约定领域 | v1.39.0 | v1.40.0 |
|:---------|:-------:|:-------:|
| LLM Spans | Development | Development |
| Agent Spans | N/A | **Draft** ⬆️ |
| GenAI Events | Development | Development |

## 参考资源

- [v1.40.0 Release Notes](https://github.com/open-telemetry/semantic-conventions/releases/tag/v1.40.0)
- [GenAI Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)

---
**更新日期**: 2026年3月16日
