# Semantic Conventions v1.39.0 → v1.40.0 完整变更日志

> **来源**: OpenTelemetry Semantic Conventions GitHub Releases
> **发布日期**: v1.40.0 (2026年2月)
> **文档状态**: ✅ 已对齐

---

## 变更概览

| 类别 | 变更数量 | 影响程度 |
|:-----|:--------:|:--------:|
| GenAI | 5项新增 | 高 |
| Database | 3项新增 | 中 |
| Mobile | 2项新增 | 中 |
| General | 稳定性升级 | 低 |

---

## GenAI语义约定变更

### 1. Agent Span 约定 (NEW - Draft)

**状态**: Draft (草案阶段)
**来源**: Google AI Agent白皮书 & OTel社区提案

#### 新增Span类型

`
gen_ai.agent.create    - Agent创建
gen_ai.agent.invoke    - Agent调用
gen_ai.agent.tool      - Agent工具调用
gen_ai.agent.plan      - Agent规划
gen_ai.agent.generate  - Agent响应生成
`

#### 新增属性

| 属性名 | 类型 | 描述 | 示例 |
|:-------|:----:|:-----|:-----|
| gen_ai.agent.id | string | Agent唯一标识 | agent-001 |
| gen_ai.agent.name | string | Agent名称 | CustomerServiceAgent |
| gen_ai.agent.version | string | Agent版本 | 1.0.0 |
| gen_ai.agent.system | string | Agent框架 | langchain, llamaindex, autogen, crewai |
| gen_ai.agent.invocation.id | string | 调用ID | inv-12345 |
| gen_ai.agent.invocation.type | string | 调用类型 | synchronous, asynchronous, streaming |
| gen_ai.agent.tool.name | string | 工具名称 | search_database |
| gen_ai.agent.tool.input | string | 工具输入 | JSON字符串 |
| gen_ai.agent.tool.output | string | 工具输出 | JSON字符串 |

### 2. GenAI成本追踪 (Development → Development)

**稳定性**: Development (持续演进)

#### 新增属性

| 属性名 | 类型 | 描述 | 示例 |
|:-------|:----:|:-----|:-----|
| gen_ai.cost.currency | string | 成本货币单位 | USD, CNY, EUR |
| gen_ai.cost.amount | double | 成本金额 | 0.0023 |

#### 使用示例

`python
span.set_attribute("gen_ai.cost.currency", "USD")
span.set_attribute("gen_ai.cost.amount", 0.0023)
`

### 3. GenAI事件 (Development → Development)

保持Development状态，持续演进中。

---

## Database语义约定变更

### 新增数据库支持

| 数据库 | 系统标识符 | 状态 |
|:-------|:-----------|:----:|
| OpenSearch | opensearch | Experimental |
| CockroachDB | cockroachdb | Experimental |
| Neo4j | neo4j | Experimental |

#### 示例属性

`yaml
db.system: opensearch
db.opensearch.cluster.name: my-cluster
db.opensearch.index.name: logs-2026-03
db.opensearch.operation: search
`

---

## Mobile语义约定变更

### 新增设备信息属性

| 属性名 | 类型 | 描述 | 示例 |
|:-------|:----:|:-----|:-----|
| device.id | string | 设备唯一标识 | 550e8400-e29b-41d4-a716-446655440000 |
| device.model.identifier | string | 设备型号标识 | iPhone15,2 |
| device.model.name | string | 设备型号名称 | iPhone 15 Pro |

### 新增网络类型属性

| 属性名 | 类型 | 描述 | 示例 |
|:-------|:----:|:-----|:-----|
| network.connection.type | string | 网络连接类型 | wifi, cellular, ethernet |
| network.carrier.name | string | 运营商名称 | China Mobile |
| network.carrier.mcc | string | 移动国家码 | 460 |
| network.carrier.mnc | string | 移动网络码 | 01 |

---

## 稳定性状态变更

### 升级至Stable

| 约定 | 原状态 | 新状态 |
|:-----|:------:|:------:|
| HTTP Client Spans | Stable | Stable |
| HTTP Server Spans | Stable | Stable |
| Database Spans | Experimental | Experimental |

### 保持Development

| 约定 | 状态 | 说明 |
|:-----|:----:|:-----|
| GenAI Spans | Development | 持续快速迭代 |
| GenAI Events | Development | 持续快速迭代 |
| Agent Spans | **Draft** | v1.40新增 |

---

## 破坏性变更

### v1.40.0 Breaking Changes

**无重大破坏性变更**

- GenAI约定保持Development状态，允许API变更
- 新增属性均为可选
- 向后兼容

---

## 迁移指南

### 从v1.39.0迁移

1. **Agent语义约定** (可选):
   - 如使用AI Agent框架，可考虑实现新的Agent Span
   - 使用Draft属性标记实验性特性

2. **成本追踪** (可选):
   `python

   # 新增成本属性

   if hasattr(response, 'cost'):
       span.set_attribute("gen_ai.cost.currency", response.cost.currency)
       span.set_attribute("gen_ai.cost.amount", response.cost.amount)
   `

3. **数据库支持** (可选):
   - 使用新的db.system标识符

---

## 参考资源

- [v1.40.0 Release Notes](https://github.com/open-telemetry/semantic-conventions/releases/tag/v1.40.0)
- [GenAI Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)
- [Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)
- [Mobile Conventions](https://opentelemetry.io/docs/specs/semconv/mobile/)

---

**文档版本**: v1.0
**更新日期**: 2026年3月16日
**维护者**: OTLP项目团队
