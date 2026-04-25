# Feature Flags 语义约定详解

> **标准来源**: OpenTelemetry Semantic Conventions v1.40.0 — Feature Flags
> **稳定性状态**: 实验性 (Experimental) → 候选稳定 (Release Candidate) 过渡中
> **核心目标**: 统一特性开关（功能开关）评估事件的可观测性语义

---

## 一、背景与价值

### 1.1 什么是特性开关？

特性开关（Feature Flags / Feature Toggles）是现代软件交付的核心技术，允许团队在不部署新代码的情况下启用或禁用功能：

```text
用户请求 → 特性开关评估 → 决策（开/关/灰度）→ 执行对应代码路径
                │
                └── 可观测性需求：
                    ├── 开关是否生效？
                    ├── 哪些用户被分配到了实验组？
                    ├── 开关对性能/错误率的影响？
                    └── 实验（A/B测试）结果归因
```

### 1.2 为什么需要专门的语义约定？

在没有标准化之前，各团队对特性开关的可观测性实现五花八门：

```text
团队A: span.setAttribute("feature_flag", "new-checkout")
团队B: span.setAttribute("ff_enabled", true)
团队C: span.setAttribute("toggles.new_checkout", "on")
团队D: 记录在日志中，不在追踪里
```

这导致：

- 无法跨团队/服务统一查询开关影响
- 无法建立特性开关与业务指标（转化率、错误率）的关联
- 实验平台难以自动归因

OpenTelemetry Feature Flags 语义约定解决了这些问题。

---

## 二、核心属性定义

### 2.1 属性总览

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `feature_flag.key` | string | 特性开关的唯一标识键 | 必须 |
| `feature_flag.provider_name` | string | 特性开关提供方的名称（如 "launchdarkly"）| 推荐 |
| `feature_flag.context.id` | string | 评估上下文的标识（如用户ID、设备ID）| 可选 |
| `feature_flag.evaluated.reason` | string | 评估原因（如 "targeted", "default", "error"）| 可选 |
| `feature_flag.variant` | string | 分配的变体名称（用于多变量测试）| 推荐 |

### 2.2 属性详细说明

#### `feature_flag.key`

特性开关的**唯一标识符**。这是最重要的属性，用于在所有遥测数据中标识涉及的开关。

```text
最佳实践:
├── 使用与特性开关管理系统中一致的键名
├── 使用点号分隔的层次命名（如 `checkout.new-flow-v2`）
├── 避免使用空格和特殊字符
└── 保持稳定，不因版本迭代而频繁变更键名

示例值:
├── "checkout.new-payment-gateway"
├── "search.ai-ranking-experiment"
└── "ui.dark-mode"
```

#### `feature_flag.provider_name`

标识提供特性开关评估服务的厂商或系统：

| 值 | 说明 |
|---|------|
| `launchdarkly` | LaunchDarkly |
| `split` | Split.io |
| `unleash` | Unleash |
| `flagsmith` | Flagsmith |
| `custom` | 自研系统 |
| `envoy` | Envoy Proxy 特性开关 |

这有助于在多厂商环境中区分数据来源。

#### `feature_flag.evaluated.reason`

说明为什么得到特定的评估结果：

| 值 | 说明 |
|---|------|
| `static` | 开关配置为全局静态值 |
| `default` | 未匹配任何规则，回退到默认值 |
| `targeted` | 匹配了定向规则（如特定用户群）|
| `split` | 基于分桶/百分比分配 |
| `conditional` | 基于动态条件评估 |
| `error` | 评估过程中出错，回退到默认值 |
| `unknown` | 原因未知 |

#### `feature_flag.variant`

用于**多变量测试（A/B/N 测试）**场景，标识用户被分配到的具体变体：

```text
示例:
├── 开关: search.algorithm-experiment
│   ├── variant: "control"      → 对照组（现有算法）
│   ├── variant: "treatment-a"  → 实验组A（新算法v1）
│   └── variant: "treatment-b"  → 实验组B（新算法v2）
```

---

## 三、使用模式

### 3.1 基本模式：开关评估事件

当应用代码评估一个特性开关时，**应该**创建一个事件（Event）记录在当前的 Span 上：

```java
// Java 示例
Span span = Span.current();

boolean newCheckoutEnabled = featureFlags.isEnabled("checkout.new-payment-gateway", userId);

// 记录特性开关评估事件
span.addEvent("feature_flag", Attributes.builder()
    .put("feature_flag.key", "checkout.new-payment-gateway")
    .put("feature_flag.provider_name", "launchdarkly")
    .put("feature_flag.variant", newCheckoutEnabled ? "on" : "off")
    .put("feature_flag.evaluated.reason", "targeted")
    .build());
```

```python
# Python 示例
from opentelemetry.trace import get_current_span

variant = feature_flags.get_variant("search.ai-ranking-experiment", user_context)

current_span = get_current_span()
current_span.add_event(
    "feature_flag",
    attributes={
        "feature_flag.key": "search.ai-ranking-experiment",
        "feature_flag.provider_name": "split",
        "feature_flag.variant": variant,
        "feature_flag.evaluated.reason": "split",
    }
)
```

### 3.2 进阶模式：将开关属性提升到 Span 级别

如果特性开关对当前请求的处理路径有**决定性影响**，建议将开关信息作为 Span 属性：

```java
// 当开关决定了完全不同的代码路径时
Span span = tracer.spanBuilder("processCheckout")
    .setAttribute("feature_flag.key", "checkout.new-payment-gateway")
    .setAttribute("feature_flag.variant", "stripe-v2")
    .startSpan();
```

这样可以在追踪后端中直接按开关值过滤和分组。

### 3.3 A/B 测试归因模式

在实验场景中，**应该**确保实验标识传播到所有下游服务：

```text
服务A (入口层)
├── 评估开关: search.algorithm-experiment
├── 变体: treatment-a
├── 将 feature_flag.variant=treatment-a 写入 Baggage
│       └── 这样下游所有服务都能知道当前请求属于哪个实验组
└── 所有子 Span 都携带实验属性

服务B (下游)
├── 从 Baggage 读取实验变体
├── 在自己的 Span 中记录相同的 feature_flag 属性
└── 确保实验组的用户体验一致性
```

```java
// 在入口服务中将实验变体写入 Baggage
Baggage.current()
    .toBuilder()
    .put("experiment.search-algorithm", "treatment-a")
    .build()
    .makeCurrent();

// 下游服务读取并记录
String experimentVariant = Baggage.current().getEntryValue("experiment.search-algorithm");
span.setAttribute("feature_flag.variant", experimentVariant);
```

---

## 四、与现有内容的关联

### 4.1 与本项目已有内容的衔接

本项目在以下文档中已提及特性开关：

- `docs/02_核心协议层/15_共享概念/01_Baggage详解.md` — 特性开关传播示例
- `docs/02_核心协议层/21_语义约定/04_Semantic_Conventions_v1.40.0_迁移指南.md` — 迁移指南中列出 Feature Flags

本文档是对上述提及的**系统化深化**，提供了完整的属性定义、使用模式和最佳实践。

### 4.2 与 Baggage 的关系

| 机制 | 适用场景 | 生命周期 |
|------|---------|---------|
| `feature_flag.*` 属性 | 记录评估结果 | Span 级别，随 Span 导出 |
| `Baggage` | 传播实验上下文 | 跨 Span 传播，可传递到下游服务 |

**推荐组合**：在入口层同时做两件事：

1. 用 `feature_flag.*` 属性记录评估结果
2. 用 `Baggage` 传播关键实验标识，确保下游可见

---

## 五、后端查询与分析

### 5.1 常用查询模式

在 Jaeger / Grafana Tempo / 其他追踪后端中：

```text
查询1: 特定开关的影响范围
├── 条件: feature_flag.key = "checkout.new-payment-gateway"
└── 聚合: 按 feature_flag.variant 分组，统计延迟和错误率

查询2: 实验组对比
├── 条件: feature_flag.key = "search.ai-ranking-experiment"
├── 分组: feature_flag.variant
└── 对比: treatment-a vs treatment-b 的转化率差异

查询3: 开关故障排查
├── 条件: feature_flag.evaluated.reason = "error"
└── 用途: 发现特性开关系统的评估异常
```

### 5.2 与指标（Metrics）的关联

除了追踪（Traces），特性开关数据**可以**通过指标暴露：

```text
指标名称: feature_flag.evaluation.count
维度:
├── feature_flag.key
├── feature_flag.variant
├── feature_flag.provider_name
└── feature_flag.evaluated.reason

用途:
├── 实时监控开关评估量
├── 发现异常的评估错误率
└── 实验组流量分配监控
```

---

## 六、检查清单

在实现特性开关可观测性时，确认：

- [ ] 使用了标准化的 `feature_flag.key` 命名
- [ ] 记录了 `feature_flag.provider_name` 以便多厂商环境识别
- [ ] A/B 测试场景记录了 `feature_flag.variant`
- [ ] 评估异常场景记录了 `feature_flag.evaluated.reason = "error"`
- [ ] 跨服务实验通过 Baggage 传播了实验上下文
- [ ] 开关属性与业务 Span（如 HTTP 请求、DB 查询）正确关联
- [ ] 后端查询和仪表盘已配置按开关维度分组分析

---

## 七、参考资源

- OpenTelemetry Semantic Conventions: Feature Flags
- OpenTelemetry Baggage 规范
- 本项目: `docs/02_核心协议层/15_共享概念/01_Baggage详解.md`

---

> **总结**: Feature Flags 语义约定将特性开关从"黑盒配置"提升为"可观测的决策点"。通过标准化的 `feature_flag.*` 属性，团队可以精确度量每个开关对系统行为、性能和用户体验的影响，是实现数据驱动发布和实验平台的基础。
