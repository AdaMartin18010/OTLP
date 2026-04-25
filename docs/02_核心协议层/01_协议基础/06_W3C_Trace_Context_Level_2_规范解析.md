# W3C Trace Context Level 2 规范解析

> **标准来源**: W3C Trace Context Level 2 — Candidate Recommendation (2024-03-28)
> **发布机构**: W3C Distributed Tracing Working Group
> **核心目标**: 深度解析 W3C Trace Context Level 2 相对于 Level 1 的演进，以及与 OpenTelemetry 的集成关系

---

## 一、W3C Trace Context 标准定位

### 1.1 标准层级

```text
┌─────────────────────────────────────────────────────────────┐
│  W3C 标准成熟度阶梯                                          │
├─────────────────────────────────────────────────────────────┤
│  工作草案 (Working Draft)                                    │
│      ↓                                                       │
│  候选推荐标准 (Candidate Recommendation) ← Trace Context L2   │
│      ↓                                                       │
│  提议推荐标准 (Proposed Recommendation)                       │
│      ↓                                                       │
│  正式推荐标准 (W3C Recommendation) ← 预计 2025 Q4 达成        │
└─────────────────────────────────────────────────────────────┘
```

W3C Trace Context 是目前**与 OpenTelemetry 关系最密切的正式 Web 标准**，OTel 默认使用 W3C `traceparent` 和 `tracestate` 作为传播格式。

### 1.2 与其他标准的关系

```text
OpenTelemetry 传播体系:
├── 默认传播器: W3C Trace Context (traceparent + tracestate)
├── 默认传播器: W3C Baggage
├── 可选传播器: B3 (Zipkin 生态兼容)
├── 可选传播器: Jaeger
└── 自定义传播器: 厂商/组织自定义

W3C Trace Context 标准家族:
├── Trace Context Level 1 (2019) — 首个稳定版本
├── Trace Context Level 2 (2024-03) — 当前候选推荐
├── Trace Context: AMQP protocol binding (Working Draft)
└── Trace Context: MQTT protocol binding (Working Draft)
```

---

## 二、Trace Context Level 2 的核心变更

### 2.1 Level 1 vs Level 2 对比

| 特性 | Level 1 (2019) | Level 2 (2024) |
|------|---------------|----------------|
| **traceparent 版本** | `00` | `00`（保持兼容，增加未来版本协商机制）|
| **trace-flags 定义** | 仅 bit 0（sampled）有定义 | 增加保留位和未来扩展机制说明 |
| **tracestate 限制** | 最多 32 个键值对 | 增加更明确的限制和截断规则 |
| **版本协商** | 无 | 新增版本不匹配时的协商行为 |
| **篡改检测** | 无 | 明确规范了对 traceparent 篡改的检测与恢复 |
| **安全隐私** | 基础提及 | 增加隐私风险（fingerprinting）的详细讨论 |
| **多协议绑定** | HTTP only | 开始定义 AMQP/MQTT 绑定（独立文档）|

### 2.2 traceparent 格式详解

```text
traceparent 头格式:

traceparent: {version}-{trace-id}-{parent-id}-{trace-flags}

示例:
traceparent: 00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01
            ││ └────────────────trace-id──────────────┘ └─parent-id──┘ │└─flags
            │└─version                                             │
            └─版本号（2位十六进制）                                  └─采样标志

字段说明:
├── version (2 hex chars)
│   ├── "00": 当前版本
│   └── "ff": 保留，表示版本协商失败
│
├── trace-id (32 hex chars = 16 bytes)
│   ├── 全局唯一标识一个分布式追踪
│   ├── 全零表示无效: 00000000000000000000000000000000
│   └── OpenTelemetry 使用随机生成的 16 字节
│
├── parent-id (16 hex chars = 8 bytes)
│   ├── 标识当前调用方（父 Span）的 ID
│   ├── 全零表示无效: 0000000000000000
│   └── 接收方应将其替换为自己的 Span ID
│
└── trace-flags (2 hex chars = 1 byte)
    ├── bit 0 (LSB): sampled 标志
    │   ├── 1 = 已采样（建议记录）
    │   └── 0 = 未采样（建议不记录）
    ├── bits 1-7: 当前保留，必须为 0
    │   └── Level 2 为未来扩展预留
    └── 注意: sampled=1 不强制要求记录，是"建议"
```

### 2.3 trace-flags 的精确语义

**常见误解**: `sampled=1` 意味着"这个 Span 必须被采样"。

**实际语义**: `sampled=1` 是**提示（hint）**，表示上游已采样，建议下游也采样。但下游的 Sampler 可以独立决策：

```text
场景分析:

场景1: 上游 sampled=1, 下游 Sampler 决策
├── 结果A: 下游尊重上游，继续采样 → Span 被记录
├── 结果B: 下游配置为 NeverSample → Span 不被记录
└── 结论: sampled=1 不是强制命令

场景2: 上游 sampled=0, 下游 Sampler 决策
├── 结果A: 下游尊重上游，不采样 → Span 不被记录
├── 结果B: 下游使用 ParentBased Sampler，跟随父 Span → 不记录
└── 结果C: 下游使用独立的概率采样器（如 10%）→ 可能记录

OpenTelemetry 默认行为:
├── ParentBased Sampler:
│   ├── remote_parent_sampled → 采样（跟随上游）
│   └── remote_parent_not_sampled → 不采样（跟随上游）
└── 这是默认行为，但用户可配置
```

### 2.4 tracestate 的演进

`tracestate` 是厂商扩展字段，允许多个追踪系统在同一个请求中传递各自的上下文数据：

```text
tracestate 头格式:

tracestate: {vendor1}={value1},{vendor2}={value2},{vendor3}={value3}

示例:
tracestate: congo=tucorr,key1=val1,key2=val2

traceresponse: congo=tucorr,key1=val1  ← Level 2 新增的响应头

Level 2 的关键改进:
├── 限制: 最多 32 个键值对
├── 单个键值对: 键最多 256 字符，值最多 256 字符
├── 截断规则: 当超出限制时，从右侧截断（删除最后的键值对）
├── 篡改检测: 如果 traceparent 被中间件修改但 tracestate 未同步更新，
│             接收方应检测并可能重置 tracestate
└── traceresponse: 新增响应头，允许服务端回传 tracestate 更新
```

---

## 三、版本协商机制（Level 2 新增）

### 3.1 版本不匹配场景

当请求的 `traceparent` 版本高于接收方支持的版本时：

```text
场景: 请求携带 traceparent: 01-... (版本 01)
      接收方仅支持版本 00

Level 2 规范要求:
├── 尝试解析: 如果版本 01 的格式与 00 兼容，尝试按已知版本解析
├── 失败处理: 如果无法解析，应：
│   ├── 重置 traceparent 为全新值（如同没有上游上下文）
│   └── 可选: 保留 tracestate（如果认为安全）
└── 响应: 在 traceresponse 中使用接收方支持的版本

场景: 请求携带 traceparent: 00-... (版本 00)
      接收方支持版本 01

Level 2 规范要求:
├── 按版本 00 的规则解析
├── 在内部处理时使用更高版本的特性
└── 响应: 在 traceresponse 中使用版本 01
```

### 3.2 未来版本扩展策略

W3C 明确表示未来版本将采用**向后兼容**的扩展策略：

- 更高版本应能解析更低版本的 traceparent
- 新增字段将使用 tracestate 或 trace-flags 的保留位
- 不计划在短期内发布版本 01（当前 `00` 足够）

---

## 四、安全与隐私考虑（Level 2 强化）

### 4.1 指纹追踪风险（Fingerprinting）

Level 2 新增了关于隐私风险的讨论：

```text
风险: 恶意网站利用 traceparent 跨站追踪用户

场景:
├── 用户访问 site-a.com，site-a 设置 traceparent
├── 同一用户访问 site-b.com，site-b 发现相同的 trace-id
└── 结论: site-b 知道这是同一个用户

缓解措施:
├── 浏览器应限制跨域 traceparent 传播
├── 隐私模式下应禁用或重置 traceparent
├── 第三方脚本不应读取或修改第一方的 traceparent
└── 用户代理（浏览器）可以选择性地过滤 traceparent
```

### 4.2 篡改检测与恢复

中间代理（如负载均衡器、API 网关）可能修改 traceparent：

```text
篡改类型:
├── 版本号被修改（如从 00 改为 ff）
├── trace-id 被替换为全零（表示无效）
├── trace-flags 被修改（如 sampled 位翻转）
└── tracestate 被截断或清空

检测与恢复:
├── 接收方应验证 traceparent 格式
├── 发现无效格式时，重置为新的有效 traceparent
├── 不要尝试"修复"部分有效的 traceparent（避免传播错误）
└── 记录篡改事件（通过 metrics 或 logs）
```

---

## 五、与 OpenTelemetry 的集成

### 5.1 OTel 中的 W3C Propagator

OpenTelemetry 默认使用 `W3CTraceContextPropagator`：

```java
// Java: 默认即 W3C
TextMapPropagator propagator = W3CTraceContextPropagator.getInstance();

// 注入
propagator.inject(context, request, setter);

// 提取
Context context = propagator.extract(Context.current(), request, getter);
```

```javascript
// Node.js: 默认即 W3C
const { W3CTraceContextPropagator } = require('@opentelemetry/core');
const propagator = new W3CTraceContextPropagator();
```

### 5.2 OTel Sampler 与 trace-flags 的交互

```java
// ParentBased Sampler 是默认采样器，与 W3C sampled 标志紧密协作
Sampler sampler = Sampler.parentBased(
    Sampler.traceIdRatioBased(0.1),  // 根 Span 的采样策略
    // remote_parent_sampled: 当上游 sampled=1 时的策略
    Sampler.alwaysOn(),
    // remote_parent_not_sampled: 当上游 sampled=0 时的策略
    Sampler.alwaysOff(),
    // local_parent_sampled: 本进程内父 Span 已采样时的策略
    Sampler.alwaysOn(),
    // local_parent_not_sampled: 本进程内父 Span 未采样时的策略
    Sampler.alwaysOff()
);
```

### 5.3 tracestate 在 OTel 中的使用

OpenTelemetry SDK 对 `tracestate` 的处理：

```text
传播行为:
├── 默认传播: OTel 的 SpanContext 包含 tracestate
├── 提取: 从传入请求中解析 tracestate，存入 SpanContext
├── 注入: 将 SpanContext 中的 tracestate 写入传出请求
└── 修改: 当前 OTel 实现通常不主动修改 tracestate 内容

厂商扩展:
├── 云厂商可以在 tracestate 中注入自己的追踪上下文
├── 例如 AWS X-Ray: tracestate: aws=Root=1-...;Parent=...;Sampled=1
├── OTel 会透传这些值，保持与厂商系统的互操作
└── 但 OTel 自身不依赖 tracestate 进行核心追踪
```

---

## 六、HTTP 协议绑定细节

### 6.1 请求头规范

```text
请求头（客户端 → 服务端）:
├── traceparent: 00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01
└── tracestate: congo=tucorr,key1=val1

响应头（服务端 → 客户端, Level 2 新增）:
└── traceresponse: congo=tucorr,key1=val1

注意:
├── traceparent 和 tracestate 都应使用小写的头名称
├── 某些 HTTP 框架可能自动将头名称转为小写或大写
├── traceresponse 是 Level 2 新增的响应头，用于服务端回传上下文更新
└── 不是所有 OTel 实现都已支持 traceresponse
```

### 6.2 头名称变体处理

```text
HTTP/1.1 和 HTTP/2 对头名称大小写的处理不同:
├── HTTP/1.1: 头名称大小写不敏感
├── HTTP/2: 头名称必须为小写
└── 实现应统一使用小写: traceparent, tracestate, traceresponse
```

---

## 七、检查清单

在实现或验证 W3C Trace Context 支持时，确认：

- [ ] 正确解析 traceparent 的四个字段（version, trace-id, parent-id, trace-flags）
- [ ] 验证 trace-id 和 parent-id 不为全零
- [ ] 从传入请求中提取 traceparent 后，将 parent-id 替换为当前 Span ID
- [ ] 正确传播 tracestate，不丢失已有的厂商键值对
- [ ] 当 traceparent 格式无效时，生成新的 traceparent 而非传播错误
- [ ] trace-flags 的保留位（bits 1-7）在处理后保持原样（不修改未知位）
- [ ] （Level 2）支持 traceresponse 响应头（如适用）
- [ ] 在多协议场景（HTTP、gRPC、消息队列）中保持一致的传播行为

---

## 八、参考资源

- W3C Trace Context Level 2: Candidate Recommendation
- W3C Trace Context Protocols Registry
- OpenTelemetry Specification: Propagators
- OpenTelemetry W3CTraceContextPropagator 实现文档

---

> **总结**: W3C Trace Context Level 2 在保持与 Level 1 完全兼容的基础上，增加了版本协商机制、篡改检测、隐私风险讨论和 traceresponse 响应头。作为 OpenTelemetry 的默认传播格式，深入理解 Level 2 的演进对于构建健壮、安全、跨厂商兼容的分布式追踪至关重要。
