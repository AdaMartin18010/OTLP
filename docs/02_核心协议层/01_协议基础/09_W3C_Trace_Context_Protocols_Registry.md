# W3C Trace Context Protocols Registry

> **标准来源**: W3C Trace Context Protocols Registry — Working Group Note
> **发布机构**: W3C Distributed Tracing Working Group
> **核心目标**: 导航 W3C 注册的 Trace Context 协议绑定，帮助开发者选择正确的传播实现

---

## 一、什么是 Protocols Registry？

W3C Trace Context Protocols Registry 是一个**官方注册表**，记录各网络协议对 W3C Trace Context 的绑定规范。它类似于 IANA 的端口注册表或 MIME 类型注册表，为分布式追踪社区提供参考。

```text
注册表作用:
├── 提供权威的协议绑定规范索引
├── 帮助开发者确认"某个协议是否支持 Trace Context"
├── 为新协议绑定提供注册入口
└── 追踪各协议绑定的标准化成熟度
```

---

## 二、已注册协议绑定总览

### 2.1 注册表状态（截至 2026-04）

| 协议 | 规范文档 | W3C 状态 | 实际采用度 |
|------|---------|---------|-----------|
| **HTTP** | Trace Context Level 1/2 | Candidate Recommendation | ⭐⭐⭐⭐⭐ 广泛采用 |
| **AMQP** | Trace Context: AMQP binding | Working Draft | ⭐⭐⭐ 逐步采用 |
| **MQTT** | Trace Context: MQTT binding | Working Draft | ⭐⭐ 早期阶段 |
| **其他** | 待社区提案 | — | — |

### 2.2 HTTP 绑定（最成熟）

```text
HTTP 绑定规范:
├── 请求头: traceparent, tracestate
├── 响应头: traceresponse (Level 2 新增)
├── 默认传播器: W3CTraceContextPropagator
└── 采用状态: 生产就绪，OpenTelemetry 默认使用

参考文档:
└── 本项目: docs/02_核心协议层/01_协议基础/06_W3C_Trace_Context_Level_2_规范解析.md
```

### 2.3 AMQP 绑定（开发中）

```text
AMQP 绑定规范:
├── AMQP 1.0: Application Properties (traceparent, tracestate)
├── AMQP 0-9-1: Headers (traceparent, tracestate)
├── 主要实现: RabbitMQ, Azure Service Bus
└── 采用状态: Working Draft，可生产使用

参考文档:
└── 本项目: docs/02_核心协议层/01_协议基础/08_W3C_Trace_Context_AMQP_绑定规范.md
```

### 2.4 MQTT 绑定（早期）

```text
MQTT 绑定规范要点:
├── MQTT v3.1.1 / v5.0 支持用户属性（User Properties）
├── traceparent 放入 MQTT User Properties
├── 限制: MQTT 消息头大小有限（通常 < 64KB 总消息）
├── 主要实现: IoT 场景（AWS IoT Core, Azure IoT Hub）
└── 采用状态: Working Draft，IoT 场景试用

MQTT v5.0 示例:
├── PUBLISH 消息:
│   └── User Properties:
│       ├── traceparent: 00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01
│       └── tracestate: congo=tucorr
│
└── 限制注意:
    ├── MQTT v3.1.1 不支持 User Properties
    │   └── 需要使用 payload 或 topic 编码（不推荐）
    └── 物联网设备资源受限，完整 traceparent 可能增加带宽负担
```

---

## 三、协议绑定对比矩阵

| 维度 | HTTP | AMQP | MQTT |
|------|------|------|------|
| **传输层** | TCP | TCP | TCP |
| **消息模式** | 请求-响应 | 队列（点对点/发布订阅）| 发布订阅 |
| **头容量** | 大（通常 8KB-16KB）| 大 | 小（建议 < 1KB）|
| **traceparent 位置** | HTTP Header | Application Properties / Headers | User Properties (v5) |
| **双向传播** | 支持（traceresponse）| 困难（消费者不直接回复生产者）| 不支持 |
| **中间件影响** | 代理可能剥离头 | 代理通常保留属性 | Broker 保留 User Properties |
| **典型场景** | REST/gRPC API | 企业消息队列 | IoT、移动推送 |
| **OpenTelemetry 支持** | 原生默认 | Messaging Semantic Conventions | 实验性 |

---

## 四、如何选择传播协议？

### 4.1 决策树

```text
应用使用什么通信机制？
├── HTTP/gRPC/REST
│   └── 使用 W3C Trace Context HTTP 绑定
│       └── OpenTelemetry 默认支持，无需额外配置
│
├── 消息队列（RabbitMQ, ActiveMQ, Service Bus）
│   └── 使用 AMQP 绑定
│       ├── AMQP 1.0: Application Properties
│       └── AMQP 0-9-1: Headers
│
├── IoT / MQTT（HiveMQ, Mosquitto, AWS IoT）
│   └── 使用 MQTT v5.0 User Properties
│       └── 注意消息大小限制
│
├── 自定义协议（TCP 二进制、UDP、WebSocket）
│   └── 参考 W3C 规范原则，自定义适配
│       ├── 找到合适的元数据载体
│       ├── 使用标准 traceparent 格式
│       └── 考虑向后提交到 W3C Registry
│
└── 遗留系统（无协议头机制）
    └── 使用 Baggage 或应用层协议扩展
```

---

## 五、向 W3C Registry 提交新协议

如果某个协议尚未注册但社区有需求，可以提交提案：

```text
提交流程:
1. 起草协议绑定规范文档
   ├── 描述协议的消息/头结构
   ├── 定义 traceparent/tracestate 的映射位置
   └── 提供实现示例

2. 在 W3C Distributed Tracing WG 会议中讨论
   ├── 发送邮件到 public-trace-context@w3.org
   ├── 参加双周会议介绍提案
   └── 收集实现者反馈

3. 形成 Working Draft
   ├── WG 共识后发布为工作草案
   └── 进入 Registry

4. 推动实现和测试
   ├── 鼓励 SDK 厂商实现
   └── 参与互操作性测试
```

---

## 六、检查清单

- [ ] 确认所用协议是否已在 W3C Registry 中注册
- [ ] 如已注册，遵循规范中的绑定方式
- [ ] 如未注册，评估是否有标准绑定草案可参考
- [ ] 自定义绑定时，保持 traceparent/tracestate 格式不变
- [ ] 测试中间件/代理不会剥离传播属性
- [ ] 关注 W3C Registry 更新，及时跟进新协议支持

---

## 七、参考资源

- W3C Trace Context Protocols Registry
- W3C Distributed Tracing Working Group
- OpenTelemetry Propagators API
- 本项目 W3C 相关文档:
  - `06_W3C_Trace_Context_Level_2_规范解析.md`
  - `08_W3C_Trace_Context_AMQP_绑定规范.md`
  - `02_W3C_Baggage_规范深度解析.md`

---

> **总结**: W3C Trace Context Protocols Registry 是分布式追踪跨协议互操作的基础设施。目前 HTTP 绑定最成熟（Candidate Recommendation），AMQP 和 MQTT 处于 Working Draft 阶段。开发者在选择传播机制时，应优先使用已注册的标准绑定，确保跨服务和跨厂商的追踪上下文互通。
