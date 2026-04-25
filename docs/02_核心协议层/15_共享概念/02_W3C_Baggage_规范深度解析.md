# W3C Baggage 规范深度解析

> **标准来源**: W3C Propagation format for distributed context: Baggage — Candidate Recommendation Snapshot (2024-05-30)
> **发布机构**: W3C Distributed Tracing Working Group
> **核心目标**: 深度解析 W3C Baggage 规范的格式限制、传播语义，以及与 OpenTelemetry Baggage 实现的对齐关系

---

## 一、Baggage 的定位与价值

### 1.1 Baggage vs Trace Context

```text
分布式上下文传播的两大支柱:

┌─────────────────────┐      ┌─────────────────────┐
│   W3C Trace Context  │      │     W3C Baggage     │
├─────────────────────┤      ├─────────────────────┤
│  传播: trace-id      │      │  传播: 用户自定义属性  │
│         span-id      │      │                      │
│         trace-flags  │      │  用途: 业务上下文传递  │
│                      │      │                      │
│  用途: 分布式追踪关联 │      │  例子: 用户ID、租户ID  │
│                      │      │        实验组、请求来源│
└─────────────────────┘      └─────────────────────┘
         ↓                            ↓
         └──────────┬─────────────────┘
                    │
              共同承载于 HTTP 头
              一起跨服务边界传播
```

**关键区别**: Trace Context 是"系统追踪元数据"，Baggage 是"用户业务上下文"。Trace Context 由框架自动管理，Baggage 由应用开发者显式设置和消费。

### 1.2 为什么 Baggage 独立成标准？

Baggage 从 Trace Context 中独立出来，因为：

- **关注点分离**: 追踪系统不应强制要求处理业务属性
- **独立演化**: Baggage 可以有自己的版本和格式演进
- **更广泛的适用性**: 即使不使用分布式追踪，也可以使用 Baggage 传播上下文

---

## 二、Baggage 格式详解

### 2.1 HTTP 头格式

```text
Baggage 头格式:

baggage: {key1}={value1},{key2}={value2},{key3}={value3}

示例:
baggage: userId=12345,tenantId=acme-corporation,feature-flag=new-checkout

属性（Property）扩展（可选）:
baggage: key1=value1;property1;property2=value,key2=value2

示例（带属性）:
baggage: userId=12345;isPremium,tenantId=acme-corporation;region=us-east
```

### 2.2 编码规则

| 规则 | 说明 | 示例 |
|------|------|------|
| **Key 编码** | 必须进行 URL 编码（百分号编码）| `user id` → `user%20id` |
| **Value 编码** | 必须进行 URL 编码 | `hello world` → `hello%20world` |
| **分隔符** | 键值对之间用逗号 `,` 分隔 | `k1=v1,k2=v2` |
| **等号** | 键和值之间用等号 `=` 分隔 | `key=value` |
| **分号** | 属性之间用分号 `;` 分隔 | `key=value;prop1;prop2=abc` |

### 2.3 大小限制（核心规范）

W3C Baggage 规范定义了严格的限制，这是实现互操作的关键：

```text
┌─────────────────────────────────────────────────────────────┐
│  W3C Baggage 大小限制                                        │
├─────────────────────────────────────────────────────────────┤
│  总大小上限: 8192 字节（8 KB）                                │
│  单个条目上限: 4096 字节（4 KB）                              │
│  条目数量上限: 180 个（推荐限制，基于 8KB / 平均条目大小估算） │
│  键长度上限: 256 字符                                         │
│  值长度上限: 推荐不超过 1024 字符                             │
└─────────────────────────────────────────────────────────────┘

超过限制时的处理:
├── 如果 baggage 头总大小 > 8192 字节
│   └── 实现应该（SHOULD）从右侧截断（删除最后的键值对）
│       直到满足限制或为空
│
└── 注意: "应该"（SHOULD）不是"必须"（MUST）
    └── 某些实现可能选择完全丢弃 baggage 而非截断
```

### 2.4 与 OpenTelemetry Baggage 的限制对比

| 限制项 | W3C 规范 | OpenTelemetry 实现 | 差异说明 |
|--------|---------|-------------------|---------|
| 总大小 | 8192 bytes | 通常遵循 W3C | 一致 |
| 单条目大小 | 4096 bytes | 通常遵循 W3C | 一致 |
| 条目数量 | 无硬性上限（约 180 推荐）| 通常无硬性上限 | 一致 |
| 键字符集 | 限制较多（需 URL 编码）| 同 W3C | 一致 |
| 值中的逗号 | 必须编码为 `%2C` | 同 W3C | 一致 |
| 多值支持 | 不原生支持（需自行序列化）| 同 W3C | 一致 |

---

## 三、传播语义详解

### 3.1 传播保证

```text
Baggage 的传播语义:

┌─────────────────────────────────────────────────────────────┐
│  Baggage 是"尽力传播"（best-effort delivery）                 │
├─────────────────────────────────────────────────────────────┤
│  • 不保证跨越所有边界（某些代理可能剥离未知头）                │
│  • 不保证大小限制被严格遵守（各实现截断策略可能不同）           │
│  • 不保证键值对的顺序保持                                      │
│  • 不保证属性（property）被下游解析和理解                      │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 传播中的变异

Baggage 在传播过程中可能发生以下变化：

| 变异类型 | 说明 | 处理建议 |
|---------|------|---------|
| **截断** | 中间节点因大小限制删除尾部条目 | 将最关键的属性放在前面 |
| **重复键** | 规范未禁止重复键，但行为未定义 | 避免使用重复键 |
| **URL 编码差异** | 不同实现对编码严格程度不同 | 始终严格编码 |
| **属性丢失** | 某些实现可能忽略分号后的属性 | 不依赖属性进行核心逻辑判断 |

### 3.3 多值传播

W3C Baggage 不原生支持一个键对应多个值。如需传递列表，需自行序列化：

```text
不推荐:
baggage: tags=tag1,tags=tag2,tags=tag3  ← 重复键，行为未定义

推荐方案1（逗号分隔）:
baggage: tags=tag1%2Ctag2%2Ctag3       ← 值内的逗号必须编码

推荐方案2（JSON）:
baggage: tags=%5B%22tag1%22%2C%22tag2%22%5D  ← JSON 数组，URL 编码
解码后: tags=["tag1","tag2"]
```

---

## 四、与 OpenTelemetry Baggage 的对齐

### 4.1 OTel Baggage API

OpenTelemetry 提供了语言无关的 Baggage API：

```java
// Java: Baggage 操作
import io.opentelemetry.api.baggage.Baggage;
import io.opentelemetry.api.baggage.BaggageEntry;

// 创建 Baggage
Baggage baggage = Baggage.builder()
    .put("userId", "12345")
    .put("tenantId", "acme-corporation")
    .put("feature-flag", "new-checkout")
    .build();

// 使 Baggage 在当前上下文生效
Scope scope = baggage.makeCurrent();
try {
    // 当前上下文中的 Baggage 会自动通过 TextMapPropagator 传播
    // 对下游服务可见
} finally {
    scope.close();
}

// 读取 Baggage
String userId = Baggage.current().getEntryValue("userId");
```

```python
# Python: Baggage 操作
from opentelemetry import baggage
from opentelemetry.context import attach, detach

# 设置 Baggage
token = attach(baggage.set_baggage("userId", "12345"))
try:
    # Baggage 在当前上下文中传播
    pass
finally:
    detach(token)

# 读取 Baggage
user_id = baggage.get_baggage("userId")
```

### 4.2 Baggage 与 Span 属性的关系

| 机制 | 作用域 | 传播性 | 使用场景 |
|------|--------|--------|---------|
| **Baggage** | Context（跨 Span） | 跨进程传播 | 需要在整个调用链中共享的业务上下文 |
| **Span 属性** | 单个 Span | 不跨 Span 传播 | 仅描述当前操作的元数据 |

**关键规则**: Baggage **不会**自动变成 Span 属性。如果希望 Baggage 中的值也记录为 Span 属性，必须显式设置：

```java
// 将 Baggage 值复制到 Span 属性（如果需要）
Span span = Span.current();
Baggage.current().asMap().forEach((key, entry) -> {
    span.setAttribute("baggage." + key, entry.getValue());
});
```

### 4.3 OTel W3CBaggagePropagator

OpenTelemetry 默认使用 `W3CBaggagePropagator` 进行 Baggage 传播：

```java
// Java: 默认 Baggage Propagator
TextMapPropagator baggagePropagator = W3CBaggagePropagator.getInstance();

// 注入（将 Baggage 写入 HTTP 头）
baggagePropagator.inject(context, request, setter);

// 提取（从 HTTP 头解析 Baggage）
Context context = baggagePropagator.extract(Context.current(), request, getter);
```

**注意**: OpenTelemetry 的 `CompositePropagator` 通常同时包含 `W3CTraceContextPropagator` 和 `W3CBaggagePropagator`，确保 traceparent 和 baggage 同时传播：

```java
TextMapPropagator propagator = TextMapPropagator.composite(
    W3CTraceContextPropagator.getInstance(),
    W3CBaggagePropagator.getInstance()
);
```

---

## 五、安全与隐私

### 5.1 Baggage 的安全风险

Baggage 传播用户定义的数据，存在以下风险：

```text
风险1: 敏感信息泄露
├── 场景: 将 JWT Token 放入 Baggage
├── 问题: Baggage 会明文传播到所有下游服务
└── 建议: 绝不将密码、Token、密钥放入 Baggage

风险2: 信息注入攻击
├── 场景: 恶意客户端设置伪造的 userId Baggage
├── 问题: 下游服务可能盲目信任 Baggage 值
└── 建议: 下游服务应验证 Baggage 值的可信度

风险3: 拒绝服务（DoS）
├── 场景: 恶意客户端发送超大 Baggage 头（如 8KB）
├── 问题: 增加网络开销和内存占用
└── 建议: 严格实施 8192 字节限制
```

### 5.2 安全使用指南

| 建议 | 说明 |
|------|------|
| 仅放入**非敏感**的标识信息 | 用户 ID、租户 ID、请求来源是安全的；密码和 Token 不是 |
| 下游服务验证 Baggage | 不要盲信上游传入的 Baggage 值，特别是涉及权限的属性 |
| 限制 Baggage 大小 | 在应用层设置更严格的限制（如最大 2KB）|
| 审计 Baggage 内容 | 在网关层记录通过的关键 Baggage 键值对 |
| 清理出站 Baggage | 对外部第三方服务调用时，考虑剥离内部 Baggage |

---

## 六、常见问题与陷阱

### 6.1 Baggage 丢失的常见原因

| 原因 | 说明 | 排查方法 |
|------|------|---------|
| 代理剥离未知头 | 某些安全代理会删除非标准 HTTP 头 | 检查代理配置，将 `baggage` 加入白名单 |
| 大小超限被截断 | 某些实现直接丢弃整个 baggage | 控制 baggage 数量和大小 |
| 未配置 Baggage Propagator | SDK 默认可能只启用 traceparent 传播 | 确认 `OTEL_PROPAGATORS` 包含 `baggage` |
| 跨语言编码差异 | 某些语言实现编码不严格 | 测试跨语言传播，确认编码一致性 |
| 异步上下文丢失 | 异步线程切换时 Context 未传递 | 确保异步框架正确传递 Context |

### 6.2 调试技巧

```text
排查 Baggage 传播问题:

1. 在入口服务打印 Baggage 内容
   Baggage.current().asMap().forEach((k, v) -> log.info("baggage: {}={}", k, v.getValue()));

2. 在下游服务打印接收到的 Baggage
   比较入口和下游的值是否一致

3. 抓包检查 HTTP 头
   确认请求中是否包含 baggage 头，内容是否正确

4. 检查 SDK 配置
   确认 Propagator 列表包含 W3CBaggagePropagator
```

---

## 七、检查清单

在实现或验证 Baggage 传播时，确认：

- [ ] 所有 Baggage 键值对正确进行了 URL 编码
- [ ] Baggage 总大小控制在 8192 字节以内
- [ ] 最关键的键值对放在前面（防止截断时丢失）
- [ ] `OTEL_PROPAGATORS` 环境变量包含 `baggage`
- [ ] 下游服务验证 Baggage 值的可信度（不盲信）
- [ ] 敏感信息（密码、Token、密钥）未放入 Baggage
- [ ] 异步调用正确传递了 Context（含 Baggage）
- [ ] 跨服务调用的代理/网关未剥离 `baggage` 头

---

## 八、参考资源

- W3C Baggage Specification: Candidate Recommendation Snapshot (2024-05-30)
- OpenTelemetry Specification: Baggage
- OpenTelemetry Specification: Propagators
- 本项目: `docs/02_核心协议层/15_共享概念/01_Baggage详解.md`

---

> **总结**: W3C Baggage 规范定义了分布式系统中用户自定义上下文的标准传播格式。`8192` 字节总限制和 `4096` 字节单条目限制是确保互操作的核心约束。OpenTelemetry 的 Baggage API 与 W3C 规范深度对齐，但开发者需要注意 Baggage **不会**自动成为 Span 属性，且需要在安全、大小和编码方面遵循最佳实践。
