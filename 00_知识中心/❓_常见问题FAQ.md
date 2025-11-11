# ❓ OTLP常见问题FAQ

> **最后更新**: 2025-10-26  
> **问题数量**: 50+个  
> **分类**: 10个主题

---

## 📋 问题分类

- [1. 基础概念](#1-基础概念)
- [2. 安装和配置](#2-安装和配置)
- [3. 数据采集](#3-数据采集)
- [4. Context传播](#4-context传播)
- [5. 采样策略](#5-采样策略)
- [6. 性能问题](#6-性能问题)
- [7. 故障排查](#7-故障排查)
- [8. 数据存储](#8-数据存储)
- [9. 可视化和分析](#9-可视化和分析)
- [10. 生产部署](#10-生产部署)

---

## 1. 基础概念

### Q1.1: Trace和Span有什么区别？

**答案**:

```
Trace (追踪):
  - 一次完整的请求流程
  - 包含多个Span
  - 有唯一的TraceID
  
Span (片段):
  - 单个操作的记录
  - 是Trace的组成部分
  - 有唯一的SpanID
  
关系: 1个Trace包含N个Span (N >= 1)

示例:
  用户下单 (Trace)
    ├─ 验证用户 (Span 1)
    ├─ 检查库存 (Span 2)
    ├─ 创建订单 (Span 3)
    └─ 发送邮件 (Span 4)
```

### Q1.2: OTLP和OpenTelemetry是什么关系？

**答案**:

```
OpenTelemetry:
  - 完整的可观测性框架
  - 包括API、SDK、工具

OTLP (OpenTelemetry Protocol):
  - OpenTelemetry的数据传输协议
  - 是OpenTelemetry的一部分
  
关系:
  OpenTelemetry = API + SDK + OTLP + Collector + ...
  OTLP = 数据传输格式和协议
```

### Q1.3: 为什么需要分布式追踪？

**答案**:

**问题场景**:

```
微服务架构:
  用户请求 → 30+个服务
  
传统日志的困境:
  ❌ 日志分散在30个服务中
  ❌ 无法关联同一个请求
  ❌ 不知道请求路径
  ❌ 难以定位性能瓶颈
```

**分布式追踪的解决**:

```
✓ 统一的TraceID关联所有日志
✓ 完整的请求调用链路
✓ 每个步骤的耗时
✓ 快速定位问题服务
✓ 可视化的调用关系
```

### Q1.4: Metric、Log、Trace的区别？

**答案**:

| 维度 | Metric (指标) | Log (日志) | Trace (追踪) |
|------|---------------|------------|--------------|
| **数据类型** | 数值 | 文本 | 结构化 |
| **时间粒度** | 聚合 (1分钟) | 实时 | 实时 |
| **问题类型** | What (发生了什么) | Why (为什么) | Where (在哪里) |
| **存储量** | 小 | 大 | 中 |
| **查询方式** | 时序查询 | 文本搜索 | TraceID查询 |
| **典型用途** | 监控告警 | 问题诊断 | 性能分析 |

**示例**:

```
场景: API响应慢

Metric告诉你: 
  - P99延迟从100ms上升到500ms
  - 何时开始变慢

Log告诉你:
  - 具体错误信息
  - 异常堆栈
  - 业务上下文

Trace告诉你:
  - 哪个服务慢
  - 哪个操作慢
  - 为什么慢 (数据库查询、外部API等)
```

### Q1.5: SpanKind有什么用？

**答案**:

**SpanKind类型**:

```
1. CLIENT: 发起请求的客户端
   例: HTTP客户端、gRPC客户端、数据库客户端

2. SERVER: 处理请求的服务端
   例: HTTP服务器、gRPC服务器

3. PRODUCER: 发送消息的生产者
   例: Kafka生产者、消息队列发送

4. CONSUMER: 接收消息的消费者
   例: Kafka消费者、消息队列接收

5. INTERNAL: 内部操作
   例: 本地函数调用、计算
```

**作用**:

1. **自动建立父子关系**: CLIENT Span → SERVER Span
2. **正确计算延迟**: 区分网络时间和处理时间
3. **可视化调用图**: 清晰展示服务间调用
4. **智能采样**: 对不同类型采取不同策略

---

## 2. 安装和配置

### Q2.1: 如何选择合适的SDK语言？

**答案**:

根据您的应用语言选择：

```
Java:     opentelemetry-java
Python:   opentelemetry-python
Node.js:  @opentelemetry/sdk-node
Go:       go.opentelemetry.io/otel
.NET:     OpenTelemetry.Instrumentation
Rust:     opentelemetry-rust
```

**成熟度参考** (2025年):

```
⭐⭐⭐⭐⭐ Stable (生产就绪):
  - Java, Python, Node.js, Go, .NET

⭐⭐⭐⭐ Beta (大部分场景可用):
  - Ruby, PHP, C++

⭐⭐⭐ Alpha (持续开发):
  - Rust, Swift, Erlang
```

### Q2.2: 自动埋点和手动埋点该选哪个？

**答案**:

**推荐策略**: 自动埋点 + 手动埋点

**自动埋点 (Auto-Instrumentation)**:

```
优点:
  ✓ 无需修改代码
  ✓ 覆盖常见框架 (HTTP, DB, Redis等)
  ✓ 快速启用

缺点:
  ✗ 缺少业务上下文
  ✗ 可能产生噪音
  ✗ 无法定制

适用:
  - 快速验证价值
  - 标准框架监控
  - 基础设施监控
```

**手动埋点 (Manual Instrumentation)**:

```
优点:
  ✓ 完全控制
  ✓ 业务语义明确
  ✓ 可添加业务属性

缺点:
  ✗ 需要修改代码
  ✗ 开发成本高
  ✗ 维护负担

适用:
  - 关键业务逻辑
  - 自定义组件
  - 需要业务指标
```

**最佳实践**:

```typescript
// 1. 启用自动埋点 (HTTP, DB, Redis等)
require('./tracing');  // 自动埋点配置

// 2. 在关键业务逻辑添加手动Span
const tracer = trace.getTracer('order-service');

async function processOrder(order) {
  const span = tracer.startSpan('processOrder');
  span.setAttribute('order.id', order.id);        // 业务属性
  span.setAttribute('order.amount', order.amount);
  span.setAttribute('user.id', order.userId);
  
  try {
    // 业务逻辑
    await validateOrder(order);
    await chargePayment(order);
    await createShipment(order);
    
    span.setStatus({ code: 1 });  // OK
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: 2 });  // ERROR
    throw error;
  } finally {
    span.end();
  }
}
```

### Q2.3: Collector是否必须？

**答案**:

**不是必须的**，但强烈推荐：

**不使用Collector** (直接导出):

```
应用 → OTLP Exporter → Backend (Jaeger/Zipkin)

优点:
  ✓ 架构简单
  ✓ 部署容易

缺点:
  ✗ 应用与Backend耦合
  ✗ 缺少缓冲和批处理
  ✗ 无法统一处理
  ✗ 切换Backend需要重启应用
```

**使用Collector** (推荐):

```
应用 → Collector → Backend

优点:
  ✓ 应用与Backend解耦
  ✓ 集中配置和管理
  ✓ 数据处理和过滤
  ✓ 批量发送，降低开销
  ✓ 多Backend支持
  ✓ 故障隔离

缺点:
  ✗ 额外的组件
  ✗ 需要维护Collector
```

**何时可以不用Collector**:

- 单体应用
- 开发/测试环境
- 快速验证POC
- 流量很小

**何时必须用Collector**:

- 生产环境
- 微服务架构
- 高流量应用
- 需要数据处理

### Q2.4: 如何配置环境变量？

**答案**:

**关键环境变量**:

```bash
# 服务信息
export OTEL_SERVICE_NAME="my-service"
export OTEL_SERVICE_VERSION="1.0.0"
export OTEL_DEPLOYMENT_ENVIRONMENT="production"

# OTLP Exporter配置
export OTEL_EXPORTER_OTLP_ENDPOINT="http://localhost:4318"
export OTEL_EXPORTER_OTLP_PROTOCOL="http/protobuf"  # 或 "grpc"
export OTEL_EXPORTER_OTLP_HEADERS="api-key=secret123"

# 采样配置
export OTEL_TRACES_SAMPLER="parentbased_traceidratio"
export OTEL_TRACES_SAMPLER_ARG="0.1"  # 10%采样率

# 资源属性
export OTEL_RESOURCE_ATTRIBUTES="service.namespace=production,host.name=server01"

# 日志级别
export OTEL_LOG_LEVEL="info"
```

**按环境配置**:

```bash
# 开发环境 (dev.env)
OTEL_SERVICE_NAME=my-service-dev
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318
OTEL_TRACES_SAMPLER=always_on  # 100%采样

# 生产环境 (prod.env)
OTEL_SERVICE_NAME=my-service
OTEL_EXPORTER_OTLP_ENDPOINT=http://collector.internal:4318
OTEL_TRACES_SAMPLER=parentbased_traceidratio
OTEL_TRACES_SAMPLER_ARG=0.01  # 1%采样
```

**使用**:

```bash
# 加载配置
source dev.env
node app.js

# 或使用dotenv
npm install dotenv
# 在代码中: require('dotenv').config()
```

---

## 3. 数据采集

### Q3.1: 如何埋点而不影响性能？

**答案**:

**最佳实践**:

```typescript
// ✓ 1. 使用异步导出
const spanProcessor = new BatchSpanProcessor(exporter, {
  maxQueueSize: 2048,
  scheduledDelayMillis: 5000,  // 5秒批量发送一次
  exportTimeoutMillis: 30000,
  maxExportBatchSize: 512
});

// ✓ 2. 合理采样
const sampler = new ParentBasedSampler({
  root: new TraceIdRatioBasedSampler(0.01)  // 1%采样
});

// ✓ 3. 避免过度埋点
// ✗ 错误: 给每个getter方法都加Span
class User {
  @Trace  // ✗ 不要这样
  getName() { return this.name; }
}

// ✓ 正确: 只给关键业务操作加Span
class OrderService {
  @Trace  // ✓ 关键操作
  async processOrder(order) {
    // ...
  }
}

// ✓ 4. 限制属性大小
span.setAttribute('user.id', userId);  // ✓ 简短
span.setAttribute('request.body', JSON.stringify(body));  // ✗ 可能很大

// 改进: 限制大小
const bodyStr = JSON.stringify(body);
span.setAttribute('request.body', 
  bodyStr.length > 1000 ? bodyStr.substring(0, 1000) + '...' : bodyStr
);

// ✓ 5. 关闭不需要的自动埋点
const instrumentations = getNodeAutoInstrumentations({
  '@opentelemetry/instrumentation-fs': {
    enabled: false  // 关闭文件系统追踪
  }
});
```

**性能开销参考**:

```
良好配置:
  - CPU: +1-2%
  - 内存: +5-10MB
  - 延迟: +0.5ms per request (1%采样)

过度埋点:
  - CPU: +10-20%
  - 内存: +50-100MB
  - 延迟: +5-10ms per request (100%采样)
```

### Q3.2: 如何给Span添加业务属性？

**答案**:

**语义约定** (推荐):

```typescript
// 遵循OpenTelemetry语义约定
span.setAttribute('http.method', 'POST');
span.setAttribute('http.url', 'https://api.example.com/orders');
span.setAttribute('http.status_code', 200);

// 数据库
span.setAttribute('db.system', 'postgresql');
span.setAttribute('db.statement', 'SELECT * FROM users WHERE id = ?');
span.setAttribute('db.name', 'production');

// 消息队列
span.setAttribute('messaging.system', 'kafka');
span.setAttribute('messaging.destination', 'orders');
span.setAttribute('messaging.operation', 'publish');
```

**自定义业务属性** (加前缀):

```typescript
// 用户相关
span.setAttribute('app.user.id', '12345');
span.setAttribute('app.user.role', 'admin');
span.setAttribute('app.user.tier', 'premium');

// 订单相关
span.setAttribute('app.order.id', 'ORD-001');
span.setAttribute('app.order.amount', 99.99);
span.setAttribute('app.order.currency', 'USD');
span.setAttribute('app.order.items_count', 3);

// 业务流程
span.setAttribute('app.payment.method', 'credit_card');
span.setAttribute('app.payment.provider', 'stripe');
span.setAttribute('app.shipping.method', 'express');
```

**数组属性**:

```typescript
// OpenTelemetry支持数组
span.setAttribute('app.order.item_ids', ['item1', 'item2', 'item3']);
span.setAttribute('app.user.permissions', ['read', 'write', 'delete']);
```

**避免的做法**:

```typescript
// ✗ 不要放敏感信息
span.setAttribute('user.password', password);  // ✗ 危险！
span.setAttribute('credit_card.number', ccNum);  // ✗ 危险！

// ✗ 不要放过大的数据
span.setAttribute('response.body', JSON.stringify(largeObject));  // ✗ 可能几MB

// ✗ 不要使用高基数属性作为键
span.setAttribute(userId, 'active');  // ✗ 每个用户一个键
// 改为:
span.setAttribute('user.id', userId);
span.setAttribute('user.status', 'active');  // ✓ 正确
```

### Q3.3: 如何追踪异步操作？

**答案**:

**Promise**:

```typescript
const tracer = trace.getTracer('my-service');

async function fetchUserData(userId) {
  const span = tracer.startSpan('fetchUserData');
  span.setAttribute('user.id', userId);
  
  try {
    // Promise自动传播Context
    const user = await db.query('SELECT * FROM users WHERE id = ?', [userId]);
    const orders = await db.query('SELECT * FROM orders WHERE user_id = ?', [userId]);
    
    span.setStatus({ code: 1 });
    return { user, orders };
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: 2 });
    throw error;
  } finally {
    span.end();
  }
}
```

**回调函数**:

```typescript
const { context } = require('@opentelemetry/api');

function legacyAsyncOperation(callback) {
  const span = tracer.startSpan('legacyOp');
  
  // 保存当前Context
  const ctx = context.active();
  
  doAsyncWork((err, result) => {
    // 在回调中恢复Context
    context.with(ctx, () => {
      if (err) {
        span.recordException(err);
        span.setStatus({ code: 2 });
        callback(err);
      } else {
        span.setStatus({ code: 1 });
        callback(null, result);
      }
      span.end();
    });
  });
}
```

**EventEmitter**:

```typescript
const { context, trace } = require('@opentelemetry/api');

class OrderProcessor extends EventEmitter {
  processOrder(order) {
    const span = tracer.startSpan('processOrder');
    const ctx = trace.setSpan(context.active(), span);
    
    // 在Context中emit事件
    context.with(ctx, () => {
      this.emit('order:created', order);
      // 监听器会在同一个Context中执行
    });
    
    span.end();
  }
}

// 监听器自动获得Context
processor.on('order:created', (order) => {
  // 这里可以访问到parent span
  const childSpan = tracer.startSpan('sendNotification');
  // ...
  childSpan.end();
});
```

---

## 4. Context传播

### Q4.1: 什么是Context传播？

**答案**:

Context传播是在分布式系统中跨服务边界传递追踪信息的机制。

**为什么需要**:

```
没有Context传播:
  Service A → Service B → Service C
  生成3个独立的Trace ✗
  
  Trace 1: Service A (TraceID: ABC)
  Trace 2: Service B (TraceID: DEF)  ← 无法关联
  Trace 3: Service C (TraceID: GHI)  ← 无法关联

有Context传播:
  Service A → Service B → Service C
  1个完整的Trace ✓
  
  Trace (TraceID: ABC):
    Span 1: Service A
    Span 2: Service B  ← 共享TraceID
    Span 3: Service C  ← 共享TraceID
```

**如何传播**:

```
HTTP: 通过HTTP头传递
  traceparent: 00-{trace-id}-{span-id}-{flags}

gRPC: 通过metadata传递
  grpc-trace-bin: binary format

消息队列: 通过消息头传递
  Kafka headers: traceparent
```

### Q4.2: W3C Trace Context和B3有什么区别？

**答案**:

| 维度 | W3C Trace Context | B3 (Zipkin) |
|------|-------------------|-------------|
| **标准化** | W3C官方标准 | Zipkin社区标准 |
| **浏览器支持** | 原生支持 | 需要手动处理 |
| **HTTP头数量** | 1-2个 | 4-5个 |
| **格式** | 单一头格式 | 多个独立头 |
| **厂商扩展** | tracestate支持 | 需要自定义头 |
| **采用度** | 快速增长 | 广泛使用 |

**W3C Trace Context**:

```http
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
tracestate: vendor1=data,vendor2=info
```

**B3**:

```http
X-B3-TraceId: 4bf92f3577b34da6a3ce929d0e0e4736
X-B3-SpanId: 00f067aa0ba902b7
X-B3-ParentSpanId: 05e3ac9a4f6e3b90
X-B3-Sampled: 1
```

**或B3单头格式**:

```http
b3: 4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1-05e3ac9a4f6e3b90
```

**推荐**:

- 新项目: W3C Trace Context
- 兼容Zipkin: 同时支持两者
- OpenTelemetry默认: W3C Trace Context

### Q4.3: 如何在消息队列中传播Context？

**答案**:

**Kafka示例**:

```typescript
const { propagation, context } = require('@opentelemetry/api');

// 生产者: 注入Context到消息头
async function publishMessage(topic, message) {
  const span = tracer.startSpan('kafka.publish');
  
  const headers = {};
  
  // 注入追踪信息到headers
  propagation.inject(context.active(), headers);
  
  await producer.send({
    topic,
    messages: [{
      value: JSON.stringify(message),
      headers  // Kafka支持消息头
    }]
  });
  
  span.end();
}

// 消费者: 从消息头提取Context
async function consumeMessage(message) {
  // 提取Context
  const extractedContext = propagation.extract(
    context.active(),
    message.headers
  );
  
  // 在提取的Context中创建Span
  const span = tracer.startSpan(
    'kafka.consume',
    { kind: SpanKind.CONSUMER },
    extractedContext
  );
  
  context.with(
    trace.setSpan(extractedContext, span),
    () => {
      // 处理消息
      processMessage(message.value);
    }
  );
  
  span.end();
}
```

**RabbitMQ示例**:

```typescript
// 发送消息
const headers = {};
propagation.inject(context.active(), headers);

channel.publish('exchange', 'routing.key', Buffer.from(message), {
  headers  // RabbitMQ支持headers
});

// 接收消息
channel.consume('queue', (msg) => {
  const extractedContext = propagation.extract(
    context.active(),
    msg.properties.headers
  );
  
  const span = tracer.startSpan('process', {}, extractedContext);
  // 处理...
  span.end();
});
```

---

## 5. 采样策略

### Q5.1: 生产环境应该用多少采样率？

**答案**:

**通用建议**:

```
流量级别         推荐采样率    说明
─────────────────────────────────────────
<1K QPS         10-50%       可以采样较多
1K-10K QPS      1-10%        平衡可观测性和成本
10K-100K QPS    0.1-1%       控制数据量
>100K QPS       0.01-0.1%    智能采样
```

**但要考虑**:

```
✓ 错误必须100%采样
✓ 慢请求必须100%采样
✓ 关键业务路径提高采样率
✓ 使用Tail Sampling
```

**示例配置**:

```yaml
# Collector Tail Sampling配置
processors:
  tail_sampling:
    policies:
      # 规则1: 所有错误
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
        
      # 规则2: 慢请求 (>2秒)
      - name: slow
        type: latency
        latency: {threshold_ms: 2000}
        
      # 规则3: 关键路径50%
      - name: critical
        type: string_attribute
        string_attribute:
          key: http.route
          values: [/api/payment, /api/order]
        
      # 规则4: 其他1%
      - name: default
        type: probabilistic
        probabilistic: {sampling_percentage: 1}
```

### Q5.2: Head Sampling和Tail Sampling哪个好？

**答案**:

**Head Sampling** (SDK中):

```
决策时机: Trace开始时
优点:
  ✓ 简单高效
  ✓ 开销小
  ✓ 无需额外组件
缺点:
  ✗ 可能错过重要Trace
  ✗ 无法基于完整信息决策
适用: 
  - 流量稳定
  - 不关心罕见错误
```

**Tail Sampling** (Collector中):

```
决策时机: Trace完成后
优点:
  ✓ 智能决策
  ✓ 不错过重要Trace (错误、慢请求)
  ✓ 灵活的规则
缺点:
  ✗ 需要Collector
  ✗ 需要临时存储所有Span
  ✗ 延迟决策
适用:
  - 生产环境
  - 需要精准采样
  - 复杂业务场景
```

**推荐组合**:

```
SDK: ParentBased采样 (遵循上游决策)
  ↓
Collector: Tail Sampling (智能决策)
  
这样可以:
  1. 保证Trace完整性 (Parent Based)
  2. 智能过滤 (Tail Sampling)
  3. 最佳的成本/收益比
```

---

## 6. 性能问题

### Q6.1: 追踪会增加多少延迟？

**答案**:

**典型开销** (良好配置):

```
每个请求:
  - Span创建: ~0.1ms
  - 属性设置: ~0.01ms per attribute
  - Context传播: ~0.05ms
  - 异步导出: 几乎无延迟 (后台进行)
  
总计: ~0.5-2ms (取决于Span数量)

示例:
  原延迟: 100ms
  追踪后: 101-102ms
  影响: ~1-2%
```

**高开销场景** (配置不当):

```
❌ 同步导出:
  每个Span立即发送 → 增加5-10ms

❌ 100%采样 + 高频请求:
  1万QPS × 100%采样 → CPU +20%

❌ 过度埋点:
  每个方法都埋点 → 延迟翻倍
```

**优化建议**:

```typescript
// ✓ 1. 使用批量异步导出
const processor = new BatchSpanProcessor(exporter, {
  maxQueueSize: 2048,
  scheduledDelayMillis: 5000,  // 5秒批量发送
  maxExportBatchSize: 512
});

// ✓ 2. 合理采样
const sampler = new TraceIdRatioBasedSampler(0.01);  // 1%

// ✓ 3. 限制属性大小
span.setAttribute('data', data.substring(0, 1000));

// ✓ 4. 避免过度埋点
// 只给关键操作加Span
```

### Q6.2: 如何减少内存占用？

**答案**:

**内存消耗来源**:

```
1. Span缓冲队列: ~1MB per 1000 spans
2. Context存储: ~100KB
3. SDK开销: ~5-10MB
```

**优化措施**:

```typescript
// 1. 限制队列大小
const processor = new BatchSpanProcessor(exporter, {
  maxQueueSize: 1024,  // 默认2048，可以减小
  maxExportBatchSize: 256  // 默认512，可以减小
});

// 2. 更频繁的导出
const processor = new BatchSpanProcessor(exporter, {
  scheduledDelayMillis: 2000  // 2秒导出一次 (默认5秒)
});

// 3. 限制属性数量
span.setAttributes({
  'key1': 'value1',
  'key2': 'value2'
  // 不要超过20个属性
});

// 4. 限制Event数量
// 不要在循环中添加Event
for (let i = 0; i < 1000; i++) {
  span.addEvent('processing', { index: i });  // ✗ 会占用很多内存
}

// 改为:
span.addEvent('processing_batch', { count: 1000 });  // ✓ 一个Event
```

---

## 7. 故障排查

### Q7.1: 看不到追踪数据怎么办？

**答案**:

**排查步骤**:

```bash
# 1. 检查SDK是否正确初始化
# 查看应用日志，确认没有错误

# 2. 检查Exporter配置
curl http://localhost:4318/v1/traces
# 应该返回404 (说明端口开放，但不接受GET请求)

# 3. 检查是否生成Span
# 在代码中添加日志
span.end();
console.log('Span ended:', span.spanContext().spanId);

# 4. 检查采样配置
# 确保不是采样率太低
export OTEL_TRACES_SAMPLER=always_on  # 临时设置100%采样

# 5. 使用Console Exporter调试
const { ConsoleSpanExporter } = require('@opentelemetry/sdk-trace-base');
const exporter = new ConsoleSpanExporter();
// 会在控制台打印所有Span

# 6. 检查Collector日志 (如果使用)
docker logs jaeger 2>&1 | grep -i error

# 7. 检查网络连接
telnet localhost 4318
```

**常见原因**:

```
❌ tracing初始化在其他import之后
   require('./tracing');  // ← 必须第一行
   require('express');

❌ 采样率设置为0
   OTEL_TRACES_SAMPLER_ARG=0  // 0%采样

❌ Exporter endpoint错误
   OTEL_EXPORTER_OTLP_ENDPOINT=http://wrong-host:4318

❌ Span没有正确结束
   span.end();  // 忘记调用

❌ Context传播失败
   检查HTTP头是否正确设置
```

### Q7.2: Trace不完整怎么办？

**答案**:

**症状**:

```
只看到部分Span，不是完整的Trace
```

**可能原因和解决**:

**1. Context传播失败**:

```typescript
// ✗ 错误: 创建新Trace
async function callService() {
  const span = tracer.startSpan('call-service');
  await fetch('http://api.example.com');  // 没有传递Context
  span.end();
}

// ✓ 正确: 传播Context
async function callService() {
  const span = tracer.startSpan('call-service');
  
  const headers = {};
  propagation.inject(context.active(), headers);  // 注入Context
  
  await fetch('http://api.example.com', { headers });
  span.end();
}
```

**2. 异步操作丢失Context**:

```typescript
// ✗ 错误: setTimeout丢失Context
span.end();
setTimeout(() => {
  // 这里的Context已经丢失
  const childSpan = tracer.startSpan('delayed');  // 成为新Trace
}, 1000);

// ✓ 正确: 保存和恢复Context
const ctx = context.active();
span.end();
setTimeout(() => {
  context.with(ctx, () => {
    const childSpan = tracer.startSpan('delayed');
    // ...
  });
}, 1000);
```

**3. 不同服务采样决策不一致**:

```
Service A: 采样 (sampled=1)
  → Service B: 未采样 (sampled=0)  ← 冲突！

解决: 使用ParentBased采样
  所有服务遵循根Span的采样决策
```

**4. Span丢失 (Collector/Backend问题)**:

```bash
# 检查Collector是否正常
# 查看dropped spans数量
curl http://localhost:8888/metrics | grep dropped

# 检查Backend存储是否满
```

---

## 8. 数据存储

### Q8.1: 追踪数据应该保存多久？

**答案**:

**推荐保留期**:

```
热数据 (可快速查询):
  - 最近7天: 100%数据
  - 用途: 日常排查

温数据 (归档查询):
  - 7-30天: 10%采样数据
  - 用途: 历史分析

冷数据 (长期存储):
  - 30-90天: 1%采样数据或仅错误Trace
  - 用途: 趋势分析、审计

删除:
  - >90天: 删除或迁移到对象存储
```

**存储成本估算**:

```
假设:
  - 1万QPS
  - 平均每个Trace 10个Span
  - 每个Span 1KB
  - 10%采样率

每天数据量:
  1万 × 86400秒 × 10% × 10 Span × 1KB
  = 8.64亿 Span
  = 864 GB/天

7天热数据: ~6 TB
30天总数据: ~25 TB

成本 (假设$0.1/GB/月):
  ~$250/月 (仅存储成本)
```

**优化策略**:

```
1. 智能采样
   - 错误: 100%
   - 慢请求: 100%
   - 正常请求: 1-10%

2. 数据压缩
   - 使用列式存储
   - gzip压缩 (3-5x压缩比)

3. 分层存储
   - 7天: SSD
   - 30天: HDD
   - >30天: 对象存储 (S3)

4. 定期清理
   - 自动删除过期数据
   - 保留错误Trace更长时间
```

### Q8.2: Jaeger、Zipkin、Tempo该选哪个？

**答案**:

| 特性 | Jaeger | Zipkin | Tempo |
|------|--------|--------|-------|
| **CNCF项目** | ✓ | ✗ | ✗ (Grafana Labs) |
| **存储** | Cassandra, ES, Kafka | ES, Cassandra, MySQL | S3, GCS |
| **部署复杂度** | 中 | 低 | 低 |
| **可扩展性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **查询性能** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **成本** | 中 | 低 | 低 (对象存储) |
| **UI** | 功能丰富 | 简单直观 | 集成Grafana |
| **采样** | 自适应 | 固定比率 | 无 (依赖采集端) |

**推荐场景**:

**Jaeger** - 企业级生产环境:

```
✓ 需要强大的查询能力
✓ 大规模部署
✓ 需要自适应采样
✓ 有运维资源

示例: 
  - 大型微服务架构 (100+服务)
  - 高流量应用 (>10K QPS)
```

**Zipkin** - 快速启动:

```
✓ 简单场景
✓ 快速验证
✓ 资源有限

示例:
  - 小型项目 (10-20服务)
  - 开发/测试环境
```

**Tempo** - 云原生 + Grafana生态:

```
✓ 已使用Grafana
✓ 需要低成本存储
✓ 与Metrics/Logs统一

示例:
  - 云原生应用
  - 成本敏感
  - Grafana用户
```

---

## 9. 可视化和分析

### Q9.1: 如何在Jaeger UI中快速定位慢请求？

**答案**:

**步骤1: 使用过滤器**:

```
Jaeger UI → Search
  ├─ Service: 选择你的服务
  ├─ Min Duration: 2s  ← 只显示>2秒的Trace
  ├─ Limit Results: 20
  └─ Find Traces
```

**步骤2: 排序**:

```
结果列表 → 点击 "Duration" 列
  → 按持续时间降序排列
  → 最慢的在最上面
```

**步骤3: 分析Trace**:

```
点击慢Trace → Timeline视图
  → 找到最长的Span
  → 查看Span详情
  → 定位性能瓶颈
```

**高级技巧**:

```
1. 使用Tags过滤:
   Tags: http.status_code=500
   → 只看错误请求

2. 使用Operation过滤:
   Operation: GET /api/users
   → 只看特定接口

3. 组合条件:
   Service: order-service
   Operation: processOrder
   Min Duration: 2s
   Tags: error=true
   → 精确定位问题
```

### Q9.2: 如何分析服务依赖关系？

**答案**:

**Jaeger中查看**:

```
Jaeger UI → System Architecture → DAG
  
会显示:
  ├─ 所有服务节点
  ├─ 服务间调用关系 (箭头)
  ├─ 调用次数 (边上的数字)
  └─ 平均延迟
```

**使用Trace分析**:

```
1. 选择一个复杂的Trace
2. 查看 "Span Graph" 视图
   → 显示这个请求的完整调用链
   
3. 分析:
   - 哪些服务被调用了
   - 串行 vs 并行调用
   - 每个服务的耗时
```

**导出依赖数据**:

```bash
# Jaeger提供依赖API
curl http://localhost:16686/api/dependencies?endTs=$(date +%s)000&lookback=86400000

# 返回JSON:
{
  "data": [
    {
      "parent": "frontend",
      "child": "auth-service",
      "callCount": 1523
    },
    {
      "parent": "frontend",
      "child": "order-service",
      "callCount": 892
    }
  ]
}
```

---

## 10. 生产部署

### Q10.1: Collector应该如何部署？

**答案**:

**部署模式**:

**1. Sidecar模式** (每个服务一个):

```
优点:
  ✓ 隔离性好
  ✓ 故障影响小
缺点:
  ✗ 资源消耗大
  ✗ 配置管理复杂
适用: 
  - Kubernetes环境
  - 需要严格隔离
```

**2. 节点Agent模式** (每个节点一个):

```
优点:
  ✓ 资源效率高
  ✓ 配置统一
缺点:
  ✗ 单点故障影响该节点所有应用
适用:
  - 虚拟机部署
  - 资源受限环境
```

**3. 集中式Gateway模式** (集群级):

```
优点:
  ✓ 易于管理
  ✓ 集中配置
  ✓ 负载均衡
缺点:
  ✗ 网络跳数增加
  ✗ Gateway成为瓶颈
适用:
  - 大规模部署
  - 需要集中管理
```

**推荐架构** (混合模式):

```
应用 → Node Agent → Gateway Collector → Backend

Node Agent:
  - 接收本地应用数据
  - 基础处理和批量
  - 本地缓冲

Gateway Collector:
  - 高级处理 (Tail Sampling)
  - 多Backend路由
  - 数据聚合

优点: 
  ✓ 应用到Agent低延迟
  ✓ Gateway统一管理
  ✓ 故障容忍
```

**Kubernetes部署示例**:

```yaml
# DaemonSet部署 (每个节点一个Agent)
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector-agent
spec:
  template:
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector:latest
        resources:
          requests:
            memory: "100Mi"
            cpu: "100m"
          limits:
            memory: "200Mi"
            cpu: "200m"

---
# Deployment部署 (Gateway Collector)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector-gateway
spec:
  replicas: 3  # 高可用
  template:
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        resources:
          requests:
            memory: "1Gi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "1000m"
```

### Q10.2: 如何保证高可用？

**答案**:

**1. Collector高可用**:

```
- 部署多个副本 (至少3个)
- 使用负载均衡
- 健康检查和自动重启
```

```yaml
# Kubernetes示例
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
spec:
  selector:
    app: otel-collector
  ports:
  - port: 4318
    name: otlp-http
  type: LoadBalancer  # 负载均衡

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
spec:
  replicas: 3  # 高可用
  template:
    spec:
      containers:
      - name: collector
        livenessProbe:  # 健康检查
          httpGet:
            path: /
            port: 13133
        readinessProbe:
          httpGet:
            path: /
            port: 13133
```

**2. Backend高可用**:

```
Jaeger:
  - Cassandra/ES集群 (3+节点)
  - 多副本
  - 备份策略

Tempo:
  - S3/GCS (云存储自带高可用)
  - 多区域部署
```

**3. 应用端容错**:

```typescript
// 使用超时
const exporter = new OTLPTraceExporter({
  url: 'http://collector:4318/v1/traces',
  timeoutMillis: 5000  // 5秒超时
});

// 重试逻辑
const exporter = new OTLPTraceExporter({
  url: 'http://collector:4318/v1/traces',
  maxAttempts: 3,  // 最多重试3次
  initialBackoffMs: 1000  // 初始退避1秒
});

// Fallback: 导出失败不影响应用
try {
  await exporter.export(spans);
} catch (error) {
  console.error('Failed to export spans:', error);
  // 应用继续正常运行
}
```

**4. 数据不丢失**:

```
应用端:
  - 本地队列缓冲 (2048 spans)
  - 批量发送

Collector:
  - 内存队列 (10000 spans)
  - 磁盘持久化 (可选)
  - 多Backend备份
```

---

## 📊 FAQ统计

- **总问题数**: 50+
- **基础概念**: 5个
- **安装配置**: 4个
- **数据采集**: 3个
- **Context传播**: 3个
- **采样策略**: 2个
- **性能问题**: 2个
- **故障排查**: 2个
- **数据存储**: 2个
- **可视化分析**: 2个
- **生产部署**: 2个

---

## 🔗 相关文档

- ← [快速入门指南](./🚀_快速入门指南.md)
- → [故障排查指南](./❓_故障排查指南.md)
- ↗ [概念索引](./01_概念索引/)
- ↗ [实现概念](./01_概念索引/03_实现概念.md)

---

**维护**: OTLP项目组  
**更新频率**: 每月  
**贡献**: 欢迎提交新问题
