# OpenTelemetry 术语与语义约定索引

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [语义约定](SEMANTIC_CONVENTIONS.md) | [快速开始](QUICK_START.md) | [架构设计](ARCHITECTURE.md)
> 最后更新: 2025-09-17

## 核心概念

### 分布式追踪 (Distributed Tracing)

- **Trace**: 表示一个完整的请求处理过程，包含多个相关的Span
- **Span**: 表示一个操作单元，包含开始时间、结束时间、属性和事件
- **TraceId**: 全局唯一标识符，用于关联分布式系统中的所有Span
- **SpanId**: 单个Span的唯一标识符
- **ParentSpanId**: 父Span的标识符，用于构建调用树
- **TraceState**: 携带跨服务边界的额外追踪状态信息

### 资源与作用域 (Resource & Scope)

- **Resource**: 描述产生遥测数据的实体（服务、主机、容器等）
- **InstrumentationScope**: 描述产生遥测数据的代码库或组件
- **Service**: 逻辑服务单元，通常对应一个微服务
- **ServiceInstance**: 服务的具体实例

### 指标 (Metrics)

- **Gauge**: 瞬时值指标，如CPU使用率、内存使用量
- **Sum/Counter**: 累加值指标，如请求总数、错误总数
- **Histogram**: 分布值指标，如响应时间分布
- **ExponentialHistogram**: 指数直方图，用于高基数指标
- **Summary**: 预聚合统计指标

### 日志 (Logs)

- **LogRecord**: 单个日志记录，包含时间戳、严重级别、消息和属性
- **Severity**: 日志严重级别（TRACE, DEBUG, INFO, WARN, ERROR, FATAL）

### 上下文传播 (Context Propagation)

- **Baggage**: 跨服务边界的键值对数据，用于传递业务上下文
- **Propagation**: 上下文信息在服务间传递的机制
- **Correlation**: 不同信号（traces/metrics/logs）之间的关联

## 语义约定 (Semantic Conventions)

### HTTP 语义约定

- `http.method`: HTTP方法（GET, POST, PUT, DELETE等）
- `http.status_code`: HTTP状态码
- `http.url`: 完整的请求URL
- `http.target`: 请求目标路径
- `http.host`: 请求主机名
- `http.user_agent`: 用户代理字符串
- `http.request_content_length`: 请求体大小
- `http.response_content_length`: 响应体大小

### 数据库语义约定

- `db.system`: 数据库系统类型（mysql, postgresql, redis等）
- `db.connection_string`: 数据库连接字符串（脱敏）
- `db.statement`: SQL语句或查询
- `db.operation`: 数据库操作类型（SELECT, INSERT, UPDATE, DELETE）
- `db.sql.table`: 表名
- `db.redis.database_index`: Redis数据库索引

### RPC 语义约定

- `rpc.system`: RPC系统（grpc, dubbo, thrift等）
- `rpc.service`: 服务名
- `rpc.method`: 方法名
- `rpc.grpc.status_code`: gRPC状态码
- `rpc.grpc.request.metadata`: 请求元数据

### 消息队列语义约定

- `messaging.system`: 消息系统（kafka, rabbitmq, nats等）
- `messaging.destination`: 目标主题或队列
- `messaging.destination_kind`: 目标类型（topic, queue）
- `messaging.message_id`: 消息ID
- `messaging.operation`: 操作类型（publish, receive, process）

### 云平台语义约定

- `cloud.provider`: 云提供商（aws, azure, gcp）
- `cloud.region`: 云区域
- `cloud.availability_zone`: 可用区
- `cloud.platform`: 云平台（aws_ec2, azure_vm, gcp_compute_engine）

### Kubernetes 语义约定

- `k8s.cluster.name`: 集群名称
- `k8s.namespace.name`: 命名空间
- `k8s.pod.name`: Pod名称
- `k8s.pod.uid`: Pod UID
- `k8s.container.name`: 容器名称
- `k8s.deployment.name`: 部署名称
- `k8s.service.name`: 服务名称

## 协议与传输

### OTLP (OpenTelemetry Protocol)

- **gRPC**: 默认传输协议，端口4317
- **HTTP/Protobuf**: 替代传输协议，端口4318
- **JSON**: 人类可读格式，用于调试

### 采样策略

- **AlwaysOn**: 采样所有请求
- **AlwaysOff**: 不采样任何请求
- **TraceIdRatioBased**: 基于TraceId的比率采样
- **ParentBased**: 基于父Span的采样决策

## 参考资源

- [OpenTelemetry 官方语义约定](https://opentelemetry.io/docs/specs/semantic_conventions/)
- [OpenTelemetry 规范文档](https://opentelemetry.io/docs/specs/)
- [各语言SDK文档](https://opentelemetry.io/docs/languages/)

### 示例

```bash
# 查询 Collector 指标以验证术语中提到的关键指标存在
curl -s http://localhost:13133/metrics | grep -E "otelcol_receiver_accepted_spans|otelcol_exporter_sent_spans" | head -n 5
```
