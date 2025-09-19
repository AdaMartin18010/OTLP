# OpenTelemetry 语义约定规范

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [术语定义](TERMS.md) | [API参考](API_REFERENCE.md) | [架构设计](ARCHITECTURE.md)
> 最后更新: 2025-09-17

## 目录

1. 概述
2. 命名规范
   - 2.1 基本规则
   - 2.2 命名空间
3. 核心语义约定
   - 3.1 HTTP 语义约定
   - 3.2 数据库语义约定
   - 3.3 RPC 语义约定
   - 3.4 消息队列语义约定
   - 3.5 云平台语义约定
   - 3.6 Kubernetes 语义约定
4. 资源语义约定
   - 4.1 服务资源
   - 4.2 主机资源
   - 4.3 容器资源
5. 最佳实践
   - 5.1 属性命名
   - 5.2 数据类型
   - 5.3 敏感信息处理
   - 5.4 性能考虑
6. 治理流程
7. 参考资源

---

## 1. 概述

语义约定（Semantic Conventions）是OpenTelemetry的核心组成部分，定义了遥测数据的标准化命名和结构。
这些约定确保了不同语言、不同框架产生的遥测数据能够被统一理解和处理。

### 2025年更新状态

- **HTTP 语义约定**: 已稳定（2023年11月）
- **RPC 语义约定**: 稳定性项目启动（2025年6月），涵盖 gRPC、JSON-RPC、Apache Dubbo 等框架
- **指标名称长度**: 从63字符增加到255字符（2025年更新）

## 2. 命名规范

### 2.1 基本规则

1. **小写字母和点号**: 使用小写字母和点号分隔，如 `http.method`
2. **层次结构**: 使用点号表示层次关系，如 `db.redis.database_index`
3. **避免缩写**: 使用完整单词，如 `database` 而不是 `db`
4. **一致性**: 相同概念在不同上下文中使用相同的命名

### 2.2 命名空间

- `http.*`: HTTP协议相关属性
- `db.*`: 数据库相关属性
- `rpc.*`: RPC调用相关属性
- `messaging.*`: 消息队列相关属性
- `cloud.*`: 云平台相关属性
- `k8s.*`: Kubernetes相关属性
- `faas.*`: 函数即服务相关属性

## 3. 核心语义约定

### 3.1 HTTP 语义约定

#### 3.1.1 必需属性

- `http.method`: HTTP方法（GET, POST, PUT, DELETE, PATCH, HEAD, OPTIONS）
- `http.url`: 完整的请求URL
- `http.status_code`: HTTP状态码（整数）

#### 3.1.2 可选属性

- `http.target`: 请求目标路径（不包含查询参数）
- `http.host`: 请求主机名
- `http.scheme`: URL方案（http, https）
- `http.user_agent`: 用户代理字符串
- `http.request_content_length`: 请求体大小（字节）
- `http.response_content_length`: 响应体大小（字节）
- `http.route`: 路由模板（如 `/users/{id}`）

#### 3.1.3 示例

```json
{
  "http.method": "POST",
  "http.url": "https://api.example.com/users",
  "http.status_code": 201,
  "http.target": "/users",
  "http.host": "api.example.com",
  "http.scheme": "https",
  "http.user_agent": "Mozilla/5.0...",
  "http.request_content_length": 1024,
  "http.response_content_length": 512
}
```

### 3.2 数据库语义约定

#### 3.2.1 必需属性

- `db.system`: 数据库系统类型
  - 常见值: `mysql`, `postgresql`, `redis`, `mongodb`, `sqlite`, `oracle`, `mssql`

#### 3.2.2 可选属性

- `db.connection_string`: 数据库连接字符串（需要脱敏）
- `db.statement`: SQL语句或查询
- `db.operation`: 数据库操作类型（SELECT, INSERT, UPDATE, DELETE, CREATE, DROP）
- `db.sql.table`: 表名
- `db.redis.database_index`: Redis数据库索引
- `db.mongodb.collection`: MongoDB集合名

#### 3.2.3 示例

```json
{
  "db.system": "postgresql",
  "db.statement": "SELECT * FROM users WHERE id = ?",
  "db.operation": "SELECT",
  "db.sql.table": "users"
}
```

### 3.3 RPC 语义约定

#### 3.3.1 必需属性

- `rpc.system`: RPC系统类型
  - 常见值: `grpc`, `dubbo`, `thrift`, `jsonrpc`

#### 3.3.2 可选属性

- `rpc.service`: 服务名
- `rpc.method`: 方法名
- `rpc.grpc.status_code`: gRPC状态码
- `rpc.grpc.request.metadata`: 请求元数据
- `rpc.grpc.response.metadata`: 响应元数据

#### 3.3.3 示例

```json
{
  "rpc.system": "grpc",
  "rpc.service": "user.UserService",
  "rpc.method": "GetUser",
  "rpc.grpc.status_code": 0
}
```

### 3.4 消息队列语义约定

#### 3.4.1 必需属性

- `messaging.system`: 消息系统类型
  - 常见值: `kafka`, `rabbitmq`, `nats`, `activemq`, `pulsar`

#### 3.4.2 可选属性

- `messaging.destination`: 目标主题或队列名
- `messaging.destination_kind`: 目标类型（topic, queue）
- `messaging.message_id`: 消息ID
- `messaging.operation`: 操作类型（publish, receive, process）
- `messaging.kafka.partition`: Kafka分区号
- `messaging.kafka.offset`: Kafka偏移量

#### 3.4.3 示例

```json
{
  "messaging.system": "kafka",
  "messaging.destination": "user-events",
  "messaging.destination_kind": "topic",
  "messaging.operation": "publish",
  "messaging.kafka.partition": 0
}
```

### 3.5 云平台语义约定

#### 3.5.1 必需属性

- `cloud.provider`: 云提供商
  - 常见值: `aws`, `azure`, `gcp`, `alibaba_cloud`, `tencent_cloud`

#### 3.5.2 可选属性

- `cloud.region`: 云区域
- `cloud.availability_zone`: 可用区
- `cloud.platform`: 云平台类型
- `cloud.account.id`: 云账户ID
- `cloud.resource_id`: 云资源ID

#### 3.5.3 示例

```json
{
  "cloud.provider": "aws",
  "cloud.region": "us-west-2",
  "cloud.availability_zone": "us-west-2a",
  "cloud.platform": "aws_ec2"
}
```

### 3.6 Kubernetes 语义约定

#### 3.6.1 可选属性

- `k8s.cluster.name`: 集群名称
- `k8s.namespace.name`: 命名空间
- `k8s.pod.name`: Pod名称
- `k8s.pod.uid`: Pod UID
- `k8s.container.name`: 容器名称
- `k8s.deployment.name`: 部署名称
- `k8s.service.name`: 服务名称
- `k8s.node.name`: 节点名称

#### 3.6.2 示例

```json
{
  "k8s.cluster.name": "production",
  "k8s.namespace.name": "default",
  "k8s.pod.name": "user-service-7d4b8c9f6-abc123",
  "k8s.pod.uid": "12345678-1234-1234-1234-123456789abc",
  "k8s.container.name": "user-service",
  "k8s.deployment.name": "user-service"
}
```

## 4. 资源语义约定

### 4.1 服务资源

- `service.name`: 服务名称（必需）
- `service.version`: 服务版本
- `service.instance.id`: 服务实例ID
- `service.namespace`: 服务命名空间

### 4.2 主机资源

- `host.name`: 主机名
- `host.id`: 主机ID
- `host.type`: 主机类型
- `host.arch`: 主机架构

### 4.3 容器资源

- `container.name`: 容器名称
- `container.id`: 容器ID
- `container.image.name`: 容器镜像名称
- `container.image.tag`: 容器镜像标签

## 5. 最佳实践

### 5.1 属性命名

- 使用官方语义约定中定义的属性名
- 避免创建自定义属性，除非确实需要
- 新增属性前先检查是否已有类似约定

### 5.2 数据类型

- 字符串属性使用双引号
- 数值属性使用原始数字类型
- 布尔属性使用 `true`/`false`
- 数组属性使用方括号

### 5.3 敏感信息处理

- 连接字符串需要脱敏
- 密码、密钥等敏感信息不应包含在属性中
- 使用环境变量或配置管理敏感信息

### 5.4 性能考虑

- 避免在属性中包含大量数据
- 使用合理的属性数量（通常不超过20个）
- 考虑属性的存储和传输成本

## 6. 治理流程

新增语义约定需要经过以下流程：

1. 在 `governance/` 目录下创建提案
2. 社区讨论和评审
3. 更新本文档
4. 更新各语言SDK实现
5. 更新测试用例

## 7. 参考资源

- [OpenTelemetry 官方语义约定](https://opentelemetry.io/docs/specs/semantic_conventions/)
- [语义约定规范](https://github.com/open-telemetry/opentelemetry-specification/tree/main/specification/semantic_conventions)
- [各语言实现](https://github.com/open-telemetry/opentelemetry-go/tree/main/semconv)
