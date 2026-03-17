---
title: 📘 Semantic Conventions速查手册
description: 📘 Semantic Conventions速查手册
 详细指南
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 参考资料
tags:
  - otlp
  - observability
status: published
---
# � Semantic Conventions速查手册

> **版本**: v1.29.0
> **最后更新**: 2025年10月9日
> **用途**: 快速查找OpenTelemetry语义约定标准

---

## 速查目录

- [� Semantic Conventions速查手册](#-semantic-conventions速查手册)
  - [速查目录](#速查目录)
  - [概述](#概述)
    - [什么是Semantic Conventions?](#什么是semantic-conventions)
    - [版本演进](#版本演进)
  - [� 通用属性](#-通用属性)
    - [核心通用属性](#核心通用属性)
    - [环境标识](#环境标识)
  - [� 资源属性](#-资源属性)
    - [Service (服务)](#service-服务)
    - [Container (容器)](#container-容器)
    - [Kubernetes (K8s)](#kubernetes-k8s)
    - [Cloud (云平台)](#cloud-云平台)
  - [Traces属性](#traces属性)
    - [Span通用属性](#span通用属性)
    - [Span Kind枚举](#span-kind枚举)
    - [错误属性](#错误属性)
  - [Metrics命名](#metrics命名)
    - [命名规范](#命名规范)
    - [常用Metrics](#常用metrics)
      - [HTTP Server](#http-server)
      - [HTTP Client](#http-client)
      - [Database](#database)
      - [System](#system)
    - [单位标准](#单位标准)
  - [Logs属性](#logs属性)
    - [核心Logs属性](#核心logs属性)
    - [日志级别](#日志级别)
  - [HTTP约定](#http约定)
    - [HTTP请求属性](#http请求属性)
    - [HTTP响应属性](#http响应属性)
    - [HTTP版本](#http版本)
    - [HTTP状态码分类](#http状态码分类)
  - [� 数据库约定](#-数据库约定)
    - [通用数据库属性](#通用数据库属性)
    - [SQL数据库](#sql数据库)
    - [NoSQL数据库](#nosql数据库)
      - [MongoDB](#mongodb)
      - [Redis](#redis)
    - [数据库系统枚举](#数据库系统枚举)
  - [� 消息队列约定](#-消息队列约定)
    - [Messaging属性](#messaging属性)
    - [Kafka特定属性](#kafka特定属性)
    - [RabbitMQ特定属性](#rabbitmq特定属性)
  - [☁ 云平台约定](#-云平台约定)
    - [AWS](#aws)
    - [Azure](#azure)
    - [Google Cloud Platform](#google-cloud-platform)
    - [阿里云](#阿里云)
  - [GenAI约定 (v1.29.0稳定) �](#genai约定-v1290稳定-)
    - [LLM调用属性](#llm调用属性)
    - [成本追踪属性](#成本追踪属性)
    - [Prompt属性](#prompt属性)
    - [支持的AI系统](#支持的ai系统)
  - [命名规范](#命名规范-1)
    - [属性命名规则](#属性命名规则)
    - [命名空间](#命名空间)
    - [Metric命名规则](#metric命名规则)
  - [快速查找工具](#快速查找工具)
    - [按技术栈查找](#按技术栈查找)
      - [Web应用](#web应用)
      - [后端服务](#后端服务)
      - [云原生](#云原生)
      - [AI应用](#ai应用)
  - [参考资源](#参考资源)
  - [最佳实践](#最佳实践)

---

## 概述

### 什么是Semantic Conventions?

语义约定定义了遥测数据（Traces、Metrics、Logs）的标准化命名和属性规范,确保不同系统间的互操作性。

### 版本演进

| 版本 | 发布时间 | 主要变更 |
|------|---------|---------|
| **v1.29.0** | 2024-10 | GenAI约定稳定 🆕 |
| v1.28.0 | 2024-08 | 云原生增强、数据库扩展 |
| v1.27.0 | 2024-06 | HTTP/3属性、容器属性 |

---

## � 通用属性

### 核心通用属性

| 属性 | 类型 | 示例 | 说明 |
|------|------|------|------|
| `service.name` | string | `"payment-api"` | **必需**,服务名称 |
| `service.version` | string | `"1.2.3"` | 服务版本 |
| `deployment.environment` | string | `"production"` | 部署环境 |
| `host.name` | string | `"web-server-01"` | 主机名 |
| `host.id` | string | `"i-0a1b2c3d"` | 主机唯一ID |

### 环境标识

```text
推荐值:
- production   (生产环境)
- staging      (预发布)
- development  (开发环境)
- test         (测试环境)
```

---

## � 资源属性

### Service (服务)

| 属性 | 必需 | 示例 | 说明 |
|------|------|------|------|
| `service.name` | ✅ | `"checkout-service"` | 服务名称 |
| `service.namespace` | ⬜ | `"ecommerce"` | 服务命名空间 |
| `service.instance.id` | ⬜ | `"pod-xyz-123"` | 实例ID |
| `service.version` | ⬜ | `"2.1.0"` | 版本号 |

### Container (容器)

| 属性 | 示例 | 说明 |
|------|------|------|
| `container.name` | `"nginx"` | 容器名称 |
| `container.id` | `"d4e5f6a7b8c9"` | 容器ID |
| `container.image.name` | `"nginx"` | 镜像名称 |
| `container.image.tag` | `"1.21-alpine"` | 镜像标签 |
| `container.runtime` | `"docker"` / `"containerd"` | 运行时 |

### Kubernetes (K8s)

| 属性 | 示例 | 说明 |
|------|------|------|
| `k8s.cluster.name` | `"prod-cluster-01"` | 集群名称 |
| `k8s.namespace.name` | `"default"` | 命名空间 |
| `k8s.pod.name` | `"web-pod-123"` | Pod名称 |
| `k8s.pod.uid` | `"a1b2c3d4-..."` | Pod UID |
| `k8s.deployment.name` | `"web-deployment"` | Deployment |
| `k8s.replicaset.name` | `"web-rs-abc123"` | ReplicaSet |
| `k8s.node.name` | `"node-01"` | 节点名称 |

### Cloud (云平台)

| 属性 | 示例 | 说明 |
|------|------|------|
| `cloud.provider` | `"aws"` / `"azure"` / `"gcp"` | 云提供商 |
| `cloud.region` | `"us-west-2"` | 区域 |
| `cloud.availability_zone` | `"us-west-2a"` | 可用区 |
| `cloud.account.id` | `"123456789012"` | 账户ID |
| `cloud.platform` | `"aws_ec2"` / `"aws_lambda"` | 平台服务 |

---

## Traces属性

### Span通用属性

| 属性 | 类型 | 示例 | 说明 |
|------|------|------|------|
| `span.kind` | enum | `"server"` | Span类型 |
| `status.code` | enum | `"OK"` / `"ERROR"` | 状态码 |
| `status.message` | string | `"Connection timeout"` | 错误描述 |

### Span Kind枚举

| 值 | 说明 | 使用场景 |
|----|------|---------|
| `INTERNAL` | 内部操作 | 函数调用、内部逻辑 |
| `SERVER` | 服务端接收 | HTTP服务端、gRPC服务端 |
| `CLIENT` | 客户端发送 | HTTP客户端、数据库客户端 |
| `PRODUCER` | 消息生产 | Kafka生产者、RabbitMQ发送 |
| `CONSUMER` | 消息消费 | Kafka消费者、RabbitMQ接收 |

### 错误属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `exception.type` | `"java.lang.NullPointerException"` | 异常类型 |
| `exception.message` | `"Object reference not set"` | 异常消息 |
| `exception.stacktrace` | `"at com.example..."` | 堆栈跟踪 |
| `exception.escaped` | `true` | 异常是否逃逸 |

---

## Metrics命名

### 命名规范

```text
格式: {namespace}.{component}.{metric_name}

示例:
- http.server.duration          (HTTP服务端响应时长)
- db.client.operation.duration  (数据库操作时长)
- system.cpu.utilization        (CPU使用率)
```

### 常用Metrics

#### HTTP Server

| Metric | 类型 | 单位 | 说明 |
|--------|------|------|------|
| `http.server.request.duration` | Histogram | `s` | 请求响应时长 |
| `http.server.active_requests` | UpDownCounter | `{requests}` | 活跃请求数 |
| `http.server.request.body.size` | Histogram | `By` | 请求体大小 |
| `http.server.response.body.size` | Histogram | `By` | 响应体大小 |

#### HTTP Client

| Metric | 类型 | 单位 | 说明 |
|--------|------|------|------|
| `http.client.request.duration` | Histogram | `s` | 请求时长 |
| `http.client.active_requests` | UpDownCounter | `{requests}` | 活跃请求 |

#### Database

| Metric | 类型 | 单位 | 说明 |
|--------|------|------|------|
| `db.client.operation.duration` | Histogram | `s` | 数据库操作时长 |
| `db.client.connections.usage` | UpDownCounter | `{connections}` | 连接数 |

#### System

| Metric | 类型 | 单位 | 说明 |
|--------|------|------|------|
| `system.cpu.utilization` | Gauge | `1` (比率) | CPU使用率 |
| `system.memory.usage` | UpDownCounter | `By` | 内存使用量 |
| `system.disk.io` | Counter | `By` | 磁盘I/O |
| `system.network.io` | Counter | `By` | 网络I/O |

### 单位标准

| 单位 | 符号 | 示例 |
|------|------|------|
| 字节 | `By` | `http.request.body.size` |
| 秒 | `s` | `http.server.duration` |
| 毫秒 | `ms` | `db.query.duration` |
| 比率 (0-1) | `1` | `system.cpu.utilization` |
| 百分比 | `%` | ⚠️ 不推荐,使用`1` |
| 计数 | `{items}` | `queue.messages` |

---

## Logs属性

### 核心Logs属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `log.level` | `"ERROR"` | 日志级别 |
| `log.message` | `"Failed to connect"` | 日志消息 |
| `log.logger.name` | `"com.example.MyClass"` | Logger名称 |
| `thread.id` | `12345` | 线程ID |
| `thread.name` | `"http-nio-8080-exec-1"` | 线程名称 |

### 日志级别

```text
标准级别 (从低到高):
- TRACE    (最详细)
- DEBUG    (调试信息)
- INFO     (常规信息) ← 默认
- WARN     (警告)
- ERROR    (错误)
- FATAL    (严重错误)
```

---

## HTTP约定

### HTTP请求属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `http.request.method` | `"GET"` / `"POST"` | HTTP方法 |
| `http.route` | `"/api/users/{id}"` | 路由模板 |
| `url.full` | `"https://api.example.com/users/123"` | 完整URL |
| `url.scheme` | `"https"` | 协议 |
| `url.path` | `"/api/users/123"` | 路径 |
| `url.query` | `"page=1&limit=10"` | 查询字符串 |
| `server.address` | `"api.example.com"` | 服务器地址 |
| `server.port` | `443` | 服务器端口 |
| `client.address` | `"192.168.1.100"` | 客户端地址 |
| `user_agent.original` | `"Mozilla/5.0..."` | User-Agent |

### HTTP响应属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `http.response.status_code` | `200` / `404` / `500` | 响应状态码 |
| `http.response.body.size` | `1024` | 响应体大小(字节) |

### HTTP版本

| 属性 | 示例 |
|------|------|
| `network.protocol.version` | `"1.1"` / `"2"` / `"3"` |

### HTTP状态码分类

```text
✅ 成功 (2xx):
  200 OK
  201 Created
  204 No Content

⚠️ 客户端错误 (4xx):
  400 Bad Request
  401 Unauthorized
  403 Forbidden
  404 Not Found
  429 Too Many Requests

❌ 服务端错误 (5xx):
  500 Internal Server Error
  502 Bad Gateway
  503 Service Unavailable
  504 Gateway Timeout
```

---

## � 数据库约定

### 通用数据库属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `db.system` | `"postgresql"` / `"mysql"` / `"mongodb"` | 数据库类型 |
| `db.name` | `"my_database"` | 数据库名称 |
| `db.user` | `"app_user"` | 数据库用户 |
| `db.connection_string` | `"postgresql://localhost:5432"` | 连接字符串(脱敏) |
| `server.address` | `"db.example.com"` | 数据库主机 |
| `server.port` | `5432` | 数据库端口 |

### SQL数据库

| 属性 | 示例 | 说明 |
|------|------|------|
| `db.operation` | `"SELECT"` / `"INSERT"` / `"UPDATE"` | SQL操作 |
| `db.statement` | `"SELECT * FROM users WHERE id = ?"` | SQL语句(参数化) |
| `db.sql.table` | `"users"` | 表名 |

### NoSQL数据库

#### MongoDB

| 属性 | 示例 |
|------|------|
| `db.mongodb.collection` | `"products"` |
| `db.operation` | `"find"` / `"insert"` |

#### Redis

| 属性 | 示例 |
|------|------|
| `db.redis.database_index` | `0` |
| `db.operation` | `"GET"` / `"SET"` |

### 数据库系统枚举

```text
SQL:
- postgresql
- mysql
- mssql
- oracle
- mariadb
- sqlite

NoSQL:
- mongodb
- redis
- cassandra
- elasticsearch
- dynamodb
- couchbase
```

---

## � 消息队列约定

### Messaging属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `messaging.system` | `"kafka"` / `"rabbitmq"` | 消息系统 |
| `messaging.operation` | `"publish"` / `"receive"` | 操作类型 |
| `messaging.destination.name` | `"orders"` | 目标(Topic/Queue) |
| `messaging.message.id` | `"msg-123456"` | 消息ID |
| `messaging.message.body.size` | `2048` | 消息大小(字节) |
| `messaging.consumer.group.name` | `"order-processors"` | 消费者组 |

### Kafka特定属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `messaging.kafka.destination.partition` | `3` | 分区号 |
| `messaging.kafka.message.offset` | `12345` | 消息偏移量 |
| `messaging.kafka.message.key` | `"user-123"` | 消息Key |
| `messaging.kafka.consumer.group` | `"payment-group"` | 消费者组 |

### RabbitMQ特定属性

| 属性 | 示例 |
|------|------|
| `messaging.rabbitmq.destination.routing_key` | `"orders.new"` |
| `messaging.rabbitmq.message.delivery_tag` | `123` |

---

## ☁ 云平台约定

### AWS

| 属性 | 示例 | 说明 |
|------|------|------|
| `cloud.provider` | `"aws"` | 云提供商 |
| `cloud.platform` | `"aws_ec2"` / `"aws_lambda"` | AWS服务 |
| `cloud.region` | `"us-east-1"` | AWS区域 |
| `aws.ecs.task.arn` | `"arn:aws:ecs:..."` | ECS任务ARN |
| `aws.lambda.invoked_arn` | `"arn:aws:lambda:..."` | Lambda ARN |

### Azure

| 属性 | 示例 | 说明 |
|------|------|------|
| `cloud.provider` | `"azure"` | 云提供商 |
| `cloud.platform` | `"azure_vm"` / `"azure_functions"` | Azure服务 |
| `cloud.region` | `"East US"` | Azure区域 |
| `azure.vm.scaleset.name` | `"my-scaleset"` | VM Scale Set |

### Google Cloud Platform

| 属性 | 示例 | 说明 |
|------|------|------|
| `cloud.provider` | `"gcp"` | 云提供商 |
| `cloud.platform` | `"gcp_compute_engine"` / `"gcp_cloud_run"` | GCP服务 |
| `cloud.region` | `"us-central1"` | GCP区域 |
| `gcp.gce.instance.name` | `"my-instance"` | GCE实例 |

### 阿里云

| 属性 | 示例 | 说明 |
|------|------|------|
| `cloud.provider` | `"alibaba_cloud"` | 云提供商 |
| `cloud.platform` | `"alibaba_cloud_ecs"` | 阿里云服务 |
| `cloud.region` | `"cn-hangzhou"` | 阿里云区域 |

---

## GenAI约定 (v1.29.0稳定) �

### LLM调用属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `gen_ai.system` | `"openai"` / `"anthropic"` / `"azure_openai"` | AI系统 |
| `gen_ai.request.model` | `"gpt-4"` / `"claude-3-opus"` | 模型名称 |
| `gen_ai.request.max_tokens` | `2048` | 最大Token数 |
| `gen_ai.request.temperature` | `0.7` | 温度参数 |
| `gen_ai.request.top_p` | `0.9` | Top-P采样 |
| `gen_ai.response.model` | `"gpt-4-0613"` | 实际模型版本 |
| `gen_ai.response.finish_reason` | `"stop"` / `"length"` | 结束原因 |
| `gen_ai.usage.input_tokens` | `150` | 输入Token数 |
| `gen_ai.usage.output_tokens` | `320` | 输出Token数 |

### 成本追踪属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `gen_ai.usage.cost` | `0.0052` | 调用成本(USD) |

### Prompt属性

| 属性 | 示例 | 说明 |
|------|------|------|
| `gen_ai.prompt.0.role` | `"system"` / `"user"` / `"assistant"` | 角色 |
| `gen_ai.prompt.0.content` | `"You are a helpful assistant"` | 内容 |

### 支持的AI系统

```text
✅ 稳定支持:
- openai           (OpenAI GPT系列)
- anthropic        (Claude系列)
- azure_openai     (Azure OpenAI服务)
- vertex_ai        (Google Vertex AI)
- bedrock          (AWS Bedrock)
- cohere           (Cohere AI)

🔧 社区支持:
- huggingface      (Hugging Face模型)
- ollama           (本地LLM部署)
- mistral          (Mistral AI)
```

---

## 命名规范

### 属性命名规则

```text
✅ 推荐:
- 使用小写字母和点号分隔: http.request.method
- 使用命名空间: {namespace}.{attribute}
- 使用描述性名称: http.response.status_code

❌ 避免:
- 驼峰命名: httpRequestMethod
- 下划线: http_request_method
- 缩写: http.req.mth
- 过长: http.server.incoming.request.method.name
```

### 命名空间

| 命名空间 | 用途 | 示例 |
|---------|------|------|
| `http.*` | HTTP协议 | `http.request.method` |
| `db.*` | 数据库 | `db.system` |
| `messaging.*` | 消息队列 | `messaging.system` |
| `rpc.*` | RPC调用 | `rpc.service` |
| `faas.*` | Serverless | `faas.trigger` |
| `cloud.*` | 云平台 | `cloud.provider` |
| `k8s.*` | Kubernetes | `k8s.pod.name` |
| `gen_ai.*` | GenAI | `gen_ai.system` |

### Metric命名规则

```text
格式: {namespace}.{component}.{metric_name}

✅ 推荐:
- http.server.request.duration   (HTTP服务端请求时长)
- db.client.operation.duration   (数据库客户端操作时长)
- system.cpu.utilization         (系统CPU使用率)

❌ 避免:
- httpServerDuration             (使用点号分隔)
- http_server_duration           (使用点号而非下划线)
- duration                       (缺少命名空间)
```

---

## 快速查找工具

### 按技术栈查找

#### Web应用

- [HTTP约定](#http约定)
- [通用属性](#通用属性)
- [Traces属性](#traces属性)

#### 后端服务

- [数据库约定](#数据库约定)
- [消息队列约定](#消息队列约定)
- [云平台约定](#云平台约定)

#### 云原生

- [Kubernetes](#kubernetes-k8s)
- [Container](#container-容器)
- [云平台约定](#云平台约定)

#### AI应用

- [GenAI约定](#genai约定-v1290稳定-)

---

## 参考资源

| 资源 | 链接 |
|------|------|
| **官方语义约定** | <https://opentelemetry.io/docs/specs/semconv/> |
| **HTTP约定** | <https://opentelemetry.io/docs/specs/semconv/http/> |
| **数据库约定** | <https://opentelemetry.io/docs/specs/semconv/database/> |
| **消息队列约定** | <https://opentelemetry.io/docs/specs/semconv/messaging/> |
| **GenAI约定** | <https://opentelemetry.io/docs/specs/semconv/gen-ai/> |
| **云平台约定** | <https://opentelemetry.io/docs/specs/semconv/cloud/> |
| **Kubernetes约定** | <https://opentelemetry.io/docs/specs/semconv/resource/k8s/> |

---

## 最佳实践

```text
✅ 使用标准属性名称,不要自定义
✅ 使用推荐的单位 (s, By, 1)
✅ 为服务设置完整的资源属性
✅ HTTP状态码使用数字而非字符串
✅ 敏感信息脱敏 (密码、Token、PII)
✅ 使用资源属性而非Span属性 (service.name)
✅ 保持属性基数可控 (<100个唯一值)
✅ 遵循命名规范 (小写+点号)
✅ 记录异常堆栈 (exception.stacktrace)
✅ 定期检查与最新标准的一致性
```

---

**最后更新**: 2025年10月9日
**上一篇**: [OTLP协议速查手册](./01_OTLP协议速查手册.md)
**下一篇**: [Collector配置速查手册](./03_Collector配置速查手册.md)

