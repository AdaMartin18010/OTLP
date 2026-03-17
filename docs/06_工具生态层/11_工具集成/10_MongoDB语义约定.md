---
title: MongoDB语义约定详解
description: MongoDB语义约定详解 详细指南和最佳实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 标准规范
tags:
  - otlp
  - observability
  - performance
  - optimization
  - security
  - compliance
status: published
---
# MongoDB语义约定详解

> **文档数据库**: MongoDB Tracing与Metrics完整规范
> **最后更新**: 2025年10月8日

---

## 目录

- [MongoDB语义约定详解](#mongodb语义约定详解)
  - [目录](#目录)
  - [1. MongoDB概述](#1-mongodb概述)
    - [1.1 MongoDB特点](#11-mongodb特点)
    - [1.2 核心架构](#12-核心架构)
  - [2. MongoDB通用属性](#2-mongodb通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. 操作类型属性](#3-操作类型属性)
    - [3.1 CRUD操作](#31-crud操作)
    - [3.2 聚合操作](#32-聚合操作)
  - [4. 连接属性](#4-连接属性)
    - [4.1 连接字符串](#41-连接字符串)
    - [4.2 副本集属性](#42-副本集属性)
  - [5. Go实现示例](#5-go实现示例)
    - [5.1 基本CRUD操作](#51-基本crud操作)
    - [5.2 聚合操作](#52-聚合操作)
    - [5.3 事务操作](#53-事务操作)
  - [6. Python实现示例](#6-python实现示例)
    - [6.1 PyMongo + OpenTelemetry](#61-pymongo--opentelemetry)
    - [6.2 Motor (异步)](#62-motor-异步)
  - [7. Java实现示例](#7-java实现示例)
    - [7.1 MongoDB Java Driver](#71-mongodb-java-driver)
  - [8. Metrics定义](#8-metrics定义)
    - [8.1 客户端Metrics](#81-客户端metrics)
    - [8.2 服务器Metrics](#82-服务器metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 安全考虑](#92-安全考虑)
    - [9.3 监控建议](#93-监控建议)

---

## 1. MongoDB概述

### 1.1 MongoDB特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MongoDB - 文档数据库:

核心特性:
✅ 文档存储 (BSON格式)
✅ 灵活Schema (动态字段)
✅ 强大查询语言 (MQL)
✅ 水平扩展 (分片)
✅ 高可用 (副本集)
✅ 聚合框架 (Pipeline)
✅ 全文搜索
✅ 地理空间查询
✅ 事务支持 (4.0+)

vs 关系型数据库:
✅ 无需预定义Schema
✅ 嵌套文档支持
✅ 水平扩展更容易
✅ 开发效率更高

适用场景:
✅ 内容管理系统
✅ 实时分析
✅ 物联网数据
✅ 移动应用后端
✅ 游戏数据存储
✅ 日志聚合

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MongoDB架构:

单节点:
┌──────────────┐
│   MongoDB    │
│   (mongod)   │
└──────────────┘

副本集 (Replica Set):
┌──────────┐     ┌──────────┐     ┌──────────┐
│ Primary  │────►│Secondary │────►│Secondary │
└──────────┘     └──────────┘     └──────────┘
      │                                  │
      └──────────────────────────────────┘
              (选举 + 同步)

分片集群 (Sharded Cluster):
                ┌───────────┐
                │  mongos   │ (路由)
                └─────┬─────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
   ┌────▼────┐   ┌────▼────┐   ┌────▼────┐
   │ Shard 1 │   │ Shard 2 │   │ Shard 3 │
   │(副本集) │   │(副本集) │   │(副本集) │
   └─────────┘   └─────────┘   └─────────┘

   配置服务器 (Config Servers):
   存储集群元数据

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. MongoDB通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.system` | string | 数据库系统 | `"mongodb"` |
| `db.operation` | string | 操作类型 | `"find"`, `"insert"`, `"update"` |
| `db.name` | string | 数据库名称 | `"myapp"` |
| `db.mongodb.collection` | string | 集合名称 | `"users"` |
| `net.peer.name` | string | MongoDB服务器地址 | `"mongo.example.com"` |
| `net.peer.port` | int | MongoDB端口 | `27017` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.statement` | string | 查询语句 | `"{\"name\": \"John\"}"` |
| `db.user` | string | 数据库用户 | `"app_user"` |
| `db.mongodb.replica_set` | string | 副本集名称 | `"rs0"` |
| `db.mongodb.connection_id` | string | 连接ID | `"conn123"` |
| `db.mongodb.read_preference` | string | 读偏好 | `"primary"`, `"secondaryPreferred"` |
| `db.response.returned_count` | int | 返回记录数 | `10` |

---

## 3. 操作类型属性

### 3.1 CRUD操作

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MongoDB CRUD操作:

Create (插入):
✅ db.operation = "insert"
✅ db.mongodb.collection
📋 db.statement (可选，避免PII)

Read (查询):
✅ db.operation = "find"
✅ db.mongodb.collection
📋 db.statement (过滤条件)
📋 db.response.returned_count

Update (更新):
✅ db.operation = "update"
✅ db.mongodb.collection
📋 db.statement (过滤条件 + 更新内容)
📋 db.response.modified_count

Delete (删除):
✅ db.operation = "delete"
✅ db.mongodb.collection
📋 db.statement (过滤条件)
📋 db.response.deleted_count

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 操作 | db.operation | 额外属性 |
|------|--------------|----------|
| InsertOne | `"insert"` | - |
| InsertMany | `"insert"` | `db.mongodb.batch_size` |
| Find | `"find"` | `db.mongodb.limit`, `db.mongodb.skip` |
| FindOne | `"find"` | `db.mongodb.limit=1` |
| UpdateOne | `"update"` | `db.response.modified_count` |
| UpdateMany | `"update"` | `db.response.modified_count` |
| DeleteOne | `"delete"` | `db.response.deleted_count` |
| DeleteMany | `"delete"` | `db.response.deleted_count` |
| FindOneAndUpdate | `"findAndModify"` | - |
| FindOneAndReplace | `"findAndModify"` | - |
| FindOneAndDelete | `"findAndModify"` | - |

### 3.2 聚合操作

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.operation` | string | 操作类型 | `"aggregate"` |
| `db.mongodb.aggregate.pipeline` | string | 聚合管道 (可选) | `"[{\"$match\":...}]"` |
| `db.mongodb.aggregate.stages` | int | 管道阶段数 | `3` |

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    MongoDB聚合操作:

    常见阶段:
    - $match: 过滤文档
    - $group: 分组聚合
    - $sort: 排序
    - $project: 投影字段
    - $lookup: 关联查询
    - $limit: 限制数量
    - $skip: 跳过记录

    示例:
    ```json
    [
    {"$match": {"status": "active"}},
    {"$group": {"_id": "$category", "count": {"$sum": 1}}},
    {"$sort": {"count": -1}}
    ]
    ```

    追踪属性:

    ```go
    span.SetAttributes(
        attribute.String("db.operation", "aggregate"),
        attribute.String("db.mongodb.collection", "orders"),
        attribute.Int("db.mongodb.aggregate.stages", 3),
        // 可选: pipeline详情 (注意大小)
    )
    ```

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

---

## 4. 连接属性

### 4.1 连接字符串

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MongoDB连接字符串:

单节点:
mongodb://user:pass@localhost:27017/mydb

副本集:
mongodb://user:pass@host1:27017,host2:27017,host3:27017/mydb?replicaSet=rs0

分片集群:
mongodb://user:pass@mongos1:27017,mongos2:27017/mydb

⚠️  安全注意:
❌ 不要在db.statement中记录密码
❌ 不要在属性中包含认证信息
✅ 使用net.peer.name记录主机名
✅ 使用db.user记录用户名 (不含密码)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.2 副本集属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.mongodb.replica_set` | string | 副本集名称 | `"rs0"` |
| `db.mongodb.read_preference` | string | 读偏好 | `"primary"`, `"secondary"`, `"primaryPreferred"`, `"secondaryPreferred"`, `"nearest"` |
| `db.mongodb.read_concern` | string | 读关注 | `"local"`, `"majority"`, `"linearizable"` |
| `db.mongodb.write_concern.w` | string | 写关注 | `"1"`, `"majority"` |

---

## 5. Go实现示例

### 5.1 基本CRUD操作

```go
package main

import (
    "context"

    "go.mongodb.org/mongo-driver/bson"
    "go.mongodb.org/mongo-driver/mongo"
    "go.mongodb.org/mongo-driver/mongo/options"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

type User struct {
    ID   string `bson:"_id,omitempty"`
    Name string `bson:"name"`
    Email string `bson:"email"`
}

func InsertUserWithTracing(
    ctx context.Context,
    collection *mongo.Collection,
    user *User,
) error {
    tracer := otel.Tracer("mongodb-client")

    // 创建Span
    ctx, span := tracer.Start(ctx, "mongodb.insert",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("insert"),
            semconv.DBNameKey.String(collection.Database().Name()),
            attribute.String("db.mongodb.collection",
                collection.Name()),
            attribute.String("net.peer.name", "localhost"),
            attribute.Int("net.peer.port", 27017),
        ),
    )
    defer span.End()

    // 执行插入
    result, err := collection.InsertOne(ctx, user)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "insert failed")
        return err
    }

    // 记录插入的ID
    span.SetAttributes(
        attribute.String("db.mongodb.inserted_id",
            result.InsertedID.(string)),
    )

    span.SetStatus(codes.Ok, "inserted")
    return nil
}

func FindUserWithTracing(
    ctx context.Context,
    collection *mongo.Collection,
    filter bson.M,
) (*User, error) {
    tracer := otel.Tracer("mongodb-client")

    // 创建Span
    ctx, span := tracer.Start(ctx, "mongodb.find",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("find"),
            semconv.DBNameKey.String(collection.Database().Name()),
            attribute.String("db.mongodb.collection",
                collection.Name()),
            // 可选: 记录查询过滤条件 (注意隐私)
            // attribute.String("db.statement",
            //     fmt.Sprintf("%v", filter)),
        ),
    )
    defer span.End()

    // 执行查询
    var user User
    err := collection.FindOne(ctx, filter).Decode(&user)
    if err != nil {
        if err == mongo.ErrNoDocuments {
            span.SetStatus(codes.Ok, "no documents")
            return nil, nil
        }
        span.RecordError(err)
        span.SetStatus(codes.Error, "find failed")
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("db.response.returned_count", 1),
    )
    span.SetStatus(codes.Ok, "found")

    return &user, nil
}

func UpdateUserWithTracing(
    ctx context.Context,
    collection *mongo.Collection,
    filter bson.M,
    update bson.M,
) error {
    tracer := otel.Tracer("mongodb-client")

    ctx, span := tracer.Start(ctx, "mongodb.update",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("update"),
            semconv.DBNameKey.String(collection.Database().Name()),
            attribute.String("db.mongodb.collection",
                collection.Name()),
        ),
    )
    defer span.End()

    // 执行更新
    result, err := collection.UpdateMany(ctx, filter, update)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "update failed")
        return err
    }

    span.SetAttributes(
        attribute.Int64("db.response.matched_count",
            result.MatchedCount),
        attribute.Int64("db.response.modified_count",
            result.ModifiedCount),
    )
    span.SetStatus(codes.Ok, "updated")

    return nil
}

func DeleteUserWithTracing(
    ctx context.Context,
    collection *mongo.Collection,
    filter bson.M,
) error {
    tracer := otel.Tracer("mongodb-client")

    ctx, span := tracer.Start(ctx, "mongodb.delete",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("delete"),
            semconv.DBNameKey.String(collection.Database().Name()),
            attribute.String("db.mongodb.collection",
                collection.Name()),
        ),
    )
    defer span.End()

    // 执行删除
    result, err := collection.DeleteMany(ctx, filter)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "delete failed")
        return err
    }

    span.SetAttributes(
        attribute.Int64("db.response.deleted_count",
            result.DeletedCount),
    )
    span.SetStatus(codes.Ok, "deleted")

    return nil
}
```

### 5.2 聚合操作

```go
func AggregateWithTracing(
    ctx context.Context,
    collection *mongo.Collection,
    pipeline mongo.Pipeline,
) ([]bson.M, error) {
    tracer := otel.Tracer("mongodb-client")

    ctx, span := tracer.Start(ctx, "mongodb.aggregate",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("aggregate"),
            semconv.DBNameKey.String(collection.Database().Name()),
            attribute.String("db.mongodb.collection",
                collection.Name()),
            attribute.Int("db.mongodb.aggregate.stages",
                len(pipeline)),
        ),
    )
    defer span.End()

    // 执行聚合
    cursor, err := collection.Aggregate(ctx, pipeline)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "aggregate failed")
        return nil, err
    }
    defer cursor.Close(ctx)

    // 读取结果
    var results []bson.M
    if err := cursor.All(ctx, &results); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "decode failed")
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("db.response.returned_count", len(results)),
    )
    span.SetStatus(codes.Ok, "aggregated")

    return results, nil
}
```

### 5.3 事务操作

```go
func TransactionWithTracing(
    ctx context.Context,
    client *mongo.Client,
    fn func(sessCtx mongo.SessionContext) error,
) error {
    tracer := otel.Tracer("mongodb-client")

    ctx, span := tracer.Start(ctx, "mongodb.transaction",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMongoDB,
            semconv.DBOperationKey.String("transaction"),
        ),
    )
    defer span.End()

    // 开始会话
    session, err := client.StartSession()
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "start session failed")
        return err
    }
    defer session.EndSession(ctx)

    // 执行事务
    err = session.WithTransaction(ctx, func(sessCtx mongo.SessionContext) (interface{}, error) {
        return nil, fn(sessCtx)
    })

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "transaction failed")
        return err
    }

    span.SetStatus(codes.Ok, "committed")
    return nil
}
```

---

## 6. Python实现示例

### 6.1 PyMongo + OpenTelemetry

```python
from pymongo import MongoClient
from opentelemetry import trace
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

def insert_user_with_tracing(collection, user: dict):
    """插入用户with tracing"""
    with tracer.start_as_current_span(
        "mongodb.insert",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "mongodb",
            SpanAttributes.DB_OPERATION: "insert",
            SpanAttributes.DB_NAME: collection.database.name,
            "db.mongodb.collection": collection.name,
            "net.peer.name": "localhost",
            "net.peer.port": 27017,
        }
    ) as span:
        try:
            result = collection.insert_one(user)

            span.set_attribute("db.mongodb.inserted_id",
                             str(result.inserted_id))
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def find_user_with_tracing(collection, filter_dict: dict):
    """查询用户with tracing"""
    with tracer.start_as_current_span(
        "mongodb.find",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "mongodb",
            SpanAttributes.DB_OPERATION: "find",
            SpanAttributes.DB_NAME: collection.database.name,
            "db.mongodb.collection": collection.name,
        }
    ) as span:
        try:
            result = collection.find_one(filter_dict)

            if result:
                span.set_attribute("db.response.returned_count", 1)
            else:
                span.set_attribute("db.response.returned_count", 0)

            span.set_status(Status(StatusCode.OK))
            return result

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def aggregate_with_tracing(collection, pipeline: list):
    """聚合操作with tracing"""
    with tracer.start_as_current_span(
        "mongodb.aggregate",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "mongodb",
            SpanAttributes.DB_OPERATION: "aggregate",
            SpanAttributes.DB_NAME: collection.database.name,
            "db.mongodb.collection": collection.name,
            "db.mongodb.aggregate.stages": len(pipeline),
        }
    ) as span:
        try:
            cursor = collection.aggregate(pipeline)
            results = list(cursor)

            span.set_attribute("db.response.returned_count",
                             len(results))
            span.set_status(Status(StatusCode.OK))

            return results

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

### 6.2 Motor (异步)

```python
from motor.motor_asyncio import AsyncIOMotorClient
from opentelemetry import trace

tracer = trace.get_tracer(__name__)

async def insert_user_async_with_tracing(collection, user: dict):
    """异步插入用户with tracing"""
    with tracer.start_as_current_span(
        "mongodb.insert",
        kind=SpanKind.CLIENT
    ) as span:
        try:
            result = await collection.insert_one(user)
            span.set_attribute("db.mongodb.inserted_id",
                             str(result.inserted_id))
            span.set_status(Status(StatusCode.OK))
            return result
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

---

## 7. Java实现示例

### 7.1 MongoDB Java Driver

```java
import com.mongodb.client.*;
import org.bson.Document;
import io.opentelemetry.api.trace.*;
import io.opentelemetry.context.Context;

public class MongoDBTracing {

    private static final Tracer tracer =
        openTelemetry.getTracer("mongodb-client");

    public void insertUserWithTracing(
        MongoCollection<Document> collection,
        Document user
    ) {
        Span span = tracer.spanBuilder("mongodb.insert")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("db.system", "mongodb")
            .setAttribute("db.operation", "insert")
            .setAttribute("db.name", collection.getNamespace().getDatabaseName())
            .setAttribute("db.mongodb.collection", collection.getNamespace().getCollectionName())
            .startSpan();

        try (Scope scope = span.makeCurrent()) {
            // 执行插入
            collection.insertOne(user);

            // 记录ID
            span.setAttribute("db.mongodb.inserted_id",
                user.getObjectId("_id").toString());
            span.setStatus(StatusCode.OK);

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR);
            throw e;
        } finally {
            span.end();
        }
    }

    public Document findUserWithTracing(
        MongoCollection<Document> collection,
        Document filter
    ) {
        Span span = tracer.spanBuilder("mongodb.find")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("db.system", "mongodb")
            .setAttribute("db.operation", "find")
            .setAttribute("db.name", collection.getNamespace().getDatabaseName())
            .setAttribute("db.mongodb.collection", collection.getNamespace().getCollectionName())
            .startSpan();

        try (Scope scope = span.makeCurrent()) {
            Document result = collection.find(filter).first();

            if (result != null) {
                span.setAttribute("db.response.returned_count", 1);
            } else {
                span.setAttribute("db.response.returned_count", 0);
            }

            span.setStatus(StatusCode.OK);
            return result;

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR);
            throw e;
        } finally {
            span.end();
        }
    }
}
```

---

## 8. Metrics定义

### 8.1 客户端Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `db.client.operation.duration` | Histogram | ms | 操作延迟 |
| `db.client.operations` | Counter | operations | 操作次数 |
| `db.client.connections.active` | Gauge | connections | 活跃连接数 |
| `db.client.connections.idle` | Gauge | connections | 空闲连接数 |
| `db.client.errors` | Counter | errors | 错误次数 |

**推荐标签**:

- `db.operation`: 操作类型
- `db.mongodb.collection`: 集合名称
- `net.peer.name`: 服务器地址

### 8.2 服务器Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `db.mongodb.connections.current` | Gauge | connections | 当前连接数 |
| `db.mongodb.operations.count` | Counter | operations | 操作统计 |
| `db.mongodb.memory.resident` | Gauge | MB | 常驻内存 |
| `db.mongodb.memory.virtual` | Gauge | MB | 虚拟内存 |
| `db.mongodb.opcounters` | Counter | operations | 操作计数器 |

---

## 9. 最佳实践

### 9.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化建议:

1. 索引优化 ⭐⭐⭐⭐⭐
   - 为查询字段创建索引
   - 使用复合索引
   - 监控慢查询

2. 连接池 ⭐⭐⭐⭐⭐
   - 配置合理的池大小
   - 复用连接
   - 监控连接数

3. 批量操作 ⭐⭐⭐⭐
   - 使用InsertMany
   - 使用BulkWrite
   - 减少网络往返

4. 投影优化 ⭐⭐⭐⭐
   - 只返回需要的字段
   - 减少数据传输

5. 聚合优化 ⭐⭐⭐⭐
   - $match尽早
   - 使用索引
   - 限制结果集

6. Read Preference ⭐⭐⭐⭐
   - 读写分离
   - Secondary读取 (非强一致性)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 安全考虑

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

安全最佳实践:

1. 认证授权 ⭐⭐⭐⭐⭐
   - 启用身份验证
   - 最小权限原则
   - 使用SCRAM-SHA-256

2. 网络安全 ⭐⭐⭐⭐⭐
   - TLS/SSL加密
   - 防火墙规则
   - 绑定内网IP

3. 敏感数据 ⭐⭐⭐⭐⭐
   - 不要在db.statement中记录密码
   - 不要在追踪中包含PII
   - 使用字段级加密

4. 注入防护 ⭐⭐⭐⭐⭐
   - 使用参数化查询
   - 验证输入
   - 避免eval

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. 性能指标
   - 查询延迟 (p50, p99)
   - 操作TPS
   - 慢查询数量

2. 连接指标
   - 活跃连接数
   - 连接池使用率
   - 连接建立失败

3. 错误指标
   - 错误率
   - 超时次数
   - 连接错误

4. 资源指标
   - CPU使用率
   - 内存使用
   - 磁盘I/O

告警规则:
- 查询延迟 > 100ms (p99)
- 慢查询 > 10/分钟
- 错误率 > 1%
- 连接池使用率 > 80%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成
**MongoDB版本**: 4.0+
**适用场景**: 文档存储、内容管理、实时分析、IoT

**关键特性**:

- ✅ 完整CRUD操作追踪
- ✅ 聚合Pipeline追踪
- ✅ 事务操作支持
- ✅ 副本集属性
- ✅ Go/Python/Java完整示例
- ✅ 性能优化建议
- ✅ 安全最佳实践

