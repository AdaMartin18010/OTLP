---
title: Cassandra语义约定详解
description: Cassandra语义约定详解 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 标准规范
tags:
  - otlp
  - observability
  - performance
  - optimization
status: published
---
# Cassandra语义约定详解

> **分布式列式数据库**: Apache Cassandra Tracing与Metrics完整规范
> **最后更新**: 2025年10月8日

---

## 目录

- [Cassandra语义约定详解](#cassandra语义约定详解)
  - [目录](#目录)
  - [1. Cassandra概述](#1-cassandra概述)
    - [1.1 Cassandra特点](#11-cassandra特点)
    - [1.2 核心架构](#12-核心架构)
  - [2. Cassandra通用属性](#2-cassandra通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. 操作类型属性](#3-操作类型属性)
    - [3.1 CQL操作](#31-cql操作)
    - [3.2 批量操作](#32-批量操作)
  - [4. 连接属性](#4-连接属性)
    - [4.1 集群属性](#41-集群属性)
    - [4.2 一致性级别](#42-一致性级别)
  - [5. Go实现示例](#5-go实现示例)
    - [5.1 基本CRUD操作](#51-基本crud操作)
    - [5.2 批量操作](#52-批量操作)
    - [5.3 预处理语句](#53-预处理语句)
  - [6. Python实现示例](#6-python实现示例)
    - [6.1 cassandra-driver](#61-cassandra-driver)
    - [6.2 异步操作](#62-异步操作)
  - [7. Java实现示例](#7-java实现示例)
    - [7.1 DataStax Java Driver](#71-datastax-java-driver)
  - [8. Metrics定义](#8-metrics定义)
    - [8.1 客户端Metrics](#81-客户端metrics)
    - [8.2 服务器Metrics](#82-服务器metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 数据建模](#92-数据建模)
    - [9.3 监控建议](#93-监控建议)

---

## 1. Cassandra概述

### 1.1 Cassandra特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Apache Cassandra - 分布式NoSQL:

核心特性:
✅ 无中心架构 (Masterless)
✅ 线性扩展 (Linear Scalability)
✅ 高可用 (Multi-DC复制)
✅ 最终一致性 (Tunable Consistency)
✅ 列族存储 (Wide Column Store)
✅ CQL查询语言 (类SQL)
✅ 无单点故障 (No SPOF)
✅ 地理分布 (Geo-Distribution)

vs 关系型数据库:
✅ 水平扩展更容易
✅ 写入性能极高
✅ 无需预定义Schema
✅ 跨数据中心复制

vs MongoDB:
✅ 更好的写入性能
✅ 更好的线性扩展
✅ 无主节点架构

适用场景:
✅ 时序数据 (IoT, 日志)
✅ 高写入负载
✅ 多数据中心
✅ 大规模数据存储
✅ 实时分析

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cassandra架构:

无中心架构 (Peer-to-Peer):
┌────────┐     ┌────────┐     ┌────────┐
│ Node 1 │◄───►│ Node 2 │◄───►│ Node 3 │
└────────┘     └────────┘     └────────┘
     ▲              │              │
     │              │              │
     └──────────────┴──────────────┘
          (Gossip Protocol)

一致性哈希 (Consistent Hashing):
Token Ring:
   Node1 (0-255)
   Node2 (256-511)
   Node3 (512-767)
   ...

数据复制 (Replication):
Replication Factor = 3
┌──────────────┐
│   Primary    │
│   (Node 1)   │
└──────┬───────┘
       │
   ┌───┴───┐
   │       │
   ▼       ▼
┌──────┐ ┌──────┐
│Replica│ │Replica│
│(Node2)│ │(Node3)│
└──────┘ └──────┘

多数据中心:
DC1 (US-East)    DC2 (EU-West)
┌────┬────┬────┐ ┌────┬────┬────┐
│N1  │N2  │N3  │ │N4  │N5  │N6  │
└────┴────┴────┘ └────┴────┴────┘
      ▲                ▲
      └────────────────┘
      (跨DC复制)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Cassandra通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.system` | string | 数据库系统 | `"cassandra"` |
| `db.operation` | string | 操作类型 | `"SELECT"`, `"INSERT"`, `"UPDATE"` |
| `db.name` | string | Keyspace名称 | `"myapp"` |
| `db.cassandra.table` | string | 表名称 | `"users"` |
| `net.peer.name` | string | Cassandra节点地址 | `"cassandra.example.com"` |
| `net.peer.port` | int | Cassandra端口 | `9042` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.statement` | string | CQL语句 | `"SELECT * FROM users WHERE id = ?"` |
| `db.cassandra.consistency_level` | string | 一致性级别 | `"QUORUM"`, `"ONE"` |
| `db.cassandra.coordinator_dc` | string | 协调器数据中心 | `"us-east-1"` |
| `db.cassandra.coordinator_id` | string | 协调器节点ID | `"node-1"` |
| `db.cassandra.page_size` | int | 分页大小 | `5000` |
| `db.cassandra.speculative_execution_count` | int | 推测执行次数 | `0` |
| `db.response.returned_rows` | int | 返回行数 | `10` |

---

## 3. 操作类型属性

### 3.1 CQL操作

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cassandra CQL操作:

SELECT (查询):
✅ db.operation = "SELECT"
✅ db.cassandra.table
📋 db.statement
📋 db.cassandra.consistency_level
📋 db.response.returned_rows

INSERT (插入):
✅ db.operation = "INSERT"
✅ db.cassandra.table
📋 db.statement
📋 db.cassandra.consistency_level

UPDATE (更新):
✅ db.operation = "UPDATE"
✅ db.cassandra.table
📋 db.statement
📋 db.cassandra.consistency_level

DELETE (删除):
✅ db.operation = "DELETE"
✅ db.cassandra.table
📋 db.statement
📋 db.cassandra.consistency_level

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| CQL命令 | db.operation | 额外属性 |
|---------|--------------|----------|
| SELECT | `"SELECT"` | `db.response.returned_rows` |
| INSERT | `"INSERT"` | - |
| UPDATE | `"UPDATE"` | - |
| DELETE | `"DELETE"` | - |
| BATCH | `"BATCH"` | `db.cassandra.batch_size` |
| CREATE TABLE | `"CREATE TABLE"` | - |
| ALTER TABLE | `"ALTER TABLE"` | - |
| TRUNCATE | `"TRUNCATE"` | - |

### 3.2 批量操作

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.operation` | string | 操作类型 | `"BATCH"` |
| `db.cassandra.batch_size` | int | 批量大小 | `100` |
| `db.cassandra.batch_type` | string | 批量类型 | `"LOGGED"`, `"UNLOGGED"`, `"COUNTER"` |

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Cassandra批量操作:

    类型:
    1. LOGGED BATCH
    - 保证原子性
    - 性能开销大
    - 同一分区推荐

    2. UNLOGGED BATCH
    - 不保证原子性
    - 性能更好
    - 跨分区推荐

    3. COUNTER BATCH
    - 计数器专用

    示例:
    ```cql
    BEGIN BATCH
    INSERT INTO users (id, name) VALUES (1, 'Alice');
    UPDATE users SET email = 'alice@example.com' WHERE id = 1;
    APPLY BATCH;
    ```

    追踪属性:

    ```go
    span.SetAttributes(
        attribute.String("db.operation", "BATCH"),
        attribute.String("db.cassandra.batch_type", "LOGGED"),
        attribute.Int("db.cassandra.batch_size", 2),
    )
    ```

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

---

## 4. 连接属性

### 4.1 集群属性

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Cassandra集群属性:

    连接配置:
    Contact Points: [node1:9042, node2:9042, node3:9042]
    Local DC: us-east-1
    Load Balancing: DCAwareRoundRobinPolicy

    追踪属性:
    ```go
    span.SetAttributes(
        attribute.String("db.cassandra.cluster.name", "my-cluster"),
        attribute.String("db.cassandra.local_dc", "us-east-1"),
        attribute.StringSlice("db.cassandra.contact_points",
            []string{"node1", "node2", "node3"}),
    )
    ```

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.cassandra.cluster.name` | string | 集群名称 | `"production-cluster"` |
| `db.cassandra.local_dc` | string | 本地数据中心 | `"us-east-1"` |
| `db.cassandra.keyspace` | string | Keyspace | `"myapp"` |
| `db.cassandra.replication_factor` | int | 复制因子 | `3` |

### 4.2 一致性级别

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cassandra一致性级别:

读一致性:
- ONE: 一个副本响应 (最快)
- TWO: 两个副本响应
- THREE: 三个副本响应
- QUORUM: 多数副本响应 (推荐)
- ALL: 所有副本响应 (最慢，最一致)
- LOCAL_QUORUM: 本地DC多数副本
- EACH_QUORUM: 每个DC多数副本

写一致性:
- ONE: 一个副本确认 (最快)
- QUORUM: 多数副本确认 (推荐)
- ALL: 所有副本确认 (最慢)
- LOCAL_QUORUM: 本地DC多数副本

权衡:
- 高一致性 → 低性能
- 低一致性 → 高性能

推荐配置:
- 写: LOCAL_QUORUM
- 读: LOCAL_QUORUM
- 保证: R + W > RF (一致性)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5. Go实现示例

### 5.1 基本CRUD操作

```go
package main

import (
    "context"

    "github.com/gocql/gocql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

type User struct {
    ID    gocql.UUID
    Name  string
    Email string
}

func InsertUserWithTracing(
    ctx context.Context,
    session *gocql.Session,
    user *User,
) error {
    tracer := otel.Tracer("cassandra-client")

    // 创建Span
    ctx, span := tracer.Start(ctx, "cassandra.insert",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemCassandra,
            semconv.DBOperationKey.String("INSERT"),
            semconv.DBNameKey.String("myapp"),
            attribute.String("db.cassandra.table", "users"),
            attribute.String("db.cassandra.consistency_level", "QUORUM"),
        ),
    )
    defer span.End()

    // 执行INSERT
    query := session.Query(
        `INSERT INTO users (id, name, email) VALUES (?, ?, ?)`,
        user.ID, user.Name, user.Email,
    ).WithContext(ctx).Consistency(gocql.Quorum)

    if err := query.Exec(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "insert failed")
        return err
    }

    span.SetStatus(codes.Ok, "inserted")
    return nil
}

func SelectUserWithTracing(
    ctx context.Context,
    session *gocql.Session,
    id gocql.UUID,
) (*User, error) {
    tracer := otel.Tracer("cassandra-client")

    ctx, span := tracer.Start(ctx, "cassandra.select",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemCassandra,
            semconv.DBOperationKey.String("SELECT"),
            semconv.DBNameKey.String("myapp"),
            attribute.String("db.cassandra.table", "users"),
            attribute.String("db.cassandra.consistency_level", "QUORUM"),
        ),
    )
    defer span.End()

    // 执行SELECT
    query := session.Query(
        `SELECT id, name, email FROM users WHERE id = ?`,
        id,
    ).WithContext(ctx).Consistency(gocql.Quorum)

    var user User
    if err := query.Scan(&user.ID, &user.Name, &user.Email); err != nil {
        if err == gocql.ErrNotFound {
            span.SetStatus(codes.Ok, "not found")
            return nil, nil
        }
        span.RecordError(err)
        span.SetStatus(codes.Error, "select failed")
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("db.response.returned_rows", 1),
    )
    span.SetStatus(codes.Ok, "selected")

    return &user, nil
}

func UpdateUserWithTracing(
    ctx context.Context,
    session *gocql.Session,
    id gocql.UUID,
    email string,
) error {
    tracer := otel.Tracer("cassandra-client")

    ctx, span := tracer.Start(ctx, "cassandra.update",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemCassandra,
            semconv.DBOperationKey.String("UPDATE"),
            semconv.DBNameKey.String("myapp"),
            attribute.String("db.cassandra.table", "users"),
        ),
    )
    defer span.End()

    // 执行UPDATE
    query := session.Query(
        `UPDATE users SET email = ? WHERE id = ?`,
        email, id,
    ).WithContext(ctx)

    if err := query.Exec(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "update failed")
        return err
    }

    span.SetStatus(codes.Ok, "updated")
    return nil
}

func DeleteUserWithTracing(
    ctx context.Context,
    session *gocql.Session,
    id gocql.UUID,
) error {
    tracer := otel.Tracer("cassandra-client")

    ctx, span := tracer.Start(ctx, "cassandra.delete",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemCassandra,
            semconv.DBOperationKey.String("DELETE"),
            semconv.DBNameKey.String("myapp"),
            attribute.String("db.cassandra.table", "users"),
        ),
    )
    defer span.End()

    // 执行DELETE
    query := session.Query(
        `DELETE FROM users WHERE id = ?`,
        id,
    ).WithContext(ctx)

    if err := query.Exec(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "delete failed")
        return err
    }

    span.SetStatus(codes.Ok, "deleted")
    return nil
}
```

### 5.2 批量操作

```go
func BatchInsertWithTracing(
    ctx context.Context,
    session *gocql.Session,
    users []*User,
) error {
    tracer := otel.Tracer("cassandra-client")

    ctx, span := tracer.Start(ctx, "cassandra.batch",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemCassandra,
            semconv.DBOperationKey.String("BATCH"),
            semconv.DBNameKey.String("myapp"),
            attribute.String("db.cassandra.batch_type", "LOGGED"),
            attribute.Int("db.cassandra.batch_size", len(users)),
        ),
    )
    defer span.End()

    // 创建批量操作
    batch := session.NewBatch(gocql.LoggedBatch).WithContext(ctx)

    for _, user := range users {
        batch.Query(
            `INSERT INTO users (id, name, email) VALUES (?, ?, ?)`,
            user.ID, user.Name, user.Email,
        )
    }

    // 执行批量操作
    if err := session.ExecuteBatch(batch); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "batch failed")
        return err
    }

    span.SetStatus(codes.Ok, "batch completed")
    return nil
}
```

### 5.3 预处理语句

```go
func PreparedStatementWithTracing(
    ctx context.Context,
    session *gocql.Session,
) error {
    tracer := otel.Tracer("cassandra-client")

    // 准备语句 (只需一次)
    stmt, err := session.Prepare(
        `INSERT INTO users (id, name, email) VALUES (?, ?, ?)`,
    )
    if err != nil {
        return err
    }

    // 使用预处理语句
    for i := 0; i < 100; i++ {
        ctx, span := tracer.Start(ctx, "cassandra.prepared_insert",
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                semconv.DBSystemCassandra,
                semconv.DBOperationKey.String("INSERT"),
                attribute.Bool("db.cassandra.prepared_statement", true),
            ),
        )

        user := &User{
            ID:    gocql.TimeUUID(),
            Name:  fmt.Sprintf("user-%d", i),
            Email: fmt.Sprintf("user%d@example.com", i),
        }

        if err := session.Query(stmt, user.ID, user.Name, user.Email).
            WithContext(ctx).Exec(); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "insert failed")
            span.End()
            return err
        }

        span.SetStatus(codes.Ok, "inserted")
        span.End()
    }

    return nil
}
```

---

## 6. Python实现示例

### 6.1 cassandra-driver

```python
from cassandra.cluster import Cluster
from cassandra.query import SimpleStatement
from opentelemetry import trace
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

def insert_user_with_tracing(session, user_id, name, email):
    """插入用户with tracing"""
    with tracer.start_as_current_span(
        "cassandra.insert",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "cassandra",
            SpanAttributes.DB_OPERATION: "INSERT",
            SpanAttributes.DB_NAME: "myapp",
            "db.cassandra.table": "users",
            "db.cassandra.consistency_level": "QUORUM",
        }
    ) as span:
        try:
            query = SimpleStatement(
                "INSERT INTO users (id, name, email) VALUES (%s, %s, %s)",
                consistency_level=ConsistencyLevel.QUORUM
            )

            session.execute(query, (user_id, name, email))
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def select_user_with_tracing(session, user_id):
    """查询用户with tracing"""
    with tracer.start_as_current_span(
        "cassandra.select",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "cassandra",
            SpanAttributes.DB_OPERATION: "SELECT",
            SpanAttributes.DB_NAME: "myapp",
            "db.cassandra.table": "users",
        }
    ) as span:
        try:
            query = SimpleStatement(
                "SELECT * FROM users WHERE id = %s"
            )

            rows = session.execute(query, (user_id,))
            result = list(rows)

            span.set_attribute("db.response.returned_rows", len(result))
            span.set_status(Status(StatusCode.OK))

            return result

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def batch_insert_with_tracing(session, users):
    """批量插入with tracing"""
    with tracer.start_as_current_span(
        "cassandra.batch",
        kind=SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "cassandra",
            SpanAttributes.DB_OPERATION: "BATCH",
            "db.cassandra.batch_type": "LOGGED",
            "db.cassandra.batch_size": len(users),
        }
    ) as span:
        try:
            batch = BatchStatement()

            for user in users:
                batch.add(
                    SimpleStatement(
                        "INSERT INTO users (id, name, email) VALUES (%s, %s, %s)"
                    ),
                    (user['id'], user['name'], user['email'])
                )

            session.execute(batch)
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

### 6.2 异步操作

```python
from cassandra.cluster import Cluster, ExecutionProfile
from cassandra.policies import DCAwareRoundRobinPolicy

async def async_select_with_tracing(session, user_id):
    """异步查询with tracing"""
    with tracer.start_as_current_span(
        "cassandra.select",
        kind=SpanKind.CLIENT
    ) as span:
        try:
            query = "SELECT * FROM users WHERE id = %s"
            future = session.execute_async(query, (user_id,))

            # 等待结果
            rows = await future.result_async()

            span.set_attribute("db.response.returned_rows", len(rows))
            span.set_status(Status(StatusCode.OK))

            return rows

        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

---

## 7. Java实现示例

### 7.1 DataStax Java Driver

```java
import com.datastax.oss.driver.api.core.CqlSession;
import com.datastax.oss.driver.api.core.cql.*;
import io.opentelemetry.api.trace.*;

public class CassandraTracing {

    private static final Tracer tracer =
        openTelemetry.getTracer("cassandra-client");

    public void insertUserWithTracing(
        CqlSession session,
        UUID id,
        String name,
        String email
    ) {
        Span span = tracer.spanBuilder("cassandra.insert")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("db.system", "cassandra")
            .setAttribute("db.operation", "INSERT")
            .setAttribute("db.name", "myapp")
            .setAttribute("db.cassandra.table", "users")
            .startSpan();

        try (Scope scope = span.makeCurrent()) {
            PreparedStatement prepared = session.prepare(
                "INSERT INTO users (id, name, email) VALUES (?, ?, ?)"
            );

            BoundStatement bound = prepared.bind(id, name, email)
                .setConsistencyLevel(DefaultConsistencyLevel.QUORUM);

            session.execute(bound);
            span.setStatus(StatusCode.OK);

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR);
            throw e;
        } finally {
            span.end();
        }
    }

    public ResultSet selectUserWithTracing(
        CqlSession session,
        UUID id
    ) {
        Span span = tracer.spanBuilder("cassandra.select")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute("db.system", "cassandra")
            .setAttribute("db.operation", "SELECT")
            .setAttribute("db.name", "myapp")
            .setAttribute("db.cassandra.table", "users")
            .startSpan();

        try (Scope scope = span.makeCurrent()) {
            SimpleStatement statement = SimpleStatement.builder(
                "SELECT * FROM users WHERE id = ?"
            )
            .addPositionalValue(id)
            .setConsistencyLevel(DefaultConsistencyLevel.QUORUM)
            .build();

            ResultSet rs = session.execute(statement);

            int rowCount = 0;
            for (Row row : rs) {
                rowCount++;
            }

            span.setAttribute("db.response.returned_rows", rowCount);
            span.setStatus(StatusCode.OK);

            return rs;

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
| `db.cassandra.speculative_executions` | Counter | executions | 推测执行次数 |
| `db.client.errors` | Counter | errors | 错误次数 |

**推荐标签**:

- `db.operation`: 操作类型
- `db.cassandra.consistency_level`: 一致性级别
- `net.peer.name`: 节点地址

### 8.2 服务器Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `db.cassandra.node.status` | Gauge | - | 节点状态 (1=UP, 0=DOWN) |
| `db.cassandra.read.latency` | Histogram | ms | 读延迟 |
| `db.cassandra.write.latency` | Histogram | ms | 写延迟 |
| `db.cassandra.compaction.pending` | Gauge | tasks | 待压缩任务 |
| `db.cassandra.memtable.size` | Gauge | MB | Memtable大小 |

---

## 9. 最佳实践

### 9.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化建议:

1. 分区键设计 ⭐⭐⭐⭐⭐
   - 均匀分布数据
   - 避免热点分区
   - 考虑查询模式

2. 批量操作 ⭐⭐⭐⭐
   - 使用UNLOGGED BATCH (跨分区)
   - 限制批量大小 (<100)
   - 同分区使用LOGGED BATCH

3. 预处理语句 ⭐⭐⭐⭐⭐
   - 减少解析开销
   - 提高性能

4. 异步操作 ⭐⭐⭐⭐
   - 并发执行查询
   - 提高吞吐量

5. 一致性级别 ⭐⭐⭐⭐⭐
   - 读写权衡 (R + W > RF)
   - LOCAL_QUORUM (跨DC)

6. 连接池 ⭐⭐⭐⭐
   - 配置合理池大小
   - 复用连接

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 数据建模

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Cassandra数据建模原则:

    1. 查询驱动设计 ⭐⭐⭐⭐⭐
    - 先设计查询
    - 再设计表结构

    2. 去规范化 ⭐⭐⭐⭐
    - 数据冗余 OK
    - 一个查询一个表

    3. 分区键选择 ⭐⭐⭐⭐⭐
    - 均匀分布
    - 避免大分区 (>100MB)

    4. 聚类键排序 ⭐⭐⭐⭐
    - 定义排序规则
    - 范围查询优化

    5. 避免扫描 ⭐⭐⭐⭐⭐
    - 使用分区键查询
    - 避免ALLOW FILTERING

    示例表结构:
    ```cql
    CREATE TABLE user_events (
        user_id UUID,
        event_time timestamp,
        event_type text,
        data text,
        PRIMARY KEY (user_id, event_time)
    ) WITH CLUSTERING ORDER BY (event_time DESC);
    ```

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 9.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. 性能指标
   - 读/写延迟 (p50, p99)
   - TPS
   - 超时次数

2. 节点状态
   - UP/DOWN状态
   - 连接数
   - CPU/内存使用

3. 压缩指标
   - 待压缩任务数
   - SSTable数量
   - Memtable大小

4. 一致性
   - Hints数量 (延迟写入)
   - Repair状态

告警规则:
- 读/写延迟 > 50ms (p99)
- 节点DOWN > 5分钟
- 待压缩任务 > 100
- Hints积压 > 1000

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成
**Cassandra版本**: 3.11+
**适用场景**: 时序数据、高写入负载、多数据中心、大规模存储

**关键特性**:

- ✅ 完整CQL操作追踪
- ✅ 批量操作支持
- ✅ 一致性级别追踪
- ✅ 预处理语句优化
- ✅ Go/Python/Java完整示例
- ✅ 性能优化建议
- ✅ 数据建模最佳实践
