---
title: Exemplars详解 - 连接Metrics和Traces的桥梁
description: OTLP Exemplars机制的完整规范、实现与应用指南，实现Metric到Trace的精确关联
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 数据模型
tags:
  - exemplars
  - metrics
  - traces
  - correlation
  - observability
status: published
---

# Exemplars详解 - 连接Metrics和Traces的桥梁

> **版本**: OTLP v1.10.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约30分钟

---

## 1. Exemplars概述

### 1.1 什么是Exemplars

**Exemplars** (样本/范例) 是在Histogram或Counter等聚合指标中保留的**原始Trace信息**，用于实现从聚合指标到具体Trace的精确跳转：

```
┌─────────────────────────────────────────────────────────────────┐
│                    Exemplars概念图解                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  问题: 聚合指标丢失了个案信息                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                                                         │   │
│  │  指标: P99延迟 = 500ms                                  │   │
│  │                                                         │   │
│  │  问题: 哪些具体的请求导致了这个延迟?                     │   │
│  │        无法从聚合指标得知                                │   │
│  │                                                         │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  解决方案: Exemplars                                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                                                         │   │
│  │  指标: P99延迟 = 500ms                                  │   │
│  │         ↓                                               │   │
│  │  Exemplar: TraceID=abc123, SpanID=def456, Value=498ms  │   │
│  │         ↓                                               │   │
│  │  [点击查看完整Trace]                                     │   │
│  │                                                         │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  价值: 从"大概知道有问题"到"精确定位问题Trace"                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Exemplars的核心价值

| 价值 | 说明 | 示例 |
|------|------|------|
| **精确关联** | 从聚合指标跳转到具体Trace | P99延迟高 → 查看对应Trace |
| **根因定位** | 快速定位异常值的原因 | 慢请求的具体调用链 |
| **采样补充** | 在低采样率下保留关键样本 | 只采样1%但保留所有慢请求 |
| **长尾分析** | 分析尾部延迟的具体情况 | P99.9延迟的详细分析 |

---

## 2. Exemplars数据结构

### 2.1 Proto定义

```protobuf
// opentelemetry/proto/metrics/v1/metrics.proto

// Exemplar是聚合测量中的代表性数据点
message Exemplar {
  // 一组筛选后的属性，减少数据量
  // 通常包含trace_id, span_id等关键信息
  repeated opentelemetry.proto.common.v1.KeyValue filtered_attributes = 1;

  // 测量时间戳
  fixed64 time_unix_nano = 2;

  // 测量值
  oneof value {
    double as_double = 3;
    sfixed64 as_int = 6;
  }

  // Trace ID (16字节)
  bytes trace_id = 4;

  // Span ID (8字节)
  bytes span_id = 5;
}
```

### 2.2 字段详解

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| **filtered_attributes** | KeyValue[] | 附加属性 | `{"user.type": "premium"}` |
| **time_unix_nano** | int64 | 时间戳 | `1640995200000000000` |
| **value** | double/int | 测量值 | `498.5` (延迟，毫秒) |
| **trace_id** | bytes | Trace ID | `0af7651916cd43dd8448eb211c80319c` |
| **span_id** | bytes | Span ID | `b7ad6b7169203331` |

---

## 3. Exemplars在指标类型中的应用

### 3.1 Histogram中的Exemplars

```
┌─────────────────────────────────────────────────────────────────┐
│                Histogram + Exemplars结构                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Histogram: http_request_duration_seconds                        │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │ Buckets (桶边界)                                           │ │
│  │                                                            │ │
│  │  le=0.005  │ count: 100 │ exemplars: [e1, e2, ...]      │ │
│  │  le=0.01   │ count: 250 │ exemplars: [e3, e4, ...]      │ │
│  │  le=0.025  │ count: 500 │ exemplars: [e5, e6, ...]      │ │
│  │  ...       │ ...        │ ...                            │ │
│  │  le=1.0    │ count: 950 │ exemplars: [e20, e21, ...]    │ │
│  │  le=+Inf   │ count: 1000│ exemplars: [e25, e26, ...]    │ │
│  │                                                            │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
│  每个桶保留最近的N个Exemplar (通常N=1-5)                         │
│                                                                 │
│  Exemplar e25 (落在le=1.0桶中):                                 │
│  {
│    "trace_id": "abc123...",
│    "span_id": "def456...",
│    "value": 0.85,              // 850ms
│    "time_unix_nano": 1640995200000000000,
│    "filtered_attributes": {
│      "http.method": "POST",
│      "http.route": "/api/orders"
│    }
│  }
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 Counter中的Exemplars

```
┌─────────────────────────────────────────────────────────────────┐
│                  Counter + Exemplars结构                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Counter: errors_total                                           │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │  value: 150                                                │ │
│  │                                                            │ │
│  │  exemplars: [                                              │ │
│  │    {                                                       │ │
│  │      trace_id: "err001...",                                │ │
│  │      span_id: "s001...",                                   │ │
│  │      value: 1,                                             │ │
│  │      filtered_attributes: {                                │ │
│  │        "error.type": "ConnectionTimeout",                  │ │
│  │        "error.message": "connection refused"               │ │
│  │      }                                                     │ │
│  │    },                                                      │ │
│  │    {                                                       │ │
│  │      trace_id: "err002...",                                │ │
│  │      span_id: "s002...",                                   │ │
│  │      value: 1,                                             │ │
│  │      filtered_attributes: {                                │ │
│  │        "error.type": "DatabaseError",                      │ │
│  │        "error.message": "lock timeout"                     │ │
│  │      }                                                     │ │
│  │    },                                                      │ │
│  │    // ... 最多保留N个最近的Exemplar                        │ │
│  │  ]                                                         │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 4. 实现指南

### 4.1 SDK配置

```go
// Go SDK配置Exemplars

import (
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/metric/view"
)

func configureExemplars() metric.View {
    // 创建自定义View启用Exemplars
    customView, _ := view.New(
        view.MatchInstrumentName("http_request_duration_*"),
        view.WithSetAggregation(aggregation.ExplicitBucketHistogram{
            Boundaries: []float64{0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10},
        }),
        // 启用Exemplars
        view.WithExemplarReservoirFactory(
            exemplar.HistogramReservoirFactory,
        ),
    )

    return customView
}

// 配置MeterProvider
mp := metric.NewMeterProvider(
    metric.WithView(configureExemplars()),
)
```

### 4.2 采样策略

```go
// 基于Trace的Exemplar采样

type TraceBasedExemplarFilter struct {
    // 只保留采样Trace的Exemplar
}

func (f *TraceBasedExemplarFilter) ShouldSample(
    ctx context.Context,
    value float64,
) bool {
    span := trace.SpanFromContext(ctx)
    if !span.IsRecording() {
        return false
    }

    spanContext := span.SpanContext()
    return spanContext.IsSampled()
}

// 基于值的Exemplar采样 (保留异常值)
type ValueBasedExemplarFilter struct {
    threshold float64
}

func (f *ValueBasedExemplarFilter) ShouldSample(
    ctx context.Context,
    value float64,
) bool {
    // 只保留超过阈值的值
    return value > f.threshold
}
```

### 4.3 完整的Exemplar收集示例

```go
package exemplar

import (
    "context"
    "time"

    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/metric/metricdata"
    "go.opentelemetry.io/otel/trace"
)

// ExemplarCollector Exemplar收集器
type ExemplarCollector struct {
    maxSize int
    reservoir []Exemplar
}

// Exemplar Exemplar数据结构
type Exemplar struct {
    TraceID    string
    SpanID     string
    Value      float64
    Timestamp  time.Time
    Attributes map[string]interface{}
}

// NewExemplarCollector 创建收集器
func NewExemplarCollector(maxSize int) *ExemplarCollector {
    return &ExemplarCollector{
        maxSize:   maxSize,
        reservoir: make([]Exemplar, 0, maxSize),
    }
}

// Collect 收集Exemplar
func (c *ExemplarCollector) Collect(
    ctx context.Context,
    value float64,
    attributes ...attribute.KeyValue,
) {
    span := trace.SpanFromContext(ctx)
    if !span.IsRecording() {
        return
    }

    spanContext := span.SpanContext()

    exemplar := Exemplar{
        TraceID:   spanContext.TraceID().String(),
        SpanID:    spanContext.SpanID().String(),
        Value:     value,
        Timestamp: time.Now(),
        Attributes: make(map[string]interface{}),
    }

    // 添加过滤后的属性
    for _, attr := range attributes {
        // 只保留关键属性，减少数据量
        if isImportantAttribute(attr.Key) {
            exemplar.Attributes[string(attr.Key)] = attr.Value
        }
    }

    c.addToReservoir(exemplar)
}

// addToReservoir 添加到蓄水池
func (c *ExemplarCollector) addToReservoir(e Exemplar) {
    if len(c.reservoir) < c.maxSize {
        c.reservoir = append(c.reservoir, e)
    } else {
        // 简单的轮转替换策略
        // 实际实现可能使用更复杂的算法
        idx := time.Now().UnixNano() % int64(c.maxSize)
        c.reservoir[idx] = e
    }
}

// GetExemplars 获取所有Exemplars
func (c *ExemplarCollector) GetExemplars() []Exemplar {
    result := make([]Exemplar, len(c.reservoir))
    copy(result, c.reservoir)
    return result
}

// isImportantAttribute 判断属性是否重要
func isImportantAttribute(key attribute.Key) bool {
    importantKeys := map[string]bool{
        "http.method":     true,
        "http.route":      true,
        "http.status_code": true,
        "db.system":       true,
        "db.operation":    true,
        "error.type":      true,
    }
    return importantKeys[string(key)]
}

// 使用示例
func recordWithExemplar(ctx context.Context, duration float64) {
    collector := NewExemplarCollector(5) // 最多保留5个Exemplar

    collector.Collect(
        ctx,
        duration,
        attribute.String("http.method", "POST"),
        attribute.String("http.route", "/api/orders"),
        attribute.Int("http.status_code", 200),
    )

    // 获取Exemplars用于上报
    exemplars := collector.GetExemplars()
    for _, e := range exemplars {
        fmt.Printf("Exemplar: TraceID=%s, Value=%.2f\n", e.TraceID, e.Value)
    }
}
```

---

## 5. 应用实践

### 5.1 Grafana Tempo集成

```yaml
# Grafana配置启用Exemplars

datasources:
  - name: Prometheus
    type: prometheus
    url: http://prometheus:9090
    jsonData:
      # 启用Exemplars
      exemplarTraceIdDestinations:
        - name: trace_id
          url: 'http://localhost:3000/explore?orgId=1&left=%5B%22now-1h%22,%22now%22,%22Tempo%22,%7B%22query%22:%22${__value.raw}%22%7D%5D'
```

### 5.2 Prometheus配置

```yaml
# prometheus.yml

# 启用Exemplars存储
storage:
  tsdb:
    exemplars:
      max_size: 10000000  # 10MB
```

### 5.3 查询示例

```promql
# 查询Histogram及其Exemplars
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# 在Grafana中点击Histogram点查看关联的Trace
```

---

## 6. 最佳实践

### 6.1 何时使用Exemplars

```markdown
## 推荐使用场景:

✅ 长尾延迟分析
   - 保留P99+延迟的具体Trace
   - 分析为什么某些请求特别慢

✅ 错误追踪
   - 保留导致错误的具体Trace
   - 快速定位错误根因

✅ 采样补充
   - 在Head-based采样中保留关键样本
   - 确保重要事件被记录

✅ 调试高基数维度
   - 当无法按所有维度分组时
   - 通过Exemplar查看原始数据

## 不推荐使用场景:

❌ 高频指标
   - 每秒数万次的指标
   - Exemplar收集会成为瓶颈

❌ 不需要关联Trace的场景
   - 基础设施指标 (CPU/内存)
   - 与业务请求无关的指标
```

### 6.2 配置建议

```yaml
# Exemplars配置建议

收集策略:
  max_exemplars_per_bucket: 1-5
    # 每个桶保留的Exemplar数量
    # 过多会增加数据量

  filter_attributes:
    # 只保留重要属性
    include:
      - trace_id
      - span_id
      - http.method
      - http.route
      - error.type
    exclude:
      - user_id  # 高基数
      - request_id  # 高基数

  value_thresholds:
    # 基于值的采样阈值
    latency:
      min: 100ms  # 只保留>100ms的请求
    errors:
      include_all: true  # 保留所有错误
```

---

**参考资源**:

- [OpenTelemetry Exemplars](https://opentelemetry.io/docs/specs/otel/metrics/data-model/#exemplars)
- [Prometheus Exemplars](https://prometheus.io/docs/prometheus/latest/feature_flags/#exemplar-storage)
- [Grafana Tempo Exemplars](https://grafana.com/docs/tempo/latest/metrics-generator/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
