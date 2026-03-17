---
title: OTLP指标体系设计方法论
description: 基于OTLP数据的指标体系设计方法论，包含USE方法、RED方法、四个黄金信号等经典方法论的系统化实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 数据分析与洞察
tags:
  - metrics
  - indicator-system
  - USE-method
  - RED-method
  - golden-signals
status: published
---

# OTLP指标体系设计方法论

> **版本**: OTLP v1.10.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约40分钟

---

## 1. 指标体系概述

### 1.1 为什么需要指标体系

```
┌─────────────────────────────────────────────────────────────────┐
│                    指标体系的价值                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  没有指标体系                    有指标体系                      │
│  ┌──────────────────┐           ┌──────────────────┐           │
│  │ "系统好像有问题" │           │ "P99延迟从50ms   │           │
│  │ "服务不太稳定"   │    →      │ 上升到200ms，    │           │
│  │ "用户体验不好"   │           │ 错误率从0.1%     │           │
│  │                  │           │ 上升到2%"        │           │
│  └──────────────────┘           └──────────────────┘           │
│                                                                 │
│  问题:                            优势:                          │
│  • 主观感受                        • 客观量化                    │
│  • 无法比较                        • 可度量可比较                │
│  • 难以定位                        • 可追溯可定位                │
│  • 无法预测                        • 可预警可预测                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 指标类型分类

OTLP提供了丰富的指标类型，支持不同的分析场景：

```yaml
# OTLP指标类型与使用场景

Counter (计数器):
  特点: 单调递增，只能增加或重置为零
  适用场景:
    - 请求总数
    - 错误总数
    - 完成的任务数
  示例: http_requests_total, errors_total

Gauge (仪表盘):
  特点: 可增可减，表示瞬时值
  适用场景:
    - 当前温度/内存使用量
    - 队列长度
    - 并发连接数
  示例: memory_usage_bytes, queue_size

Histogram (直方图):
  特点: 采样分布，包含桶计数和总和
  适用场景:
    - 请求延迟分布
    - 响应大小分布
    - 任意需要分位数的场景
  示例: http_request_duration_seconds

Summary (摘要):
  特点: 客户端计算的滑动窗口分位数
  适用场景:
    - 需要客户端计算分位数
    - 服务端无法计算Histogram的场景
  注意: 尽量避免使用，推荐Histogram

ExponentialHistogram (指数直方图):
  特点: 使用指数桶边界，适合大范围数值
  适用场景:
    - 延迟指标 (纳秒到秒的范围)
    - 需要高效存储和传输
  OTLP v0.11+ 新增
```

---

## 2. 经典方法论

### 2.1 四个黄金信号 (Four Golden Signals)

Google SRE提出的经典监控指标：

```
┌─────────────────────────────────────────────────────────────────┐
│                    四个黄金信号                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 延迟 (Latency)                                              │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 定义: 服务处理请求所需的时间                          │    │
│     │                                                      │    │
│     │ 关键指标:                                            │    │
│     │ • http_request_duration_seconds (直方图)             │    │
│     │   - 分位数: P50, P95, P99                           │    │
│     │   - 区分成功/失败请求的延迟                          │    │
│     │                                                      │    │
│     │ 注意事项:                                            │    │
│     │ • 失败的请求可能延迟很低 (快速失败)                  │    │
│     │ • 必须区分成功和失败的延迟                           │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  2. 流量 (Traffic)                                              │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 定义: 系统的需求量，衡量繁忙程度                      │    │
│     │                                                      │    │
│     │ 关键指标:                                            │    │
│     │ • http_requests_total (计数器)                       │    │
│     │   - 按方法/端点/状态码分组                           │    │
│     │ • rpc_requests_total                                 │    │
│     │ • message_queue_messages_published                  │    │
│     │                                                      │    │
│     │ 注意事项:                                            │    │
│     │ • 区分读取和写入流量                                 │    │
│     │ • 考虑业务层面的流量指标                             │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  3. 错误 (Errors)                                               │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 定义: 请求失败率                                      │    │
│     │                                                      │    │
│     │ 关键指标:                                            │    │
│     │ • http_requests_total{status=~"5.."}                │    │
│     │ • errors_total                                       │    │
│     │ • error_rate = errors / total_requests              │    │
│     │                                                      │    │
│     │ 注意事项:                                            │    │
│     │ • 显式失败 + 隐式失败 (如HTTP 200但内容错误)        │    │
│     │ • 按错误类型分类                                     │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  4. 饱和度 (Saturation)                                         │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 定义: 服务容量有多"满"                               │    │
│     │                                                      │    │
│     │ 关键指标:                                            │    │
│     │ • CPU使用率                                          │    │
│     │ • 内存使用率                                         │    │
│     │ • 磁盘I/O利用率                                      │    │
│     │ • 连接池使用率                                       │    │
│     │ • 线程池队列长度                                     │    │
│     │                                                      │    │
│     │ 注意事项:                                            │    │
│     │ • 通常 hardest to interpret                          │    │
│     │ • 需要设定阈值                                       │    │
│     │ • 考虑软限制和硬限制                                 │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 USE方法

Brendan Gregg提出的资源利用率方法论：

```
USE方法: 针对资源（如CPU、内存、磁盘）的三步法

┌─────────────────────────────────────────────────────────────────┐
│  U - Utilization (利用率)                                       │
│     定义: 资源有多忙，以百分比表示                               │
│                                                                      │
│     指标示例:                                                    │
│     • cpu.utilization_percent                                    │
│     • memory.utilization_percent                                 │
│     • disk.utilization_percent                                   │
│     • network.bandwidth.utilization                              │
│                                                                      │
│     正常范围: 0-100%                                             │
│     告警阈值: > 80% (警告), > 90% (严重)                         │
│                                                                      │
├─────────────────────────────────────────────────────────────────┤
│  S - Saturation (饱和度)                                        │
│     定义: 有多少工作在等待资源，衡量排队                          │
│                                                                      │
│     指标示例:                                                    │
│     • cpu.run_queue_length                                       │
│     • disk.io_queue_depth                                        │
│     • network.backlog                                            │
│     • thread_pool.queue_size                                     │
│                                                                      │
│     正常范围: 接近0                                              │
│     告警阈值: > 0 (表示有排队)                                   │
│                                                                      │
├─────────────────────────────────────────────────────────────────┤
│  E - Errors (错误)                                              │
│     定义: 资源相关的错误事件                                      │
│                                                                      │
│     指标示例:                                                    │
│     • disk.io_errors                                             │
│     • network.errors                                             │
│     • memory.allocation_failures                                 │
│                                                                      │
│     正常范围: 0                                                  │
│     告警阈值: > 0                                                │
│                                                                      │
└─────────────────────────────────────────────────────────────────┘

USE方法应用示例 - CPU监控:
┌─────────────────┬────────────────────┬──────────────┐
│ 指标            │ 名称               │ 正常范围     │
├─────────────────┼────────────────────┼──────────────┤
│ Utilization     │ cpu.usage_percent  │ < 80%        │
│ Saturation      │ cpu.load_average   │ < CPU核心数  │
│ Errors          │ cpu.throttling_count│ 0            │
└─────────────────┴────────────────────┴──────────────┘

USE方法应用示例 - 内存监控:
┌─────────────────┬────────────────────┬──────────────┐
│ 指标            │ 名称               │ 正常范围     │
├─────────────────┼────────────────────┼──────────────┤
│ Utilization     │ memory.usage_percent│ < 80%       │
│ Saturation      │ memory.swap_usage  │ 0            │
│ Errors          │ memory.oom_events  │ 0            │
└─────────────────┴────────────────────┴──────────────┘
```

### 2.3 RED方法

Tom Wilkie提出的面向服务的监控方法：

```
RED方法: 针对微服务/HTTP API的请求驱动指标

┌─────────────────────────────────────────────────────────────────┐
│  R - Rate (请求率)                                              │
│     定义: 每秒请求数 (Requests per Second)                       │
│                                                                      │
│     指标示例:                                                    │
│     • http_requests_per_second                                   │
│     • rpc_requests_per_second                                    │
│                                                                      │
│     计算公式:                                                    │
│     rate(http_requests_total[5m])                                │
│                                                                      │
│     用途:                                                        │
│     • 容量规划                                                  │
│     • 流量趋势分析                                              │
│     • 异常流量检测                                              │
│                                                                      │
├─────────────────────────────────────────────────────────────────┤
│  E - Errors (错误率)                                            │
│     定义: 每秒错误请求数                                         │
│                                                                      │
│     指标示例:                                                    │
│     • http_errors_per_second                                     │
│     • error_rate_percent                                         │
│                                                                      │
│     计算公式:                                                    │
│     rate(http_requests_total{status=~"5.."}[5m])                │
│     /                                                            │
│     rate(http_requests_total[5m])                                │
│                                                                      │
│     用途:                                                        │
│     • 服务质量监控                                              │
│     • 故障检测                                                  │
│     • SLA监控                                                   │
│                                                                      │
├─────────────────────────────────────────────────────────────────┤
│  D - Duration (持续时间)                                        │
│     定义: 请求处理时间的分布                                     │
│                                                                      │
│     指标示例:                                                    │
│     • http_request_duration_seconds                              │
│     • rpc_request_duration_seconds                               │
│                                                                      │
│     关键分位数:                                                  │
│     • P50 (中位数) - 典型用户体验                               │
│     • P95 - 大多数用户体验                                       │
│     • P99 - 最差用户体验                                         │
│                                                                      │
│     计算公式 (PromQL):                                           │
│     histogram_quantile(0.95,                                     │
│       rate(http_request_duration_bucket[5m]))                   │
│                                                                      │
│     用途:                                                        │
│     • 性能监控                                                  │
│     • 容量规划                                                  │
│     • SLO监控                                                   │
│                                                                      │
└─────────────────────────────────────────────────────────────────┘

RED方法 vs 四个黄金信号:
┌──────────────────┬─────────────────┬─────────────────┐
│ 维度             │ RED方法         │ 四个黄金信号    │
├──────────────────┼─────────────────┼─────────────────┤
│ 面向对象         │ 服务/API        │ 系统整体        │
│ Rate             │ ✅              │ ✅ (Traffic)    │
│ Errors           │ ✅              │ ✅              │
│ Duration         │ ✅              │ ✅ (Latency)    │
│ Saturation       │ ❌              │ ✅              │
│ 适用场景         │ 微服务          │ 基础设施        │
└──────────────────┴─────────────────┴─────────────────┘

最佳实践: 将RED用于服务层，四个黄金信号用于基础设施层
```

---

## 3. 指标体系设计实践

### 3.1 分层指标体系

```
┌─────────────────────────────────────────────────────────────────┐
│                    分层指标体系架构                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Layer 4: 业务层指标 (Business KPIs)                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • 订单转化率                    • 用户留存率             │   │
│  │ • 平均订单价值                  • 用户活跃度             │   │
│  │ • 支付成功率                    • 业务错误率             │   │
│  │                                                          │   │
│  │ 特点: 直接关联业务目标，非技术人员理解                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Layer 3: 应用层指标 (Application Metrics)                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • 请求延迟 (P50/P95/P99)        • 吞吐量 (RPS)          │   │
│  │ • 错误率                        • 并发连接数            │   │
│  │ • 缓存命中率                    • 队列深度              │   │
│  │                                                          │   │
│  │ 特点: RED方法应用，开发团队关注                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Layer 2: 系统层指标 (System Metrics)                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • CPU利用率                     • 内存使用率            │   │
│  │ • 磁盘I/O                       • 网络吞吐量            │   │
│  │ • 文件描述符使用                • 进程/线程数           │   │
│  │                                                          │   │
│  │ 特点: USE方法应用，运维团队关注                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Layer 1: 基础设施层指标 (Infrastructure Metrics)               │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • 实例健康状态                  • 网络延迟              │   │
│  │ • 负载均衡器指标                • 存储容量              │   │
│  │ • 容器资源使用                  • 调度延迟              │   │
│  │                                                          │   │
│  │ 特点: 四个黄金信号，平台团队关注                         │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

分层指标关联示例:
业务层: 订单转化率下降
    ↓
应用层: 支付API错误率上升 → 延迟P99增加
    ↓
系统层: 数据库连接池饱和 → CPU利用率升高
    ↓
基础设施层: 数据库实例CPU达到100%

结论: 需要扩容数据库实例或优化慢查询
```

### 3.2 指标命名规范

```yaml
# Prometheus/OpenMetrics 最佳实践命名规范

通用格式:
  <namespace>_<subsystem>_<metric_name>_<unit>_<suffix>

命名原则:
  1. 使用蛇形命名法 (snake_case)
  2. 单位作为后缀 (_seconds, _bytes, _total)
  3. 使用基本单位 (seconds, not milliseconds)
  4. 计数器以 _total 结尾
  5. 布尔值使用 _enabled/_disabled

命名示例:
  # 好的命名
  http_requests_total                    # 总请求数
  http_request_duration_seconds          # 请求持续时间
  http_request_duration_seconds_bucket   # 直方图桶
  http_request_duration_seconds_sum      # 持续时间总和
  http_request_duration_seconds_count    # 请求计数
  system_memory_usage_bytes              # 内存使用字节
  queue_messages_pending                 # 队列等待消息数

  # 不好的命名
  httpRequests                           # 驼峰命名
  req_latency                            # 不清晰
  request_time_ms                        # 使用毫秒而非秒
  errors                                 # 缺少上下文

标签命名规范:
  # 好的标签
  http_method: "GET"
  http_status_code: "200"
  service_name: "order-service"
  environment: "production"

  # 不好的标签
  method: "GET"              # 太通用
  code: "200"                # 不清晰
  service: "order-service"   # 建议使用service_name
  env: "prod"                # 不清晰

高基数标签警告:
  避免使用高基数标签，如:
  ❌ user_id (每个用户都不同)
  ❌ request_id (每个请求都不同)
  ❌ session_id (每个会话都不同)

  应该使用:
  ✅ user_tier (free/premium/enterprise)
  ✅ request_type (read/write)
  ✅ session_country (US/CN/DE)
```

### 3.3 指标采集策略

```go
// Go SDK指标采集示例

package metrics

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// RED指标采集器
type REDMetrics struct {
    // Rate
    requestCounter metric.Int64Counter

    // Errors
    errorCounter metric.Int64Counter

    // Duration
    durationHistogram metric.Float64Histogram
}

func NewREDMetrics(meter metric.Meter) (*REDMetrics, error) {
    requestCounter, err := meter.Int64Counter(
        "http_requests_total",
        metric.WithDescription("Total HTTP requests"),
    )
    if err != nil {
        return nil, err
    }

    errorCounter, err := meter.Int64Counter(
        "http_errors_total",
        metric.WithDescription("Total HTTP errors"),
    )
    if err != nil {
        return nil, err
    }

    durationHistogram, err := meter.Float64Histogram(
        "http_request_duration_seconds",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
    )
    if err != nil {
        return nil, err
    }

    return &REDMetrics{
        requestCounter:    requestCounter,
        errorCounter:      errorCounter,
        durationHistogram: durationHistogram,
    }, nil
}

// RecordRequest 记录请求指标
func (m *REDMetrics) RecordRequest(
    ctx context.Context,
    method string,
    path string,
    statusCode int,
    duration time.Duration,
) {
    attrs := []attribute.KeyValue{
        attribute.String("http.method", method),
        attribute.String("http.route", path),
        attribute.Int("http.status_code", statusCode),
    }

    // Rate: 记录总请求
    m.requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))

    // Errors: 记录错误
    if statusCode >= 400 {
        m.errorCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
    }

    // Duration: 记录延迟
    m.durationHistogram.Record(ctx, duration.Seconds(), metric.WithAttributes(attrs...))
}

// USE指标采集器
type USEMetrics struct {
    cpuUtilization    metric.Float64ObservableGauge
    memoryUtilization metric.Float64ObservableGauge
    diskQueueLength   metric.Float64ObservableGauge
}

func NewUSEMetrics(meter metric.Meter) (*USEMetrics, error) {
    cpuUtilization, err := meter.Float64ObservableGauge(
        "system_cpu_utilization_percent",
        metric.WithDescription("CPU utilization percentage"),
    )
    if err != nil {
        return nil, err
    }

    memoryUtilization, err := meter.Float64ObservableGauge(
        "system_memory_utilization_percent",
        metric.WithDescription("Memory utilization percentage"),
    )
    if err != nil {
        return nil, err
    }

    diskQueueLength, err := meter.Float64ObservableGauge(
        "system_disk_queue_length",
        metric.WithDescription("Disk queue length"),
    )
    if err != nil {
        return nil, err
    }

    // 注册回调函数
    _, err = meter.RegisterCallback(
        func(ctx context.Context, obs metric.Observer) error {
            // Utilization: CPU使用率
            cpuPercent := getCPUUtilization()
            obs.ObserveFloat64(cpuUtilization, cpuPercent)

            // Utilization: 内存使用率
            memPercent := getMemoryUtilization()
            obs.ObserveFloat64(memoryUtilization, memPercent)

            // Saturation: 磁盘队列长度
            diskQueue := getDiskQueueLength()
            obs.ObserveFloat64(diskQueueLength, diskQueue)

            return nil
        },
        cpuUtilization, memoryUtilization, diskQueueLength,
    )
    if err != nil {
        return nil, err
    }

    return &USEMetrics{
        cpuUtilization:    cpuUtilization,
        memoryUtilization: memoryUtilization,
        diskQueueLength:   diskQueueLength,
    }, nil
}

// 辅助函数 (需要根据实际平台实现)
func getCPUUtilization() float64 {
    // 实现CPU使用率采集
    return 0.0
}

func getMemoryUtilization() float64 {
    // 实现内存使用率采集
    return 0.0
}

func getDiskQueueLength() float64 {
    // 实现磁盘队列长度采集
    return 0.0
}
```

---

## 4. 常用指标计算公式

### 4.1 PromQL查询示例

```promql
# ===== RED指标查询 =====

# 1. Rate (每秒请求数)
rate(http_requests_total[5m])

# 按服务和方法分组
sum by (service, method) (rate(http_requests_total[5m]))

# 2. Errors (错误率)
# HTTP 5xx错误率
sum(rate(http_requests_total{status=~"5.."}[5m]))
/ sum(rate(http_requests_total[5m]))

# 按服务分组的错误率
sum by (service) (rate(http_requests_total{status=~"5.."}[5m]))
/ sum by (service) (rate(http_requests_total[5m]))

# 3. Duration (延迟分位数)
# P99延迟
histogram_quantile(0.99,
  sum by (le) (rate(http_request_duration_seconds_bucket[5m]))
)

# 按服务分组的P95延迟
histogram_quantile(0.95,
  sum by (service, le) (rate(http_request_duration_seconds_bucket[5m]))
)

# ===== USE指标查询 =====

# Utilization (CPU使用率)
system_cpu_utilization_percent

# 集群平均CPU使用率
avg(system_cpu_utilization_percent)

# Saturation (负载)
# 运行队列长度 / CPU核心数
node_load1 / count without(cpu, mode) (node_cpu_seconds_total{mode="idle"})

# ===== 复合指标 =====

# 可用性 (成功请求比例)
1 - (
  sum(rate(http_requests_total{status=~"5.."}[5m]))
  / sum(rate(http_requests_total[5m]))
)

# 吞吐量 (每分钟请求数)
sum(rate(http_requests_total[1m])) * 60

# 平均响应时间 (总时间 / 总请求数)
sum(rate(http_request_duration_seconds_sum[5m]))
/ sum(rate(http_request_duration_seconds_count[5m]))

# 错误预算消耗率 (相对于SLO)
(
  sum(rate(http_requests_total{status=~"5.."}[1h]))
  / sum(rate(http_requests_total[1h]))
) / (1 - 0.999)  # 假设SLO是99.9%
```

### 4.2 TraceQL查询示例 (Grafana Tempo)

```traceql
# ===== 基础查询 =====

# 按服务名查询
{service.name="order-service"}

# 按Span名查询
{name="HTTP GET /api/orders"}

# 组合条件
{service.name="order-service" && name="HTTP GET"}

# ===== 属性过滤 =====

# 按状态过滤
{status=error}

# 按持续时间过滤 (超过1秒的Span)
{duration > 1s}

# 按自定义属性过滤
{http.status_code=500}
{user.id="12345"}
{db.system="mysql"}

# ===== 聚合查询 =====

# 计算平均持续时间
avg({service.name="order-service"} | select(duration))

# 按服务分组统计Span数
{status=error} | count() by (service.name)

# ===== 链路分析 =====

# 查找包含特定Span的完整Trace
{span.http.url="/api/orders"} >> {status=error}

# 查找特定服务的上下游调用
{service.name="gateway"} > {service.name="order-service"}

# 查找慢调用链
{duration > 2s} | select(duration, service.name, name)
```

---

## 5. 指标告警规则

### 5.1 告警规则模板

```yaml
# Prometheus告警规则示例
groups:
  - name: red_method_alerts
    interval: 30s
    rules:
      # 高错误率告警
      - alert: HighErrorRate
        expr: |
          (
            sum(rate(http_requests_total{status=~"5.."}[5m]))
            / sum(rate(http_requests_total[5m]))
          ) > 0.01
        for: 2m
        labels:
          severity: warning
          method: red
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }}"

      # 高延迟告警 (P99 > 1s)
      - alert: HighLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
          ) > 1
        for: 5m
        labels:
          severity: warning
          method: red
        annotations:
          summary: "High latency detected"
          description: "P99 latency is {{ $value }}s"

      # 流量突增告警 (比过去1小时平均高3倍)
      - alert: TrafficSpike
        expr: |
          sum(rate(http_requests_total[5m]))
          > 3 * avg_over_time(sum(rate(http_requests_total[5m]))[1h:5m])
        for: 2m
        labels:
          severity: info
          method: red
        annotations:
          summary: "Traffic spike detected"

  - name: use_method_alerts
    interval: 30s
    rules:
      # CPU使用率高
      - alert: HighCPUUsage
        expr: system_cpu_utilization_percent > 80
        for: 5m
        labels:
          severity: warning
          method: use
        annotations:
          summary: "High CPU usage"
          description: "CPU usage is {{ $value }}%"

      # 内存饱和 (开始使用swap)
      - alert: MemorySaturation
        expr: |
          node_memory_SwapTotal_bytes - node_memory_SwapFree_bytes > 0
        for: 1m
        labels:
          severity: critical
          method: use
        annotations:
          summary: "Memory saturation detected"
          description: "System is using swap"

      # 磁盘饱和 (队列长度>10)
      - alert: DiskSaturation
        expr: rate(node_disk_io_time_seconds_total[5m]) > 0.8
        for: 5m
        labels:
          severity: warning
          method: use
        annotations:
          summary: "Disk saturation"
          description: "Disk I/O utilization is high"
```

---

## 6. 总结

### 指标体系建设检查清单

```markdown
## 设计阶段
- [ ] 确定监控目标 (用户/开发/运维)
- [ ] 选择合适的方法论 (RED/USE/四个黄金信号)
- [ ] 定义分层指标体系
- [ ] 设计指标命名规范

## 实现阶段
- [ ] 实现核心指标采集
- [ ] 配置指标导出
- [ ] 验证指标准确性
- [ ] 设置合理的采集间隔

## 运营阶段
- [ ] 创建Dashboard
- [ ] 配置告警规则
- [ ] 建立On-call流程
- [ ] 定期Review和优化
```

### 方法论选择指南

| 场景 | 推荐方法论 | 关键指标 |
|------|-----------|----------|
| HTTP API/微服务 | RED | Rate, Errors, Duration |
| 基础设施/资源 | USE | Utilization, Saturation, Errors |
| 整体系统健康 | 四个黄金信号 | Latency, Traffic, Errors, Saturation |
| 用户体验 | 自定义业务指标 | 转化率, 留存率, 满意度 |

---

**参考资源**:

- [Google SRE Book - Monitoring](https://sre.google/sre-book/monitoring/)
- [Brendan Gregg - USE Method](http://www.brendangregg.com/usemethod.html)
- [Tom Wilkie - RED Method](https://www.weave.works/blog/the-red-method-key-metrics-for-microservices-architecture/)
- [Prometheus Best Practices](https://prometheus.io/docs/practices/naming/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
