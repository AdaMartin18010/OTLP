---
title: PromQL与TraceQL完全指南
description: PromQL指标查询语言和TraceQL追踪查询语言的完全指南，包含语法、函数、最佳实践和实战案例
version: Prometheus v2.55 / Grafana Tempo v2.6
date: 2026-03-17
author: OTLP项目团队
category: 数据分析与洞察
tags:
  - promql
  - traceql
  - query-language
  - prometheus
  - tempo
status: published
---

# PromQL与TraceQL完全指南

> **版本**: Prometheus v2.55 / Grafana Tempo v2.6
> **最后更新**: 2026-03-17
> **阅读时间**: 约45分钟

---

## 1. PromQL基础

### 1.1 数据模型

```
┌─────────────────────────────────────────────────────────────────┐
│                    Prometheus数据模型                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  时间序列 (Time Series)                                         │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  唯一标识: metric_name + label_set                       │   │
│  │                                                          │   │
│  │  http_requests_total{method="GET", status="200"}         │   │
│  │         ↑              ↑                    ↑            │   │
│  │    metric_name    label key           label value        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  样本 (Sample)                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  每个样本包含:                                           │   │
│  │  • float64值                                            │   │
│  │  • 毫秒精度的时间戳                                     │   │
│  │                                                          │   │
│  │  示例: (timestamp: 1640995200000, value: 42.5)         │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  指标类型                                                       │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Counter: 累计值，单调递增 (http_requests_total)         │   │
│  │  Gauge: 瞬时值，可增可减 (temperature_celsius)           │   │
│  │  Histogram: 分布采样 (request_duration_seconds)          │   │
│  │  Summary: 预计算分位数                                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 基础查询

```promql
# ===== 瞬时向量 (Instant Vector) =====
# 返回最新样本
http_requests_total

# 带标签过滤的瞬时向量
http_requests_total{method="GET", status="200"}

# 正则匹配
http_requests_total{status=~"2.."}
http_requests_total{method=~"GET|POST"}

# 不等于
http_requests_total{status!="200"}

# ===== 范围向量 (Range Vector) =====
# 返回一段时间内的所有样本
http_requests_total[5m]        # 过去5分钟
http_requests_total[1h]        # 过去1小时
http_requests_total[1d]        # 过去1天

# 范围向量不能直接显示，必须配合函数使用
rate(http_requests_total[5m])  # 正确

# ===== 偏移 (Offset) =====
# 查询历史数据
http_requests_total offset 1h   # 1小时前
http_requests_total offset 1d   # 1天前

# 与范围向量结合
rate(http_requests_total[5m] offset 1d)
```

### 1.3 运算符

```promql
# ===== 算术运算符 =====
# + 加法
node_memory_MemTotal_bytes + node_memory_MemFree_bytes

# - 减法
node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes

# * 乘法
http_requests_total * 100

# / 除法
node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes

# % 取模
up % 2

# ^ 幂运算
2 ^ 10

# ===== 比较运算符 =====
# == 等于
http_requests_total == 100

# != 不等于
up != 1

# > 大于
http_request_duration_seconds > 0.5

# < 小于
temperature_celsius < 0

# >= 大于等于
disk_usage_percent >= 80

# <= 小于等于
memory_usage_percent <= 90

# ===== 逻辑运算符 =====
# and (交集)
http_requests_total and up

# or (并集)
http_requests_total or node_cpu_seconds_total

# unless (差集)
http_requests_total unless http_requests_total{status="200"}

# ===== 向量匹配 =====
# on (按指定标签匹配)
node_memory_MemTotal_bytes / on(instance) node_memory_MemAvailable_bytes

# ignoring (忽略指定标签)
rate(http_requests_total[5m]) / ignoring(method) rate(http_requests_total[5m])

# group_left (多对一匹配)
http_requests_total / on(service) group_left method:http_errors_total

# group_right (一对多匹配)
method:http_errors_total / on(service) group_right http_requests_total
```

---

## 2. PromQL函数

### 2.1 聚合函数

```promql
# ===== sum (求和) =====
# 所有值求和
sum(http_requests_total)

# 按标签分组求和
sum by (method) (http_requests_total)
sum by (method, status) (http_requests_total)

# without (排除标签)
sum without (instance) (http_requests_total)

# ===== avg (平均值) =====
avg(http_request_duration_seconds)
avg by (service) (http_request_duration_seconds)

# ===== min/max (最小/最大值) =====
min(http_request_duration_seconds)
max(http_request_duration_seconds)

# ===== count (计数) =====
# 时间序列数量
count(up)

# count_values (按值计数)
count_values("version", build_info)

# ===== quantile (分位数) =====
# 注意: 这是对时间序列的分位数，不是Histogram的分位数
quantile(0.95, http_request_duration_seconds)

# ===== topk/bottomk (前/后N个) =====
topk(5, http_requests_total)
bottomk(3, http_request_duration_seconds)

# ===== stddev/stdvar (标准差/方差) =====
stddev(http_request_duration_seconds)
stdvar(http_request_duration_seconds)
```

### 2.2 范围向量函数

```promql
# ===== rate (增长率) =====
# 计算Counter的每秒增长率
# 必须配合范围向量使用
rate(http_requests_total[5m])

# 按服务分组的QPS
sum by (service) (rate(http_requests_total[5m]))

# ===== irate (瞬时增长率) =====
# 基于最后两个样本计算，更灵敏
irate(http_requests_total[5m])

# ===== increase (增长量) =====
# 计算范围内的增长总量
increase(http_requests_total[1h])

# ===== delta (差值) =====
# 计算Gauge的差值
delta(temperature_celsius[1h])

# ===== idelta (瞬时差值) =====
idelta(temperature_celsius[5m])

# ===== deriv (导数) =====
# 计算Gauge的每秒变化率
deriv(temperature_celsius[10m])

# ===== predict_linear (线性预测) =====
# 基于线性回归预测未来值
predict_linear(disk_usage_percent[1h], 3600)  # 预测1小时后的磁盘使用率

# ===== holt_winters (霍尔特-温特斯平滑) =====
# 双指数平滑，用于趋势预测
holt_winters(temperature_celsius[1d], 0.1, 0.5)
```

### 2.3 Histogram函数

```promql
# ===== histogram_quantile (直方图分位数) =====
# 计算Histogram的分位数

# P50延迟
histogram_quantile(0.5,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# P95延迟
histogram_quantile(0.95,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# P99延迟
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# 按服务分组的P99
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (service, le)
)

# ===== 直方图桶操作 =====
# 统计特定范围内的请求数
sum(rate(http_request_duration_seconds_bucket{le="0.1"}[5m]))

# 计算直方图平均值
sum(rate(http_request_duration_seconds_sum[5m]))
/
sum(rate(http_request_duration_seconds_count[5m]))

# ===== 估算分布比例 =====
# 计算超过1秒的请求比例
sum(rate(http_request_duration_seconds_bucket{le="1"}[5m]))
/
sum(rate(http_request_duration_seconds_bucket{le="+Inf"}[5m]))
```

### 2.4 时间函数

```promql
# ===== 时间戳函数 =====
time()                    # 当前Unix时间戳
timestamp(metric)         # 样本的时间戳

# ===== 日期时间函数 =====
year(v=vector(time()))    # 年份
month(v=vector(time()))   # 月份 (1-12)
day_of_month(v=vector(time()))  # 日期 (1-31)
day_of_week(v=vector(time()))   # 星期 (0-6, 0是周日)
hour(v=vector(time()))    # 小时 (0-23)
minute(v=vector(time()))  # 分钟 (0-59)

# ===== 使用示例: 工作时间过滤 =====
# 只监控工作时间 (9:00-18:00, 周一到周五)
metric
  and on() (hour() >= 9 and hour() <= 18)
  and on() (day_of_week() > 0 and day_of_week() < 6)
```

---

## 3. PromQL高级技巧

### 3.1 子查询

```promql
# ===== 子查询语法 =====
# <instant_query> [<range>:<resolution>]

# 计算过去1小时最大QPS
max_over_time(
  sum(rate(http_requests_total[5m]))[1h:1m]
)

# 计算平均CPU使用率的标准差
stddev_over_time(
  avg(cpu_usage_percent)[1h:5m]
)

# ===== 常见子查询模式 =====

# 1. 计算5分钟内的平均QPS
avg_over_time(
  sum(rate(http_requests_total[1m]))[5m:1m]
)

# 2. 查找过去1小时的最大延迟
max_over_time(
  histogram_quantile(0.99,
    sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
  )[1h:5m]
)

# 3. 计算错误率的波动
stddev_over_time(
  (
    sum(rate(http_requests_total{status=~"5.."}[5m]))
    /
    sum(rate(http_requests_total[5m]))
  )[1h:5m]
)
```

### 3.2 复杂查询案例

```promql
# ===== 案例1: 计算Apdex分数 =====
# Apdex = (满意样本 + 0.5 * 容忍样本) / 总样本
# 假设满意: < 0.5s, 容忍: < 2s

(
  sum(rate(http_request_duration_seconds_bucket{le="0.5"}[5m]))
  +
  sum(rate(http_request_duration_seconds_bucket{le="2"}[5m])) / 2
)
/
sum(rate(http_request_duration_seconds_bucket{le="+Inf"}[5m]))

# ===== 案例2: 计算服务依赖延迟贡献 =====
# 找出对总延迟贡献最大的下游服务

sum by ( downstream_service ) (
  rate(span_duration_seconds_sum{span_kind="client"}[5m])
)
/
sum (
  rate(span_duration_seconds_sum{span_kind="server"}[5m])
)

# ===== 案例3: 检测延迟退化 =====
# 当前P99比过去1小时平均P99高50%

histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)
>
1.5 * avg_over_time(
  histogram_quantile(0.99,
    sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
  )[1h:5m]
)

# ===== 案例4: 计算可用性 =====
# 过去30天的可用性 (基于错误率)

1 - (
  sum_over_time(
    (sum(rate(http_requests_total{status=~"5.."}[5m]))
     /
     sum(rate(http_requests_total[5m])))[30d:5m]
  ) / (30 * 24 * 12)  # 30天内的5分钟间隔数
)

# ===== 案例5: 查找慢节点 =====
# 延迟P99超过整体P99 2倍的实例

histogram_quantile(0.99,
  sum by (instance, le) (rate(http_request_duration_seconds_bucket[5m]))
)
>
2 * histogram_quantile(0.99,
  sum by (le) (rate(http_request_duration_seconds_bucket[5m]))
)
```

---

## 4. TraceQL基础

### 4.1 TraceQL数据模型

```
┌─────────────────────────────────────────────────────────────────┐
│                    TraceQL数据模型                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Trace (追踪)                                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • traceID: 唯一标识符                                    │   │
│  │ • rootSpan: 根Span                                       │   │
│  │ • duration: 总持续时间                                   │   │
│  │ • services: 涉及的服务列表                               │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  Span (跨度)                                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • spanID: 唯一标识符                                     │   │
│  │ • name: Span名称 (如 "HTTP GET /api/users")              │   │
│  │ • kind: Span类型 (client/server/internal/producer/consumer)│  │
│  │ • status: 状态 (ok/error/unset)                          │   │
│  │ • duration: 持续时间                                     │   │
│  │ • attributes: 键值对属性                                 │   │
│  │ • events: 事件列表                                       │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  属性类型                                                       │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ 内置属性:                                                │   │
│  │ • service.name, span.name, span.kind, status             │   │
│  │ • duration, traceDuration                                │   │
│  │                                                          │   │
│  │ 资源属性:                                                │   │
│  │ • resource.service.name, resource.host.name              │   │
│  │                                                          │   │
│  │ 自定义属性:                                              │   │
│  │ • http.method, http.status_code, db.system               │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 TraceQL基础查询

```traceql
# ===== 基础选择器 =====

# 按服务名查询
{service.name="order-service"}

# 按Span名查询
{name="HTTP GET /api/orders"}

# 按状态查询
{status=error}
{status=ok}

# 按Span类型查询
{span.kind="server"}
{span.kind="client"}

# ===== 属性过滤 =====

# 字符串匹配
{http.method="GET"}
{http.route="/api/orders/:id"}

# 数值比较
{http.status_code=200}
{http.status_code>=400}
{duration>100ms}
{duration<1s}

# 正则匹配
{http.url=~"/api/.*"}
{service.name=~"order-.*"}

# 不等于
{http.method!="OPTIONS"}

# 存在性检查
{http.status_code}
{custom.attribute}

# ===== 组合条件 =====

# AND
{service.name="order-service" && http.method="POST"}

# OR
{status=error || http.status_code>=500}

# 复杂条件
{service.name="order-service" && http.method="POST" && duration>1s}

# 括号分组
{(service.name="order-service" || service.name="payment-service") && status=error}
```

### 4.3 TraceQL结构查询

```traceql
# ===== 父子关系查询 =====

# 查找父Span是"HTTP GET"的所有子Span
{name="HTTP GET"} > {status=error}

# 查找特定服务的直接子Span
{service.name="gateway"} > {service.name="order-service"}

# 查找任意层级的后代Span
{service.name="gateway"} >> {http.status_code=500}

# ===== 祖先查询 =====

# 查找以特定Span结束的Trace
{service.name="order-service"} < {service.name="gateway"}

# ===== 同级查询 =====

# 查找与指定Span同级的其他Span
{service.name="order-service"} ~ {service.name="payment-service"}
```

### 4.4 TraceQL聚合与选择

```traceql
# ===== select (选择字段) =====

# 选择特定字段
{service.name="order-service"} | select(duration, span.http.url)

# 选择所有字段
{service.name="order-service"} | select_all

# ===== count (计数) =====

# 统计Span数量
{service.name="order-service"} | count()

# 按服务分组计数
{} | count() by (service.name)

# ===== avg/min/max (聚合) =====

# 平均持续时间
{service.name="order-service"} | avg(duration)

# 最大持续时间
{service.name="order-service"} | max(duration)

# 按服务分组的最大延迟
{status=error} | max(duration) by (service.name)

# ===== sum (求和) =====

# 总持续时间
{service.name="order-service"} | sum(duration)

# ===== quantile (分位数) =====

# P95延迟
{service.name="order-service"} | quantile(duration, 0.95)

# P99延迟
{service.name="order-service"} | quantile(duration, 0.99)
```

---

## 5. TraceQL高级查询

### 5.1 复杂查询案例

```traceql
# ===== 案例1: 查找特定错误链路 =====
# 查找订单服务调用支付服务失败的链路

{service.name="order-service" && http.method="POST"}
  > {service.name="payment-service" && status=error}

# ===== 案例2: 查找慢调用链 =====
# 查找持续时间超过2秒的完整Trace

{traceDuration>2s}

# ===== 案例3: 查找特定用户的请求 =====
# 查找用户ID为12345的所有请求

{user.id="12345"}

# ===== 案例4: 查找数据库慢查询 =====
# 查找执行时间超过100ms的数据库查询

{db.system="mysql" && duration>100ms}
| select(duration, db.statement, db.operation)

# ===== 案例5: 查找跨服务错误传播 =====
# 查找从gateway开始，在下游服务出错的链路

{service.name="gateway"}
  >> {status=error}

# ===== 案例6: 查找重复请求 =====
# 查找同一Trace中有多个相同HTTP方法的请求

{http.method="GET"}
| count() by (traceID, http.url)
> 1

# ===== 案例7: 查找特定模式的调用链 =====
# gateway -> order-service -> payment-service

{service.name="gateway"}
  > {service.name="order-service"}
  > {service.name="payment-service"}

# ===== 案例8: 分析错误率最高的端点 =====
# 找出错误率最高的HTTP端点

{status=error}
| count() by (http.route)
/ {}
| count() by (http.route)

# ===== 案例9: 查找超时请求 =====
# 查找被取消或超时的请求

{http.status_code=499 || status=error}
| select(duration, http.url, error.message)

# ===== 案例10: 查找未完成的操作 =====
# 查找没有对应client Span的server Span

{span.kind="server"}
  !~ {span.kind="client"}
```

### 5.2 TraceQL与Metrics关联

```
Trace与Metrics的关联分析:

# 1. 通过Exemplar关联
# Metric中的Exemplar指向具体的Trace
# 在Grafana中点击Metric点可以直接跳转到对应Trace

# 2. 通过标签关联
# 确保Trace和Metric使用相同的标签
# 如: service.name, http.route, http.method

# 3. 关联查询示例
# 先通过PromQL找到高延迟时间段
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
) > 1

# 然后通过TraceQL查询该时间段的慢Trace
# 使用相同的时间范围和服务名
{service.name="order-service" && duration>1s}
```

---

## 6. 查询性能优化

### 6.1 PromQL性能优化

```promql
# ===== 避免高基数查询 =====

# ❌ 不好的: 按instance和pod查询，基数太高
sum by (instance, pod) (metric)

# ✅ 好的: 只按必要的标签分组
sum by (service) (metric)

# ===== 减少时间范围 =====

# ❌ 不好的: 大范围查询
rate(metric[1d])

# ✅ 好的: 使用合理的时间范围
rate(metric[5m])

# ===== 避免嵌套聚合 =====

# ❌ 不好的: 多层嵌套
sum(rate(sum(metric)[5m]))

# ✅ 好的: 单层聚合
sum(rate(metric[5m]))

# ===== 使用录制规则 =====

# 对于复杂查询，使用录制规则预计算
# rules/recording.yml:
# groups:
#   - name: latency_rules
#     rules:
#       - record: job:http_request_latency:p95
#         expr: histogram_quantile(0.95, ...)

# 然后直接查询录制规则
job:http_request_latency:p95
```

### 6.2 TraceQL性能优化

```traceql
# ===== 使用具体标签过滤 =====

# ❌ 不好的: 宽泛的查询
{}

# ✅ 好的: 具体的服务名过滤
{service.name="order-service"}

# ===== 限制时间范围 =====

# 使用合理的时间范围
# Grafana中通常默认查询最近1小时

# ===== 避免深层结构查询 =====

# ❌ 不好的: 深层递归查询
{service.name="gateway"} >>>> {status=error}

# ✅ 好的: 限制层级
{service.name="gateway"} >> {status=error}

# ===== 使用聚合减少返回数据 =====

# ❌ 不好的: 返回所有Span
{service.name="order-service"}

# ✅ 好的: 只返回需要的统计信息
{service.name="order-service"} | count()
```

---

## 7. 实战案例

### 7.1 SLO监控Dashboard

```promql
# ===== 延迟SLO面板 =====
# 目标: P99 < 200ms

# P99延迟
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# SLO合规性
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
) < 0.2

# 错误预算消耗
(
  sum(rate(http_requests_total{status=~"5.."}[1h]))
  / sum(rate(http_requests_total[1h]))
) / 0.001

# ===== 可用性SLO面板 =====
# 目标: 99.9%可用

# 当前可用性
1 - (
  sum(rate(http_requests_total{status=~"5.."}[5m]))
  / sum(rate(http_requests_total[5m]))
)

# ===== 流量面板 =====
# QPS按服务分组
sum by (service) (rate(http_requests_total[5m]))
```

### 7.2 故障排查查询

```promql
# ===== 查找错误突增 =====
# 错误率比过去1小时平均值高3倍

(
  sum(rate(http_requests_total{status=~"5.."}[5m]))
  / sum(rate(http_requests_total[5m]))
)
>
3 * avg_over_time(
  (sum(rate(http_requests_total{status=~"5.."}[5m]))
   / sum(rate(http_requests_total[5m])))[1h:5m]
)

# ===== 查找性能退化 =====
# P99延迟比基线高50%

histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)
>
1.5 * avg_over_time(
  histogram_quantile(0.99,
    sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
  )[1d:5m]
)
```

```traceql
# ===== 查找特定错误链路 =====
# 订单服务调用库存服务失败的Trace

{service.name="order-service" && span.name="checkInventory"}
  > {service.name="inventory-service" && status=error}

# ===== 查找最慢的数据库查询 =====
{db.system="mysql"}
| select(duration, db.statement, db.operation)
| max(duration) by (db.statement)
```

---

## 8. 查询最佳实践

### 8.1 PromQL最佳实践

```markdown
## 1. 使用rate()处理Counter
- Counter必须使用rate()或increase()
- 避免直接使用Counter值

## 2. 直方图使用bucket
- 查询分位数必须使用_bucket指标
- 使用histogram_quantile()函数

## 3. 合理设置时间范围
- rate(): 至少4个样本，通常是5m
- 长期趋势: 使用avg_over_time()

## 4. 避免高基数标签
- 不要在标签中使用用户ID、订单ID等
- 使用高层次的聚合维度

## 5. 使用录制规则
- 复杂查询预计算
- 提高Dashboard加载速度
```

### 8.2 TraceQL最佳实践

```markdown
## 1. 使用具体过滤条件
- 始终指定service.name
- 使用status=error快速定位问题

## 2. 限制查询范围
- 使用合理的时间窗口
- 避免查询过长时间的Trace

## 3. 结合Metrics分析
- 先用Metrics定位问题时间窗口
- 再用TraceQL分析具体原因

## 4. 使用结构化查询
- 使用>和>>分析调用链
- 结合聚合函数统计

## 5. 保存常用查询
- 在Grafana中保存为模板
- 便于快速故障排查
```

---

**参考资源**:

- [PromQL Cheat Sheet](https://promlabs.com/promql-cheat-sheet/)
- [PromQL for Humans](https://timber.io/blog/promql-for-humans/)
- [TraceQL Documentation](https://grafana.com/docs/tempo/latest/traceql/)
- [Querying Traces in Grafana](https://grafana.com/docs/tempo/latest/query/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
