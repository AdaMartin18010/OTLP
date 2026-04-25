# Prometheus / OpenMetrics 兼容性完整映射

> **标准来源**: OpenTelemetry Specification v1.56.0 — Compatibility / Prometheus and OpenMetrics
> **参考标准**: OpenMetrics Specification (CNCF Incubating)
> **核心目标**: 系统化映射 OpenTelemetry Metrics 与 Prometheus/OpenMetrics 之间的数据模型差异、转换规则和边界情况

---

## 一、标准定位与关系

### 1.1 三个标准的三角关系

OpenTelemetry Metrics 的设计与 Prometheus 高度兼容，同时 OpenMetrics 作为 Prometheus 的演进标准，正在推动更广泛的行业采纳。OpenTelemetry Collector 是连接这两个生态的关键桥梁。

### 1.2 为什么兼容性至关重要

Prometheus 是云原生监控的事实标准，绝大多数 Kubernetes 集群运行 Prometheus，Grafana 仪表盘生态基于 PromQL，云厂商也提供托管 Prometheus 服务。OpenTelemetry 必须无缝集成这个生态，而不是试图替代它。

---

## 二、数据模型对比

### 2.1 核心概念映射

| OpenTelemetry | Prometheus / OpenMetrics | 说明 |
|--------------|-------------------------|------|
| `Counter` | `Counter` | 单调递增计数器 |
| `UpDownCounter` | `Gauge` | 可增可减，Prometheus 无直接对应 |
| `Histogram` | `Histogram` | 分桶直方图 |
| `ExponentialHistogram` | `Native Histogram` | Prometheus v2.40+ 支持 |
| `Gauge` | `Gauge` | 瞬时值 |
| `ObservableGauge` | `Gauge` | 异步采集的 Gauge |
| `ObservableCounter` | `Counter` | 异步采集的 Counter |
| `ObservableUpDownCounter` | `Gauge` | 异步可增减，映射为 Gauge |
| `Summary` | `Summary` | OTel 不推荐使用 Summary |
| `Attributes` | `Labels` | 维度键值对 |
| `Resource` | `Target Labels` | 资源元数据，通过 relabel 注入 |
| `Scope` | 无直接对应 | OTel 的 Instrumentation Scope |

### 2.2 Counter 的差异

OpenTelemetry Counter 支持 Delta 和 Cumulative 两种 temporality，而 Prometheus Counter 总是 Cumulative。映射时，OTel Cumulative Counter 可直接映射，Delta Counter 需要在 Collector 中累加为 Cumulative。

### 2.3 UpDownCounter 的挑战

Prometheus 无原生 UpDownCounter 类型，解决方案是映射为 Gauge。Gauge 在 Prometheus 中就是可增可减的，Cumulative UpDownCounter 可直接映射，Delta UpDownCounter 需要在 Collector 中累加。

### 2.4 Histogram 的关键差异

OpenTelemetry Histogram 支持 Explicit Bucket 和 Exponential Bucket，支持 Delta 和 Cumulative temporality。Prometheus Histogram 仅支持 Explicit Bucket，总是 Cumulative，桶边界由服务端在抓取时定义。当桶边界不匹配时，Collector 需要进行重分桶，这会引入误差。建议让 OTel SDK 使用与 Prometheus 服务端相同的桶边界。

---

## 三、名称映射

### 3.1 指标名称转换

| 约束 | OpenTelemetry | Prometheus / OpenMetrics |
|------|--------------|-------------------------|
| 字符集 | 允许 `.` 和 `-` | 只允许 `[a-zA-Z_:][a-zA-Z0-9_:]*` |
| 分隔符 | 推荐使用 `.` | 使用 `_` |
| 单位后缀 | 推荐在名称中包含 | 通常不包含 |

转换规则：将 `.` 替换为 `_`，添加单位后缀。例如 `http.request.duration` 转换为 `http_request_duration_seconds`。

---

## 四、Temporality 转换

### 4.1 Delta vs Cumulative

Delta 只导出周期内的增量值，数据量小、延迟低，适合流式处理。Cumulative 是从启动开始的累积值，查询简单，丢失一个点仍可查询，适合 PromQL rate() 函数。

### 4.2 Collector 转换

Collector 提供 `deltatocumulative` 处理器将 Delta 转为 Cumulative，`cumulativetodelta` 处理器反向转换，`deltatorate` 处理器将 Delta 转为 Rate Gauge。

---

## 五、边界情况与陷阱

### 5.1 Staleness 处理

Prometheus 如果指标在 5 分钟内未被抓取，标记为 stale，stale 指标在查询时被视为不存在。需要确保 Collector 高可用，配置 metric_expiration 与 Prometheus 一致。

### 5.2 目标信息映射

OpenTelemetry 的 Resource 在 Prometheus 中通过 `target_info` 指标映射。关联查询使用 PromQL 的 info 函数，例如 `http_requests_total * on(instance) group_left(service_version) target_info`。

### 5.3 Exemplars 映射

OpenTelemetry Exemplar 包含值、时间戳、Trace ID、Span ID，附加在 Histogram/Summary 桶上。Prometheus OpenMetrics 格式支持 Exemplar，Prometheus v2.26+ 支持存储和查询 Exemplar。Collector 可直接映射 OTel Exemplar 到 Prometheus Exemplar。

---

## 六、检查清单

- [ ] SDK temporality 设置与后端 Prometheus 期望一致（通常 Cumulative）
- [ ] Histogram 桶边界与 Prometheus scrape 配置对齐
- [ ] Resource 属性通过 target_info 正确映射
- [ ] 指标名称中的 `.` 和 `-` 已正确替换为 `_`
- [ ] 单位后缀已正确添加
- [ ] Exemplars 已启用（如果后端支持）
- [ ] Staleness 配置一致
- [ ] UpDownCounter 正确映射为 Gauge
- [ ] Delta 指标在 Collector 中正确转换为 Cumulative

---

## 七、参考资源

- OpenTelemetry Specification: Compatibility / Prometheus and OpenMetrics
- OpenMetrics Specification
- Prometheus Data Model Documentation
- OpenTelemetry Collector: Prometheus Receiver / Exporter

---

> **总结**: OpenTelemetry Metrics 与 Prometheus/OpenMetrics 的兼容性总体良好，核心挑战在于 temporality 转换、桶边界对齐和名称映射。通过合理配置 Collector 和 SDK，可以实现两个生态的无缝对接。
