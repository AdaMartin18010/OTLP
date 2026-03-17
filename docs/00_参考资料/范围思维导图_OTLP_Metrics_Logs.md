# 范围思维导图：OTLP / Metrics / Logs

> **覆盖范围**: 三条内容范围（OTLP 协议、Metrics 数据模型、Logs 数据模型）
> **用途**: 概念层级与知识结构按范围分开展示
> **关联**: [00_范围-权威对齐矩阵](../../docs/🔬_批判性评价与持续改进计划/00_范围-权威对齐矩阵.md)

---

## 1. OTLP 协议范围思维导图

（传输 / 序列化 / 语义约定）

```mermaid
mindmap
  root((OTLP协议))
    传输
      gRPC
        HTTP/2
        端口4317
      HTTP
        HTTP/1.1
        端口4318
    序列化
      Protobuf
        默认编码
        二进制
      JSON
        HTTP JSON
        可读
    语义约定
      HTTP属性
      gRPC属性
      数据库与消息队列
      云平台与FaaS
```

---

## 2. OTLP Metrics 数据模型范围思维导图

（类型 / 聚合 / 映射）

```mermaid
mindmap
  root((Metrics数据模型))
    类型
      Counter
      Gauge
      Histogram
      UpDownCounter
      ExponentialHistogram
    聚合
      Cumulative
      Delta
      pre_aggregated时序
    Prometheus_StatsD映射
      Prometheus_to_OTLP
      OTLP_to_Prometheus
      StatsD_to_OTLP
      OTLP_to_StatsD
```

---

## 3. OTLP Logs 数据模型范围思维导图

（Event / 属性 / 资源 / 格式映射）

```mermaid
mindmap
  root((Logs数据模型))
    Event_LogRecord
      时间戳与严重性
      body
      trace_span关联
    属性
      LogRecord_attributes
      事件级键值对
    Resource
      Resource_attributes
      实体级共用
    格式映射
      JSON_to_LogRecord
      Syslog_to_LogRecord
      云格式_to_LogRecord
```
