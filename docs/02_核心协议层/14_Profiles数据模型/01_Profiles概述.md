---
title: Profiles概述 - 可观测性第四大支柱
description: OpenTelemetry Profiles信号概述，作为可观测性第四大支柱，与Traces、Metrics、Logs并列
version: OTLP v1.9.0
spec_version: v1.55.0
date: 2026-03-17
category: 核心协议
tags:
  - profiles
  - profiling
  - ebpf
  - performance
  - observability
status: published
---

# Profiles概述 - 可观测性第四大支柱

> **OTLP版本**: v1.9.0 (Profiles部分为development状态)
> **规范状态**: Development/Unstable
> **预期GA**: 2025年
> **最后更新**: 2026-03-17

---

## 1. Profiles信号简介

### 1.1 什么是Profiles

**Profiles（性能剖析）是OpenTelemetry引入的第四大可观测性信号**，与Metrics、Traces、Logs并列：

| 信号类型 | 回答的问题 | 典型用途 |
|----------|-----------|----------|
| **Metrics** | "什么"和"多少" | 系统整体健康度、趋势 |
| **Traces** | "哪里" | 请求流经路径、依赖关系 |
| **Logs** | "什么发生了" | 事件详情、调试信息 |
| **Profiles** ⭐ | "为什么"和"效率如何" | 代码级性能分析、资源瓶颈 |

### 1.2 Profiles的核心价值

```
┌─────────────────────────────────────────────────────────────────┐
│                    Profiles核心价值                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  🔍 代码级可见性                                                │
│     └── 精确到函数/行号的性能数据                               │
│                                                                 │
│  📊 资源使用分析                                                │
│     └── CPU、内存、I/O的详细分解                                │
│                                                                 │
│  🔗 跨信号关联                                                  │
│     └── 从Metrics峰值 → Trace慢请求 → Profile代码位置          │
│                                                                 │
│  ⚡ 低开销持续采样                                              │
│     └── eBPF技术实现<1%性能开销                                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Profiles发展里程碑

| 时间 | 里程碑 | 状态 |
|------|--------|------|
| 2020年10月 | 提议将Profiling添加为信号 | ✅ 完成 |
| 2022年6月 | 首次SIG会议 | ✅ 完成 |
| 2024年3月 | OpenTelemetry宣布支持Profiling | ✅ 完成 |
| 2024年6月 | Elastic捐赠eBPF Continuous Profiling Agent | ✅ 完成 |
| OTLP v1.3.0 | Profiles作为新信号类型添加到OTLP | ✅ 完成 |
| Collector v0.112.0+ | Collector支持接收、处理和导出Profiling数据 | ✅ 完成 |
| **2025年** | **预期GA（正式发布）** | ⏳ 计划中 |

---

## 3. Profiles数据模型

### 3.1 核心概念

```
┌─────────────────────────────────────────────────────────────────┐
│                    Profile数据模型核心概念                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐                                                │
│  │   Profile   │  单次采样收集的性能数据                         │
│  └──────┬──────┘                                                │
│         │                                                       │
│    ┌────┴────┐                                                  │
│    │         │                                                   │
│    ▼         ▼                                                   │
│ ┌───────┐ ┌───────┐                                             │
│ │Sample │ │Location│                                             │
│ │采样点 │ │ 位置   │                                             │
│ └───┬───┘ └───┬───┘                                             │
│     │         │                                                  │
│     │    ┌────┴────┐                                             │
│     │    │         │                                             │
│     │    ▼         ▼                                             │
│     │ ┌───────┐ ┌───────┐                                       │
│     │ │Function│ │  Line  │                                      │
│     │ │ 函数   │ │  行号  │                                      │
│     │ └───────┘ └───────┘                                       │
│     │                                                            │
│     ▼                                                            │
│ ┌───────────┐                                                   │
│ │ StackTrace │  调用栈（从下到上：根→叶）                        │
│ │   栈跟踪   │                                                   │
│ └───────────┘                                                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 Profile结构定义

```protobuf
// opentelemetry/proto/profiles/v1development/profiles.proto

message Profile {
  // 采样类型和周期
  repeated ValueType sample_type = 1;

  // 实际采样数据
  repeated Sample sample = 2;

  // 映射信息（二进制文件）
  repeated Mapping mapping = 3;

  // 位置信息（函数+行号）
  repeated Location location = 4;

  // 函数元数据
  repeated Function function = 5;

  // 字符串表（节省空间）
  repeated string string_table = 6;

  // 时间戳
  fixed64 time_nanos = 7;

  // 采样周期（纳秒）
  int64 duration_nanos = 8;

  // 与pprof的兼容性
  bytes original_payload = 9;
  string original_payload_format = 10;  // "pprof", "jfr", "linux_perf"
}

message Sample {
  // 位置ID列表（栈帧）
  repeated uint64 location_id = 1;

  // 采样值（与sample_type对应）
  repeated int64 value = 2;

  // 标签（属性）
  repeated Label label = 3;
}

message Location {
  uint64 id = 1;
  uint64 mapping_id = 2;
  uint64 address = 3;
  repeated Line line = 4;
}

message Function {
  uint64 id = 1;
  int64 name = 2;      // 字符串表索引
  int64 system_name = 3;
  int64 filename = 4;
  int64 start_line = 5;
}
```

### 3.3 与pprof的关系

**设计决策**: Profiles SIG决定**不追求与pprof的严格线级兼容性，而是追求可转换性(convertibility)**

```
┌─────────────────────────────────────────────────────────────────┐
│                  Profiles与pprof关系                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   pprof格式          OTLP Profiles格式          其他格式        │
│      │                      │                      │            │
│      │    ┌──────────────┐  │  ┌──────────────┐   │            │
│      └───→│   转换器      ├──┼─→│   转换器      │←──┘            │
│           │ (pprof→OTLP) │  │  │ (OTLP→其他)  │                │
│           └──────────────┘  │  └──────────────┘                │
│                             │                                   │
│                      ┌──────▼──────┐                           │
│                      │  统一分析   │                           │
│                      │  平台/工具  │                           │
│                      └─────────────┘                           │
│                                                                 │
│   优势:                                                         │
│   • 与其他OTLP信号保持一致的设计                                │
│   • 支持双向转换                                                │
│   • 可扩展性更强                                                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 4. Profiles采集技术

### 4.1 采集方式对比

| 采集方式 | 原理 | 开销 | 适用场景 |
|----------|------|------|----------|
| **eBPF** | 内核探针 | <1% | 生产环境持续采样 |
| **语言内置** | 运行时支持 | 2-5% | 特定语言深度分析 |
| **系统级** | perf_event | <1% | 系统级性能分析 |

### 4.2 eBPF Continuous Profiling架构

```
┌─────────────────────────────────────────────────────────────────┐
│              OpenTelemetry eBPF Profiler架构                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    用户空间 (User Space)                  │   │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │   │
│  │  │  符号解析    │    │  栈聚合      │    │  OTLP导出器  │  │   │
│  │  │  (Symbol    │←───│  (Stack      │←───│  (OTLP       │  │   │
│  │  │   Resolver) │    │   Aggregator)│    │   Exporter)  │  │   │
│  │  └─────────────┘    └─────────────┘    └─────────────┘  │   │
│  │           ↑                                    │          │   │
│  │           │                                    │          │   │
│  │           └────────────────────────────────────┘          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                            │                                   │
│                            │ perf_event_open()                 │
│                            │ eBPF maps                         │
│                            ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    内核空间 (Kernel Space)                │   │
│  │  ┌─────────────────────────────────────────────────┐     │   │
│  │  │              eBPF程序                            │     │   │
│  │  │  • CPU采样 (perf_event)                         │     │   │
│  │  │  • 栈走查 (bpf_get_stackid)                     │     │   │
│  │  │  • 进程过滤 (task_struct)                       │     │   │
│  │  │  • 数据聚合 (BPF_MAP_TYPE_STACK_TRACE)         │     │   │
│  │  └─────────────────────────────────────────────────┘     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 5. Profiles与其他信号的关联

### 5.1 双向链接能力

```
┌─────────────────────────────────────────────────────────────────┐
│                Profiles跨信号关联能力                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐         ┌──────────┐         ┌──────────┐       │
│  │ Metrics  │←───────→│  Traces  │←───────→│  Logs    │       │
│  └────┬─────┘         └────┬─────┘         └──────────┘       │
│       │                    │                                   │
│       │                    │                                   │
│       │              ┌─────┴─────┐                            │
│       └─────────────→│ Profiles  │←───────────────────────────┘
│                      │  (代码级)  │                            │
│                      └───────────┘                            │
│                                                                 │
│  关联场景:                                                      │
│  • CPU峰值(Metrics) → 慢请求(Trace) → 热点函数(Profile)        │
│  • 内存泄漏(Metrics) → 分配栈(Profile)                         │
│  • 错误日志(Log) → 异常栈(Profile)                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 关联示例

**场景**: 发现服务CPU使用率异常

```
步骤1: Metrics告警
  └── cpu_usage_percent > 80%

步骤2: 关联到Trace
  └── 发现/trace/orders/create端点P99延迟增加

步骤3: 关联到Profile
  └── 该端点的热点函数: parseJSON()占用65% CPU

步骤4: 定位根因
  └── parseJSON()处理大JSON对象，需要优化
```

---

## 6. Collector Profiles Pipeline

### 6.1 配置示例

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  batch:
    timeout: 10s
    send_batch_size: 256

  # 保留特定服务的Profile
  filter:
    error_mode: ignore
    traces:
      span:
        - 'attributes["service.name"] == "unwanted-service"'

exporters:
  otlphttp:
    endpoint: https://profiling-backend.internal
    compression: gzip

service:
  pipelines:
    profiles:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlphttp]
```

### 6.2 启用Profiles支持

**注意**: Profiles支持需要启用特性门

```bash
# 使用--feature-gates启用profiles支持
otelcol --config config.yaml --feature-gates=service.profilesSupport
```

---

## 7. 部署模式

### 7.1 Kubernetes DaemonSet部署

```yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-profiling-agent
  namespace: monitoring
spec:
  selector:
    matchLabels:
      app: otel-profiling-agent
  template:
    metadata:
      labels:
        app: otel-profiling-agent
    spec:
      hostPID: true  # 访问主机进程
      containers:
        - name: profiling-agent
          image: ghcr.io/open-telemetry/opentelemetry-ebpf-profiler:v0.12.0
          args:
            - "-collection-agent"
            - "otel-collector.monitoring.svc:4317"
            - "-reporter-interval"
            - "60s"
            - "-samples-per-second"
            - "20"
          securityContext:
            privileged: true  # 需要特权运行eBPF
          resources:
            requests:
              cpu: 50m
              memory: 128Mi
            limits:
              cpu: 200m
              memory: 512Mi
          volumeMounts:
            - name: hostfs
              mountPath: /hostfs
              readOnly: true
      volumes:
        - name: hostfs
          hostPath:
            path: /
```

### 7.2 性能开销

| 配置 | CPU开销 | 内存开销 | 网络开销 |
|------|---------|----------|----------|
| 20 samples/sec | <1% | ~100MB | ~10KB/s |
| 50 samples/sec | 1-2% | ~200MB | ~25KB/s |
| 100 samples/sec | 2-3% | ~400MB | ~50KB/s |

---

## 8. 已知限制和未来工作

### 8.1 当前限制

| 限制 | 说明 | 计划解决时间 |
|------|------|--------------|
| **稳定性** | Profiles信号标记为unstable | 2025 GA |
| **符号解析** | 需要访问二进制文件和调试符号 | 持续优化 |
| **多语言** | 当前主要支持Linux/eBPF | 扩展中 |
| **存储成本** | Profile数据量大 | 采样优化 |

### 8.2 路线图

```
2025 Q1:  Collector Profiles Pipeline稳定
2025 Q2:  Java/Python运行时Profiler
2025 Q3:  完整符号解析方案
2025 Q4:  Profiles GA发布
```

---

## 9. 参考文档

| 资源 | 链接 |
|------|------|
| Profiles规范 | <https://opentelemetry.io/docs/specs/otel/profiles/> |
| Profiles博客 | <https://opentelemetry.io/blog/2024/state-profiling/> |
| eBPF Profiler | <https://github.com/open-telemetry/opentelemetry-ebpf-profiler> |
| OTLP Proto | <https://github.com/open-telemetry/opentelemetry-proto> |

---

**最后更新**: 2026-03-17
**维护者**: OTLP核心协议团队
**状态**: Development (向GA演进中)
