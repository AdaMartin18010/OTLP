---
title: Collector v0.117.0高级配置详解
description: 深入解析Collector v0.117.0的高级配置选项、性能调优、多租户架构和生产环境最佳实践
version: Collector v0.117.0 / OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 核心实现
status: published
tags: [Collector, 配置, 性能优化, 多租户, v0.117.0]
---

# Collector v0.117.0高级配置详解

> **版本**: Collector v0.117.0  
> **对应OTLP**: v1.10.0  
> **最后更新**: 2026-03-17

---

## 目录

1. [配置架构概述](#1-配置架构概述)
2. [Receivers高级配置](#2-receivers高级配置)
3. [Processors高级配置](#3-processors高级配置)
4. [Exporters高级配置](#4-exporters高级配置)
5. [Extensions高级配置](#5-extensions高级配置)
6. [多租户架构配置](#6-多租户架构配置)
7. [性能调优指南](#7-性能调优指南)
8. [高可用配置](#8-高可用配置)
9. [安全配置](#9-安全配置)
10. [监控与可观测性](#10-监控与可观测性)

---

## 1. 配置架构概述

### 1.1 v0.117.0配置结构

```yaml
# Collector v0.117.0 完整配置架构
receivers:
  # 接收器配置
  
processors:
  # 处理器配置
  
exporters:
  # 导出器配置
  
extensions:
  # 扩展组件配置
  
connectors:
  # 连接器配置 (v0.117.0新增/增强)
  
service:
  # 服务级配置
  pipelines:
    # 数据处理流水线
  telemetry:
    # 自监控配置
  extensions: []
    # 启用的扩展列表
```

### 1.2 v0.117.0新特性概览

```yaml
版本亮点:
  Profiles支持:
    - Profiles接收器GA
    - Profiles处理器支持
    - Profiles导出器(多个后端)
  
  性能增强:
    - batch处理器内存优化
    - 更高效的队列管理
    - 改进的并发控制
  
  配置增强:
    - 更灵活的管道配置
    - 改进的资源检测
    - 更强的上下文传播
  
  稳定性:
    - 减少内存泄漏风险
    - 更好的错误处理
    - 改进的重试机制
```

---

## 2. Receivers高级配置

### 2.1 OTLP Receiver完整配置

```yaml
receivers:
  otlp:
    # gRPC协议配置
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        
        # v0.117.0: 增强的TLS配置
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          client_ca_file: /etc/otel/certs/ca.crt
          # 客户端证书验证
          client_auth_type: "require_and_verify_client_cert"
        
        # gRPC特定配置
        max_recv_msg_size_mib: 64
        max_concurrent_streams: 100
        read_buffer_size: 512
        write_buffer_size: 512
        
        # 保持连接配置
        keepalive:
          server:
            enforcement_policy:
              min_time: 5s
              permit_without_stream: true
            parameters:
              max_connection_age: 1200s
              max_connection_age_grace: 300s
              time: 300s
              timeout: 20s
      
      # HTTP协议配置
      http:
        endpoint: 0.0.0.0:4318
        
        # CORS配置
        cors:
          allowed_origins: ["*"]
          allowed_headers: ["*"]
          max_age: 7200
        
        # v0.117.0: 增强的TLS
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
        
        # 请求处理配置
        max_request_body_size: 20971520  # 20MB
        include_metadata: true
        
        # 压缩配置
        compression_algorithms: ["gzip", "zstd", "snappy", "lz4"]
    
    # v0.117.0: 信号类型特定配置
    traces:
      # Traces特定设置
      max_recv_msg_size_mib: 64
    
    metrics:
      # Metrics特定设置
      max_recv_msg_size_mib: 64
    
    logs:
      # Logs特定设置
      max_recv_msg_size_mib: 64
    
    # v0.117.0: Profiles支持
    profiles:
      enabled: true
      max_recv_msg_size_mib: 128  # Profiles通常更大
```

### 2.2 其他重要Receivers

```yaml
receivers:
  # Prometheus Receiver - 高级配置
  prometheus:
    config:
      scrape_configs:
        - job_name: 'kubernetes-pods'
          kubernetes_sd_configs:
            - role: pod
          relabel_configs:
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
              action: keep
              regex: true
          scrape_interval: 15s
          scrape_timeout: 10s
      
      # v0.117.0: 增强的target分配
      target_allocator:
        enabled: true
        endpoint: http://target-allocator:8080
        interval: 30s
  
  # Jaeger Receiver
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
      thrift_compact:
        endpoint: 0.0.0.0:6831
    
    # v0.117.0: 远程采样支持
    remote_sampling:
      strategy_file: /etc/otel/sampling_strategies.json
      strategy_file_reload_interval: 30s
  
  # Kafka Receiver - 高吞吐量场景
  kafka:
    brokers:
      - kafka-1:9092
      - kafka-2:9092
      - kafka-3:9092
    topic: otlp-metrics
    group_id: otel-collector
    
    # v0.117.0: 增强的消费者配置
    consumer:
      max_fetch_min: 1
      max_fetch_max: 1000000
      default_fetch_min: 1
      default_fetch_max: 52428800  # 50MB
      fetch_default: 1048576  # 1MB
    
    # 认证配置
    auth:
      plain_text:
        username: ${KAFKA_USERNAME}
        password: ${KAFKA_PASSWORD}
    
    # TLS配置
    tls:
      insecure: false
      ca_file: /etc/otel/certs/kafka-ca.crt
```

---

## 3. Processors高级配置

### 3.1 Batch Processor深度优化

```yaml
processors:
  batch:
    # 基本配置
    timeout: 1s
    send_batch_size: 8192
    send_batch_max_size: 10240
    
    # v0.117.0: 新增的高级配置
    metadata_keys: ["tenant_id", "environment"]
    metadata_cardinality_limit: 1000
    
    # 内存管理
    # 动态批大小调整
    dynamic_batching:
      enabled: true
      min_batch_size: 1024
      max_batch_size: 32768
      target_latency: 100ms
    
  # 区分信号类型的Batch配置
  batch/traces:
    timeout: 500ms
    send_batch_size: 4096
    send_batch_max_size: 8192
  
  batch/metrics:
    timeout: 2s
    send_batch_size: 16384
    send_batch_max_size: 32768
  
  batch/logs:
    timeout: 1s
    send_batch_size: 8192
    send_batch_max_size: 16384
    
  # v0.117.0: Profiles专用Batch
  batch/profiles:
    timeout: 5s
    send_batch_size: 1024
    send_batch_max_size: 4096
```

### 3.2 Memory Limiter精细控制

```yaml
processors:
  memory_limiter:
    # v0.117.0: 改进的内存检测
    check_interval: 1s
    
    # 内存限制 - 支持百分比和绝对值
    limit_mib: 1500
    # 或 limit_percentage: 75
    
    # 触发限制的水位线
    spike_limit_mib: 256
    # 或 spike_limit_percentage: 20
    
    # v0.117.0: 新的内存管理策略
    memory_management:
      strategy: "soft_limit"  # soft_limit / hard_limit / adaptive
      adaptive:
        target_utilization: 70
        scale_up_factor: 1.2
        scale_down_factor: 0.8
        evaluation_period: 30s
```

### 3.3 Resource Processor增强

```yaml
processors:
  resource:
    # 属性操作
    attributes:
      # 设置属性
      - key: environment
        value: production
        action: upsert
      
      # 从现有属性提取
      - key: service.namespace
        from_attribute: k8s.namespace.name
        action: upsert
      
      # 删除敏感属性
      - key: http.request.header.authorization
        action: delete
      
      # v0.117.0: 条件操作
      - key: tier
        from_attribute: service.name
        action: extract
        # 使用正则提取
        pattern: "^(.*)-service$"
        replacement: "$1"
      
      # v0.117.0: 基于条件的属性操作
      - key: region
        value: us-west-2
        action: upsert
        # 条件表达式
        condition: 'attributes["cloud.provider"] == "aws"'
  
  # Resource Detection处理器
  resourcedetection:
    # 检测器列表
    detectors: [env, system, ec2, ecs, eks, lambda, azure, gcp]
    
    # 超时配置
    timeout: 5s
    
    # 覆盖策略
    override: true
    
    # v0.117.0: 特定检测器配置
    ec2:
      # 自定义标签到属性的映射
      tags:
        - Name
        - Environment
        - Team
    
    # 系统检测器增强
    system:
      hostname_sources: [os, dns, cname]
```

### 3.4 Attributes Processor高级用法

```yaml
processors:
  attributes:
    actions:
      # 基本的CRUD操作
      - key: http.method
        action: delete  # 删除
      
      - key: http.request.method
        from_attribute: http.method
        action: upsert  # 重命名
      
      # v0.117.0: 复杂条件操作
      - key: error.type
        from_attribute: http.status_code
        action: insert
        # 条件表达式
        condition: 'attributes["http.status_code"] >= 400'
      
      # 批量操作
      - key: http.request.header.user_agent
        action: hash
        # 敏感信息哈希
      
      # 值转换
      - key: http.url
        action: extract
        pattern: "https?://([^/]+)/.*"
        replacement: "$1"
        result_key: http.host
  
  # Metrics特定属性处理
  attributes/metrics:
    actions:
      - key: metric_type
        from_attribute: type
        action: upsert
      
      # 维度基数控制
      - key: user_id
        action: delete
      
      # 基数限制
      - key: http.route
        action: limit_cardinality
        max_cardinality: 1000
        fallback_value: "/other"
```

---

## 4. Exporters高级配置

### 4.1 OTLP Exporter生产配置

```yaml
exporters:
  otlp:
    # 端点配置
    endpoint: otel-collector.backend:4317
    
    # TLS配置
    tls:
      insecure: false
      ca_file: /etc/otel/certs/ca.crt
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      # v0.117.0: 增强的服务器名称验证
      server_name_override: "otel-collector.backend"
    
    # 超时和重试
    timeout: 30s
    
    # v0.117.0: 智能重试策略
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
      max_elapsed_time: 300s
      # 指数退避 + 抖动
      randomization_factor: 0.5
      multiplier: 1.5
    
    # 队列配置
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
      # v0.117.0: 持久化队列支持
      persistent_storage:
        enabled: true
        directory: /var/lib/otel/queue
        max_size_mib: 1024
    
    # 压缩
    compression: gzip  # gzip, zstd, snappy, none
    
    # 负载均衡
    # v0.117.0: 内置负载均衡
    load_balancing:
      enabled: true
      resolver:
        static:
          hostnames: ["backend-1:4317", "backend-2:4317", "backend-3:4317"]
      routing_key: "service"
  
  # 区分信号类型的OTLP导出器
  otlp/traces:
    endpoint: jaeger-collector:4317
    timeout: 10s
    retry_on_failure:
      enabled: true
      initial_interval: 500ms
      max_interval: 10s
    sending_queue:
      queue_size: 5000
  
  otlp/metrics:
    endpoint: prometheus-remote-write:4317
    timeout: 30s
    compression: zstd
    sending_queue:
      queue_size: 20000
  
  # v0.117.0: Profiles导出器
  otlp/profiles:
    endpoint: pyroscope:4317
    timeout: 60s
    compression: zstd
    sending_queue:
      queue_size: 5000
```

### 4.2 Prometheus Remote Write

```yaml
exporters:
  prometheusremotewrite:
    endpoint: http://prometheus:9090/api/v1/write
    
    # v0.117.0: 增强的认证支持
    auth:
      authenticator: basicauth/prw
    
    # 标签管理
    external_labels:
      collector: ${HOSTNAME}
      environment: production
    
    # 请求配置
    timeout: 30s
    read_buffer_size: 0
    write_buffer_size: 524288
    
    # v0.117.0: 高级重试
    retry:
      enabled: true
      initial_interval: 50ms
      max_interval: 5s
      max_elapsed_time: 30s
    
    # WAL (Write Ahead Log)
    wal:
      enabled: true
      directory: /var/lib/otel/wal
      # v0.117.0: 增强的WAL配置
      max_size: 300
      truncate_frequency: 60s
      cache_size: 1000
    
    # 指标转换
    target_info:
      enabled: true
    
    # 资源属性到标签的映射
    resource_to_telemetry_conversion:
      enabled: true
```

### 4.3 多后端导出策略

```yaml
exporters:
  # 主要后端 - Jaeger
  jaeger:
    endpoint: jaeger-collector:14250
    tls:
      insecure: true
    
  # 主要后端 - Tempo
  otlp/tempo:
    endpoint: tempo:4317
    tls:
      insecure: true
  
  # 主要后端 - Prometheus
  prometheusremotewrite:
    endpoint: http://prometheus:9090/api/v1/write
  
  # 备份后端 - 对象存储
  awsxray:
    region: us-west-2
    no_verify_ssl: false
    local_mode: false
    # v0.117.0: 改进的批处理
    batch_size: 1000
    
  # 冷存储 - S3
  awss3:
    region: us-west-2
    s3uploader:
      region: us-west-2
      s3_bucket: otel-backup
      s3_prefix: traces/
      s3_partition: hour
  
  # v0.117.0: Profiles后端 - Pyroscope
  pyroscope:
    endpoint: http://pyroscope:4040
    tenant_id: ${TENANT_ID}
```

---

## 5. Extensions高级配置

### 5.1 Health Check Extension

```yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    # v0.117.0: 增强的健康检查
    path: /health
    
    # 详细的健康检查端点
    check_collector_pipeline:
      enabled: true
      interval: 5m
      exporter_failure_threshold: 5
    
    # 自定义健康检查
    include_metadata: true
```

### 5.2 PProf Extension

```yaml
extensions:
  pprof:
    endpoint: 0.0.0.0:1777
    # v0.117.0: 增强的分析选项
    block_profile_fraction: 0
    mutex_profile_fraction: 0
    save_to_file: ""  # 可配置保存到文件路径
```

### 5.3 zPages Extension

```yaml
extensions:
  zpages:
    endpoint: 0.0.0.0:55679
    # v0.117.0: 更多zPages
    # /debug/tracez - 采样追踪
    # /debug/rpcz - RPC统计
    # /debug/pipelinez - 流水线状态
    # /debug/featurez - 特性标志
```

### 5.4 File Storage Extension (持久化)

```yaml
extensions:
  file_storage:
    directory: /var/lib/otel/storage
    timeout: 1s
    # v0.117.0: 增强的存储配置
    compaction:
      enabled: true
      interval: 5m
      threshold: 10000
```

### 5.5 OIDC Authentication

```yaml
extensions:
  oidc:
    issuer_url: https://auth.example.com
    audience: otel-collector
    # v0.117.0: 增强的OIDC
    username_claim: email
    groups_claim: groups
    # 本地验证缓存
    local_jwks:
      path: /etc/otel/jwks.json
      refresh_interval: 1h
```

---

## 6. 多租户架构配置

### 6.1 基于Pipeline的多租户

```yaml
# 多租户Collector配置示例
receivers:
  # 租户A的接收端点
  otlp/tenant-a:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        include_metadata: true
      http:
        endpoint: 0.0.0.0:4318
        include_metadata: true
  
  # 租户B的接收端点
  otlp/tenant-b:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4327
        include_metadata: true
      http:
        endpoint: 0.0.0.0:4328
        include_metadata: true

processors:
  # 租户A的资源处理
  resource/tenant-a:
    attributes:
      - key: tenant.id
        value: tenant-a
        action: upsert
      - key: tenant.tier
        value: premium
        action: upsert
  
  # 租户B的资源处理
  resource/tenant-b:
    attributes:
      - key: tenant.id
        value: tenant-b
        action: upsert
      - key: tenant.tier
        value: standard
        action: upsert
  
  # 租户A的专用采样
  probabilistic_sampler/tenant-a:
    sampling_percentage: 10.0
  
  # 租户B的专用采样(更高采样率)
  probabilistic_sampler/tenant-b:
    sampling_percentage: 50.0
  
  # 租户专用的批处理
  batch/tenant-a:
    timeout: 1s
    send_batch_size: 1024
  
  batch/tenant-b:
    timeout: 2s
    send_batch_size: 2048

exporters:
  # 租户A的后端
  otlp/tenant-a-backend:
    endpoint: backend-a:4317
    headers:
      x-tenant-id: tenant-a
  
  # 租户B的后端
  otlp/tenant-b-backend:
    endpoint: backend-b:4317
    headers:
      x-tenant-id: tenant-b

service:
  pipelines:
    # 租户A的Traces流水线
    traces/tenant-a:
      receivers: [otlp/tenant-a]
      processors: [resource/tenant-a, probabilistic_sampler/tenant-a, batch/tenant-a]
      exporters: [otlp/tenant-a-backend]
    
    # 租户B的Traces流水线
    traces/tenant-b:
      receivers: [otlp/tenant-b]
      processors: [resource/tenant-b, probabilistic_sampler/tenant-b, batch/tenant-b]
      exporters: [otlp/tenant-b-backend]
    
    # Metrics和Logs同理
```

### 6.2 基于路由的多租户 (v0.117.0推荐)

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        include_metadata: true
      http:
        endpoint: 0.0.0.0:4318
        include_metadata: true

processors:
  # 使用routing processor进行租户隔离
  routing:
    # 从metadata提取tenant_id
    attribute_source: metadata
    from_attribute: x-tenant-id
    
    # 默认目标
    default_exporters: [otlp/default]
    
    # 路由表
    table:
      - value: tenant-a
        exporters: [otlp/tenant-a]
      - value: tenant-b
        exporters: [otlp/tenant-b]
      - value: tenant-c
        exporters: [otlp/tenant-c]
  
  # v0.117.0: 增强的groupbyattrs处理器
  groupbyattrs/tenant:
    keys:
      - tenant.id
      - service.name
    
    # 按租户分组处理
    grouping: strict

exporters:
  otlp/tenant-a:
    endpoint: backend-a:4317
  
  otlp/tenant-b:
    endpoint: backend-b:4317
  
  otlp/tenant-c:
    endpoint: backend-c:4317
  
  otlp/default:
    endpoint: default-backend:4317
```

### 6.3 资源隔离与限制

```yaml
processors:
  # 内存限制 - 每租户
  memory_limiter/tenant-a:
    limit_mib: 512
    spike_limit_mib: 128
  
  memory_limiter/tenant-b:
    limit_mib: 1024
    spike_limit_mib: 256
  
  # 基于属性的过滤 - 限制高基数
  filter/tenant-a:
    metrics:
      metric:
        - 'type == METRIC_DATA_TYPE_HISTOGRAM and name matches "http.*"'
    logs:
      log_record:
        - 'severity_number < SEVERITY_NUMBER_WARN'
  
  # v0.117.0: 资源配额处理器
  resourcequota:
    enabled: true
    limits:
      - tenant: tenant-a
        max_spans_per_second: 1000
        max_metrics_per_second: 5000
        max_logs_per_second: 10000
      - tenant: tenant-b
        max_spans_per_second: 500
        max_metrics_per_second: 2500
        max_logs_per_second: 5000
```

---

## 7. 性能调优指南

### 7.1 批处理优化

```yaml
processors:
  batch:
    # 关键参数调优
    timeout: 200ms  # 降低延迟，但增加请求数
    send_batch_size: 8192  # 增加批大小，提高吞吐量
    send_batch_max_size: 10240  # 防止超大请求
    
    # v0.117.0: 动态批处理
    dynamic_batching:
      enabled: true
      target_latency: 50ms
      min_batch_size: 512
      max_batch_size: 16384
```

### 7.2 并发优化

```yaml
exporters:
  otlp:
    endpoint: backend:4317
    # 增加并发消费者
    sending_queue:
      num_consumers: 20  # 默认10，根据CPU核心调整
      queue_size: 10000
    
    # 连接池配置
    # v0.117.0: 更细粒度的连接控制
    keepalive:
      enabled: true
      time: 30s
      timeout: 10s
      permit_without_stream: true
```

### 7.3 内存优化

```yaml
processors:
  memory_limiter:
    # 设置合理的内存限制
    limit_mib: 4000  # 容器限制的80%
    spike_limit_mib: 800
    
    # v0.117.0: 自适应内存管理
    memory_management:
      strategy: adaptive
      adaptive:
        target_utilization: 75
        evaluation_period: 10s
```

### 7.4 CPU优化

```yaml
service:
  telemetry:
    metrics:
      level: normal
      # 禁用不必要的自监控
      address: 0.0.0.0:8888
  
  # v0.117.0: GOMAXPROCS自动检测
  # 自动设置runtime.GOMAXPROCS以匹配容器CPU限制
```

---

## 8. 高可用配置

### 8.1 负载均衡配置

```yaml
exporters:
  # 使用负载均衡导出器
  loadbalancing:
    # 后端解析器
    resolver:
      dns:
        hostname: otel-collector-headless
        port: 4317
      # 或 Kubernetes端点
      k8s:
        service: otel-collector
        namespace: observability
        port: 4317
    
    # 路由策略
    routing_key: traceID  # traceID / service / metric
    
    # 健康检查
    health_check:
      enabled: true
      interval: 5s
      timeout: 3s
    
    # v0.117.0: 故障转移
    failover:
      enabled: true
      max_retries: 3
      backup_exporters: [otlp/backup]
```

### 8.2 故障转移配置

```yaml
exporters:
  # 主要后端
  otlp/primary:
    endpoint: primary-backend:4317
    retry_on_failure:
      enabled: true
      max_elapsed_time: 60s
    sending_queue:
      queue_size: 10000
  
  # 备份后端
  otlp/backup:
    endpoint: backup-backend:4317
    retry_on_failure:
      enabled: true
      max_elapsed_time: 300s
    sending_queue:
      queue_size: 50000  # 更大的队列
      persistent_storage:
        enabled: true
        directory: /var/lib/otel/backup-queue
  
  # 灾难恢复 - 对象存储
  awss3/dr:
    region: us-west-2
    s3uploader:
      s3_bucket: otel-dr
      s3_prefix: emergency/

processors:
  # 复制处理器 - 同时发送到多个后端
  replicate:
    exporters:
      - otlp/primary
      - otlp/backup
```

### 8.3 Kubernetes高可用部署

```yaml
# StatefulSet配置
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: otel-collector
spec:
  serviceName: otel-collector-headless
  replicas: 3
  
  template:
    spec:
      containers:
        - name: otel-collector
          image: otel/opentelemetry-collector-contrib:0.117.0
          resources:
            requests:
              memory: "2Gi"
              cpu: "1000m"
            limits:
              memory: "4Gi"
              cpu: "2000m"
          env:
            # v0.117.0: 自动资源检测
            - name: OTEL_RESOURCE_ATTRIBUTES
              value: "k8s.pod.name=$(POD_NAME),k8s.node.name=$(NODE_NAME)"
          volumeMounts:
            - name: config
              mountPath: /etc/otel
            - name: queue-storage
              mountPath: /var/lib/otel/queue
      
      # 反亲和性 - 分布在不同节点
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
            - weight: 100
              podAffinityTerm:
                labelSelector:
                  matchExpressions:
                    - key: app
                      operator: In
                      values:
                        - otel-collector
                topologyKey: kubernetes.io/hostname
```

---

## 9. 安全配置

### 9.1 TLS全面配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          client_ca_file: /etc/otel/certs/ca.crt
          client_auth_type: require_and_verify_client_cert
          # v0.117.0: 增强的TLS配置
          min_version: "1.3"  # 强制TLS 1.3
          cipher_suites: [
            TLS_AES_256_GCM_SHA384,
            TLS_CHACHA20_POLY1305_SHA256
          ]

exporters:
  otlp:
    tls:
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      ca_file: /etc/otel/certs/ca.crt
      insecure_skip_verify: false
```

### 9.2 认证配置

```yaml
extensions:
  # Basic Auth
  basicauth:
    client_auth:
      username: ${USERNAME}
      password: ${PASSWORD}
  
  # Bearer Token
  bearertokenauth:
    token: ${BEARER_TOKEN}
  
  # OIDC
  oidc:
    issuer_url: https://auth.example.com
    audience: otel-collector
    # v0.117.0: 支持多个issuer
    issuer_urls: 
      - https://auth1.example.com
      - https://auth2.example.com
  
  # mTLS
  mtls:
    cert_file: /etc/otel/certs/server.crt
    key_file: /etc/otel/certs/server.key

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: oidc
```

### 9.3 数据脱敏

```yaml
processors:
  # 属性脱敏
  attributes:
    actions:
      # 删除敏感头
      - key: http.request.header.authorization
        action: delete
      - key: http.request.header.cookie
        action: delete
      - key: db.statement
        action: hash  # 哈希化而非删除，保留查询模式分析
      
      # 掩码处理
      - key: user.email
        action: mask
        mask_pattern: "(^.).*(@.*$)"
        mask_replacement: "$1***$2"
  
  # v0.117.0: 敏感数据检测器
  sensivedata:
    detectors:
      - credit_card
      - ssn
      - email
      - phone
    action: mask
    
    # 自定义检测规则
    custom_rules:
      - name: api_key
        pattern: "sk-[a-zA-Z0-9]{48}"
        action: hash
```

---

## 10. 监控与可观测性

### 10.1 自监控配置

```yaml
service:
  telemetry:
    # 指标
    metrics:
      level: detailed  # none / basic / normal / detailed
      address: 0.0.0.0:8888
      # v0.117.0: 自定义标签
      resource:
        service.name: otel-collector
        deployment.environment: production
    
    # 日志
    logs:
      level: info  # debug / info / warn / error
      development: false
      sampling:
        initial: 2
        thereafter: 500
      output_paths: [stdout]
      error_output_paths: [stderr]
    
    # v0.117.0: 追踪
    traces:
      # Collector自身的分布式追踪
      processors:
        - batch:
            timeout: 1s
            send_batch_size: 1024
      exporters:
        - otlp:
            endpoint: localhost:4317
            insecure: true

extensions:
  # Prometheus自监控端点
  prometheus:
    endpoint: 0.0.0.0:9090
    # v0.117.0: 额外的 Collector 指标
    metric_expiration: 5m
  
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
  
  # pprof分析
  pprof:
    endpoint: 0.0.0.0:1777
```

### 10.2 关键监控指标

```yaml
# Prometheus抓取配置示例
scrape_configs:
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
    metrics_path: /metrics
    
    # 关键指标
    metric_relabel_configs:
      # 保留重要指标
      - source_labels: [__name__]
        regex: 'otelcol_(receiver|processor|exporter)_.*'
        action: keep
      
      - source_labels: [__name__]
        regex: 'otelcol_process_(memory|cpu|uptime).*'
        action: keep
      
      - source_labels: [__name__]
        regex: 'otelcol_queue_.*'
        action: keep
```

### 10.3 告警规则

```yaml
# 关键告警规则
groups:
  - name: otel-collector
    rules:
      # 导出失败率高
      - alert: OTLPExporterHighFailureRate
        expr: |
          sum(rate(otelcol_exporter_send_failed_spans[5m])) 
          / 
          sum(rate(otelcol_exporter_sent_spans[5m])) > 0.1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "OTLP导出失败率超过10%"
      
      # 队列接近满载
      - alert: OTLPQueueNearCapacity
        expr: |
          otelcol_queue_capacity - otelcol_queue_size < 1000
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "Collector队列接近满载"
      
      # 内存使用高
      - alert: OTLPHighMemoryUsage
        expr: |
          otelcol_process_memory_rss / otelcol_process_memory_limit > 0.9
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Collector内存使用率超过90%"
      
      # 接收速率下降
      - alert: OTLPReceiverRateDrop
        expr: |
          sum(rate(otelcol_receiver_accepted_spans[5m])) 
          < 
          0.5 * avg_over_time(sum(rate(otelcol_receiver_accepted_spans[5m]))[1h])
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "接收速率显著下降"
```

---

## 附录

### A. 完整生产配置示例

```yaml
# 生产环境推荐的完整配置
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  
  pprof:
    endpoint: 0.0.0.0:1777
  
  zpages:
    endpoint: 0.0.0.0:55679
  
  memory_ballast:
    size_mib: 512

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 64
      http:
        endpoint: 0.0.0.0:4318

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 1500
    spike_limit_mib: 256
  
  resource:
    attributes:
      - key: collector.hostname
        from_attribute: host.name
        action: upsert
  
  batch:
    timeout: 1s
    send_batch_size: 8192
    send_batch_max_size: 10240

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      ca_file: /etc/otel/certs/ca.crt
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000

service:
  extensions: [health_check, pprof, zpages, memory_ballast]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp]
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp]
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp]
  
  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888
    logs:
      level: info
```

### B. 配置验证命令

```bash
# 验证配置文件
otelcol-contrib validate --config=file:/etc/otel/config.yaml

# 检查组件
otelcol-contrib components

# 查看配置详情
otelcol-contrib --config=file:/etc/otel/config.yaml --dry-run
```

---

**文档维护**: OTLP项目团队  
**最后更新**: 2026-03-17 (Collector v0.117.0)
