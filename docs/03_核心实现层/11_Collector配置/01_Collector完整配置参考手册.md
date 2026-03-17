---
title: Collector完整配置参考手册
description: OpenTelemetry Collector完整配置参考，包含所有Receiver、Processor、Exporter详细配置
version: OTLP v1.10.0
collector_version: v0.147.0
date: 2026-03-17
category: 核心实现
tags:
  - collector
  - configuration
  - receiver
  - processor
  - exporter
status: published
---

# Collector完整配置参考手册

> **Collector版本**: v0.147.0  
> **配置格式**: YAML  
> **最后更新**: 2026-03-17  

---

## 1. 配置文件结构

```yaml
# Collector配置文件结构

receivers:      # 数据接收器
  # Receiver配置

processors:     # 数据处理器
  # Processor配置

exporters:      # 数据导出器
  # Exporter配置

extensions:     # 扩展组件
  # Extension配置

connectors:     # 连接器 (v0.147.0+)
  # Connector配置

service:        # 服务配置
  pipelines:    # 数据处理管道
  telemetry:    # 遥测配置
  extensions:   # 启用的扩展
```

---

## 2. Receivers 完整配置

### 2.1 OTLP Receiver

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 64
        max_concurrent_streams: 100
        read_buffer_size: 512 KiB
        write_buffer_size: 512 KiB
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          client_ca_file: /etc/otel/certs/ca.crt
          client_auth: require
      
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins: ["*"]
          allowed_headers: ["*"]
          max_age: 7200
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
        keepalive:
          server_parameters:
            max_connection_idle: 10s
            max_connection_age: 30s
            max_connection_age_grace: 5s
          enforcement_policy:
            min_time: 5s
            permit_without_stream: true
        
        # HTTP特定配置
        include_metadata: true
        response_headers:
          X-Custom-Header: "value"
```

### 2.2 Prometheus Receiver

```yaml
receivers:
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
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
              action: replace
              target_label: __metrics_path__
              regex: (.+)
          metric_relabel_configs:
            - source_labels: [__name__]
              regex: 'go_memstats.*'
              action: drop
      
      # 全局配置
      global:
        scrape_interval: 15s
        scrape_timeout: 10s
        evaluation_interval: 15s
      
      # 规则文件
      rule_files:
        - /etc/otel/rules/*.yml
      
      # 告警配置
      alerting:
        alertmanagers:
          - static_configs:
              - targets: ['alertmanager:9093']
    
    # Receiver特定配置
    use_start_time_metric: true
    start_time_metric_regex: "^(.+_)*process_start_time_seconds$"
    report_scrape_error: true
```

### 2.3 Kafka Receiver

```yaml
receivers:
  kafka:
    # Broker配置
    brokers:
      - kafka-0:9092
      - kafka-1:9092
      - kafka-2:9092
    
    # Topic配置
    topic: otlp-metrics
    encoding: otlp_proto     # otlp_proto, otlp_json, zipkin_proto, zipkin_json, jaeger_proto, jaeger_json
    
    # 消费组配置
    group_id: otel-collector
    client_id: otel-collector-1
    
    # 认证配置
    auth:
      plain_text:
        username: ${KAFKA_USERNAME}
        password: ${KAFKA_PASSWORD}
      # 或 SASL
      sasl:
        username: ${KAFKA_USERNAME}
        password: ${KAFKA_PASSWORD}
        mechanism: SCRAM-SHA-512
      # 或 TLS
      tls:
        ca_file: /etc/otel/certs/kafka-ca.crt
        cert_file: /etc/otel/certs/kafka-client.crt
        key_file: /etc/otel/certs/kafka-client.key
    
    # 消费者配置
    session_timeout: 10s
    heartbeat_interval: 3s
    min_fetch_size: 1
    default_fetch_min_bytes: 1
    fetch_max_bytes: 52428800
    fetch_default_max_bytes: 1048576
    max_poll_records: 500
    
    # 消息处理
    message_mark_after: 0    # 0 = 立即标记
    header_extraction:
      extract_headers: true
      headers:
        - x-tenant-id
        - x-request-id
```

### 2.4 Filelog Receiver

```yaml
receivers:
  filelog:
    # 文件路径 (支持通配符)
    include:
      - /var/log/*.log
      - /var/log/myapp/*.log
    exclude:
      - /var/log/secure*.log
      - "*.gz"
    
    # 多行日志处理
    multiline:
      line_start_pattern: '^\['    # 以[开头的行是新日志
      
    # 解析配置
    operators:
      # 解析JSON日志
      - type: json_parser
        timestamp:
          parse_from: attributes.time
          layout: '%Y-%m-%d %H:%M:%S'
        severity:
          parse_from: attributes.level
          mapping:
            debug: DEBUG
            info: INFO
            warn: WARN
            error: ERROR
      
      # 添加资源属性
      - type: add
        field: resource.service.name
        value: my-application
      
      # 删除原始时间字段
      - type: remove
        field: attributes.time
      
      # 正则提取
      - type: regex_parser
        regex: '^(?P<ip>\d+\.\d+\.\d+\.\d+) - (?P<user>\S+)'
        parse_from: body
      
      # 时间戳解析
      - type: time_parser
        parse_from: attributes.timestamp
        layout: '%Y-%m-%dT%H:%M:%S.%fZ'
      
      # 严重级别解析
      - type: severity_parser
        parse_from: attributes.level
        preset: default
    
    # 文件轮转处理
    force_flush_period: 5s
    encoding: utf-8
    fingerprint_size: 1KB
    max_log_size: 1MiB
    max_concurrent_files: 1024
```

---

## 3. Processors 完整配置

### 3.1 Batch Processor

```yaml
processors:
  batch:
    # 时间触发
    timeout: 1s
    
    # 大小触发
    send_batch_size: 1024        # spans/metrics/logs
    send_batch_max_size: 2048    # 硬性上限
    
    # 元数据键 (多租户)
    metadata_keys:
      - tenant.id
      - service.name
    
    # 优化配置
    send_batch_max_size_bytes: 0  # 0 = 无限制
```

### 3.2 Memory Limiter

```yaml
processors:
  memory_limiter:
    # 检查间隔
    check_interval: 1s
    
    # 内存限制 (Mib)
    limit_mib: 1500
    
    # 尖峰限制
    spike_limit_mib: 300
    
    # 百分比限制 (与limit_mib取较小值)
    limit_percentage: 75
    spike_limit_percentage: 15
```

### 3.3 Tail Sampling Processor

```yaml
processors:
  tail_sampling:
    # 决策等待时间
    decision_wait: 10s
    
    # 追踪数限制
    num_traces: 100000
    expected_new_traces_per_sec: 1000
    
    # 策略配置
    policies:
      # 策略1: 状态码采样
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 策略2: 延迟采样
      - name: slow_requests
        type: latency
        latency:
          threshold_ms: 1000
      
      # 策略3: 概率采样
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 5
          hash_seed: 22
      
      # 策略4: 字符串属性匹配
      - name: critical_services
        type: string_attribute
        string_attribute:
          key: service.name
          values:
            - payment-service
            - auth-service
          enabled_regex_matching: false
          invert_match: false
      
      # 策略5: 数值属性匹配
      - name: high_value_orders
        type: numeric_attribute
        numeric_attribute:
          key: order.value
          min_value: 1000
      
      # 策略6: 速率限制
      - name: rate_limit
        type: rate_limiting
        rate_limiting:
          rate: 100
          spike_size: 100
      
      # 策略7: 跨度数
      - name: large_traces
        type: span_count
        span_count:
          min_spans: 10
      
      # 策略8: 布尔属性
      - name: trace_critical
        type: boolean_attribute
        boolean_attribute:
          key: trace.critical
          value: true
      
      # 策略9: 复合策略 (OR)
      - name: composite
        type: composite
        composite:
          max_total_spans_per_second: 1000
          policy_order:
            - errors
            - slow_requests
            - probabilistic
      
      # 策略10:  always_sample
      - name: always
        type: always_sample
```

### 3.4 Attributes Processor

```yaml
processors:
  attributes:
    actions:
      # 插入
      - key: environment
        value: production
        action: insert      # 仅在不存在时插入
      
      # 更新
      - key: service.version
        value: 2.0.0
        action: update      # 仅更新已存在的
      
      # 不存在则插入
      - key: host.id
        from_attribute: host.name
        action: upsert      # insert或update
      
      # 删除
      - key: http.request.header.authorization
        action: delete
      
      # 哈希
      - key: user.id
        action: hash        # SHA-256哈希
      
      # 提取
      - key: http.url
        pattern: ^https?://(?P<http_target>.*)$
        action: extract
      
      # 转换大小写
      - key: http.method
        action: convert
        converted_type: upper_case
      
      # 正则替换
      - key: http.url
        pattern: /users/\d+
        replacement: /users/{id}
        action: replace
      
      # 从另一个属性复制
      - key: service.instance.id
        from_attribute: host.name
        action: upsert
    
    # 包含/排除过滤
    include:
      match_type: strict
      services:
        - my-service
    
    exclude:
      match_type: regexp
      log_bodies:
        - "health.*"
```

### 3.5 Resource Processor

```yaml
processors:
  resource:
    # 属性操作
    attributes:
      - key: environment
        value: production
        action: upsert
      
      - key: datacenter
        from_attribute: host.zone
        action: upsert
      
      - key: host.ip
        action: delete
    
    # 标签（已废弃，使用attributes）
    labels:
      team: backend
      project: payments
```

### 3.6 Filter Processor

```yaml
processors:
  filter:
    error_mode: ignore    # ignore, propagate
    
    traces:
      span:
        - 'attributes["http.url"] == "/health"'
        - 'attributes["http.url"] == "/metrics"'
        - 'attributes["http.route"] == "/favicon.ico"'
        - 'IsMatch(name, "health.*")'
      
      # 从Resource过滤
      resource:
        - 'attributes["service.name"] == "load-generator"'
    
    metrics:
      # 指标名称匹配
      metric:
        - 'type == METRIC_DATA_TYPE_GAUGE'
        - 'IsMatch(name, "go_memstats.*")'
      
      # 数据点过滤
      datapoint:
        - 'attributes["state"] == "idle"'
    
    logs:
      log_record:
        - 'severity_number < SEVERITY_NUMBER_WARN'
        - 'IsMatch(body, "debug.*")'
```

### 3.7 Transform Processor

```yaml
processors:
  transform:
    error_mode: ignore
    
    trace_statements:
      # Span名称修改
      - context: span
        statements:
          - set(name, Concat([attributes["http.method"], attributes["http.route"]], " "))
      
      # 状态码设置
      - context: span
        statements:
          - set(status.code, 1) where attributes["http.status_code"] < 500
          - set(status.code, 2) where attributes["http.status_code"] >= 500
      
      # 属性计算
      - context: span
        statements:
          - set(attributes["duration_ms"], duration / 1000000)
      
      # 条件设置
      - context: span
        statements:
          - set(attributes["error"], true) where status.code == 2
    
    metric_statements:
      # 指标名称修改
      - context: metric
        statements:
          - set(name, "new_" + name)
      
      # 标签操作
      - context: datapoint
        statements:
          - set(attributes["env"], "prod")
          - delete_key(attributes, "temp_label")
    
    log_statements:
      # 日志内容修改
      - context: log
        statements:
          - set(body, ConvertCase(body, "upper"))
          - set(severity_text, "WARN") where severity_number == 13
```

### 3.8 新增处理器 (v0.147.0)

```yaml
# Isolation Forest异常检测
processors:
  isolationforest:
    max_samples: 1000
    max_features: 3
    n_estimators: 100
    contamination: 0.01
    threshold: 0.6
    feature_keys:
      - http_request_duration
      - cpu_usage
    anomaly_attribute: "is_anomaly"

# Interval指标聚合
processors:
  interval:
    interval: 60s
    aggregations:
      - metric_name: http_request_duration
        aggregation: p99
      - metric_name: cpu_usage
        aggregation: avg

# Log去重
processors:
  logdedup:
    interval: 30s
    log_identity_attributes:
      - body
      - severity_number
```

---

## 4. Exporters 完整配置

### 4.1 OTLP Exporter

```yaml
exporters:
  otlp:
    endpoint: backend:4317
    
    # TLS配置
    tls:
      insecure: false
      ca_file: /etc/otel/certs/ca.crt
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      insecure_skip_verify: false
      server_name_override: backend.example.com
    
    # 超时和重试
    timeout: 10s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    
    # 发送队列
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
      storage: file_storage    # 使用扩展存储
    
    # 压缩
    compression: gzip    # gzip, snappy, zstd, none
    
    # 负载均衡
    load_balancing:
      resolver:
        static:
          hostnames:
            - backend-1:4317
            - backend-2:4317
      
    # 元数据
    headers:
      x-api-key: ${API_KEY}
      x-tenant-id: ${TENANT_ID}
```

### 4.2 Prometheus Remote Write Exporter

```yaml
exporters:
  prometheusremotewrite:
    endpoint: https://prometheus/api/v1/write
    
    # 认证
    auth:
      authenticator: basicauth/client
    
    # TLS
    tls:
      insecure_skip_verify: false
    
    # 超时和重试
    timeout: 30s
    retry_on_failure:
      enabled: true
    
    # 队列
    sending_queue:
      enabled: true
      num_consumers: 5
      queue_size: 1000
    
    # 外部标签
    external_labels:
      cluster: production
      replica: ${POD_NAME}
    
    # 指标转换
    add_metric_suffixes: true
    metric_expiration: 5m
    resource_to_telemetry_conversion:
      enabled: true
```

### 4.3 Elasticsearch Exporter

```yaml
exporters:
  elasticsearch:
    endpoints:
      - https://elasticsearch:9200
    
    # 认证
    user: ${ES_USER}
    password: ${ES_PASSWORD}
    
    # TLS
    tls:
      ca_file: /etc/otel/certs/es-ca.crt
    
    # 索引配置
    logs_index: otel-logs
    traces_index: otel-traces
    
    # 索引生命周期
    index:
      prefix: otel
      date_format: yyyy.MM.dd
      
    # 批量配置
    bulk:
      size: 5MB
      workers: 2
      flush:
        bytes: 5MB
        interval: 30s
    
    # 字段映射
    mapping:
      mode: ecs    # ecs, otel, raw
```

### 4.4 Kafka Exporter

```yaml
exporters:
  kafka:
    brokers:
      - kafka-0:9092
      - kafka-1:9092
    
    # Topic配置
    topic: otlp-traces
    encoding: otlp_proto
    
    # 认证
    auth:
      tls:
        ca_file: /etc/otel/certs/kafka-ca.crt
        cert_file: /etc/otel/certs/client.crt
        key_file: /etc/otel/certs/client.key
    
    # 生产者配置
    producer:
      max_message_bytes: 1000000
      required_acks: 1
      compression: snappy
    
    # 元数据
    metadata:
      full: false
      retry:
        max: 3
        backoff: 250ms
    
    # 分区
    partition_traces_by_id: true
    partition_metrics_by_resource_attributes:
      - service.name
```

### 4.5 File Exporter

```yaml
exporters:
  file:
    path: /var/log/otel/output.json
    
    # 轮转
    rotation:
      max_megabytes: 10
      max_days: 7
      max_backups: 3
      localtime: true
      compress: true
    
    # 格式
    format: json    # json, proto
    
    # 追加或覆盖
    append: true
    
    # 压缩
    compression: zstd
    
    # 异步
    async: true
    queue_size: 1000
```

---

## 5. Extensions 配置

```yaml
extensions:
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
    response_body: {"status": "healthy"}
    check_collector_pipeline:
      enabled: true
      interval: 5m
      exporter_failure_threshold: 5
  
  # pprof性能分析
  pprof:
    endpoint: localhost:1777
    block_profile_fraction: 0
    mutex_profile_fraction: 0
    save_to_file: ""
  
  # zpages调试
  zpages:
    endpoint: localhost:55679
  
  # 内存性能分析
  memory_ballast:
    size_mib: 512
  
  # 文件存储
  file_storage:
    directory: /var/lib/otel/storage
    timeout: 1s
    compaction:
      on_rebound: true
      rebound_needed_threshold_mib: 100
      rebound_trigger_threshold_mib: 10
      check_interval: 5s
  
  # 基本认证
  basicauth/server:
    htpasswd:
      file: /etc/otel/htpasswd
      inline: |
        admin:$apr1$h30.../
  
  # OAuth2
  oauth2client:
    client_id: ${OAUTH_CLIENT_ID}
    client_secret: ${OAUTH_CLIENT_SECRET}
    token_url: https://auth.example.com/oauth2/token
    scopes: ["telemetry.write"]
    timeout: 10s
  
  # OIDC
  oidc:
    issuer_url: https://auth.example.com
    audience: otel-collector
    username_claim: email
```

---

## 6. Service 配置

```yaml
service:
  # 遥测配置
  telemetry:
    logs:
      level: info    # debug, info, warn, error
      development: false
      sampling:
        initial: 2
        thereafter: 500
      output_paths: [stdout]
      error_output_paths: [stderr]
    
    metrics:
      level: detailed    # none, basic, normal, detailed
      readers:
        - pull:
            exporter:
              prometheus:
                host: localhost
                port: 8888
        - push:
            exporter:
              otlp:
                protocol: http/protobuf
                endpoint: https://metrics-backend:4318
    
    traces:
      processors:
        - batch:
            exporter:
              otlp:
                protocol: grpc
                endpoint: localhost:4317
  
  # 启用的扩展
  extensions:
    - health_check
    - pprof
    - zpages
    - file_storage
  
  # 数据处理管道
  pipelines:
    traces:
      receivers: [otlp, jaeger, zipkin]
      processors: [memory_limiter, batch]
      exporters: [otlp, zipkin]
    
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, batch]
      exporters: [otlp, prometheusremotewrite]
    
    logs:
      receivers: [otlp, filelog]
      processors: [memory_limiter, batch]
      exporters: [otlp, elasticsearch]
    
    traces/tenant-a:
      receivers: [otlp/tenant-a]
      processors: [memory_limiter, resource/tenant-a, batch]
      exporters: [otlp/tenant-a-backend]
  
  # 管道错误处理
  pipelines_error:
    error_mode: ignore
```

---

## 7. 完整生产配置示例

```yaml
# 生产环境Collector配置

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 64
        tls:
          cert_file: /etc/otel/certs/tls.crt
          key_file: /etc/otel/certs/tls.key
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins: ["*"]

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 1500
    spike_limit_mib: 300
  
  resource:
    attributes:
      - key: environment
        value: production
        action: upsert
  
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 1000
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: slow
        type: latency
        latency: {threshold_ms: 1000}
      - name: probabilistic
        type: probabilistic
        probabilistic: {sampling_percentage: 5}

exporters:
  otlp:
    endpoint: ${OTLP_BACKEND}
    tls:
      insecure: false
      ca_file: /etc/otel/certs/ca.crt
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
    retry_on_failure:
      enabled: true
      max_elapsed_time: 300s

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  memory_ballast:
    size_mib: 512

service:
  extensions: [health_check, memory_ballast]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, tail_sampling, batch]
      exporters: [otlp]
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp]
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp]
```

---

**最后更新**: 2026-03-17  
**维护者**: OTLP核心实现团队  
**状态**: Production Ready
