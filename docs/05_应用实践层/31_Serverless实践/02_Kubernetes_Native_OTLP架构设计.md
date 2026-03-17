---
title: Kubernetes Native OTLP架构设计
description: 在Kubernetes环境中设计和部署OpenTelemetry的高可用、可扩展架构，包括Operator、Sidecar、DaemonSet等多种部署模式
category: 应用实践
tags:
  - kubernetes
  - otel-operator
  - sidecar
  - daemonset
  - deployment
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# Kubernetes Native OTLP架构设计

> **适用场景**: Kubernetes集群可观测性
> **部署复杂度**: ⭐⭐⭐⭐ (高级)
> **最后更新**: 2026-03-17

---

## 1. 架构设计原则

### 1.1 Kubernetes可观测性挑战

```
传统架构                  Kubernetes架构
─────────────────        ─────────────────
固定主机                 动态Pod
静态配置                 自动扩缩容
单点采集                 分布式追踪
长期运行                 短生命周期

K8s特有挑战:
├── Pod生命周期短暂
├── 网络拓扑动态变化
├── 多租户隔离需求
├── 大规模集群管理
└── 资源限制与配额
```

### 1.2 设计目标

| 目标 | 描述 | 实现方式 |
|------|------|----------|
| 自动发现 | 自动识别新Pod和服务 | Operator + Admission Webhook |
| 最小侵入 | 无需修改应用代码 | Sidecar自动注入 |
| 高可用 | 采集路径无单点 | DaemonSet + Deployment冗余 |
| 可扩展 | 随集群规模自动扩展 | HPA + 分片采集 |
| 多租户 | 支持命名空间隔离 | RBAC + 独立Pipeline |

---

## 2. 部署架构模式

### 2.1 模式对比

```
┌─────────────────────────────────────────────────────────────┐
│                    部署架构模式对比                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  模式1: DaemonSet Collector                                 │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Node 1         Node 2         Node 3                │   │
│  │ ┌─────────┐   ┌─────────┐   ┌─────────┐            │   │
│  │ │App Pod  │   │App Pod  │   │App Pod  │            │   │
│  │ │App Pod  │   │App Pod  │   │App Pod  │            │   │
│  │ └────┬────┘   └────┬────┘   └────┬────┘            │   │
│  │      │             │             │                  │   │
│  │ ┌────▼────┐   ┌────▼────┐   ┌────▼────┐            │   │
│  │ │Collector│   │Collector│   │Collector│            │   │
│  │ │DaemonSet│   │DaemonSet│   │DaemonSet│            │   │
│  │ └────┬────┘   └────┬────┘   └────┬────┘            │   │
│  │      └─────────────┴─────────────┘                  │   │
│  │                    │                                 │   │
│  │              ┌─────▼─────┐                          │   │
│  │              │  Backend  │                          │   │
│  │              └───────────┘                          │   │
│  └─────────────────────────────────────────────────────┘   │
│  ✅ 优点: 资源高效、本地采集、无网络跳转                      │
│  ❌ 缺点: 节点级隔离差、升级复杂                            │
│                                                             │
│  模式2: Sidecar注入                                        │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Pod 1                              Pod 2            │   │
│  │ ┌───────────────┐                 ┌───────────────┐ │   │
│  │ │ ┌───┐ ┌───┐  │                 │ ┌───┐ ┌───┐  │ │   │
│  │ │ │App│ │Col│  │                 │ │App│ │Col│  │ │   │
│  │ │ └───┘ └───┘  │                 │ └───┘ └───┘  │ │   │
│  │ │      │       │                 │      │       │ │   │
│  │ └──────┼───────┘                 └──────┼───────┘ │   │
│  │         └────────────────────────────────┘         │   │
│  │                      │                             │   │
│  │                 ┌────▼─────┐                       │   │
│  │                 │ Backend  │                       │   │
│  │                 └──────────┘                       │   │
│  └─────────────────────────────────────────────────────┘   │
│  ✅ 优点: 应用级隔离、独立配置、生命周期绑定                   │
│  ❌ 缺点: 资源开销高、配置复杂                              │
│                                                             │
│  模式3: Deployment + Service                              │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                                                     │   │
│  │   Pods ────────> Service ───────> Collector        │   │
│  │   (App)          (LB)              (Deployment)     │   │
│  │                                        │            │   │
│  │                              ┌─────────▼────────┐   │   │
│  │                              │ Collector Pods   │   │   │
│  │                              │ (HPA Auto-scale) │   │   │
│  │                              └─────────┬────────┘   │   │
│  │                                        │            │   │
│  │                                   Backend          │   │
│  └─────────────────────────────────────────────────────┘   │
│  ✅ 优点: 集中管理、易于升级、独立扩缩容                       │
│  ❌ 缺点: 网络跳转、可能成为瓶颈                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 混合架构推荐

```yaml
# 推荐的混合架构配置
# 结合三种模式的优点

# 1. DaemonSet用于基础指标采集
daemonset-collector:
  role: node-agent
  receivers:
    - hostmetrics      # 节点级指标
    - filelog          # 节点日志
    - kubeletstats     # Kubelet指标
  processors:
    - memory_limiter
    - batch
  exporters:
    - otlp/deployment  # 发送到中央Collector

# 2. Deployment用于聚合和导出
central-collector:
  role: aggregator
  replicas: 3
  hpa:
    min: 3
    max: 20
    targetCPU: 70%
  processors:
    - memory_limiter
    - batch
    - tail_sampling
    - resource
  exporters:
    - otlp/backend

# 3. Sidecar用于特殊场景
sidecar-injection:
  enabled: true
  namespaces:
    - sensitive-apps   # 高安全要求应用
    - legacy-apps      # 无法修改的遗留应用
```

---

## 3. OpenTelemetry Operator部署

### 3.1 Operator安装

```bash
# 安装Cert Manager (Operator依赖)
kubectl apply -f https://github.com/cert-manager/cert-manager/releases/download/v1.13.0/cert-manager.yaml

# 等待Cert Manager就绪
kubectl wait --for=condition=Available deployment/cert-manager -n cert-manager --timeout=120s

# 安装OpenTelemetry Operator
kubectl apply -f https://github.com/open-telemetry/opentelemetry-operator/releases/download/v0.96.0/opentelemetry-operator.yaml

# 验证安装
kubectl get pods -n opentelemetry-operator-system
```

### 3.2 OpenTelemetry Collector自定义资源

```yaml
# base-collector.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: base-collector
  namespace: observability
spec:
  mode: daemonset
  serviceAccount: otel-collector

  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318

      hostmetrics:
        collection_interval: 30s
        scrapers:
          cpu:
          memory:
          disk:
          load:
          filesystem:
          network:

      kubeletstats:
        collection_interval: 20s
        endpoint: https://${K8S_NODE_NAME}:10250
        auth_type: serviceAccount
        insecure_skip_verify: true
        metric_groups:
          - node
          - pod
          - container

      filelog:
        include:
          - /var/log/pods/*/*/*.log
        exclude:
          - /var/log/pods/*/otel-collector*/*.log
        operators:
          - type: json_parser
            timestamp:
              parse_from: attributes.time
              layout: '%Y-%m-%dT%H:%M:%S.%LZ'
          - type: severity_parser
            parse_from: attributes.level

    processors:
      memory_limiter:
        limit_mib: 800
        spike_limit_mib: 200
        check_interval: 5s

      resource:
        attributes:
          - key: k8s.cluster.name
            value: production
            action: upsert
          - key: k8s.node.name
            from_attribute: k8s.node.name
            action: upsert

      batch:
        timeout: 1s
        send_batch_size: 1024
        send_batch_max_size: 2048

      k8sattributes:
        auth_type: serviceAccount
        passthrough: false
        extract:
          metadata:
            - k8s.namespace.name
            - k8s.deployment.name
            - k8s.statefulset.name
            - k8s.daemonset.name
            - k8s.cronjob.name
            - k8s.job.name
            - k8s.node.name
            - k8s.pod.name
            - k8s.pod.uid
            - k8s.pod.start_time
          labels:
            - tag_name: app.label.component
              key: app.kubernetes.io/component
              from: pod
        pod_association:
          - sources:
              - from: resource_attribute
                name: k8s.pod.ip
          - sources:
              - from: resource_attribute
                name: k8s.pod.uid
          - sources:
              - from: connection

    exporters:
      otlp/central:
        endpoint: central-collector.observability.svc.cluster.local:4317
        tls:
          insecure: true
        sending_queue:
          enabled: true
          num_consumers: 10
          queue_size: 5000
        retry_on_failure:
          enabled: true
          initial_interval: 5s
          max_interval: 30s
          max_elapsed_time: 300s

      debug:
        verbosity: detailed

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp/central]

        metrics:
          receivers: [otlp, hostmetrics, kubeletstats]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp/central]

        logs:
          receivers: [otlp, filelog]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp/central]
```

### 3.3 中央聚合Collector

```yaml
# central-collector.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: central-collector
  namespace: observability
spec:
  mode: deployment
  replicas: 3

  # HPA配置
  autoscaler:
    minReplicas: 3
    maxReplicas: 20
    targetCPUUtilization: 70
    targetMemoryUtilization: 80

  resources:
    requests:
      cpu: "500m"
      memory: "1Gi"
    limits:
      cpu: "2000m"
      memory: "4Gi"

  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
            max_recv_msg_size_mib: 16
          http:
            endpoint: 0.0.0.0:4318

    processors:
      memory_limiter:
        limit_mib: 3000
        spike_limit_mib: 500
        check_interval: 5s

      resource:
        attributes:
          - key: environment
            value: production
            action: upsert
          - key: datacenter
            value: dc-east
            action: upsert

      batch:
        timeout: 2s
        send_batch_size: 2048
        send_batch_max_size: 4096

      # 尾部采样 - 只保留错误和慢请求
      tail_sampling:
        decision_wait: 10s
        num_traces: 100000
        expected_new_traces_per_sec: 10000
        policies:
          - name: errors
            type: status_code
            status_code: {status_codes: [ERROR]}
          - name: slow_requests
            type: latency
            latency: {threshold_ms: 1000}
          - name: probabilistic
            type: probabilistic
            probabilistic: {sampling_percentage: 10}

      # 指标转换
      metricstransform:
        transforms:
          - include: k8s.pod.cpu.usage
            match_type: regexp
            action: update
            operations:
              - action: aggregate_labels
                label_set: [pod, namespace]
                aggregation_type: sum

    exporters:
      otlp/jaeger:
        endpoint: jaeger-collector.monitoring.svc.cluster.local:4317
        tls:
          insecure: true

      prometheusremotewrite:
        endpoint: http://prometheus.monitoring.svc.cluster.local:9090/api/v1/write
        headers:
          X-Scope-OrgID: production

      loki:
        endpoint: http://loki.monitoring.svc.cluster.local:3100/loki/api/v1/push
        labels:
          attributes:
            k8s.namespace.name: "namespace"
            k8s.pod.name: "pod"
            k8s.container.name: "container"

      debug:
        verbosity: normal

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, batch, tail_sampling]
          exporters: [otlp/jaeger, debug]

        metrics:
          receivers: [otlp]
          processors: [memory_limiter, resource, metricstransform, batch]
          exporters: [prometheusremotewrite, debug]

        logs:
          receivers: [otlp]
          processors: [memory_limiter, resource, batch]
          exporters: [loki, debug]
```

---

## 4. Sidecar自动注入

### 4.1 Instrumentation资源

```yaml
# instrumentation.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: Instrumentation
metadata:
  name: auto-instrumentation
  namespace: observability
spec:
  # Java自动注入
  java:
    image: ghcr.io/open-telemetry/opentelemetry-operator/autoinstrumentation-java:1.32.0
    env:
      - name: OTEL_JAVAAGENT_DEBUG
        value: "false"
      - name: OTEL_INSTRUMENTATION_JDBC_ENABLED
        value: "true"
      - name: OTEL_INSTRUMENTATION_KAFKA_ENABLED
        value: "true"

  # Node.js自动注入
  nodejs:
    image: ghcr.io/open-telemetry/opentelemetry-operator/autoinstrumentation-nodejs:0.46.0
    env:
      - name: OTEL_NODEJS_DEBUG
        value: "false"

  # Python自动注入
  python:
    image: ghcr.io/open-telemetry/opentelemetry-operator/autoinstrumentation-python:0.44b0
    env:
      - name: OTEL_PYTHON_LOG_CORRELATION
        value: "true"

  # .NET自动注入
  dotnet:
    image: ghcr.io/open-telemetry/opentelemetry-operator/autoinstrumentation-dotnet:1.2.0

  # 通用配置
  exporter:
    endpoint: http://base-collector.observability.svc.cluster.local:4317

  propagators:
    - tracecontext
    - baggage

  sampler:
    type: parentbased_traceidratio
    argument: "0.1"

  resource:
    addK8sUIDAttributes: true
```

### 4.2 Pod注解注入

```yaml
# 应用部署示例 - 自动注入Sidecar
apiVersion: apps/v1
kind: Deployment
metadata:
  name: payment-service
  namespace: payment
spec:
  replicas: 3
  selector:
    matchLabels:
      app: payment-service
  template:
    metadata:
      labels:
        app: payment-service
      # 注入注解
      annotations:
        # 启用Sidecar注入
        instrumentation.opentelemetry.io/inject-java: "true"
        # 使用哪个Instrumentation资源
        instrumentation.opentelemetry.io/container-names: "app"
        # 自定义环境变量
        instrumentation.opentelemetry.io/env: "OTEL_SERVICE_NAME=payment-service,OTEL_LOG_LEVEL=info"
    spec:
      containers:
        - name: app
          image: payment-service:v1.2.3
          ports:
            - containerPort: 8080
          env:
            - name: JAVA_TOOL_OPTIONS
              value: "-XX:+UseContainerSupport -XX:MaxRAMPercentage=75.0"
```

### 4.3 命名空间级注入

```yaml
# 为整个命名空间启用自动注入
apiVersion: v1
kind: Namespace
metadata:
  name: payment
  labels:
    # 启用OpenTelemetry注入
    opentelemetry.io/injection: "enabled"
  annotations:
    # 指定Instrumentation资源
    instrumentation.opentelemetry.io/default: observability/auto-instrumentation
```

---

## 5. 高级配置模式

### 5.1 多租户隔离架构

```yaml
# 租户A配置
tenant-a-pipeline.yaml
---
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: tenant-a-collector
  namespace: tenant-a
spec:
  mode: deployment
  serviceAccount: tenant-a-collector
  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

    processors:
      resource/tenant:
        attributes:
          - key: tenant.id
            value: tenant-a
            action: upsert
          - key: tenant.tier
            value: premium
            action: upsert

      # 资源配额限制
      memory_limiter:
        limit_mib: 500  # 租户A限制500MB

    exporters:
      otlp:
        endpoint: shared-backend.observability.svc.cluster.local:4317
        headers:
          X-Tenant-ID: tenant-a

# RBAC配置
---
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  name: tenant-a-collector
  namespace: tenant-a
rules:
  - apiGroups: [""]
    resources: ["pods", "services", "endpoints"]
    verbs: ["get", "list", "watch"]
  - apiGroups: ["apps"]
    resources: ["replicasets", "deployments", "daemonsets", "statefulsets"]
    verbs: ["get", "list", "watch"]
```

### 5.2 分片采集架构

```yaml
# 大规模集群分片采集
# shard-1-collector.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: collector-shard-1
  namespace: observability
spec:
  mode: daemonset
  serviceAccount: otel-collector

  # 节点选择器 - 只采集特定节点
  nodeSelector:
    observability.shard: "shard-1"

  tolerations:
    - key: "observability"
      operator: "Equal"
      value: "true"
      effect: "NoSchedule"

  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

    exporters:
      otlp/shard-backend:
        endpoint: backend-shard-1.monitoring.svc.cluster.local:4317

# 节点打标签
# kubectl label nodes node-1 node-2 node-3 observability.shard=shard-1
# kubectl label nodes node-4 node-5 node-6 observability.shard=shard-2
```

### 5.3 边缘计算场景

```yaml
# 边缘节点轻量级Collector
edge-collector.yaml
---
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: edge-collector
  namespace: observability
spec:
  mode: daemonset

  # 边缘节点资源限制
  resources:
    requests:
      cpu: "100m"
      memory: "128Mi"
    limits:
      cpu: "500m"
      memory: "512Mi"

  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

    processors:
      # 边缘预处理 - 减少传输
      batch:
        timeout: 5s           # 更长超时，减少连接
        send_batch_size: 5000  # 更大批次

      # 过滤低价值数据
      filter:
        metrics:
          exclude:
            match_type: regexp
            metric_names:
              - .*_bucket$    # 过滤直方图桶
              - .*_sum$       # 过滤sum

      memory_limiter:
        limit_mib: 400

    exporters:
      otlp/central:
        endpoint: central-collector.cloud.svc.cluster.local:4317
        # 边缘可能有不稳定连接
        retry_on_failure:
          enabled: true
          max_elapsed_time: 600s  # 更长的重试时间
        sending_queue:
          enabled: true
          queue_size: 10000       # 更大的队列，应对网络中断
```

---

## 6. 监控与运维

### 6.1 Collector自身监控

```yaml
# Collector自监控配置
self-monitoring-collector.yaml
---
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: monitoring-collector
  namespace: observability
spec:
  mode: deployment
  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

      # 采集其他Collector的指标
      prometheus:
        config:
          scrape_configs:
            - job_name: 'collectors'
              kubernetes_sd_configs:
                - role: pod
                  namespaces:
                    names:
                      - observability
              relabel_configs:
                - source_labels: [__meta_kubernetes_pod_label_app_kubernetes_io_component]
                  action: keep
                  regex: opentelemetry-collector
                - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
                  action: keep
                  regex: true
                - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_port]
                  action: replace
                  target_label: __address__
                  regex: ([^:]+)(?::\d+)?;(\d+)
                  replacement: $1:$2

    processors:
      memory_limiter:
        limit_mib: 1500

      batch:
        timeout: 1s

    exporters:
      prometheusremotewrite:
        endpoint: http://prometheus.monitoring.svc.cluster.local:9090/api/v1/write

      debug:
        verbosity: normal

    service:
      pipelines:
        metrics:
          receivers: [otlp, prometheus]
          processors: [memory_limiter, batch]
          exporters: [prometheusremotewrite, debug]

      # 启用Collector自监控
      telemetry:
        metrics:
          level: detailed
          address: 0.0.0.0:8888
        logs:
          level: info
```

### 6.2 关键监控指标

```promql
# Collector健康度Dashboard

# 1. 接收速率
sum(rate(otelcol_receiver_accepted_spans[5m])) by (receiver)
sum(rate(otelcol_receiver_accepted_metric_points[5m])) by (receiver)
sum(rate(otelcol_receiver_accepted_log_records[5m])) by (receiver)

# 2. 导出速率
sum(rate(otelcol_exporter_sent_spans[5m])) by (exporter)
sum(rate(otelcol_exporter_sent_metric_points[5m])) by (exporter)

# 3. 丢弃率 (应该接近0)
sum(rate(otelcol_exporter_send_failed_spans[5m])) by (exporter)
/
sum(rate(otelcol_exporter_sent_spans[5m])) by (exporter)

# 4. 队列使用
otelcol_exporter_queue_size / otelcol_exporter_queue_capacity

# 5. 处理延迟
histogram_quantile(0.99,
  sum(rate(otelcol_processor_batch_batch_send_size_bucket[5m])) by (le)
)

# 6. 内存使用
process_memory_rss / 1024 / 1024  # MB

# 7. CPU使用
rate(process_cpu_seconds[5m])
```

### 6.3 告警规则

```yaml
# collector-alerts.yaml
groups:
  - name: collector-health
    rules:
      # 高丢弃率告警
      - alert: CollectorHighDropRate
        expr: |
          (
            sum(rate(otelcol_exporter_send_failed_spans[5m]))
            /
            sum(rate(otelcol_exporter_sent_spans[5m]))
          ) > 0.05
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Collector丢弃率过高"
          description: "Collector {{ $labels.instance }} 丢弃率超过5%"

      # 队列满告警
      - alert: CollectorQueueFull
        expr: |
          otelcol_exporter_queue_size / otelcol_exporter_queue_capacity > 0.9
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "Collector队列即将满"
          description: "队列使用率超过90%"

      # 内存使用高
      - alert: CollectorHighMemory
        expr: process_memory_rss / 1024 / 1024 > 3000
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Collector内存使用高"
          description: "内存使用超过3GB"

      # 无数据接收
      - alert: CollectorNoData
        expr: |
          sum(rate(otelcol_receiver_accepted_spans[5m])) == 0
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Collector未接收数据"
          description: "10分钟内未接收任何span"
```

---

## 7. 性能优化

### 7.1 资源调优建议

```
┌─────────────────────────────────────────────────────────────┐
│                   Collector资源调优矩阵                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  场景                    CPU      内存      批大小    副本数  │
│  ─────────────────────────────────────────────────────────  │
│  小型集群(<100节点)      500m     1Gi       1024      2-3   │
│  中型集群(100-500节点)   1000m    2Gi       2048      5-10  │
│  大型集群(500-2000节点)  2000m    4Gi       4096      10-20 │
│  超大规模(>2000节点)     4000m    8Gi+      8192      20-50 │
│                                                             │
│  特殊场景:                                                  │
│  • 高流量追踪: 增加批大小到8192，提高内存到8Gi               │
│  • 日志-heavy: 增加CPU到2000m，启用文件缓存                  │
│  • 边缘计算: CPU 100m, 内存 256Mi，增大批超时                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 7.2 网络优化

```yaml
# 网络优化配置
network-optimized-collector.yaml
---
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: network-optimized
spec:
  mode: deployment
  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
            # 增大gRPC窗口大小
            max_recv_msg_size_mib: 64
            # 保持长连接
            keepalive:
              server_parameters:
                max_connection_idle: 60s
                max_connection_age: 300s
          http:
            endpoint: 0.0.0.0:4318
            # 启用压缩
            compression_algorithms:
              - gzip
              - zstd

    processors:
      batch:
        timeout: 2s
        send_batch_size: 4096
        # 启用压缩
        metadata_keys:
          - x-compression-type

    exporters:
      otlp:
        endpoint: backend:4317
        compression: zstd  # 使用zstd压缩比gzip更快
        # 连接池
        balancer_name: round_robin
        # 超时设置
        timeout: 10s
        # 重试策略
        retry_on_failure:
          enabled: true
          initial_interval: 1s
          max_interval: 5s
          max_elapsed_time: 30s
```

---

## 8. 故障排查指南

### 8.1 常见问题诊断

```bash
# 1. 检查Collector状态
kubectl get pods -n observability -l app.kubernetes.io/component=opentelemetry-collector

# 2. 查看日志
kubectl logs -n observability -l app.kubernetes.io/component=opentelemetry-collector --tail=100

# 3. 检查配置
kubectl get otelcol -n observability -o yaml

# 4. 验证Service
kubectl get svc -n observability

# 5. 网络连通性测试
kubectl run -it --rm debug --image=curlimages/curl --restart=Never -- \
  curl -v http://central-collector.observability.svc.cluster.local:4318/v1/traces

# 6. 资源使用
kubectl top pods -n observability

# 7. 检查事件
kubectl get events -n observability --sort-by='.lastTimestamp' | tail -20
```

### 8.2 调试模式

```yaml
# 启用调试模式
debug-collector.yaml
---
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: debug-collector
spec:
  mode: deployment
  args:
    # 启用详细日志
    - --log-level=DEBUG
    # 启用Go性能分析
    - --set=service.telemetry.metrics.level=detailed

  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

    processors:
      batch:
        timeout: 1s

    exporters:
      # 详细输出到stdout
      debug:
        verbosity: detailed

      # 文件导出用于分析
      file:
        path: /var/log/otel/traces.json

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [batch]
          exporters: [debug, file]
```

---

## 9. 参考文档

| 资源 | 链接 |
|------|------|
| OpenTelemetry Operator | <https://github.com/open-telemetry/opentelemetry-operator> |
| K8s Attributes Processor | <https://pkg.go.dev/github.com/open-telemetry/opentelemetry-collector-contrib/processor/k8sattributesprocessor> |
| Kubelet Stats Receiver | <https://pkg.go.dev/github.com/open-telemetry/opentelemetry-collector-contrib/receiver/kubeletstatsreceiver> |
| Filelog Receiver | <https://pkg.go.dev/github.com/open-telemetry/opentelemetry-collector-contrib/receiver/filelogreceiver> |

---

**最后更新**: 2026-03-17
**维护者**: OTLP实践团队
**状态**: Published
