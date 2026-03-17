---
title: Collector多可用区部署方案
description: OpenTelemetry Collector在生产环境的多可用区高可用部署方案，包括故障转移、数据同步和负载均衡
category: 运维实践
tags:
  - high-availability
  - multi-az
  - disaster-recovery
  - collector
  - production
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# Collector多可用区部署方案

> **可用性目标**: 99.99%
> **RTO**: < 5分钟
> **RPO**: < 1分钟
> **技术深度**: ⭐⭐⭐⭐ (高级)
> **最后更新**: 2026-03-17

---

## 1. 架构设计

### 1.1 多可用区架构图

```
┌─────────────────────────────────────────────────────────────┐
│                     多可用区Collector架构                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                        智能DNS/GSLB                          │
│                              │                              │
│          ┌───────────────────┼───────────────────┐          │
│          │                   │                   │          │
│          ▼                   ▼                   ▼          │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐    │
│  │  可用区 A    │   │  可用区 B    │   │  可用区 C    │    │
│  │ (Primary)    │   │ (Secondary)  │   │ (DR)         │    │
│  │              │   │              │   │              │    │
│  │ Collector    │◄─►│ Collector    │◄─►│ Collector    │    │
│  │ Cluster      │   │ Cluster      │   │ Cluster      │    │
│  │ - 3 replicas │   │ - 3 replicas │   │ - 2 replicas │    │
│  │ - HPA 3-20   │   │ - HPA 3-20   │   │ - HPA 2-10   │    │
│  │ - Active     │   │ - Active     │   │ - Standby    │    │
│  │              │   │              │   │              │    │
│  └──────┬───────┘   └──────┬───────┘   └──────┬───────┘    │
│         │                  │                  │             │
│         └──────────────────┼──────────────────┘             │
│                            │                               │
│                    ┌───────▼───────┐                       │
│                    │  全局后端存储  │                       │
│                    │  (跨区域复制)  │                       │
│                    └───────────────┘                       │
│                                                             │
│  流量分配:                                                  │
│  - 平时: A区 60%, B区 40%                                    │
│  - A区故障: B区 100%                                         │
│  - A+B故障: C区 100% (降级模式)                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 架构组件说明

| 组件 | A区 (主) | B区 (备) | C区 (灾备) | 说明 |
|------|----------|----------|------------|------|
| Collector实例 | 3-20 | 3-20 | 2-10 | HPA自动扩缩容 |
| 流量比例 | 60% | 40% | 0% | 智能DNS分配 |
| 存储角色 | 主写 | 只读 | 只读 | 异步复制 |
| RTO | - | <2min | <5min | 故障切换时间 |

---

## 2. Kubernetes部署配置

### 2.1 多可用区部署

```yaml
# collector-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: collector-zone-a
  namespace: observability
  labels:
    app: collector
    zone: a
spec:
  replicas: 3
  selector:
    matchLabels:
      app: collector
      zone: a
  template:
    metadata:
      labels:
        app: collector
        zone: a
    spec:
      # 节点亲和性 - 强制部署到A区
      affinity:
        nodeAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
            nodeSelectorTerms:
              - matchExpressions:
                  - key: topology.kubernetes.io/zone
                    operator: In
                    values:
                      - us-east-1a
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
            - weight: 100
              podAffinityTerm:
                labelSelector:
                  matchExpressions:
                    - key: app
                      operator: In
                      values:
                        - collector
                topologyKey: kubernetes.io/hostname

      containers:
        - name: collector
          image: otel/opentelemetry-collector-contrib:0.147.0
          args:
            - --config=/etc/otel/collector.yaml
          resources:
            requests:
              cpu: "500m"
              memory: "1Gi"
            limits:
              cpu: "2000m"
              memory: "4Gi"
          ports:
            - containerPort: 4317  # OTLP gRPC
            - containerPort: 4318  # OTLP HTTP
            - containerPort: 8888  # Metrics
          volumeMounts:
            - name: config
              mountPath: /etc/otel
            - name: queue-storage
              mountPath: /var/otel/storage
          livenessProbe:
            httpGet:
              path: /health/status
              port: 13133
            initialDelaySeconds: 10
            periodSeconds: 5
          readinessProbe:
            httpGet:
              path: /health/status
              port: 13133
            initialDelaySeconds: 5
            periodSeconds: 3

      volumes:
        - name: config
          configMap:
            name: collector-config-zone-a
        - name: queue-storage
          persistentVolumeClaim:
            claimName: collector-queue-zone-a
```

### 2.2 HPA自动扩缩容

```yaml
# collector-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: collector-hpa-zone-a
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: collector-zone-a
  minReplicas: 3
  maxReplicas: 20
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
    - type: Pods
      pods:
        metric:
          name: otelcol_exporter_queue_size
        target:
          type: AverageValue
          averageValue: "8000"
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
        - type: Percent
          value: 100
          periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
        - type: Percent
          value: 10
          periodSeconds: 60
```

---

## 3. 数据同步策略

### 3.1 跨区域复制

```yaml
# 主区Collector配置 (A区)
exporters:
  # 本地后端
  otlp/local:
    endpoint: backend-zone-a:4317
    sending_queue:
      enabled: true
      queue_size: 10000

  # 跨区域复制到B区
  otlp/cross-zone-b:
    endpoint: collector-zone-b.observability.svc.cluster.local:4317
    sending_queue:
      enabled: true
      queue_size: 50000  # 更大队列应对网络延迟
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 60s
      max_elapsed_time: 300s

  # 跨区域复制到C区 (DR)
  otlp/cross-zone-c:
    endpoint: collector-zone-c.observability.svc.cluster.local:4317
    sending_queue:
      enabled: true
      queue_size: 100000
    retry_on_failure:
      enabled: true
      max_elapsed_time: 600s  # 更长的重试时间

processors:
  # 路由处理器
  routing:
    from_attribute: zone
    default_exporters: [otlp/local]
    table:
      - value: zone-a
        exporters: [otlp/local, otlp/cross-zone-b]
      - value: zone-b
        exporters: [otlp/local, otlp/cross-zone-a]
      - value: critical
        exporters: [otlp/local, otlp/cross-zone-b, otlp/cross-zone-c]
```

### 3.2 故障转移配置

```yaml
extensions:
  # 健康检查扩展
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health/status
    check_collector_pipeline:
      enabled: true
      interval: 5s
      exporter_failure_threshold: 5

  # 故障转移控制器
  failover:
    endpoint: 0.0.0.0:13333
    peers:
      - endpoint: collector-zone-b:13333
        priority: 1
      - endpoint: collector-zone-c:13333
        priority: 2
    health_check_interval: 10s
```

---

## 4. 负载均衡

### 4.1 全局负载均衡配置

```yaml
# Global Load Balancer (GLB)配置
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: collector-gateway
  namespace: observability
spec:
  selector:
    istio: ingressgateway
  servers:
    - port:
        number: 4317
        name: grpc-otlp
        protocol: GRPC
      hosts:
        - "collector.example.com"
      tls:
        mode: SIMPLE
        credentialName: collector-tls
    - port:
        number: 4318
        name: http-otlp
        protocol: HTTP
      hosts:
        - "collector.example.com"

---
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: collector-routing
  namespace: observability
spec:
  hosts:
    - "collector.example.com"
  gateways:
    - collector-gateway
  http:
    - match:
        - uri:
            prefix: /v1/traces
      route:
        - destination:
            host: collector-zone-a
            port:
              number: 4318
          weight: 60
        - destination:
            host: collector-zone-b
            port:
              number: 4318
          weight: 40
      retries:
        attempts: 3
        perTryTimeout: 2s
        retryOn: gateway-error,connect-failure,refused-stream
```

### 4.2 故障自动切换

```yaml
# 故障检测与切换
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: collector-failover
  namespace: observability
spec:
  host: collector-zone-a
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        h2UpgradePolicy: UPGRADE
        http1MaxPendingRequests: 100
        http2MaxRequests: 1000
    loadBalancer:
      simple: LEAST_CONN
      localityLbSetting:
        enabled: true
        failover:
          - from: us-east-1a
            to: us-east-1b
          - from: us-east-1b
            to: us-east-1c
    outlierDetection:
      consecutive5xxErrors: 5
      interval: 30s
      baseEjectionTime: 30s
```

---

## 5. 监控告警

### 5.1 关键监控指标

```promql
# 各可用区Collector健康状态
up{job="otel-collector", zone=~"a|b|c"}

# 各可用区流量分布
sum(rate(otelcol_receiver_accepted_spans[5m])) by (zone)

# 跨区域复制延迟
histogram_quantile(0.99,
  sum(rate(otelcol_exporter_send_latency_bucket{exporter=~"cross-zone-.*"}[5m])) by (le, zone)
)

# 故障切换次数
increase(collector_failover_switches_total[1h])

# 数据同步延迟
otelcol_cross_zone_replication_lag_seconds
```

### 5.2 告警规则

```yaml
groups:
  - name: multi-zone-alerts
    rules:
      # 可用区故障告警
      - alert: CollectorZoneDown
        expr: sum(up{job="otel-collector"}) by (zone) == 0
        for: 1m
        labels:
          severity: critical
          team: platform
        annotations:
          summary: "Collector可用区 {{ $labels.zone }} 完全不可用"

      # 跨区域复制延迟告警
      - alert: CrossZoneReplicationHighLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(otelcol_exporter_send_latency_bucket{exporter=~"cross-zone-.*"}[5m])) by (le, zone)
          ) > 5
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "跨区域复制延迟过高"

      # 数据丢失风险告警
      - alert: DataLossRisk
        expr: |
          otelcol_exporter_queue_size / otelcol_exporter_queue_capacity > 0.9
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "队列即将满，存在数据丢失风险"
```

---

## 6. 故障演练

### 6.1 演练场景

```yaml
# 故障演练计划
scenarios:
  - name: 单可用区故障
    steps:
      - 模拟A区网络中断
      - 验证自动切换到B区
      - 验证数据零丢失
      - 恢复A区服务
      - 验证流量回切

  - name: 双可用区故障
    steps:
      - 同时中断A区和B区
      - 验证切换到C区(DR)
      - 验证降级模式运行
      - 逐步恢复服务

  - name: 网络分区
    steps:
      - A区与B区间网络中断
      - 验证各自独立运行
      - 验证网络恢复后数据同步
```

---

**最后更新**: 2026-03-17
**维护者**: OTLP运维团队
**状态**: Published
