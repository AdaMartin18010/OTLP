# ☸️ OTLP Kubernetes部署完整指南

> **目标**: 帮助用户在Kubernetes集群中部署生产级OTLP环境
> **适用场景**: 生产环境、大规模部署
> **更新时间**: 2025年10月20日

---

## 📋 目录

- [☸️ OTLP Kubernetes部署完整指南](#️-otlp-kubernetes部署完整指南)
  - [📋 目录](#-目录)
  - [🚀 环境准备](#-环境准备)
    - [1. 前置条件](#1-前置条件)
    - [2. 创建命名空间](#2-创建命名空间)
  - [🎯 快速开始](#-快速开始)
    - [1. 使用Helm部署](#1-使用helm部署)
    - [2. 验证部署](#2-验证部署)
  - [🏗️ 完整部署](#️-完整部署)
    - [1. OpenTelemetry Collector部署](#1-opentelemetry-collector部署)
    - [2. 应用配置](#2-应用配置)
    - [3. 验证部署](#3-验证部署)
  - [🔧 Jaeger部署](#-jaeger部署)
  - [⚙️ 配置管理](#️-配置管理)
    - [1. 使用Kustomize](#1-使用kustomize)
    - [2. 使用Helm Values](#2-使用helm-values)
  - [📈 扩展和高可用](#-扩展和高可用)
    - [1. DaemonSet模式（节点级采集）](#1-daemonset模式节点级采集)
    - [2. StatefulSet模式（有状态部署）](#2-statefulset模式有状态部署)
    - [3. 多层架构](#3-多层架构)
  - [📊 监控和日志](#-监控和日志)
    - [1. Prometheus ServiceMonitor](#1-prometheus-servicemonitor)
    - [2. 日志聚合](#2-日志聚合)
    - [3. Grafana Dashboard](#3-grafana-dashboard)
  - [🔧 故障排查](#-故障排查)
    - [1. Pod无法启动](#1-pod无法启动)
    - [2. 服务连接问题](#2-服务连接问题)
    - [3. 性能问题](#3-性能问题)
  - [📋 最佳实践](#-最佳实践)
    - [1. RBAC配置](#1-rbac配置)
    - [2. 资源限制](#2-资源限制)
    - [3. 节点亲和性](#3-节点亲和性)
    - [4. PodDisruptionBudget](#4-poddisruptionbudget)
    - [5. NetworkPolicy](#5-networkpolicy)
  - [🔗 相关资源](#-相关资源)

---

## 🚀 环境准备

### 1. 前置条件

```bash
# Kubernetes集群 >= 1.24
kubectl version

# Helm >= 3.0
helm version

# 确认集群可用
kubectl cluster-info
kubectl get nodes
```

### 2. 创建命名空间

```bash
# 创建observability命名空间
kubectl create namespace observability

# 设置默认命名空间
kubectl config set-context --current --namespace=observability
```

---

## 🎯 快速开始

### 1. 使用Helm部署

```bash
# 添加OpenTelemetry Helm仓库
helm repo add open-telemetry https://open-telemetry.github.io/opentelemetry-helm-charts
helm repo update

# 安装OpenTelemetry Collector
helm install otel-collector open-telemetry/opentelemetry-collector \
  --namespace observability \
  --create-namespace

# 安装Jaeger
helm repo add jaegertracing https://jaegertracing.github.io/helm-charts
helm install jaeger jaegertracing/jaeger \
  --namespace observability
```

### 2. 验证部署

```bash
# 查看Pod状态
kubectl get pods -n observability

# 查看服务
kubectl get svc -n observability

# 端口转发访问Jaeger UI
kubectl port-forward -n observability svc/jaeger-query 16686:16686
# 访问 http://localhost:16686
```

✅ **快速部署完成！**

---

## 🏗️ 完整部署

### 1. OpenTelemetry Collector部署

创建 `otel-collector.yaml`:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: observability
data:
  otel-config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318

    processors:
      memory_limiter:
        check_interval: 1s
        limit_mib: 2048
        spike_limit_mib: 512

      batch:
        timeout: 1s
        send_batch_size: 512

      resourcedetection:
        detectors: [env, system, docker]
        timeout: 5s

    exporters:
      jaeger:
        endpoint: jaeger-collector.observability.svc.cluster.local:14250
        tls:
          insecure: true

      prometheus:
        endpoint: 0.0.0.0:8889

      logging:
        loglevel: info

    extensions:
      health_check:
        endpoint: 0.0.0.0:13133

      pprof:
        endpoint: 0.0.0.0:1777

    service:
      extensions: [health_check, pprof]
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, resourcedetection, batch]
          exporters: [jaeger, logging]

        metrics:
          receivers: [otlp]
          processors: [memory_limiter, batch]
          exporters: [prometheus]

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
  labels:
    app: otel-collector
    component: collector
spec:
  replicas: 2
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        args:
          - "--config=/conf/otel-config.yaml"
        ports:
        - containerPort: 4317
          name: otlp-grpc
          protocol: TCP
        - containerPort: 4318
          name: otlp-http
          protocol: TCP
        - containerPort: 13133
          name: health-check
          protocol: TCP
        - containerPort: 8888
          name: metrics
          protocol: TCP
        - containerPort: 8889
          name: prometheus
          protocol: TCP

        env:
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace

        resources:
          requests:
            memory: "1Gi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "1000m"

        livenessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 30
          periodSeconds: 10

        readinessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 10
          periodSeconds: 5

        volumeMounts:
        - name: config
          mountPath: /conf

      volumes:
      - name: config
        configMap:
          name: otel-collector-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
  labels:
    app: otel-collector
spec:
  type: ClusterIP
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
    protocol: TCP
  - name: otlp-http
    port: 4318
    targetPort: 4318
    protocol: TCP
  - name: metrics
    port: 8888
    targetPort: 8888
    protocol: TCP
  - name: prometheus
    port: 8889
    targetPort: 8889
    protocol: TCP
  selector:
    app: otel-collector

---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
  minReplicas: 2
  maxReplicas: 10
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
```

### 2. 应用配置

```bash
kubectl apply -f otel-collector.yaml
```

### 3. 验证部署

```bash
# 查看Deployment
kubectl get deployment -n observability

# 查看Pod
kubectl get pods -n observability -l app=otel-collector

# 查看Service
kubectl get svc -n observability otel-collector

# 查看HPA
kubectl get hpa -n observability
```

---

## 🔧 Jaeger部署

创建 `jaeger.yaml`:

```yaml
apiVersion: v1
kind: Service
metadata:
  name: jaeger-collector
  namespace: observability
  labels:
    app: jaeger
    component: collector
spec:
  type: ClusterIP
  ports:
  - name: grpc
    port: 14250
    targetPort: 14250
    protocol: TCP
  - name: http
    port: 14268
    targetPort: 14268
    protocol: TCP
  selector:
    app: jaeger
    component: collector

---
apiVersion: v1
kind: Service
metadata:
  name: jaeger-query
  namespace: observability
  labels:
    app: jaeger
    component: query
spec:
  type: LoadBalancer
  ports:
  - name: http-query
    port: 16686
    targetPort: 16686
    protocol: TCP
  selector:
    app: jaeger
    component: query

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: jaeger
  namespace: observability
  labels:
    app: jaeger
spec:
  replicas: 1
  selector:
    matchLabels:
      app: jaeger
  template:
    metadata:
      labels:
        app: jaeger
        component: all-in-one
    spec:
      containers:
      - name: jaeger
        image: jaegertracing/all-in-one:latest
        env:
        - name: COLLECTOR_OTLP_ENABLED
          value: "true"
        - name: SPAN_STORAGE_TYPE
          value: "badger"
        - name: BADGER_EPHEMERAL
          value: "false"
        - name: BADGER_DIRECTORY_VALUE
          value: "/badger/data"
        - name: BADGER_DIRECTORY_KEY
          value: "/badger/key"
        ports:
        - containerPort: 16686
          name: query
        - containerPort: 14250
          name: grpc
        - containerPort: 14268
          name: http
        - containerPort: 6831
          name: thrift
          protocol: UDP

        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"

        volumeMounts:
        - name: badger-data
          mountPath: /badger

      volumes:
      - name: badger-data
        persistentVolumeClaim:
          claimName: jaeger-pvc

---
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: jaeger-pvc
  namespace: observability
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 10Gi
```

应用配置:

```bash
kubectl apply -f jaeger.yaml
```

---

## ⚙️ 配置管理

### 1. 使用Kustomize

创建目录结构:

```text
k8s/
├── base/
│   ├── kustomization.yaml
│   ├── otel-collector.yaml
│   └── jaeger.yaml
├── overlays/
│   ├── dev/
│   │   └── kustomization.yaml
│   ├── staging/
│   │   └── kustomization.yaml
│   └── prod/
│       └── kustomization.yaml
```

**base/kustomization.yaml**:

```yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
  - otel-collector.yaml
  - jaeger.yaml

commonLabels:
  app.kubernetes.io/name: otlp
  app.kubernetes.io/managed-by: kustomize
```

**overlays/prod/kustomization.yaml**:

```yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

bases:
  - ../../base

namespace: observability-prod

replicas:
  - name: otel-collector
    count: 5

patchesStrategicMerge:
  - |-
    apiVersion: apps/v1
    kind: Deployment
    metadata:
      name: otel-collector
    spec:
      template:
        spec:
          containers:
          - name: otel-collector
            resources:
              requests:
                memory: "2Gi"
                cpu: "1000m"
              limits:
                memory: "4Gi"
                cpu: "2000m"
```

部署:

```bash
# 开发环境
kubectl apply -k k8s/overlays/dev

# 生产环境
kubectl apply -k k8s/overlays/prod
```

### 2. 使用Helm Values

创建 `values.yaml`:

```yaml
# OpenTelemetry Collector配置
opentelemetry-collector:
  mode: deployment
  replicaCount: 3

  image:
    repository: otel/opentelemetry-collector-contrib
    tag: latest

  resources:
    requests:
      cpu: 500m
      memory: 1Gi
    limits:
      cpu: 1000m
      memory: 2Gi

  config:
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318

    processors:
      memory_limiter:
        limit_mib: 2048
      batch:
        timeout: 1s

    exporters:
      jaeger:
        endpoint: jaeger-collector:14250
        tls:
          insecure: true

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, batch]
          exporters: [jaeger]

  autoscaling:
    enabled: true
    minReplicas: 2
    maxReplicas: 10
    targetCPUUtilizationPercentage: 70
```

部署:

```bash
helm install otel-collector open-telemetry/opentelemetry-collector \
  --namespace observability \
  --values values.yaml
```

---

## 📈 扩展和高可用

### 1. DaemonSet模式（节点级采集）

```yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector-agent
  template:
    metadata:
      labels:
        app: otel-collector-agent
    spec:
      serviceAccountName: otel-collector
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        args:
          - "--config=/conf/otel-agent-config.yaml"
        volumeMounts:
        - name: config
          mountPath: /conf
        - name: hostfs
          mountPath: /hostfs
          readOnly: true
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "200m"

      volumes:
      - name: config
        configMap:
          name: otel-collector-agent-config
      - name: hostfs
        hostPath:
          path: /
```

### 2. StatefulSet模式（有状态部署）

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: otel-collector-stateful
  namespace: observability
spec:
  serviceName: otel-collector-stateful
  replicas: 3
  selector:
    matchLabels:
      app: otel-collector-stateful
  template:
    metadata:
      labels:
        app: otel-collector-stateful
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        volumeMounts:
        - name: data
          mountPath: /data

  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: [ "ReadWriteOnce" ]
      resources:
        requests:
          storage: 10Gi
```

### 3. 多层架构

```text
┌─────────────────────────────────────────────┐
│           应用Pod (每个节点)                 │
│         ↓ (DaemonSet Agent)                 │
├─────────────────────────────────────────────┤
│      otel-collector-agent (DaemonSet)       │
│         ↓ (本地聚合)                        │
├─────────────────────────────────────────────┤
│    otel-collector-gateway (Deployment)      │
│         ↓ (集中处理)                        │
├─────────────────────────────────────────────┤
│         Jaeger / Prometheus / ES            │
└─────────────────────────────────────────────┘
```

---

## 📊 监控和日志

### 1. Prometheus ServiceMonitor

```yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: otel-collector
  namespace: observability
  labels:
    app: otel-collector
spec:
  selector:
    matchLabels:
      app: otel-collector
  endpoints:
  - port: metrics
    interval: 30s
    path: /metrics
```

### 2. 日志聚合

```bash
# 查看所有Collector日志
kubectl logs -n observability -l app=otel-collector --tail=100 -f

# 查看特定Pod日志
kubectl logs -n observability otel-collector-xxx -f

# 导出日志
kubectl logs -n observability -l app=otel-collector > collector.log
```

### 3. Grafana Dashboard

```bash
# 安装Grafana
helm install grafana grafana/grafana \
  --namespace observability \
  --set adminPassword=admin123

# 端口转发
kubectl port-forward -n observability svc/grafana 3000:80

# 访问 http://localhost:3000
```

---

## 🔧 故障排查

### 1. Pod无法启动

```bash
# 查看Pod状态
kubectl get pods -n observability

# 查看Pod详情
kubectl describe pod -n observability otel-collector-xxx

# 查看事件
kubectl get events -n observability --sort-by='.lastTimestamp'

# 查看日志
kubectl logs -n observability otel-collector-xxx --previous
```

### 2. 服务连接问题

```bash
# 测试服务DNS
kubectl run -it --rm debug --image=busybox --restart=Never -n observability -- sh
nslookup otel-collector
nslookup jaeger-collector

# 测试服务连接
kubectl run -it --rm debug --image=curlimages/curl --restart=Never -n observability -- \
  curl http://otel-collector:13133/
```

### 3. 性能问题

```bash
# 查看资源使用
kubectl top pods -n observability

# 查看节点资源
kubectl top nodes

# 查看HPA状态
kubectl get hpa -n observability
kubectl describe hpa otel-collector-hpa -n observability
```

---

## 📋 最佳实践

### 1. RBAC配置

```yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: otel-collector
rules:
- apiGroups: [""]
  resources:
  - nodes
  - nodes/proxy
  - services
  - endpoints
  - pods
  verbs: ["get", "list", "watch"]
- apiGroups: [""]
  resources:
  - configmaps
  verbs: ["get"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: otel-collector
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: otel-collector
subjects:
- kind: ServiceAccount
  name: otel-collector
  namespace: observability
```

### 2. 资源限制

```yaml
resources:
  requests:
    memory: "1Gi"
    cpu: "500m"
  limits:
    memory: "2Gi"
    cpu: "1000m"
```

### 3. 节点亲和性

```yaml
affinity:
  nodeAffinity:
    requiredDuringSchedulingIgnoredDuringExecution:
      nodeSelectorTerms:
      - matchExpressions:
        - key: node-role.kubernetes.io/worker
          operator: In
          values:
          - "true"

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

### 4. PodDisruptionBudget

```yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: otel-collector-pdb
  namespace: observability
spec:
  minAvailable: 1
  selector:
    matchLabels:
      app: otel-collector
```

### 5. NetworkPolicy

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otel-collector-netpol
  namespace: observability
spec:
  podSelector:
    matchLabels:
      app: otel-collector
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector: {}
    ports:
    - protocol: TCP
      port: 4317
    - protocol: TCP
      port: 4318
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: observability
    ports:
    - protocol: TCP
      port: 14250  # Jaeger
```

---

## 🔗 相关资源

- [🐳 Docker部署指南](🐳_Docker部署完整指南.md) - Docker部署
- [🔧 故障排查手册](🔧_故障排查完整手册.md) - 解决问题
- [⚡ 性能优化指南](⚡_性能优化完整指南.md) - 优化性能

---

**更新时间**: 2025年10月20日
**版本**: v1.0.0
**维护者**: OTLP项目团队

---

**☸️ 在Kubernetes上部署生产级OTLP环境！** 🚀
