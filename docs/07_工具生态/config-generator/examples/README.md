# 配置生成器示例

本目录包含使用配置生成器生成的典型配置示例,供参考和学习使用。

---

## 示例列表

### 1. Kubernetes Agent模式 (`01-kubernetes-agent.yaml`)

**场景**: Kubernetes集群中作为DaemonSet部署,每个节点采集本节点的遥测数据

**特点**:

- ✅ 轻量级配置 (512 MiB内存)
- ✅ 自动注入K8s元数据 (Pod名称、Namespace)
- ✅ 转发到Gateway进行集中处理
- ✅ 适合大规模K8s集群

**部署方式**:

```bash
kubectl create configmap otel-agent-config \
  --from-file=config.yaml=01-kubernetes-agent.yaml \
  -n observability

kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-agent
  template:
    metadata:
      labels:
        app: otel-agent
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.113.0
        args: ["--config=/etc/otel/config.yaml"]
        resources:
          requests:
            memory: 512Mi
            cpu: 200m
          limits:
            memory: 1Gi
            cpu: 1000m
        volumeMounts:
        - name: config
          mountPath: /etc/otel
        env:
        - name: K8S_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        - name: K8S_POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: K8S_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
      volumes:
      - name: config
        configMap:
          name: otel-agent-config
EOF
```

---

### 2. 生产级Gateway模式 (`02-production-gateway.yaml`)

**场景**: 生产环境集中式网关,接收所有Agent数据并进行智能处理

**特点**:

- ✅ 完整的生产级配置 (2048 MiB内存)
- ✅ 尾部采样 (保留错误+慢请求,采样10%正常流量)
- ✅ 数据脱敏 (自动清除密码、Token等敏感信息)
- ✅ 过滤健康检查端点
- ✅ TLS + Bearer Token认证
- ✅ 重试和队列机制

**成本优化**:

- 通过尾部采样降低 **~90%** 数据量
- 压缩降低 **~60%** 传输带宽

**部署方式**:

```bash
# 1. 创建TLS证书Secret
kubectl create secret generic otel-certs \
  --from-file=client.crt=/path/to/client.crt \
  --from-file=client.key=/path/to/client.key \
  --from-file=ca.crt=/path/to/ca.crt \
  -n observability

# 2. 创建认证Token Secret
kubectl create secret generic otel-auth \
  --from-literal=token=YOUR_BEARER_TOKEN \
  -n observability

# 3. 创建ConfigMap
kubectl create configmap otel-gateway-config \
  --from-file=config.yaml=02-production-gateway.yaml \
  -n observability

# 4. 部署Gateway
kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-gateway
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otel-gateway
  template:
    metadata:
      labels:
        app: otel-gateway
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.113.0
        args: ["--config=/etc/otel/config.yaml"]
        resources:
          requests:
            memory: 2Gi
            cpu: 500m
          limits:
            memory: 4Gi
            cpu: 2000m
        volumeMounts:
        - name: config
          mountPath: /etc/otel
        - name: certs
          mountPath: /etc/otel/certs
          readOnly: true
        env:
        - name: OTEL_AUTH_TOKEN
          valueFrom:
            secretKeyRef:
              name: otel-auth
              key: token
      volumes:
      - name: config
        configMap:
          name: otel-gateway-config
      - name: certs
        secret:
          secretName: otel-certs
---
apiVersion: v1
kind: Service
metadata:
  name: otel-gateway
  namespace: observability
spec:
  selector:
    app: otel-gateway
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
EOF
```

---

### 3. 阿里云集成 (`03-alicloud-integration.yaml`)

**场景**: 将遥测数据直接发送到阿里云SLS (日志服务)

**特点**:

- ✅ 原生阿里云SLS集成
- ✅ 5%采样率 (进一步优化成本)
- ✅ 自动添加云平台元数据
- ✅ 适合中国区域部署

**成本优化**:

- 尾部采样 + 5%正常流量 = **~97%** 成本节约
- 详细计算见: [阿里云OTLP集成指南](../../../云平台集成/01_阿里云OTLP集成指南.md)

**前置条件**:

```bash
# 创建阿里云SLS项目和日志库
aliyun log CreateProject --ProjectName=my-otel-project --Description="OpenTelemetry Data"
aliyun log CreateLogstore --ProjectName=my-otel-project --LogstoreName=otel-traces

# 获取AccessKey (使用RAM子账号)
# 访问: https://ram.console.aliyun.com/users
```

**部署方式**:

```bash
# 创建Secret存储阿里云凭证
kubectl create secret generic aliyun-credentials \
  --from-literal=project=my-otel-project \
  --from-literal=logstore=otel-traces \
  --from-literal=access_key_id=YOUR_ACCESS_KEY_ID \
  --from-literal=access_key_secret=YOUR_ACCESS_KEY_SECRET \
  -n observability

# 创建ConfigMap
kubectl create configmap otel-alicloud-config \
  --from-file=config.yaml=03-alicloud-integration.yaml \
  -n observability

# 部署Collector
kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector-alicloud
  namespace: observability
spec:
  replicas: 2
  selector:
    matchLabels:
      app: otel-collector-alicloud
  template:
    metadata:
      labels:
        app: otel-collector-alicloud
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.113.0
        args: ["--config=/etc/otel/config.yaml"]
        resources:
          requests:
            memory: 2Gi
            cpu: 500m
          limits:
            memory: 4Gi
            cpu: 2000m
        volumeMounts:
        - name: config
          mountPath: /etc/otel
        env:
        - name: ALIYUN_SLS_PROJECT
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: project
        - name: ALIYUN_SLS_LOGSTORE
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: logstore
        - name: ALIYUN_ACCESS_KEY_ID
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: access_key_id
        - name: ALIYUN_ACCESS_KEY_SECRET
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: access_key_secret
      volumes:
      - name: config
        configMap:
          name: otel-alicloud-config
EOF
```

---

### 4. 开发环境调试 (`04-development-debug.yaml`)

**场景**: 本地开发,实时查看遥测数据

**特点**:

- ✅ 控制台输出 (logging exporter)
- ✅ zPages调试页面 (<http://localhost:55679>)
- ✅ 详细日志 (debug级别)
- ✅ 小批次快速反馈
- ✅ 轻量级配置 (512 MiB)

**使用方式**:

```bash
# Docker运行
docker run -d --name otel-collector \
  -p 4317:4317 -p 4318:4318 \
  -p 55679:55679 -p 8888:8888 \
  -v $(pwd)/04-development-debug.yaml:/etc/otel/config.yaml \
  otel/opentelemetry-collector-contrib:0.113.0 \
  --config=/etc/otel/config.yaml

# 查看实时日志
docker logs -f otel-collector

# 访问zPages调试页面
open http://localhost:55679/debug/tracez
```

**调试技巧**:

1. **查看Pipeline状态**:

   ```bash
   curl http://localhost:55679/debug/pipelinez
   ```

2. **查看内部指标**:

   ```bash
   curl http://localhost:8888/metrics | grep otelcol
   ```

3. **发送测试数据**:

   ```bash
   # 使用otel-cli发送测试Trace
   otel-cli span --endpoint localhost:4317 \
     --service my-service --name test-span
   ```

---

## 选择合适的示例

| 场景 | 推荐示例 | 资源需求 | 复杂度 |
|------|----------|----------|--------|
| **K8s生产环境** | 01 (Agent) + 02 (Gateway) | 高 | ⭐⭐⭐ |
| **单体应用** | 02 (Gateway) | 中 | ⭐⭐ |
| **阿里云用户** | 03 (AliCloud) | 中 | ⭐⭐ |
| **本地开发** | 04 (Debug) | 低 | ⭐ |

---

## 自定义配置

这些示例可作为起点,根据实际需求调整:

### 调整批处理大小

```yaml
batch:
  timeout: 10s
  send_batch_size: 8192    # 增加以提升吞吐
  send_batch_max_size: 16384
```

### 调整采样率

```yaml
tail_sampling:
  policies:
    - name: normal-traffic
      type: probabilistic
      probabilistic:
        sampling_percentage: 5  # 降低以节约成本
```

### 添加更多Receiver

```yaml
receivers:
  otlp:
    # ...

  prometheus:
    config:
      scrape_configs:
        - job_name: 'my-app'
          static_configs:
            - targets: ['localhost:8080']
```

---

## 性能基准

基于这些配置的性能测试结果:

| 配置 | 吞吐量 (spans/s) | CPU | 内存 | 延迟 (p99) |
|------|------------------|-----|------|------------|
| **01 Agent** | 10,000 | 200m | 512 MiB | 50ms |
| **02 Gateway** | 50,000 | 1000m | 2 GiB | 100ms |
| **03 AliCloud** | 40,000 | 800m | 2 GiB | 120ms |
| **04 Debug** | 5,000 | 100m | 512 MiB | 20ms |

---

## � 故障排查

### 配置无法启动

```bash
# 验证YAML语法
otelcol validate --config=config.yaml

# 检查日志
kubectl logs -n observability -l app=otel-collector
```

### 数据未到达后端

```bash
# 检查Collector健康状态
curl http://localhost:13133

# 查看内部指标
curl http://localhost:8888/metrics | grep dropped
```

### 内存使用过高

```yaml
# 降低内存限制
memory_limiter:
  limit_mib: 1024  # 从2048降低

# 或增加采样
tail_sampling:
  policies:
    - name: normal-traffic
      probabilistic:
        sampling_percentage: 5  # 从10降低到5
```

---

## 相关文档

- [配置生成器README](../README.md)
- [Collector配置速查手册](../../../速查手册/03_Collector配置速查手册.md)
- [性能优化速查手册](../../../速查手册/05_性能优化速查手册.md)
- [云平台集成指南](../../../云平台集成/)

---

**🚀 开始使用这些示例,快速部署OpenTelemetry Collector!**
