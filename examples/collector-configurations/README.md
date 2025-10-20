# 🔧 OpenTelemetry Collector配置示例集

> **目的**: 提供生产级Collector配置模板，涵盖常见使用场景  
> **版本**: OpenTelemetry Collector Contrib 0.91+  
> **配套文档**: [数据模型与语义转换完整指南](../../📊_数据模型与语义转换完整指南_2025_10_20.md) | [可视化图表](../../📊_OTLP数据生命周期可视化图表_2025_10_20.md)

---

## 📋 配置文件清单

| 文件 | 场景 | 复杂度 | 推荐用途 |
|------|------|--------|---------|
| [01-basic-pipeline.yaml](01-basic-pipeline.yaml) | 基础Pipeline | ⭐☆☆☆☆ | 开发/测试环境 |
| [02-tail-sampling.yaml](02-tail-sampling.yaml) | 智能采样 | ⭐⭐⭐☆☆ | 生产环境（高吞吐） |
| [03-span-metrics.yaml](03-span-metrics.yaml) | Span→Metric | ⭐⭐☆☆☆ | 长期趋势分析 |
| [04-multi-backend.yaml](04-multi-backend.yaml) | 多后端导出 | ⭐⭐⭐⭐☆ | 生产环境（统一平台） |
| [05-attributes-processing.yaml](05-attributes-processing.yaml) | 数据清洗 | ⭐⭐⭐⭐⭐ | 合规要求（PII脱敏） |

---

## 🚀 快速开始

### 前置条件

1. **Docker**

   ```bash
   docker --version
   ```

2. **下载Collector镜像**

   ```bash
   # Contrib版本（推荐，包含所有processors）
   docker pull otel/opentelemetry-collector-contrib:latest
   
   # 核心版本（精简）
   docker pull otel/opentelemetry-collector:latest
   ```

### 使用方法

#### 方法1: Docker运行（推荐）

```bash
# 运行基础配置
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  -p 8888:8888 \
  -v $(pwd)/01-basic-pipeline.yaml:/etc/otel-collector-config.yaml \
  otel/opentelemetry-collector-contrib:latest \
  --config=/etc/otel-collector-config.yaml
```

#### 方法2: Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./02-tail-sampling.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Metrics
      - "8889:8889"   # Prometheus exporter
      - "13133:13133" # Health check
    depends_on:
      - jaeger
      - prometheus
  
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
  
  prometheus:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9090:9090"
```

启动:

```bash
docker-compose up -d
```

#### 方法3: Kubernetes部署

```yaml
# otel-collector-deployment.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
data:
  otel-collector-config.yaml: |
    # 粘贴配置文件内容
    
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
spec:
  replicas: 3
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
        command: ["--config=/etc/otel-collector-config.yaml"]
        volumeMounts:
        - name: config
          mountPath: /etc/otel-collector-config.yaml
          subPath: otel-collector-config.yaml
        ports:
        - containerPort: 4317
        - containerPort: 4318
        - containerPort: 8888
      volumes:
      - name: config
        configMap:
          name: otel-collector-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
spec:
  selector:
    app: otel-collector
  ports:
    - name: grpc
      port: 4317
      targetPort: 4317
    - name: http
      port: 4318
      targetPort: 4318
    - name: metrics
      port: 8888
      targetPort: 8888
```

部署:

```bash
kubectl apply -f otel-collector-deployment.yaml
```

---

## 📊 配置文件详解

### 1. 基础Pipeline配置 (01-basic-pipeline.yaml)

**适用场景**:

- 开发/测试环境
- 学习OpenTelemetry
- 单后端简单场景

**核心功能**:

```yaml
receivers:
  otlp/grpc:       # gRPC接收器
  otlp/http:       # HTTP接收器

processors:
  batch:           # 批处理优化
  memory_limiter:  # 防止OOM

exporters:
  jaeger:          # 导出到Jaeger
  logging:         # 调试输出
```

**性能优化**:

- 批处理大小: 512 spans
- 超时: 1秒
- 内存限制: 512MB

**启动命令**:

```bash
docker run -d --name otel-collector \
  -p 4317:4317 -p 4318:4318 -p 8888:8888 \
  --link jaeger:jaeger \
  -v $(pwd)/01-basic-pipeline.yaml:/etc/otel-collector-config.yaml \
  otel/opentelemetry-collector-contrib:latest \
  --config=/etc/otel-collector-config.yaml
```

---

### 2. 尾部采样配置 (02-tail-sampling.yaml)

**适用场景**:

- 生产环境（高吞吐量）
- 需要智能采样
- 成本优化

**核心功能**:

```yaml
processors:
  tail_sampling:
    policies:
      - 100% 保留错误trace
      - 100% 保留慢trace (>2s)
      - 100% 保留VIP用户
      - 100% 保留高风险交易
      - 100% 保留欺诈检测
      - 1% 采样普通流量
```

**采样效果**:

```text
输入: 10M traces/天

过滤后: 971K traces/天 (减少90.3%)

但保留了:
✅ 100%的错误trace
✅ 100%的慢trace
✅ 100%的VIP用户trace
✅ 100%的高风险交易
✅ 99.9%的关键业务信息
```

**成本节省**:

```text
存储成本: $1M/月 → $97K/月
节省: 90.3% ($903K/月)
```

**配置要点**:

- `decision_wait: 10s` - 等待完整trace
- `num_traces: 100000` - 内存中保留trace数
- 策略按顺序评估，匹配第一个即采样

---

### 3. Span转Metric配置 (03-span-metrics.yaml)

**适用场景**:

- 需要长期趋势分析
- Prometheus告警
- 减少Trace存储成本

**核心功能**:

```yaml
processors:
  spanmetrics:
    namespace: span.metrics
    dimensions:        # 聚合维度
      - http.method
      - http.status_code
      - myshop.user.tier
      - fintech.risk.level
    histogram:
      buckets: [10ms, 50ms, 100ms, 200ms, 500ms, 1s, 2s, 5s, 10s]
```

**生成的Metric**:

1. **调用总数 (Counter)**:

   ```promql
   span_metrics_calls_total{
     service_name="order-service",
     http_method="POST",
     http_status_code="200",
     myshop_user_tier="gold"
   }
   ```

2. **延迟分布 (Histogram)**:

   ```promql
   span_metrics_duration_milliseconds_bucket{
     service_name="order-service",
     http_method="POST",
     le="100"
   }
   ```

**常用PromQL查询**:

```promql
# P99延迟
histogram_quantile(0.99, 
  sum by (le, service_name) (
    rate(span_metrics_duration_milliseconds_bucket[5m])
  )
)

# 错误率
sum(rate(span_metrics_calls_total{http_status_code=~"5.."}[5m])) /
sum(rate(span_metrics_calls_total[5m]))

# QPS
sum(rate(span_metrics_calls_total[1m])) by (service_name)

# 按用户等级的请求分布
sum(rate(span_metrics_calls_total[5m])) by (myshop_user_tier)
```

**Prometheus抓取配置**:

```yaml
# prometheus.yml
scrape_configs:
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8889']
```

---

### 4. 多后端导出配置 (04-multi-backend.yaml)

**适用场景**:

- 生产环境
- 统一可观测性平台
- 不同信号路由到不同后端

**核心功能**:

```yaml
exporters:
  jaeger:         # Trace → Jaeger
  prometheus:     # Metric → Prometheus
  elasticsearch:  # Log → Elasticsearch
  kafka:          # 消息队列缓冲
  otlp/remote:    # 转发到远程Collector
```

**数据流向**:

```text
Application
  ↓ OTLP
Collector
  ├─ Traces → Jaeger + Elasticsearch + Kafka
  ├─ Metrics → Prometheus
  └─ Logs → Elasticsearch
```

**高级特性**:

- 资源检测 (`resourcedetection`): 自动添加云平台属性
- 属性清洗 (`attributes/cleanup`): 删除敏感数据、PII哈希
- 重试机制: 失败自动重试，exponential backoff
- 负载均衡: Round Robin分发到多个后端

**K8s资源检测示例**:

```yaml
# 自动添加的属性
k8s.cluster.name: "prod-cluster"
k8s.namespace.name: "default"
k8s.pod.name: "order-service-7d4f8b9c-xk2lp"
k8s.deployment.name: "order-service"
cloud.provider: "aws"
cloud.region: "us-east-1"
```

---

### 5. 高级属性处理配置 (05-attributes-processing.yaml)

**适用场景**:

- 合规要求（GDPR、CCPA、PCI-DSS）
- PII数据脱敏
- 复杂数据转换

**核心功能**:

#### 5.1 敏感数据删除

```yaml
attributes/remove_sensitive:
  actions:
    - key: http.request.header.authorization
      action: delete
    - key: credit_card.number
      action: delete
```

#### 5.2 PII哈希化

```yaml
attributes/hash_pii:
  actions:
    - key: user.email
      action: hash  # SHA256
    - key: user.phone
      action: hash
    - key: client.ip
      action: hash  # GDPR要求
```

#### 5.3 属性重命名

```yaml
attributes/rename:
  actions:
    - key: http.method
      from_attribute: http.request.method
      action: update
```

#### 5.4 正则提取

```yaml
attributes/extract:
  actions:
    # 从URL提取API版本
    - key: http.target
      pattern: ^/api/v(\d+)/.*
      action: extract
      to_attribute: api.version
```

#### 5.5 复杂转换

```yaml
transform:
  traces:
    - context: span
      statements:
        # 是否成功
        - set(attributes["request.success"], 
              attributes["http.status_code"] < 400)
        
        # 高额交易分类
        - set(attributes["fintech.transaction.category"], 
              attributes["fintech.transaction.amount"] > 10000 ? 
              "high_value" : "standard")
```

**处理示例**:

输入:

```text
user.email: "user@example.com"
credit_card.number: "1234-5678-9012-3456"
http.request.method: "POST"
http.target: "/api/v2/orders"
myshop.order.total_amount: 99.99
```

输出:

```text
user.email: "a1b2c3d4e5f6..." (SHA256哈希)
# credit_card.number已删除
http.method: "POST" (重命名)
http.target: "/api/v2/orders"
api.version: "2" (正则提取)
myshop.order.total_amount: 100 (取整)
request.success: true (派生属性)
```

**合规检查清单**:

- ✅ 信用卡号删除（PCI-DSS要求）
- ✅ PII哈希化（GDPR/CCPA要求）
- ✅ 健康检查过滤（减少噪音）
- ✅ 属性标准化（便于查询）

---

## 🎯 配置选择指南

### 按场景选择

| 场景 | 推荐配置 | 说明 |
|------|---------|------|
| **开发环境** | 01-basic-pipeline | 简单直接，易于调试 |
| **测试环境** | 01 + 03 (Span Metrics) | 性能测试时查看Metric |
| **小规模生产** | 01 + 04 (多后端) | <1M traces/天 |
| **大规模生产** | 02 + 03 + 04 | 智能采样 + Metric + 多后端 |
| **金融/医疗** | 02 + 04 + 05 | 合规要求 + PII脱敏 |

### 按吞吐量选择

| 吞吐量 | 配置组合 | 采样率 |
|--------|---------|--------|
| **<10K traces/天** | 01-basic | 100% |
| **10K-100K/天** | 01 + 03 | 50% |
| **100K-1M/天** | 02 + 03 | 10% |
| **>1M/天** | 02 + 03 + 04 + Kafka | 1-5% |

### 按预算选择

| 月预算 | 配置策略 | 说明 |
|--------|---------|------|
| **<$1K** | 01 + 高采样率 | 小型项目 |
| **$1K-$10K** | 02 (尾部采样) | 智能采样节省成本 |
| **>$10K** | 02 + 03 + Kafka | 企业级，高可用 |

---

## 🛠️ 故障排查

### 问题1: Collector启动失败

**错误信息**:

```text
Error: cannot load configuration: ...
```

**解决方案**:

1. 检查YAML语法:

   ```bash
   yamllint 01-basic-pipeline.yaml
   ```

2. 验证配置:

   ```bash
   docker run --rm \
     -v $(pwd)/01-basic-pipeline.yaml:/etc/otel-collector-config.yaml \
     otel/opentelemetry-collector-contrib:latest \
     validate --config=/etc/otel-collector-config.yaml
   ```

---

### 问题2: 数据未导出

**检查步骤**:

1. 检查Collector健康状态:

   ```bash
   curl http://localhost:13133/
   ```

2. 查看Collector日志:

   ```bash
   docker logs otel-collector
   ```

3. 检查后端连接:

   ```bash
   # 检查Jaeger
   curl http://localhost:16686/
   
   # 检查Prometheus
   curl http://localhost:9090/
   ```

4. 查看Metrics:

   ```bash
   curl http://localhost:8888/metrics
   ```

   关键指标:
   - `otelcol_receiver_accepted_spans`: 接收的spans
   - `otelcol_exporter_sent_spans`: 导出的spans
   - `otelcol_processor_batch_batch_send_size`: 批处理大小

---

### 问题3: 内存不足

**错误信息**:

```text
Memory limiter processor is refusing data
```

**解决方案**:

```yaml
processors:
  memory_limiter:
    limit_mib: 2048     # 增大限制
    spike_limit_mib: 512
```

或增加Docker内存:

```bash
docker run --memory=2g ...
```

---

## 📈 性能优化建议

### 1. 批处理优化

```yaml
batch:
  timeout: 1s           # 低延迟: 100ms, 高吞吐: 5s
  send_batch_size: 512  # 低吞吐: 128, 高吞吐: 2048
```

### 2. 并发处理

```yaml
receivers:
  otlp/grpc:
    protocols:
      grpc:
        max_recv_msg_size_mib: 16       # 增大消息大小
        max_concurrent_streams: 100     # 增加并发流
```

### 3. 资源限制

```yaml
memory_limiter:
  check_interval: 1s
  limit_mib: 2048       # 根据实际情况调整
  spike_limit_mib: 512
```

### 4. 队列配置

```yaml
exporters:
  jaeger:
    sending_queue:
      enabled: true
      num_consumers: 10   # 增加消费者
      queue_size: 5000    # 增大队列
```

---

## 🔗 相关资源

### 配套文档

| 文档 | 链接 |
|------|------|
| **数据模型指南** | [📊_数据模型与语义转换完整指南_2025_10_20.md](../../📊_数据模型与语义转换完整指南_2025_10_20.md) |
| **可视化图表** | [📊_OTLP数据生命周期可视化图表_2025_10_20.md](../../📊_OTLP数据生命周期可视化图表_2025_10_20.md) (查看Collector处理流程图) |
| **对标分析报告** | [📊_OTLP项目2025年10月20日全面对标分析报告.md](../../📊_OTLP项目2025年10月20日全面对标分析报告.md) |

### 官方文档

- [Collector文档](https://opentelemetry.io/docs/collector/)
- [Collector配置参考](https://opentelemetry.io/docs/collector/configuration/)
- [Processors参考](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor)
- [Exporters参考](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter)

### 社区资源

- [GitHub仓库](https://github.com/open-telemetry/opentelemetry-collector)
- [Slack频道](https://cloud-native.slack.com/archives/C01N6P7KR6W)
- [示例配置](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/examples)

---

**创建时间**: 2025年10月20日  
**作者**: OTLP项目团队  
**版本**: v1.0.0  
**Collector版本**: 0.91+

---

**🔧 Collector配置让数据处理如此简单！** ✨
