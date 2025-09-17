# OpenTelemetry 集成指南

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [API参考](API_REFERENCE.md) | [部署指南](DEPLOYMENT_GUIDE.md) | [性能优化](PERFORMANCE_GUIDE.md)
> 最后更新: 2025-09-17

## 后端系统集成

### 1. Jaeger集成

```yaml
exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
```

### 2. Prometheus集成

```yaml
exporters:
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: "otel"
    const_labels:
      environment: "production"
      service: "collector"
    send_timestamps: true
    metric_relabeling:
      - source_labels: [__name__]
        regex: "http_requests_total"
        target_label: "metric_type"
        replacement: "counter"
```

### 3. Elasticsearch集成

```yaml
exporters:
  elasticsearch:
    endpoints: ["http://elasticsearch:9200"]
    index: "otel-traces"
    mapping:
      mode: "ecs"
    bulk_actions: 1000
    bulk_size: 5242880
    timeout: 60s
    retry:
      enabled: true
      max_requests: 3
      initial_interval: 100ms
      max_interval: 1s
```

### 4. Kafka集成

```yaml
exporters:
  kafka:
    brokers: ["kafka:9092"]
    topic: "otel-data"
    encoding: "json"
    metadata:
      full: true
      retry:
        max: 3
        backoff: 1s
    compression: "gzip"
    required_acks: 1
```

## 云平台集成

### 1. AWS集成

```yaml
exporters:
  awsxray:
    region: "us-west-2"
    role_arn: "arn:aws:iam::123456789012:role/otel-collector"
    endpoint: "https://xray.us-west-2.amazonaws.com"
  
  awscloudwatch:
    region: "us-west-2"
    namespace: "OpenTelemetry"
    log_group_name: "/aws/otel/collector"
    log_stream_name: "otel-collector"
```

### 2. GCP集成

```yaml
exporters:
  googlecloud:
    project: "my-project"
    location: "us-central1"
    credentials_file: "/path/to/credentials.json"
    metric:
      prefix: "custom.googleapis.com/opentelemetry"
    trace:
      project_id: "my-project"
```

### 3. Azure集成

```yaml
exporters:
  azuremonitor:
    connection_string: "${AZURE_MONITOR_CONNECTION_STRING}"
    instrumentation_key: "${AZURE_MONITOR_INSTRUMENTATION_KEY}"
```

## 框架集成

### 1. Spring Boot集成

```xml
<dependency>
    <groupId>io.opentelemetry</groupId>
    <artifactId>opentelemetry-spring-boot-starter</artifactId>
    <version>1.0.0</version>
</dependency>
```

```yaml
# application.yml
management:
  tracing:
    sampling:
      probability: 1.0
  metrics:
    export:
      prometheus:
        enabled: true
```

### 2. Django集成

```python
# settings.py
INSTALLED_APPS = [
    'django.contrib.admin',
    'django.contrib.auth',
    'django.contrib.contenttypes',
    'django.contrib.sessions',
    'django.contrib.messages',
    'django.contrib.staticfiles',
    'opentelemetry.instrumentation.django',
]

# 中间件配置
MIDDLEWARE = [
    'opentelemetry.instrumentation.django.middleware.DjangoMiddleware',
    'django.middleware.security.SecurityMiddleware',
    # ... 其他中间件
]
```

### 3. Express.js集成

```javascript
const { NodeSDK } = require('@opentelemetry/auto-instrumentations-node');
const { getNodeAutoInstrumentations } = require('@opentelemetry/auto-instrumentations-node');

const sdk = new NodeSDK({
  instrumentations: [getNodeAutoInstrumentations()],
});

sdk.start();
```

## 数据库集成

### 1. MySQL集成

```yaml
processors:
  attributes:
    actions:
      - key: "db.system"
        action: "insert"
        value: "mysql"
      - key: "db.connection_string"
        action: "delete"
```

### 2. PostgreSQL集成

```yaml
processors:
  attributes:
    actions:
      - key: "db.system"
        action: "insert"
        value: "postgresql"
      - key: "db.statement"
        action: "hash"
```

### 3. Redis集成

```yaml
processors:
  attributes:
    actions:
      - key: "db.system"
        action: "insert"
        value: "redis"
      - key: "db.redis.database_index"
        action: "insert"
        value: "0"
```

## 消息队列集成

### 1. Kafka集成

```yaml
processors:
  attributes:
    actions:
      - key: "messaging.system"
        action: "insert"
        value: "kafka"
      - key: "messaging.destination"
        action: "insert"
        from_attribute: "kafka.topic"
```

### 2. RabbitMQ集成

```yaml
processors:
  attributes:
    actions:
      - key: "messaging.system"
        action: "insert"
        value: "rabbitmq"
      - key: "messaging.destination"
        action: "insert"
        from_attribute: "rabbitmq.queue"
```

### 3. NATS集成

```yaml
processors:
  attributes:
    actions:
      - key: "messaging.system"
        action: "insert"
        value: "nats"
      - key: "messaging.destination"
        action: "insert"
        from_attribute: "nats.subject"
```

## 监控系统集成

### 1. Grafana集成

```yaml
# Grafana数据源配置
datasources:
  - name: Prometheus
    type: prometheus
    url: http://prometheus:9090
    access: proxy
    isDefault: true
  
  - name: Jaeger
    type: jaeger
    url: http://jaeger:16686
    access: proxy
```

### 2. Datadog集成

```yaml
exporters:
  datadog:
    api:
      key: "${DATADOG_API_KEY}"
      site: "datadoghq.com"
    traces:
      ignore_resources: ["health_check"]
    metrics:
      namespace: "otel"
```

### 3. New Relic集成

```yaml
exporters:
  newrelic:
    apikey: "${NEW_RELIC_API_KEY}"
    endpoint: "https://trace-api.newrelic.com/trace/v1"
    timeout: 30s
```

## 自定义集成

### 1. 自定义导出器

```go
package main

import (
    "context"
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/exporter"
)

type customExporter struct {
    config *Config
}

func (e *customExporter) Start(ctx context.Context, host component.Host) error {
    // 初始化导出器
    return nil
}

func (e *customExporter) Shutdown(ctx context.Context) error {
    // 清理资源
    return nil
}

func (e *customExporter) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 处理追踪数据
    return nil
}

func (e *customExporter) ConsumeMetrics(ctx context.Context, md pmetric.Metrics) error {
    // 处理指标数据
    return nil
}

func (e *customExporter) ConsumeLogs(ctx context.Context, ld plog.Logs) error {
    // 处理日志数据
    return nil
}
```

### 2. 自定义处理器

```go
package main

import (
    "context"
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/processor"
)

type customProcessor struct {
    config *Config
}

func (p *customProcessor) Start(ctx context.Context, host component.Host) error {
    // 初始化处理器
    return nil
}

func (p *customProcessor) Shutdown(ctx context.Context) error {
    // 清理资源
    return nil
}

func (p *customProcessor) ProcessTraces(ctx context.Context, td ptrace.Traces) (ptrace.Traces, error) {
    // 处理追踪数据
    return td, nil
}

func (p *customProcessor) ProcessMetrics(ctx context.Context, md pmetric.Metrics) (pmetric.Metrics, error) {
    // 处理指标数据
    return md, nil
}

func (p *customProcessor) ProcessLogs(ctx context.Context, ld plog.Logs) (plog.Logs, error) {
    // 处理日志数据
    return ld, nil
}
```

## 高级集成场景

### 1. 微服务架构集成

#### 服务网格集成

```yaml
# Istio配置
apiVersion: networking.istio.io/v1alpha3
kind: EnvoyFilter
metadata:
  name: otel-tracing
spec:
  configPatches:
  - applyTo: HTTP_FILTER
    match:
      context: SIDECAR_INBOUND
      listener:
        filterChain:
          filter:
            name: "envoy.filters.network.http_connection_manager"
    patch:
      operation: INSERT_BEFORE
      value:
        name: envoy.filters.http.otel_tracing
        typed_config:
          "@type": type.googleapis.com/opentelemetry.proto.extension.v1.OtelTracingConfig
          collector_cluster: otel-collector
          service_name: "{{ .Workload.Name }}"
```

#### 服务发现集成

```yaml
# Consul服务发现
exporters:
  otlp:
    endpoint: "consul://otel-collector:4317"
    service_discovery:
      type: consul
      consul:
        address: "consul:8500"
        service: "otel-collector"
        tags: ["otel", "collector"]
```

### 2. 容器化集成

#### Docker集成

```dockerfile
# Dockerfile
FROM golang:1.21-alpine AS builder
WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download
COPY . .
RUN go build -o app .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/app .
COPY --from=builder /app/otel-config.yaml .

# 设置OpenTelemetry环境变量
ENV OTEL_SERVICE_NAME=my-app
ENV OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
ENV OTEL_EXPORTER_OTLP_PROTOCOL=grpc

CMD ["./app"]
```

#### Kubernetes集成

```yaml
# Kubernetes Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
      annotations:
        sidecar.istio.io/inject: "true"
    spec:
      containers:
      - name: my-app
        image: my-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_SERVICE_NAME
          value: "my-app"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector.observability.svc.cluster.local:4317"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "k8s.namespace.name=$(KUBERNETES_NAMESPACE),k8s.pod.name=$(KUBERNETES_POD_NAME)"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
```

### 3. 云原生集成

#### AWS EKS集成

```yaml
# AWS EKS配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: aws-otel-config
  namespace: observability
data:
  otel-collector.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
    processors:
      batch:
        timeout: 1s
        send_batch_size: 512
      resource:
        attributes:
          - key: cloud.provider
            value: aws
            action: insert
          - key: cloud.region
            value: ${AWS_REGION}
            action: insert
    exporters:
      awsxray:
        region: ${AWS_REGION}
        role_arn: ${AWS_ROLE_ARN}
      awscloudwatch:
        region: ${AWS_REGION}
        namespace: OpenTelemetry
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [resource, batch]
          exporters: [awsxray]
        metrics:
          receivers: [otlp]
          processors: [resource, batch]
          exporters: [awscloudwatch]
```

#### GCP GKE集成

```yaml
# GCP GKE配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: gcp-otel-config
  namespace: observability
data:
  otel-collector.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
    processors:
      batch:
        timeout: 1s
        send_batch_size: 512
      resource:
        attributes:
          - key: cloud.provider
            value: gcp
            action: insert
          - key: cloud.region
            value: ${GCP_REGION}
            action: insert
    exporters:
      googlecloud:
        project: ${GCP_PROJECT}
        location: ${GCP_REGION}
        credentials_file: /etc/gcp/credentials.json
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [resource, batch]
          exporters: [googlecloud]
        metrics:
          receivers: [otlp]
          processors: [resource, batch]
          exporters: [googlecloud]
```

### 4. 企业级集成

#### 企业服务总线集成

```yaml
# ESB集成配置
exporters:
  kafka:
    brokers: ["kafka-cluster:9092"]
    topic: "otel-data"
    encoding: "json"
    metadata:
      full: true
      retry:
        max: 3
        backoff: 1s
    compression: "gzip"
    required_acks: 1
    partitioner:
      type: "round_robin"
```

#### 企业监控平台集成

```yaml
# 企业监控平台集成
exporters:
  datadog:
    api:
      key: "${DATADOG_API_KEY}"
      site: "datadoghq.com"
    traces:
      ignore_resources: ["health_check", "ping"]
    metrics:
      namespace: "opentelemetry"
      tags:
        - "env:production"
        - "team:platform"
  
  newrelic:
    apikey: "${NEW_RELIC_API_KEY}"
    endpoint: "https://trace-api.newrelic.com/trace/v1"
    timeout: 30s
    headers:
      "User-Agent": "OpenTelemetry-Collector/1.0.0"
```

### 5. 边缘计算集成

#### 边缘节点集成

```yaml
# 边缘节点配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 5s
    send_batch_size: 256
  memory_limiter:
    limit_mib: 128
    spike_limit_mib: 32

exporters:
  otlp:
    endpoint: "https://central-collector.company.com:4317"
    tls:
      insecure: false
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
  logging:
    loglevel: error

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp, logging]
```

### 6. 多租户集成

#### 租户隔离配置

```yaml
# 多租户配置
processors:
  routing:
    from_attribute: "tenant.id"
    default_exporters: [logging]
    table:
      - value: "tenant-a"
        exporters: [jaeger-tenant-a, prometheus-tenant-a]
      - value: "tenant-b"
        exporters: [jaeger-tenant-b, prometheus-tenant-b]

exporters:
  jaeger-tenant-a:
    endpoint: jaeger-tenant-a:14250
    tls:
      insecure: true
  jaeger-tenant-b:
    endpoint: jaeger-tenant-b:14250
    tls:
      insecure: true
  prometheus-tenant-a:
    endpoint: "0.0.0.0:8889"
    namespace: "tenant_a"
  prometheus-tenant-b:
    endpoint: "0.0.0.0:8890"
    namespace: "tenant_b"
```

## 集成测试

### 1. 单元测试

```go
// 集成测试示例
func TestOTLPIntegration(t *testing.T) {
    // 创建测试Collector
    collector := startTestCollector(t)
    defer collector.Stop()
    
    // 创建测试应用
    app := createTestApp(t, collector.Endpoint())
    defer app.Stop()
    
    // 发送测试数据
    app.SendTestTraces()
    
    // 验证数据接收
    traces := collector.GetReceivedTraces()
    assert.Len(t, traces, 1)
    assert.Equal(t, "test-operation", traces[0].Name)
}
```

### 2. 集成测试

```bash
#!/bin/bash
# integration-test.sh

echo "=== OpenTelemetry 集成测试 ==="

# 启动测试环境
docker-compose -f docker-compose.test.yml up -d

# 等待服务启动
sleep 30

# 运行测试应用
go run test-app.go

# 验证数据
curl -s http://localhost:16686/api/traces | jq '.data | length'

# 清理环境
docker-compose -f docker-compose.test.yml down

echo "=== 集成测试完成 ==="
```

### 3. 性能测试

```bash
#!/bin/bash
# performance-test.sh

echo "=== OpenTelemetry 性能测试 ==="

# 启动性能测试环境
docker-compose -f docker-compose.perf.yml up -d

# 运行性能测试
./benchmarks/run-rust.ps1 -Loops 100000 -SleepMs 0

# 收集性能指标
curl -s http://localhost:13133/metrics > performance-metrics.txt

# 分析结果
python analyze-performance.py performance-metrics.txt

# 清理环境
docker-compose -f docker-compose.perf.yml down

echo "=== 性能测试完成 ==="
```

## 最佳实践

### 1. 集成策略

- **渐进式集成**: 逐步集成各个组件
- **测试驱动**: 先测试后集成
- **监控集成**: 集成后立即监控
- **版本控制**: 使用版本控制管理集成配置
- **文档化**: 详细记录集成过程

### 2. 配置管理

- **环境隔离**: 不同环境使用不同配置
- **版本控制**: 使用版本控制管理配置
- **配置验证**: 集成前验证配置
- **配置中心**: 使用配置中心管理配置
- **热重载**: 支持配置热重载

### 3. 性能优化

- **批处理**: 使用批处理提高性能
- **异步处理**: 使用异步处理减少延迟
- **资源限制**: 设置合理的资源限制
- **连接池**: 使用连接池管理连接
- **压缩**: 启用数据压缩

### 4. 故障处理

- **重试机制**: 实现重试机制
- **降级策略**: 实现降级策略
- **监控告警**: 设置监控和告警
- **熔断器**: 使用熔断器防止级联故障
- **健康检查**: 实现健康检查

### 5. 安全考虑

- **传输加密**: 使用TLS加密传输
- **认证授权**: 实现认证和授权
- **数据脱敏**: 过滤敏感数据
- **访问控制**: 实施访问控制
- **审计日志**: 记录审计日志

### 6. 运维管理

- **自动化部署**: 实现自动化部署
- **监控告警**: 设置监控和告警
- **日志管理**: 集中管理日志
- **备份恢复**: 实现备份和恢复
- **容量规划**: 进行容量规划
