# OpenTelemetry 性能优化指南

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [架构设计](ARCHITECTURE.md) | [集成指南](INTEGRATION_GUIDE.md) | [故障排除](TROUBLESHOOTING.md)
> 最后更新: 2025-09-17

## 性能基准

### 官方基准数据

| 传输方式 | 吞吐量 | CPU使用 | 内存使用 | 网络带宽 |
|----------|--------|---------|----------|----------|
| gRPC | 200k spans/s | 1.2核 | 512MB | 280 Mb/s |
| HTTP | 60k spans/s | 1.5核 | 768MB | 310 Mb/s |

### 硬件要求

- **CPU**: 2核以上
- **内存**: 1GB以上
- **网络**: 100Mbps以上
- **存储**: SSD推荐

## 采样优化

### 采样策略选择

```yaml
# 生产环境推荐
processors:
  probabilistic_sampler:
    sampling_percentage: 1.0  # 1%采样率

# 开发环境
processors:
  probabilistic_sampler:
    sampling_percentage: 100.0  # 100%采样率
```

### 动态采样

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 50000
    expected_new_traces_per_sec: 10
    policies:
      - name: error-rate-policy
        type: rate_limiting
        rate_limiting:
          spans_per_second: 100
      - name: latency-policy
        type: latency
        latency:
          threshold_ms: 1000
```

## 批处理优化

### 批处理配置

```yaml
processors:
  batch:
    timeout: 1s
    send_batch_size: 512
    send_batch_max_size: 2048
    metadata_keys:
      - "service.name"
      - "service.version"
```

### 内存管理

```yaml
processors:
  memory_limiter:
    check_interval: 2s
    limit_mib: 512
    spike_limit_mib: 128
    limit_percentage: 80
    spike_limit_percentage: 95
```

## 网络优化

### 连接池配置

```yaml
exporters:
  otlp:
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

### 压缩配置

```yaml
exporters:
  otlp:
    compression: "gzip"
    timeout: 10s
```

## 存储优化

### 数据保留策略

```yaml
exporters:
  jaeger:
    endpoint: jaeger:14250
    sending_queue:
      queue_size: 1000
    retry_on_failure:
      max_elapsed_time: 300s
```

### 索引优化

```yaml
exporters:
  elasticsearch:
    endpoints: ["http://elasticsearch:9200"]
    index: "otel-traces"
    mapping:
      mode: "ecs"
    bulk_actions: 1000
    bulk_size: 5242880
```

## 应用层优化

### SDK配置

```go
// Go SDK优化
tracerProvider := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter, 
        sdktrace.WithBatchTimeout(time.Second),
        sdktrace.WithMaxExportBatchSize(512),
    ),
    sdktrace.WithSpanLimits(sdktrace.SpanLimits{
        AttributeCountLimit: 128,
        EventCountLimit: 128,
        LinkCountLimit: 128,
    }),
)
```

### 异步处理

```go
// 异步Span处理
tracerProvider := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter),
    sdktrace.WithResource(resource),
)
```

## 监控和调优

### 关键指标

```yaml
# Collector指标
otelcol_receiver_accepted_spans
otelcol_receiver_refused_spans
otelcol_processor_batch_batch_send_size
otelcol_exporter_sent_spans
otelcol_exporter_send_failed_spans
```

### 性能监控

```yaml
service:
  telemetry:
    metrics:
      address: 0.0.0.0:8888
      readers:
        - periodic:
            interval: 10s
```

### 告警规则

```yaml
groups:
- name: performance-alerts
  rules:
  - alert: HighRefusedSpans
    expr: rate(otelcol_receiver_refused_spans[5m]) > 100
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High number of refused spans"
  
  - alert: HighMemoryUsage
    expr: otelcol_memory_usage_bytes / otelcol_memory_limit_bytes > 0.8
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "High memory usage"
```

## 压力测试

### 测试脚本

```bash
# 运行压力测试
./benchmarks/run-rust.ps1 -Loops 10000 -SleepMs 0

# 监控系统资源
top -p $(pgrep otelcol)
```

### 测试指标

- 吞吐量 (spans/second)
- 延迟 (P50, P95, P99)
- 内存使用
- CPU使用
- 网络带宽

## 故障恢复

### 自动恢复

```yaml
exporters:
  otlp:
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
      multiplier: 2.0
```

### 降级策略

```yaml
processors:
  routing:
    from_attribute: "service.name"
    default_exporters: [logging]
    table:
      - value: "critical-service"
        exporters: [jaeger, prometheus]
      - value: "normal-service"
        exporters: [jaeger]
```

## 高级性能优化

### 1. 内存优化策略

#### 内存池管理

```go
// 使用内存池减少GC压力
var spanPool = sync.Pool{
    New: func() interface{} {
        return &Span{
            Attributes: make(map[string]interface{}, 16),
            Events:     make([]Event, 0, 8),
        }
    },
}

func getSpan() *Span {
    return spanPool.Get().(*Span)
}

func putSpan(s *Span) {
    s.Reset()
    spanPool.Put(s)
}
```

#### 内存映射文件

```yaml
# 使用内存映射文件存储大量数据
exporters:
  file:
    path: /tmp/otel-data.bin
    format: binary
    memory_mapped: true
    buffer_size: 64MB
```

### 2. CPU优化策略

#### 并发处理优化

```yaml
# 优化并发处理
processors:
  batch:
    timeout: 100ms
    send_batch_size: 1024
    send_batch_max_size: 2048
    metadata_keys:
      - "service.name"
      - "service.version"

exporters:
  otlp:
    sending_queue:
      enabled: true
      num_consumers: 20
      queue_size: 2000
      storage: "file_storage"
```

#### CPU亲和性设置

```bash
# 设置CPU亲和性
taskset -c 0-3 otelcol --config=config.yaml

# 或使用Docker
docker run --cpuset-cpus="0-3" otel/opentelemetry-collector-contrib:latest
```

### 3. 网络优化策略

#### 连接复用

```yaml
# 优化连接复用
exporters:
  otlp:
    endpoint: "http://collector:4317"
    compression: "gzip"
    timeout: 10s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
```

#### 网络缓冲区优化

```bash
# 优化网络缓冲区
echo 'net.core.rmem_max = 134217728' >> /etc/sysctl.conf
echo 'net.core.wmem_max = 134217728' >> /etc/sysctl.conf
echo 'net.ipv4.tcp_rmem = 4096 87380 134217728' >> /etc/sysctl.conf
echo 'net.ipv4.tcp_wmem = 4096 65536 134217728' >> /etc/sysctl.conf
sysctl -p
```

### 4. 存储优化策略

#### 数据压缩

```yaml
# 启用数据压缩
exporters:
  otlp:
    compression: "gzip"
    compression_level: 6
  
  kafka:
    compression: "gzip"
    compression_level: 6
    batch_size: 1048576
```

#### 存储分层

```yaml
# 实现存储分层
exporters:
  hot_storage:
    type: "jaeger"
    endpoint: "jaeger-hot:14250"
    storage_ttl: "24h"
  
  cold_storage:
    type: "s3"
    bucket: "otel-cold-storage"
    prefix: "traces/"
    storage_ttl: "30d"
```

### 5. 缓存优化策略

#### 多级缓存

```yaml
# 实现多级缓存
processors:
  cache:
    type: "redis"
    endpoint: "redis:6379"
    ttl: "1h"
    max_size: 10000
  
  memory_cache:
    type: "lru"
    max_size: 1000
    ttl: "10m"
```

#### 缓存预热

```go
// 缓存预热策略
func warmupCache() {
    // 预加载常用数据
    commonTraces := getCommonTraces()
    for _, trace := range commonTraces {
        cache.Set(trace.ID, trace, time.Hour)
    }
}
```

## 性能监控和分析

### 1. 实时性能监控

#### 关键指标监控

```yaml
# 关键性能指标
groups:
- name: performance-monitoring
  rules:
  - alert: HighCPUUsage
    expr: rate(otelcol_cpu_usage_percent[5m]) > 80
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High CPU usage detected"
  
  - alert: HighMemoryUsage
    expr: otelcol_memory_usage_bytes / otelcol_memory_limit_bytes > 0.8
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High memory usage detected"
  
  - alert: HighQueueSize
    expr: otelcol_processor_batch_queue_size > 1000
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "High queue size detected"
```

#### 性能分析工具

```bash
#!/bin/bash
# performance-analysis.sh

echo "=== OpenTelemetry 性能分析 ==="

# 收集性能数据
echo "收集CPU使用情况..."
top -p $(pgrep otelcol) -n 1 -b > cpu-usage.txt

echo "收集内存使用情况..."
ps aux | grep otelcol > memory-usage.txt

echo "收集网络统计..."
ss -tuln | grep 4317 > network-stats.txt

echo "收集Collector指标..."
curl -s http://localhost:13133/metrics > collector-metrics.txt

echo "分析性能瓶颈..."
python analyze-performance.py cpu-usage.txt memory-usage.txt network-stats.txt collector-metrics.txt

echo "=== 性能分析完成 ==="
```

### 2. 性能基准测试

#### 自动化基准测试

```bash
#!/bin/bash
# benchmark-test.sh

echo "=== OpenTelemetry 基准测试 ==="

# 测试不同负载下的性能
for load in 1000 5000 10000 20000; do
    echo "测试负载: $load spans/second"
    
    # 启动测试
    ./benchmarks/run-rust.ps1 -Loops $load -SleepMs 0 &
    TEST_PID=$!
    
    # 监控性能
    start_time=$(date +%s)
    while kill -0 $TEST_PID 2>/dev/null; do
        cpu_usage=$(ps -p $TEST_PID -o %cpu= | tr -d ' ')
        memory_usage=$(ps -p $TEST_PID -o %mem= | tr -d ' ')
        echo "$(date): CPU: ${cpu_usage}%, Memory: ${memory_usage}%"
        sleep 1
    done
    end_time=$(date +%s)
    
    duration=$((end_time - start_time))
    echo "负载 $load 完成，耗时: ${duration}秒"
done

echo "=== 基准测试完成 ==="
```

#### 性能对比测试

```bash
#!/bin/bash
# performance-comparison.sh

echo "=== OpenTelemetry 性能对比测试 ==="

# 测试不同配置的性能
configs=("minimal.yaml" "optimized.yaml" "high-performance.yaml")

for config in "${configs[@]}"; do
    echo "测试配置: $config"
    
    # 启动Collector
    otelcol --config="$config" &
    COLLECTOR_PID=$!
    sleep 10
    
    # 运行性能测试
    ./benchmarks/run-rust.ps1 -Loops 10000 -SleepMs 0
    
    # 收集结果
    curl -s http://localhost:13133/metrics > "results-${config}.txt"
    
    # 停止Collector
    kill $COLLECTOR_PID
    sleep 5
done

echo "=== 性能对比测试完成 ==="
```

### 3. 性能调优建议

#### 基于负载的调优

```yaml
# 低负载配置 (< 1k spans/s)
processors:
  batch:
    timeout: 1s
    send_batch_size: 256
    send_batch_max_size: 512

# 中等负载配置 (1k-10k spans/s)
processors:
  batch:
    timeout: 500ms
    send_batch_size: 512
    send_batch_max_size: 1024

# 高负载配置 (> 10k spans/s)
processors:
  batch:
    timeout: 100ms
    send_batch_size: 1024
    send_batch_max_size: 2048
```

#### 基于硬件的调优

```yaml
# 低配置硬件 (2核4GB)
processors:
  memory_limiter:
    limit_mib: 512
    spike_limit_mib: 128
  batch:
    timeout: 1s
    send_batch_size: 256

# 中等配置硬件 (4核8GB)
processors:
  memory_limiter:
    limit_mib: 1024
    spike_limit_mib: 256
  batch:
    timeout: 500ms
    send_batch_size: 512

# 高配置硬件 (8核16GB+)
processors:
  memory_limiter:
    limit_mib: 2048
    spike_limit_mib: 512
  batch:
    timeout: 100ms
    send_batch_size: 1024
```

## 性能优化工具

### 1. 性能分析工具

#### Go性能分析

```bash
# 启动性能分析
go tool pprof http://localhost:13133/debug/pprof/profile

# 内存分析
go tool pprof http://localhost:13133/debug/pprof/heap

# 协程分析
go tool pprof http://localhost:13133/debug/pprof/goroutine
```

#### 系统性能分析

```bash
# 使用perf分析
perf record -p $(pgrep otelcol) -g sleep 30
perf report

# 使用strace跟踪系统调用
strace -p $(pgrep otelcol) -o otelcol-strace.log

# 使用tcpdump分析网络
tcpdump -i any port 4317 -w otelcol-network.pcap
```

### 2. 性能监控工具

#### 自定义监控脚本

```bash
#!/bin/bash
# performance-monitor.sh

while true; do
    # 收集性能数据
    timestamp=$(date +%s)
    cpu_usage=$(ps aux | grep otelcol | grep -v grep | awk '{print $3}')
    memory_usage=$(ps aux | grep otelcol | grep -v grep | awk '{print $4}')
    network_io=$(cat /proc/net/dev | grep eth0 | awk '{print $2,$10}')
    
    # 输出到日志
    echo "$timestamp,$cpu_usage,$memory_usage,$network_io" >> performance.log
    
    sleep 1
done
```

#### Grafana仪表盘

```json
{
  "dashboard": {
    "title": "OpenTelemetry Performance",
    "panels": [
      {
        "title": "CPU Usage",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otelcol_cpu_usage_percent[5m])",
            "legendFormat": "CPU Usage %"
          }
        ]
      },
      {
        "title": "Memory Usage",
        "type": "graph",
        "targets": [
          {
            "expr": "otelcol_memory_usage_bytes",
            "legendFormat": "Memory Usage"
          }
        ]
      },
      {
        "title": "Throughput",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otelcol_receiver_accepted_spans[5m])",
            "legendFormat": "Spans/sec"
          }
        ]
      }
    ]
  }
}
```

## 最佳实践

### 1. 配置优化

- 根据负载调整批处理大小
- 设置合适的内存限制
- 配置合理的采样率
- 使用连接池管理连接
- 启用数据压缩

### 2. 监控设置

- 监控关键性能指标
- 设置性能告警
- 定期进行压力测试
- 建立性能基线
- 持续监控性能趋势

### 3. 容量规划

- 根据业务增长规划容量
- 预留足够的系统资源
- 建立扩容流程
- 定期评估容量需求
- 实施弹性伸缩

### 4. 故障预防

- 定期检查系统健康
- 建立故障恢复流程
- 进行灾难恢复演练
- 实施监控告警
- 建立性能优化流程

### 5. 持续优化

- 定期进行性能评估
- 实施性能优化措施
- 监控优化效果
- 建立性能优化知识库
- 分享优化经验
