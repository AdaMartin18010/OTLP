# OTLP (OpenTelemetry Protocol) 概览

## 概述

OTLP (OpenTelemetry Protocol) 是OpenTelemetry项目定义的标准遥测数据传输协议。它提供了统一的、供应商中立的协议，用于传输traces、metrics和logs数据。

## 核心特性

### 1. 统一协议

- **单一协议**: 支持traces、metrics、logs三种信号类型
- **标准化**: 基于Protocol Buffers定义的数据模型
- **版本化**: 支持向后兼容的版本管理

### 2. 双传输模式

- **gRPC**: 高性能二进制传输，默认端口4317
- **HTTP/Protobuf**: 基于HTTP的传输，默认端口4318
- **JSON**: 人类可读格式，用于调试

### 3. 供应商中立

- **无厂商锁定**: 不绑定任何特定的APM厂商
- **开放标准**: CNCF毕业项目，社区驱动
- **互操作性**: 支持多种后端系统

## 数据模型

### 核心概念

#### Resource

描述产生遥测数据的实体：

```protobuf
message Resource {
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 1;
  uint32 dropped_attributes_count = 2;
}
```

#### InstrumentationScope

描述产生遥测数据的代码库：

```protobuf
message InstrumentationScope {
  string name = 1;
  string version = 2;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 3;
  uint32 dropped_attributes_count = 4;
}
```

#### Span (Traces)

表示一个操作单元：

```protobuf
message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  bytes parent_span_id = 4;
  string name = 5;
  SpanKind kind = 6;
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 9;
  uint32 dropped_attributes_count = 10;
  repeated StatusEvent events = 11;
  uint32 dropped_events_count = 12;
  repeated SpanLink links = 13;
  uint32 dropped_links_count = 14;
  Status status = 15;
}
```

#### Metric

表示指标数据：

```protobuf
message Metric {
  string name = 1;
  string description = 2;
  string unit = 3;
  oneof data {
    Gauge gauge = 5;
    Sum sum = 7;
    Histogram histogram = 9;
    ExponentialHistogram exponential_histogram = 10;
    Summary summary = 11;
  }
}
```

#### LogRecord

表示日志记录：

```protobuf
message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 2;
  SeverityNumber severity_number = 3;
  string severity_text = 4;
  opentelemetry.proto.common.v1.AnyValue body = 5;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;
  bytes span_id = 10;
}
```

## 传输协议

### gRPC传输

```yaml
# 默认配置
endpoint: "0.0.0.0:4317"
protocol: "grpc"
insecure: true

# 安全配置
endpoint: "0.0.0.0:4317"
protocol: "grpc"
tls:
  cert_file: "/path/to/cert.pem"
  key_file: "/path/to/key.pem"
  client_ca_file: "/path/to/ca.pem"
```

### HTTP传输

```yaml
# 默认配置
endpoint: "0.0.0.0:4318"
protocol: "http/protobuf"
insecure: true

# 安全配置
endpoint: "0.0.0.0:4318"
protocol: "http/protobuf"
tls:
  cert_file: "/path/to/cert.pem"
  key_file: "/path/to/key.pem"
  client_ca_file: "/path/to/ca.pem"
```

## 服务接口

### ExportTraceService

```protobuf
service ExportTraceService {
  rpc Export(ExportTraceServiceRequest) returns (ExportTraceServiceResponse);
}

message ExportTraceServiceRequest {
  repeated ResourceSpans resource_spans = 1;
}

message ExportTraceServiceResponse {
  ExportLogsPartialSuccess partial_success = 1;
}
```

### ExportMetricsService

```protobuf
service ExportMetricsService {
  rpc Export(ExportMetricsServiceRequest) returns (ExportMetricsServiceResponse);
}

message ExportMetricsServiceRequest {
  repeated ResourceMetrics resource_metrics = 1;
}

message ExportMetricsServiceResponse {
  ExportLogsPartialSuccess partial_success = 1;
}
```

### ExportLogsService

```protobuf
service ExportLogsService {
  rpc Export(ExportLogsServiceRequest) returns (ExportLogsServiceResponse);
}

message ExportLogsServiceRequest {
  repeated ResourceLogs resource_logs = 1;
}

message ExportLogsServiceResponse {
  ExportLogsPartialSuccess partial_success = 1;
}
```

## 错误处理

### 状态码

- **OK**: 成功
- **CANCELLED**: 操作被取消
- **UNKNOWN**: 未知错误
- **INVALID_ARGUMENT**: 无效参数
- **DEADLINE_EXCEEDED**: 超时
- **NOT_FOUND**: 资源未找到
- **ALREADY_EXISTS**: 资源已存在
- **PERMISSION_DENIED**: 权限拒绝
- **RESOURCE_EXHAUSTED**: 资源耗尽
- **FAILED_PRECONDITION**: 前置条件失败
- **ABORTED**: 操作中止
- **OUT_OF_RANGE**: 超出范围
- **UNIMPLEMENTED**: 未实现
- **INTERNAL**: 内部错误
- **UNAVAILABLE**: 服务不可用
- **DATA_LOSS**: 数据丢失
- **UNAUTHENTICATED**: 未认证

### 瞬态错误定义（2025年澄清）

根据 OpenTelemetry 规范 1.25.0 的更新，瞬态错误（Transient Errors）的定义已得到澄清：

- **可重试错误**: `UNAVAILABLE`, `DEADLINE_EXCEEDED`, `RESOURCE_EXHAUSTED`
- **不可重试错误**: `INVALID_ARGUMENT`, `PERMISSION_DENIED`, `NOT_FOUND`
- **重试策略**: 仅对瞬态错误实施指数退避重试

### 重试策略

```go
// 指数退避重试
retryConfig := otlptracegrpc.RetryConfig{
    Enabled:         true,
    InitialInterval: time.Second,
    MaxInterval:     time.Second * 30,
    MaxElapsedTime:  time.Minute * 5,
}
```

## 性能特性

### 批处理

```yaml
# 批处理配置
batch:
  timeout: 1s
  send_batch_size: 512
  send_batch_max_size: 2048
```

### 压缩

- **gzip**: 默认压缩算法
- **deflate**: 替代压缩算法
- **identity**: 无压缩

### 性能基准

| 传输方式 | 吞吐量 | CPU使用 | 网络带宽 |
|----------|--------|---------|----------|
| gRPC gzip | 200k spans/s | 1.2核 | 280 Mb/s |
| HTTP gzip | 60k spans/s | 1.5核 | 310 Mb/s |

## 安全考虑

### 传输安全

- **TLS 1.2+**: 传输层加密
- **mTLS**: 双向认证
- **证书管理**: 支持CA证书链

### 认证授权

- **Bearer Token**: 基于令牌的认证
- **Basic Auth**: 基础认证
- **自定义Header**: 自定义认证头

### 数据保护

- **敏感数据脱敏**: 在SDK层处理
- **数据最小化**: 只收集必要数据
- **访问控制**: 基于角色的访问控制

## 兼容性

### 版本兼容性

- **v1.0.0**: 稳定版本，向后兼容到2026年
- **向后兼容**: 未知字段自动跳过
- **向前兼容**: 新字段可选添加

### 后端兼容性

- **Jaeger**: 直接支持
- **Prometheus**: 通过Collector转换
- **Zipkin**: 通过Collector转换
- **自定义后端**: 通过Collector扩展

## 最佳实践

### 1. 配置优化

```yaml
# 生产环境配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size: 4194304
        max_concurrent_streams: 16

processors:
  batch:
    timeout: 1s
    send_batch_size: 512
    send_batch_max_size: 2048
  memory_limiter:
    check_interval: 2s
    limit_mib: 512
    spike_limit_mib: 128
```

### 2. 错误处理

```go
// 处理导出错误
func handleExportError(err error) {
    if status.Code(err) == codes.ResourceExhausted {
        // 资源耗尽，降低采样率
        adjustSamplingRate(0.5)
    } else if status.Code(err) == codes.Unavailable {
        // 服务不可用，重试
        retryExport()
    }
}
```

### 3. 监控指标

```go
// 监控导出性能
exporterMetrics := meter.NewInt64Counter(
    "otel_exporter_sent_spans",
    metric.WithDescription("Number of spans sent by exporter"),
)

exporterMetrics.Add(ctx, spanCount)
```

## 故障排除

### 常见问题

1. **连接失败**: 检查网络配置和防火墙设置
2. **认证失败**: 验证证书和令牌配置
3. **性能问题**: 调整批处理参数和采样率
4. **数据丢失**: 检查重试配置和错误处理

### 调试工具

```bash
# 检查Collector状态
curl http://localhost:13133/

# 验证配置
otelcol --config=config.yaml --dry-run

# 查看日志
docker logs otel-collector
```

## 总结

OTLP作为OpenTelemetry的核心协议，提供了统一、高效、安全的遥测数据传输方案。通过遵循OTLP标准，可以实现：

- **统一的数据模型**: 跨语言、跨框架的一致性
- **高性能传输**: 支持大规模数据收集
- **供应商中立**: 避免厂商锁定
- **安全可靠**: 内置安全和错误处理机制

选择合适的传输方式、配置合理的批处理参数、实施适当的错误处理策略，是成功部署OTLP系统的关键。
