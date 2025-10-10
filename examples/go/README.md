# Go OTLP Trace Example

这是一个简单的Go示例，展示如何使用OpenTelemetry SDK发送trace数据到OTLP Collector。

## 功能

- 创建OTLP gRPC导出器
- 配置TracerProvider和Resource
- 创建根Span和子Span
- 添加属性和元数据
- 批量导出到Collector

## 前置要求

- Go 1.21+
- Docker 和 Docker Compose (运行Collector和Jaeger)

## 快速开始

### 1. 启动基础设施

首先启动OpenTelemetry Collector和Jaeger：

```bash
# 在项目根目录
docker-compose up -d
```

验证服务运行：
```bash
docker-compose ps
```

### 2. 安装依赖

```bash
cd examples/go
go mod download
```

### 3. 运行示例

```bash
go run hello_trace.go
```

### 4. 查看Trace

打开浏览器访问Jaeger UI：
```
http://localhost:16686
```

在Service下拉菜单选择 `hello-trace-go`，点击 "Find Traces" 即可看到发送的trace。

## 代码说明

### 核心组件

1. **OTLP Exporter** - 负责将trace数据发送到Collector
   ```go
   exporter, err := otlptracegrpc.New(ctx,
       otlptracegrpc.WithEndpoint("localhost:4317"),
       otlptracegrpc.WithInsecure(),
   )
   ```

2. **Resource** - 描述服务的元数据
   ```go
   resource.WithAttributes(
       semconv.ServiceName("hello-trace-go"),
       semconv.ServiceVersion("1.0.0"),
   )
   ```

3. **TracerProvider** - 创建Tracer的工厂
   ```go
   tp := sdktrace.NewTracerProvider(
       sdktrace.WithBatcher(exporter),
       sdktrace.WithResource(res),
   )
   ```

4. **Span** - 代表一个操作单元
   ```go
   ctx, span := tracer.Start(ctx, "hello-operation")
   span.SetAttributes(attribute.String("greeting", "Hello OTLP!"))
   span.End()
   ```

## 配置说明

### Endpoint配置

- **开发环境**: `localhost:4317` (非加密)
- **生产环境**: 使用TLS加密，需配置证书

### 采样策略

当前使用 `AlwaysSample()`，即全量采样。生产环境建议使用：
- `TraceIDRatioBased(0.1)` - 10%采样率
- `ParentBased()` - 基于父Span的采样决策

### 批处理配置

使用 `WithBatcher()` 自动批量发送，减少网络开销。

## 故障排除

### 连接失败

如果看到 `connection refused` 错误：
1. 确认Collector正在运行: `docker-compose ps`
2. 检查端口是否开放: `netstat -an | grep 4317`
3. 查看Collector日志: `docker-compose logs otel-collector`

### Trace未显示

1. 等待2-5秒，批处理器有延迟
2. 确认Jaeger正常运行: `http://localhost:16686`
3. 检查Service名称是否正确

## 更多示例

查看 [examples/README.md](../README.md) 了解更多示例。

## 参考文档

- [OpenTelemetry Go SDK](https://opentelemetry.io/docs/languages/go/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

