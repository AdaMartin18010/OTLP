# OTLP Examples

这个目录包含OpenTelemetry Protocol (OTLP)的实用代码示例，展示如何在不同语言中使用OTLP发送遥测数据。

## 📁 示例列表

| 语言 | 目录 | 说明 | 难度 |
|------|------|------|------|
| **Go** | [go/](go/) | Go语言OTLP trace示例 | ⭐ 入门 |
| **Python** | [python/](python/) | Python OTLP trace示例 | ⭐ 入门 |

## 🚀 快速开始

### 前置要求

1. **Docker & Docker Compose** - 运行Collector和Jaeger
2. **语言环境**:
   - Go 1.21+ (for Go examples)
   - Python 3.8+ (for Python examples)

### 启动基础设施

所有示例都需要先启动OpenTelemetry Collector和Jaeger：

```bash
# 在项目根目录
docker-compose up -d

# 验证服务状态
docker-compose ps

# 查看日志（可选）
docker-compose logs -f
```

### 运行示例

#### Go示例

```bash
cd examples/go
go mod download
go run hello_trace.go
```

#### Python示例

```bash
cd examples/python
pip install -r requirements.txt
python hello_trace.py
```

### 查看结果

打开浏览器访问Jaeger UI：

```text
http://localhost:16686
```

## 📊 服务端口

| 服务 | 端口 | 用途 |
|------|------|------|
| **OTLP Collector** | | |
| - gRPC | 4317 | OTLP gRPC接收端点 |
| - HTTP | 4318 | OTLP HTTP接收端点 |
| - Metrics | 8888 | Collector自身指标 |
| - Health | 13133 | 健康检查端点 |
| **Jaeger** | | |
| - UI | 16686 | Jaeger Web界面 |
| - gRPC | 14250 | Collector连接端点 |
| - HTTP | 14268 | 直接接收spans |

## 🏗️ 架构

```text
┌─────────────┐     OTLP gRPC     ┌──────────────────┐
│ Application │ ──────4317──────> │ OTLP Collector   │
│  (Go/Python)│                   │                  │
└─────────────┘                   │  - Receivers     │
                                  │  - Processors    │
                                  │  - Exporters     │
                                  └────────┬─────────┘
                                           │
                                    gRPC 14250
                                           │
                                           ▼
                                  ┌──────────────────┐
                                  │     Jaeger       │
                                  │                  │
                                  │  - Storage       │
                                  │  - Query Service │
                                  │  - UI (16686)    │
                                  └──────────────────┘
```

## 📖 示例说明

### Go示例 (examples/go/)

**功能**:

- 创建OTLP gRPC导出器
- 配置TracerProvider和Resource
- 创建根Span和子Span
- 添加属性和元数据

**关键代码**:

```go
exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("localhost:4317"),
    otlptracegrpc.WithInsecure(),
)
```

**查看详情**: [go/README.md](go/README.md)

### Python示例 (examples/python/)

**功能**:

- OTLP gRPC导出器配置
- 层级Span创建
- 事件记录和异常处理
- 状态管理

**关键代码**:

```python
otlp_exporter = OTLPSpanExporter(
    endpoint="localhost:4317",
    insecure=True
)
```

**查看详情**: [python/README.md](python/README.md)

## 🔧 配置说明

### Collector配置 (otel-config.yaml)

核心配置项：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
```

### Docker Compose配置

关键服务：

1. **otel-collector**
   - Image: `otel/opentelemetry-collector:0.111.0`
   - 配置: `otel-config.yaml`
   - 健康检查: `http://localhost:13133`

2. **jaeger**
   - Image: `jaegertracing/all-in-one:1.61`
   - UI: `http://localhost:16686`
   - OTLP enabled

## 🛠️ 故障排除

### 常见问题

#### 1. 连接失败 (connection refused)

**症状**: 应用报错 `connection refused to localhost:4317`

**原因**: Collector未运行或端口未开放

**解决**:

```bash
# 检查Collector状态
docker-compose ps

# 重启服务
docker-compose restart otel-collector

# 查看日志
docker-compose logs otel-collector
```

#### 2. Trace未显示在Jaeger

**症状**: Jaeger UI中看不到trace

**可能原因**:

- 批处理延迟（等待2-5秒）
- Service名称不匹配
- 时间范围设置错误

**解决**:

```bash
# 1. 检查Collector日志
docker-compose logs otel-collector | grep -i error

# 2. 检查Jaeger日志
docker-compose logs jaeger | grep -i error

# 3. 验证数据流
# 访问 http://localhost:8888/metrics 查看Collector指标
```

#### 3. Docker容器无法启动

**症状**: `docker-compose up` 失败

**解决**:

```bash
# 检查端口占用
netstat -ano | findstr "4317 16686"  # Windows
netstat -tuln | grep -E "4317|16686" # Linux/Mac

# 清理并重建
docker-compose down -v
docker-compose up -d
```

### 调试技巧

#### 1. 启用详细日志

修改 `otel-config.yaml`:

```yaml
exporters:
  logging:
    verbosity: detailed
```

#### 2. 检查健康状态

```bash
# Collector健康检查
curl http://localhost:13133

# Jaeger健康检查
curl http://localhost:16686
```

#### 3. 查看Collector指标

访问 `http://localhost:8888/metrics` 查看：

- `otelcol_receiver_accepted_spans` - 接收的span数
- `otelcol_exporter_sent_spans` - 导出的span数
- `otelcol_processor_batch_batch_send_size` - 批处理大小

## 📚 学习路径

### 初学者

1. ✅ 运行Go示例 → 理解基本概念
2. ✅ 运行Python示例 → 学习不同语言实现
3. ✅ 查看Jaeger UI → 理解trace可视化
4. 📝 阅读 [OTLP规范](../doc/02_标准规范与对标/)

### 进阶

1. 修改采样率 → 理解采样策略
2. 添加Metrics示例 → 扩展到其他信号
3. 自定义Processor → 学习数据处理
4. 生产环境部署 → TLS、认证、监控

## 🔗 相关文档

### 项目文档

- [项目README](../README.md)
- [批判性评价报告](../doc/批判性评价-执行摘要_2025_10_10.md)
- [改进计划](../doc/可持续改进与中断恢复计划_2025_10_10.md)

### 官方文档

- [OpenTelemetry官网](https://opentelemetry.io/)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)
- [Go SDK文档](https://opentelemetry.io/docs/languages/go/)
- [Python SDK文档](https://opentelemetry.io/docs/languages/python/)
- [Collector文档](https://opentelemetry.io/docs/collector/)

## 🎯 下一步

- [ ] 添加Rust示例
- [ ] 添加Metrics示例
- [ ] 添加Logs示例
- [ ] 添加自动instrumentation示例
- [ ] 添加Kubernetes部署示例
- [ ] 添加生产环境配置示例

## 💡 贡献

欢迎贡献新的示例！请查看 [贡献指南](../CONTRIBUTING.md)。

---

**最后更新**: 2025-10-10  
**维护者**: OTLP项目团队
