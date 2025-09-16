# OpenTelemetry 快速开始指南

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [教程与学习路径](TUTORIALS.md) | [故障排除](TROUBLESHOOTING.md) | [部署指南](DEPLOYMENT_GUIDE.md)

## 5分钟快速体验

### 1. 环境准备

```bash
# 安装Docker
docker --version

# 安装Go (可选)
go version

# 安装Python (可选)
python --version

# 安装Rust (可选)
cargo --version
```

### 2. 一键启动

```bash
# 启动完整栈
./scripts/run-compose.ps1

# 或单独启动Collector
./scripts/run-collector.ps1
```

### 3. 运行示例

```bash
# Rust示例
cd examples/minimal-rust && cargo run

# Go示例
cd examples/minimal-go && go run .

# Python示例
cd examples/minimal-python && python main.py
```

### 4. 查看结果

- **Jaeger UI**: <http://localhost:16686>
- **Prometheus**: <http://localhost:9090>
- **Grafana**: <http://localhost:3000> (admin/admin)

## 核心概念速览

### 三大信号

- **Traces**: 分布式追踪，跟踪请求路径
- **Metrics**: 指标监控，监控系统性能
- **Logs**: 日志记录，记录系统事件

### 核心组件

- **SDK**: 数据收集和预处理
- **Collector**: 数据聚合和转换
- **Backend**: 数据存储和可视化

## 常用配置

### 环境变量

```bash
export OTEL_SERVICE_NAME="my-service"
export OTEL_EXPORTER_OTLP_ENDPOINT="http://localhost:4317"
export OTEL_EXPORTER_OTLP_PROTOCOL="grpc"
```

### 基础配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
processors:
  batch:
    timeout: 1s
    send_batch_size: 512
exporters:
  logging:
    loglevel: info
service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging]
```

## 故障排除

### 常见问题

1. **端口被占用**: 修改配置文件中的端口
2. **权限问题**: 使用管理员权限运行脚本
3. **网络问题**: 检查防火墙设置

### 调试命令

```bash
# 检查Collector状态
curl http://localhost:13133/

# 查看日志
docker logs otel-collector

# 测试连接
telnet localhost 4317
```

## 下一步

- 阅读完整文档: `docs/TERMS.md`
- 学习最佳实践: `governance/BEST_PRACTICES.md`
- 运行基准测试: `benchmarks/`
