# OpenTelemetry Collector 使用指南

> 最后更新: 2025-09-17

## 快速开始（无 Docker 的最小验证）

- 安装 OpenTelemetry Collector 二进制并加入 PATH（或使用容器）
- 运行最小配置：

```bash
# Windows PowerShell
./scripts/run-collector.ps1 -ConfigPath implementations/collector/minimal.yaml
```

验证：

```bash
# 健康检查
curl -s http://localhost:13133/ | head -n 1
# 端口可达性（任选其一）
# Test-NetConnection -ComputerName localhost -Port 4317
# telnet localhost 4317
```

## 使用 Docker Compose 启动完整栈

前置：安装 Docker Desktop 并启用 Compose。

```bash
# 启动
./scripts/run-compose.ps1
# 访问
# Jaeger:     http://localhost:16686
# Grafana:    http://localhost:3000 (admin/admin)
# Prometheus: http://localhost:9090
```

## 常用变体（按需替换 minimal.yaml）

- export-prometheus.yaml：仅导出指标至 Prometheus
- export-jaeger.yaml：Traces 导出至 Jaeger
- export-tempo.yaml：Traces 导出至 Tempo
- export-loki.yaml：Logs 导出至 Loki
- advanced.yaml：启用批处理、队列、重试、限流等
- security.yaml：启用 TLS/mTLS、安全扩展与过滤器

替换方式：

```bash
./scripts/run-collector.ps1 -ConfigPath implementations/collector/export-jaeger.yaml
```

## 典型修改项速查

- 端口：`receivers.otlp.protocols.grpc.endpoint`
- 批处理：`processors.batch.*`
- 采样：`processors.probabilistic_sampler.sampling_percentage`
- TLS：`receivers.otlp.protocols.grpc.tls.*`
- 导出器：`exporters.*` 与 `service.pipelines.*.exporters`

## 故障排除

- 端口占用：修改 YAML 中端口或停止占用进程
- 无数据：提高采样或检查导出器/后端地址
- 证书错误：检查证书路径与 CA 链
