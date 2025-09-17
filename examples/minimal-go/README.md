# Minimal Go + OTLP 示例

- 目标：生成 1 条 trace/metric/log 并通过 OTLP 发送到 Collector（见 `implementations/collector/minimal.yaml`）
- 步骤：
  1. 安装 Go 与 OTel SDK
  2. 启动 Collector：`otelcol --config implementations/collector/minimal.yaml` 或 `./scripts/run-collector.ps1`
  3. 运行示例：`go run .`
  4. 在 Collector 日志导出器中查看数据

## 参数化运行

```bash
set OTEL_SERVICE_NAME=minimal-go
set OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
set OTEL_EXPORTER_OTLP_PROTOCOL=grpc
```

若网络受限，可设置 `GOPROXY` 后再执行：

```powershell
Set-Item Env:GOPROXY 'https://goproxy.cn,direct'
go mod tidy
go run .
```

## 期望输出（Collector logging 导出器）

```text
ResourceSpans #0
InstrumentationLibrarySpans #0
Span #0
  Name         : demo-span
```
