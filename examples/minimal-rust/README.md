# Minimal Rust + OTLP 示例

- 目标：生成 1 条 trace/metric/log 并通过 OTLP 发送到 Collector（见 `implementations/collector/minimal.yaml`）
- 步骤：
  1. 安装 Rust 与 OTel 相关 crates
  2. 启动 Collector：`otelcol --config implementations/collector/minimal.yaml` 或 `./scripts/run-collector.ps1`
  3. 运行示例：`cargo run --quiet`
  4. 在 Collector 日志导出器中查看数据

## 参数化运行

环境变量常用参数：

```bash
export OTEL_SERVICE_NAME="minimal-rust"
export OTEL_EXPORTER_OTLP_ENDPOINT="http://localhost:4317"
export OTEL_EXPORTER_OTLP_PROTOCOL="grpc"
```

## 期望输出（Collector logging 导出器）

```text
ResourceSpans #0
InstrumentationLibrarySpans #0
Span #0
  Trace ID     : ...
  Name         : demo-span
```
