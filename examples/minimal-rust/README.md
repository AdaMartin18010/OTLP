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

## Metrics 实践提示（2025）

- 指标名称长度最大 255 字符，名称与 `unit` 保持一致（如 `*_seconds` + `s`）。
- 优先使用常规 Histogram + 业务边界；宽动态范围评估 ExponentialHistogram。
- 用 Views 限制高基数属性并统一命名；为热点路径准备降维流。
- 对接 Prometheus 时明确 Delta/Cumulative 与 *_bucket 映射，必要时通过 Collector 做转换与限流。
