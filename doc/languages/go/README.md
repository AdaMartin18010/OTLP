# Go 语言接入指引（最小可用）

- 依赖：`go.opentelemetry.io/otel`, `go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc`, `otelmetric`
- 环境：Collector 运行于 `implementations/collector/minimal.yaml`
- 步骤：初始化 Resource、TraceProvider/MetricReader，设置 OTLP gRPC Exporter，生成一条 span 与一个 gauge。
