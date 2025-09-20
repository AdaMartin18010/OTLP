# Rust 语言接入指引（最小可用）

- 依赖：`opentelemetry`, `opentelemetry-otlp`, `tracing`, `tracing-subscriber`
- 环境：Collector 运行于 `implementations/collector/minimal.yaml`
- 步骤：初始化全局 tracer/provider，配置 OTLP gRPC exporter，通过 tracing 生成 span 与事件。
