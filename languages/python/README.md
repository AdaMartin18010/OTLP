# Python 语言接入指引（最小可用）

- 依赖：`opentelemetry-api`, `opentelemetry-sdk`, `opentelemetry-exporter-otlp`
- 环境：Collector 运行于 `implementations/collector/minimal.yaml`
- 步骤：初始化 Resource、TracerProvider/MeterProvider，设置 OTLP gRPC Exporter，生成一条 span 与一个 counter。
