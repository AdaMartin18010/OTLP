# Minimal Go + OTLP 示例

- 目标：生成 1 条 trace/metric/log 并通过 OTLP 发送到 Collector（见 `implementations/collector/minimal.yaml`）
- 步骤：
  1. 安装 Go 与 OTel SDK
  2. 启动 Collector：`otelcol --config implementations/collector/minimal.yaml`
  3. 运行示例：`go run .`
  4. 在 Collector 日志导出器中查看数据
