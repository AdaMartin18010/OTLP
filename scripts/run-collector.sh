#!/usr/bin/env bash
set -euo pipefail
CONFIG=${1:-implementations/collector/minimal.yaml}

if ! command -v otelcol >/dev/null 2>&1; then
  echo "未检测到 otelcol，请安装 OpenTelemetry Collector 并加入 PATH" >&2
  exit 1
fi

if [[ ! -f "$CONFIG" ]]; then
  echo "配置文件未找到: $CONFIG" >&2
  exit 1
fi

echo "Starting otelcol with config: $CONFIG"
otelcol --config "$CONFIG"
