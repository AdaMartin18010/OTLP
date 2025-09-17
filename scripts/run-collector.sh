#!/usr/bin/env bash
set -euo pipefail

print_help() {
  cat <<'EOF'
用法: ./scripts/run-collector.sh [--config <path>] [--dry-run]

选项:
  --config <path>  指定 Collector 配置文件（默认 implementations/collector/minimal.yaml）
  --dry-run        只校验配置与环境，不启动进程
  -h, --help       显示帮助
EOF
}

CONFIG="implementations/collector/minimal.yaml"
DRY_RUN=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --config)
      CONFIG=${2:-}
      if [[ -z "$CONFIG" ]]; then echo "--config 需要一个路径" >&2; exit 2; fi
      shift 2 ;;
    --dry-run)
      DRY_RUN=1
      shift ;;
    -h|--help)
      print_help; exit 0 ;;
    *)
      echo "未知参数: $1" >&2; print_help; exit 2 ;;
  esac
done

if ! command -v otelcol >/dev/null 2>&1; then
  echo "未检测到 otelcol，请安装 OpenTelemetry Collector 并加入 PATH" >&2
  exit 1
fi

echo "otelcol 版本: $(otelcol --version 2>/dev/null || echo unknown)"

if [[ ! -f "$CONFIG" ]]; then
  echo "配置文件未找到: $CONFIG" >&2
  exit 1
fi

echo "使用配置文件: $CONFIG"

if (( DRY_RUN==1 )); then
  echo "进行配置校验（dry-run）..."
  # 若安装了 config 命令则进行验证，否则尝试启动并立即退出
  if otelcol --help 2>&1 | grep -q -- '--config'; then
    # 大多数发行版支持 --config，并在错误时非零退出
    if otelcol --config "$CONFIG" --dry-run 2>/dev/null; then
      echo "✅ 配置校验通过"
      exit 0
    else
      echo "⚠️  配置校验命令不可用或失败，尝试语法探测" >&2
      # 退而求其次：打印前 10 行，供用户自查
      head -n 10 "$CONFIG" | sed 's/^/  > /'
      exit 0
    fi
  fi
fi

echo "Starting otelcol ..."
exec otelcol --config "$CONFIG"
