#!/usr/bin/env bash
set -euo pipefail

print_help() {
  cat <<'EOF'
用法: ./scripts/run-compose.sh [--down] [--help]

说明:
  默认执行启动（up -d）。使用 --down 进行停止并清理（down --remove-orphans）。
EOF
}

DO_DOWN=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --down) DO_DOWN=1; shift ;;
    -h|--help) print_help; exit 0 ;;
    *) echo "未知参数: $1" >&2; print_help; exit 2 ;;
  esac
done

cd "$(dirname "$0")/.." >/dev/null
cd implementations/collector/compose

# Detect docker and compose availability
if ! command -v docker >/dev/null 2>&1; then
  echo "未检测到 docker，请先安装 Docker Desktop 或 Docker Engine 并加入 PATH" >&2
  exit 1
fi

COMPOSE_CMD="docker compose"
if ! docker compose version >/dev/null 2>&1; then
  if command -v docker-compose >/dev/null 2>&1; then
    COMPOSE_CMD="docker-compose"
  else
    echo "未检测到 docker compose（v2 或 v1），请安装 docker compose" >&2
    exit 1
  fi
fi

echo "使用 compose 命令：$COMPOSE_CMD"
if (( DO_DOWN==1 )); then
  $COMPOSE_CMD down --remove-orphans
  echo "Compose 已停止并清理。"
  exit 0
fi

$COMPOSE_CMD up -d --remove-orphans

echo "Compose 已启动，可访问以下服务："
echo "- Jaeger:     http://localhost:16686"
echo "- Grafana:    http://localhost:3000 (admin/admin)"
echo "- Prometheus: http://localhost:9090"
