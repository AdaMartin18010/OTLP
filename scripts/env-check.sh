#!/usr/bin/env bash
set -euo pipefail

ok() { command -v "$1" >/dev/null 2>&1; }

printf "OTLP 项目环境自检结果 (bash):\n"

check() {
  local name="$1" advice="$2" cmd="$3"
  if ok "$cmd"; then
    printf -- "- %-32s : OK\n" "$name"
  else
    printf -- "- %-32s : MISSING\n  建议: %s\n" "$name" "$advice"
  fi
}

check "Python" "安装 Python 3.10+ 并确保加入 PATH" python
check "Go" "安装 Go 1.21+；如网络受限设置 GOPROXY" go
check "Rust (cargo)" "安装 Rust stable (rustup)" cargo
check "Docker" "安装 Docker 并启动服务" docker
# docker compose v2
if docker compose version >/dev/null 2>&1; then
  printf -- "- %-32s : OK\n" "Docker Compose"
else
  printf -- "- %-32s : MISSING\n  建议: 升级 Docker 以获得 docker compose\n" "Docker Compose"
fi
check "OpenTelemetry Collector (otelcol)" "下载 otelcol 二进制并加入 PATH" otelcol

exit 0
