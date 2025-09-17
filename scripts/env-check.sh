#!/usr/bin/env bash
set -euo pipefail

ok() { command -v "$1" >/dev/null 2>&1; }

printf "OTLP 项目环境自检结果 (bash):\n"

print_ok_with_version() {
  local name="$1" cmd="$2" ver_flag="$3"
  local ver=""
  if [[ -n "$ver_flag" ]]; then
    ver=$($cmd $ver_flag 2>/dev/null | head -n1 || true)
  fi
  if [[ -n "$ver" ]]; then
    printf -- "- %-32s : OK (%s)\n" "$name" "$ver"
  else
    printf -- "- %-32s : OK\n" "$name"
  fi
}

check() {
  local name="$1" advice="$2" cmd="$3" ver_flag="${4:-}"
  if ok "$cmd"; then
    print_ok_with_version "$name" "$cmd" "$ver_flag"
  else
    printf -- "- %-32s : MISSING\n  建议: %s\n" "$name" "$advice"
  fi
}

check "Python" "安装 Python 3.10+ 并确保加入 PATH" python "--version"
check "Go" "安装 Go 1.21+；如网络受限设置 GOPROXY" go "version"
check "Rust (cargo)" "安装 Rust stable (rustup)" cargo "--version"
check "Docker" "安装 Docker 并启动服务" docker "--version"
# docker compose v2
if docker compose version >/dev/null 2>&1; then
  printf -- "- %-32s : OK (docker compose %s)\n" "Docker Compose" "$(docker compose version --short 2>/dev/null || echo v2)"
else
  printf -- "- %-32s : MISSING\n  建议: 升级 Docker 以获得 docker compose\n" "Docker Compose"
fi
check "OpenTelemetry Collector (otelcol)" "下载 otelcol 二进制并加入 PATH" otelcol "--version"

exit 0
