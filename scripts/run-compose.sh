#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.." >/dev/null
cd implementations/collector/compose

docker compose up -d --remove-orphans

echo "Compose started. UIs:"
echo "- Jaeger:     http://localhost:16686"
echo "- Grafana:    http://localhost:3000 (admin/admin)"
echo "- Prometheus: http://localhost:9090"
