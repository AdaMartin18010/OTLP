Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
  [Parameter(Mandatory=$false)][switch]$Down,
  [Parameter(Mandatory=$false)][switch]$Help
)

function Show-Help {
  @"
用法: .\scripts\run-compose.ps1 [-Down] [-Help]

说明:
  默认执行启动（up -d）。使用 -Down 进行停止并清理（down --remove-orphans）。
"@
}

if ($Help) { Show-Help; exit 0 }

if (-not (Get-Command docker -ErrorAction SilentlyContinue)) {
  Write-Error "未检测到 'docker' 命令，请安装 Docker 或将其加入 PATH。"
  exit 1
}

try {
  docker info | Out-Null
} catch {
  Write-Error "Docker 未运行或不可用，请启动 Docker Desktop/守护进程后重试。"
  exit 1
}

${scriptDir} = Split-Path -Parent $MyInvocation.MyCommand.Path
$composeDir = Join-Path (Join-Path $scriptDir "..") "implementations/collector/compose"
Push-Location $composeDir | Out-Location

$composeBinary = $null
if (Get-Command "docker" -ErrorAction SilentlyContinue) {
  try { docker compose version | Out-Null; $composeBinary = "docker compose" } catch {}
}
if (-not $composeBinary -and (Get-Command "docker-compose" -ErrorAction SilentlyContinue)) {
  $composeBinary = "docker-compose"
}
if (-not $composeBinary) {
  Pop-Location | Out-Null
  Write-Error "未找到 'docker compose' 或 'docker-compose' 命令。"
  exit 1
}

try {
  if ($Down) {
    Write-Host "Stopping docker compose stack..."
    if ($composeBinary -eq "docker compose") { docker compose down --remove-orphans }
    else { docker-compose down --remove-orphans }
  } else {
    Write-Host "Starting docker compose stack..."
    if ($composeBinary -eq "docker compose") { docker compose up -d --remove-orphans }
    else { docker-compose up -d --remove-orphans }
    Write-Host "Compose 已启动，可访问以下服务："
    Write-Host "- Jaeger:     http://localhost:16686"
    Write-Host "- Grafana:    http://localhost:3000 (admin/admin)"
    Write-Host "- Prometheus: http://localhost:9090"
  }
} finally {
  Pop-Location | Out-Null
}
