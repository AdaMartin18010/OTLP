Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Write-Host "Starting docker compose stack..."
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
Push-Location $composeDir | Out-Null
$composeCmd = $null
if (Get-Command "docker" -ErrorAction SilentlyContinue) {
  $composeCmd = { docker compose up -d }
}
if (-not $composeCmd -and (Get-Command "docker-compose" -ErrorAction SilentlyContinue)) {
  $composeCmd = { docker-compose up -d }
}
if (-not $composeCmd) {
  Pop-Location | Out-Null
  Write-Error "未找到 'docker compose' 或 'docker-compose' 命令。"
  exit 1
}
try {
  & $composeCmd
} finally {
  Pop-Location | Out-Null
}

