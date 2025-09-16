Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
  [ValidateNotNullOrEmpty()][string]$ConfigPath = "implementations/collector/minimal.yaml"
)

Write-Host "Starting otelcol with config: $ConfigPath"
if (-not ([System.IO.Path]::IsPathRooted($ConfigPath))) {
  $scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
  $ConfigPath = Join-Path (Join-Path $scriptDir "..") $ConfigPath
}
if (-not (Test-Path $ConfigPath)) {
  Write-Error "配置文件未找到: $ConfigPath"
  exit 1
}

if (-not (Get-Command otelcol -ErrorAction SilentlyContinue)) {
  Write-Error "未检测到 'otelcol' 命令，请安装 OpenTelemetry Collector 或将其加入 PATH。"
  exit 1
}
try {
  otelcol --config $ConfigPath | Get-Content
} catch {
  throw
}

