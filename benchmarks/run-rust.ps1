Param(
    [ValidateNotNullOrEmpty()][string]$Endpoint = "http://localhost:4317",
    [ValidateRange(1, 100000)][int]$Loops = 100,
    [ValidateRange(0, 60000)][int]$SleepMs = 50,
    [ValidateNotNullOrEmpty()][string]$ServiceName = "minimal-rust-bench"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not (Get-Command cargo -ErrorAction SilentlyContinue)) {
  Write-Error "未检测到 'cargo' 命令，请安装 Rust 工具链或将其加入 PATH。"
  exit 1
}

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$examplesRustDir = Join-Path (Join-Path $scriptDir "..") "examples/minimal-rust"

if (-not (Test-Path $examplesRustDir)) {
  Write-Error "示例目录不存在: $examplesRustDir"
  exit 1
}

$env:OTEL_EXPORTER_OTLP_ENDPOINT = $Endpoint
$env:OTEL_SERVICE_NAME = $ServiceName

Write-Host "Running Rust example $Loops times -> $Endpoint"

try {
  Push-Location $examplesRustDir
  for ($i = 0; $i -lt $Loops; $i++) {
    cargo run --quiet | Out-Null
    Start-Sleep -Milliseconds $SleepMs
  }
} finally {
  Pop-Location
}

Write-Host "Done. Verify in Jaeger."


