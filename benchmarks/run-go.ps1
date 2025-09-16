Param(
    [ValidateNotNullOrEmpty()][string]$Endpoint = "http://localhost:4317",
    [ValidateSet("grpc", "http/protobuf")][string]$Protocol = "grpc",
    [ValidateRange(1, 100000)][int]$Loops = 100,
    [ValidateRange(0, 60000)][int]$SleepMs = 50,
    [ValidateNotNullOrEmpty()][string]$ServiceName = "minimal-go-bench"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not (Get-Command go -ErrorAction SilentlyContinue)) {
  Write-Error "未检测到 'go' 命令，请安装 Go 工具链或将其加入 PATH。"
  exit 1
}

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$examplesGoDir = Join-Path (Join-Path $scriptDir "..") "examples/minimal-go"

if (-not (Test-Path $examplesGoDir)) {
  Write-Error "示例目录不存在: $examplesGoDir"
  exit 1
}

$env:OTEL_EXPORTER_OTLP_ENDPOINT = $Endpoint
$env:OTEL_EXPORTER_OTLP_PROTOCOL = $Protocol
$env:OTEL_SERVICE_NAME = $ServiceName

Write-Host "Running Go example $Loops times -> $Endpoint using $Protocol"

try {
  Push-Location $examplesGoDir
  for ($i = 0; $i -lt $Loops; $i++) {
    go run . | Out-Null
    Start-Sleep -Milliseconds $SleepMs
  }
} finally {
  Pop-Location
}

Write-Host "Done. Verify in Jaeger."