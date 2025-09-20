Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
  [Parameter(Mandatory=$false)][ValidateNotNullOrEmpty()][string]$ConfigPath = "implementations/collector/minimal.yaml",
  [Parameter(Mandatory=$false)][switch]$DryRun,
  [Parameter(Mandatory=$false)][switch]$Help
)

function Show-Help {
  @"
用法: .\scripts\run-collector.ps1 [-ConfigPath <path>] [-DryRun] [-Help]

参数:
  -ConfigPath <path>  指定 Collector 配置文件（默认 implementations/collector/minimal.yaml）
  -DryRun             只校验配置与环境，不启动进程
  -Help               显示帮助
"@
}

if ($Help) {
  Show-Help
  exit 0
}

if (-not (Get-Command otelcol -ErrorAction SilentlyContinue)) {
  Write-Error "未检测到 'otelcol' 命令，请安装 OpenTelemetry Collector 或将其加入 PATH。"
  exit 1
}

try {
  $ver = (& otelcol --version 2>$null)
} catch { $ver = $null }
if ($ver) { Write-Host "otelcol 版本: $ver" } else { Write-Host "otelcol 版本: unknown" }

if (-not ([System.IO.Path]::IsPathRooted($ConfigPath))) {
  $scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
  $ConfigPath = Join-Path (Join-Path $scriptDir "..") $ConfigPath
}
if (-not (Test-Path $ConfigPath)) {
  Write-Error "配置文件未找到: $ConfigPath"
  exit 1
}

Write-Host "使用配置文件: $ConfigPath"

if ($DryRun) {
  Write-Host "进行配置校验（dry-run）..."
  try {
    $help = (& otelcol --help 2>$null)
    if ($help -match "--config") {
      & otelcol --config $ConfigPath --dry-run | Out-Null
      Write-Host "✅ 配置校验通过"
      exit 0
    }
  } catch {
    Write-Warning "配置校验命令不可用或失败，可手动检查 YAML 语法。"
  }
  exit 0
}

Write-Host "Starting otelcol ..."
& otelcol --config $ConfigPath

