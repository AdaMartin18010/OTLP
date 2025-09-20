param()

$results = @()

function Test-Cmd($name) {
  $exists = Get-Command $name -ErrorAction SilentlyContinue
  return [bool]$exists
}

# Python
$hasPython = Test-Cmd python
$results += @{ name = 'Python'; present = $hasPython; advice = '安装 Python 3.10+ 并确保加入 PATH' }

# Go
$hasGo = Test-Cmd go
$results += @{ name = 'Go'; present = $hasGo; advice = '安装 Go 1.21+；如网络受限设置 GOPROXY' }

# Rust
$hasCargo = Test-Cmd cargo
$results += @{ name = 'Rust (cargo)'; present = $hasCargo; advice = '安装 Rust stable (rustup)' }

# Docker
$hasDocker = Test-Cmd docker
$results += @{ name = 'Docker'; present = $hasDocker; advice = '安装 Docker Desktop 并启用 Compose' }

# Docker Compose (v2 内置 docker compose)
$hasCompose = $false
try { $null = (& docker compose version) 2>$null; if ($LASTEXITCODE -eq 0) { $hasCompose = $true } } catch {}
$results += @{ name = 'Docker Compose'; present = $hasCompose; advice = '升级 Docker Desktop 以获得 docker compose' }

# otelcol
$hasOtelcol = Test-Cmd otelcol
$results += @{ name = 'OpenTelemetry Collector (otelcol)'; present = $hasOtelcol; advice = '下载 otelcol 二进制并加入 PATH' }

# PowerShell ExecutionPolicy
$pol = Get-ExecutionPolicy -Scope Process
$results += @{ name = 'PowerShell 执行策略'; present = ($pol -ne 'Undefined'); advice = '使用 -ExecutionPolicy Bypass 运行脚本' }

Write-Host 'OTLP 项目环境自检结果:' -ForegroundColor Cyan
foreach ($r in $results) {
  $status = if ($r.present) { 'OK' } else { 'MISSING' }
  $color = if ($r.present) { 'Green' } else { 'Yellow' }
  Write-Host ('- {0,-32} : {1}' -f $r.name, $status) -ForegroundColor $color
  if (-not $r.present) { Write-Host ('  建议: {0}' -f $r.advice) -ForegroundColor Yellow }
}

# 退出码固定 0，便于流水线不中断
exit 0
