# OTLP 项目快速质量检查脚本
# 用于验证项目基本质量和完整性

param(
    [string]$ProjectPath = ".",
    [switch]$Verbose
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Write-Host "🔍 开始OTLP项目质量检查..." -ForegroundColor Green

$Issues = @()
$Stats = @{
    TotalFiles = 0
    ValidFiles = 0
    IssuesFound = 0
}

# 检查核心文档
$CoreDocs = @(
    "README.md",
    "OTLP_2025_FINAL_DELIVERY_COMPLETE.md",
    "01_Theory_Foundation/OTLP_2025_KNOWLEDGE_FRAMEWORK.md",
    "06_Technical_Architecture/OTLP_2025_TECHNICAL_ARCHITECTURE.md"
)

Write-Host "📋 检查核心文档..." -ForegroundColor Yellow
foreach ($Doc in $CoreDocs) {
    $DocPath = Join-Path $ProjectPath $Doc
    if (Test-Path $DocPath) {
        $Stats.TotalFiles++
        $Stats.ValidFiles++
        Write-Host "  ✅ $Doc" -ForegroundColor Green
    } else {
        $Stats.TotalFiles++
        $Issues += "核心文档缺失: $Doc"
        Write-Host "  ❌ $Doc (缺失)" -ForegroundColor Red
    }
}

# 检查示例代码
$Examples = @(
    "examples/minimal-rust",
    "examples/minimal-go", 
    "examples/minimal-python",
    "examples/minimal-java",
    "examples/minimal-javascript"
)

Write-Host "💻 检查示例代码..." -ForegroundColor Yellow
foreach ($Example in $Examples) {
    $ExamplePath = Join-Path $ProjectPath $Example
    if (Test-Path $ExamplePath) {
        $Stats.TotalFiles++
        $Stats.ValidFiles++
        Write-Host "  ✅ $Example" -ForegroundColor Green
    } else {
        $Stats.TotalFiles++
        $Issues += "示例代码缺失: $Example"
        Write-Host "  ❌ $Example (缺失)" -ForegroundColor Red
    }
}

# 检查配置文件
$Configs = @(
    "implementations/collector/minimal.yaml",
    "implementations/collector/production.yaml",
    "implementations/collector/security-enhanced.yaml"
)

Write-Host "⚙️ 检查配置文件..." -ForegroundColor Yellow
foreach ($Config in $Configs) {
    $ConfigPath = Join-Path $ProjectPath $Config
    if (Test-Path $ConfigPath) {
        $Stats.TotalFiles++
        $Stats.ValidFiles++
        Write-Host "  ✅ $Config" -ForegroundColor Green
    } else {
        $Stats.TotalFiles++
        $Issues += "配置文件缺失: $Config"
        Write-Host "  ❌ $Config (缺失)" -ForegroundColor Red
    }
}

# 检查脚本文件
$Scripts = @(
    "scripts/run-collector.ps1",
    "scripts/run-compose.ps1",
    "scripts/version-check.ps1"
)

Write-Host "🔧 检查脚本文件..." -ForegroundColor Yellow
foreach ($Script in $Scripts) {
    $ScriptPath = Join-Path $ProjectPath $Script
    if (Test-Path $ScriptPath) {
        $Stats.TotalFiles++
        $Stats.ValidFiles++
        Write-Host "  ✅ $Script" -ForegroundColor Green
    } else {
        $Stats.TotalFiles++
        $Issues += "脚本文件缺失: $Script"
        Write-Host "  ❌ $Script (缺失)" -ForegroundColor Red
    }
}

# 检查基准测试
$Benchmarks = @(
    "benchmarks/run-rust.ps1",
    "benchmarks/run-go.ps1", 
    "benchmarks/run-python.ps1"
)

Write-Host "📊 检查基准测试..." -ForegroundColor Yellow
foreach ($Benchmark in $Benchmarks) {
    $BenchmarkPath = Join-Path $ProjectPath $Benchmark
    if (Test-Path $BenchmarkPath) {
        $Stats.TotalFiles++
        $Stats.ValidFiles++
        Write-Host "  ✅ $Benchmark" -ForegroundColor Green
    } else {
        $Stats.TotalFiles++
        $Issues += "基准测试缺失: $Benchmark"
        Write-Host "  ❌ $Benchmark (缺失)" -ForegroundColor Red
    }
}

# 统计结果
$Stats.IssuesFound = $Issues.Count
$SuccessRate = if ($Stats.TotalFiles -gt 0) { [math]::Round(($Stats.ValidFiles / $Stats.TotalFiles) * 100, 2) } else { 0 }

Write-Host "`n📈 质量检查结果:" -ForegroundColor Cyan
Write-Host "  总文件数: $($Stats.TotalFiles)" -ForegroundColor White
Write-Host "  有效文件数: $($Stats.ValidFiles)" -ForegroundColor White
Write-Host "  问题数量: $($Stats.IssuesFound)" -ForegroundColor White
Write-Host "  成功率: $SuccessRate%" -ForegroundColor White

if ($Issues.Count -gt 0) {
    Write-Host "`n❌ 发现的问题:" -ForegroundColor Red
    foreach ($Issue in $Issues) {
        Write-Host "  • $Issue" -ForegroundColor Red
    }
} else {
    Write-Host "`n✅ 所有检查通过！项目质量优秀！" -ForegroundColor Green
}

# 质量评级
$QualityGrade = switch ($SuccessRate) {
    { $_ -ge 95 } { "A+" }
    { $_ -ge 90 } { "A" }
    { $_ -ge 80 } { "B" }
    { $_ -ge 70 } { "C" }
    default { "D" }
}

Write-Host "`n🏆 项目质量评级: $QualityGrade" -ForegroundColor $(if ($QualityGrade -eq "A+" -or $QualityGrade -eq "A") { "Green" } else { "Yellow" })

if ($SuccessRate -ge 90) {
    Write-Host "🎉 项目已达到高质量标准！" -ForegroundColor Green
    exit 0
} else {
    Write-Host "⚠️ 项目需要进一步改进。" -ForegroundColor Yellow
    exit 1
}
