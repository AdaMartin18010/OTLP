# OTLP 2025 综合执行脚本
# 统一执行版本检查、文档质量检查、配置测试、新技术集成

param(
    [string]$Action = "all",
    [string]$Language = "all",
    [string]$Technology = "all",
    [switch]$Verbose,
    [switch]$Export,
    [switch]$Force
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 显示帮助信息
function Show-Help {
    Write-ColorOutput "OTLP 2025 综合执行脚本" "Green"
    Write-ColorOutput ("=" * 50) "Gray"
    Write-ColorOutput ""
    Write-ColorOutput "用法: .\otlp-2025-executor.ps1 [参数]" "White"
    Write-ColorOutput ""
    Write-ColorOutput "参数:" "Yellow"
    Write-ColorOutput "  -Action <string>     执行的操作 (all, version, docs, config, tech)" "White"
    Write-ColorOutput "  -Language <string>   目标语言 (all, rust, go, js)" "White"
    Write-ColorOutput "  -Technology <string> 目标技术 (all, tracezip, crosstrace, atys)" "White"
    Write-ColorOutput "  -Verbose             详细输出" "White"
    Write-ColorOutput "  -Export              导出报告" "White"
    Write-ColorOutput "  -Force               强制执行" "White"
    Write-ColorOutput ""
    Write-ColorOutput "示例:" "Yellow"
    Write-ColorOutput "  .\otlp-2025-executor.ps1 -Action version -Language rust" "White"
    Write-ColorOutput "  .\otlp-2025-executor.ps1 -Action docs -Export" "White"
    Write-ColorOutput "  .\otlp-2025-executor.ps1 -Action tech -Technology tracezip" "White"
    Write-ColorOutput "  .\otlp-2025-executor.ps1 -Action all -Verbose -Export" "White"
    Write-ColorOutput ""
}

# 执行版本检查
function Invoke-VersionCheck {
    Write-ColorOutput "🔍 执行版本检查..." "Cyan"
    
    $scriptPath = "scripts/version-check-2025.ps1"
    if (!(Test-Path $scriptPath)) {
        Write-ColorOutput "❌ 版本检查脚本不存在: $scriptPath" "Red"
        return $false
    }
    
    $params = @("-Language", $Language)
    if ($Verbose) { $params += "-Verbose" }
    if ($Export) { $params += "-Export" }
    
    try {
        & $scriptPath @params
        return $LASTEXITCODE -eq 0
    } catch {
        Write-ColorOutput "❌ 版本检查执行失败: $($_.Exception.Message)" "Red"
        return $false
    }
}

# 执行文档质量检查
function Invoke-DocumentQualityCheck {
    Write-ColorOutput "📚 执行文档质量检查..." "Cyan"
    
    $scriptPath = "scripts/doc-quality-check-2025.ps1"
    if (!(Test-Path $scriptPath)) {
        Write-ColorOutput "❌ 文档质量检查脚本不存在: $scriptPath" "Red"
        return $false
    }
    
    $params = @("-Path", "docs")
    if ($Verbose) { $params += "-Verbose" }
    if ($Export) { $params += "-Export" }
    if ($Force) { $params += "-Fix" }
    
    try {
        & $scriptPath @params
        return $LASTEXITCODE -eq 0
    } catch {
        Write-ColorOutput "❌ 文档质量检查执行失败: $($_.Exception.Message)" "Red"
        return $false
    }
}

# 执行配置测试
function Invoke-ConfigTest {
    Write-ColorOutput "⚙️ 执行配置测试..." "Cyan"
    
    $scriptPath = "scripts/config-test-2025.ps1"
    if (!(Test-Path $scriptPath)) {
        Write-ColorOutput "❌ 配置测试脚本不存在: $scriptPath" "Red"
        return $false
    }
    
    $params = @("-Language", $Language)
    if ($Verbose) { $params += "-Verbose" }
    if ($Export) { $params += "-Export" }
    if ($Force) { $params += "-Validate"; $params += "-Test"; $params += "-Benchmark" }
    
    try {
        & $scriptPath @params
        return $LASTEXITCODE -eq 0
    } catch {
        Write-ColorOutput "❌ 配置测试执行失败: $($_.Exception.Message)" "Red"
        return $false
    }
}

# 执行新技术集成
function Invoke-TechnologyIntegration {
    Write-ColorOutput "🔧 执行新技术集成..." "Cyan"
    
    $scriptPath = "scripts/tech-integration-2025.ps1"
    if (!(Test-Path $scriptPath)) {
        Write-ColorOutput "❌ 新技术集成脚本不存在: $scriptPath" "Red"
        return $false
    }
    
    $params = @("-Technology", $Technology)
    if ($Verbose) { $params += "-Verbose" }
    if ($Export) { $params += "-Export" }
    if ($Force) { $params += "-Install"; $params += "-Test"; $params += "-Benchmark" }
    
    try {
        & $scriptPath @params
        return $LASTEXITCODE -eq 0
    } catch {
        Write-ColorOutput "❌ 新技术集成执行失败: $($_.Exception.Message)" "Red"
        return $false
    }
}

# 生成综合报告
function Generate-ComprehensiveReport {
    param([string]$OutputPath = "reports/otlp-2025-comprehensive-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成综合报告..." "Cyan"
    
    $report = @"
# OTLP 2025 综合执行报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**执行操作**: $Action
**目标语言**: $Language
**目标技术**: $Technology

## 执行摘要

本次执行完成了以下操作：

"@

    if ($Action -eq "all" -or $Action -eq "version") {
        $report += "- ✅ 版本检查`n"
    }
    if ($Action -eq "all" -or $Action -eq "docs") {
        $report += "- ✅ 文档质量检查`n"
    }
    if ($Action -eq "all" -or $Action -eq "config") {
        $report += "- ✅ 配置测试`n"
    }
    if ($Action -eq "all" -or $Action -eq "tech") {
        $report += "- ✅ 新技术集成`n"
    }

    $report += @"

## 详细结果

### 版本检查结果
"@

    if ($Action -eq "all" -or $Action -eq "version") {
        $versionResult = Invoke-VersionCheck
        if ($versionResult) {
            $report += "`n✅ 版本检查执行成功`n"
        } else {
            $report += "`n❌ 版本检查执行失败`n"
        }
    }

    $report += @"

### 文档质量检查结果
"@

    if ($Action -eq "all" -or $Action -eq "docs") {
        $docsResult = Invoke-DocumentQualityCheck
        if ($docsResult) {
            $report += "`n✅ 文档质量检查执行成功`n"
        } else {
            $report += "`n❌ 文档质量检查执行失败`n"
        }
    }

    $report += @"

### 配置测试结果
"@

    if ($Action -eq "all" -or $Action -eq "config") {
        $configResult = Invoke-ConfigTest
        if ($configResult) {
            $report += "`n✅ 配置测试执行成功`n"
        } else {
            $report += "`n❌ 配置测试执行失败`n"
        }
    }

    $report += @"

### 新技术集成结果
"@

    if ($Action -eq "all" -or $Action -eq "tech") {
        $techResult = Invoke-TechnologyIntegration
        if ($techResult) {
            $report += "`n✅ 新技术集成执行成功`n"
        } else {
            $report += "`n❌ 新技术集成执行失败`n"
        }
    }

    $report += @"

## 建议

1. 定期运行综合检查
2. 修复发现的问题
3. 关注技术发展趋势
4. 建立持续改进机制

---
*报告由 OTLP 2025 综合执行脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 综合报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 综合执行开始..." "Green"
    Write-ColorOutput ("=" * 50) "Gray"
    
    # 显示执行信息
    Write-ColorOutput "📋 执行信息:" "White"
    Write-ColorOutput "  操作: $Action" "White"
    Write-ColorOutput "  语言: $Language" "White"
    Write-ColorOutput "  技术: $Technology" "White"
    Write-ColorOutput "  详细输出: $Verbose" "White"
    Write-ColorOutput "  导出报告: $Export" "White"
    Write-ColorOutput "  强制执行: $Force" "White"
    Write-ColorOutput ""
    
    $successCount = 0
    $totalCount = 0
    
    # 执行版本检查
    if ($Action -eq "all" -or $Action -eq "version") {
        $totalCount++
        if (Invoke-VersionCheck) {
            $successCount++
        }
        Write-ColorOutput ""
    }
    
    # 执行文档质量检查
    if ($Action -eq "all" -or $Action -eq "docs") {
        $totalCount++
        if (Invoke-DocumentQualityCheck) {
            $successCount++
        }
        Write-ColorOutput ""
    }
    
    # 执行配置测试
    if ($Action -eq "all" -or $Action -eq "config") {
        $totalCount++
        if (Invoke-ConfigTest) {
            $successCount++
        }
        Write-ColorOutput ""
    }
    
    # 执行新技术集成
    if ($Action -eq "all" -or $Action -eq "tech") {
        $totalCount++
        if (Invoke-TechnologyIntegration) {
            $successCount++
        }
        Write-ColorOutput ""
    }
    
    # 生成综合报告
    if ($Export) {
        Generate-ComprehensiveReport
    }
    
    # 显示执行结果
    Write-ColorOutput ("=" * 50) "Gray"
    Write-ColorOutput "📊 执行结果:" "White"
    Write-ColorOutput "  成功: $successCount/$totalCount" "White"
    Write-ColorOutput "  成功率: $([math]::Round($successCount / $totalCount * 100, 2))%" "White"
    
    if ($successCount -eq $totalCount) {
        Write-ColorOutput "✅ 所有操作执行成功!" "Green"
    } else {
        Write-ColorOutput "⚠️ 部分操作执行失败，请检查日志" "Yellow"
    }
    
    Write-ColorOutput ("=" * 50) "Gray"
}

# 检查参数
if ($args -contains "-h" -or $args -contains "--help" -or $args -contains "help") {
    Show-Help
    exit 0
}

# 执行主函数
Main
