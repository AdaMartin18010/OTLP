Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
    [string]$CollectorEndpoint,
    [int]$TestDuration,
    [switch]$SkipRust,
    [switch]$SkipGo,
    [switch]$SkipPython
)

# 设置默认值
if (-not $CollectorEndpoint) {
    $CollectorEndpoint = "http://localhost:4317"
}

if (-not $TestDuration) {
    $TestDuration = 30
}

# 参数验证
if ([string]::IsNullOrEmpty($CollectorEndpoint)) {
    throw "CollectorEndpoint 不能为空"
}

if ($TestDuration -lt 1 -or $TestDuration -gt 1000) {
    throw "TestDuration 必须在 1-1000 之间"
}

Write-Host "=== OpenTelemetry 端到端集成测试 ===" -ForegroundColor Green
Write-Host "Collector端点: $CollectorEndpoint" -ForegroundColor Yellow
Write-Host "测试持续时间: $TestDuration 秒" -ForegroundColor Yellow

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir

# 测试结果
$testResults = @{
    Rust = @{ Success = $false; Error = $null; Duration = 0 }
    Go = @{ Success = $false; Error = $null; Duration = 0 }
    Python = @{ Success = $false; Error = $null; Duration = 0 }
}

# 测试Rust示例
if (-not $SkipRust) {
    Write-Host "`n=== 测试Rust示例 ===" -ForegroundColor Cyan
    try {
        $rustDir = Join-Path $projectRoot "examples\minimal-rust"
        if (Test-Path $rustDir) {
            $startTime = Get-Date
            Push-Location $rustDir
            
            # 设置环境变量
            $env:OTEL_EXPORTER_OTLP_ENDPOINT = $CollectorEndpoint
            $env:OTEL_SERVICE_NAME = "integration-test-rust"
            
            # 运行Rust示例
            $output = cargo run 2>&1
            $endTime = Get-Date
            $duration = ($endTime - $startTime).TotalSeconds
            
            if ($LASTEXITCODE -eq 0) {
                $testResults.Rust.Success = $true
                $testResults.Rust.Duration = $duration
                Write-Host "✅ Rust示例测试成功 (耗时: $([math]::Round($duration, 2))秒)" -ForegroundColor Green
            } else {
                $testResults.Rust.Error = "退出码: $LASTEXITCODE"
                Write-Host "❌ Rust示例测试失败: $($testResults.Rust.Error)" -ForegroundColor Red
            }
            
            Pop-Location
        } else {
            $testResults.Rust.Error = "目录不存在: $rustDir"
            Write-Host "❌ Rust示例目录不存在" -ForegroundColor Red
        }
    } catch {
        $testResults.Rust.Error = $_.Exception.Message
        Write-Host "❌ Rust示例测试异常: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 测试Go示例
if (-not $SkipGo) {
    Write-Host "`n=== 测试Go示例 ===" -ForegroundColor Cyan
    try {
        $goDir = Join-Path $projectRoot "examples\minimal-go"
        if (Test-Path $goDir) {
            $startTime = Get-Date
            Push-Location $goDir
            
            # 设置环境变量
            $env:OTEL_EXPORTER_OTLP_ENDPOINT = $CollectorEndpoint
            $env:OTEL_SERVICE_NAME = "integration-test-go"
            
            # 尝试运行Go示例
            $output = go run . 2>&1
            $endTime = Get-Date
            $duration = ($endTime - $startTime).TotalSeconds
            
            if ($LASTEXITCODE -eq 0) {
                $testResults.Go.Success = $true
                $testResults.Go.Duration = $duration
                Write-Host "✅ Go示例测试成功 (耗时: $([math]::Round($duration, 2))秒)" -ForegroundColor Green
            } else {
                $testResults.Go.Error = "退出码: $LASTEXITCODE"
                Write-Host "❌ Go示例测试失败: $($testResults.Go.Error)" -ForegroundColor Red
                Write-Host "输出: $output" -ForegroundColor Yellow
            }
            
            Pop-Location
        } else {
            $testResults.Go.Error = "目录不存在: $goDir"
            Write-Host "❌ Go示例目录不存在" -ForegroundColor Red
        }
    } catch {
        $testResults.Go.Error = $_.Exception.Message
        Write-Host "❌ Go示例测试异常: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 测试Python示例
if (-not $SkipPython) {
    Write-Host "`n=== 测试Python示例 ===" -ForegroundColor Cyan
    try {
        $pythonDir = Join-Path $projectRoot "examples\minimal-python"
        if (Test-Path $pythonDir) {
            $startTime = Get-Date
            Push-Location $pythonDir
            
            # 设置环境变量
            $env:OTEL_EXPORTER_OTLP_ENDPOINT = $CollectorEndpoint
            $env:OTEL_SERVICE_NAME = "integration-test-python"
            
            # 检查Python是否可用
            $pythonCmd = $null
            if (Get-Command python -ErrorAction SilentlyContinue) {
                $pythonCmd = "python"
            } elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
                $pythonCmd = "python3"
            } elseif (Get-Command py -ErrorAction SilentlyContinue) {
                $pythonCmd = "py"
            }
            
            if ($pythonCmd) {
                # 运行Python示例
                $output = & $pythonCmd main.py 2>&1
                $endTime = Get-Date
                $duration = ($endTime - $startTime).TotalSeconds
                
                if ($LASTEXITCODE -eq 0) {
                    $testResults.Python.Success = $true
                    $testResults.Python.Duration = $duration
                    Write-Host "✅ Python示例测试成功 (耗时: $([math]::Round($duration, 2))秒)" -ForegroundColor Green
                } else {
                    $testResults.Python.Error = "退出码: $LASTEXITCODE"
                    Write-Host "❌ Python示例测试失败: $($testResults.Python.Error)" -ForegroundColor Red
                    Write-Host "输出: $output" -ForegroundColor Yellow
                }
            } else {
                $testResults.Python.Error = "未找到Python解释器"
                Write-Host "❌ 未找到Python解释器" -ForegroundColor Red
            }
            
            Pop-Location
        } else {
            $testResults.Python.Error = "目录不存在: $pythonDir"
            Write-Host "❌ Python示例目录不存在" -ForegroundColor Red
        }
    } catch {
        $testResults.Python.Error = $_.Exception.Message
        Write-Host "❌ Python示例测试异常: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 输出测试结果摘要
Write-Host "`n=== 测试结果摘要 ===" -ForegroundColor Green
$totalTests = 0
$passedTests = 0

foreach ($language in @("Rust", "Go", "Python")) {
    $totalTests++
    if ($testResults[$language].Success) {
        $passedTests++
        Write-Host "✅ $language`: 通过 (耗时: $([math]::Round($testResults[$language].Duration, 2))秒)" -ForegroundColor Green
    } else {
        Write-Host "❌ $language`: 失败 - $($testResults[$language].Error)" -ForegroundColor Red
    }
}

Write-Host "`n总体结果: $passedTests/$totalTests 测试通过" -ForegroundColor $(if ($passedTests -eq $totalTests) { "Green" } else { "Yellow" })

# 生成测试报告
$reportPath = Join-Path $projectRoot "test-report-$(Get-Date -Format 'yyyyMMdd-HHmmss').json"
$report = @{
    Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    CollectorEndpoint = $CollectorEndpoint
    TestDuration = $TestDuration
    Results = $testResults
    Summary = @{
        Total = $totalTests
        Passed = $passedTests
        Failed = $totalTests - $passedTests
        SuccessRate = [math]::Round(($passedTests / $totalTests) * 100, 2)
    }
}

$report | ConvertTo-Json -Depth 3 | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "`n测试报告已保存到: $reportPath" -ForegroundColor Cyan

if ($passedTests -eq $totalTests) {
    Write-Host "`n🎉 所有测试通过！OpenTelemetry集成测试成功完成。" -ForegroundColor Green
    exit 0
} else {
    Write-Host "`n⚠️ 部分测试失败，请检查上述错误信息。" -ForegroundColor Yellow
    exit 1
}
