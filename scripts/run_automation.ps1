# OpenTelemetry 2025 自动化系统 PowerShell 脚本
# 支持 Windows PowerShell 和 PowerShell Core

param(
    [switch]$SkipDependencyCheck,
    [switch]$Verbose
)

# 设置控制台编码
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8

Write-Host "🚀 OpenTelemetry 2025 自动化系统" -ForegroundColor Green
Write-Host "================================================" -ForegroundColor Green
Write-Host ""

# 检查Python环境
$pythonCmd = $null

# 优先使用虚拟环境
if (Test-Path ".venv\Scripts\python.exe") {
    Write-Host "✅ 找到虚拟环境" -ForegroundColor Green
    $pythonCmd = ".venv\Scripts\python.exe"
} elseif (Test-Path ".venv\bin\python") {
    Write-Host "✅ 找到虚拟环境 (Linux/macOS)" -ForegroundColor Green
    $pythonCmd = ".venv\bin\python"
} else {
    Write-Host "⚠️ 未找到虚拟环境，使用系统Python" -ForegroundColor Yellow
    $pythonCmd = "python"
}

# 检查Python是否可用
try {
    $pythonVersion = & $pythonCmd --version 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Python版本: $pythonVersion" -ForegroundColor Green
    } else {
        throw "Python不可用"
    }
} catch {
    Write-Host "❌ Python不可用，请检查安装" -ForegroundColor Red
    Read-Host "按回车键退出"
    exit 1
}

# 检查依赖
if (-not $SkipDependencyCheck) {
    Write-Host "🔍 检查依赖..." -ForegroundColor Cyan
    
    try {
        & $pythonCmd -c "import yaml" 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ 依赖检查通过" -ForegroundColor Green
        } else {
            throw "缺少PyYAML依赖"
        }
    } catch {
        Write-Host "❌ 缺少PyYAML依赖，正在安装..." -ForegroundColor Yellow
        & $pythonCmd -m pip install PyYAML
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ 依赖安装成功" -ForegroundColor Green
        } else {
            Write-Host "❌ 依赖安装失败" -ForegroundColor Red
            Read-Host "按回车键退出"
            exit 1
        }
    }
}

Write-Host ""
Write-Host "🚀 开始运行自动化任务..." -ForegroundColor Cyan
Write-Host ""

# 运行自动化脚本
try {
    if ($Verbose) {
        & $pythonCmd scripts/run_all_automation.py
    } else {
        & $pythonCmd scripts/run_all_automation.py 2>&1 | ForEach-Object {
            if ($_ -match "✅|❌|📁|📄|🔄|📊|🎉|⚠️") {
                Write-Host $_ -ForegroundColor Green
            } elseif ($_ -match "错误|失败|异常") {
                Write-Host $_ -ForegroundColor Red
            } else {
                Write-Host $_
            }
        }
    }
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host ""
        Write-Host "🎉 自动化任务完成！" -ForegroundColor Green
    } else {
        Write-Host ""
        Write-Host "⚠️ 部分任务执行失败" -ForegroundColor Yellow
    }
} catch {
    Write-Host "❌ 执行过程中发生错误: $_" -ForegroundColor Red
}

Write-Host ""
Write-Host "💡 提示:" -ForegroundColor Cyan
Write-Host "- 查看 doc/00_项目概览与导航/ 目录获取最新文档" -ForegroundColor White
Write-Host "- 查看 scripts/backups/ 目录获取备份文件" -ForegroundColor White
Write-Host ""

# 询问是否打开结果目录
$openDir = Read-Host "是否打开结果目录? (y/n)"
if ($openDir -eq "y" -or $openDir -eq "Y") {
    $resultDir = "doc\00_项目概览与导航"
    if (Test-Path $resultDir) {
        if ($IsWindows -or $env:OS -eq "Windows_NT") {
            Start-Process "explorer.exe" -ArgumentList $resultDir
        } else {
            Start-Process "open" -ArgumentList $resultDir
        }
    }
}

Read-Host "按回车键退出"
