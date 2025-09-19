# OTLP 2025 版本检查脚本
# 支持 Rust、Go、JavaScript 版本检查

param(
    [string]$Language = "all",
    [switch]$Verbose,
    [switch]$Export
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 检查 Rust 版本
function Check-RustVersions {
    Write-ColorOutput "🔍 检查 Rust 版本..." "Cyan"
    
    try {
        $rustVersion = rustc --version 2>$null
        if ($rustVersion) {
            Write-ColorOutput "✅ Rust: $rustVersion" "Green"
        } else {
            Write-ColorOutput "❌ Rust 未安装" "Red"
        }
        
        $cargoVersion = cargo --version 2>$null
        if ($cargoVersion) {
            Write-ColorOutput "✅ Cargo: $cargoVersion" "Green"
        }
        
        # 检查 OpenTelemetry Rust 依赖版本
        if (Test-Path "examples/minimal-rust/Cargo.toml") {
            $cargoToml = Get-Content "examples/minimal-rust/Cargo.toml" -Raw
            $otlpVersions = [regex]::Matches($cargoToml, 'opentelemetry[^"]*"([^"]*)"')
            foreach ($match in $otlpVersions) {
                Write-ColorOutput "📦 OpenTelemetry Rust: $($match.Groups[1].Value)" "Yellow"
            }
        }
    } catch {
        Write-ColorOutput "❌ Rust 检查失败: $($_.Exception.Message)" "Red"
    }
}

# 检查 Go 版本
function Check-GoVersions {
    Write-ColorOutput "🔍 检查 Go 版本..." "Cyan"
    
    try {
        $goVersion = go version 2>$null
        if ($goVersion) {
            Write-ColorOutput "✅ Go: $goVersion" "Green"
        } else {
            Write-ColorOutput "❌ Go 未安装" "Red"
        }
        
        # 检查 OpenTelemetry Go 依赖版本
        if (Test-Path "examples/minimal-go/go.mod") {
            $goMod = Get-Content "examples/minimal-go/go.mod" -Raw
            $otlpVersions = [regex]::Matches($goMod, 'go\.opentelemetry\.io/otel[^"]*v([^\s]+)')
            foreach ($match in $otlpVersions) {
                Write-ColorOutput "📦 OpenTelemetry Go: v$($match.Groups[1].Value)" "Yellow"
            }
        }
    } catch {
        Write-ColorOutput "❌ Go 检查失败: $($_.Exception.Message)" "Red"
    }
}

# 检查 JavaScript 版本
function Check-JavaScriptVersions {
    Write-ColorOutput "🔍 检查 JavaScript 版本..." "Cyan"
    
    try {
        $nodeVersion = node --version 2>$null
        if ($nodeVersion) {
            Write-ColorOutput "✅ Node.js: $nodeVersion" "Green"
        } else {
            Write-ColorOutput "❌ Node.js 未安装" "Red"
        }
        
        $npmVersion = npm --version 2>$null
        if ($npmVersion) {
            Write-ColorOutput "✅ npm: $npmVersion" "Green"
        }
        
        # 检查 OpenTelemetry JavaScript 依赖版本
        if (Test-Path "examples/minimal-javascript/package.json") {
            $packageJson = Get-Content "examples/minimal-javascript/package.json" -Raw | ConvertFrom-Json
            foreach ($dep in $packageJson.dependencies.PSObject.Properties) {
                if ($dep.Name -like "*opentelemetry*") {
                    Write-ColorOutput "📦 $($dep.Name): $($dep.Value)" "Yellow"
                }
            }
        }
    } catch {
        Write-ColorOutput "❌ JavaScript 检查失败: $($_.Exception.Message)" "Red"
    }
}

# 检查系统环境
function Check-SystemEnvironment {
    Write-ColorOutput "🔍 检查系统环境..." "Cyan"
    
    $os = [System.Environment]::OSVersion
    Write-ColorOutput "🖥️ 操作系统: $($os.VersionString)" "White"
    
    $psVersion = $PSVersionTable.PSVersion
    Write-ColorOutput "⚡ PowerShell: $psVersion" "White"
    
    $dotnetVersion = dotnet --version 2>$null
    if ($dotnetVersion) {
        Write-ColorOutput "🔷 .NET: $dotnetVersion" "White"
    }
}

# 生成版本报告
function Generate-VersionReport {
    param([string]$OutputPath = "reports/version-check-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成版本报告..." "Cyan"
    
    $report = @"
# OTLP 2025 版本检查报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**检查范围**: $Language

## 系统环境
- 操作系统: $([System.Environment]::OSVersion.VersionString)
- PowerShell: $($PSVersionTable.PSVersion)

## 语言版本检查

### Rust
"@

    try {
        $rustVersion = rustc --version 2>$null
        if ($rustVersion) {
            $report += "`n- ✅ Rust: $rustVersion`n"
        } else {
            $report += "`n- ❌ Rust 未安装`n"
        }
    } catch {
        $report += "`n- ❌ Rust 检查失败`n"
    }

    $report += @"

### Go
"@

    try {
        $goVersion = go version 2>$null
        if ($goVersion) {
            $report += "`n- ✅ Go: $goVersion`n"
        } else {
            $report += "`n- ❌ Go 未安装`n"
        }
    } catch {
        $report += "`n- ❌ Go 检查失败`n"
    }

    $report += @"

### JavaScript
"@

    try {
        $nodeVersion = node --version 2>$null
        if ($nodeVersion) {
            $report += "`n- ✅ Node.js: $nodeVersion`n"
        } else {
            $report += "`n- ❌ Node.js 未安装`n"
        }
    } catch {
        $report += "`n- ❌ JavaScript 检查失败`n"
    }

    $report += @"

## 依赖版本检查

### OpenTelemetry Rust 依赖
"@

    if (Test-Path "examples/minimal-rust/Cargo.toml") {
        $cargoToml = Get-Content "examples/minimal-rust/Cargo.toml" -Raw
        $otlpVersions = [regex]::Matches($cargoToml, 'opentelemetry[^"]*"([^"]*)"')
        foreach ($match in $otlpVersions) {
            $report += "`n- $($match.Groups[0].Value)" 
        }
    }

    $report += @"

### OpenTelemetry Go 依赖
"@

    if (Test-Path "examples/minimal-go/go.mod") {
        $goMod = Get-Content "examples/minimal-go/go.mod" -Raw
        $otlpVersions = [regex]::Matches($goMod, 'go\.opentelemetry\.io/otel[^"]*v([^\s]+)')
        foreach ($match in $otlpVersions) {
            $report += "`n- $($match.Groups[0].Value)"
        }
    }

    $report += @"

### OpenTelemetry JavaScript 依赖
"@

    if (Test-Path "examples/minimal-javascript/package.json") {
        $packageJson = Get-Content "examples/minimal-javascript/package.json" -Raw | ConvertFrom-Json
        foreach ($dep in $packageJson.dependencies.PSObject.Properties) {
            if ($dep.Name -like "*opentelemetry*") {
                $report += "`n- $($dep.Name): $($dep.Value)"
            }
        }
    }

    $report += @"

## 建议

1. 定期更新 OpenTelemetry 依赖到最新稳定版本
2. 关注安全公告和兼容性更新
3. 在生产环境中固定次要版本号
4. 启用依赖版本锁定机制

---
*报告由 OTLP 2025 版本检查脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 版本报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 版本检查开始..." "Green"
    Write-ColorOutput ("=" * 50) "Gray"
    
    Check-SystemEnvironment
    
    switch ($Language.ToLower()) {
        "rust" { Check-RustVersions }
        "go" { Check-GoVersions }
        "js" { Check-JavaScriptVersions }
        "javascript" { Check-JavaScriptVersions }
        "all" { 
            Check-RustVersions
            Check-GoVersions
            Check-JavaScriptVersions
        }
        default {
            Write-ColorOutput "❌ 不支持的语言: $Language" "Red"
            Write-ColorOutput "支持的语言: rust, go, js, all" "Yellow"
            exit 1
        }
    }
    
    if ($Export) {
        Generate-VersionReport
    }
    
    Write-ColorOutput ("=" * 50) "Gray"
    Write-ColorOutput "✅ 版本检查完成!" "Green"
}

# 执行主函数
Main
