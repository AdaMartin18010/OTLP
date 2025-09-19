# OTLP 2025 配置测试脚本
# 支持 Collector 配置验证、SDK 配置测试、集成测试

param(
    [string]$ConfigPath = "implementations/collector",
    [string]$Language = "all",
    [switch]$Validate,
    [switch]$Test,
    [switch]$Benchmark,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 验证 Collector 配置
function Test-CollectorConfig {
    param([string]$ConfigFile)
    
    Write-ColorOutput "🔍 验证 Collector 配置: $ConfigFile" "Cyan"
    
    $issues = @()
    $content = Get-Content $ConfigFile -Raw -Encoding UTF8
    
    try {
        # 检查 YAML 语法
        $yaml = [System.Web.Script.Serialization.JavaScriptSerializer]::new()
        $config = $yaml.DeserializeObject($content)
        
        # 检查必需字段
        $requiredFields = @("receivers", "processors", "exporters", "service")
        foreach ($field in $requiredFields) {
            if (!($config.ContainsKey($field))) {
                $issues += "❌ 缺少必需字段: $field"
            }
        }
        
        # 检查服务配置
        if ($config.ContainsKey("service")) {
            $service = $config.service
            if (!($service.ContainsKey("pipelines"))) {
                $issues += "❌ 服务配置缺少 pipelines"
            }
        }
        
        # 检查接收器配置
        if ($config.ContainsKey("receivers")) {
            $receivers = $config.receivers
            foreach ($receiver in $receivers.Keys) {
                $receiverConfig = $receivers[$receiver]
                
                # 检查 OTLP 接收器
                if ($receiver -like "*otlp*") {
                    if (!($receiverConfig.ContainsKey("protocols"))) {
                        $issues += "⚠️ OTLP 接收器缺少 protocols 配置"
                    }
                }
            }
        }
        
        # 检查导出器配置
        if ($config.ContainsKey("exporters")) {
            $exporters = $config.exporters
            foreach ($exporter in $exporters.Keys) {
                $exporterConfig = $exporters[$exporter]
                
                # 检查端点配置
                if ($exporterConfig.ContainsKey("endpoint")) {
                    $endpoint = $exporterConfig.endpoint
                    if (!($endpoint -match '^https?://')) {
                        $issues += "⚠️ 导出器端点格式可能不正确: $endpoint"
                    }
                }
            }
        }
        
        # 检查处理器配置
        if ($config.ContainsKey("processors")) {
            $processors = $config.processors
            foreach ($processor in $processors.Keys) {
                $processorConfig = $processors[$processor]
                
                # 检查批处理器配置
                if ($processor -like "*batch*") {
                    if (!($processorConfig.ContainsKey("timeout"))) {
                        $issues += "⚠️ 批处理器缺少 timeout 配置"
                    }
                    if (!($processorConfig.ContainsKey("send_batch_size"))) {
                        $issues += "⚠️ 批处理器缺少 send_batch_size 配置"
                    }
                }
            }
        }
        
    } catch {
        $issues += "❌ YAML 语法错误: $($_.Exception.Message)"
    }
    
    return $issues
}

# 测试 Rust 配置
function Test-RustConfig {
    Write-ColorOutput "🔍 测试 Rust 配置..." "Cyan"
    
    $issues = @()
    $cargoToml = "examples/minimal-rust/Cargo.toml"
    
    if (Test-Path $cargoToml) {
        $content = Get-Content $cargoToml -Raw -Encoding UTF8
        
        # 检查 OpenTelemetry 依赖
        if ($content -notmatch 'opentelemetry') {
            $issues += "❌ 缺少 OpenTelemetry 依赖"
        }
        
        # 检查必需特性
        $requiredFeatures = @("trace", "rt-tokio", "http-proto")
        foreach ($feature in $requiredFeatures) {
            if ($content -notmatch $feature) {
                $issues += "⚠️ 缺少特性: $feature"
            }
        }
        
        # 检查版本兼容性
        if ($content -match 'opentelemetry.*"([^"]*)"') {
            $version = $matches[1]
            if ($version -notmatch '^\d+\.\d+\.\d+') {
                $issues += "⚠️ 版本格式可能不正确: $version"
            }
        }
    } else {
        $issues += "❌ Cargo.toml 文件不存在"
    }
    
    return $issues
}

# 测试 Go 配置
function Test-GoConfig {
    Write-ColorOutput "🔍 测试 Go 配置..." "Cyan"
    
    $issues = @()
    $goMod = "examples/minimal-go/go.mod"
    
    if (Test-Path $goMod) {
        $content = Get-Content $goMod -Raw -Encoding UTF8
        
        # 检查 OpenTelemetry 依赖
        if ($content -notmatch 'go\.opentelemetry\.io/otel') {
            $issues += "❌ 缺少 OpenTelemetry 依赖"
        }
        
        # 检查版本格式
        $versions = [regex]::Matches($content, 'go\.opentelemetry\.io/otel[^"]*v([^\s]+)')
        foreach ($version in $versions) {
            $ver = $version.Groups[1].Value
            if ($ver -notmatch '^\d+\.\d+\.\d+') {
                $issues += "⚠️ 版本格式可能不正确: v$ver"
            }
        }
    } else {
        $issues += "❌ go.mod 文件不存在"
    }
    
    return $issues
}

# 测试 JavaScript 配置
function Test-JavaScriptConfig {
    Write-ColorOutput "🔍 测试 JavaScript 配置..." "Cyan"
    
    $issues = @()
    $packageJson = "examples/minimal-javascript/package.json"
    
    if (Test-Path $packageJson) {
        try {
            $content = Get-Content $packageJson -Raw -Encoding UTF8
            $package = $content | ConvertFrom-Json
            
            # 检查 OpenTelemetry 依赖
            $otlpDeps = $package.dependencies.PSObject.Properties | Where-Object { $_.Name -like "*opentelemetry*" }
            if ($otlpDeps.Count -eq 0) {
                $issues += "❌ 缺少 OpenTelemetry 依赖"
            }
            
            # 检查版本格式
            foreach ($dep in $otlpDeps) {
                $version = $dep.Value
                if ($version -notmatch '^\^?\d+\.\d+\.\d+') {
                    $issues += "⚠️ 版本格式可能不正确: $($dep.Name)@$version"
                }
            }
            
            # 检查必需依赖
            $requiredDeps = @("@opentelemetry/api", "@opentelemetry/sdk-node")
            foreach ($reqDep in $requiredDeps) {
                if (!($package.dependencies.PSObject.Properties.Name -contains $reqDep)) {
                    $issues += "⚠️ 缺少必需依赖: $reqDep"
                }
            }
            
        } catch {
            $issues += "❌ package.json 解析错误: $($_.Exception.Message)"
        }
    } else {
        $issues += "❌ package.json 文件不存在"
    }
    
    return $issues
}

# 运行集成测试
function Start-IntegrationTest {
    param([string]$Language)
    
    Write-ColorOutput "🧪 运行集成测试: $Language" "Cyan"
    
    $issues = @()
    
    switch ($Language.ToLower()) {
        "rust" {
            $projectPath = "examples/minimal-rust"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    cargo check --quiet
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "❌ Rust 项目编译失败"
                    } else {
                        Write-ColorOutput "✅ Rust 项目编译成功" "Green"
                    }
                } catch {
                    $issues += "❌ Rust 集成测试失败: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            } else {
                $issues += "❌ Rust 项目路径不存在"
            }
        }
        
        "go" {
            $projectPath = "examples/minimal-go"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    go mod tidy
                    go build -o /dev/null .
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "❌ Go 项目编译失败"
                    } else {
                        Write-ColorOutput "✅ Go 项目编译成功" "Green"
                    }
                } catch {
                    $issues += "❌ Go 集成测试失败: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            } else {
                $issues += "❌ Go 项目路径不存在"
            }
        }
        
        "js" {
            $projectPath = "examples/minimal-javascript"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    npm ci --silent
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "❌ JavaScript 依赖安装失败"
                    } else {
                        Write-ColorOutput "✅ JavaScript 依赖安装成功" "Green"
                    }
                } catch {
                    $issues += "❌ JavaScript 集成测试失败: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            } else {
                $issues += "❌ JavaScript 项目路径不存在"
            }
        }
    }
    
    return $issues
}

# 运行性能基准测试
function Start-BenchmarkTest {
    param([string]$Language)
    
    Write-ColorOutput "⚡ 运行性能基准测试: $Language" "Cyan"
    
    $issues = @()
    
    switch ($Language.ToLower()) {
        "rust" {
            $projectPath = "examples/minimal-rust"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    cargo bench --quiet 2>$null
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "⚠️ Rust 基准测试失败或无基准测试"
                    } else {
                        Write-ColorOutput "✅ Rust 基准测试完成" "Green"
                    }
                } catch {
                    $issues += "⚠️ Rust 基准测试异常: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            }
        }
        
        "go" {
            $projectPath = "examples/minimal-go"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    go test -bench=. -benchmem -run=^$ 2>$null
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "⚠️ Go 基准测试失败或无基准测试"
                    } else {
                        Write-ColorOutput "✅ Go 基准测试完成" "Green"
                    }
                } catch {
                    $issues += "⚠️ Go 基准测试异常: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            }
        }
        
        "js" {
            $projectPath = "examples/minimal-javascript"
            if (Test-Path $projectPath) {
                try {
                    Push-Location $projectPath
                    npm run benchmark 2>$null
                    if ($LASTEXITCODE -ne 0) {
                        $issues += "⚠️ JavaScript 基准测试失败或无基准测试"
                    } else {
                        Write-ColorOutput "✅ JavaScript 基准测试完成" "Green"
                    }
                } catch {
                    $issues += "⚠️ JavaScript 基准测试异常: $($_.Exception.Message)"
                } finally {
                    Pop-Location
                }
            }
        }
    }
    
    return $issues
}

# 生成配置测试报告
function Generate-ConfigTestReport {
    param([string]$OutputPath = "reports/config-test-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成配置测试报告..." "Cyan"
    
    $report = @"
# OTLP 2025 配置测试报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**测试路径**: $ConfigPath
**测试语言**: $Language

## 配置验证结果

### Collector 配置
"@

    $configFiles = Get-ChildItem -Path $ConfigPath -Filter "*.yaml" -Recurse
    foreach ($file in $configFiles) {
        $issues = Test-CollectorConfig $file.FullName
        $report += "`n#### $($file.Name)`n"
        if ($issues.Count -eq 0) {
            $report += "✅ 配置验证通过`n"
        } else {
            foreach ($issue in $issues) {
                $report += "- $issue`n"
            }
        }
    }

    $report += @"

### 语言配置测试
"@

    if ($Language -eq "all" -or $Language -eq "rust") {
        $rustIssues = Test-RustConfig
        $report += "`n#### Rust 配置`n"
        if ($rustIssues.Count -eq 0) {
            $report += "✅ Rust 配置验证通过`n"
        } else {
            foreach ($issue in $rustIssues) {
                $report += "- $issue`n"
            }
        }
    }

    if ($Language -eq "all" -or $Language -eq "go") {
        $goIssues = Test-GoConfig
        $report += "`n#### Go 配置`n"
        if ($goIssues.Count -eq 0) {
            $report += "✅ Go 配置验证通过`n"
        } else {
            foreach ($issue in $goIssues) {
                $report += "- $issue`n"
            }
        }
    }

    if ($Language -eq "all" -or $Language -eq "js") {
        $jsIssues = Test-JavaScriptConfig
        $report += "`n#### JavaScript 配置`n"
        if ($jsIssues.Count -eq 0) {
            $report += "✅ JavaScript 配置验证通过`n"
        } else {
            foreach ($issue in $jsIssues) {
                $report += "- $issue`n"
            }
        }
    }

    $report += @"

## 集成测试结果
"@

    if ($Test) {
        if ($Language -eq "all" -or $Language -eq "rust") {
            $rustTestIssues = Start-IntegrationTest "rust"
            $report += "`n#### Rust 集成测试`n"
            if ($rustTestIssues.Count -eq 0) {
                $report += "✅ Rust 集成测试通过`n"
            } else {
                foreach ($issue in $rustTestIssues) {
                    $report += "- $issue`n"
                }
            }
        }

        if ($Language -eq "all" -or $Language -eq "go") {
            $goTestIssues = Start-IntegrationTest "go"
            $report += "`n#### Go 集成测试`n"
            if ($goTestIssues.Count -eq 0) {
                $report += "✅ Go 集成测试通过`n"
            } else {
                foreach ($issue in $goTestIssues) {
                    $report += "- $issue`n"
                }
            }
        }

        if ($Language -eq "all" -or $Language -eq "js") {
            $jsTestIssues = Start-IntegrationTest "js"
            $report += "`n#### JavaScript 集成测试`n"
            if ($jsTestIssues.Count -eq 0) {
                $report += "✅ JavaScript 集成测试通过`n"
            } else {
                foreach ($issue in $jsTestIssues) {
                    $report += "- $issue`n"
                }
            }
        }
    }

    $report += @"

## 性能基准测试结果
"@

    if ($Benchmark) {
        if ($Language -eq "all" -or $Language -eq "rust") {
            $rustBenchIssues = Start-BenchmarkTest "rust"
            $report += "`n#### Rust 基准测试`n"
            if ($rustBenchIssues.Count -eq 0) {
                $report += "✅ Rust 基准测试通过`n"
            } else {
                foreach ($issue in $rustBenchIssues) {
                    $report += "- $issue`n"
                }
            }
        }

        if ($Language -eq "all" -or $Language -eq "go") {
            $goBenchIssues = Start-BenchmarkTest "go"
            $report += "`n#### Go 基准测试`n"
            if ($goBenchIssues.Count -eq 0) {
                $report += "✅ Go 基准测试通过`n"
            } else {
                foreach ($issue in $goBenchIssues) {
                    $report += "- $issue`n"
                }
            }
        }

        if ($Language -eq "all" -or $Language -eq "js") {
            $jsBenchIssues = Start-BenchmarkTest "js"
            $report += "`n#### JavaScript 基准测试`n"
            if ($jsBenchIssues.Count -eq 0) {
                $report += "✅ JavaScript 基准测试通过`n"
            } else {
                foreach ($issue in $jsBenchIssues) {
                    $report += "- $issue`n"
                }
            }
        }
    }

    $report += @"

## 建议

1. 定期运行配置验证
2. 修复发现的配置问题
3. 建立配置管理规范
4. 启用自动化测试

---
*报告由 OTLP 2025 配置测试脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 配置测试报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 配置测试开始..." "Green"
    Write-ColorOutput ("=" * 50) "Gray"
    
    if (!(Test-Path $ConfigPath)) {
        Write-ColorOutput "❌ 配置路径不存在: $ConfigPath" "Red"
        exit 1
    }
    
    # 验证配置
    if ($Validate) {
        Write-ColorOutput "🔍 验证配置..." "Cyan"
        $configFiles = Get-ChildItem -Path $ConfigPath -Filter "*.yaml" -Recurse
        foreach ($file in $configFiles) {
            $issues = Test-CollectorConfig $file.FullName
            if ($issues.Count -gt 0) {
                Write-ColorOutput "📄 $($file.Name):" "Yellow"
                foreach ($issue in $issues) {
                    Write-ColorOutput "  $issue" "Red"
                }
            } else {
                if ($Verbose) {
                    Write-ColorOutput "✅ $($file.Name): 配置验证通过" "Green"
                }
            }
        }
    }
    
    # 测试语言配置
    if ($Language -eq "all" -or $Language -eq "rust") {
        $rustIssues = Test-RustConfig
        if ($rustIssues.Count -gt 0) {
            Write-ColorOutput "📄 Rust 配置:" "Yellow"
            foreach ($issue in $rustIssues) {
                Write-ColorOutput "  $issue" "Red"
            }
        } else {
            if ($Verbose) {
                Write-ColorOutput "✅ Rust 配置验证通过" "Green"
            }
        }
    }
    
    if ($Language -eq "all" -or $Language -eq "go") {
        $goIssues = Test-GoConfig
        if ($goIssues.Count -gt 0) {
            Write-ColorOutput "📄 Go 配置:" "Yellow"
            foreach ($issue in $goIssues) {
                Write-ColorOutput "  $issue" "Red"
            }
        } else {
            if ($Verbose) {
                Write-ColorOutput "✅ Go 配置验证通过" "Green"
            }
        }
    }
    
    if ($Language -eq "all" -or $Language -eq "js") {
        $jsIssues = Test-JavaScriptConfig
        if ($jsIssues.Count -gt 0) {
            Write-ColorOutput "📄 JavaScript 配置:" "Yellow"
            foreach ($issue in $jsIssues) {
                Write-ColorOutput "  $issue" "Red"
            }
        } else {
            if ($Verbose) {
                Write-ColorOutput "✅ JavaScript 配置验证通过" "Green"
            }
        }
    }
    
    # 运行集成测试
    if ($Test) {
        Write-ColorOutput "🧪 运行集成测试..." "Cyan"
        if ($Language -eq "all" -or $Language -eq "rust") {
            Start-IntegrationTest "rust"
        }
        if ($Language -eq "all" -or $Language -eq "go") {
            Start-IntegrationTest "go"
        }
        if ($Language -eq "all" -or $Language -eq "js") {
            Start-IntegrationTest "js"
        }
    }
    
    # 运行性能基准测试
    if ($Benchmark) {
        Write-ColorOutput "⚡ 运行性能基准测试..." "Cyan"
        if ($Language -eq "all" -or $Language -eq "rust") {
            Start-BenchmarkTest "rust"
        }
        if ($Language -eq "all" -or $Language -eq "go") {
            Start-BenchmarkTest "go"
        }
        if ($Language -eq "all" -or $Language -eq "js") {
            Start-BenchmarkTest "js"
        }
    }
    
    # 生成报告
    if ($Validate -or $Test -or $Benchmark) {
        Generate-ConfigTestReport
    }
    
    Write-ColorOutput ("=" * 50) "Gray"
    Write-ColorOutput "✅ 配置测试完成!" "Green"
}

# 执行主函数
Main
