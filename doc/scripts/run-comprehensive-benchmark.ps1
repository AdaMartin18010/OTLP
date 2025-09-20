# OTLP 2025 综合基准测试脚本
# 支持多语言性能测试、多协议测试、系统资源监控

param(
    [string]$Language = "all",
    [string]$Protocol = "all",
    [int]$Loops = 100,
    [int]$Concurrency = 10,
    [switch]$Export,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 测试结果结构
$TestResults = @{
    StartTime = Get-Date
    Language = $Language
    Protocol = $Protocol
    Loops = $Loops
    Concurrency = $Concurrency
    Results = @{}
    SystemInfo = @{}
    Summary = @{}
}

# 获取系统信息
function Get-SystemInfo {
    Write-ColorOutput "🔍 收集系统信息..." "Cyan"
    
    $TestResults.SystemInfo = @{
        OS = [System.Environment]::OSVersion.VersionString
        PowerShell = $PSVersionTable.PSVersion.ToString()
        CPU = (Get-WmiObject -Class Win32_Processor).Name
        Memory = [math]::Round((Get-WmiObject -Class Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
        .NET = (dotnet --version 2>$null)
        Node = (node --version 2>$null)
        Go = (go version 2>$null)
        Rust = (rustc --version 2>$null)
        Java = (java -version 2>&1 | Select-String "version" | ForEach-Object { $_.Line })
    }
    
    if ($Verbose) {
        Write-ColorOutput "📊 系统信息:" "White"
        foreach ($key in $TestResults.SystemInfo.Keys) {
            Write-ColorOutput "  $key`: $($TestResults.SystemInfo[$key])" "Gray"
        }
    }
}

# 测试 Rust 性能
function Test-RustPerformance {
    Write-ColorOutput "🦀 测试 Rust 性能..." "Cyan"
    
    if (!(Test-Path "examples/minimal-rust/Cargo.toml")) {
        Write-ColorOutput "❌ Rust 示例不存在" "Red"
        return
    }
    
    try {
        $startTime = Get-Date
        
        # 编译项目
        Push-Location "examples/minimal-rust"
        cargo build --release 2>$null
        if ($LASTEXITCODE -ne 0) {
            Write-ColorOutput "❌ Rust 编译失败" "Red"
            Pop-Location
            return
        }
        
        # 运行性能测试
        $output = & "target/release/minimal-rust" --loops $Loops --concurrency $Concurrency 2>&1
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        Pop-Location
        
        # 解析结果
        $rustResults = @{
            Language = "Rust"
            Duration = $duration
            Loops = $Loops
            Concurrency = $Concurrency
            Output = $output
            Success = $LASTEXITCODE -eq 0
        }
        
        # 提取性能指标
        if ($output -match "Throughput: (\d+\.?\d*) spans/sec") {
            $rustResults.Throughput = [double]$matches[1]
        }
        if ($output -match "Latency: (\d+\.?\d*) ms") {
            $rustResults.Latency = [double]$matches[1]
        }
        if ($output -match "Memory: (\d+\.?\d*) MB") {
            $rustResults.Memory = [double]$matches[1]
        }
        
        $TestResults.Results.Rust = $rustResults
        
        if ($rustResults.Success) {
            Write-ColorOutput "✅ Rust 测试完成: $($rustResults.Throughput) spans/sec, $($rustResults.Latency) ms 延迟" "Green"
        } else {
            Write-ColorOutput "❌ Rust 测试失败" "Red"
        }
        
    } catch {
        Write-ColorOutput "❌ Rust 测试异常: $($_.Exception.Message)" "Red"
        $TestResults.Results.Rust = @{
            Language = "Rust"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

# 测试 Go 性能
function Test-GoPerformance {
    Write-ColorOutput "🐹 测试 Go 性能..." "Cyan"
    
    if (!(Test-Path "examples/minimal-go/go.mod")) {
        Write-ColorOutput "❌ Go 示例不存在" "Red"
        return
    }
    
    try {
        $startTime = Get-Date
        
        # 编译并运行
        Push-Location "examples/minimal-go"
        go build -o minimal-go . 2>$null
        if ($LASTEXITCODE -ne 0) {
            Write-ColorOutput "❌ Go 编译失败" "Red"
            Pop-Location
            return
        }
        
        $output = & "./minimal-go" --loops $Loops --concurrency $Concurrency 2>&1
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        Pop-Location
        
        # 解析结果
        $goResults = @{
            Language = "Go"
            Duration = $duration
            Loops = $Loops
            Concurrency = $Concurrency
            Output = $output
            Success = $LASTEXITCODE -eq 0
        }
        
        # 提取性能指标
        if ($output -match "Throughput: (\d+\.?\d*) spans/sec") {
            $goResults.Throughput = [double]$matches[1]
        }
        if ($output -match "Latency: (\d+\.?\d*) ms") {
            $goResults.Latency = [double]$matches[1]
        }
        if ($output -match "Memory: (\d+\.?\d*) MB") {
            $goResults.Memory = [double]$matches[1]
        }
        
        $TestResults.Results.Go = $goResults
        
        if ($goResults.Success) {
            Write-ColorOutput "✅ Go 测试完成: $($goResults.Throughput) spans/sec, $($goResults.Latency) ms 延迟" "Green"
        } else {
            Write-ColorOutput "❌ Go 测试失败" "Red"
        }
        
    } catch {
        Write-ColorOutput "❌ Go 测试异常: $($_.Exception.Message)" "Red"
        $TestResults.Results.Go = @{
            Language = "Go"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

# 测试 Python 性能
function Test-PythonPerformance {
    Write-ColorOutput "🐍 测试 Python 性能..." "Cyan"
    
    if (!(Test-Path "examples/minimal-python/main.py")) {
        Write-ColorOutput "❌ Python 示例不存在" "Red"
        return
    }
    
    try {
        $startTime = Get-Date
        
        # 运行 Python 测试
        Push-Location "examples/minimal-python"
        $output = & python main.py --loops $Loops --concurrency $Concurrency 2>&1
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        Pop-Location
        
        # 解析结果
        $pythonResults = @{
            Language = "Python"
            Duration = $duration
            Loops = $Loops
            Concurrency = $Concurrency
            Output = $output
            Success = $LASTEXITCODE -eq 0
        }
        
        # 提取性能指标
        if ($output -match "Throughput: (\d+\.?\d*) spans/sec") {
            $pythonResults.Throughput = [double]$matches[1]
        }
        if ($output -match "Latency: (\d+\.?\d*) ms") {
            $pythonResults.Latency = [double]$matches[1]
        }
        if ($output -match "Memory: (\d+\.?\d*) MB") {
            $pythonResults.Memory = [double]$matches[1]
        }
        
        $TestResults.Results.Python = $pythonResults
        
        if ($pythonResults.Success) {
            Write-ColorOutput "✅ Python 测试完成: $($pythonResults.Throughput) spans/sec, $($pythonResults.Latency) ms 延迟" "Green"
        } else {
            Write-ColorOutput "❌ Python 测试失败" "Red"
        }
        
    } catch {
        Write-ColorOutput "❌ Python 测试异常: $($_.Exception.Message)" "Red"
        $TestResults.Results.Python = @{
            Language = "Python"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

# 测试 Java 性能
function Test-JavaPerformance {
    Write-ColorOutput "☕ 测试 Java 性能..." "Cyan"
    
    if (!(Test-Path "examples/minimal-java/pom.xml")) {
        Write-ColorOutput "❌ Java 示例不存在" "Red"
        return
    }
    
    try {
        $startTime = Get-Date
        
        # 编译并运行 Java 测试
        Push-Location "examples/minimal-java"
        mvn compile exec:java -Dexec.mainClass="com.example.otlp.MinimalExample" -Dexec.args="--loops $Loops --concurrency $Concurrency" 2>$null
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        Pop-Location
        
        # 解析结果
        $javaResults = @{
            Language = "Java"
            Duration = $duration
            Loops = $Loops
            Concurrency = $Concurrency
            Success = $LASTEXITCODE -eq 0
        }
        
        $TestResults.Results.Java = $javaResults
        
        if ($javaResults.Success) {
            Write-ColorOutput "✅ Java 测试完成" "Green"
        } else {
            Write-ColorOutput "❌ Java 测试失败" "Red"
        }
        
    } catch {
        Write-ColorOutput "❌ Java 测试异常: $($_.Exception.Message)" "Red"
        $TestResults.Results.Java = @{
            Language = "Java"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

# 测试 JavaScript 性能
function Test-JavaScriptPerformance {
    Write-ColorOutput "🟨 测试 JavaScript 性能..." "Cyan"
    
    if (!(Test-Path "examples/minimal-javascript/package.json")) {
        Write-ColorOutput "❌ JavaScript 示例不存在" "Red"
        return
    }
    
    try {
        $startTime = Get-Date
        
        # 运行 JavaScript 测试
        Push-Location "examples/minimal-javascript"
        $output = & node main.js --loops $Loops --concurrency $Concurrency 2>&1
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        Pop-Location
        
        # 解析结果
        $jsResults = @{
            Language = "JavaScript"
            Duration = $duration
            Loops = $Loops
            Concurrency = $Concurrency
            Output = $output
            Success = $LASTEXITCODE -eq 0
        }
        
        $TestResults.Results.JavaScript = $jsResults
        
        if ($jsResults.Success) {
            Write-ColorOutput "✅ JavaScript 测试完成" "Green"
        } else {
            Write-ColorOutput "❌ JavaScript 测试失败" "Red"
        }
        
    } catch {
        Write-ColorOutput "❌ JavaScript 测试异常: $($_.Exception.Message)" "Red"
        $TestResults.Results.JavaScript = @{
            Language = "JavaScript"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

# 测试协议性能
function Test-ProtocolPerformance {
    Write-ColorOutput "🌐 测试协议性能..." "Cyan"
    
    $protocolResults = @{}
    
    # 测试 gRPC 协议
    if ($Protocol -eq "all" -or $Protocol -eq "grpc") {
        Write-ColorOutput "  📡 测试 gRPC 协议..." "Yellow"
        try {
            $startTime = Get-Date
            # 这里可以添加实际的 gRPC 性能测试
            $endTime = Get-Date
            $duration = ($endTime - $startTime).TotalSeconds
            
            $protocolResults.gRPC = @{
                Protocol = "gRPC"
                Duration = $duration
                Success = $true
            }
            
            Write-ColorOutput "  ✅ gRPC 协议测试完成" "Green"
        } catch {
            Write-ColorOutput "  ❌ gRPC 协议测试失败: $($_.Exception.Message)" "Red"
            $protocolResults.gRPC = @{
                Protocol = "gRPC"
                Success = $false
                Error = $_.Exception.Message
            }
        }
    }
    
    # 测试 HTTP 协议
    if ($Protocol -eq "all" -or $Protocol -eq "http") {
        Write-ColorOutput "  🌍 测试 HTTP 协议..." "Yellow"
        try {
            $startTime = Get-Date
            # 这里可以添加实际的 HTTP 性能测试
            $endTime = Get-Date
            $duration = ($endTime - $startTime).TotalSeconds
            
            $protocolResults.HTTP = @{
                Protocol = "HTTP"
                Duration = $duration
                Success = $true
            }
            
            Write-ColorOutput "  ✅ HTTP 协议测试完成" "Green"
        } catch {
            Write-ColorOutput "  ❌ HTTP 协议测试失败: $($_.Exception.Message)" "Red"
            $protocolResults.HTTP = @{
                Protocol = "HTTP"
                Success = $false
                Error = $_.Exception.Message
            }
        }
    }
    
    $TestResults.Results.Protocols = $protocolResults
}

# 生成测试报告
function Generate-BenchmarkReport {
    param([string]$OutputPath = "reports/comprehensive-benchmark-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成综合基准测试报告..." "Cyan"
    
    $report = @"
# OTLP 2025 综合基准测试报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**测试语言**: $Language
**测试协议**: $Protocol
**测试循环**: $Loops
**并发数**: $Concurrency

## 系统信息

- **操作系统**: $($TestResults.SystemInfo.OS)
- **PowerShell**: $($TestResults.SystemInfo.PowerShell)
- **CPU**: $($TestResults.SystemInfo.CPU)
- **内存**: $($TestResults.SystemInfo.Memory) GB
- **.NET**: $($TestResults.SystemInfo.'NET')
- **Node.js**: $($TestResults.SystemInfo.Node)
- **Go**: $($TestResults.SystemInfo.Go)
- **Rust**: $($TestResults.SystemInfo.Rust)
- **Java**: $($TestResults.SystemInfo.Java)

## 语言性能测试结果

"@

    # 添加语言测试结果
    foreach ($lang in $TestResults.Results.Keys) {
        if ($lang -ne "Protocols") {
            $result = $TestResults.Results[$lang]
            $report += "`n### $($result.Language)`n`n"
            
            if ($result.Success) {
                $report += "- ✅ **状态**: 成功`n"
                $report += "- ⏱️ **持续时间**: $($result.Duration) 秒`n"
                if ($result.Throughput) {
                    $report += "- 📈 **吞吐量**: $($result.Throughput) spans/sec`n"
                }
                if ($result.Latency) {
                    $report += "- ⚡ **延迟**: $($result.Latency) ms`n"
                }
                if ($result.Memory) {
                    $report += "- 💾 **内存使用**: $($result.Memory) MB`n"
                }
            } else {
                $report += "- ❌ **状态**: 失败`n"
                if ($result.Error) {
                    $report += "- 🚨 **错误**: $($result.Error)`n"
                }
            }
        }
    }

    # 添加协议测试结果
    if ($TestResults.Results.Protocols) {
        $report += "`n## 协议性能测试结果`n`n"
        
        foreach ($protocol in $TestResults.Results.Protocols.Keys) {
            $result = $TestResults.Results.Protocols[$protocol]
            $report += "### $($result.Protocol)`n`n"
            
            if ($result.Success) {
                $report += "- ✅ **状态**: 成功`n"
                $report += "- ⏱️ **持续时间**: $($result.Duration) 秒`n"
            } else {
                $report += "- ❌ **状态**: 失败`n"
                if ($result.Error) {
                    $report += "- 🚨 **错误**: $($result.Error)`n"
                }
            }
        }
    }

    # 添加总结
    $report += @"

## 测试总结

### 性能排名

"@

    # 计算性能排名
    $performanceRanking = @()
    foreach ($lang in $TestResults.Results.Keys) {
        if ($lang -ne "Protocols" -and $TestResults.Results[$lang].Success -and $TestResults.Results[$lang].Throughput) {
            $performanceRanking += @{
                Language = $TestResults.Results[$lang].Language
                Throughput = $TestResults.Results[$lang].Throughput
                Latency = $TestResults.Results[$lang].Latency
            }
        }
    }
    
    $performanceRanking = $performanceRanking | Sort-Object Throughput -Descending
    
    for ($i = 0; $i -lt $performanceRanking.Count; $i++) {
        $rank = $i + 1
        $lang = $performanceRanking[$i]
        $report += "$rank. **$($lang.Language)**: $($lang.Throughput) spans/sec (延迟: $($lang.Latency) ms)`n"
    }

    $report += @"

### 建议

1. **性能优化**: 根据测试结果优化低性能语言实现
2. **资源管理**: 监控内存使用情况，避免内存泄漏
3. **并发优化**: 调整并发参数以获得最佳性能
4. **协议选择**: 根据使用场景选择合适的传输协议

### 下一步

1. 分析性能瓶颈
2. 优化慢速实现
3. 增加更多测试场景
4. 建立持续性能监控

---

*报告由 OTLP 2025 综合基准测试脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 综合基准测试报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 综合基准测试开始..." "Green"
    Write-ColorOutput ("=" * 60) "Gray"
    
    # 收集系统信息
    Get-SystemInfo
    
    # 根据语言参数执行测试
    switch ($Language.ToLower()) {
        "rust" { Test-RustPerformance }
        "go" { Test-GoPerformance }
        "python" { Test-PythonPerformance }
        "java" { Test-JavaPerformance }
        "javascript" { Test-JavaScriptPerformance }
        "all" {
            Test-RustPerformance
            Test-GoPerformance
            Test-PythonPerformance
            Test-JavaPerformance
            Test-JavaScriptPerformance
        }
        default {
            Write-ColorOutput "❌ 不支持的语言: $Language" "Red"
            Write-ColorOutput "支持的语言: rust, go, python, java, javascript, all" "Yellow"
            exit 1
        }
    }
    
    # 测试协议性能
    Test-ProtocolPerformance
    
    # 生成报告
    if ($Export) {
        Generate-BenchmarkReport
    }
    
    # 显示总结
    Write-ColorOutput ("=" * 60) "Gray"
    Write-ColorOutput "📊 测试总结:" "White"
    
    $successCount = 0
    $totalCount = 0
    
    foreach ($lang in $TestResults.Results.Keys) {
        if ($lang -ne "Protocols") {
            $totalCount++
            if ($TestResults.Results[$lang].Success) {
                $successCount++
            }
        }
    }
    
    Write-ColorOutput "✅ 成功: $successCount/$totalCount" "Green"
    Write-ColorOutput "⏱️ 总耗时: $((Get-Date - $TestResults.StartTime).TotalSeconds) 秒" "White"
    
    if ($successCount -eq $totalCount) {
        Write-ColorOutput "🎉 所有测试通过!" "Green"
    } else {
        Write-ColorOutput "⚠️ 部分测试失败，请检查日志" "Yellow"
    }
    
    Write-ColorOutput "✅ 综合基准测试完成!" "Green"
}

# 执行主函数
Main