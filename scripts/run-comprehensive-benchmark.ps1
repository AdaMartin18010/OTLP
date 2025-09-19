# OpenTelemetry 综合基准测试脚本
# 执行完整的性能基准测试并生成详细报告

param(
    [string]$OutputDir = "benchmark-results",
    [int]$Duration = 300,  # 测试持续时间（秒）
    [int]$Concurrency = 10,  # 并发数
    [string]$Protocol = "both",  # grpc, http, both
    [switch]$IncludeJava,
    [switch]$IncludeJavaScript,
    [switch]$Verbose,
    [switch]$GenerateReport
)

# 创建输出目录
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
}

$Timestamp = Get-Date -Format "yyyy-MM-dd-HHmmss"
$LogFile = Join-Path $OutputDir "benchmark-$Timestamp.log"

# 日志函数
function Write-Log {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $LogMessage = "[$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')] [$Level] $Message"
    
    if ($Verbose -or $Level -eq "ERROR" -or $Level -eq "WARN") {
        Write-Host $LogMessage
    }
    
    Add-Content -Path $LogFile -Value $LogMessage
}

# 检查环境
function Test-Environment {
    Write-Log "检查测试环境..."
    
    $RequiredTools = @("docker", "docker-compose")
    $MissingTools = @()
    
    foreach ($Tool in $RequiredTools) {
        if (!(Get-Command $Tool -ErrorAction SilentlyContinue)) {
            $MissingTools += $Tool
        }
    }
    
    if ($MissingTools.Count -gt 0) {
        Write-Log "缺少必需工具: $($MissingTools -join ', ')" "ERROR"
        return $false
    }
    
    # 检查端口是否可用
    $RequiredPorts = @(4317, 4318, 16686, 9090)
    $UsedPorts = @()
    
    foreach ($Port in $RequiredPorts) {
        $Connection = Test-NetConnection -ComputerName localhost -Port $Port -InformationLevel Quiet -WarningAction SilentlyContinue
        if ($Connection) {
            $UsedPorts += $Port
        }
    }
    
    if ($UsedPorts.Count -gt 0) {
        Write-Log "端口被占用: $($UsedPorts -join ', ')" "WARN"
        Write-Log "请确保这些端口可用或停止相关服务" "WARN"
    }
    
    Write-Log "环境检查完成"
    return $true
}

# 启动测试环境
function Start-TestEnvironment {
    Write-Log "启动测试环境..."
    
    try {
        # 启动Collector和存储后端
        docker-compose -f implementations/collector/compose/docker-compose.yaml up -d
        
        # 等待服务启动
        Write-Log "等待服务启动..."
        Start-Sleep -Seconds 30
        
        # 检查服务健康状态
        $Services = @(
            @{Name="Collector"; Url="http://localhost:13133"},
            @{Name="Jaeger"; Url="http://localhost:16686"},
            @{Name="Prometheus"; Url="http://localhost:9090"}
        )
        
        foreach ($Service in $Services) {
            try {
                $Response = Invoke-WebRequest -Uri $Service.Url -TimeoutSec 10 -UseBasicParsing
                if ($Response.StatusCode -eq 200) {
                    Write-Log "$($Service.Name) 服务启动成功"
                } else {
                    Write-Log "$($Service.Name) 服务状态异常: $($Response.StatusCode)" "WARN"
                }
            }
            catch {
                Write-Log "$($Service.Name) 服务启动失败: $($_.Exception.Message)" "ERROR"
            }
        }
        
        Write-Log "测试环境启动完成"
        return $true
    }
    catch {
        Write-Log "启动测试环境失败: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

# 停止测试环境
function Stop-TestEnvironment {
    Write-Log "停止测试环境..."
    
    try {
        docker-compose -f implementations/collector/compose/docker-compose.yaml down
        Write-Log "测试环境已停止"
    }
    catch {
        Write-Log "停止测试环境失败: $($_.Exception.Message)" "ERROR"
    }
}

# 运行Rust基准测试
function Invoke-RustBenchmark {
    param(
        [string]$Protocol,
        [int]$Duration,
        [int]$Concurrency
    )
    
    Write-Log "运行Rust基准测试 (协议: $Protocol, 持续时间: ${Duration}s, 并发: $Concurrency)..."
    
    $RustResults = @{
        Language = "Rust"
        Protocol = $Protocol
        Duration = $Duration
        Concurrency = $Concurrency
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    try {
        $RustScript = "benchmarks/run-rust.ps1"
        if (Test-Path $RustScript) {
            $Arguments = @("-Duration", $Duration, "-Concurrency", $Concurrency)
            
            if ($Protocol -eq "grpc" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "grpc")
                $GrpcResult = & $RustScript @Arguments
                $RustResults.GrpcResult = $GrpcResult
            }
            
            if ($Protocol -eq "http" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "http")
                $HttpResult = & $RustScript @Arguments
                $RustResults.HttpResult = $HttpResult
            }
            
            Write-Log "Rust基准测试完成"
        } else {
            Write-Log "Rust基准测试脚本不存在" "WARN"
        }
    }
    catch {
        Write-Log "Rust基准测试失败: $($_.Exception.Message)" "ERROR"
        $RustResults.Error = $_.Exception.Message
    }
    
    return $RustResults
}

# 运行Go基准测试
function Invoke-GoBenchmark {
    param(
        [string]$Protocol,
        [int]$Duration,
        [int]$Concurrency
    )
    
    Write-Log "运行Go基准测试 (协议: $Protocol, 持续时间: ${Duration}s, 并发: $Concurrency)..."
    
    $GoResults = @{
        Language = "Go"
        Protocol = $Protocol
        Duration = $Duration
        Concurrency = $Concurrency
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    try {
        $GoScript = "benchmarks/run-go.ps1"
        if (Test-Path $GoScript) {
            $Arguments = @("-Duration", $Duration, "-Concurrency", $Concurrency)
            
            if ($Protocol -eq "grpc" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "grpc")
                $GrpcResult = & $GoScript @Arguments
                $GoResults.GrpcResult = $GrpcResult
            }
            
            if ($Protocol -eq "http" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "http")
                $HttpResult = & $GoScript @Arguments
                $GoResults.HttpResult = $HttpResult
            }
            
            Write-Log "Go基准测试完成"
        } else {
            Write-Log "Go基准测试脚本不存在" "WARN"
        }
    }
    catch {
        Write-Log "Go基准测试失败: $($_.Exception.Message)" "ERROR"
        $GoResults.Error = $_.Exception.Message
    }
    
    return $GoResults
}

# 运行Python基准测试
function Invoke-PythonBenchmark {
    param(
        [string]$Protocol,
        [int]$Duration,
        [int]$Concurrency
    )
    
    Write-Log "运行Python基准测试 (协议: $Protocol, 持续时间: ${Duration}s, 并发: $Concurrency)..."
    
    $PythonResults = @{
        Language = "Python"
        Protocol = $Protocol
        Duration = $Duration
        Concurrency = $Concurrency
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    try {
        $PythonScript = "benchmarks/run-python.ps1"
        if (Test-Path $PythonScript) {
            $Arguments = @("-Duration", $Duration, "-Concurrency", $Concurrency)
            
            if ($Protocol -eq "grpc" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "grpc")
                $GrpcResult = & $PythonScript @Arguments
                $PythonResults.GrpcResult = $GrpcResult
            }
            
            if ($Protocol -eq "http" -or $Protocol -eq "both") {
                $Arguments += @("-Protocol", "http")
                $HttpResult = & $PythonScript @Arguments
                $PythonResults.HttpResult = $HttpResult
            }
            
            Write-Log "Python基准测试完成"
        } else {
            Write-Log "Python基准测试脚本不存在" "WARN"
        }
    }
    catch {
        Write-Log "Python基准测试失败: $($_.Exception.Message)" "ERROR"
        $PythonResults.Error = $_.Exception.Message
    }
    
    return $PythonResults
}

# 运行Java基准测试
function Invoke-JavaBenchmark {
    param(
        [string]$Protocol,
        [int]$Duration,
        [int]$Concurrency
    )
    
    Write-Log "运行Java基准测试 (协议: $Protocol, 持续时间: ${Duration}s, 并发: $Concurrency)..."
    
    $JavaResults = @{
        Language = "Java"
        Protocol = $Protocol
        Duration = $Duration
        Concurrency = $Concurrency
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    try {
        $JavaExample = "examples/minimal-java"
        if (Test-Path $JavaExample) {
            Push-Location $JavaExample
            
            # 编译Java项目
            mvn clean compile -q
            if ($LASTEXITCODE -eq 0) {
                # 运行基准测试
                $Arguments = @("-Dexec.args", "-Duration $Duration -Concurrency $Concurrency -Protocol $Protocol")
                mvn exec:java @Arguments
                
                Write-Log "Java基准测试完成"
            } else {
                Write-Log "Java项目编译失败" "ERROR"
                $JavaResults.Error = "编译失败"
            }
            
            Pop-Location
        } else {
            Write-Log "Java示例不存在" "WARN"
        }
    }
    catch {
        Write-Log "Java基准测试失败: $($_.Exception.Message)" "ERROR"
        $JavaResults.Error = $_.Exception.Message
    }
    
    return $JavaResults
}

# 运行JavaScript基准测试
function Invoke-JavaScriptBenchmark {
    param(
        [string]$Protocol,
        [int]$Duration,
        [int]$Concurrency
    )
    
    Write-Log "运行JavaScript基准测试 (协议: $Protocol, 持续时间: ${Duration}s, 并发: $Concurrency)..."
    
    $JavaScriptResults = @{
        Language = "JavaScript"
        Protocol = $Protocol
        Duration = $Duration
        Concurrency = $Concurrency
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    try {
        $JavaScriptExample = "examples/minimal-javascript"
        if (Test-Path $JavaScriptExample) {
            Push-Location $JavaScriptExample
            
            # 安装依赖
            npm install --silent
            if ($LASTEXITCODE -eq 0) {
                # 运行基准测试
                $Env:OTEL_EXPORTER_OTLP_ENDPOINT = "http://localhost:4318"
                $Env:OTEL_EXPORTER_OTLP_PROTOCOL = $Protocol
                $Env:BENCHMARK_DURATION = $Duration
                $Env:BENCHMARK_CONCURRENCY = $Concurrency
                
                npm run benchmark
                
                Write-Log "JavaScript基准测试完成"
            } else {
                Write-Log "JavaScript依赖安装失败" "ERROR"
                $JavaScriptResults.Error = "依赖安装失败"
            }
            
            Pop-Location
        } else {
            Write-Log "JavaScript示例不存在" "WARN"
        }
    }
    catch {
        Write-Log "JavaScript基准测试失败: $($_.Exception.Message)" "ERROR"
        $JavaScriptResults.Error = $_.Exception.Message
    }
    
    return $JavaScriptResults
}

# 收集系统指标
function Get-SystemMetrics {
    Write-Log "收集系统指标..."
    
    $SystemMetrics = @{
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        CPU = @{
            Usage = (Get-Counter -Counter "\Processor(_Total)\% Processor Time" -SampleInterval 1 -MaxSamples 1).CounterSamples[0].CookedValue
            Cores = (Get-WmiObject -Class Win32_Processor).NumberOfCores
        }
        Memory = @{
            Total = [math]::Round((Get-WmiObject -Class Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
            Available = [math]::Round((Get-WmiObject -Class Win32_OperatingSystem).FreePhysicalMemory / 1MB, 2)
            Usage = [math]::Round((1 - (Get-WmiObject -Class Win32_OperatingSystem).FreePhysicalMemory / (Get-WmiObject -Class Win32_ComputerSystem).TotalPhysicalMemory) * 100, 2)
        }
        Network = @{
            Interfaces = Get-NetAdapter | Where-Object {$_.Status -eq "Up"} | Select-Object Name, InterfaceDescription
        }
        Disk = @{
            Drives = Get-WmiObject -Class Win32_LogicalDisk | Select-Object DeviceID, @{Name="Size(GB)";Expression={[math]::Round($_.Size/1GB,2)}}, @{Name="FreeSpace(GB)";Expression={[math]::Round($_.FreeSpace/1GB,2)}}
        }
    }
    
    return $SystemMetrics
}

# 生成基准测试报告
function New-BenchmarkReport {
    param(
        [array]$Results,
        [hashtable]$SystemMetrics
    )
    
    Write-Log "生成基准测试报告..."
    
    $ReportPath = Join-Path $OutputDir "benchmark-report-$Timestamp.md"
    
    $Report = @"
# OpenTelemetry 综合基准测试报告

**测试时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**测试持续时间**: $Duration 秒
**并发数**: $Concurrency
**测试协议**: $Protocol

## 测试环境

### 系统信息
- **操作系统**: $($env:OS)
- **处理器**: $((Get-WmiObject -Class Win32_Processor).Name)
- **CPU核心数**: $($SystemMetrics.CPU.Cores)
- **CPU使用率**: $($SystemMetrics.CPU.Usage)%
- **总内存**: $($SystemMetrics.Memory.Total) GB
- **可用内存**: $($SystemMetrics.Memory.Available) GB
- **内存使用率**: $($SystemMetrics.Memory.Usage)%

### 网络接口
"@

    foreach ($Interface in $SystemMetrics.Network.Interfaces) {
        $Report += "`n- **$($Interface.Name)**: $($Interface.InterfaceDescription)"
    }

    $Report += @"

### 磁盘信息
"@

    foreach ($Drive in $SystemMetrics.Disk.Drives) {
        $Report += "`n- **$($Drive.DeviceID)**: $($Drive.'Size(GB)') GB (可用: $($Drive.'FreeSpace(GB)') GB)"
    }

    $Report += @"

## 测试结果

### 性能对比

| 语言 | 协议 | 吞吐量 (spans/s) | 延迟 (ms) | 内存使用 (MB) | CPU使用 (%) |
|------|------|------------------|-----------|---------------|-------------|
"@

    foreach ($Result in $Results) {
        if ($Result.GrpcResult) {
            $Report += "`n| $($Result.Language) | gRPC | $($Result.GrpcResult.Throughput) | $($Result.GrpcResult.Latency) | $($Result.GrpcResult.MemoryUsage) | $($Result.GrpcResult.CpuUsage) |"
        }
        if ($Result.HttpResult) {
            $Report += "`n| $($Result.Language) | HTTP | $($Result.HttpResult.Throughput) | $($Result.HttpResult.Latency) | $($Result.HttpResult.MemoryUsage) | $($Result.HttpResult.CpuUsage) |"
        }
    }

    $Report += @"

### 详细结果

"@

    foreach ($Result in $Results) {
        $Report += @"

#### $($Result.Language)

**测试时间**: $($Result.Timestamp)
**并发数**: $($Result.Concurrency)
**持续时间**: $($Result.Duration) 秒

"@

        if ($Result.GrpcResult) {
            $Report += @"
**gRPC协议结果**:
- 吞吐量: $($Result.GrpcResult.Throughput) spans/s
- 平均延迟: $($Result.GrpcResult.Latency) ms
- P95延迟: $($Result.GrpcResult.P95Latency) ms
- P99延迟: $($Result.GrpcResult.P99Latency) ms
- 内存使用: $($Result.GrpcResult.MemoryUsage) MB
- CPU使用: $($Result.GrpcResult.CpuUsage) %
- 错误率: $($Result.GrpcResult.ErrorRate) %

"@
        }

        if ($Result.HttpResult) {
            $Report += @"
**HTTP协议结果**:
- 吞吐量: $($Result.HttpResult.Throughput) spans/s
- 平均延迟: $($Result.HttpResult.Latency) ms
- P95延迟: $($Result.HttpResult.P95Latency) ms
- P99延迟: $($Result.HttpResult.P99Latency) ms
- 内存使用: $($Result.HttpResult.MemoryUsage) MB
- CPU使用: $($Result.HttpResult.CpuUsage) %
- 错误率: $($Result.HttpResult.ErrorRate) %

"@
        }

        if ($Result.Error) {
            $Report += "`n**错误**: $($Result.Error)`n"
        }
    }

    $Report += @"

## 性能分析

### 最佳性能语言
"@

    # 分析最佳性能
    $BestPerformance = $Results | Sort-Object {[int]$_.GrpcResult.Throughput} -Descending | Select-Object -First 1
    if ($BestPerformance) {
        $Report += "`n- **最高吞吐量**: $($BestPerformance.Language) ($($BestPerformance.GrpcResult.Throughput) spans/s)"
    }

    $Report += @"

### 协议对比
"@

    $GrpcResults = $Results | Where-Object {$_.GrpcResult}
    $HttpResults = $Results | Where-Object {$_.HttpResult}

    if ($GrpcResults -and $HttpResults) {
        $AvgGrpcThroughput = ($GrpcResults | Measure-Object -Property {$_.GrpcResult.Throughput} -Average).Average
        $AvgHttpThroughput = ($HttpResults | Measure-Object -Property {$_.HttpResult.Throughput} -Average).Average
        
        $Report += "`n- **gRPC平均吞吐量**: $([math]::Round($AvgGrpcThroughput, 2)) spans/s"
        $Report += "`n- **HTTP平均吞吐量**: $([math]::Round($AvgHttpThroughput, 2)) spans/s"
        $Report += "`n- **性能提升**: $([math]::Round(($AvgGrpcThroughput - $AvgHttpThroughput) / $AvgHttpThroughput * 100, 2))%"
    }

    $Report += @"

## 建议

### 性能优化建议
1. **高吞吐场景**: 推荐使用 gRPC 协议
2. **防火墙穿透**: 推荐使用 HTTP 协议
3. **内存优化**: 调整批处理大小和采样率
4. **CPU优化**: 使用多核处理和异步操作

### 部署建议
1. **生产环境**: 使用 gRPC 协议，配置适当的批处理参数
2. **开发环境**: 使用 HTTP 协议，便于调试和监控
3. **监控**: 设置适当的告警阈值和监控指标

## 测试配置

### 测试参数
- 测试持续时间: $Duration 秒
- 并发数: $Concurrency
- 测试协议: $Protocol
- 包含语言: $($Results.Language -join ', ')

### 环境配置
- Collector配置: implementations/collector/minimal.yaml
- 存储后端: Jaeger, Prometheus
- 监控: Grafana仪表盘

---
*报告生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')*
*测试执行者: 自动化基准测试脚本*
"@

    Set-Content -Path $ReportPath -Value $Report
    Write-Log "基准测试报告已生成: $ReportPath"
    
    return $ReportPath
}

# 主函数
function Main {
    Write-Log "开始OpenTelemetry综合基准测试..." "INFO"
    Write-Log "测试参数: 持续时间=$Duration秒, 并发=$Concurrency, 协议=$Protocol" "INFO"
    
    # 检查环境
    if (!(Test-Environment)) {
        Write-Log "环境检查失败，退出测试" "ERROR"
        exit 1
    }
    
    # 启动测试环境
    if (!(Start-TestEnvironment)) {
        Write-Log "测试环境启动失败，退出测试" "ERROR"
        exit 1
    }
    
    try {
        # 收集系统指标
        $SystemMetrics = Get-SystemMetrics
        
        # 运行基准测试
        $Results = @()
        
        # Rust测试
        $RustResults = Invoke-RustBenchmark -Protocol $Protocol -Duration $Duration -Concurrency $Concurrency
        $Results += $RustResults
        
        # Go测试
        $GoResults = Invoke-GoBenchmark -Protocol $Protocol -Duration $Duration -Concurrency $Concurrency
        $Results += $GoResults
        
        # Python测试
        $PythonResults = Invoke-PythonBenchmark -Protocol $Protocol -Duration $Duration -Concurrency $Concurrency
        $Results += $PythonResults
        
        # Java测试（如果启用）
        if ($IncludeJava) {
            $JavaResults = Invoke-JavaBenchmark -Protocol $Protocol -Duration $Duration -Concurrency $Concurrency
            $Results += $JavaResults
        }
        
        # JavaScript测试（如果启用）
        if ($IncludeJavaScript) {
            $JavaScriptResults = Invoke-JavaScriptBenchmark -Protocol $Protocol -Duration $Duration -Concurrency $Concurrency
            $Results += $JavaScriptResults
        }
        
        # 生成报告
        if ($GenerateReport) {
            $ReportPath = New-BenchmarkReport -Results $Results -SystemMetrics $SystemMetrics
            Write-Log "基准测试报告: $ReportPath" "INFO"
        }
        
        Write-Log "综合基准测试完成" "INFO"
        
    }
    finally {
        # 停止测试环境
        Stop-TestEnvironment
    }
}

# 执行主函数
if ($MyInvocation.InvocationName -ne '.') {
    Main
}
