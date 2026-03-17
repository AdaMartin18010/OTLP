# OTLP文档迁移脚本 - 填充05_应用实践层和06_工具生态层
# 迁移策略：复制而非移动，保留原文档作为参考

$ErrorActionPreference = "Stop"
$docsRoot = "E:\_src\OTLP\docs"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  OTLP文档迁移工具" -ForegroundColor Cyan
Write-Host "  填充05_应用实践层和06_工具生态层" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan

# 定义迁移映射
$migrations = @(
    # ===== 05_应用实践层 =====
    # 01_行业案例
    @{ From = "00_参考资料/academic/OTLP_Case_Studies_Detailed.md"; To = "05_应用实践层/01_行业案例/01_OTLP形式化验证框架案例研究.md" },
    @{ From = "04_部署运维层/31_性能优化/03_实际案例性能数据分析报告.md"; To = "05_应用实践层/01_行业案例/02_实际案例性能数据分析报告.md" },
    
    # 11_GenAI可观测性
    @{ From = "00_参考资料/指南_AI_AI驱动日志分析完整指南_LLM异常检测与RCA.md"; To = "05_应用实践层/11_GenAI可观测性/01_AI驱动日志分析完整指南_LLM异常检测与RCA.md" },
    @{ From = "00_参考资料/指南_AI_OTLP自主运维能力完整架构_AIOps平台设计.md"; To = "05_应用实践层/11_GenAI可观测性/02_OTLP自主运维能力完整架构_AIOps平台设计.md" },
    @{ From = "00_参考资料/指南_AI_时序异常检测实战指南_Prophet_LSTM_IsolationForest.md"; To = "05_应用实践层/11_GenAI可观测性/03_时序异常检测实战指南_Prophet_LSTM_IsolationForest.md" },
    @{ From = "07_项目管理层/11_趋势追踪/AI_ML_可观测性追踪.md"; To = "05_应用实践层/11_GenAI可观测性/04_AI_ML可观测性趋势追踪.md" },
    
    # 21_微服务实践
    @{ From = "00_参考资料/指南_服务网格_服务网格可观测性完整指南_Istio_Linkerd深度集成.md"; To = "05_应用实践层/21_微服务实践/01_服务网格可观测性完整指南_Istio_Linkerd深度集成.md" },
    @{ From = "00_参考资料/指南_工作流_工作流自动化完整指南_Temporal_io与可观测性集成.md"; To = "05_应用实践层/21_微服务实践/02_工作流自动化完整指南_Temporal_io与可观测性集成.md" },
    
    # 31_Serverless实践
    @{ From = "02_核心协议层/21_语义约定/01_AWS_Lambda.md"; To = "05_应用实践层/31_Serverless实践/01_AWS_Lambda语义约定与OTLP集成.md" },
    @{ From = "02_核心协议层/21_语义约定/02_Azure_Functions.md"; To = "05_应用实践层/31_Serverless实践/02_Azure_Functions语义约定与OTLP集成.md" },
    @{ From = "02_核心协议层/21_语义约定/03_Google_Cloud_Functions.md"; To = "05_应用实践层/31_Serverless实践/03_Google_Cloud_Functions语义约定与OTLP集成.md" },
    
    # 41_边缘计算
    @{ From = "00_参考资料/指南_eBPF_eBPF可观测性深度技术指南_零侵入式追踪.md"; To = "05_应用实践层/41_边缘计算/01_eBPF可观测性深度技术指南_零侵入式追踪.md" },
    @{ From = "02_核心协议层/21_语义约定/07_MQTT.md"; To = "05_应用实践层/41_边缘计算/02_MQTT物联网协议语义约定.md" },
    @{ From = "07_项目管理层/11_趋势追踪/Wasm_插件生态追踪.md"; To = "05_应用实践层/41_边缘计算/03_Wasm插件生态追踪.md" },
    @{ From = "03_核心实现层/32_移动端可观测性/01_iOS平台OTLP完整接入指南.md"; To = "05_应用实践层/41_边缘计算/11_iOS平台OTLP完整接入指南.md" },
    @{ From = "03_核心实现层/32_移动端可观测性/02_Android平台OTLP接入指南.md"; To = "05_应用实践层/41_边缘计算/12_Android平台OTLP接入指南.md" },
    @{ From = "03_核心实现层/32_移动端可观测性/03_React_Native跨平台OTLP方案.md"; To = "05_应用实践层/41_边缘计算/13_React_Native跨平台OTLP方案.md" },
    @{ From = "03_核心实现层/32_移动端可观测性/04_WebAssembly_OTLP观测技术.md"; To = "05_应用实践层/41_边缘计算/14_WebAssembly_OTLP观测技术.md" },
    
    # ===== 06_工具生态层 =====
    # 01_SDK指南
    @{ From = "00_参考资料/指南_SDK_OTLP_SDK最佳实践指南_多语言全栈实现.md"; To = "06_工具生态层/01_SDK指南/01_OTLP_SDK最佳实践指南_多语言全栈实现.md" },
    @{ From = "00_参考资料/44_矩阵_语言SDK对比矩阵.md"; To = "06_工具生态层/01_SDK指南/02_语言SDK对比矩阵.md" },
    @{ From = "03_核心实现层/01_SDK实现/03_SDK最佳实践.md"; To = "06_工具生态层/01_SDK指南/03_SDK最佳实践.md" },
    @{ From = "03_核心实现层/01_SDK实现/01_SDK概述.md"; To = "06_工具生态层/01_SDK指南/04_SDK概述.md" },
    
    # 11_工具集成
    @{ From = "02_核心协议层/21_语义约定/Zipkin_Exporter弃用说明与迁移指南.md"; To = "06_工具生态层/11_工具集成/01_Zipkin_Exporter弃用说明与迁移指南.md" },
    @{ From = "02_核心协议层/12_Metrics数据模型/03_Pre-aggregation与Prometheus_StatsD映射.md"; To = "06_工具生态层/11_工具集成/02_Prometheus_StatsD映射指南.md" },
    @{ From = "02_核心协议层/21_语义约定/04_Elasticsearch.md"; To = "06_工具生态层/11_工具集成/03_Elasticsearch语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/01_Kafka.md"; To = "06_工具生态层/11_工具集成/04_Kafka语义约定与集成.md" },
    @{ From = "02_核心协议层/21_语义约定/02_NATS.md"; To = "06_工具生态层/11_工具集成/05_NATS语义约定与集成.md" },
    @{ From = "02_核心协议层/21_语义约定/04_RabbitMQ.md"; To = "06_工具生态层/11_工具集成/06_RabbitMQ语义约定与集成.md" },
    @{ From = "02_核心协议层/21_语义约定/05_Apache_Pulsar.md"; To = "06_工具生态层/11_工具集成/07_Apache_Pulsar语义约定与集成.md" },
    @{ From = "02_核心协议层/21_语义约定/06_AWS_SQS_SNS.md"; To = "06_工具生态层/11_工具集成/08_AWS_SQS_SNS语义约定与集成.md" },
    @{ From = "02_核心协议层/21_语义约定/01_SQL数据库属性详解.md"; To = "06_工具生态层/11_工具集成/09_SQL数据库语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/02_MongoDB.md"; To = "06_工具生态层/11_工具集成/10_MongoDB语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/03_Redis.md"; To = "06_工具生态层/11_工具集成/11_Redis语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/03_Cassandra.md"; To = "06_工具生态层/11_工具集成/12_Cassandra语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/01_HTTP.md"; To = "06_工具生态层/11_工具集成/13_HTTP语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/02_gRPC.md"; To = "06_工具生态层/11_工具集成/14_gRPC语义约定.md" },
    @{ From = "02_核心协议层/21_语义约定/04_RPC.md"; To = "06_工具生态层/11_工具集成/15_RPC语义约定.md" },
    
    # 21_可视化工具
    @{ From = "04_部署运维层/31_性能优化/01_架构图表与可视化指南_Mermaid完整版.md"; To = "06_工具生态层/21_可视化工具/01_架构图表与可视化指南_Mermaid完整版.md" },
    
    # 31_社区资源
    @{ From = "00_参考资料/41_矩阵_后端方案对比矩阵.md"; To = "06_工具生态层/31_社区资源/01_后端方案对比矩阵.md" },
    @{ From = "00_参考资料/42_矩阵_竞争力分析矩阵.md"; To = "06_工具生态层/31_社区资源/02_竞争力分析矩阵.md" },
    @{ From = "00_参考资料/51_工具_Collector组件矩阵.md"; To = "06_工具生态层/31_社区资源/03_Collector组件矩阵.md" }
)

# 统计
$success = 0
$failed = 0
$skipped = 0

foreach ($migration in $migrations) {
    $sourcePath = Join-Path $docsRoot $migration.From
    $targetPath = Join-Path $docsRoot $migration.To
    
    # 检查源文件是否存在
    if (-not (Test-Path $sourcePath)) {
        Write-Host "⚠ 源文件不存在: $($migration.From)" -ForegroundColor Yellow
        $skipped++
        continue
    }
    
    # 创建目标目录
    $targetDir = Split-Path $targetPath -Parent
    if (-not (Test-Path $targetDir)) {
        New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
    }
    
    # 复制文件
    try {
        Copy-Item -Path $sourcePath -Destination $targetPath -Force
        Write-Host "✓ 复制: $($migration.From) → $($migration.To)" -ForegroundColor Green
        $success++
    } catch {
        Write-Host "✗ 失败: $($migration.From) - $_" -ForegroundColor Red
        $failed++
    }
}

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  迁移完成统计" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "成功: $success" -ForegroundColor Green
Write-Host "失败: $failed" -ForegroundColor Red
Write-Host "跳过: $skipped" -ForegroundColor Yellow
Write-Host "========================================" -ForegroundColor Cyan
