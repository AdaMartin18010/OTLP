# 批量重命名文件 - 规范化命名
# 将不规范的文件名改为 NN_类别_主题.md 格式

$ErrorActionPreference = "Stop"
$docsRoot = "E:\_src\OTLP\docs"

# 定义重命名映射
$renameMappings = @(
    # 01_基础理论层/01_语义模型 - 英文文件
    @{ From = "01_基础理论层/01_语义模型/CONTROL_FLOW_EXECUTION_DATA_FLOW_ANALYSIS.md"; To = "01_基础理论层/01_语义模型/01_控制流_执行流数据流分析.md" },
    @{ From = "01_基础理论层/01_语义模型/DISTRIBUTED_SYSTEMS_THEORY.md"; To = "01_基础理论层/01_语义模型/02_分布式_分布式系统理论.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_THEORETICAL_FRAMEWORK_INDEX.md"; To = "01_基础理论层/01_语义模型/00_索引_OTLP理论框架总导航.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_UNIFIED_THEORETICAL_FRAMEWORK.md"; To = "01_基础理论层/01_语义模型/01_理论_OTLP统一理论框架第一部分.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART2.md"; To = "01_基础理论层/01_语义模型/02_理论_OTLP统一理论框架第二部分.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART3.md"; To = "01_基础理论层/01_语义模型/03_理论_OTLP统一理论框架第三部分.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART4.md"; To = "01_基础理论层/01_语义模型/04_理论_OTLP统一理论框架第四部分.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART5.md"; To = "01_基础理论层/01_语义模型/05_理论_OTLP统一理论框架第五部分.md" },
    @{ From = "01_基础理论层/01_语义模型/QUICK_REFERENCE.md"; To = "01_基础理论层/01_语义模型/90_速查_语义模型快速参考.md" },
    @{ From = "01_基础理论层/01_语义模型/SELF_AWARENESS_SELF_OPS_FRAMEWORK.md"; To = "01_基础理论层/01_语义模型/06_运维_自我感知与自主运维框架.md" },
    @{ From = "01_基础理论层/01_语义模型/SELF_HEALING_AUTO_ADJUSTMENT_ARCHITECTURE.md"; To = "01_基础理论层/01_语义模型/07_自愈_自愈合自动调整架构.md" },
    @{ From = "01_基础理论层/01_语义模型/SEMANTIC_MODELS_ANALYSIS_SUMMARY.md"; To = "01_基础理论层/01_语义模型/08_总结_语义模型分析总结.md" },
    @{ From = "01_基础理论层/01_语义模型/SEMANTIC_MODELS_AND_FLOW_ANALYSIS.md"; To = "01_基础理论层/01_语义模型/09_流分析_语义模型与流分析.md" },
    
    # 01_基础理论层/01_语义模型 - 中文缺编号
    @{ From = "01_基础理论层/01_语义模型/OTLP数据模型语义完整性形式化论证.md"; To = "01_基础理论层/01_语义模型/10_论证_OTLP数据模型语义完整性形式化论证.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP与竞品语义模型深度对比.md"; To = "01_基础理论层/01_语义模型/11_对比_OTLP与竞品语义模型深度对比.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP语义模型本体论基础.md"; To = "01_基础理论层/01_语义模型/12_本体论_OTLP语义模型本体论基础.md" },
    @{ From = "01_基础理论层/01_语义模型/OTLP语义演化与版本兼容性理论.md"; To = "01_基础理论层/01_语义模型/13_演化_OTLP语义演化与版本兼容性理论.md" },
    
    # 02_核心协议层 - 版本和变更日志
    @{ From = "02_核心协议层/01_协议基础/OTLP_v1.9.0更新说明.md"; To = "02_核心协议层/01_协议基础/91_版本_OTLP_v1.9.0更新说明.md" },
    @{ From = "02_核心协议层/21_语义约定/Semantic_Conventions_v1.40.0_完整变更日志.md"; To = "02_核心协议层/21_语义约定/91_变更日志_Semantic_Conventions_v1.40.0完整变更日志.md" },
    @{ From = "02_核心协议层/21_语义约定/版本更新日志_v1.29_to_v1.38.md"; To = "02_核心协议层/21_语义约定/92_变更日志_版本更新日志_v1.29_to_v1.38.md" },
    @{ From = "02_核心协议层/21_语义约定/版本更新日志_v1.38_to_v1.39.md"; To = "02_核心协议层/21_语义约定/93_变更日志_版本更新日志_v1.38_to_v1.39.md" },
    @{ From = "02_核心协议层/21_语义约定/版本更新日志_v1.39_to_v1.40.md"; To = "02_核心协议层/21_语义约定/94_变更日志_版本更新日志_v1.39_to_v1.40.md" },
    @{ From = "02_核心协议层/21_语义约定/Zipkin_Exporter弃用说明与迁移指南.md"; To = "02_核心协议层/21_语义约定/81_迁移_Zipkin_Exporter弃用说明与迁移指南.md" },
    
    # 03_核心实现层
    @{ From = "03_核心实现层/01_SDK实现/Collector_v0.147.0_完整变更日志.md"; To = "03_核心实现层/01_SDK实现/91_变更日志_Collector_v0.147.0完整变更日志.md" },
    @{ From = "03_核心实现层/01_SDK实现/OTLP_Collector_v0.147.0更新说明.md"; To = "03_核心实现层/01_SDK实现/92_版本_Collector_v0.147.0更新说明.md" },
    @{ From = "03_核心实现层/01_SDK实现/声明式配置完整指南_v1.0.md"; To = "03_核心实现层/01_SDK实现/81_指南_声明式配置完整指南.md" },
    @{ From = "03_核心实现层/31_eBPF自动插桩/OBI_2026年目标更新.md"; To = "03_核心实现层/31_eBPF自动插桩/91_规划_OBI_2026年目标更新.md" },
    
    # 04_部署运维层
    @{ From = "04_部署运维层/01_部署指南/成本优化与FinOps实践指南.md"; To = "04_部署运维层/01_部署指南/11_FinOps_成本优化与FinOps实践指南.md" },
    @{ From = "04_部署运维层/01_部署指南/大规模Collector生产部署架构指南.md"; To = "04_部署运维层/01_部署指南/01_部署_大规模Collector生产部署架构指南.md" },
    @{ From = "04_部署运维层/41_安全合规/安全加固完整清单_v1.0.md"; To = "04_部署运维层/41_安全合规/01_安全_安全加固完整清单.md" },
    
    # 07_项目管理层
    @{ From = "07_项目管理层/11_趋势追踪/2025_Q4_趋势分析.md"; To = "07_项目管理层/11_趋势追踪/01_趋势_2025_Q4趋势分析.md" },
    @{ From = "07_项目管理层/11_趋势追踪/AI_ML_可观测性追踪.md"; To = "07_项目管理层/11_趋势追踪/02_AI_ML_可观测性趋势追踪.md" },
    @{ From = "07_项目管理层/11_趋势追踪/eBPF_生态追踪.md"; To = "07_项目管理层/11_趋势追踪/03_eBPF_生态趋势追踪.md" },
    @{ From = "07_项目管理层/11_趋势追踪/Profiling_信号追踪.md"; To = "07_项目管理层/11_趋势追踪/04_Profiling_信号趋势追踪.md" },
    @{ From = "07_项目管理层/11_趋势追踪/Wasm_插件生态追踪.md"; To = "07_项目管理层/11_趋势追踪/05_Wasm_插件生态趋势追踪.md" },
    @{ From = "07_项目管理层/21_评价模型/范围专项批判性评价.md"; To = "07_项目管理层/21_评价模型/01_范围_范围专项批判性评价.md" },
    @{ From = "07_项目管理层/21_评价模型/项目全面批判性评价.md"; To = "07_项目管理层/21_评价模型/02_项目_项目全面批判性评价.md" },
    @{ From = "07_项目管理层/21_评价模型/项目优势分析.md"; To = "07_项目管理层/21_评价模型/03_优势_项目优势分析.md" },
    @{ From = "07_项目管理层/31_改进计划/短期改进计划_Q4_2025.md"; To = "07_项目管理层/31_改进计划/01_计划_短期改进计划_Q4_2025.md" }
)

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  批量重命名工具 - 规范化文件命名" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# 统计
$success = 0
$failed = 0
$notFound = 0

foreach ($mapping in $renameMappings) {
    $sourcePath = Join-Path $docsRoot $mapping.From
    $targetPath = Join-Path $docsRoot $mapping.To
    
    # 检查源文件是否存在
    if (-not (Test-Path $sourcePath)) {
        Write-Host "⚠ 源文件不存在: $($mapping.From)" -ForegroundColor Yellow
        $notFound++
        continue
    }
    
    # 检查目标文件是否已存在
    if (Test-Path $targetPath) {
        Write-Host "⚠ 目标文件已存在，跳过: $($mapping.To)" -ForegroundColor Yellow
        $failed++
        continue
    }
    
    # 执行重命名
    try {
        Rename-Item -Path $sourcePath -NewName (Split-Path $targetPath -Leaf) -ErrorAction Stop
        Write-Host "✓ 重命名: $($mapping.From)" -ForegroundColor Green
        Write-Host "    → $($mapping.To)" -ForegroundColor DarkGreen
        $success++
    } catch {
        Write-Host "✗ 失败: $($mapping.From) - $_" -ForegroundColor Red
        $failed++
    }
}

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  重命名完成统计" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "成功: $success" -ForegroundColor Green
Write-Host "失败: $failed" -ForegroundColor Red
Write-Host "未找到: $notFound" -ForegroundColor Yellow
Write-Host "总计: $($success + $failed + $notFound)" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan

# 生成映射表供后续引用更新使用
$mappingTable = $renameMappings | ForEach-Object {
    [PSCustomObject]@{
        原文件名 = $_.From
        新文件名 = $_.To
    }
}

$mappingTable | Export-Csv -Path "$PSScriptRoot\文件重命名映射表.csv" -NoTypeInformation -Encoding UTF8
Write-Host "映射表已保存到: $PSScriptRoot\文件重命名映射表.csv" -ForegroundColor Green
