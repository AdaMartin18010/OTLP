# 更新文件内的交叉引用链接
# 根据重命名映射表更新所有Markdown文件中的相对链接

$ErrorActionPreference = "Stop"
$docsRoot = "E:\_src\OTLP\docs"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  更新交叉引用链接" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# 定义链接映射（旧文件名 -> 新文件名，不含路径）
$linkMappings = @{
    # 01_基础理论层
    "CONTROL_FLOW_EXECUTION_DATA_FLOW_ANALYSIS.md" = "01_控制流_执行流数据流分析.md"
    "DISTRIBUTED_SYSTEMS_THEORY.md" = "02_分布式_分布式系统理论.md"
    "OTLP_THEORETICAL_FRAMEWORK_INDEX.md" = "00_索引_OTLP理论框架总导航.md"
    "OTLP_UNIFIED_THEORETICAL_FRAMEWORK.md" = "01_理论_OTLP统一理论框架第一部分.md"
    "OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART2.md" = "02_理论_OTLP统一理论框架第二部分.md"
    "OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART3.md" = "03_理论_OTLP统一理论框架第三部分.md"
    "OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART4.md" = "04_理论_OTLP统一理论框架第四部分.md"
    "OTLP_UNIFIED_THEORETICAL_FRAMEWORK_PART5.md" = "05_理论_OTLP统一理论框架第五部分.md"
    "QUICK_REFERENCE.md" = "90_速查_语义模型快速参考.md"
    "SELF_AWARENESS_SELF_OPS_FRAMEWORK.md" = "06_运维_自我感知与自主运维框架.md"
    "SELF_HEALING_AUTO_ADJUSTMENT_ARCHITECTURE.md" = "07_自愈_自愈合自动调整架构.md"
    "SEMANTIC_MODELS_ANALYSIS_SUMMARY.md" = "08_总结_语义模型分析总结.md"
    "SEMANTIC_MODELS_AND_FLOW_ANALYSIS.md" = "09_流分析_语义模型与流分析.md"
    "OTLP数据模型语义完整性形式化论证.md" = "10_论证_OTLP数据模型语义完整性形式化论证.md"
    "OTLP与竞品语义模型深度对比.md" = "11_对比_OTLP与竞品语义模型深度对比.md"
    "OTLP语义模型本体论基础.md" = "12_本体论_OTLP语义模型本体论基础.md"
    "OTLP语义演化与版本兼容性理论.md" = "13_演化_OTLP语义演化与版本兼容性理论.md"
    
    # 02_核心协议层
    "OTLP_v1.9.0更新说明.md" = "91_版本_OTLP_v1.9.0更新说明.md"
    "Semantic_Conventions_v1.40.0_完整变更日志.md" = "91_变更日志_Semantic_Conventions_v1.40.0完整变更日志.md"
    "版本更新日志_v1.29_to_v1.38.md" = "92_变更日志_版本更新日志_v1.29_to_v1.38.md"
    "版本更新日志_v1.38_to_v1.39.md" = "93_变更日志_版本更新日志_v1.38_to_v1.39.md"
    "版本更新日志_v1.39_to_v1.40.md" = "94_变更日志_版本更新日志_v1.39_to_v1.40.md"
    "Zipkin_Exporter弃用说明与迁移指南.md" = "81_迁移_Zipkin_Exporter弃用说明与迁移指南.md"
    
    # 03_核心实现层
    "Collector_v0.147.0_完整变更日志.md" = "91_变更日志_Collector_v0.147.0完整变更日志.md"
    "OTLP_Collector_v0.147.0更新说明.md" = "92_版本_Collector_v0.147.0更新说明.md"
    "声明式配置完整指南_v1.0.md" = "81_指南_声明式配置完整指南.md"
    "OBI_2026年目标更新.md" = "91_规划_OBI_2026年目标更新.md"
    
    # 04_部署运维层
    "成本优化与FinOps实践指南.md" = "11_FinOps_成本优化与FinOps实践指南.md"
    "大规模Collector生产部署架构指南.md" = "01_部署_大规模Collector生产部署架构指南.md"
    "安全加固完整清单_v1.0.md" = "01_安全_安全加固完整清单.md"
    
    # 07_项目管理层
    "2025_Q4_趋势分析.md" = "01_趋势_2025_Q4趋势分析.md"
    "AI_ML_可观测性追踪.md" = "02_AI_ML_可观测性趋势追踪.md"
    "eBPF_生态追踪.md" = "03_eBPF_生态趋势追踪.md"
    "Profiling_信号追踪.md" = "04_Profiling_信号趋势追踪.md"
    "Wasm_插件生态追踪.md" = "05_Wasm_插件生态趋势追踪.md"
    "范围专项批判性评价.md" = "01_范围_范围专项批判性评价.md"
    "项目全面批判性评价.md" = "02_项目_项目全面批判性评价.md"
    "项目优势分析.md" = "03_优势_项目优势分析.md"
    "短期改进计划_Q4_2025.md" = "01_计划_短期改进计划_Q4_2025.md"
}

# 获取所有markdown文件
$files = Get-ChildItem -Path $docsRoot -Recurse -File -Filter "*.md"
Write-Host "扫描到 $($files.Count) 个Markdown文件" -ForegroundColor Cyan
Write-Host ""

# 统计
$updatedFiles = 0
$totalReplacements = 0

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
    $originalContent = $content
    $fileReplacements = 0
    
    # 检查并替换每个链接映射
    foreach ($oldName in $linkMappings.Keys) {
        $newName = $linkMappings[$oldName]
        
        # 使用简单的字符串替换（处理链接形式）
        # 匹配 (path/oldName) 或 (oldName)
        $oldPattern1 = "]($oldName)"
        $newPattern1 = "]($newName)"
        
        $count1 = 0
        while ($content.Contains($oldPattern1)) {
            $content = $content.Replace($oldPattern1, $newPattern1)
            $count1++
        }
        
        # 匹配路径中的文件名 (dir/oldName)
        $oldPattern2 = "/$oldName)"
        $newPattern2 = "/$newName)"
        
        $count2 = 0
        while ($content.Contains($oldPattern2)) {
            $content = $content.Replace($oldPattern2, $newPattern2)
            $count2++
        }
        
        $fileReplacements += $count1 + $count2
    }
    
    # 如果内容有变化，写回文件
    if ($content -ne $originalContent) {
        Set-Content -Path $file.FullName -Value $content -Encoding UTF8
        Write-Host "✓ 更新: $($file.FullName.Replace($docsRoot, 'docs')) ($fileReplacements 处替换)" -ForegroundColor Green
        $updatedFiles++
        $totalReplacements += $fileReplacements
    }
}

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  交叉引用更新完成" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "更新文件数: $updatedFiles" -ForegroundColor Green
Write-Host "总替换次数: $totalReplacements" -ForegroundColor Green
Write-Host "========================================" -ForegroundColor Cyan
