# 批量重命名docs/00_参考资料目录下的文件
# 将不规范的命名改为NN_类别_主题.md格式
# 保留已有规范前缀的文件

param(
    [string]$TargetDir = "$PSScriptRoot\..\docs\00_参考资料",
    [switch]$WhatIf  # 预览模式，不实际执行重命名
)

$ErrorActionPreference = "Stop"

# 规范化路径
$targetPath = Resolve-Path $TargetDir -ErrorAction Stop
Write-Host "目标目录: $targetPath" -ForegroundColor Cyan
Write-Host "=" * 60

# 定义重命名映射表（不规范文件名 -> 规范文件名）
$renameMap = @{
    # 组件/工具类
    "Collector组件矩阵.md" = "51_工具_Collector组件矩阵.md"
    
    # 参考/文档类
    "knowledge_README.md" = "99_参考_knowledge_README.md"
    
    # 知识图谱类
    "OpenTelemetry完整知识图谱.md" = "11_图谱_OpenTelemetry完整知识图谱.md"
    "主题关系图谱.md" = "12_图谱_主题关系图谱.md"
    
    # 版本/更新类
    "OTLP_v1.10.0版本更新说明.md" = "91_版本_OTLP_v1.10.0版本更新说明.md"
    
    # 问题/FAQ类
    "❓_常见问题FAQ.md" = "71_问题_常见问题FAQ.md"
    
    # 思维导图类
    "主题总览思维导图.md" = "21_导图_主题总览思维导图.md"
    "学习路径导图.md" = "22_导图_学习路径导图.md"
    "战略规划导图.md" = "23_导图_战略规划导图.md"
    "范围思维导图_OTLP_Metrics_Logs.md" = "24_导图_范围思维导图.md"
    "项目级思维导图.md" = "25_导图_项目级思维导图.md"
    
    # 矩阵对比类
    "后端方案对比矩阵.md" = "41_矩阵_后端方案对比矩阵.md"
    "竞争力分析矩阵.md" = "42_矩阵_竞争力分析矩阵.md"
    "范围矩阵_协议与数据模型对比.md" = "43_矩阵_范围矩阵_协议与数据模型对比.md"
    "语言SDK对比矩阵.md" = "44_矩阵_语言SDK对比矩阵.md"
    "质量评估矩阵.md" = "45_矩阵_质量评估矩阵.md"
    "采样策略对比矩阵.md" = "46_矩阵_采样策略对比矩阵.md"
    "项目级多维矩阵.md" = "47_矩阵_项目级多维矩阵.md"
    
    # 决策树类
    "技术选型决策树.md" = "31_决策_技术选型决策树.md"
    "插桩方式选择决策树.md" = "32_决策_插桩方式选择决策树.md"
    "故障排查决策树.md" = "33_决策_故障排查决策树.md"
    
    # 导航类（emoji转数字前缀）
    "🎓_学习路径快速导航.md" = "02_导航_学习路径快速导航.md"
    "文档地图_可视化导航.md" = "01_导航_文档地图_可视化导航.md"
    
    # 指南类（emoji转数字前缀）
    "🔧_故障排查指南.md" = "82_指南_故障排查指南.md"
    "🚀_快速入门指南.md" = "83_指南_快速入门指南.md"
    "快速开始指南.md" = "81_指南_快速开始指南.md"
    
    # 报告类
    "表征体系构建完成报告.md" = "61_报告_表征体系构建完成报告.md"
    
    # 论文/学术类
    "ARTIFACT_PREPARATION_GUIDE.md" = "92_论文_ARTIFACT_PREPARATION_GUIDE.md"
    "COMPILATION_GUIDE.md" = "93_论文_COMPILATION_GUIDE.md"
    
    # README文件
    "README.md" = "00_README.md"
}

# 定义保留的文件模式（不需要重命名）
$preservePatterns = @(
    "^\d{2}_"           # 已有数字前缀（如00_, 01_等）
    "^参考_"            # 已有"参考_"前缀
    "^指南_"            # 已有"指南_"前缀
    "^快速_"            # 已有"快速_"前缀
)

# 统计计数器
$stats = @{
    Renamed = 0
    Skipped = 0
    Conflicts = 0
    Preserved = 0
    NotFound = 0
}

# 检查文件是否应该被保留（不处理）
function ShouldPreserve($fileName) {
    foreach ($pattern in $preservePatterns) {
        if ($fileName -match $pattern) {
            return $true
        }
    }
    return $false
}

# 获取目录下所有.md文件
$allFiles = Get-ChildItem -Path $targetPath -File -Filter "*.md" | Select-Object -ExpandProperty Name

Write-Host "扫描到 $($allFiles.Count) 个markdown文件" -ForegroundColor Gray
Write-Host ""

# 处理每个需要重命名的文件
foreach ($entry in $renameMap.GetEnumerator()) {
    $oldName = $entry.Key
    $newName = $entry.Value
    $oldPath = Join-Path $targetPath $oldName
    $newPath = Join-Path $targetPath $newName
    
    # 检查源文件是否存在
    if (-not (Test-Path $oldPath)) {
        Write-Host "⚠ 未找到: $oldName" -ForegroundColor Yellow
        $stats.NotFound++
        continue
    }
    
    # 如果文件已经有规范前缀，跳过
    if (ShouldPreserve $oldName) {
        Write-Host "→ 保留: $oldName" -ForegroundColor DarkGray
        $stats.Preserved++
        continue
    }
    
    # 检查目标文件名是否已存在
    if (Test-Path $newPath) {
        Write-Host "❌ 冲突: $oldName -> $newName (目标已存在)" -ForegroundColor Red
        $stats.Conflicts++
        continue
    }
    
    # 执行重命名
    try {
        if ($WhatIf) {
            Write-Host "[预览] $oldName -> $newName" -ForegroundColor Cyan
        } else {
            Rename-Item -Path $oldPath -NewName $newName -ErrorAction Stop
            Write-Host "✓ 重命名: $oldName -> $newName" -ForegroundColor Green
        }
        $stats.Renamed++
    }
    catch {
        Write-Host "❌ 错误: $oldName -> $newName : $($_.Exception.Message)" -ForegroundColor Red
        $stats.Conflicts++
    }
}

# 检查目录中是否有未处理的文件（未被映射且不符合保留规则的）
Write-Host ""
Write-Host "检查未映射文件..." -ForegroundColor Cyan
$processedNames = $renameMap.Keys + ($allFiles | Where-Object { ShouldPreserve $_ })
$unmappedFiles = $allFiles | Where-Object { 
    $file = $_
    -not ($processedNames -contains $file) -and 
    -not (ShouldPreserve $file)
}

if ($unmappedFiles) {
    Write-Host "以下文件未被映射，可能需要手动处理:" -ForegroundColor Yellow
    foreach ($file in $unmappedFiles) {
        Write-Host "  - $file" -ForegroundColor Yellow
    }
} else {
    Write-Host "所有文件已处理或已保留" -ForegroundColor Green
}

# 输出统计信息
Write-Host ""
Write-Host "=" * 60
Write-Host "处理完成统计:" -ForegroundColor Cyan
Write-Host "  重命名: $($stats.Renamed)" -ForegroundColor Green
Write-Host "  保留(已有规范前缀): $($stats.Preserved)" -ForegroundColor DarkGray
Write-Host "  未找到: $($stats.NotFound)" -ForegroundColor Yellow
Write-Host "  冲突/错误: $($stats.Conflicts)" -ForegroundColor Red
if ($unmappedFiles) {
    Write-Host "  未映射: $($unmappedFiles.Count)" -ForegroundColor Yellow
}
Write-Host "=" * 60

if ($WhatIf) {
    Write-Host "`n注意: 当前为预览模式，未实际执行重命名操作。" -ForegroundColor Magenta
    Write-Host "去掉 -WhatIf 参数以实际执行重命名。" -ForegroundColor Magenta
}
