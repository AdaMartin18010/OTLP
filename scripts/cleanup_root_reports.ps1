# PowerShell Script: 清理根目录报告文件
# 功能：将28个历史报告文件移动到归档目录
# 作者：OTLP项目团队
# 日期：2025-10-18

<#
.SYNOPSIS
清理OTLP项目根目录的历史报告文件

.DESCRIPTION
将根目录中的28个历史"完成报告"文件移动到doc_legacy_archive/2025_10_reports/目录
包含预览模式和执行模式，确保安全操作

.PARAMETER Execute
实际执行文件移动（不加此参数仅预览）

.EXAMPLE
.\cleanup_root_reports.ps1
# 预览模式：显示将要移动的文件

.EXAMPLE
.\cleanup_root_reports.ps1 -Execute
# 执行模式：实际移动文件
#>

param(
    [switch]$Execute = $false
)

# 设置错误处理
$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# 获取项目根目录
$projectRoot = Split-Path -Parent $PSScriptRoot
$archiveDir = Join-Path $projectRoot "doc_legacy_archive\2025_10_reports"

Write-ColorOutput "`n================================================" "Cyan"
Write-ColorOutput "OTLP项目根目录清理工具 (PowerShell版本)" "Cyan"
Write-ColorOutput "================================================`n" "Cyan"

# 要移动的文件模式（28个历史报告）
$filePatterns = @(
    "⚡_*.md",
    "✅_*.md",
    "🌟_*.md",
    "🎉_*.md",
    "🎊_*.md",
    "🎓_*.md",
    "🎯_*.md",
    "🏆_*.md",
    "📊_*.md",
    "📝_*.md",
    "🔴_*.md",
    "🚀_*.md"
)

# 排除的文件（最新的状态文件要保留）
$excludeFiles = @(
    "PROJECT_STATUS_2025_10_18.md",
    "OTLP项目全面批判性评价_2025_10_18_最新Web标准对标.md",
    "OTLP项目可中断执行改进计划_2025_10_18.md",
    "📋_OTLP项目批判性评价执行摘要_2025_10_18.md",
    "🚀_开始这里_批判性评价报告导航_2025_10_18.md"
)

# 收集要移动的文件
$filesToMove = @()
foreach ($pattern in $filePatterns) {
    $files = Get-ChildItem -Path $projectRoot -Filter $pattern -File
    foreach ($file in $files) {
        if ($excludeFiles -notcontains $file.Name) {
            $filesToMove += $file
        }
    }
}

# 去重和排序
$filesToMove = $filesToMove | Sort-Object Name -Unique

Write-ColorOutput "📁 项目根目录: $projectRoot" "Yellow"
Write-ColorOutput "📦 归档目录: $archiveDir" "Yellow"
Write-ColorOutput "`n🔍 扫描结果:" "Green"
Write-ColorOutput "找到 $($filesToMove.Count) 个需要移动的文件`n" "Green"

# 显示文件列表
Write-ColorOutput "文件列表:" "White"
Write-ColorOutput "----------------------------------------" "Gray"
$index = 1
foreach ($file in $filesToMove) {
    $sizeKB = [math]::Round($file.Length / 1KB, 2)
    Write-ColorOutput "$index. $($file.Name) ($sizeKB KB)" "White"
    $index++
}
Write-ColorOutput "----------------------------------------`n" "Gray"

# 预览模式 vs 执行模式
if (-not $Execute) {
    Write-ColorOutput "⚠️  这是预览模式，文件不会被移动" "Yellow"
    Write-ColorOutput "`n要实际执行移动，请运行:" "Yellow"
    Write-ColorOutput "  .\scripts\cleanup_root_reports.ps1 -Execute`n" "Cyan"
    
    Write-ColorOutput "📋 操作说明:" "Green"
    Write-ColorOutput "1. 将创建归档目录: $archiveDir" "White"
    Write-ColorOutput "2. 移动上述 $($filesToMove.Count) 个文件到归档目录" "White"
    Write-ColorOutput "3. 创建归档README说明文件" "White"
    Write-ColorOutput "4. Git会自动跟踪这些变更，无需担心数据丢失" "White"
    
    exit 0
}

# 执行模式
Write-ColorOutput "🚀 执行模式：开始移动文件..." "Green"

# 创建归档目录
if (-not (Test-Path $archiveDir)) {
    Write-ColorOutput "`n📁 创建归档目录..." "Yellow"
    New-Item -Path $archiveDir -ItemType Directory -Force | Out-Null
    Write-ColorOutput "✅ 归档目录创建成功" "Green"
}

# 移动文件
Write-ColorOutput "`n📦 移动文件中..." "Yellow"
$movedCount = 0
$failedCount = 0

foreach ($file in $filesToMove) {
    try {
        $destination = Join-Path $archiveDir $file.Name
        Move-Item -Path $file.FullName -Destination $destination -Force
        Write-ColorOutput "  ✅ $($file.Name)" "Green"
        $movedCount++
    }
    catch {
        Write-ColorOutput "  ❌ 失败: $($file.Name) - $($_.Exception.Message)" "Red"
        $failedCount++
    }
}

# 创建归档README
$readmeContent = @"
# 2025年10月历史报告归档

> **归档日期**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
> **归档原因**: 项目结构清理，统一状态管理  
> **工具**: PowerShell自动化脚本

---

## 📋 归档说明

本目录包含OTLP项目在2025年10月之前创建的历史"完成报告"文件。这些文件记录了项目的历史进展，但造成了根目录混乱。

### 为什么归档？

1. **结构混乱**: 根目录包含28个类似的报告文件
2. **用户困惑**: 不清楚项目当前状态
3. **版本管理**: 多个"最终版本"造成混淆

### 新的状态管理

现在项目使用统一的状态管理：
- **主状态文件**: `PROJECT_STATUS_2025_10_18.md`
- **JSON追踪**: `.progress/current_status.json`
- **清晰导航**: 单一入口，清晰的项目状态

---

## 📁 归档文件

本次归档了 **$movedCount** 个文件：

$(foreach ($file in $filesToMove) { "- $($file.Name)`n" })

---

## 🔄 如何查看历史

如果需要查看项目历史进展：

1. **本目录**: 包含所有历史报告
2. **Git历史**: `git log --oneline`
3. **主状态文件**: 包含关键成就总结

---

## ⚠️  注意事项

- 这些文件仅用于历史参考
- 请查看根目录的 `PROJECT_STATUS_2025_10_18.md` 了解当前状态
- 不要恢复这些文件到根目录

---

**归档完成时间**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**归档工具版本**: PowerShell Script v1.0
"@

$readmePath = Join-Path $archiveDir "README.md"
$readmeContent | Out-File -FilePath $readmePath -Encoding UTF8

Write-ColorOutput "`n✅ 归档README创建成功" "Green"

# 最终报告
Write-ColorOutput "`n================================================" "Cyan"
Write-ColorOutput "清理完成！" "Green"
Write-ColorOutput "================================================" "Cyan"
Write-ColorOutput "`n📊 统计信息:" "Yellow"
Write-ColorOutput "  ✅ 成功移动: $movedCount 个文件" "Green"
if ($failedCount -gt 0) {
    Write-ColorOutput "  ❌ 失败: $failedCount 个文件" "Red"
}
Write-ColorOutput "  📁 归档位置: $archiveDir" "Yellow"

Write-ColorOutput "`n🎯 下一步建议:" "Green"
Write-ColorOutput "1. 检查根目录是否干净: Get-ChildItem *.md" "White"
Write-ColorOutput "2. 检查归档目录: Get-ChildItem $archiveDir" "White"
Write-ColorOutput "3. Git提交变更: git add . && git commit -m 'chore: archive legacy reports'" "White"

Write-ColorOutput "`n✨ 项目根目录现在整洁了！" "Green"


