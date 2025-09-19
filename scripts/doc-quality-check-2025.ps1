# OTLP 2025 文档质量检查脚本
# 支持 Markdown 文档质量检查、链接验证、格式检查

param(
    [string]$Path = "docs",
    [switch]$Fix,
    [switch]$Verbose,
    [switch]$Export
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 检查 Markdown 文件
function Test-MarkdownFile {
    param([string]$FilePath)
    
    $issues = @()
    $content = Get-Content $FilePath -Raw -Encoding UTF8
    
    # 检查文件编码
    if ($content -match "[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]") {
        $issues += "❌ 文件包含非UTF-8字符"
    }
    
    # 检查标题结构
    $headings = [regex]::Matches($content, '^#+\s+(.+)$', [System.Text.RegularExpressions.RegexOptions]::Multiline)
    $headingLevels = @()
    foreach ($heading in $headings) {
        $level = ($heading.Value -split '#').Length - 1
        $headingLevels += $level
    }
    
    # 检查标题层级跳跃
    for ($i = 1; $i -lt $headingLevels.Length; $i++) {
        if ($headingLevels[$i] - $headingLevels[$i-1] -gt 1) {
            $issues += "⚠️ 标题层级跳跃: $($headingLevels[$i-1]) -> $($headingLevels[$i])"
        }
    }
    
    # 检查空行
    if ($content -match '\n\n\n+') {
        $issues += "⚠️ 存在多余空行"
    }
    
    # 检查行尾空格
    $lines = $content -split "`n"
    for ($i = 0; $i -lt $lines.Length; $i++) {
        if ($lines[$i] -match '\s+$') {
            $issues += "⚠️ 第$($i+1)行存在行尾空格"
        }
    }
    
    # 检查链接格式
    $links = [regex]::Matches($content, '\[([^\]]+)\]\(([^)]+)\)')
    foreach ($link in $links) {
        $url = $link.Groups[2].Value
        if ($url -match '^https?://' -and $url -notmatch '^https://[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}') {
            $issues += "⚠️ 可疑链接格式: $url"
        }
    }
    
    # 检查图片链接
    $images = [regex]::Matches($content, '!\[([^\]]*)\]\(([^)]+)\)')
    foreach ($image in $images) {
        $alt = $image.Groups[1].Value
        if ([string]::IsNullOrWhiteSpace($alt)) {
            $issues += "⚠️ 图片缺少alt文本"
        }
    }
    
    # 检查代码块
    $codeBlocks = [regex]::Matches($content, '```(\w+)?\n([\s\S]*?)```')
    foreach ($block in $codeBlocks) {
        $language = $block.Groups[1].Value
        $code = $block.Groups[2].Value
        
        if ([string]::IsNullOrWhiteSpace($language)) {
            $issues += "⚠️ 代码块缺少语言标识"
        }
        
        # 检查代码块内容
        if ($code -match '\t') {
            $issues += "⚠️ 代码块包含制表符，建议使用空格"
        }
    }
    
    # 检查表格格式
    $tables = [regex]::Matches($content, '\|.*\|', [System.Text.RegularExpressions.RegexOptions]::Multiline)
    if ($tables.Count -gt 0) {
        $tableLines = $tables | ForEach-Object { $_.Value }
        $columnCounts = $tableLines | ForEach-Object { ($_ -split '\|').Length - 2 }
        $uniqueCounts = $columnCounts | Sort-Object -Unique
        if ($uniqueCounts.Count -gt 1) {
            $issues += "⚠️ 表格列数不一致"
        }
    }
    
    return $issues
}

# 检查文档结构
function Test-DocumentStructure {
    param([string]$DocsPath)
    
    $issues = @()
    
    # 检查必需文件
    $requiredFiles = @(
        "README.md",
        "INDEX.md",
        "TOC.md",
        "QUICK_START.md",
        "API_REFERENCE.md",
        "ARCHITECTURE.md"
    )
    
    foreach ($file in $requiredFiles) {
        $filePath = Join-Path $DocsPath $file
        if (!(Test-Path $filePath)) {
            $issues += "❌ 缺少必需文件: $file"
        }
    }
    
    # 检查目录结构
    $expectedDirs = @("examples", "implementations", "languages", "governance")
    foreach ($dir in $expectedDirs) {
        $dirPath = Join-Path $DocsPath "..\$dir"
        if (!(Test-Path $dirPath)) {
            $issues += "❌ 缺少必需目录: $dir"
        }
    }
    
    return $issues
}

# 检查链接有效性
function Test-Links {
    param([string]$FilePath)
    
    $issues = @()
    $content = Get-Content $FilePath -Raw -Encoding UTF8
    
    # 提取所有链接
    $links = [regex]::Matches($content, '\[([^\]]+)\]\(([^)]+)\)')
    
    foreach ($link in $links) {
        $url = $link.Groups[2].Value
        
        # 跳过外部链接
        if ($url -match '^https?://') {
            continue
        }
        
        # 检查内部链接
        if ($url -match '^#') {
            # 锚点链接
            $anchor = $url.Substring(1)
            $headings = [regex]::Matches($content, '^#+\s+(.+)$', [System.Text.RegularExpressions.RegexOptions]::Multiline)
            $found = $false
            foreach ($heading in $headings) {
                $headingText = $heading.Groups[1].Value -replace '[^\w\s]', '' -replace '\s+', '-'
                if ($headingText -eq $anchor) {
                    $found = $true
                    break
                }
            }
            if (!$found) {
                $issues += "❌ 无效锚点链接: $url"
            }
        } elseif ($url -match '\.md$') {
            # Markdown 文件链接
            $linkPath = Join-Path (Split-Path $FilePath -Parent) $url
            if (!(Test-Path $linkPath)) {
                $issues += "❌ 无效文件链接: $url"
            }
        }
    }
    
    return $issues
}

# 生成质量报告
function Generate-QualityReport {
    param([string]$OutputPath = "doc-quality-reports/doc-quality-report-$(Get-Date -Format 'yyyy-MM-dd-HHmmss').md")
    
    Write-ColorOutput "📊 生成文档质量报告..." "Cyan"
    
    $report = @"
# OTLP 2025 文档质量检查报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**检查路径**: $Path

## 检查结果

### 文档结构检查
"@

    $structureIssues = Test-DocumentStructure $Path
    if ($structureIssues.Count -eq 0) {
        $report += "`n✅ 文档结构检查通过`n"
    } else {
        foreach ($issue in $structureIssues) {
            $report += "`n$issue`n"
        }
    }

    $report += @"

### 文件质量检查
"@

    $markdownFiles = Get-ChildItem -Path $Path -Filter "*.md" -Recurse
    $totalIssues = 0
    
    foreach ($file in $markdownFiles) {
        $fileIssues = Test-MarkdownFile $file.FullName
        $linkIssues = Test-Links $file.FullName
        $allIssues = $fileIssues + $linkIssues
        
        if ($allIssues.Count -gt 0) {
            $report += "`n#### $($file.Name)`n"
            foreach ($issue in $allIssues) {
                $report += "- $issue`n"
            }
            $totalIssues += $allIssues.Count
        }
    }

    if ($totalIssues -eq 0) {
        $report += "`n✅ 所有文档文件质量检查通过`n"
    }

    $report += @"

## 统计信息

- 检查文件数: $($markdownFiles.Count)
- 发现问题数: $totalIssues
- 检查时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

## 建议

1. 定期运行文档质量检查
2. 修复发现的问题
3. 建立文档编写规范
4. 启用自动化检查

---
*报告由 OTLP 2025 文档质量检查脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 文档质量报告已生成: $OutputPath" "Green"
}

# 修复文档问题
function Fix-DocumentIssues {
    param([string]$FilePath)
    
    Write-ColorOutput "🔧 修复文档问题: $FilePath" "Yellow"
    
    $content = Get-Content $FilePath -Raw -Encoding UTF8
    
    # 修复行尾空格
    $content = $content -replace '\s+$', ''
    
    # 修复多余空行
    $content = $content -replace '\n\n\n+', "`n`n"
    
    # 修复制表符
    $content = $content -replace '\t', '    '
    
    # 保存修复后的内容
    $content | Out-File -FilePath $FilePath -Encoding UTF8 -NoNewline
    Write-ColorOutput "✅ 文档问题已修复" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 文档质量检查开始..." "Green"
    Write-ColorOutput ("=" * 50) "Gray"
    
    if (!(Test-Path $Path)) {
        Write-ColorOutput "❌ 路径不存在: $Path" "Red"
        exit 1
    }
    
    # 检查文档结构
    Write-ColorOutput "🔍 检查文档结构..." "Cyan"
    $structureIssues = Test-DocumentStructure $Path
    foreach ($issue in $structureIssues) {
        Write-ColorOutput $issue "Red"
    }
    
    # 检查 Markdown 文件
    Write-ColorOutput "🔍 检查 Markdown 文件..." "Cyan"
    $markdownFiles = Get-ChildItem -Path $Path -Filter "*.md" -Recurse
    $totalIssues = 0
    
    foreach ($file in $markdownFiles) {
        if ($Verbose) {
            Write-ColorOutput "检查文件: $($file.Name)" "White"
        }
        
        $fileIssues = Test-MarkdownFile $file.FullName
        $linkIssues = Test-Links $file.FullName
        $allIssues = $fileIssues + $linkIssues
        
        if ($allIssues.Count -gt 0) {
            Write-ColorOutput "📄 $($file.Name):" "Yellow"
            foreach ($issue in $allIssues) {
                Write-ColorOutput "  $issue" "Red"
            }
            $totalIssues += $allIssues.Count
            
            if ($Fix) {
                Fix-DocumentIssues $file.FullName
            }
        } else {
            if ($Verbose) {
                Write-ColorOutput "✅ $($file.Name): 无问题" "Green"
            }
        }
    }
    
    if ($Export) {
        Generate-QualityReport
    }
    
    Write-ColorOutput ("=" * 50) "Gray"
    Write-ColorOutput "✅ 文档质量检查完成!" "Green"
    Write-ColorOutput "📊 总计发现问题: $totalIssues" "White"
    
    if ($totalIssues -gt 0 -and !$Fix) {
        Write-ColorOutput "💡 使用 -Fix 参数自动修复问题" "Yellow"
    }
}

# 执行主函数
Main
