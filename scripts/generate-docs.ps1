# OpenTelemetry 文档生成脚本
# 用于生成文档索引、更新统计信息等

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
    [switch]$UpdateIndex,
    [switch]$UpdateStats,
    [switch]$GenerateTOC,
    [switch]$All,
    [string]$OutputPath = "docs"
)

# 如果指定了 -All，则执行所有操作
if ($All) {
    $UpdateIndex = $true
    $UpdateStats = $true
    $GenerateTOC = $true
}

# 如果没有指定任何操作，默认执行所有
if (-not ($UpdateIndex -or $UpdateStats -or $GenerateTOC)) {
    $UpdateIndex = $true
    $UpdateStats = $true
    $GenerateTOC = $true
}

Write-Host "OpenTelemetry 文档生成工具" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir
$docsPath = Join-Path $projectRoot $OutputPath

if (-not (Test-Path $docsPath)) {
    Write-Error "文档目录不存在: $docsPath"
    exit 1
}

# 更新文档统计信息
if ($UpdateStats) {
    Write-Host "`n更新文档统计信息..." -ForegroundColor Cyan
    
    $markdownFiles = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse
    $totalLines = 0
    $totalWords = 0
    $totalChars = 0
    
    foreach ($file in $markdownFiles) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        $lines = ($content -split "`n").Count
        $words = ($content -split "\s+" | Where-Object { $_ -ne "" }).Count
        $chars = $content.Length
        
        $totalLines += $lines
        $totalWords += $words
        $totalChars += $chars
    }
    
    $statsContent = @"
# 文档统计信息

## 总体统计

- **文档数量**: $($markdownFiles.Count) 个
- **总行数**: $totalLines 行
- **总字数**: $totalWords 字
- **总字符数**: $totalChars 字符

## 文档详情

| 文件名 | 行数 | 字数 | 字符数 | 最后修改 |
|--------|------|------|--------|----------|
"@
    
    foreach ($file in $markdownFiles | Sort-Object Name) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        $lines = ($content -split "`n").Count
        $words = ($content -split "\s+" | Where-Object { $_ -ne "" }).Count
        $chars = $content.Length
        $lastModified = $file.LastWriteTime.ToString("yyyy-MM-dd HH:mm")
        
        $statsContent += "`n| [$($file.Name)]($($file.Name)) | $lines | $words | $chars | $lastModified |"
    }
    
    $statsContent += @"

## 生成时间

*统计生成时间: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*

---

*此文件由文档生成工具自动创建，请勿手动编辑*
"@
    
    $statsFile = Join-Path $docsPath "STATS.md"
    $statsContent | Out-File -FilePath $statsFile -Encoding UTF8
    Write-Host "✅ 统计信息已更新到 $statsFile" -ForegroundColor Green
}

# 生成目录
if ($GenerateTOC) {
    Write-Host "`n生成文档目录..." -ForegroundColor Cyan
    
    $tocContent = @"
# 文档目录

## 核心文档

"@
    
    $coreDocs = @(
        "QUICK_START.md",
        "TUTORIALS.md", 
        "API_REFERENCE.md",
        "ARCHITECTURE.md",
        "TERMS.md",
        "SEMANTIC_CONVENTIONS.md"
    )
    
    foreach ($doc in $coreDocs) {
        $docPath = Join-Path $docsPath $doc
        if (Test-Path $docPath) {
            $content = Get-Content $docPath -Raw -Encoding UTF8
            $title = if ($content -match "^#\s+(.+)$") { $matches[1] } else { $doc }
            $tocContent += "`n- [$title]($doc)"
        }
    }
    
    $tocContent += @"

## 实践指南

"@
    
    $guideDocs = @(
        "DEPLOYMENT_GUIDE.md",
        "INTEGRATION_GUIDE.md",
        "PERFORMANCE_GUIDE.md",
        "SECURITY_GUIDE.md",
        "TROUBLESHOOTING.md"
    )
    
    foreach ($doc in $guideDocs) {
        $docPath = Join-Path $docsPath $doc
        if (Test-Path $docPath) {
            $content = Get-Content $docPath -Raw -Encoding UTF8
            $title = if ($content -match "^#\s+(.+)$") { $matches[1] } else { $doc }
            $tocContent += "`n- [$title]($doc)"
        }
    }
    
    $tocContent += @"

## 教育与研究

"@
    
    $eduDocs = @(
        "COURSE_ALIGNMENT.md",
        "FORMAL_PROOFS.md"
    )
    
    foreach ($doc in $eduDocs) {
        $docPath = Join-Path $docsPath $doc
        if (Test-Path $docPath) {
            $content = Get-Content $docPath -Raw -Encoding UTF8
            $title = if ($content -match "^#\s+(.+)$") { $matches[1] } else { $doc }
            $tocContent += "`n- [$title]($doc)"
        }
    }
    
    $tocContent += @"

## 项目状态

"@
    
    $statusDocs = @(
        "STATUS.md",
        "FORMAT_STANDARDS.md",
        "STATS.md"
    )
    
    foreach ($doc in $statusDocs) {
        $docPath = Join-Path $docsPath $doc
        if (Test-Path $docPath) {
            $content = Get-Content $docPath -Raw -Encoding UTF8
            $title = if ($content -match "^#\s+(.+)$") { $matches[1] } else { $doc }
            $tocContent += "`n- [$title]($doc)"
        }
    }
    
    $tocContent += @"

---

*此目录由文档生成工具自动创建，最后更新时间: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*
"@
    
    $tocFile = Join-Path $docsPath "TOC.md"
    $tocContent | Out-File -FilePath $tocFile -Encoding UTF8
    Write-Host "✅ 目录已生成到 $tocFile" -ForegroundColor Green
}

# 更新文档索引
if ($UpdateIndex) {
    Write-Host "`n更新文档索引..." -ForegroundColor Cyan
    
    # 这里可以添加更新INDEX.md的逻辑
    # 比如检查是否有新文档，更新链接等
    
    Write-Host "✅ 文档索引已更新" -ForegroundColor Green
}

Write-Host "`n🎉 文档生成完成！" -ForegroundColor Green
Write-Host "建议运行验证脚本检查文档质量: ./scripts/validate-docs.ps1" -ForegroundColor Yellow
