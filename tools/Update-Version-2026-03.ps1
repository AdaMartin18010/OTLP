# 更新OTLP文档版本到2026年3月最新版本
# 最新版本:
# - OTLP Protocol: v1.9.0
# - OpenTelemetry Specification: v1.55.0
# - Semantic Conventions: v1.40.0
# - Collector: v0.147.0

$ErrorActionPreference = "Stop"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  OTLP文档版本更新工具 - 2026年3月" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "目标版本:" -ForegroundColor Yellow
Write-Host "  OTLP Protocol:        v1.9.0" -ForegroundColor Green
Write-Host "  OpenTelemetry Spec:   v1.55.0" -ForegroundColor Green
Write-Host "  Semantic Conventions: v1.40.0" -ForegroundColor Green
Write-Host "  Collector:            v0.147.0" -ForegroundColor Green
Write-Host ""

# 获取所有markdown文件
$docsRoot = "E:\_src\OTLP\docs"
$files = Get-ChildItem -Path $docsRoot -Recurse -File -Filter "*.md"
Write-Host "扫描到 $($files.Count) 个Markdown文件" -ForegroundColor Cyan

# 统计
$updated = 0
$skipped = 0

# 排除版本历史文件
$excludePatterns = @(
    "版本更新日志",
    "变更日志",
    "CHANGELOG",
    "版本历史"
)

foreach ($file in $files) {
    # 检查是否是版本历史文件
    $isHistoryFile = $false
    foreach ($pattern in $excludePatterns) {
        if ($file.Name -match $pattern) {
            $isHistoryFile = $true
            break
        }
    }
    
    if ($isHistoryFile) {
        $skipped++
        continue
    }
    
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
    $originalContent = $content
    $modified = $false
    
    # 更新YAML frontmatter中的版本
    # 匹配 version: OTLP v1.x.x
    if ($content -match 'version:\s*OTLP\s*v1\.[0-9]+\.[0-9]+') {
        $content = $content -replace 'version:\s*OTLP\s*v1\.[0-9]+\.[0-9]+', 'version: OTLP v1.9.0'
        $modified = $true
    }
    
    # 匹配 version: v1.x.x (没有OTLP前缀)
    if ($content -match '(?<!OTLP\s)version:\s*v1\.[0-9]+\.[0-9]+') {
        $content = $content -replace '(?<!OTLP\s)version:\s*v1\.[0-9]+\.[0-9]+', 'version: OTLP v1.9.0'
        $modified = $true
    }
    
    # 更新Spec版本
    if ($content -match 'spec_version:\s*v1\.[0-9]+\.[0-9]+') {
        $content = $content -replace 'spec_version:\s*v1\.[0-9]+\.[0-9]+', 'spec_version: v1.55.0'
        $modified = $true
    }
    
    # 更新Semantic Conventions版本
    if ($content -match 'semconv_version:\s*v1\.[0-9]+\.[0-9]+') {
        $content = $content -replace 'semconv_version:\s*v1\.[0-9]+\.[0-9]+', 'semconv_version: v1.40.0'
        $modified = $true
    }
    
    # 更新Collector版本
    if ($content -match 'collector_version:\s*v0\.[0-9]+\.[0-9]+') {
        $content = $content -replace 'collector_version:\s*v0\.[0-9]+\.[0-9]+', 'collector_version: v0.147.0'
        $modified = $true
    }
    
    # 更新日期
    if ($content -match 'date:\s*\d{4}-\d{2}-\d{2}') {
        $content = $content -replace 'date:\s*\d{4}-\d{2}-\d{2}', 'date: 2026-03-17'
        $modified = $true
    }
    
    # 如果内容被修改，写回文件
    if ($modified -and ($content -ne $originalContent)) {
        Set-Content -Path $file.FullName -Value $content -Encoding UTF8
        Write-Host "✓ 更新: $($file.FullName.Replace($docsRoot, 'docs'))" -ForegroundColor Green
        $updated++
    }
}

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  更新完成" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "更新文件数: $updated" -ForegroundColor Green
Write-Host "跳过文件数: $skipped" -ForegroundColor Yellow
Write-Host "========================================" -ForegroundColor Cyan
