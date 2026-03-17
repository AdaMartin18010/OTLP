# OTLP知识库全面版本对齐脚本
# 将v1.9.0更新为v1.10.0，并同步其他组件版本

param(
    [switch]$TestMode,
    [switch]$CreateBackup
)

$ErrorActionPreference = "Stop"

# 版本映射表
$VersionMappings = @(
    # OTLP Protocol
    @{ Pattern = 'OTLP v1\.9\.0'; Replacement = 'OTLP v1.10.0' }
    @{ Pattern = 'OTLP Protocol v1\.9\.0'; Replacement = 'OTLP Protocol v1.10.0' }
    @{ Pattern = 'opentelemetry-proto v1\.9\.0'; Replacement = 'opentelemetry-proto v1.10.0' }
    
    # Collector (已有v0.147.0，无需更新)
    # Semantic Conventions (已有v1.40.0，无需更新)
    # OpenTelemetry Spec (已有v1.55.0，无需更新)
)

Write-Host "🚀 开始全面版本对齐..." -ForegroundColor Green
Write-Host "═══════════════════════════════════════════"

# 获取所有Markdown文件
$files = Get-ChildItem -Path "docs" -Filter "*.md" -Recurse
Write-Host "📄 找到 $($files.Count) 个Markdown文件"

$updatedFiles = 0
$totalReplacements = 0

foreach ($file in $files) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $originalContent = $content
    $fileReplacements = 0
    
    foreach ($mapping in $VersionMappings) {
        $matches = [regex]::Matches($content, $mapping.Pattern)
        if ($matches.Count -gt 0) {
            $content = $content -replace $mapping.Pattern, $mapping.Replacement
            $fileReplacements += $matches.Count
            $totalReplacements += $matches.Count
        }
    }
    
    if ($fileReplacements -gt 0) {
        if (-not $TestMode) {
            if ($CreateBackup) {
                Copy-Item $file.FullName "$($file.FullName).bak" -Force
            }
            Set-Content -Path $file.FullName -Value $content -Encoding UTF8 -NoNewline
        }
        Write-Host "  ✅ $($file.Name): 更新 $fileReplacements 处" -ForegroundColor Cyan
        $updatedFiles++
    }
}

Write-Host "═══════════════════════════════════════════"
Write-Host "📊 更新统计:" -ForegroundColor Green
Write-Host "   处理文件: $($files.Count)"
Write-Host "   更新文件: $updatedFiles"
Write-Host "   替换次数: $totalReplacements"

if ($TestMode) {
    Write-Host ""
    Write-Host "⚠️  测试模式 - 未实际修改文件" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "✅ 版本对齐完成!" -ForegroundColor Green
