#Requires -Version 5.1
<#
.SYNOPSIS
    测试版本替换规则

.DESCRIPTION
    此脚本用于测试版本替换规则，验证正则表达式是否正确匹配预期内容
#>

param(
    [string]$DocsPath = "./docs"
)

# 定义测试用例
$testCases = @(
    # OTLP版本测试
    @{ Input = "version: OTLP v1.9.0"; Expected = "version: OTLP v1.10.0"; Description = "YAML frontmatter版本" }
    @{ Input = "对标: OTLP v1.9.0"; Expected = "对标: OTLP v1.10.0"; Description = "对标声明" }
    @{ Input = "基于 OTLP v1.9.0"; Expected = "基于 OTLP v1.10.0"; Description = "基于声明" }
    @{ Input = "当前 OTLP v1.9.0"; Expected = "当前 OTLP v1.10.0"; Description = "当前声明" }
    @{ Input = "version: OTLP 1.9.0"; Expected = "version: OTLP 1.10.0"; Description = "无v前缀版本" }
    
    # Semantic Conventions测试
    @{ Input = "Semantic Conventions v1.38.0"; Expected = "Semantic Conventions v1.40.0"; Description = "SC v1.38.0" }
    @{ Input = "version: Semantic Conventions v1.39.0"; Expected = "version: Semantic Conventions v1.40.0"; Description = "SC frontmatter版本" }
    @{ Input = "Semantic Conventions v1.41.0.0"; Expected = "Semantic Conventions v1.40.0"; Description = "SC v1.41.0.0降级" }
    
    # Collector测试
    @{ Input = "Collector v0.117.0"; Expected = "Collector v0.121.0"; Description = "Collector v0.117.0" }
    @{ Input = "OpenTelemetry Collector v0.118.0"; Expected = "OpenTelemetry Collector v0.121.0"; Description = "Collector v0.118.0" }
    
    # 表格测试
    @{ Input = "| OTLP Protocol | v1.9.0 |"; Expected = "| OTLP Protocol | v1.10.0 |"; Description = "表格中的版本" }
)

# 替换规则（简化版）
$rules = @(
    @{
        Name = "OTLP v1.9.0"
        Pattern = '(?i)(version:\s*OTLP\s+v|对标[:：]\s*OTLP\s+v|基于[:：]?\s*OTLP\s+v|当前[:：]?\s*OTLP\s+v|最新[:：]?\s*OTLP\s+v|对齐[:：]?\s*OTLP\s+v|符合[:：]?\s*OTLP\s+v|支持[:：]?\s*OTLP\s+v)1\.9\.0'
        Replacement = "`${1}1.10.0"
    }
    @{
        Name = "OTLP 1.9.0"
        Pattern = '(?i)(version:\s*OTLP\s+|对标[:：]\s*OTLP\s+|基于[:：]?\s*OTLP\s+|当前[:：]?\s*OTLP\s+|最新[:：]?\s*OTLP\s+|对齐[:：]?\s*OTLP\s+|符合[:：]?\s*OTLP\s+)1\.9\.0'
        Replacement = "`${1}1.10.0"
    }
    @{
        Name = "Semantic Conventions v1.3x.0"
        Pattern = '(?i)(Semantic\s+Conventions\s+v|version:\s*Semantic\s+Conventions\s+v|对标[:：]\s*Semantic\s+Conventions\s+v|基于[:：]?\s*Semantic\s+Conventions\s+v)1\.3\d\.0'
        Replacement = "`${1}1.40.0"
    }
    @{
        Name = "Semantic Conventions v1.41.0.0"
        Pattern = '(?i)(Semantic\s+Conventions\s+v)1\.41\.0\.0'
        Replacement = "`${1}1.40.0"
    }
    @{
        Name = "Collector v0.11x.0"
        Pattern = '(?i)(Collector\s+v)0\.11\d\.0'
        Replacement = "`${1}0.121.0"
    }
    @{
        Name = "表格版本对齐"
        Pattern = '(?i)(\|\s*OTLP\s+Protocol\s*\|\s*v?)1\.9\.0(\s*\|)'
        Replacement = "`${1}1.10.0`${2}"
    }
)

Write-Host "========================================" -ForegroundColor Blue
Write-Host "  版本替换规则测试" -ForegroundColor Blue
Write-Host "========================================" -ForegroundColor Blue
Write-Host ""

$passed = 0
$failed = 0

foreach ($test in $testCases) {
    $result = $test.Input
    
    foreach ($rule in $rules) {
        $result = [regex]::Replace($result, $rule.Pattern, $rule.Replacement)
    }
    
    $isMatch = $result -eq $test.Expected
    
    if ($isMatch) {
        Write-Host "✅ PASS" -ForegroundColor Green -NoNewline
        $passed++
    } else {
        Write-Host "❌ FAIL" -ForegroundColor Red -NoNewline
        $failed++
    }
    
    Write-Host " - $($test.Description)"
    Write-Host "   输入:    $($test.Input)"
    Write-Host "   期望:    $($test.Expected)"
    Write-Host "   实际:    $result"
    Write-Host ""
}

Write-Host "========================================" -ForegroundColor Blue
Write-Host "  测试结果: $passed 通过, $failed 失败" -ForegroundColor $(if ($failed -eq 0) { "Green" } else { "Red" })
Write-Host "========================================" -ForegroundColor Blue

# 扫描实际文件中的匹配项
Write-Host ""
Write-Host "扫描实际文档中的版本声明..." -ForegroundColor Yellow

$patterns = @(
    'OTLP\s+v?1\.9\.0'
    'Semantic\s+Conventions\s+v1\.(3\d|41)\.0'
    'Collector\s+v0\.11\d\.0'
)

$docsPathResolved = Resolve-Path $DocsPath
$allMdFiles = Get-ChildItem -Path $docsPathResolved -Filter "*.md" -Recurse -File | Select-Object -First 20

foreach ($pattern in $patterns) {
    Write-Host ""
    Write-Host "模式: $pattern" -ForegroundColor Cyan
    
    foreach ($file in $allMdFiles) {
        $content = Get-Content -Path $file.FullName -Raw -ErrorAction SilentlyContinue
        $matches = [regex]::Matches($content, $pattern, [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
        
        if ($matches.Count -gt 0) {
            Write-Host "  $($file.Name): 找到 $($matches.Count) 处匹配"
            foreach ($match in $matches | Select-Object -First 3) {
                $context = $content.Substring([Math]::Max(0, $match.Index - 30), [Math]::Min(60, $content.Length - [Math]::Max(0, $match.Index - 30)))
                Write-Host "    ...$context..." -ForegroundColor DarkGray
            }
        }
    }
}
