#Requires -Version 5.1
<#
.SYNOPSIS
    批量更新docs目录下Markdown文件中的版本信息。

.DESCRIPTION
    此脚本用于批量更新OTLP项目文档中的版本声明，包括：
    - OTLP协议规范版本
    - OpenTelemetry Specification版本
    - Semantic Conventions版本
    - Collector版本
    
    脚本会智能识别并跳过：
    - 版本更新日志文件
    - 学术引用和参考文献
    - 历史记录中的版本信息

.PARAMETER TargetVersionOTLP
    OTLP协议规范目标版本，默认为 "1.10.0"

.PARAMETER TargetVersionSpec
    OpenTelemetry Specification目标版本，默认为 "1.55.0"

.PARAMETER TargetVersionSemConv
    Semantic Conventions目标版本，默认为 "1.40.0"

.PARAMETER TargetVersionCollector
    Collector目标版本，默认为 "0.121.0"

.PARAMETER DocsPath
    文档目录路径，默认为 "./docs"

.PARAMETER TestMode
    测试模式，只显示将要修改的内容而不实际修改

.PARAMETER CreateBackup
    是否创建备份文件

.PARAMETER BackupSuffix
    备份文件后缀，默认为 ".bak"

.EXAMPLE
    .\Update-DocsVersion.ps1
    执行版本更新，使用默认目标版本

.EXAMPLE
    .\Update-DocsVersion.ps1 -TestMode
    测试模式，预览将要修改的内容

.EXAMPLE
    .\Update-DocsVersion.ps1 -CreateBackup -BackupSuffix ".backup"
    执行更新并创建备份文件

.NOTES
    作者: OTLP项目团队
    日期: 2026-03-17
    版本: 1.0.0
#>

[CmdletBinding(SupportsShouldProcess = $true)]
param(
    [string]$TargetVersionOTLP = "1.10.0",
    
    [string]$TargetVersionSpec = "1.55.0",
    
    [string]$TargetVersionSemConv = "1.40.0",
    
    [string]$TargetVersionCollector = "0.121.0",
    
    [string]$DocsPath = "./docs",
    
    [switch]$TestMode,
    
    [switch]$CreateBackup,
    
    [string]$BackupSuffix = ".bak"
)

#region Configuration

# 排除的文件模式（正则表达式）
$ExcludeFilePatterns = @(
    '版本更新.*\.md$',           # 版本更新说明文件
    '版本更新日志.*\.md$',       # 版本更新日志
    '变更日志.*\.md$',           # 变更日志
    'CHANGELOG.*\.md$',          # 英文变更日志
    '更新说明.*\.md$',           # 更新说明
    '.*_v\d+\.\d+_to_v\d+\.\d+\.md$',  # 版本对比日志
    'academic[\\/].*\.md$',      # 学术目录下的文件
    '参考文献.*\.md$',           # 参考文献
    'Bibliography.*\.md$'        # 英文参考文献
)

# 排除的目录
$ExcludeDirectories = @(
    'academic',
    '参考文献',
    'bibliography'
)

#endregion

#region Helper Functions

function Test-ShouldExcludeFile {
    <#
    .SYNOPSIS
        检查文件是否应该被排除
    #>
    param([string]$FilePath)
    
    $fileName = [System.IO.Path]::GetFileName($FilePath)
    $relativePath = $FilePath -replace [regex]::Escape((Resolve-Path $DocsPath).Path), ''
    
    # 检查排除模式
    foreach ($pattern in $ExcludeFilePatterns) {
        if ($fileName -match $pattern -or $relativePath -match $pattern) {
            return $true
        }
    }
    
    # 检查排除目录
    foreach ($dir in $ExcludeDirectories) {
        if ($relativePath -match "[\\/]$dir[\\/]" -or $relativePath -match "^[\\/]?$dir[\\/]") {
            return $true
        }
    }
    
    return $false
}

function Get-VersionReplacementRules {
    <#
    .SYNOPSIS
        获取版本替换规则
        
    .DESCRIPTION
        定义各种版本声明的正则替换规则
        只匹配"当前"、"最新"、"基于"等声明，不匹配历史记录
    #>
    param(
        [string]$OTLPVersion,
        [string]$SpecVersion,
        [string]$SemConvVersion,
        [string]$CollectorVersion
    )
    
    $rules = @()
    
    # 规则1: OTLP v1.9.0 → OTLP v1.10.0 (在版本声明上下文中)
    # 匹配: version: OTLP v1.9.0, 对标: OTLP v1.9.0, 基于 OTLP v1.9.0 等
    $rules += @{
        Name = "OTLP v1.9.0"
        Pattern = '(?i)(version:\s*OTLP\s+v|对标[:：]\s*OTLP\s+v|基于[:：]?\s*OTLP\s+v|当前[:：]?\s*OTLP\s+v|最新[:：]?\s*OTLP\s+v|对齐[:：]?\s*OTLP\s+v|符合[:：]?\s*OTLP\s+v|支持[:：]?\s*OTLP\s+v)1\.9\.0'
        Replacement = "`${1}$OTLPVersion"
        Description = "OTLP v1.9.0 → OTLP v$OTLPVersion"
    }
    
    # 规则2: OTLP 1.9.0 (无v前缀)
    $rules += @{
        Name = "OTLP 1.9.0"
        Pattern = '(?i)(version:\s*OTLP\s+|对标[:：]\s*OTLP\s+|基于[:：]?\s*OTLP\s+|当前[:：]?\s*OTLP\s+|最新[:：]?\s*OTLP\s+|对齐[:：]?\s*OTLP\s+|符合[:：]?\s*OTLP\s+)1\.9\.0'
        Replacement = "`${1}$OTLPVersion"
        Description = "OTLP 1.9.0 → OTLP $OTLPVersion"
    }
    
    # 规则3: OTLP Protocol v1.9.0
    $rules += @{
        Name = "OTLP Protocol v1.9.0"
        Pattern = '(?i)(OTLP\s+Protocol\s+v)1\.9\.0'
        Replacement = "`${1}$OTLPVersion"
        Description = "OTLP Protocol v1.9.0 → OTLP Protocol v$OTLPVersion"
    }
    
    # 规则4: Semantic Conventions v1.3x.0 → v1.40.0 (在版本声明中)
    # 匹配 v1.30.0 到 v1.39.0
    $rules += @{
        Name = "Semantic Conventions v1.3x.0"
        Pattern = '(?i)(Semantic\s+Conventions\s+v|version:\s*Semantic\s+Conventions\s+v|对标[:：]\s*Semantic\s+Conventions\s+v|基于[:：]?\s*Semantic\s+Conventions\s+v)1\.3\d\.0'
        Replacement = "`${1}$SemConvVersion"
        Description = "Semantic Conventions v1.3x.0 → Semantic Conventions v$SemConvVersion"
    }
    
    # 规则5: Semantic Conventions v1.41.0.0 → v1.40.0 (降级到稳定版本)
    $rules += @{
        Name = "Semantic Conventions v1.41.0.0"
        Pattern = '(?i)(Semantic\s+Conventions\s+v)1\.41\.0\.0'
        Replacement = "`${1}$SemConvVersion"
        Description = "Semantic Conventions v1.41.0.0 → Semantic Conventions v$SemConvVersion"
    }
    
    # 规则6: Collector v0.11x.0 → v0.121.0
    # 匹配 v0.110.0 到 v0.119.0
    $rules += @{
        Name = "Collector v0.11x.0"
        Pattern = '(?i)(Collector\s+v)0\.11\d\.0'
        Replacement = "`${1}$CollectorVersion"
        Description = "Collector v0.11x.0 → Collector v$CollectorVersion"
    }
    
    # 规则7: Collector v0.117.0 → v0.121.0 (特定版本)
    $rules += @{
        Name = "Collector v0.117.0"
        Pattern = '(?i)(Collector\s+v)0\.117\.0'
        Replacement = "`${1}$CollectorVersion"
        Description = "Collector v0.117.0 → Collector v$CollectorVersion"
    }
    
    # 规则8: OpenTelemetry Specification v1.5x.0 → v1.55.0
    # 匹配 v1.50.0 到 v1.54.0
    $rules += @{
        Name = "OpenTelemetry Specification v1.5x.0"
        Pattern = '(?i)(OpenTelemetry\s+Specification\s+v)1\.5[0-4]\.0'
        Replacement = "`${1}$SpecVersion"
        Description = "OpenTelemetry Specification v1.5x.0 → OpenTelemetry Specification v$SpecVersion"
    }
    
    # 规则9: 表格中的版本对齐状态 (项目版本列)
    $rules += @{
        Name = "表格版本对齐"
        Pattern = '(?i)(\|\s*\*\*OTLP\s+Protocol\*\*\s*\|\s*v?)1\.9\.0(\s*\|)'
        Replacement = "`${1}$OTLPVersion`${2}"
        Description = "表格中OTLP版本更新"
    }
    
    # 规则10: YAML frontmatter中纯版本号
    $rules += @{
        Name = "YAML版本"
        Pattern = '(?m)^version:\s*OTLP\s+v1\.9\.0$'
        Replacement = "version: OTLP v$OTLPVersion"
        Description = "YAML frontmatter版本更新"
    }
    
    return $rules
}

function Invoke-VersionReplacement {
    <#
    .SYNOPSIS
        对单个文件执行版本替换
    #>
    param(
        [string]$FilePath,
        [array]$Rules,
        [switch]$TestMode
    )
    
    $content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $originalContent = $content
    $modifications = @()
    $wasModified = $false
    
    foreach ($rule in $Rules) {
        $matches = [regex]::Matches($content, $rule.Pattern)
        
        if ($matches.Count -gt 0) {
            $newContent = [regex]::Replace($content, $rule.Pattern, $rule.Replacement)
            
            if ($newContent -ne $content) {
                foreach ($match in $matches) {
                    $lineNumber = ($originalContent.Substring(0, $match.Index) -split "`r?`n").Count
                    $modifications += [PSCustomObject]@{
                        Rule = $rule.Name
                        Description = $rule.Description
                        LineNumber = $lineNumber
                        Original = $match.Value
                        Replacement = [regex]::Replace($match.Value, $rule.Pattern, $rule.Replacement)
                    }
                }
                $content = $newContent
                $wasModified = $true
            }
        }
    }
    
    if ($wasModified) {
        if (-not $TestMode) {
            Set-Content -Path $FilePath -Value $content -Encoding UTF8 -NoNewline
        }
    }
    
    return @{
        WasModified = $wasModified
        Modifications = $modifications
        NewContent = if ($TestMode) { $content } else { $null }
    }
}

function Format-ModificationOutput {
    <#
    .SYNOPSIS
        格式化输出修改信息
    #>
    param(
        [string]$FilePath,
        [array]$Modifications
    )
    
    Write-Host "  文件: " -NoNewline
    Write-Host $FilePath -ForegroundColor Cyan
    
    foreach ($mod in $Modifications) {
        Write-Host "    行 $($mod.LineNumber): " -NoNewline -ForegroundColor Yellow
        Write-Host $mod.Description
        Write-Host "      原内容: " -NoNewline -ForegroundColor DarkGray
        Write-Host $mod.Original -ForegroundColor Red
        Write-Host "      新内容: " -NoNewline -ForegroundColor DarkGray
        Write-Host $mod.Replacement -ForegroundColor Green
    }
    Write-Host ""
}

#endregion

#region Main Script

# 显示脚本信息
Write-Host "========================================" -ForegroundColor Blue
Write-Host "  OTLP文档版本批量更新工具" -ForegroundColor Blue
Write-Host "========================================" -ForegroundColor Blue
Write-Host ""

if ($TestMode) {
    Write-Host "【测试模式】只预览修改，不实际执行" -ForegroundColor Magenta
    Write-Host ""
}

Write-Host "目标版本:" -ForegroundColor Green
Write-Host "  OTLP Protocol:        v$TargetVersionOTLP"
Write-Host "  OpenTelemetry Spec:   v$TargetVersionSpec"
Write-Host "  Semantic Conventions: v$TargetVersionSemConv"
Write-Host "  Collector:            v$TargetVersionCollector"
Write-Host ""

# 验证文档目录
if (-not (Test-Path $DocsPath)) {
    Write-Error "文档目录不存在: $DocsPath"
    exit 1
}

# 获取所有Markdown文件
$docsPathResolved = Resolve-Path $DocsPath
$allMdFiles = Get-ChildItem -Path $docsPathResolved -Filter "*.md" -Recurse -File

Write-Host "扫描到 $($allMdFiles.Count) 个Markdown文件" -ForegroundColor DarkGray

# 过滤掉排除的文件
$filesToProcess = $allMdFiles | Where-Object { -not (Test-ShouldExcludeFile -FilePath $_.FullName) }

Write-Host "将处理 $($filesToProcess.Count) 个文件 (已排除 $($allMdFiles.Count - $filesToProcess.Count) 个)" -ForegroundColor DarkGray
Write-Host ""

# 获取替换规则
$replacementRules = Get-VersionReplacementRules `
    -OTLPVersion $TargetVersionOTLP `
    -SpecVersion $TargetVersionSpec `
    -SemConvVersion $TargetVersionSemConv `
    -CollectorVersion $TargetVersionCollector

Write-Host "替换规则:" -ForegroundColor Green
foreach ($rule in $replacementRules) {
    Write-Host "  - $($rule.Description)"
}
Write-Host ""

# 统计
$stats = @{
    Processed = 0
    Modified = 0
    Skipped = 0
    BackupsCreated = 0
    Errors = 0
}

# 处理每个文件
foreach ($file in $filesToProcess) {
    $stats.Processed++
    
    Write-Progress -Activity "更新文档版本" -Status $file.Name -PercentComplete (($stats.Processed / $filesToProcess.Count) * 100)
    
    try {
        # 创建备份
        if ($CreateBackup -and -not $TestMode) {
            $backupPath = $file.FullName + $BackupSuffix
            Copy-Item -Path $file.FullName -Destination $backupPath -Force
            $stats.BackupsCreated++
        }
        
        # 执行替换
        $result = Invoke-VersionReplacement -FilePath $file.FullName -Rules $replacementRules -TestMode:$TestMode
        
        if ($result.WasModified) {
            $stats.Modified++
            Format-ModificationOutput -FilePath $file.FullName -Modifications $result.Modifications
        }
    }
    catch {
        Write-Error "处理文件时出错: $($file.FullName) - $($_.Exception.Message)"
        $stats.Errors++
    }
}

Write-Progress -Activity "更新文档版本" -Completed

# 显示统计
Write-Host "========================================" -ForegroundColor Blue
Write-Host "  处理完成" -ForegroundColor Blue
Write-Host "========================================" -ForegroundColor Blue
Write-Host ""
Write-Host "统计信息:" -ForegroundColor Green
Write-Host "  处理文件数:  $($stats.Processed)"
Write-Host "  修改文件数:  $($stats.Modified)" -ForegroundColor $(if ($stats.Modified -gt 0) { "Green" } else { "Gray" })
Write-Host "  跳过文件数:  $($stats.Skipped)"
if ($CreateBackup) {
    Write-Host "  创建备份数:  $($stats.BackupsCreated)"
}
if ($stats.Errors -gt 0) {
    Write-Host "  错误数:      $($stats.Errors)" -ForegroundColor Red
}

if ($TestMode) {
    Write-Host ""
    Write-Host "【测试模式完成】未执行实际修改" -ForegroundColor Magenta
    Write-Host "要执行实际更新，请运行: .\Update-DocsVersion.ps1" -ForegroundColor Yellow
}

#endregion
