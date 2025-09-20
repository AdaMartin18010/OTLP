# OpenTelemetry 文档质量检查脚本 (简化版)
# 检查文档格式一致性和基本问题

param(
    [string]$DocPath = "docs",
    [string]$OutputDir = "doc-quality-reports",
    [switch]$Verbose
)

# 创建输出目录
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
}

$Timestamp = Get-Date -Format "yyyy-MM-dd-HHmmss"
$LogFile = Join-Path $OutputDir "doc-quality-check-$Timestamp.log"
$ReportFile = Join-Path $OutputDir "doc-quality-report-$Timestamp.md"

# 日志函数
function Write-Log {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $LogMessage = "[$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')] [$Level] $Message"
    
    if ($Verbose -or $Level -eq "ERROR" -or $Level -eq "WARN") {
        Write-Host $LogMessage
    }
    
    Add-Content -Path $LogFile -Value $LogMessage
}

# 检查Markdown文件
function Test-MarkdownFile {
    param(
        [string]$FilePath
    )
    
    $Issues = @()
    $Content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $Lines = Get-Content -Path $FilePath -Encoding UTF8
    
    Write-Log "检查文件: $FilePath" "INFO"
    
    # 检查文件编码
    if ($Content -match "[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]") {
        $Issues += @{
            Type = "Encoding"
            Severity = "WARN"
            Message = "文件包含非UTF-8字符"
            Line = 0
        }
    }
    
    # 检查文件末尾空行
    if ($Content -notmatch "\n$") {
        $Issues += @{
            Type = "Formatting"
            Severity = "INFO"
            Message = "文件末尾缺少空行"
            Line = $Lines.Count
        }
    }
    
    # 检查标题格式
    for ($i = 0; $i -lt $Lines.Count; $i++) {
        $Line = $Lines[$i]
        
        # 检查标题格式
        if ($Line -match "^#+\s+") {
            $Level = ($Line -split "#").Count - 1
            
            # 检查标题层级
            if ($i -eq 0 -and $Level -ne 1) {
                $Issues += @{
                    Type = "Title"
                    Severity = "WARN"
                    Message = "文件应以一级标题开始"
                    Line = $i + 1
                }
            }
        }
        
        # 检查行长度
        if ($Line.Length -gt 120) {
            $Issues += @{
                Type = "LineLength"
                Severity = "INFO"
                Message = "行长度超过120字符: $($Line.Length)字符"
                Line = $i + 1
            }
        }
        
        # 检查尾随空格
        if ($Line -match '\s+$') {
            $Issues += @{
                Type = "Whitespace"
                Severity = "INFO"
                Message = "行尾有尾随空格"
                Line = $i + 1
            }
        }
    }
    
    return $Issues
}

# 生成质量报告
function New-QualityReport {
    param(
        [hashtable]$Results
    )
    
    Write-Log "生成文档质量报告..." "INFO"
    
    $Report = @"
# OpenTelemetry 文档质量检查报告

**检查时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**检查路径**: $DocPath

## 检查概览

| 文件 | 总问题数 | 错误 | 警告 | 信息 |
|------|----------|------|------|------|
"@

    $TotalIssues = 0
    $TotalErrors = 0
    $TotalWarnings = 0
    $TotalInfos = 0

    foreach ($File in $Results.Keys) {
        $FileIssues = $Results[$File]
        $ErrorCount = ($FileIssues | Where-Object { $_.Severity -eq "ERROR" }).Count
        $WarningCount = ($FileIssues | Where-Object { $_.Severity -eq "WARN" }).Count
        $InfoCount = ($FileIssues | Where-Object { $_.Severity -eq "INFO" }).Count
        $FileTotal = $FileIssues.Count

        $TotalIssues += $FileTotal
        $TotalErrors += $ErrorCount
        $TotalWarnings += $WarningCount
        $TotalInfos += $InfoCount

        $Report += "`n| $File | $FileTotal | $ErrorCount | $WarningCount | $InfoCount |"
    }

    $Report += @"

## 总体统计

- **总文件数**: $($Results.Keys.Count)
- **总问题数**: $TotalIssues
- **错误数**: $TotalErrors
- **警告数**: $TotalWarnings
- **信息数**: $TotalInfos

## 详细问题列表

"@

    foreach ($File in $Results.Keys) {
        $FileIssues = $Results[$File]
        if ($FileIssues.Count -gt 0) {
            $Report += @"

### $File

"@
            foreach ($Issue in $FileIssues) {
                $SeverityIcon = switch ($Issue.Severity) {
                    "ERROR" { "❌" }
                    "WARN" { "⚠️" }
                    "INFO" { "ℹ️" }
                    default { "📝" }
                }
                
                $Report += "`n$SeverityIcon **$($Issue.Type)** (行 $($Issue.Line)): $($Issue.Message)"
            }
        }
    }

    $Report += @"

## 质量评分

"@

    # 计算质量评分
    $MaxScore = 100
    $Deduction = $TotalErrors * 10 + $TotalWarnings * 5 + $TotalInfos * 1
    $Score = [Math]::Max(0, $MaxScore - $Deduction)

    $Report += @"
- **质量评分**: $Score/100
- **评分说明**: 
  - 错误: -10分/个
  - 警告: -5分/个
  - 信息: -1分/个

## 修复建议

### 高优先级修复
1. **修复所有错误**: 解决所有标记为ERROR的问题
2. **统一格式**: 统一标题格式、列表格式等
3. **优化结构**: 改善文档结构和标题层级

### 中优先级修复
1. **控制行长度**: 控制行长度在合理范围内
2. **清理格式**: 移除尾随空格等格式问题
3. **完善内容**: 确保内容完整性和准确性

---
*报告生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')*
*检查工具: OpenTelemetry 文档质量检查脚本*
"@

    Set-Content -Path $ReportFile -Value $Report -Encoding UTF8
    Write-Log "文档质量报告已生成: $ReportFile" "INFO"
    
    return $ReportFile
}

# 主函数
function Main {
    Write-Log "开始文档质量检查..." "INFO"
    Write-Log "检查路径: $DocPath" "INFO"
    Write-Log "输出目录: $OutputDir" "INFO"
    
    # 检查路径是否存在
    if (!(Test-Path $DocPath)) {
        Write-Log "检查路径不存在: $DocPath" "ERROR"
        exit 1
    }
    
    # 获取所有Markdown文件
    $MarkdownFiles = Get-ChildItem -Path $DocPath -Filter "*.md" -Recurse
    Write-Log "找到 $($MarkdownFiles.Count) 个Markdown文件" "INFO"
    
    $Results = @{}
    
    # 检查每个文件
    foreach ($File in $MarkdownFiles) {
        $RelativePath = $File.FullName.Replace((Get-Location).Path + "\", "").Replace("\", "/")
        
        $Issues = Test-MarkdownFile -FilePath $File.FullName
        $Results[$RelativePath] = $Issues
    }
    
    # 生成报告
    $ReportPath = New-QualityReport -Results $Results
    
    # 统计结果
    $TotalIssues = ($Results.Values | Measure-Object -Property Count -Sum).Sum
    $ErrorCount = ($Results.Values | ForEach-Object { $_ | Where-Object { $_.Severity -eq "ERROR" } } | Measure-Object).Count
    $WarningCount = ($Results.Values | ForEach-Object { $_ | Where-Object { $_.Severity -eq "WARN" } } | Measure-Object).Count
    $InfoCount = ($Results.Values | ForEach-Object { $_ | Where-Object { $_.Severity -eq "INFO" } } | Measure-Object).Count
    
    Write-Log "文档质量检查完成" "INFO"
    Write-Log "总问题数: $TotalIssues (错误: $ErrorCount, 警告: $WarningCount, 信息: $InfoCount)" "INFO"
    Write-Log "质量报告: $ReportPath" "INFO"
    
    exit 0
}

# 执行主函数
if ($MyInvocation.InvocationName -ne '.') {
    Main
}
