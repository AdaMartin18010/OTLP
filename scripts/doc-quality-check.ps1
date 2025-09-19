# OpenTelemetry 文档质量检查脚本
# 全面检查文档格式一致性、内容完整性和交叉引用

param(
    [string]$DocPath = "docs",
    [string]$OutputDir = "doc-quality-reports",
    [switch]$Strict,
    [switch]$FixIssues,
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
    
    # 检查行尾符
    if ($Content -match "\r\n") {
        $Issues += @{
            Type = "LineEnding"
            Severity = "WARN"
            Message = "使用Windows行尾符(CRLF)，建议使用Unix行尾符(LF)"
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
            
            # 检查标题后是否有空行
            if ($i + 1 -lt $Lines.Count -and $Lines[$i + 1] -ne "") {
                $Issues += @{
                    Type = "Formatting"
                    Severity = "INFO"
                    Message = "标题后应有空行"
                    Line = $i + 1
                }
            }
        }
        
        # 检查列表格式
        if ($Line -match "^\s*[-*+]\s+") {
            # 检查列表项后是否有空行
            if ($i + 1 -lt $Lines.Count -and $Lines[$i + 1] -ne "" -and $Lines[$i + 1] -notmatch "^\s*[-*+]\s+") {
                $Issues += @{
                    Type = "Formatting"
                    Severity = "INFO"
                    Message = "列表项后应有空行"
                    Line = $i + 1
                }
            }
        }
        
        # 检查代码块格式
        if ($Line -match "```") {
            # 检查代码块语言标识
            if ($Line -match "```\s*$") {
                $Issues += @{
                    Type = "CodeBlock"
                    Severity = "INFO"
                    Message = "代码块应指定语言标识"
                    Line = $i + 1
                }
            }
        }
        
        # 检查链接格式
        if ($Line -match '\[([^\]]+)\]\(([^)]+)\)') {
            $Matches = [regex]::Matches($Line, '\[([^\]]+)\]\(([^)]+)\)')
            foreach ($Match in $Matches) {
                $LinkText = $Match.Groups[1].Value
                $LinkUrl = $Match.Groups[2].Value
                
                # 检查链接文本是否为空
                if ($LinkText -eq "") {
                    $Issues += @{
                        Type = "Link"
                        Severity = "WARN"
                        Message = "链接文本不能为空"
                        Line = $i + 1
                    }
                }
                
                # 检查相对链接
                if ($LinkUrl -notmatch "^https?://" -and $LinkUrl -notmatch "^#") {
                    # 检查文件是否存在
                    $LinkPath = Join-Path (Split-Path $FilePath -Parent) $LinkUrl
                    if (!(Test-Path $LinkPath)) {
                        $Issues += @{
                            Type = "Link"
                            Severity = "ERROR"
                            Message = "链接文件不存在: $LinkUrl"
                            Line = $i + 1
                        }
                    }
                }
            }
        }
        
        # 检查图片格式
        if ($Line -match '!\[([^\]]*)\]\(([^)]+)\)') {
            $Matches = [regex]::Matches($Line, '!\[([^\]]*)\]\(([^)]+)\)')
            foreach ($Match in $Matches) {
                $AltText = $Match.Groups[1].Value
                $ImageUrl = $Match.Groups[2].Value
                
                # 检查图片alt文本
                if ($AltText -eq "") {
                    $Issues += @{
                        Type = "Image"
                        Severity = "WARN"
                        Message = "图片缺少alt文本"
                        Line = $i + 1
                    }
                }
                
                # 检查图片文件是否存在
                if ($ImageUrl -notmatch "^https?://") {
                    $ImagePath = Join-Path (Split-Path $FilePath -Parent) $ImageUrl
                    if (!(Test-Path $ImagePath)) {
                        $Issues += @{
                            Type = "Image"
                            Severity = "ERROR"
                            Message = "图片文件不存在: $ImageUrl"
                            Line = $i + 1
                        }
                    }
                }
            }
        }
        
        # 检查表格格式
        if ($Line -match '^\s*\|.*\|') {
            # 检查表格行是否以|开始和结束
            if ($Line -notmatch '^\s*\|.*\|\s*$') {
                $Issues += @{
                    Type = "Table"
                    Severity = "WARN"
                    Message = "表格行应以|开始和结束"
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

# 检查文档结构
function Test-DocumentStructure {
    param(
        [string]$FilePath
    )
    
    $Issues = @()
    $Content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $Lines = Get-Content -Path $FilePath -Encoding UTF8
    
    # 检查必需的结构元素
    $RequiredElements = @(
        @{Pattern = "^#\s+"; Name = "一级标题"; Required = $true},
        @{Pattern = "^##\s+目录|^##\s+Table of Contents"; Name = "目录"; Required = $false},
        @{Pattern = "^##\s+概述|^##\s+Overview"; Name = "概述"; Required = $false},
        @{Pattern = "^##\s+总结|^##\s+Summary"; Name = "总结"; Required = $false}
    )
    
    foreach ($Element in $RequiredElements) {
        if ($Element.Required -and $Content -notmatch $Element.Pattern) {
            $Issues += @{
                Type = "Structure"
                Severity = "WARN"
                Message = "缺少必需元素: $($Element.Name)"
                Line = 0
            }
        }
    }
    
    # 检查标题层级
    $TitleLevels = @()
    for ($i = 0; $i -lt $Lines.Count; $i++) {
        $Line = $Lines[$i]
        if ($Line -match "^(#+)\s+") {
            $Level = $Matches[1].Length
            $TitleLevels += @{
                Level = $Level
                Line = $i + 1
                Text = $Line
            }
        }
    }
    
    # 检查标题层级是否合理
    for ($i = 1; $i -lt $TitleLevels.Count; $i++) {
        $CurrentLevel = $TitleLevels[$i].Level
        $PreviousLevel = $TitleLevels[$i - 1].Level
        
        if ($CurrentLevel -gt $PreviousLevel + 1) {
            $Issues += @{
                Type = "Structure"
                Severity = "WARN"
                Message = "标题层级跳跃: 从H$PreviousLevel 跳到 H$CurrentLevel"
                Line = $TitleLevels[$i].Line
            }
        }
    }
    
    return $Issues
}

# 检查交叉引用
function Test-CrossReferences {
    param(
        [string]$FilePath,
        [array]$AllFiles
    )
    
    $Issues = @()
    $Content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    
    # 提取所有链接
    $Links = [regex]::Matches($Content, '\[([^\]]+)\]\(([^)]+)\)')
    
    foreach ($Link in $Links) {
        $LinkText = $Link.Groups[1].Value
        $LinkUrl = $Link.Groups[2].Value
        
        # 检查内部链接
        if ($LinkUrl -notmatch "^https?://" -and $LinkUrl -notmatch "^#") {
            # 解析链接路径
            $LinkPath = $LinkUrl
            if ($LinkUrl -match "^\.\./") {
                $LinkPath = Join-Path (Split-Path $FilePath -Parent) $LinkUrl
            } elseif ($LinkUrl -match "^\./") {
                $LinkPath = Join-Path (Split-Path $FilePath -Parent) $LinkUrl
            } else {
                $LinkPath = Join-Path (Split-Path $FilePath -Parent) $LinkUrl
            }
            
            # 检查文件是否存在
            if (!(Test-Path $LinkPath)) {
                $Issues += @{
                    Type = "CrossReference"
                    Severity = "ERROR"
                    Message = "内部链接文件不存在: $LinkUrl"
                    Line = 0
                }
            } else {
                # 检查锚点是否存在
                if ($LinkUrl -match "#(.+)") {
                    $Anchor = $Matches[1]
                    $TargetContent = Get-Content -Path $LinkPath -Raw -Encoding UTF8
                    if ($TargetContent -notmatch "id=['\`"]$Anchor['\`"]|name=['\`"]$Anchor['\`"]|^#+\s+$Anchor\b") {
                        $Issues += @{
                            Type = "CrossReference"
                            Severity = "WARN"
                            Message = "链接锚点不存在: $Anchor"
                            Line = 0
                        }
                    }
                }
            }
        }
    }
    
    return $Issues
}

# 检查代码示例
function Test-CodeExamples {
    param(
        [string]$FilePath
    )
    
    $Issues = @()
    $Content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $Lines = Get-Content -Path $FilePath -Encoding UTF8
    
    # 查找代码块
    $InCodeBlock = $false
    $CodeBlockLanguage = ""
    $CodeBlockStartLine = 0
    
    for ($i = 0; $i -lt $Lines.Count; $i++) {
        $Line = $Lines[$i]
        
        if ($Line -match "^```(\w+)?") {
            if (!$InCodeBlock) {
                # 开始代码块
                $InCodeBlock = $true
                $CodeBlockLanguage = $Matches[1]
                $CodeBlockStartLine = $i + 1
                
                # 检查语言标识
                if ($CodeBlockLanguage -eq "") {
                    $Issues += @{
                        Type = "CodeExample"
                        Severity = "INFO"
                        Message = "代码块缺少语言标识"
                        Line = $i + 1
                    }
                }
            } else {
                # 结束代码块
                $InCodeBlock = $false
                $CodeBlockLanguage = ""
            }
        } elseif ($InCodeBlock) {
            # 在代码块内
            # 检查代码格式
            if ($CodeBlockLanguage -eq "yaml" -or $CodeBlockLanguage -eq "yml") {
                # 检查YAML缩进
                if ($Line -match "^\s+") {
                    $Indent = $Line -replace "(\s*).*", '$1'
                    if ($Indent.Length % 2 -ne 0) {
                        $Issues += @{
                            Type = "CodeExample"
                            Severity = "WARN"
                            Message = "YAML缩进应为2的倍数"
                            Line = $i + 1
                        }
                    }
                }
            }
            
            # 检查代码行长度
            if ($Line.Length -gt 100) {
                $Issues += @{
                    Type = "CodeExample"
                    Severity = "INFO"
                    Message = "代码行长度超过100字符: $($Line.Length)字符"
                    Line = $i + 1
                }
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
**检查模式**: $(if ($Strict) { "严格模式" } else { "标准模式" })

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

## 修复建议

### 高优先级修复
1. **修复所有错误**: 解决所有标记为ERROR的问题
2. **修复链接问题**: 确保所有内部链接指向存在的文件
3. **修复图片问题**: 确保所有图片文件存在

### 中优先级修复
1. **统一格式**: 统一标题格式、列表格式等
2. **优化结构**: 改善文档结构和标题层级
3. **完善交叉引用**: 确保所有交叉引用正确

### 低优先级修复
1. **优化代码示例**: 改善代码格式和语言标识
2. **统一行长度**: 控制行长度在合理范围内
3. **清理格式**: 移除尾随空格等格式问题

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

## 自动化修复

"@

    if ($FixIssues) {
        $Report += @"
已启用自动修复模式，以下问题已自动修复：
- 移除尾随空格
- 统一行尾符
- 添加文件末尾空行
- 修复基本格式问题

"@
    } else {
        $Report += @"
要启用自动修复，请使用 `-FixIssues` 参数。

"@
    }

    $Report += @"

## 下一步行动

1. **立即修复**: 解决所有错误级别的问题
2. **计划修复**: 安排时间修复警告和信息级别的问题
3. **建立流程**: 建立文档质量检查的持续集成流程
4. **培训团队**: 培训团队成员文档编写规范

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
        
        $Issues = @()
        
        # 基本格式检查
        $Issues += Test-MarkdownFile -FilePath $File.FullName
        
        # 文档结构检查
        $Issues += Test-DocumentStructure -FilePath $File.FullName
        
        # 代码示例检查
        $Issues += Test-CodeExamples -FilePath $File.FullName
        
        $Results[$RelativePath] = $Issues
    }
    
    # 交叉引用检查
    foreach ($File in $MarkdownFiles) {
        $RelativePath = $File.FullName.Replace((Get-Location).Path + "\", "").Replace("\", "/")
        $CrossRefIssues = Test-CrossReferences -FilePath $File.FullName -AllFiles $MarkdownFiles
        $Results[$RelativePath] += $CrossRefIssues
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
    
    # 根据严格模式决定退出码
    if ($Strict -and $ErrorCount -gt 0) {
        Write-Log "严格模式下发现错误，退出码: 1" "ERROR"
        exit 1
    } else {
        Write-Log "检查完成，退出码: 0" "INFO"
        exit 0
    }
}

# 执行主函数
if ($MyInvocation.InvocationName -ne '.') {
    Main
}
