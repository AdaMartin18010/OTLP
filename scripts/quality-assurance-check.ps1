# OTLP 2025 质量保证检查脚本
# 综合质量检查：代码质量、文档质量、配置质量、安全质量

param(
    [string]$CheckType = "all",
    [switch]$Fix,
    [switch]$Export,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 质量检查结果
$QualityResults = @{
    StartTime = Get-Date
    CheckType = $CheckType
    Results = @{
        CodeQuality = @{}
        DocumentQuality = @{}
        ConfigQuality = @{}
        SecurityQuality = @{}
        PerformanceQuality = @{}
    }
    Summary = @{
        TotalChecks = 0
        PassedChecks = 0
        FailedChecks = 0
        Warnings = 0
    }
}

# 代码质量检查
function Test-CodeQuality {
    Write-ColorOutput "🔍 检查代码质量..." "Cyan"
    
    $codeResults = @{
        Language = @{}
        Overall = @{
            Score = 0
            Issues = @()
            Recommendations = @()
        }
    }
    
    # 检查 Rust 代码质量
    if (Test-Path "examples/minimal-rust/Cargo.toml") {
        Write-ColorOutput "  🦀 检查 Rust 代码质量..." "Yellow"
        try {
            Push-Location "examples/minimal-rust"
            
            # 运行 clippy 检查
            $clippyOutput = cargo clippy -- -D warnings 2>&1
            $clippyIssues = ($clippyOutput | Where-Object { $_ -match "warning|error" }).Count
            
            # 运行 fmt 检查
            $fmtOutput = cargo fmt -- --check 2>&1
            $fmtIssues = ($fmtOutput | Where-Object { $_ -match "Diff" }).Count
            
            # 运行测试
            $testOutput = cargo test 2>&1
            $testPassed = $testOutput -match "test result: ok"
            
            Pop-Location
            
            $rustScore = 100
            if ($clippyIssues -gt 0) { $rustScore -= $clippyIssues * 5 }
            if ($fmtIssues -gt 0) { $rustScore -= $fmtIssues * 2 }
            if (!$testPassed) { $rustScore -= 20 }
            
            $codeResults.Language.Rust = @{
                Score = [Math]::Max(0, $rustScore)
                ClippyIssues = $clippyIssues
                FormatIssues = $fmtIssues
                TestsPassed = $testPassed
                Output = $clippyOutput + $fmtOutput + $testOutput
            }
            
            Write-ColorOutput "  ✅ Rust 代码质量: $($codeResults.Language.Rust.Score)/100" "Green"
            
        } catch {
            Write-ColorOutput "  ❌ Rust 代码质量检查失败: $($_.Exception.Message)" "Red"
            $codeResults.Language.Rust = @{
                Score = 0
                Error = $_.Exception.Message
            }
        }
    }
    
    # 检查 Go 代码质量
    if (Test-Path "examples/minimal-go/go.mod") {
        Write-ColorOutput "  🐹 检查 Go 代码质量..." "Yellow"
        try {
            Push-Location "examples/minimal-go"
            
            # 运行 go vet
            $vetOutput = go vet ./... 2>&1
            $vetIssues = ($vetOutput | Where-Object { $_ -match "vet:" }).Count
            
            # 运行 go fmt 检查
            $fmtOutput = go fmt ./... 2>&1
            $fmtIssues = ($fmtOutput | Where-Object { $_ -match "diff" }).Count
            
            # 运行测试
            $testOutput = go test ./... 2>&1
            $testPassed = $testOutput -match "PASS"
            
            Pop-Location
            
            $goScore = 100
            if ($vetIssues -gt 0) { $goScore -= $vetIssues * 10 }
            if ($fmtIssues -gt 0) { $goScore -= $fmtIssues * 5 }
            if (!$testPassed) { $goScore -= 20 }
            
            $codeResults.Language.Go = @{
                Score = [Math]::Max(0, $goScore)
                VetIssues = $vetIssues
                FormatIssues = $fmtIssues
                TestsPassed = $testPassed
                Output = $vetOutput + $fmtOutput + $testOutput
            }
            
            Write-ColorOutput "  ✅ Go 代码质量: $($codeResults.Language.Go.Score)/100" "Green"
            
        } catch {
            Write-ColorOutput "  ❌ Go 代码质量检查失败: $($_.Exception.Message)" "Red"
            $codeResults.Language.Go = @{
                Score = 0
                Error = $_.Exception.Message
            }
        }
    }
    
    # 检查 Python 代码质量
    if (Test-Path "examples/minimal-python/main.py") {
        Write-ColorOutput "  🐍 检查 Python 代码质量..." "Yellow"
        try {
            Push-Location "examples/minimal-python"
            
            # 运行 flake8 检查
            $flake8Output = flake8 . 2>&1
            $flake8Issues = ($flake8Output | Where-Object { $_ -match ":" }).Count
            
            # 运行 black 检查
            $blackOutput = black --check . 2>&1
            $blackIssues = ($blackOutput | Where-Object { $_ -match "would reformat" }).Count
            
            # 运行测试
            $testOutput = python -m pytest 2>&1
            $testPassed = $testOutput -match "passed"
            
            Pop-Location
            
            $pythonScore = 100
            if ($flake8Issues -gt 0) { $pythonScore -= $flake8Issues * 3 }
            if ($blackIssues -gt 0) { $pythonScore -= $blackIssues * 2 }
            if (!$testPassed) { $pythonScore -= 20 }
            
            $codeResults.Language.Python = @{
                Score = [Math]::Max(0, $pythonScore)
                Flake8Issues = $flake8Issues
                BlackIssues = $blackIssues
                TestsPassed = $testPassed
                Output = $flake8Output + $blackOutput + $testOutput
            }
            
            Write-ColorOutput "  ✅ Python 代码质量: $($codeResults.Language.Python.Score)/100" "Green"
            
        } catch {
            Write-ColorOutput "  ❌ Python 代码质量检查失败: $($_.Exception.Message)" "Red"
            $codeResults.Language.Python = @{
                Score = 0
                Error = $_.Exception.Message
            }
        }
    }
    
    # 计算总体代码质量分数
    $totalScore = 0
    $languageCount = 0
    foreach ($lang in $codeResults.Language.Keys) {
        if ($codeResults.Language[$lang].Score -gt 0) {
            $totalScore += $codeResults.Language[$lang].Score
            $languageCount++
        }
    }
    
    if ($languageCount -gt 0) {
        $codeResults.Overall.Score = [Math]::Round($totalScore / $languageCount, 2)
    }
    
    $QualityResults.Results.CodeQuality = $codeResults
    $QualityResults.Summary.TotalChecks++
    if ($codeResults.Overall.Score -ge 80) {
        $QualityResults.Summary.PassedChecks++
    } else {
        $QualityResults.Summary.FailedChecks++
    }
}

# 文档质量检查
function Test-DocumentQuality {
    Write-ColorOutput "📚 检查文档质量..." "Cyan"
    
    $docResults = @{
        Files = @{}
        Overall = @{
            Score = 0
            Issues = @()
            Recommendations = @()
        }
    }
    
    # 检查 Markdown 文件
    $markdownFiles = Get-ChildItem -Path "." -Filter "*.md" -Recurse | Where-Object { 
        $_.FullName -notmatch "node_modules|target|\.git" 
    }
    
    $totalFiles = $markdownFiles.Count
    $passedFiles = 0
    $totalIssues = 0
    
    foreach ($file in $markdownFiles) {
        $fileIssues = @()
        
        try {
            $content = Get-Content $file.FullName -Raw -Encoding UTF8
            
            # 检查文件编码
            if ($content -match "[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]") {
                $fileIssues += "非UTF-8字符"
            }
            
            # 检查标题结构
            $headings = [regex]::Matches($content, '^#+\s+(.+)$', [System.Text.RegularExpressions.RegexOptions]::Multiline)
            if ($headings.Count -eq 0) {
                $fileIssues += "缺少标题"
            }
            
            # 检查空行
            if ($content -match '\n\n\n+') {
                $fileIssues += "多余空行"
            }
            
            # 检查行尾空格
            $lines = $content -split "`n"
            $trailingSpaces = 0
            for ($i = 0; $i -lt $lines.Length; $i++) {
                if ($lines[$i] -match '\s+$') {
                    $trailingSpaces++
                }
            }
            if ($trailingSpaces -gt 0) {
                $fileIssues += "$trailingSpaces 个行尾空格"
            }
            
            # 检查链接格式
            $links = [regex]::Matches($content, '\[([^\]]+)\]\(([^)]+)\)')
            $brokenLinks = 0
            foreach ($link in $links) {
                $url = $link.Groups[2].Value
                if ($url -match '^https?://' -and $url -notmatch '^https://[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}') {
                    $brokenLinks++
                }
            }
            if ($brokenLinks -gt 0) {
                $fileIssues += "$brokenLinks 个可疑链接"
            }
            
            # 计算文件分数
            $fileScore = 100
            $fileScore -= $fileIssues.Count * 10
            $fileScore = [Math]::Max(0, $fileScore)
            
            if ($fileScore -ge 80) {
                $passedFiles++
            }
            
            $totalIssues += $fileIssues.Count
            
            $docResults.Files[$file.Name] = @{
                Path = $file.FullName
                Score = $fileScore
                Issues = $fileIssues
            }
            
        } catch {
            $docResults.Files[$file.Name] = @{
                Path = $file.FullName
                Score = 0
                Error = $_.Exception.Message
            }
        }
    }
    
    # 计算总体文档质量分数
    if ($totalFiles -gt 0) {
        $docResults.Overall.Score = [Math]::Round(($passedFiles / $totalFiles) * 100, 2)
    }
    
    $QualityResults.Results.DocumentQuality = $docResults
    $QualityResults.Summary.TotalChecks++
    if ($docResults.Overall.Score -ge 80) {
        $QualityResults.Summary.PassedChecks++
    } else {
        $QualityResults.Summary.FailedChecks++
    }
    
    Write-ColorOutput "✅ 文档质量检查完成: $($docResults.Overall.Score)/100 ($passedFiles/$totalFiles 文件通过)" "Green"
}

# 配置质量检查
function Test-ConfigQuality {
    Write-ColorOutput "⚙️ 检查配置质量..." "Cyan"
    
    $configResults = @{
        Files = @{}
        Overall = @{
            Score = 0
            Issues = @()
            Recommendations = @()
        }
    }
    
    # 检查 YAML 配置文件
    $yamlFiles = Get-ChildItem -Path "." -Filter "*.yaml" -Recurse | Where-Object { 
        $_.FullName -notmatch "node_modules|target|\.git" 
    }
    
    $totalConfigs = $yamlFiles.Count
    $passedConfigs = 0
    
    foreach ($file in $yamlFiles) {
        $fileIssues = @()
        
        try {
            $content = Get-Content $file.FullName -Raw -Encoding UTF8
            
            # 检查 YAML 语法
            if ($content -match '^\s*-\s*$' -and $content -notmatch '^\s*-\s*[^:]') {
                $fileIssues += "空列表项"
            }
            
            # 检查缩进
            $lines = $content -split "`n"
            $indentIssues = 0
            for ($i = 0; $i -lt $lines.Length; $i++) {
                if ($lines[$i] -match '^\s*[^-\s]' -and $lines[$i] -notmatch '^\s*$') {
                    $indent = $lines[$i] -replace '^(\s*).*', '$1'
                    if ($indent.Length % 2 -ne 0) {
                        $indentIssues++
                    }
                }
            }
            if ($indentIssues -gt 0) {
                $fileIssues += "$indentIssues 个缩进问题"
            }
            
            # 检查必需字段
            if ($file.Name -like "*collector*") {
                if ($content -notmatch 'receivers:') {
                    $fileIssues += "缺少 receivers 配置"
                }
                if ($content -notmatch 'processors:') {
                    $fileIssues += "缺少 processors 配置"
                }
                if ($content -notmatch 'exporters:') {
                    $fileIssues += "缺少 exporters 配置"
                }
                if ($content -notmatch 'service:') {
                    $fileIssues += "缺少 service 配置"
                }
            }
            
            # 计算配置分数
            $configScore = 100
            $configScore -= $fileIssues.Count * 15
            $configScore = [Math]::Max(0, $configScore)
            
            if ($configScore -ge 80) {
                $passedConfigs++
            }
            
            $configResults.Files[$file.Name] = @{
                Path = $file.FullName
                Score = $configScore
                Issues = $fileIssues
            }
            
        } catch {
            $configResults.Files[$file.Name] = @{
                Path = $file.FullName
                Score = 0
                Error = $_.Exception.Message
            }
        }
    }
    
    # 计算总体配置质量分数
    if ($totalConfigs -gt 0) {
        $configResults.Overall.Score = [Math]::Round(($passedConfigs / $totalConfigs) * 100, 2)
    }
    
    $QualityResults.Results.ConfigQuality = $configResults
    $QualityResults.Summary.TotalChecks++
    if ($configResults.Overall.Score -ge 80) {
        $QualityResults.Summary.PassedChecks++
    } else {
        $QualityResults.Summary.FailedChecks++
    }
    
    Write-ColorOutput "✅ 配置质量检查完成: $($configResults.Overall.Score)/100 ($passedConfigs/$totalConfigs 配置通过)" "Green"
}

# 安全质量检查
function Test-SecurityQuality {
    Write-ColorOutput "🔒 检查安全质量..." "Cyan"
    
    $securityResults = @{
        Checks = @{}
        Overall = @{
            Score = 0
            Issues = @()
            Recommendations = @()
        }
    }
    
    $securityChecks = @{
        "敏感信息检查" = @{
            Pattern = '(password|secret|key|token|api_key)\s*[:=]\s*["\']?[^"\'\s]+["\']?'
            Severity = "High"
        }
        "硬编码凭据" = @{
            Pattern = '(Bearer\s+[A-Za-z0-9+/=]+|Basic\s+[A-Za-z0-9+/=]+)'
            Severity = "High"
        }
        "不安全的URL" = @{
            Pattern = 'http://[^"\'\s]+'
            Severity = "Medium"
        }
        "调试信息" = @{
            Pattern = '(console\.log|debug|trace|verbose)'
            Severity = "Low"
        }
    }
    
    $totalSecurityIssues = 0
    $highSeverityIssues = 0
    
    foreach ($checkName in $securityChecks.Keys) {
        $check = $securityChecks[$checkName]
        $pattern = $check.Pattern
        $severity = $check.Severity
        
        $issues = @()
        $files = Get-ChildItem -Path "." -Filter "*.*" -Recurse | Where-Object { 
            $_.Extension -match '\.(js|ts|py|go|rs|java|yaml|yml|json)$' -and
            $_.FullName -notmatch 'node_modules|target|\.git|vendor'
        }
        
        foreach ($file in $files) {
            try {
                $content = Get-Content $file.FullName -Raw -Encoding UTF8
                $matches = [regex]::Matches($content, $pattern, [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
                
                foreach ($match in $matches) {
                    $lineNumber = ($content.Substring(0, $match.Index) -split "`n").Count
                    $issues += @{
                        File = $file.FullName
                        Line = $lineNumber
                        Match = $match.Value
                        Severity = $severity
                    }
                    $totalSecurityIssues++
                    if ($severity -eq "High") {
                        $highSeverityIssues++
                    }
                }
            } catch {
                # 忽略无法读取的文件
            }
        }
        
        $securityResults.Checks[$checkName] = @{
            Severity = $severity
            Issues = $issues
            Count = $issues.Count
        }
    }
    
    # 计算安全质量分数
    $securityScore = 100
    $securityScore -= $highSeverityIssues * 20
    $securityScore -= ($totalSecurityIssues - $highSeverityIssues) * 5
    $securityScore = [Math]::Max(0, $securityScore)
    
    $securityResults.Overall.Score = $securityScore
    $securityResults.Overall.Issues = $totalSecurityIssues
    
    $QualityResults.Results.SecurityQuality = $securityResults
    $QualityResults.Summary.TotalChecks++
    if ($securityResults.Overall.Score -ge 80) {
        $QualityResults.Summary.PassedChecks++
    } else {
        $QualityResults.Summary.FailedChecks++
    }
    
    Write-ColorOutput "✅ 安全质量检查完成: $($securityResults.Overall.Score)/100 ($totalSecurityIssues 个问题)" "Green"
}

# 性能质量检查
function Test-PerformanceQuality {
    Write-ColorOutput "⚡ 检查性能质量..." "Cyan"
    
    $performanceResults = @{
        Checks = @{}
        Overall = @{
            Score = 0
            Issues = @()
            Recommendations = @()
        }
    }
    
    # 检查大文件
    $largeFiles = Get-ChildItem -Path "." -Recurse | Where-Object { 
        $_.Length -gt 1MB -and $_.FullName -notmatch 'node_modules|target|\.git|vendor'
    }
    
    $largeFileIssues = @()
    foreach ($file in $largeFiles) {
        $sizeMB = [Math]::Round($file.Length / 1MB, 2)
        $largeFileIssues += @{
            File = $file.FullName
            Size = "$sizeMB MB"
        }
    }
    
    # 检查重复代码
    $duplicateCodeIssues = @()
    $codeFiles = Get-ChildItem -Path "." -Filter "*.*" -Recurse | Where-Object { 
        $_.Extension -match '\.(js|ts|py|go|rs|java)$' -and
        $_.FullName -notmatch 'node_modules|target|\.git|vendor'
    }
    
    # 简化的重复代码检测
    $fileHashes = @{}
    foreach ($file in $codeFiles) {
        try {
            $content = Get-Content $file.FullName -Raw -Encoding UTF8
            $hash = $content.GetHashCode()
            if ($fileHashes.ContainsKey($hash)) {
                $duplicateCodeIssues += @{
                    File1 = $fileHashes[$hash]
                    File2 = $file.FullName
                }
            } else {
                $fileHashes[$hash] = $file.FullName
            }
        } catch {
            # 忽略无法读取的文件
        }
    }
    
    # 计算性能质量分数
    $performanceScore = 100
    $performanceScore -= $largeFileIssues.Count * 10
    $performanceScore -= $duplicateCodeIssues.Count * 15
    $performanceScore = [Math]::Max(0, $performanceScore)
    
    $performanceResults.Checks["大文件检查"] = @{
        Issues = $largeFileIssues
        Count = $largeFileIssues.Count
    }
    
    $performanceResults.Checks["重复代码检查"] = @{
        Issues = $duplicateCodeIssues
        Count = $duplicateCodeIssues.Count
    }
    
    $performanceResults.Overall.Score = $performanceScore
    
    $QualityResults.Results.PerformanceQuality = $performanceResults
    $QualityResults.Summary.TotalChecks++
    if ($performanceResults.Overall.Score -ge 80) {
        $QualityResults.Summary.PassedChecks++
    } else {
        $QualityResults.Summary.FailedChecks++
    }
    
    Write-ColorOutput "✅ 性能质量检查完成: $($performanceResults.Overall.Score)/100" "Green"
}

# 生成质量报告
function Generate-QualityReport {
    param([string]$OutputPath = "reports/quality-assurance-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成质量保证报告..." "Cyan"
    
    $report = @"
# OTLP 2025 质量保证检查报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**检查类型**: $CheckType
**总检查数**: $($QualityResults.Summary.TotalChecks)
**通过检查**: $($QualityResults.Summary.PassedChecks)
**失败检查**: $($QualityResults.Summary.FailedChecks)

## 检查结果概览

| 检查类型 | 分数 | 状态 |
|---------|------|------|
| 代码质量 | $($QualityResults.Results.CodeQuality.Overall.Score)/100 | $(if ($QualityResults.Results.CodeQuality.Overall.Score -ge 80) { "✅ 通过" } else { "❌ 失败" }) |
| 文档质量 | $($QualityResults.Results.DocumentQuality.Overall.Score)/100 | $(if ($QualityResults.Results.DocumentQuality.Overall.Score -ge 80) { "✅ 通过" } else { "❌ 失败" }) |
| 配置质量 | $($QualityResults.Results.ConfigQuality.Overall.Score)/100 | $(if ($QualityResults.Results.ConfigQuality.Overall.Score -ge 80) { "✅ 通过" } else { "❌ 失败" }) |
| 安全质量 | $($QualityResults.Results.SecurityQuality.Overall.Score)/100 | $(if ($QualityResults.Results.SecurityQuality.Overall.Score -ge 80) { "✅ 通过" } else { "❌ 失败" }) |
| 性能质量 | $($QualityResults.Results.PerformanceQuality.Overall.Score)/100 | $(if ($QualityResults.Results.PerformanceQuality.Overall.Score -ge 80) { "✅ 通过" } else { "❌ 失败" }) |

## 详细检查结果

### 代码质量检查

"@

    # 添加代码质量详情
    foreach ($lang in $QualityResults.Results.CodeQuality.Language.Keys) {
        $langResult = $QualityResults.Results.CodeQuality.Language[$lang]
        $report += "`n#### $lang`n`n"
        $report += "- **分数**: $($langResult.Score)/100`n"
        if ($langResult.Error) {
            $report += "- **错误**: $($langResult.Error)`n"
        } else {
            if ($langResult.ClippyIssues) { $report += "- **Clippy 问题**: $($langResult.ClippyIssues)`n" }
            if ($langResult.VetIssues) { $report += "- **Vet 问题**: $($langResult.VetIssues)`n" }
            if ($langResult.Flake8Issues) { $report += "- **Flake8 问题**: $($langResult.Flake8Issues)`n" }
            if ($langResult.FormatIssues) { $report += "- **格式问题**: $($langResult.FormatIssues)`n" }
            $report += "- **测试状态**: $(if ($langResult.TestsPassed) { "✅ 通过" } else { "❌ 失败" })`n"
        }
    }

    # 添加其他检查详情
    $report += @"

### 文档质量检查

- **总体分数**: $($QualityResults.Results.DocumentQuality.Overall.Score)/100
- **检查文件数**: $($QualityResults.Results.DocumentQuality.Files.Count)
- **主要问题**: 格式问题、链接问题、结构问题

### 配置质量检查

- **总体分数**: $($QualityResults.Results.ConfigQuality.Overall.Score)/100
- **检查配置数**: $($QualityResults.Results.ConfigQuality.Files.Count)
- **主要问题**: 语法问题、必需字段缺失

### 安全质量检查

- **总体分数**: $($QualityResults.Results.SecurityQuality.Overall.Score)/100
- **发现问题数**: $($QualityResults.Results.SecurityQuality.Overall.Issues)
- **主要问题**: 敏感信息泄露、硬编码凭据

### 性能质量检查

- **总体分数**: $($QualityResults.Results.PerformanceQuality.Overall.Score)/100
- **主要问题**: 大文件、重复代码

## 改进建议

"@

    # 生成改进建议
    if ($QualityResults.Results.CodeQuality.Overall.Score -lt 80) {
        $report += "1. **代码质量改进**: 修复代码质量问题，提高测试覆盖率`n"
    }
    if ($QualityResults.Results.DocumentQuality.Overall.Score -lt 80) {
        $report += "2. **文档质量改进**: 修复文档格式问题，完善文档结构`n"
    }
    if ($QualityResults.Results.ConfigQuality.Overall.Score -lt 80) {
        $report += "3. **配置质量改进**: 修复配置语法问题，完善必需字段`n"
    }
    if ($QualityResults.Results.SecurityQuality.Overall.Score -lt 80) {
        $report += "4. **安全质量改进**: 移除敏感信息，加强安全检查`n"
    }
    if ($QualityResults.Results.PerformanceQuality.Overall.Score -lt 80) {
        $report += "5. **性能质量改进**: 优化大文件，消除重复代码`n"
    }

    $report += @"

## 下一步行动

1. 修复发现的问题
2. 建立持续质量检查
3. 提高质量标准
4. 定期质量评估

---

*报告由 OTLP 2025 质量保证检查脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 质量保证报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 质量保证检查开始..." "Green"
    Write-ColorOutput ("=" * 60) "Gray"
    
    # 根据检查类型执行检查
    switch ($CheckType.ToLower()) {
        "code" { Test-CodeQuality }
        "document" { Test-DocumentQuality }
        "config" { Test-ConfigQuality }
        "security" { Test-SecurityQuality }
        "performance" { Test-PerformanceQuality }
        "all" {
            Test-CodeQuality
            Test-DocumentQuality
            Test-ConfigQuality
            Test-SecurityQuality
            Test-PerformanceQuality
        }
        default {
            Write-ColorOutput "❌ 不支持的检查类型: $CheckType" "Red"
            Write-ColorOutput "支持的检查类型: code, document, config, security, performance, all" "Yellow"
            exit 1
        }
    }
    
    # 生成报告
    if ($Export) {
        Generate-QualityReport
    }
    
    # 显示总结
    Write-ColorOutput ("=" * 60) "Gray"
    Write-ColorOutput "📊 质量检查总结:" "White"
    Write-ColorOutput "✅ 通过: $($QualityResults.Summary.PassedChecks)/$($QualityResults.Summary.TotalChecks)" "Green"
    Write-ColorOutput "❌ 失败: $($QualityResults.Summary.FailedChecks)/$($QualityResults.Summary.TotalChecks)" "Red"
    Write-ColorOutput "⏱️ 总耗时: $((Get-Date - $QualityResults.StartTime).TotalSeconds) 秒" "White"
    
    if ($QualityResults.Summary.PassedChecks -eq $QualityResults.Summary.TotalChecks) {
        Write-ColorOutput "🎉 所有质量检查通过!" "Green"
    } else {
        Write-ColorOutput "⚠️ 部分质量检查失败，请查看详细报告" "Yellow"
    }
    
    Write-ColorOutput "✅ 质量保证检查完成!" "Green"
}

# 执行主函数
Main
