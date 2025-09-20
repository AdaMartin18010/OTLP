# OpenTelemetry 版本检查自动化脚本
# 用于检查官方版本更新并通知项目维护者

param(
    [string]$ConfigPath = "version-check-config.json",
    [switch]$DryRun,
    [switch]$Verbose
)

# 配置默认值
$DefaultConfig = @{
    "check_interval_hours" = 24
    "notification_channels" = @("email", "slack")
    "monitored_components" = @{
        "specification" = "https://api.github.com/repos/open-telemetry/opentelemetry-specification/releases/latest"
        "collector" = "https://api.github.com/repos/open-telemetry/opentelemetry-collector/releases/latest"
        "go_sdk" = "https://api.github.com/repos/open-telemetry/opentelemetry-go/releases/latest"
        "python_sdk" = "https://api.github.com/repos/open-telemetry/opentelemetry-python/releases/latest"
        "rust_sdk" = "https://api.github.com/repos/open-telemetry/opentelemetry-rust/releases/latest"
        "java_sdk" = "https://api.github.com/repos/open-telemetry/opentelemetry-java/releases/latest"
        "javascript_sdk" = "https://api.github.com/repos/open-telemetry/opentelemetry-js/releases/latest"
    }
    "current_versions" = @{
        "specification" = "1.25.0"
        "collector" = "0.91.0"
        "go_sdk" = "1.19.0"
        "python_sdk" = "1.20.0"
        "rust_sdk" = "0.24.0"
        "java_sdk" = "1.32.0"
        "javascript_sdk" = "1.15.0"
    }
    "notification_settings" = @{
        "email" = @{
            "enabled" = $false
            "recipients" = @("maintainer@example.com")
            "smtp_server" = "smtp.example.com"
        }
        "slack" = @{
            "enabled" = $false
            "webhook_url" = "https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK"
            "channel" = "#opentelemetry-updates"
        }
    }
}

# 日志函数
function Write-Log {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $LogMessage = "[$Timestamp] [$Level] $Message"
    
    if ($Verbose -or $Level -eq "ERROR" -or $Level -eq "WARN") {
        Write-Host $LogMessage
    }
    
    # 写入日志文件
    $LogFile = "logs/version-check-$(Get-Date -Format 'yyyy-MM-dd').log"
    $LogDir = Split-Path $LogFile -Parent
    if (!(Test-Path $LogDir)) {
        New-Item -ItemType Directory -Path $LogDir -Force | Out-Null
    }
    Add-Content -Path $LogFile -Value $LogMessage
}

# 获取最新版本信息
function Get-LatestVersion {
    param(
        [string]$Component,
        [string]$ApiUrl
    )
    
    try {
        Write-Log "检查 $Component 的最新版本..." "INFO"
        
        $Headers = @{
            "Accept" = "application/vnd.github.v3+json"
            "User-Agent" = "OpenTelemetry-Version-Checker/1.0"
        }
        
        $Response = Invoke-RestMethod -Uri $ApiUrl -Headers $Headers -TimeoutSec 30
        
        if ($Response.tag_name) {
            $Version = $Response.tag_name -replace '^v', ''
            Write-Log "$Component 最新版本: $Version" "INFO"
            return @{
                "version" = $Version
                "published_at" = $Response.published_at
                "html_url" = $Response.html_url
                "body" = $Response.body
            }
        } else {
            Write-Log "无法获取 $Component 版本信息" "WARN"
            return $null
        }
    }
    catch {
        Write-Log "获取 $Component 版本信息失败: $($_.Exception.Message)" "ERROR"
        return $null
    }
}

# 比较版本号
function Compare-Versions {
    param(
        [string]$CurrentVersion,
        [string]$LatestVersion
    )
    
    try {
        $Current = [Version]$CurrentVersion
        $Latest = [Version]$LatestVersion
        
        if ($Latest -gt $Current) {
            return "newer"
        } elseif ($Latest -eq $Current) {
            return "same"
        } else {
            return "older"
        }
    }
    catch {
        Write-Log "版本比较失败: $($_.Exception.Message)" "ERROR"
        return "unknown"
    }
}

# 发送通知
function Send-Notification {
    param(
        [string]$Component,
        [string]$CurrentVersion,
        [string]$LatestVersion,
        [string]$ReleaseUrl,
        [hashtable]$Config
    )
    
    $Message = @"
🚀 OpenTelemetry 版本更新通知

组件: $Component
当前版本: $CurrentVersion
最新版本: $LatestVersion
发布页面: $ReleaseUrl

请及时更新项目文档和配置。
"@

    # 发送邮件通知
    if ($Config.notification_settings.email.enabled) {
        try {
            Send-MailMessage -To $Config.notification_settings.email.recipients -Subject "OpenTelemetry 版本更新: $Component" -Body $Message -SmtpServer $Config.notification_settings.email.smtp_server
            Write-Log "邮件通知已发送" "INFO"
        }
        catch {
            Write-Log "邮件通知发送失败: $($_.Exception.Message)" "ERROR"
        }
    }
    
    # 发送Slack通知
    if ($Config.notification_settings.slack.enabled) {
        try {
            $SlackMessage = @{
                text = $Message
                channel = $Config.notification_settings.slack.channel
            } | ConvertTo-Json
            
            Invoke-RestMethod -Uri $Config.notification_settings.slack.webhook_url -Method Post -Body $SlackMessage -ContentType "application/json"
            Write-Log "Slack通知已发送" "INFO"
        }
        catch {
            Write-Log "Slack通知发送失败: $($_.Exception.Message)" "ERROR"
        }
    }
}

# 更新项目版本信息
function Update-ProjectVersions {
    param(
        [hashtable]$Updates,
        [string]$ConfigPath
    )
    
    try {
        $Config = Get-Content $ConfigPath | ConvertFrom-Json | ConvertTo-Hashtable
        
        foreach ($Component in $Updates.Keys) {
            $Config.current_versions.$Component = $Updates[$Component]
            Write-Log "更新 $Component 版本为 $($Updates[$Component])" "INFO"
        }
        
        $Config | ConvertTo-Json -Depth 10 | Set-Content $ConfigPath
        Write-Log "项目版本信息已更新" "INFO"
    }
    catch {
        Write-Log "更新项目版本信息失败: $($_.Exception.Message)" "ERROR"
    }
}

# 生成更新报告
function Generate-UpdateReport {
    param(
        [hashtable]$UpdateResults
    )
    
    $ReportPath = "reports/version-check-report-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md"
    $ReportDir = Split-Path $ReportPath -Parent
    if (!(Test-Path $ReportDir)) {
        New-Item -ItemType Directory -Path $ReportDir -Force | Out-Null
    }
    
    $Report = @"
# OpenTelemetry 版本检查报告

**检查时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**检查者**: 自动化脚本

## 检查结果

| 组件 | 当前版本 | 最新版本 | 状态 | 更新建议 |
|------|----------|----------|------|----------|
"@

    foreach ($Component in $UpdateResults.Keys) {
        $Result = $UpdateResults[$Component]
        $Status = switch ($Result.status) {
            "newer" { "🆕 有新版本" }
            "same" { "✅ 已是最新" }
            "older" { "⚠️ 版本异常" }
            default { "❓ 检查失败" }
        }
        
        $Recommendation = switch ($Result.status) {
            "newer" { "建议更新到 $($Result.latest_version)" }
            "same" { "无需更新" }
            "older" { "需要调查版本异常" }
            default { "需要手动检查" }
        }
        
        $Report += "`n| $Component | $($Result.current_version) | $($Result.latest_version) | $Status | $Recommendation |"
    }
    
    $Report += @"

## 更新建议

### 高优先级更新
- 检查规范更新是否影响项目文档
- 验证SDK更新是否兼容现有示例
- 更新Collector配置以支持新功能

### 文档更新
- 更新版本号引用
- 检查API变更
- 更新最佳实践建议

### 测试验证
- 运行集成测试
- 验证配置兼容性
- 检查性能影响

## 下一步行动

1. 审查更新内容
2. 更新项目文档
3. 测试新版本兼容性
4. 部署更新

---
*报告生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')*
"@

    Set-Content -Path $ReportPath -Value $Report
    Write-Log "更新报告已生成: $ReportPath" "INFO"
    
    return $ReportPath
}

# 主函数
function Main {
    Write-Log "开始OpenTelemetry版本检查..." "INFO"
    
    # 加载配置
    if (Test-Path $ConfigPath) {
        $Config = Get-Content $ConfigPath | ConvertFrom-Json | ConvertTo-Hashtable
    } else {
        Write-Log "配置文件不存在，使用默认配置" "WARN"
        $Config = $DefaultConfig
        $DefaultConfig | ConvertTo-Json -Depth 10 | Set-Content $ConfigPath
    }
    
    $UpdateResults = @{}
    $Updates = @{}
    
    # 检查每个组件
    foreach ($Component in $Config.monitored_components.Keys) {
        $ApiUrl = $Config.monitored_components[$Component]
        $CurrentVersion = $Config.current_versions[$Component]
        
        $LatestInfo = Get-LatestVersion -Component $Component -ApiUrl $ApiUrl
        
        if ($LatestInfo) {
            $Comparison = Compare-Versions -CurrentVersion $CurrentVersion -LatestVersion $LatestInfo.version
            
            $UpdateResults[$Component] = @{
                "current_version" = $CurrentVersion
                "latest_version" = $LatestInfo.version
                "status" = $Comparison
                "published_at" = $LatestInfo.published_at
                "html_url" = $LatestInfo.html_url
            }
            
            if ($Comparison -eq "newer") {
                Write-Log "$Component 有新版本可用: $($LatestInfo.version)" "WARN"
                
                if (!$DryRun) {
                    Send-Notification -Component $Component -CurrentVersion $CurrentVersion -LatestVersion $LatestInfo.version -ReleaseUrl $LatestInfo.html_url -Config $Config
                    $Updates[$Component] = $LatestInfo.version
                }
            } else {
                Write-Log "$Component 已是最新版本" "INFO"
            }
        } else {
            $UpdateResults[$Component] = @{
                "current_version" = $CurrentVersion
                "latest_version" = "unknown"
                "status" = "error"
                "published_at" = "unknown"
                "html_url" = "unknown"
            }
        }
    }
    
    # 生成报告
    $ReportPath = Generate-UpdateReport -UpdateResults $UpdateResults
    
    # 更新项目版本（如果不是干运行）
    if (!$DryRun -and $Updates.Count -gt 0) {
        Update-ProjectVersions -Updates $Updates -ConfigPath $ConfigPath
    }
    
    Write-Log "版本检查完成，报告: $ReportPath" "INFO"
    
    return $UpdateResults
}

# 执行主函数
if ($MyInvocation.InvocationName -ne '.') {
    Main
}
