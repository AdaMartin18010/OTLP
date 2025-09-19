#!/bin/bash
# OpenTelemetry 版本检查自动化脚本 (Linux/macOS版本)
# 用于检查官方版本更新并通知项目维护者

set -euo pipefail

# 默认配置
CONFIG_PATH="${1:-version-check-config.json}"
DRY_RUN="${2:-false}"
VERBOSE="${3:-false}"

# 日志函数
log() {
    local level="$1"
    shift
    local message="$*"
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    local log_message="[$timestamp] [$level] $message"
    
    if [[ "$VERBOSE" == "true" ]] || [[ "$level" == "ERROR" ]] || [[ "$level" == "WARN" ]]; then
        echo "$log_message"
    fi
    
    # 写入日志文件
    local log_dir="logs"
    local log_file="$log_dir/version-check-$(date '+%Y-%m-%d').log"
    mkdir -p "$log_dir"
    echo "$log_message" >> "$log_file"
}

# 获取最新版本信息
get_latest_version() {
    local component="$1"
    local api_url="$2"
    
    log "INFO" "检查 $component 的最新版本..."
    
    local response
    if response=$(curl -s -H "Accept: application/vnd.github.v3+json" \
                      -H "User-Agent: OpenTelemetry-Version-Checker/1.0" \
                      --max-time 30 \
                      "$api_url"); then
        
        local version
        version=$(echo "$response" | jq -r '.tag_name // empty' | sed 's/^v//')
        
        if [[ -n "$version" && "$version" != "null" ]]; then
            log "INFO" "$component 最新版本: $version"
            echo "$version"
        else
            log "WARN" "无法获取 $component 版本信息"
            echo ""
        fi
    else
        log "ERROR" "获取 $component 版本信息失败"
        echo ""
    fi
}

# 比较版本号
compare_versions() {
    local current="$1"
    local latest="$2"
    
    if [[ -z "$current" || -z "$latest" ]]; then
        echo "unknown"
        return
    fi
    
    # 使用sort -V进行版本比较
    if [[ "$latest" == "$current" ]]; then
        echo "same"
    elif printf '%s\n%s\n' "$current" "$latest" | sort -V -C; then
        echo "newer"
    else
        echo "older"
    fi
}

# 发送Slack通知
send_slack_notification() {
    local component="$1"
    local current_version="$2"
    local latest_version="$3"
    local release_url="$4"
    local webhook_url="$5"
    local channel="$6"
    
    local message="🚀 OpenTelemetry 版本更新通知

组件: $component
当前版本: $current_version
最新版本: $latest_version
发布页面: $release_url

请及时更新项目文档和配置。"
    
    local payload
    payload=$(jq -n \
        --arg text "$message" \
        --arg channel "$channel" \
        '{text: $text, channel: $channel}')
    
    if curl -s -X POST -H 'Content-type: application/json' \
            --data "$payload" \
            "$webhook_url" > /dev/null; then
        log "INFO" "Slack通知已发送"
    else
        log "ERROR" "Slack通知发送失败"
    fi
}

# 发送邮件通知
send_email_notification() {
    local component="$1"
    local current_version="$2"
    local latest_version="$3"
    local release_url="$4"
    local recipients="$5"
    
    local subject="OpenTelemetry 版本更新: $component"
    local body="🚀 OpenTelemetry 版本更新通知

组件: $component
当前版本: $current_version
最新版本: $latest_version
发布页面: $release_url

请及时更新项目文档和配置。"
    
    if command -v mail >/dev/null 2>&1; then
        echo "$body" | mail -s "$subject" "$recipients"
        log "INFO" "邮件通知已发送"
    else
        log "WARN" "mail命令不可用，跳过邮件通知"
    fi
}

# 发送通知
send_notification() {
    local component="$1"
    local current_version="$2"
    local latest_version="$3"
    local release_url="$4"
    
    # 从配置文件读取通知设置
    local email_enabled
    local email_recipients
    local slack_enabled
    local slack_webhook
    local slack_channel
    
    email_enabled=$(jq -r '.notification_settings.email.enabled // false' "$CONFIG_PATH")
    email_recipients=$(jq -r '.notification_settings.email.recipients[] // empty' "$CONFIG_PATH" | tr '\n' ' ')
    slack_enabled=$(jq -r '.notification_settings.slack.enabled // false' "$CONFIG_PATH")
    slack_webhook=$(jq -r '.notification_settings.slack.webhook_url // empty' "$CONFIG_PATH")
    slack_channel=$(jq -r '.notification_settings.slack.channel // "#opentelemetry-updates"' "$CONFIG_PATH")
    
    if [[ "$email_enabled" == "true" && -n "$email_recipients" ]]; then
        send_email_notification "$component" "$current_version" "$latest_version" "$release_url" "$email_recipients"
    fi
    
    if [[ "$slack_enabled" == "true" && -n "$slack_webhook" ]]; then
        send_slack_notification "$component" "$current_version" "$latest_version" "$release_url" "$slack_webhook" "$slack_channel"
    fi
}

# 更新项目版本信息
update_project_versions() {
    local updates_json="$1"
    
    if [[ "$DRY_RUN" == "true" ]]; then
        log "INFO" "干运行模式，跳过版本更新"
        return
    fi
    
    # 使用jq更新配置文件
    local temp_file
    temp_file=$(mktemp)
    
    jq --argjson updates "$updates_json" '
        .current_versions = (.current_versions * $updates)
    ' "$CONFIG_PATH" > "$temp_file"
    
    mv "$temp_file" "$CONFIG_PATH"
    log "INFO" "项目版本信息已更新"
}

# 生成更新报告
generate_update_report() {
    local update_results="$1"
    
    local report_dir="reports"
    local report_path="$report_dir/version-check-report-$(date '+%Y-%m-%d-%H%M').md"
    mkdir -p "$report_dir"
    
    cat > "$report_path" << EOF
# OpenTelemetry 版本检查报告

**检查时间**: $(date '+%Y-%m-%d %H:%M:%S')
**检查者**: 自动化脚本

## 检查结果

| 组件 | 当前版本 | 最新版本 | 状态 | 更新建议 |
|------|----------|----------|------|----------|
EOF

    # 处理每个组件的检查结果
    echo "$update_results" | jq -r '
        to_entries[] | 
        "| \(.key) | \(.value.current_version) | \(.value.latest_version) | \(
            if .value.status == "newer" then "🆕 有新版本"
            elif .value.status == "same" then "✅ 已是最新"
            elif .value.status == "older" then "⚠️ 版本异常"
            else "❓ 检查失败"
            end
        ) | \(
            if .value.status == "newer" then "建议更新到 \(.value.latest_version)"
            elif .value.status == "same" then "无需更新"
            elif .value.status == "older" then "需要调查版本异常"
            else "需要手动检查"
            end
        ) |"
    ' >> "$report_path"
    
    cat >> "$report_path" << EOF

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
*报告生成时间: $(date '+%Y-%m-%d %H:%M:%S')*
EOF

    log "INFO" "更新报告已生成: $report_path"
    echo "$report_path"
}

# 创建默认配置文件
create_default_config() {
    cat > "$CONFIG_PATH" << 'EOF'
{
  "check_interval_hours": 24,
  "notification_channels": ["email", "slack"],
  "monitored_components": {
    "specification": "https://api.github.com/repos/open-telemetry/opentelemetry-specification/releases/latest",
    "collector": "https://api.github.com/repos/open-telemetry/opentelemetry-collector/releases/latest",
    "go_sdk": "https://api.github.com/repos/open-telemetry/opentelemetry-go/releases/latest",
    "python_sdk": "https://api.github.com/repos/open-telemetry/opentelemetry-python/releases/latest",
    "rust_sdk": "https://api.github.com/repos/open-telemetry/opentelemetry-rust/releases/latest",
    "java_sdk": "https://api.github.com/repos/open-telemetry/opentelemetry-java/releases/latest",
    "javascript_sdk": "https://api.github.com/repos/open-telemetry/opentelemetry-js/releases/latest"
  },
  "current_versions": {
    "specification": "1.25.0",
    "collector": "0.91.0",
    "go_sdk": "1.19.0",
    "python_sdk": "1.20.0",
    "rust_sdk": "0.24.0",
    "java_sdk": "1.32.0",
    "javascript_sdk": "1.15.0"
  },
  "notification_settings": {
    "email": {
      "enabled": false,
      "recipients": ["maintainer@example.com"],
      "smtp_server": "smtp.example.com"
    },
    "slack": {
      "enabled": false,
      "webhook_url": "https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK",
      "channel": "#opentelemetry-updates"
    }
  }
}
EOF
}

# 主函数
main() {
    log "INFO" "开始OpenTelemetry版本检查..."
    
    # 检查依赖
    if ! command -v jq >/dev/null 2>&1; then
        log "ERROR" "jq命令不可用，请安装jq"
        exit 1
    fi
    
    if ! command -v curl >/dev/null 2>&1; then
        log "ERROR" "curl命令不可用，请安装curl"
        exit 1
    fi
    
    # 加载配置
    if [[ ! -f "$CONFIG_PATH" ]]; then
        log "WARN" "配置文件不存在，创建默认配置"
        create_default_config
    fi
    
    local update_results="{}"
    local updates="{}"
    
    # 检查每个组件
    local components
    components=$(jq -r '.monitored_components | keys[]' "$CONFIG_PATH")
    
    while IFS= read -r component; do
        local api_url
        local current_version
        local latest_version
        
        api_url=$(jq -r ".monitored_components.$component" "$CONFIG_PATH")
        current_version=$(jq -r ".current_versions.$component" "$CONFIG_PATH")
        
        latest_version=$(get_latest_version "$component" "$api_url")
        
        if [[ -n "$latest_version" ]]; then
            local comparison
            comparison=$(compare_versions "$current_version" "$latest_version")
            
            # 更新结果
            update_results=$(echo "$update_results" | jq --arg comp "$component" \
                --arg current "$current_version" \
                --arg latest "$latest_version" \
                --arg status "$comparison" \
                '. + {($comp): {current_version: $current, latest_version: $latest, status: $status}}')
            
            if [[ "$comparison" == "newer" ]]; then
                log "WARN" "$component 有新版本可用: $latest_version"
                
                if [[ "$DRY_RUN" != "true" ]]; then
                    local release_url
                    release_url="https://github.com/open-telemetry/opentelemetry-$component/releases/tag/v$latest_version"
                    send_notification "$component" "$current_version" "$latest_version" "$release_url"
                    
                    updates=$(echo "$updates" | jq --arg comp "$component" --arg version "$latest_version" \
                        '. + {($comp): $version}')
                fi
            else
                log "INFO" "$component 已是最新版本"
            fi
        else
            update_results=$(echo "$update_results" | jq --arg comp "$component" \
                --arg current "$current_version" \
                '. + {($comp): {current_version: $current, latest_version: "unknown", status: "error"}}')
        fi
    done <<< "$components"
    
    # 生成报告
    local report_path
    report_path=$(generate_update_report "$update_results")
    
    # 更新项目版本
    if [[ "$updates" != "{}" ]]; then
        update_project_versions "$updates"
    fi
    
    log "INFO" "版本检查完成，报告: $report_path"
    
    echo "$update_results"
}

# 执行主函数
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
