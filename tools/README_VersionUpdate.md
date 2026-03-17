# OTLP文档版本批量更新工具

## 简介

此PowerShell脚本用于批量更新OTLP项目docs目录下所有Markdown文件中的版本信息声明。

## 文件说明

| 文件 | 说明 |
|------|------|
| `Update-DocsVersion.ps1` | 主脚本，执行版本更新 |
| `Test-VersionReplacement.ps1` | 测试脚本，验证替换规则 |
| `README_VersionUpdate.md` | 本文档 |

## 快速开始

### 1. 测试模式（推荐先测试）

```powershell
# 预览将要修改的内容
.\Update-DocsVersion.ps1 -TestMode
```

### 2. 执行更新

```powershell
# 直接执行更新
.\Update-DocsVersion.ps1

# 创建备份后更新
.\Update-DocsVersion.ps1 -CreateBackup

# 指定备份后缀
.\Update-DocsVersion.ps1 -CreateBackup -BackupSuffix ".backup_20260317"
```

### 3. 自定义版本

```powershell
# 使用自定义目标版本
.\Update-DocsVersion.ps1 `
    -TargetVersionOTLP "1.11.0" `
    -TargetVersionSpec "1.56.0" `
    -TargetVersionSemConv "1.41.0" `
    -TargetVersionCollector "0.122.0"
```

## 目标版本（默认值）

| 组件 | 目标版本 |
|------|----------|
| OTLP协议规范 | 1.10.0 |
| OpenTelemetry Specification | 1.55.0 |
| Semantic Conventions | 1.40.0 |
| Collector | 0.121.0 |

## 替换规则

### OTLP版本
- `OTLP v1.9.0` → `OTLP v1.10.0`
- `OTLP 1.9.0` → `OTLP 1.10.0`

### Semantic Conventions版本
- `Semantic Conventions v1.30.0` 到 `v1.39.0` → `v1.40.0`
- `Semantic Conventions v1.41.0.0` → `v1.40.0`

### Collector版本
- `Collector v0.110.0` 到 `v0.119.0` → `v0.121.0`
- `Collector v0.117.0` → `v0.121.0`

### OpenTelemetry Specification版本
- `Specification v1.50.0` 到 `v1.54.0` → `v1.55.0`

## 智能排除

脚本会自动排除以下文件，避免修改历史记录：

- 版本更新说明文件（文件名包含"版本更新"）
- 版本更新日志（文件名包含"版本更新日志"）
- 变更日志（文件名包含"变更日志"或"CHANGELOG"）
- 学术目录下的文件（`academic/`）
- 参考文献文件

## 输出示例

```
========================================
  OTLP文档版本批量更新工具
========================================

目标版本:
  OTLP Protocol:        v1.10.0
  OpenTelemetry Spec:   v1.55.0
  Semantic Conventions: v1.40.0
  Collector:            v0.121.0

扫描到 253 个Markdown文件
将处理 197 个文件 (已排除 56 个)

  文件: E:\_src\OTLP\docs\00_参考资料\00_OTLP知识宇宙导航.md
    行 4: OTLP v1.9.0 → OTLP v1.10.0
      原内容: version: OTLP v1.9.0
      新内容: version: OTLP v1.10.0

========================================
  处理完成
========================================

统计信息:
  处理文件数:  197
  修改文件数:  41
```

## 注意事项

1. **先测试后执行**：建议先使用 `-TestMode` 参数预览修改
2. **创建备份**：重要更新建议使用 `-CreateBackup` 参数
3. **检查排除文件**：确保重要的历史文档已被正确排除
4. **编码格式**：脚本使用UTF-8编码处理文件

## 测试脚本

运行测试脚本验证替换规则：

```powershell
.\Test-VersionReplacement.ps1
```

此脚本会：
1. 验证所有替换规则的正确性
2. 扫描实际文档中的版本声明
3. 显示找到的匹配项

## 故障排除

### 执行策略限制

如果遇到执行策略错误，请运行：

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

或在每次执行时添加参数：

```powershell
powershell -ExecutionPolicy Bypass -File .\Update-DocsVersion.ps1
```

### 文件编码问题

脚本默认使用UTF-8编码。如果遇到编码问题，可以修改脚本中的编码参数。
