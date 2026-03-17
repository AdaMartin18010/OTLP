# 归档过时文档脚本
# 将旧版本文档移动到99_归档目录

param(
    [switch]$WhatIf  # 仅预览，不实际移动
)

$archiveDir = "docs/99_归档"
$timestamp = Get-Date -Format "yyyyMMdd"

# 确保归档目录存在
if (-not (Test-Path $archiveDir)) {
    New-Item -ItemType Directory -Path $archiveDir -Force | Out-Null
}

# 定义归档规则
$archiveRules = @(
    # 旧版本协议文档
    @{ 
        Pattern = "*v1.9.0*"; 
        Description = "OTLP v1.9.0旧版本文档(v1.10.0已更新)";
        TargetSubdir = "协议版本/v1.9.0"
    }
    # 可以添加更多规则
)

Write-Host "📦 归档过时文档..." -ForegroundColor Yellow
Write-Host "═══════════════════════════════════════════"

$archivedCount = 0

foreach ($rule in $archiveRules) {
    $files = Get-ChildItem -Path "docs" -Filter $rule.Pattern -Recurse | 
             Where-Object { $_.FullName -notlike "*$archiveDir*" }
    
    if ($files.Count -gt 0) {
        Write-Host "`n📂 规则: $($rule.Description)" -ForegroundColor Cyan
        
        $targetDir = "$archiveDir/$($rule.TargetSubdir)"
        if (-not $WhatIf) {
            New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
        }
        
        foreach ($file in $files) {
            $targetFile = "$targetDir/$($file.Name)"
            
            if ($WhatIf) {
                Write-Host "   [预览] 将归档: $($file.FullName.Replace($PWD.Path, ''))" -ForegroundColor Gray
            } else {
                # 添加归档注释
                $content = Get-Content $file.FullName -Raw -Encoding UTF8
                $archiveHeader = @"
---
archived: true
archive_date: $(Get-Date -Format "yyyy-MM-dd")
archive_reason: $($rule.Description)
original_path: $($file.FullName.Replace($PWD.Path, ''))
---

"@
                $newContent = $archiveHeader + $content
                Set-Content -Path $targetFile -Value $newContent -Encoding UTF8 -NoNewline
                
                # 删除原文件
                Remove-Item $file.FullName -Force
                
                Write-Host "   ✅ 已归档: $($file.Name)" -ForegroundColor Green
            }
            $archivedCount++
        }
    }
}

Write-Host "`n═══════════════════════════════════════════"
if ($WhatIf) {
    Write-Host "📊 预览结果: 将归档 $archivedCount 个文档" -ForegroundColor Yellow
    Write-Host "   (使用 -WhatIf:$false 执行实际归档)"
} else {
    Write-Host "📊 归档完成: 共归档 $archivedCount 个文档" -ForegroundColor Green
}
