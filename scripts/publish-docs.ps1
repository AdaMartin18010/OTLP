# OpenTelemetry 文档发布脚本
# 用于发布文档到各种平台

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

param(
    [ValidateSet("local", "github", "gitbook", "mkdocs")]
    [string]$Target = "local",
    [switch]$Validate,
    [switch]$Build,
    [switch]$Deploy,
    [string]$OutputDir = "dist/docs"
)

Write-Host "OpenTelemetry 文档发布工具" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir
$docsPath = Join-Path $projectRoot "docs"
$outputPath = Join-Path $projectRoot $OutputDir

# 验证文档
if ($Validate) {
    Write-Host "`n验证文档质量..." -ForegroundColor Cyan
    
    $validateScript = Join-Path $scriptDir "validate-docs.ps1"
    if (Test-Path $validateScript) {
        & $validateScript -All
        if ($LASTEXITCODE -ne 0) {
            Write-Error "文档验证失败，请修复错误后重试"
            exit 1
        }
    } else {
        Write-Warning "验证脚本不存在: $validateScript"
    }
}

# 生成文档
if ($Build) {
    Write-Host "`n生成文档..." -ForegroundColor Cyan
    
    $generateScript = Join-Path $scriptDir "generate-docs.ps1"
    if (Test-Path $generateScript) {
        & $generateScript -All
    } else {
        Write-Warning "生成脚本不存在: $generateScript"
    }
}

# 根据目标平台处理文档
switch ($Target) {
    "local" {
        Write-Host "`n准备本地发布..." -ForegroundColor Cyan
        
        if (-not (Test-Path $outputPath)) {
            New-Item -ItemType Directory -Path $outputPath -Force | Out-Null
        }
        
        # 复制文档文件
        Copy-Item -Path "$docsPath\*" -Destination $outputPath -Recurse -Force
        
        # 创建本地服务器配置
        $serverConfig = @"
# 本地文档服务器配置
# 使用 Python 简单服务器:
# python -m http.server 8000 -d $OutputDir

# 或使用 Node.js serve:
# npx serve $OutputDir

# 或使用 PowerShell:
# Start-Process "http://localhost:8000"
"@
        
        $serverConfig | Out-File -FilePath (Join-Path $outputPath "README.md") -Encoding UTF8
        
        Write-Host "✅ 本地文档已准备到: $outputPath" -ForegroundColor Green
        Write-Host "启动本地服务器: cd $OutputDir && python -m http.server 8000" -ForegroundColor Yellow
    }
    
    "github" {
        Write-Host "`n准备GitHub Pages发布..." -ForegroundColor Cyan
        
        if (-not (Test-Path $outputPath)) {
            New-Item -ItemType Directory -Path $outputPath -Force | Out-Null
        }
        
        # 复制文档文件
        Copy-Item -Path "$docsPath\*" -Destination $outputPath -Recurse -Force
        
        # 创建GitHub Pages配置
        $githubConfig = @"
# GitHub Pages 配置

## 设置步骤

1. 在仓库设置中启用 GitHub Pages
2. 选择 Source 为 "Deploy from a branch"
3. 选择 Branch 为 "gh-pages" 或 "main"
4. 选择 Folder 为 "/docs" 或 "/root"

## 自定义域名 (可选)

在仓库根目录创建 CNAME 文件:
```
your-domain.com
```

## 自动部署

使用 GitHub Actions 自动部署:

```yaml
name: Deploy Docs
on:
  push:
    branches: [ main ]
    paths: [ 'docs/**' ]
jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Deploy to GitHub Pages
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: `${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./docs
```
"@
        
        $githubConfig | Out-File -FilePath (Join-Path $outputPath "GITHUB_PAGES.md") -Encoding UTF8
        
        Write-Host "✅ GitHub Pages 文档已准备到: $outputPath" -ForegroundColor Green
    }
    
    "gitbook" {
        Write-Host "`n准备GitBook发布..." -ForegroundColor Cyan
        
        # 创建GitBook配置
        $gitbookConfig = @"
{
    "title": "OpenTelemetry 完整学习与实践平台",
    "description": "OpenTelemetry 的完整文档、示例和最佳实践",
    "author": "OpenTelemetry 项目团队",
    "language": "zh-hans",
    "gitbook": "3.2.3",
    "root": ".",
    "structure": {
        "readme": "README.md",
        "summary": "SUMMARY.md"
    },
    "plugins": [
        "search",
        "sharing",
        "fontsettings",
        "highlight",
        "livereload"
    ],
    "pluginsConfig": {
        "fontsettings": {
            "theme": "white",
            "family": "sans",
            "size": 2
        }
    }
}
"@
        
        $gitbookConfig | Out-File -FilePath (Join-Path $docsPath "book.json") -Encoding UTF8
        
        # 创建SUMMARY.md
        $summaryContent = @"
# 目录

## 快速开始
* [快速开始指南](QUICK_START.md)
* [教程与学习路径](TUTORIALS.md)

## 核心文档
* [API参考](API_REFERENCE.md)
* [架构设计](ARCHITECTURE.md)
* [术语定义](TERMS.md)
* [语义约定](SEMANTIC_CONVENTIONS.md)

## 实践指南
* [部署指南](DEPLOYMENT_GUIDE.md)
* [集成指南](INTEGRATION_GUIDE.md)
* [性能优化](PERFORMANCE_GUIDE.md)
* [安全指南](SECURITY_GUIDE.md)
* [故障排除](TROUBLESHOOTING.md)

## 教育与研究
* [课程对齐](COURSE_ALIGNMENT.md)
* [形式化证明](FORMAL_PROOFS.md)

## 项目状态
* [文档状态](STATUS.md)
* [格式标准](FORMAT_STANDARDS.md)
"@
        
        $summaryContent | Out-File -FilePath (Join-Path $docsPath "SUMMARY.md") -Encoding UTF8
        
        Write-Host "✅ GitBook 配置已创建" -ForegroundColor Green
        Write-Host "安装 GitBook: npm install -g gitbook-cli" -ForegroundColor Yellow
        Write-Host "构建文档: cd docs && gitbook build" -ForegroundColor Yellow
    }
    
    "mkdocs" {
        Write-Host "`n准备MkDocs发布..." -ForegroundColor Cyan
        
        # 创建MkDocs配置
        $mkdocsConfig = @"
site_name: OpenTelemetry 完整学习与实践平台
site_description: OpenTelemetry 的完整文档、示例和最佳实践
site_author: OpenTelemetry 项目团队
site_url: https://your-domain.com

theme:
  name: material
  language: zh
  palette:
    - scheme: default
      primary: blue
      accent: blue
      toggle:
        icon: material/brightness-7
        name: 切换到深色模式
    - scheme: slate
      primary: blue
      accent: blue
      toggle:
        icon: material/brightness-4
        name: 切换到浅色模式
  features:
    - navigation.tabs
    - navigation.sections
    - navigation.expand
    - navigation.path
    - search.highlight
    - search.share
    - toc.follow

nav:
  - 快速开始:
    - 快速开始指南: QUICK_START.md
    - 教程与学习路径: TUTORIALS.md
  - 核心文档:
    - API参考: API_REFERENCE.md
    - 架构设计: ARCHITECTURE.md
    - 术语定义: TERMS.md
    - 语义约定: SEMANTIC_CONVENTIONS.md
  - 实践指南:
    - 部署指南: DEPLOYMENT_GUIDE.md
    - 集成指南: INTEGRATION_GUIDE.md
    - 性能优化: PERFORMANCE_GUIDE.md
    - 安全指南: SECURITY_GUIDE.md
    - 故障排除: TROUBLESHOOTING.md
  - 教育与研究:
    - 课程对齐: COURSE_ALIGNMENT.md
    - 形式化证明: FORMAL_PROOFS.md
  - 项目状态:
    - 文档状态: STATUS.md
    - 格式标准: FORMAT_STANDARDS.md

plugins:
  - search
  - mkdocstrings

markdown_extensions:
  - pymdownx.highlight:
      anchor_linenums: true
  - pymdownx.inlinehilite
  - pymdownx.superfences
  - pymdownx.tabbed:
      alternate_style: true
  - tables
  - toc:
      permalink: true
"@
        
        $mkdocsConfig | Out-File -FilePath (Join-Path $projectRoot "mkdocs.yml") -Encoding UTF8
        
        Write-Host "✅ MkDocs 配置已创建" -ForegroundColor Green
        Write-Host "安装 MkDocs: pip install mkdocs mkdocs-material" -ForegroundColor Yellow
        Write-Host "预览文档: mkdocs serve" -ForegroundColor Yellow
        Write-Host "构建文档: mkdocs build" -ForegroundColor Yellow
    }
}

# 部署文档
if ($Deploy) {
    Write-Host "`n部署文档..." -ForegroundColor Cyan
    
    switch ($Target) {
        "github" {
            Write-Host "部署到 GitHub Pages..." -ForegroundColor Yellow
            # 这里可以添加GitHub Pages部署逻辑
        }
        "gitbook" {
            Write-Host "部署到 GitBook..." -ForegroundColor Yellow
            # 这里可以添加GitBook部署逻辑
        }
        "mkdocs" {
            Write-Host "部署到 MkDocs..." -ForegroundColor Yellow
            # 这里可以添加MkDocs部署逻辑
        }
    }
}

Write-Host "`n🎉 文档发布准备完成！" -ForegroundColor Green
Write-Host "目标平台: $Target" -ForegroundColor Yellow
Write-Host "输出目录: $outputPath" -ForegroundColor Yellow
