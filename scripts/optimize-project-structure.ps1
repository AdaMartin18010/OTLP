# OTLP 2025 项目结构优化脚本
# 重新组织目录结构，提高可维护性和可扩展性

param(
    [switch]$DryRun,
    [switch]$Backup,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

# 颜色输出函数
function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# 项目结构优化配置
$StructureOptimization = @{
    StartTime = Get-Date
    Changes = @()
    BackupPath = ""
    DryRun = $DryRun
}

# 创建备份
function Create-Backup {
    if ($Backup) {
        $backupDir = "backup-$(Get-Date -Format 'yyyy-MM-dd-HHmmss')"
        Write-ColorOutput "📦 创建项目备份: $backupDir" "Cyan"
        
        try {
            # 复制整个项目到备份目录
            Copy-Item -Path "." -Destination $backupDir -Recurse -Exclude @("node_modules", "target", ".git", "backup-*")
            $StructureOptimization.BackupPath = $backupDir
            Write-ColorOutput "✅ 备份创建成功: $backupDir" "Green"
        } catch {
            Write-ColorOutput "❌ 备份创建失败: $($_.Exception.Message)" "Red"
            exit 1
        }
    }
}

# 优化目录结构
function Optimize-DirectoryStructure {
    Write-ColorOutput "🗂️ 优化目录结构..." "Cyan"
    
    # 定义新的目录结构
    $newStructure = @{
        "01_Core" = @{
            "description" = "核心组件和基础功能"
            "subdirs" = @("api", "sdk", "protocols", "semantics")
        }
        "02_Implementations" = @{
            "description" = "多语言实现"
            "subdirs" = @("rust", "go", "python", "java", "javascript", "dotnet")
        }
        "03_Integrations" = @{
            "description" = "集成和扩展"
            "subdirs" = @("collectors", "exporters", "processors", "instrumentations")
        }
        "04_Examples" = @{
            "description" = "示例和教程"
            "subdirs" = @("basic", "advanced", "tutorials", "demos")
        }
        "05_Testing" = @{
            "description" = "测试和基准"
            "subdirs" = @("unit", "integration", "benchmarks", "performance")
        }
        "06_Documentation" = @{
            "description" = "文档和规范"
            "subdirs" = @("specs", "guides", "api-docs", "tutorials")
        }
        "07_Tools" = @{
            "description" = "工具和脚本"
            "subdirs" = @("scripts", "utilities", "generators", "validators")
        }
        "08_Deployment" = @{
            "description" = "部署和运维"
            "subdirs" = @("docker", "kubernetes", "helm", "monitoring")
        }
        "09_Research" = @{
            "description" = "研究和实验"
            "subdirs" = @("experiments", "papers", "prototypes", "analysis")
        }
        "10_Community" = @{
            "description" = "社区和治理"
            "subdirs" = @("governance", "contributing", "releases", "roadmap")
        }
    }
    
    # 创建新目录结构
    foreach ($dir in $newStructure.Keys) {
        $dirInfo = $newStructure[$dir]
        
        if (!(Test-Path $dir)) {
            if ($DryRun) {
                Write-ColorOutput "  📁 [DRY RUN] 创建目录: $dir" "Yellow"
            } else {
                New-Item -ItemType Directory -Path $dir -Force | Out-Null
                Write-ColorOutput "  📁 创建目录: $dir" "Green"
            }
            
            $StructureOptimization.Changes += @{
                Type = "CreateDirectory"
                Path = $dir
                Description = $dirInfo.description
            }
        }
        
        # 创建子目录
        foreach ($subdir in $dirInfo.subdirs) {
            $subdirPath = Join-Path $dir $subdir
            if (!(Test-Path $subdirPath)) {
                if ($DryRun) {
                    Write-ColorOutput "    📁 [DRY RUN] 创建子目录: $subdirPath" "Yellow"
                } else {
                    New-Item -ItemType Directory -Path $subdirPath -Force | Out-Null
                    Write-ColorOutput "    📁 创建子目录: $subdirPath" "Green"
                }
                
                $StructureOptimization.Changes += @{
                    Type = "CreateSubDirectory"
                    Path = $subdirPath
                    Description = "子目录: $subdir"
                }
            }
        }
    }
}

# 重新组织现有文件
function Reorganize-ExistingFiles {
    Write-ColorOutput "📋 重新组织现有文件..." "Cyan"
    
    # 文件移动映射
    $fileMappings = @{
        # 核心组件
        "spec/*.md" = "06_Documentation/specs/"
        "docs/*.md" = "06_Documentation/guides/"
        
        # 实现
        "examples/minimal-rust" = "04_Examples/basic/rust/"
        "examples/minimal-go" = "04_Examples/basic/go/"
        "examples/minimal-python" = "04_Examples/basic/python/"
        "examples/minimal-java" = "04_Examples/basic/java/"
        "examples/minimal-javascript" = "04_Examples/basic/javascript/"
        "languages/rust" = "02_Implementations/rust/"
        "languages/go" = "02_Implementations/go/"
        "languages/python" = "02_Implementations/python/"
        "languages/java" = "02_Implementations/java/"
        "languages/javascript" = "02_Implementations/javascript/"
        
        # 集成
        "implementations/collector" = "03_Integrations/collectors/"
        "technologies/tracezip" = "03_Integrations/processors/tracezip/"
        "technologies/crosstrace" = "03_Integrations/processors/crosstrace/"
        "technologies/atys" = "03_Integrations/processors/atys/"
        
        # 测试
        "benchmarks" = "05_Testing/benchmarks/"
        "tests" = "05_Testing/unit/"
        
        # 工具
        "scripts" = "07_Tools/scripts/"
        "governance" = "10_Community/governance/"
        
        # 部署
        "docker" = "08_Deployment/docker/"
        "kubernetes" = "08_Deployment/kubernetes/"
    }
    
    foreach ($source in $fileMappings.Keys) {
        $destination = $fileMappings[$source]
        
        # 检查源路径是否存在
        if (Test-Path $source) {
            # 确保目标目录存在
            $destDir = Split-Path $destination -Parent
            if (!(Test-Path $destDir)) {
                if ($DryRun) {
                    Write-ColorOutput "  📁 [DRY RUN] 创建目标目录: $destDir" "Yellow"
                } else {
                    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
                }
            }
            
            # 移动文件或目录
            if ($DryRun) {
                Write-ColorOutput "  📦 [DRY RUN] 移动: $source -> $destination" "Yellow"
            } else {
                try {
                    Move-Item -Path $source -Destination $destination -Force
                    Write-ColorOutput "  📦 移动: $source -> $destination" "Green"
                    
                    $StructureOptimization.Changes += @{
                        Type = "MoveFile"
                        Source = $source
                        Destination = $destination
                    }
                } catch {
                    Write-ColorOutput "  ❌ 移动失败: $source -> $destination ($($_.Exception.Message))" "Red"
                }
            }
        } else {
            if ($Verbose) {
                Write-ColorOutput "  ⚠️ 源路径不存在: $source" "Yellow"
            }
        }
    }
}

# 创建目录说明文件
function Create-DirectoryReadme {
    Write-ColorOutput "📝 创建目录说明文件..." "Cyan"
    
    $directoryDescriptions = @{
        "01_Core" = @"
# 核心组件 (Core Components)

本目录包含 OpenTelemetry 的核心组件和基础功能。

## 子目录说明

- **api/**: OpenTelemetry API 定义和接口
- **sdk/**: SDK 核心实现
- **protocols/**: 协议定义和实现
- **semantics/**: 语义约定和规范

## 相关文档

- [API 参考文档](../06_Documentation/api-docs/)
- [协议规范](../06_Documentation/specs/)
- [语义约定](../06_Documentation/specs/semantic-conventions.md)
"@
        
        "02_Implementations" = @"
# 多语言实现 (Multi-Language Implementations)

本目录包含各种编程语言的 OpenTelemetry 实现。

## 支持的语言

- **rust/**: Rust 语言实现
- **go/**: Go 语言实现
- **python/**: Python 语言实现
- **java/**: Java 语言实现
- **javascript/**: JavaScript/TypeScript 实现
- **dotnet/**: .NET 语言实现

## 使用指南

每个语言目录都包含：
- 完整的 SDK 实现
- 示例代码
- 测试用例
- 文档和教程

## 相关文档

- [实现指南](../06_Documentation/guides/implementations.md)
- [API 参考](../06_Documentation/api-docs/)
"@
        
        "03_Integrations" = @"
# 集成和扩展 (Integrations & Extensions)

本目录包含各种集成组件和扩展功能。

## 组件类型

- **collectors/**: OpenTelemetry Collector 配置和扩展
- **exporters/**: 各种导出器实现
- **processors/**: 数据处理和转换组件
- **instrumentations/**: 自动检测库

## 新兴技术

- **tracezip/**: Tracezip 压缩技术
- **crosstrace/**: CrossTrace 跨服务关联
- **atys/**: Atys 热点分析

## 相关文档

- [集成指南](../06_Documentation/guides/integrations.md)
- [Collector 配置](../06_Documentation/guides/collector.md)
"@
        
        "04_Examples" = @"
# 示例和教程 (Examples & Tutorials)

本目录包含各种示例代码和教程。

## 示例分类

- **basic/**: 基础示例，适合初学者
- **advanced/**: 高级示例，展示复杂用法
- **tutorials/**: 完整教程，包含步骤说明
- **demos/**: 演示项目，展示实际应用

## 语言支持

每个示例都提供多种语言版本：
- Rust
- Go
- Python
- Java
- JavaScript

## 相关文档

- [快速开始](../06_Documentation/guides/quick-start.md)
- [教程索引](../06_Documentation/tutorials/)
"@
        
        "05_Testing" = @"
# 测试和基准 (Testing & Benchmarks)

本目录包含测试用例和性能基准。

## 测试类型

- **unit/**: 单元测试
- **integration/**: 集成测试
- **benchmarks/**: 性能基准测试
- **performance/**: 性能测试和分析

## 测试覆盖

- 功能测试
- 性能测试
- 兼容性测试
- 压力测试

## 相关文档

- [测试指南](../06_Documentation/guides/testing.md)
- [性能基准](../06_Documentation/guides/benchmarks.md)
"@
        
        "06_Documentation" = @"
# 文档和规范 (Documentation & Specifications)

本目录包含完整的项目文档和规范。

## 文档类型

- **specs/**: 技术规范和协议定义
- **guides/**: 使用指南和教程
- **api-docs/**: API 参考文档
- **tutorials/**: 详细教程

## 文档结构

- 快速开始指南
- 详细使用说明
- API 参考
- 最佳实践
- 故障排除

## 相关链接

- [项目主页](../../README.md)
- [贡献指南](../10_Community/contributing/)
"@
        
        "07_Tools" = @"
# 工具和脚本 (Tools & Scripts)

本目录包含各种开发工具和自动化脚本。

## 工具类型

- **scripts/**: 自动化脚本
- **utilities/**: 实用工具
- **generators/**: 代码生成器
- **validators/**: 验证工具

## 脚本功能

- 版本检查
- 质量检查
- 性能测试
- 部署脚本

## 使用方法

```bash
# 运行版本检查
./scripts/version-check-2025.ps1

# 运行质量检查
./scripts/quality-assurance-check.ps1

# 运行性能测试
./scripts/run-comprehensive-benchmark.ps1
```
"@
        
        "08_Deployment" = @"
# 部署和运维 (Deployment & Operations)

本目录包含部署配置和运维工具。

## 部署方式

- **docker/**: Docker 容器化部署
- **kubernetes/**: Kubernetes 集群部署
- **helm/**: Helm 图表
- **monitoring/**: 监控和告警配置

## 环境支持

- 开发环境
- 测试环境
- 生产环境
- 云环境

## 相关文档

- [部署指南](../06_Documentation/guides/deployment.md)
- [运维手册](../06_Documentation/guides/operations.md)
"@
        
        "09_Research" = @"
# 研究和实验 (Research & Experiments)

本目录包含研究项目和实验性功能。

## 研究领域

- **experiments/**: 实验性功能
- **papers/**: 研究论文
- **prototypes/**: 原型实现
- **analysis/**: 分析报告

## 研究方向

- 性能优化
- 新算法研究
- 架构改进
- 标准制定

## 相关文档

- [研究计划](../06_Documentation/guides/research.md)
- [实验报告](../06_Documentation/guides/experiments.md)
"@
        
        "10_Community" = @"
# 社区和治理 (Community & Governance)

本目录包含社区治理和贡献指南。

## 治理结构

- **governance/**: 治理框架和流程
- **contributing/**: 贡献指南
- **releases/**: 发布管理
- **roadmap/**: 路线图规划

## 社区参与

- 贡献代码
- 报告问题
- 提出建议
- 参与讨论

## 相关文档

- [贡献指南](./contributing/)
- [治理框架](./governance/)
- [发布流程](./releases/)
"@
    }
    
    foreach ($dir in $directoryDescriptions.Keys) {
        $readmePath = Join-Path $dir "README.md"
        
        if ($DryRun) {
            Write-ColorOutput "  📝 [DRY RUN] 创建 README: $readmePath" "Yellow"
        } else {
            $directoryDescriptions[$dir] | Out-File -FilePath $readmePath -Encoding UTF8
            Write-ColorOutput "  📝 创建 README: $readmePath" "Green"
            
            $StructureOptimization.Changes += @{
                Type = "CreateReadme"
                Path = $readmePath
                Description = "目录说明文件"
            }
        }
    }
}

# 更新项目根目录 README
function Update-RootReadme {
    Write-ColorOutput "📝 更新项目根目录 README..." "Cyan"
    
    $newReadme = @"
# OpenTelemetry 2025年学术研究项目

> **项目重新定位**: 基于国际2025年最新技术工程方案标准，本项目重新定位为**知识经验梳理和论证形式化证明**的学术研究项目

## 🎯 项目概述

本项目是基于国际2025年最新技术工程方案标准，重新定位为**知识经验梳理和论证形式化证明**的学术研究项目。通过对标国际权威标准、著名大学研究成果和行业最佳实践，建立了一套完整的OpenTelemetry知识体系和技术论证框架。

## 📁 项目结构

\`\`\`
OTLP_2025/
├── 01_Core/                    # 核心组件和基础功能
│   ├── api/                    # OpenTelemetry API 定义
│   ├── sdk/                    # SDK 核心实现
│   ├── protocols/              # 协议定义和实现
│   └── semantics/              # 语义约定和规范
│
├── 02_Implementations/         # 多语言实现
│   ├── rust/                   # Rust 语言实现
│   ├── go/                     # Go 语言实现
│   ├── python/                 # Python 语言实现
│   ├── java/                   # Java 语言实现
│   ├── javascript/             # JavaScript/TypeScript 实现
│   └── dotnet/                 # .NET 语言实现
│
├── 03_Integrations/            # 集成和扩展
│   ├── collectors/             # OpenTelemetry Collector
│   ├── exporters/              # 各种导出器
│   ├── processors/             # 数据处理组件
│   └── instrumentations/       # 自动检测库
│
├── 04_Examples/                # 示例和教程
│   ├── basic/                  # 基础示例
│   ├── advanced/               # 高级示例
│   ├── tutorials/              # 完整教程
│   └── demos/                  # 演示项目
│
├── 05_Testing/                 # 测试和基准
│   ├── unit/                   # 单元测试
│   ├── integration/            # 集成测试
│   ├── benchmarks/             # 性能基准
│   └── performance/            # 性能测试
│
├── 06_Documentation/           # 文档和规范
│   ├── specs/                  # 技术规范
│   ├── guides/                 # 使用指南
│   ├── api-docs/               # API 参考
│   └── tutorials/              # 详细教程
│
├── 07_Tools/                   # 工具和脚本
│   ├── scripts/                # 自动化脚本
│   ├── utilities/              # 实用工具
│   ├── generators/             # 代码生成器
│   └── validators/             # 验证工具
│
├── 08_Deployment/              # 部署和运维
│   ├── docker/                 # Docker 部署
│   ├── kubernetes/             # Kubernetes 部署
│   ├── helm/                   # Helm 图表
│   └── monitoring/             # 监控配置
│
├── 09_Research/                # 研究和实验
│   ├── experiments/            # 实验性功能
│   ├── papers/                 # 研究论文
│   ├── prototypes/             # 原型实现
│   └── analysis/               # 分析报告
│
└── 10_Community/               # 社区和治理
    ├── governance/             # 治理框架
    ├── contributing/           # 贡献指南
    ├── releases/               # 发布管理
    └── roadmap/                # 路线图规划
\`\`\`

## 🚀 快速开始

### 环境要求

- **Docker**: 用于运行 Collector 和完整栈
- **Go**: 1.21+ (可选)
- **Python**: 3.10+ (可选)
- **Rust**: 1.78+ (可选)
- **Node.js**: 18.0+ (可选)
- **Java**: 11+ (可选)

### 5分钟快速体验

1. **启动 Collector**
   \`\`\`bash
   # Windows (PowerShell)
   ./07_Tools/scripts/run-collector.ps1
   
   # Linux/macOS (bash)
   ./07_Tools/scripts/run-collector.sh
   \`\`\`

2. **运行示例**
   \`\`\`bash
   # Rust (推荐，性能最佳)
   cd 04_Examples/basic/rust && cargo run
   
   # Go
   cd 04_Examples/basic/go && go run .
   
   # Python
   cd 04_Examples/basic/python && python main.py
   
   # Java
   cd 04_Examples/basic/java && mvn exec:java
   
   # JavaScript
   cd 04_Examples/basic/javascript && npm start
   \`\`\`

3. **查看结果**
   - **Jaeger UI**: http://localhost:16686
   - **Prometheus**: http://localhost:9090
   - **Grafana**: http://localhost:3000 (admin/admin)

## 📚 文档导航

- [📖 完整文档索引](06_Documentation/guides/)
- [🚀 快速开始](06_Documentation/guides/quick-start.md)
- [📋 教程路径](06_Documentation/tutorials/)
- [🔧 API 参考](06_Documentation/api-docs/)
- [📊 性能基准](05_Testing/benchmarks/)

## 🛠️ 工具和脚本

- **版本检查**: \`./07_Tools/scripts/version-check-2025.ps1\`
- **质量检查**: \`./07_Tools/scripts/quality-assurance-check.ps1\`
- **性能测试**: \`./07_Tools/scripts/run-comprehensive-benchmark.ps1\`
- **项目优化**: \`./07_Tools/scripts/optimize-project-structure.ps1\`

## 🤝 贡献指南

请查看 [贡献指南](10_Community/contributing/) 了解如何参与项目。

## 📄 许可证

本项目采用 MIT 许可证，详见 [LICENSE](LICENSE) 文件。

## 🙏 致谢

感谢 OpenTelemetry 社区的所有贡献者，以及以下项目的支持：

- [OpenTelemetry](https://opentelemetry.io/) - 核心项目
- [Jaeger](https://www.jaegertracing.io/) - 分布式追踪
- [Prometheus](https://prometheus.io/) - 指标监控
- [Grafana](https://grafana.com/) - 可视化

---

**项目状态**: ✅ 持续改进中  
**最后更新**: $(Get-Date -Format 'yyyy-MM-dd')  
**版本**: 2025.1.0
"@
    
    if ($DryRun) {
        Write-ColorOutput "  📝 [DRY RUN] 更新根目录 README.md" "Yellow"
    } else {
        $newReadme | Out-File -FilePath "README.md" -Encoding UTF8
        Write-ColorOutput "  📝 更新根目录 README.md" "Green"
        
        $StructureOptimization.Changes += @{
            Type = "UpdateReadme"
            Path = "README.md"
            Description = "项目根目录说明"
        }
    }
}

# 生成优化报告
function Generate-OptimizationReport {
    param([string]$OutputPath = "reports/project-structure-optimization-$(Get-Date -Format 'yyyy-MM-dd-HHmm').md")
    
    Write-ColorOutput "📊 生成项目结构优化报告..." "Cyan"
    
    $report = @"
# OTLP 2025 项目结构优化报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**优化模式**: $(if ($DryRun) { "干运行 (Dry Run)" } else { "实际执行" })
**备份路径**: $($StructureOptimization.BackupPath)

## 优化概览

本次优化重新组织了项目目录结构，提高了可维护性和可扩展性。

### 新的目录结构

\`\`\`
OTLP_2025/
├── 01_Core/                    # 核心组件和基础功能
├── 02_Implementations/         # 多语言实现
├── 03_Integrations/            # 集成和扩展
├── 04_Examples/                # 示例和教程
├── 05_Testing/                 # 测试和基准
├── 06_Documentation/           # 文档和规范
├── 07_Tools/                   # 工具和脚本
├── 08_Deployment/              # 部署和运维
├── 09_Research/                # 研究和实验
└── 10_Community/               # 社区和治理
\`\`\`

## 优化详情

### 执行的操作

"@

    # 统计操作类型
    $operationStats = @{}
    foreach ($change in $StructureOptimization.Changes) {
        if (!$operationStats.ContainsKey($change.Type)) {
            $operationStats[$change.Type] = 0
        }
        $operationStats[$change.Type]++
    }
    
    foreach ($operation in $operationStats.Keys) {
        $count = $operationStats[$operation]
        $report += "`n- **$operation**: $count 次`n"
    }
    
    $report += @"

### 详细变更记录

"@

    foreach ($change in $StructureOptimization.Changes) {
        $report += "`n- **$($change.Type)**: $($change.Path)"
        if ($change.Description) {
            $report += " - $($change.Description)"
        }
        if ($change.Source) {
            $report += " (从: $($change.Source))"
        }
        if ($change.Destination) {
            $report += " (到: $($change.Destination))"
        }
    }

    $report += @"

## 优化效果

### 改进点

1. **清晰的层次结构**: 使用数字前缀确保目录顺序
2. **功能分组**: 相关功能组织在同一目录下
3. **易于导航**: 每个目录都有明确的用途和说明
4. **可扩展性**: 新功能可以轻松添加到相应目录
5. **文档完善**: 每个目录都有详细的 README 说明

### 目录说明

- **01_Core**: 核心组件，项目的基础功能
- **02_Implementations**: 多语言实现，支持各种编程语言
- **03_Integrations**: 集成组件，扩展功能
- **04_Examples**: 示例代码，学习和参考
- **05_Testing**: 测试用例，质量保证
- **06_Documentation**: 项目文档，使用指南
- **07_Tools**: 开发工具，自动化脚本
- **08_Deployment**: 部署配置，运维支持
- **09_Research**: 研究项目，实验功能
- **10_Community**: 社区治理，贡献指南

## 使用建议

### 开发工作流

1. **新功能开发**: 在相应的功能目录下创建
2. **文档更新**: 在 06_Documentation 目录下维护
3. **测试编写**: 在 05_Testing 目录下添加
4. **工具开发**: 在 07_Tools 目录下实现

### 维护指南

1. **定期检查**: 确保目录结构的一致性
2. **文档同步**: 及时更新目录说明
3. **清理无用文件**: 定期清理过时内容
4. **备份重要数据**: 重要变更前创建备份

## 下一步计划

1. **完善文档**: 补充各目录的详细说明
2. **建立规范**: 制定目录使用规范
3. **自动化检查**: 建立结构一致性检查
4. **持续优化**: 根据使用反馈持续改进

---

*报告由 OTLP 2025 项目结构优化脚本自动生成*
"@

    # 确保报告目录存在
    $reportDir = Split-Path $OutputPath -Parent
    if (!(Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }

    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-ColorOutput "✅ 项目结构优化报告已生成: $OutputPath" "Green"
}

# 主函数
function Main {
    Write-ColorOutput "🚀 OTLP 2025 项目结构优化开始..." "Green"
    Write-ColorOutput ("=" * 60) "Gray"
    
    if ($DryRun) {
        Write-ColorOutput "🔍 运行模式: 干运行 (Dry Run)" "Yellow"
        Write-ColorOutput "💡 提示: 使用 -Backup 参数创建备份" "Yellow"
    } else {
        Write-ColorOutput "⚡ 运行模式: 实际执行" "Red"
        if (!$Backup) {
            Write-ColorOutput "⚠️ 警告: 未创建备份，建议使用 -Backup 参数" "Yellow"
        }
    }
    
    # 创建备份
    Create-Backup
    
    # 优化目录结构
    Optimize-DirectoryStructure
    
    # 重新组织现有文件
    Reorganize-ExistingFiles
    
    # 创建目录说明文件
    Create-DirectoryReadme
    
    # 更新项目根目录 README
    Update-RootReadme
    
    # 生成优化报告
    Generate-OptimizationReport
    
    # 显示总结
    Write-ColorOutput ("=" * 60) "Gray"
    Write-ColorOutput "📊 项目结构优化总结:" "White"
    Write-ColorOutput "📁 创建目录: $($StructureOptimization.Changes | Where-Object { $_.Type -like "*Directory*" } | Measure-Object).Count" "Green"
    Write-ColorOutput "📦 移动文件: $($StructureOptimization.Changes | Where-Object { $_.Type -eq "MoveFile" } | Measure-Object).Count" "Green"
    Write-ColorOutput "📝 创建文档: $($StructureOptimization.Changes | Where-Object { $_.Type -like "*Readme*" } | Measure-Object).Count" "Green"
    Write-ColorOutput "⏱️ 总耗时: $((Get-Date - $StructureOptimization.StartTime).TotalSeconds) 秒" "White"
    
    if ($StructureOptimization.BackupPath) {
        Write-ColorOutput "📦 备份路径: $($StructureOptimization.BackupPath)" "Cyan"
    }
    
    Write-ColorOutput "✅ 项目结构优化完成!" "Green"
    
    if ($DryRun) {
        Write-ColorOutput "💡 要实际执行优化，请移除 -DryRun 参数" "Yellow"
    }
}

# 执行主函数
Main
