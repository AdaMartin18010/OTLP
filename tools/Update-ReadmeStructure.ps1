# 更新docs/README.md的版本信息和文档结构

$readmePath = "E:\_src\OTLP\docs\README.md"
$content = Get-Content -Path $readmePath -Raw -Encoding UTF8

# 更新最新日期
$content = $content -replace '最新更新: \*\*2025年10月20日\*\*', '最新更新: **2026年3月17日**'

# 更新文档数量
$content = $content -replace '文档数量: 89\+ 核心文档', '文档数量: 294 篇核心文档'

# 更新版本声明
$content = $content -replace 'OTLP v1\.9\.0 \+ Semantic Conventions v1\.40\.0', 'OTLP v1.10.0 + Semantic Conventions v1.40.0 + Collector v0.121.0'

# 更新完成度
$content = $content -replace '完成度: ✅ \*\*基础100% \+ Q4增强75%\*\*', '完成度: ✅ **7层架构100%完整**'

# 更新文档结构部分
$oldStructure = @'## 文档结构

```text
标准深度梳理_2025_10/
├── 01_OTLP核心协议/           # 协议基础
│   ├── 01_协议概述.md          (✅ 657行)
│   ├── 02_传输层_gRPC.md       (✅ 1542行)
│   ├── 03_传输层_HTTP.md       (✅ 1536行)
│   └── 04_Protocol_Buffers编码.md (✅ 1333行)
│
├── 02_Semantic_Conventions/   # 语义约定
│   ├── 00_语义约定总览.md      (✅ 874行)
│   └── 02_追踪属性/
│       ├── 01_HTTP.md          (✅ 846行)
│       ├── 02_gRPC.md          (✅ 839行)
│       └── 03_数据库.md        (✅ 808行)
│
├── 03_数据模型/               # 数据模型
│   ├── 01_Traces数据模型/
│   │   ├── 01_Span结构.md      (✅ 895行)
│   │   ├── 02_SpanContext.md   (✅ 893行)
│   │   └── 03_SpanKind.md      (✅ 1042行)
│   └── 02_Metrics数据模型/
│       └── 01_Metrics概述.md   (✅ 936行)
│
├── 04_核心组件/               # SDK和Collector
│   └── 01_SDK概述.md           (✅ 1004行)
│
├── 05_采样与性能/             # 性能优化
│   └── 01_采样策略.md          (✅ 884行)
│
├── 06_实战案例/               # 实战演练
│   └── 01_微服务追踪实战.md    (✅ 1242行)
│
├── 📅_项目里程碑时间线.md     # 项目发展历程
└── README.md                  # 本文件
```
'@

$newStructure = @'## 文档结构

采用**7层架构**组织，总计**294篇文档**：

```text
docs/
├── 00_参考资料/              # 125篇 - 快速参考、术语表、学术资源
│   ├── 01_速查手册/
│   ├── 02_术语表/
│   ├── 03_学术资源/
│   └── academic/
│
├── 01_基础理论层/            # 29篇 - 语义模型、形式化论证、演化理论
│   ├── 01_语义模型/
│   ├── 02_形式化论证/
│   └── 03_演化理论/
│
├── 02_核心协议层/            # 49篇 - 协议基础、数据模型、语义约定
│   ├── 01_协议基础/
│   ├── 11_Traces数据模型/
│   ├── 12_Metrics数据模型/
│   ├── 13_Logs数据模型/
│   ├── 14_Profiles数据模型/
│   ├── 15_共享概念/
│   └── 21_语义约定/
│
├── 03_核心实现层/            # 26篇 - SDK实现、采样策略、专项技术
│   ├── 01_SDK实现/
│   ├── 11_Collector配置/
│   ├── 21_采样策略/
│   ├── 31_eBPF自动插桩/
│   └── 32_移动端可观测性/
│
├── 04_部署运维层/            # 13篇 - 部署指南、运维管理、故障排查
│   ├── 01_部署指南/
│   ├── 11_运维管理/
│   ├── 21_故障排查/
│   ├── 31_性能优化/
│   └── 41_安全合规/
│
├── 05_应用实践层/            # 18篇 ⭐新增 - 行业案例、GenAI、微服务、Serverless
│   ├── 01_行业案例/
│   ├── 11_GenAI可观测性/
│   ├── 21_微服务实践/
│   ├── 31_Serverless实践/
│   └── 41_边缘计算/
│
├── 06_工具生态层/            # 23篇 ⭐新增 - SDK指南、工具集成、可视化、社区资源
│   ├── 01_SDK指南/
│   ├── 11_工具集成/
│   ├── 21_可视化工具/
│   └── 31_社区资源/
│
├── 07_项目管理层/            # 9篇 - 项目概览、趋势追踪、评价模型
│   ├── 01_项目概览/
│   ├── 11_趋势追踪/
│   ├── 21_评价模型/
│   ├── 31_改进计划/
│   └── 41_完成报告/
│
└── 99_归档/                  # 归档文件
```

### 最新版本对齐

| 组件 | 版本 | 状态 |
|------|------|------|
| **OTLP Protocol** | v1.10.0 | ✅ 已对齐 |
| **OpenTelemetry Specification** | v1.55.0 | ✅ 已对齐 |
| **Semantic Conventions** | v1.40.0 | ✅ 已对齐 |
| **Collector** | v0.121.0 | ✅ 已对齐 |
'@

$content = $content -replace [regex]::Escape($oldStructure), $newStructure

# 保存文件
Set-Content -Path $readmePath -Value $content -Encoding UTF8
Write-Host "✅ README.md 已更新" -ForegroundColor Green
