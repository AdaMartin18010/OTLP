# OpenTelemetry 文档索引

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [快速开始](QUICK_START.md) | [教程与学习路径](TUTORIALS.md) | [故障排除](TROUBLESHOOTING.md)

## 📚 文档导航

### 🚀 快速开始

- [快速开始指南](QUICK_START.md) - 5分钟快速体验OpenTelemetry
- [教程与学习路径](TUTORIALS.md) - 完整的学习路径和实践项目

### 📖 核心文档

- [API参考](API_REFERENCE.md) - 完整的API参考文档
- [架构设计](ARCHITECTURE.md) - 系统架构和设计原理
- [术语定义](TERMS.md) - 核心概念和术语索引
- [语义约定](SEMANTIC_CONVENTIONS.md) - 标准化命名和结构规范

### 🛠️ 实践指南

- [部署指南](DEPLOYMENT_GUIDE.md) - 各种部署方式的详细指南
- [集成指南](INTEGRATION_GUIDE.md) - 与各种系统的集成方法
- [性能优化](PERFORMANCE_GUIDE.md) - 性能调优和优化策略
- [安全指南](SECURITY_GUIDE.md) - 安全配置和最佳实践
- [故障排除](TROUBLESHOOTING.md) - 常见问题

### 🎓 教育与研究

- [课程对齐](COURSE_ALIGNMENT.md) - 与大学课程的对应关系
- [形式化证明](FORMAL_PROOFS.md) - 数学理论和形式化分析

### 📊 项目状态

- [文档状态](STATUS.md) - 文档完成度和质量状态
- [格式标准](FORMAT_STANDARDS.md) - 文档格式和质量标准
- [翻译模板](TRANSLATION_TEMPLATE.md) - 多语言翻译指南和模板
- [质量报告](QUALITY_REPORT.md) - 文档质量评估和总结报告

## 🔗 相关资源

### 规范文档

- [OTLP协议概述](../spec/OTLP_OVERVIEW.md) - OTLP协议详细说明
- [分布式追踪规范](../spec/TRACES.md) - 追踪数据规范
- [指标监控规范](../spec/METRICS.md) - 指标数据规范
- [日志处理规范](../spec/LOGS.md) - 日志数据规范

### 示例代码

- [Rust示例](../examples/minimal-rust/) - Rust最小示例
- [Go示例](../examples/minimal-go/) - Go最小示例
- [Python示例](../examples/minimal-python/) - Python最小示例

### 高级示例

- [Rust高级示例](../languages/rust/) - Rust高级用法
- [Go高级示例](../languages/go/) - Go高级用法
- [Python高级示例](../languages/python/) - Python高级用法

### 配置模板

- [Collector配置](../implementations/collector/) - 各种Collector配置
- [Docker配置](../implementations/collector/compose/) - 完整栈配置

### 基准测试

- [基准测试脚本](../benchmarks/) - 性能基准测试
- [测试报告模板](../benchmarks/REPORT_TEMPLATE.md) - 标准化测试报告

### 治理框架

- [最佳实践](../governance/BEST_PRACTICES.md) - 开发最佳实践
- [变更提案模板](../governance/CHANGE_PROPOSAL_TEMPLATE.md) - 变更管理流程
- [合规检查清单](../governance/COMPLIANCE_CHECKLIST.md) - 合规性检查

### 自动化脚本

- [Collector启动脚本](../scripts/run-collector.ps1) - Collector启动
- [完整栈启动脚本](../scripts/run-compose.ps1) - 完整栈启动
- [集成测试脚本](../scripts/test-integration.ps1) - 集成测试

## 📋 学习路径

### 初学者 (0-2周)

1. 阅读 [快速开始指南](QUICK_START.md)
2. 运行最小示例
3. 学习 [术语定义](TERMS.md)
4. 理解 [架构设计](ARCHITECTURE.md)

### 进阶用户 (2-4周)

1. 学习 [API参考](API_REFERENCE.md)
2. 实践 [集成指南](INTEGRATION_GUIDE.md)
3. 运行 [基准测试](../benchmarks/)
4. 配置 [安全设置](SECURITY_GUIDE.md)

### 高级用户 (1-2个月)

1. 研究 [形式化证明](FORMAL_PROOFS.md)
2. 实践 [治理框架](../governance/)
3. 开发自定义扩展
4. 贡献社区项目

## 🎯 使用场景

### 开发环境

- [快速开始指南](QUICK_START.md) - 快速搭建开发环境
- [故障排除](TROUBLESHOOTING.md) - 解决开发中的问题

### 生产环境

- [部署指南](DEPLOYMENT_GUIDE.md) - 生产环境部署
- [性能优化](PERFORMANCE_GUIDE.md) - 生产环境优化
- [安全指南](SECURITY_GUIDE.md) - 生产环境安全

### 教学环境

- [课程对齐](COURSE_ALIGNMENT.md) - 课程设计参考
- [教程与学习路径](TUTORIALS.md) - 教学资源

### 研究环境

- [形式化证明](FORMAL_PROOFS.md) - 理论研究
- [架构设计](ARCHITECTURE.md) - 系统设计研究

## 📞 获取帮助

### 文档问题

- 检查 [故障排除](TROUBLESHOOTING.md)
- 查看 常见问题（参见 TROUBLESHOOTING.md）

### 技术问题

- 参考 [API参考](API_REFERENCE.md)
- 查看 [集成指南](INTEGRATION_GUIDE.md)

### 学习问题

- 使用 [教程与学习路径](TUTORIALS.md)
- 参考 [课程对齐](COURSE_ALIGNMENT.md)

---

*最后更新时间: 2024年12月*
*文档版本: v1.0*
*维护者: OpenTelemetry 项目团队*

### 示例

```bash
# 验证 Collector 健康检查端点
curl -s http://localhost:13133/ | head -n 1
```
