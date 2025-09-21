# OpenTelemetry 文档翻译模板

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [格式标准](FORMAT_STANDARDS.md) | [文档状态](STATUS.md) | [快速开始](QUICK_START.md)

## 翻译指南

### 翻译原则

1. **准确性**: 保持技术术语的准确性，避免歧义
2. **一致性**: 统一术语翻译，保持整个文档的一致性
3. **可读性**: 符合目标语言的表达习惯
4. **完整性**: 确保所有内容都被翻译，不遗漏任何信息

### 术语对照表

| 英文术语 | 中文翻译 | 说明 |
|----------|----------|------|
| OpenTelemetry | OpenTelemetry | 保持原名 |
| OTLP | OTLP | 保持原名 |
| Trace | 追踪/分布式追踪 | 根据上下文选择 |
| Span | Span | 保持原名 |
| Metrics | 指标 | 统一使用"指标" |
| Logs | 日志 | 统一使用"日志" |
| Collector | 收集器 | 统一使用"收集器" |
| SDK | SDK | 保持原名 |
| Instrumentation | 检测/埋点 | 根据上下文选择 |
| Sampling | 采样 | 统一使用"采样" |
| Export | 导出 | 统一使用"导出" |
| Import | 导入 | 统一使用"导入" |
| Configuration | 配置 | 统一使用"配置" |
| Deployment | 部署 | 统一使用"部署" |
| Integration | 集成 | 统一使用"集成" |
| Performance | 性能 | 统一使用"性能" |
| Security | 安全 | 统一使用"安全" |
| Troubleshooting | 故障排除 | 统一使用"故障排除" |

### 代码示例翻译

#### 注释翻译

```go
// 创建Tracer - Create Tracer
tracer := otel.Tracer("service-name")

// 创建Span - Create Span
ctx, span := tracer.Start(ctx, "operation-name")
defer span.End()

// 设置属性 - Set Attributes
span.SetAttributes(
    attribute.String("key", "value"),
    attribute.Int("number", 42),
)
```

#### 变量名翻译

```python
# 服务名称 - Service Name
service_name = "my-service"

# 端点地址 - Endpoint Address
endpoint = "http://localhost:4317"

# 配置参数 - Configuration Parameters
config_params = {
    "timeout": 30,
    "retries": 3
}
```

### 文档结构翻译

#### 标题翻译

```markdown
# OpenTelemetry API 参考 - OpenTelemetry API Reference

## 核心API - Core APIs

### 1. Tracer API

#### 创建Tracer - Creating Tracer
```

#### 列表翻译

```markdown
**功能特性** - **Features**:
- 分布式追踪 - Distributed Tracing
- 指标监控 - Metrics Monitoring  
- 日志收集 - Log Collection
- 上下文传播 - Context Propagation
```

### 翻译检查清单

#### 内容检查

- [ ] 所有文本都已翻译
- [ ] 技术术语使用正确
- [ ] 代码注释已翻译
- [ ] 链接地址正确
- [ ] 图片说明已翻译

#### 格式检查

- [ ] 标题层级正确
- [ ] 代码块语言标记正确
- [ ] 表格格式正确
- [ ] 列表格式统一
- [ ] 链接格式标准

#### 质量检查

- [ ] 语言表达自然
- [ ] 技术概念准确
- [ ] 上下文连贯
- [ ] 无语法错误
- [ ] 无拼写错误

### 翻译工具推荐

#### 在线工具

- [Google Translate](https://translate.google.com/) - 基础翻译
- [DeepL](https://www.deepl.com/) - 高质量翻译
- [百度翻译](https://fanyi.baidu.com/) - 中文翻译

#### 本地工具

- [OmegaT](https://omegat.org/) - 开源翻译工具
- [Trados](https://www.trados.com/) - 专业翻译软件
- [MemoQ](https://www.memoq.com/) - 翻译管理工具

#### 编辑器插件

- [VS Code 翻译插件](https://marketplace.visualstudio.com/items?itemName=MS-CEINTL.vscode-language-pack-zh-hans)
- [IntelliJ IDEA 中文语言包](https://plugins.jetbrains.com/plugin/13710-chinese-simplified-language-pack----)

### 翻译工作流程

#### 1. 准备阶段

1. 阅读原文，理解技术概念
2. 准备术语对照表
3. 设置翻译环境
4. 创建翻译分支

#### 2. 翻译阶段

1. 逐段翻译内容
2. 保持代码示例不变
3. 翻译注释和说明
4. 检查术语一致性

#### 3. 检查阶段

1. 自我检查翻译质量
2. 技术准确性验证
3. 格式和链接检查
4. 语言表达优化

#### 4. 发布阶段

1. 提交翻译内容
2. 代码审查
3. 测试验证
4. 发布更新

### 多语言支持结构

```text
docs/
├── en/                    # 英文文档
│   ├── QUICK_START.md
│   ├── API_REFERENCE.md
│   └── ...
├── zh/                    # 中文文档
│   ├── QUICK_START.md
│   ├── API_REFERENCE.md
│   └── ...
├── ja/                    # 日文文档
│   ├── QUICK_START.md
│   ├── API_REFERENCE.md
│   └── ...
└── ko/                    # 韩文文档
    ├── QUICK_START.md
    ├── API_REFERENCE.md
    └── ...
```

### 翻译质量保证

#### 自动化检查

- 术语一致性检查
- 链接有效性检查
- 格式标准检查
- 完整性检查

#### 人工审核

- 技术准确性审核
- 语言质量审核
- 用户体验审核
- 文化适应性审核

### 贡献指南

#### 如何参与翻译

1. Fork 项目仓库
2. 选择要翻译的文档
3. 创建翻译分支
4. 按照翻译指南进行翻译
5. 提交 Pull Request

#### 翻译要求

- 具备相关技术背景
- 熟悉目标语言
- 遵循翻译标准
- 积极参与讨论

### 维护更新

#### 定期更新

- 跟随原文更新
- 术语对照表更新
- 翻译质量改进
- 用户反馈处理

#### 版本管理

- 翻译版本号
- 更新日志
- 变更记录
- 回滚机制

---

*最后更新时间: 2024年12月*
*维护者: OpenTelemetry 翻译团队*
