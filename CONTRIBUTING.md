# 贡献指南 / Contributing Guide

> **Language**: 中文 / 英文 (Chinese / English)

感谢您对OTLP项目的关注！我们欢迎各种形式的贡献。

Thank you for your interest in the OTLP project! We welcome contributions of all kinds.

---

## 📋 目录 / Table of Contents

- [行为准则](#行为准则--code-of-conduct)
- [如何贡献](#如何贡献--how-to-contribute)
- [报告Bug](#报告bug--reporting-bugs)
- [建议功能](#建议功能--suggesting-features)
- [提交PR](#提交pr--submitting-pull-requests)
- [文档贡献](#文档贡献--documentation-contributions)
- [代码贡献](#代码贡献--code-contributions)
- [社区](#社区--community)

---

## 行为准则 / Code of Conduct

### 中文

我们致力于为所有贡献者提供一个友好、安全和受欢迎的环境。请遵循以下原则：

- ✅ 保持尊重和友好
- ✅ 接受建设性批评
- ✅ 关注对社区最有利的事情
- ✅ 对其他社区成员表现同理心
- ❌ 使用性别化或其他不当语言
- ❌ 人身攻击或政治攻击
- ❌ 公开或私下的骚扰
- ❌ 未经许可发布他人的私人信息

### English

We are committed to providing a friendly, safe, and welcoming environment for all contributors. Please follow these principles:

- ✅ Be respectful and friendly
- ✅ Accept constructive criticism
- ✅ Focus on what's best for the community
- ✅ Show empathy towards other community members
- ❌ Use sexualized or inappropriate language
- ❌ Personal or political attacks
- ❌ Public or private harassment
- ❌ Publishing others' private information without permission

---

## 如何贡献 / How to Contribute

### 中文

有多种方式可以贡献：

1. **报告Bug**: 发现问题？请创建Bug报告
2. **建议功能**: 有好主意？请创建功能请求
3. **改进文档**: 发现文档问题？请提交修正
4. **贡献代码**: 想添加功能或修复bug？请提交PR
5. **参与讨论**: 在Discussions中分享经验和见解
6. **测试**: 测试新功能并提供反馈
7. **翻译**: 帮助翻译文档为其他语言

### English

There are several ways to contribute:

1. **Report Bugs**: Found an issue? Create a bug report
2. **Suggest Features**: Have a great idea? Create a feature request
3. **Improve Documentation**: Found a doc issue? Submit a correction
4. **Contribute Code**: Want to add features or fix bugs? Submit a PR
5. **Participate in Discussions**: Share experiences and insights in Discussions
6. **Test**: Test new features and provide feedback
7. **Translate**: Help translate documentation to other languages

---

## 报告Bug / Reporting Bugs

### 中文

在报告bug之前：

1. ✅ 检查[现有Issues](../../issues)，确保问题未被报告
2. ✅ 阅读相关文档，确认这是bug而非预期行为
3. ✅ 尝试在最新版本中复现问题

**创建Bug报告**：

1. 点击[New Issue](../../issues/new/choose)
2. 选择"🐛 Bug Report"模板
3. 填写所有必填字段
4. 提供清晰的复现步骤
5. 附上日志、错误信息或截图

### English

Before reporting a bug:

1. ✅ Check [existing Issues](../../issues) to ensure it hasn't been reported
2. ✅ Read relevant documentation to confirm it's a bug, not expected behavior
3. ✅ Try to reproduce the issue with the latest version

**Creating a Bug Report**:

1. Click [New Issue](../../issues/new/choose)
2. Select the "🐛 Bug Report" template
3. Fill in all required fields
4. Provide clear reproduction steps
5. Attach logs, error messages, or screenshots

---

## 建议功能 / Suggesting Features

### 中文

在建议新功能之前：

1. ✅ 检查[现有Issues](../../issues?q=is%3Aissue+label%3Aenhancement)
2. ✅ 在[Discussions](../../discussions)中讨论想法
3. ✅ 考虑功能与项目目标的一致性

**创建功能请求**：

1. 点击[New Issue](../../issues/new/choose)
2. 选择"✨ Feature Request"模板
3. 清晰描述问题和建议解决方案
4. 说明预期收益
5. 考虑提供实现建议

### English

Before suggesting a new feature:

1. ✅ Check [existing Issues](../../issues?q=is%3Aissue+label%3Aenhancement)
2. ✅ Discuss the idea in [Discussions](../../discussions)
3. ✅ Consider alignment with project goals

**Creating a Feature Request**:

1. Click [New Issue](../../issues/new/choose)
2. Select the "✨ Feature Request" template
3. Clearly describe the problem and proposed solution
4. Explain expected benefits
5. Consider providing implementation suggestions

---

## 提交PR / Submitting Pull Requests

### 中文

#### PR提交流程

1. **Fork仓库**

   ```bash
   # 在GitHub上Fork仓库
   # 克隆您的fork
   git clone https://github.com/YOUR_USERNAME/OTLP.git
   cd OTLP
   ```

2. **创建分支**

   ```bash
   git checkout -b feature/your-feature-name
   # 或
   git checkout -b fix/your-bug-fix
   ```

3. **进行更改**
   - 遵循项目代码风格
   - 添加必要的测试
   - 更新相关文档

4. **提交更改**

   ```bash
   git add .
   git commit -m "feat: add new feature description"
   # 或
   git commit -m "fix: fix bug description"
   ```

   **提交消息格式**：
   - `feat:` - 新功能
   - `fix:` - Bug修复
   - `docs:` - 文档更新
   - `style:` - 格式化（不影响代码逻辑）
   - `refactor:` - 重构
   - `test:` - 添加测试
   - `chore:` - 构建/工具相关

5. **推送分支**

   ```bash
   git push origin feature/your-feature-name
   ```

6. **创建Pull Request**
   - 前往GitHub上您的fork
   - 点击"New Pull Request"
   - 填写PR描述（使用PR模板）
   - 链接相关Issue（如有）

#### PR审查流程

1. 自动化测试将运行
2. 维护者将审查您的代码
3. 根据反馈进行修改
4. 获得批准后合并

### English

#### PR Submission Process

1. **Fork the Repository**

   ```bash
   # Fork the repository on GitHub
   # Clone your fork
   git clone https://github.com/YOUR_USERNAME/OTLP.git
   cd OTLP
   ```

2. **Create a Branch**

   ```bash
   git checkout -b feature/your-feature-name
   # or
   git checkout -b fix/your-bug-fix
   ```

3. **Make Changes**
   - Follow project code style
   - Add necessary tests
   - Update relevant documentation

4. **Commit Changes**

   ```bash
   git add .
   git commit -m "feat: add new feature description"
   # or
   git commit -m "fix: fix bug description"
   ```

   **Commit Message Format**:
   - `feat:` - New feature
   - `fix:` - Bug fix
   - `docs:` - Documentation update
   - `style:` - Formatting (doesn't affect code logic)
   - `refactor:` - Refactoring
   - `test:` - Adding tests
   - `chore:` - Build/tool related

5. **Push Branch**

   ```bash
   git push origin feature/your-feature-name
   ```

6. **Create Pull Request**
   - Go to your fork on GitHub
   - Click "New Pull Request"
   - Fill in PR description (use PR template)
   - Link related issues (if any)

#### PR Review Process

1. Automated tests will run
2. Maintainers will review your code
3. Make changes based on feedback
4. Merge after approval

---

## 文档贡献 / Documentation Contributions

### 中文

#### 文档类型

- **API文档**: 接口说明和示例
- **用户指南**: 使用说明和教程
- **理论文档**: 技术原理和形式化证明
- **最佳实践**: 实践经验和建议

#### 文档标准

- ✅ 使用Markdown格式
- ✅ 遵循项目文档结构
- ✅ 提供中英文双语（如可能）
- ✅ 包含代码示例（如适用）
- ✅ 使用清晰的标题和目录
- ✅ 添加适当的链接和引用

#### 文档审查清单

- [ ] 内容准确无误
- [ ] 格式符合Markdown规范
- [ ] 代码示例可运行
- [ ] 链接有效
- [ ] 图片可显示
- [ ] 中英文表述一致（如有双语）

### English

#### Documentation Types

- **API Documentation**: Interface descriptions and examples
- **User Guides**: Usage instructions and tutorials
- **Theoretical Documentation**: Technical principles and formal proofs
- **Best Practices**: Practical experiences and recommendations

#### Documentation Standards

- ✅ Use Markdown format
- ✅ Follow project documentation structure
- ✅ Provide bilingual content (if possible)
- ✅ Include code examples (if applicable)
- ✅ Use clear headings and table of contents
- ✅ Add appropriate links and references

#### Documentation Review Checklist

- [ ] Content is accurate
- [ ] Format complies with Markdown standards
- [ ] Code examples are runnable
- [ ] Links are valid
- [ ] Images are displayable
- [ ] Bilingual expressions are consistent (if bilingual)

---

## 代码贡献 / Code Contributions

### 中文

#### 代码风格

**Go**:

- 遵循[Go Code Review Comments](https://github.com/golang/go/wiki/CodeReviewComments)
- 使用`gofmt`格式化代码
- 运行`golint`检查

**Python**:

- 遵循[PEP 8](https://peps.python.org/pep-0008/)
- 使用`black`格式化代码
- 运行`pylint`检查

**Java**:

- 遵循[Google Java Style Guide](https://google.github.io/styleguide/javaguide.html)
- 使用Maven Checkstyle插件

**JavaScript/Node.js**:

- 遵循[Airbnb JavaScript Style Guide](https://github.com/airbnb/javascript)
- 使用`eslint`检查
- 使用`prettier`格式化

#### 测试要求

- ✅ 为新功能添加单元测试
- ✅ 确保所有测试通过
- ✅ 测试覆盖率≥80%（如可能）
- ✅ 添加集成测试（如适用）

#### CI/CD

- 所有PR必须通过CI检查
- 包括：构建、测试、linting、安全扫描

### English

#### Code Style

**Go**:

- Follow [Go Code Review Comments](https://github.com/golang/go/wiki/CodeReviewComments)
- Format code with `gofmt`
- Run `golint` checks

**Python**:

- Follow [PEP 8](https://peps.python.org/pep-0008/)
- Format code with `black`
- Run `pylint` checks

**Java**:

- Follow [Google Java Style Guide](https://google.github.io/styleguide/javaguide.html)
- Use Maven Checkstyle plugin

**JavaScript/Node.js**:

- Follow [Airbnb JavaScript Style Guide](https://github.com/airbnb/javascript)
- Use `eslint` for linting
- Use `prettier` for formatting

#### Testing Requirements

- ✅ Add unit tests for new features
- ✅ Ensure all tests pass
- ✅ Test coverage ≥80% (if possible)
- ✅ Add integration tests (if applicable)

#### CI/CD

- All PRs must pass CI checks
- Includes: build, test, linting, security scanning

---

## 社区 / Community

### 中文

#### 参与方式

- 💬 **GitHub Discussions**: 一般性讨论和问答
- 🐛 **Issues**: Bug报告和功能请求
- 📢 **Pull Requests**: 代码和文档贡献
- ⭐ **Star项目**: 支持项目发展
- 📣 **分享**: 向他人推荐项目

#### 获取帮助

- 查看[文档](./README.md)
- 搜索[Issues](../../issues)
- 在[Discussions](../../discussions)中提问
- 阅读[OpenTelemetry官方文档](https://opentelemetry.io/docs/)

#### 联系维护者

- 通过GitHub Issues联系
- 在Discussions中@维护者
- 查看[贡献者列表](../../graphs/contributors)

### English

#### Ways to Participate

- 💬 **GitHub Discussions**: General discussions and Q&A
- 🐛 **Issues**: Bug reports and feature requests
- 📢 **Pull Requests**: Code and documentation contributions
- ⭐ **Star the Project**: Support project development
- 📣 **Share**: Recommend the project to others

#### Getting Help

- Check the [Documentation](./README.md)
- Search [Issues](../../issues)
- Ask in [Discussions](../../discussions)
- Read [OpenTelemetry Official Docs](https://opentelemetry.io/docs/)

#### Contact Maintainers

- Contact via GitHub Issues
- @ maintainers in Discussions
- Check [Contributors List](../../graphs/contributors)

---

## 📝 总结 / Summary

### 中文

感谢您考虑为OTLP项目做出贡献！无论是报告bug、建议功能、改进文档还是贡献代码，我们都非常欢迎。

**快速链接**：

- [创建Issue](../../issues/new/choose)
- [开始讨论](../../discussions/new)
- [查看贡献者](../../graphs/contributors)

我们期待您的贡献！🎉

### English

Thank you for considering contributing to the OTLP project! Whether it's reporting bugs, suggesting features, improving documentation, or contributing code, we welcome all contributions.

**Quick Links**:

- [Create Issue](../../issues/new/choose)
- [Start Discussion](../../discussions/new)
- [View Contributors](../../graphs/contributors)

We look forward to your contributions! 🎉

---

**最后更新 / Last Updated**: 2025-10-17
**维护者 / Maintainer**: OTLP Project Team
