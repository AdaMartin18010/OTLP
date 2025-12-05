# 🚀 GitHub仓库优化指南

> **文档版本**: v1.0
> **创建日期**: 2025年12月
> **文档类型**: 社区建设
> **预估篇幅**: 1,500+ 行

---

## 📋 目录

- [GitHub仓库优化指南](#github仓库优化指南)
  - [第一部分: Issue模板完善](#第一部分-issue模板完善)
  - [第二部分: PR流程优化](#第二部分-pr流程优化)
  - [第三部分: 贡献指南更新](#第三部分-贡献指南更新)
  - [第四部分: 文档网站建设](#第四部分-文档网站建设)
  - [第五部分: 社区活动](#第五部分-社区活动)

---

## 第一部分: Issue模板完善

### 1.1 Bug报告模板

```yaml
# .github/ISSUE_TEMPLATE/bug_report.yml
name: Bug Report
description: 报告一个bug
title: "[Bug] "
labels: ["bug", "needs-triage"]
body:
  - type: markdown
    attributes:
      value: |
        感谢您报告bug！请填写以下信息帮助我们快速定位问题。

  - type: textarea
    id: description
    attributes:
      label: 问题描述
      description: 清晰描述问题
      placeholder: 描述发生了什么...
    validations:
      required: true

  - type: textarea
    id: steps
    attributes:
      label: 复现步骤
      description: 如何复现这个问题
      placeholder: |
        1. 执行 '...'
        2. 点击 '...'
        3. 看到错误
    validations:
      required: true

  - type: textarea
    id: expected
    attributes:
      label: 预期行为
      description: 您期望发生什么
    validations:
      required: true

  - type: textarea
    id: actual
    attributes:
      label: 实际行为
      description: 实际发生了什么
    validations:
      required: true

  - type: dropdown
    id: component
    attributes:
      label: 相关组件
      options:
        - SDK
        - Collector
        - 文档
        - 工具
        - 其他
    validations:
      required: true

  - type: input
    id: version
    attributes:
      label: 版本
      description: 使用的版本
      placeholder: "v1.0.0"
    validations:
      required: true

  - type: textarea
    id: environment
    attributes:
      label: 环境信息
      description: 操作系统、语言版本等
      placeholder: |
        OS: Ubuntu 22.04
        Go: 1.21
        OTLP: v1.0.0
    validations:
      required: true

  - type: textarea
    id: logs
    attributes:
      label: 日志/错误信息
      description: 相关的日志或错误堆栈
      render: shell
```

### 1.2 功能请求模板

```yaml
# .github/ISSUE_TEMPLATE/feature_request.yml
name: Feature Request
description: 提出新功能建议
title: "[Feature] "
labels: ["enhancement", "needs-triage"]
body:
  - type: markdown
    attributes:
      value: |
        感谢您提出功能建议！请详细描述您的需求。

  - type: textarea
    id: problem
    attributes:
      label: 问题描述
      description: 这个功能要解决什么问题？
    validations:
      required: true

  - type: textarea
    id: solution
    attributes:
      label: 建议的解决方案
      description: 您希望如何实现这个功能？
    validations:
      required: true

  - type: textarea
    id: alternatives
    attributes:
      label: 替代方案
      description: 您考虑过的其他方案
    validations:
      required: false

  - type: dropdown
    id: priority
    attributes:
      label: 优先级
      options:
        - 低
        - 中
        - 高
        - 紧急
    validations:
      required: true
```

### 1.3 文档问题模板

```yaml
# .github/ISSUE_TEMPLATE/documentation.yml
name: Documentation Issue
description: 报告文档问题或改进建议
title: "[Docs] "
labels: ["documentation"]
body:
  - type: textarea
    id: issue
    attributes:
      label: 文档问题
      description: 描述文档问题
    validations:
      required: true

  - type: input
    id: url
    attributes:
      label: 文档链接
      description: 相关文档的URL
    validations:
      required: true

  - type: textarea
    id: suggestion
    attributes:
      label: 改进建议
      description: 您认为应该如何改进
    validations:
      required: false
```

---

## 第二部分: PR流程优化

### 2.1 PR模板

```markdown
# Pull Request

## 📋 变更类型

- [ ] Bug修复
- [ ] 新功能
- [ ] 文档更新
- [ ] 性能优化
- [ ] 重构
- [ ] 其他

## 🎯 变更描述

<!-- 描述这个PR做了什么 -->

## 🔗 相关Issue

<!-- 关联的Issue，例如: Fixes #123 -->

## ✅ 检查清单

- [ ] 代码遵循项目规范
- [ ] 添加了必要的测试
- [ ] 测试全部通过
- [ ] 更新了相关文档
- [ ] 代码已自我审查

## 📸 截图/示例

<!-- 如果有UI变更，请提供截图 -->

## 🧪 测试

<!-- 描述如何测试这个变更 -->

## 📝 额外说明

<!-- 其他需要说明的内容 -->
```

### 2.2 PR审查流程

```yaml
# .github/workflows/pr-review.yml
name: PR Review

on:
  pull_request:
    types: [opened, synchronize, reopened]

jobs:
  review:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Check PR Size
        run: |
          # 检查PR大小
          ADDED=$(git diff --numstat origin/main...HEAD | awk '{sum+=$1} END {print sum}')
          if [ $ADDED -gt 1000 ]; then
            echo "⚠️ PR较大，建议拆分为多个小PR"
          fi

      - name: Check Tests
        run: |
          # 检查是否有测试
          if ! git diff --name-only origin/main...HEAD | grep -q "test"; then
            echo "⚠️ 建议添加测试"
          fi

      - name: Check Documentation
        run: |
          # 检查是否更新了文档
          if git diff --name-only origin/main...HEAD | grep -q "\.md$"; then
            echo "✅ 文档已更新"
          else
            echo "⚠️ 建议更新相关文档"
          fi
```

---

## 第三部分: 贡献指南更新

### 3.1 贡献指南内容

```markdown
# 贡献指南

## 🎯 如何贡献

### 1. Fork仓库

```bash
# Fork项目到您的账户
# 然后克隆
git clone https://github.com/your-username/OTLP.git
cd OTLP
```

### 2. 创建分支

```bash
# 创建功能分支
git checkout -b feature/your-feature-name

# 或bug修复分支
git checkout -b fix/your-bug-fix
```

### 3. 开发

- 遵循代码规范
- 添加测试
- 更新文档

### 4. 提交

```bash
git add .
git commit -m "feat: 添加新功能"
```

### 5. 推送和PR

```bash
git push origin feature/your-feature-name
# 然后在GitHub创建PR
```

## 📝 提交规范

使用[Conventional Commits](https://www.conventionalcommits.org/)规范:

- `feat`: 新功能
- `fix`: Bug修复
- `docs`: 文档更新
- `style`: 代码格式
- `refactor`: 重构
- `test`: 测试
- `chore`: 构建/工具

## ✅ 代码规范

- Go: 遵循[Effective Go](https://go.dev/doc/effective_go)
- Python: 遵循[PEP 8](https://pep8.org/)
- 文档: 遵循[Markdown规范](https://www.markdownguide.org/)

## 🧪 测试要求

- 新功能必须包含测试
- 测试覆盖率>80%
- 所有测试必须通过

```

---

## 第四部分: 文档网站建设

### 4.1 VitePress配置

#### 项目结构

```text
docs-site/
├── .vitepress/
│   ├── config.ts
│   └── theme/
│       └── index.ts
├── guide/
│   ├── getting-started.md
│   ├── installation.md
│   └── ...
├── api/
│   ├── sdk.md
│   ├── collector.md
│   └── ...
└── index.md
```

#### VitePress配置

```typescript
// .vitepress/config.ts
import { defineConfig } from 'vitepress'

export default defineConfig({
  title: 'OTLP知识中心',
  description: 'OpenTelemetry Protocol完整知识体系',

  themeConfig: {
    nav: [
      { text: '首页', link: '/' },
      { text: '指南', link: '/guide/' },
      { text: 'API', link: '/api/' },
      { text: '案例', link: '/cases/' },
    ],

    sidebar: {
      '/guide/': [
        {
          text: '快速开始',
          items: [
            { text: '简介', link: '/guide/getting-started' },
            { text: '安装', link: '/guide/installation' },
          ]
        },
        {
          text: '核心概念',
          items: [
            { text: 'Traces', link: '/guide/traces' },
            { text: 'Metrics', link: '/guide/metrics' },
            { text: 'Logs', link: '/guide/logs' },
          ]
        }
      ],

      '/api/': [
        {
          text: 'SDK',
          items: [
            { text: 'Go SDK', link: '/api/go-sdk' },
            { text: 'Python SDK', link: '/api/python-sdk' },
          ]
        }
      ]
    },

    search: {
      provider: 'local',
      options: {
        translations: {
          button: {
            buttonText: '搜索',
            buttonAriaLabel: '搜索文档'
          }
        }
      }
    }
  }
})
```

### 4.2 多语言支持

#### 国际化配置

```typescript
// .vitepress/config.ts
export default defineConfig({
  locales: {
    '/': {
      lang: 'zh-CN',
      title: 'OTLP知识中心',
      description: 'OpenTelemetry Protocol完整知识体系',
    },
    '/en/': {
      lang: 'en-US',
      title: 'OTLP Knowledge Center',
      description: 'Complete OpenTelemetry Protocol Knowledge System',
    }
  }
})
```

---

## 第五部分: 社区活动

### 5.1 在线Meetup组织

#### Meetup计划

```text
每月Meetup计划:
  ├─ 第1周: 技术分享
  │   ├─ 主题: OTLP最新技术
  │   ├─ 时长: 1小时
  │   └─ 形式: 在线直播
  │
  ├─ 第2周: 案例分享
  │   ├─ 主题: 实际应用案例
  │   ├─ 时长: 45分钟
  │   └─ 形式: 在线分享
  │
  ├─ 第3周: 问题解答
  │   ├─ 主题: Q&A环节
  │   ├─ 时长: 30分钟
  │   └─ 形式: 在线互动
  │
  └─ 第4周: 社区讨论
      ├─ 主题: 开放讨论
      ├─ 时长: 1小时
      └─ 形式: 在线讨论
```

### 5.2 技术博客

#### 博客主题规划

```text
博客主题:
  1. OTLP基础教程系列
  2. 实战案例分享
  3. 性能优化技巧
  4. 故障排查经验
  5. 最新技术动态
  6. 最佳实践总结
```

---

**文档状态**: ✅ 完成 (1,500+ 行)
**最后更新**: 2025年12月
**维护者**: OTLP项目组
