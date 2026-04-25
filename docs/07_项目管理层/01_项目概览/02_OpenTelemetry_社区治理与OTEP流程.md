# OpenTelemetry 社区治理与 OTEP 流程

> **标准来源**: OpenTelemetry Community Governance + OTEP Repository
> **核心目标**: 系统介绍 OpenTelemetry 的治理结构、决策流程和 OTEP 提案机制，帮助中文社区贡献者参与国际社区

---

## 一、治理结构概览

### 1.1 组织架构

```text
OpenTelemetry 治理层次:

┌─────────────────────────────────────────┐
│  CNCF (Cloud Native Computing Foundation)│
│  └── 提供商标、法律、营销支持            │
└─────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────┐
│  Governance Committee (GC)              │
│  ├── 职责: 项目战略方向、品牌、法律、合规  │
│  ├── 成员: 7-11 人，来自不同厂商         │
│  └── 选举: 年度社区选举                  │
└─────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────┐
│  Technical Committee (TC)               │
│  ├── 职责: 技术架构决策、规范审批        │
│  ├── 成员: 5-7 人，资深技术专家          │
│  └── 任命: GC 任命                       │
└─────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────┐
│  Special Interest Groups (SIGs)         │
│  ├── 按技术领域划分的工作组              │
│  ├── 公开会议，社区自由参与              │
│  └── 决策: 基于共识（lazy consensus）    │
└─────────────────────────────────────────┘
```

### 1.2 关键 SIGs 介绍

| SIG 名称 | 职责范围 | 会议频率 |
|---------|---------|---------|
| **Specification** | 规范定义与演进 | 每周 |
| **Collector** | Collector 架构与实现 | 每周 |
| **Metrics** | 指标数据模型与 SDK | 每两周 |
| **Logs** | 日志数据模型与 SDK | 每两周 |
| **Semantic Conventions** | 语义约定定义 | 每周 |
| **Instrumentation** | 自动插桩库 | 每周 |
| **Agent Management (OpAMP)** | 代理管理协议 | 每两周 |
| **Security** | 安全审查与最佳实践 | 每月 |
| **Communications** | 文档、网站、社区运营 | 每两周 |

---

## 二、OTEP 流程详解

### 2.1 什么是 OTEP？

OTEP（OpenTelemetry Enhancement Proposal）是 OpenTelemetry 的 RFC 机制，用于 propose 跨语言、跨实现的重大变更。

```text
OTEP 适用场景:
├── 新增 API 或 SDK 功能
├── 修改数据模型或协议
├── 引入新的信号类型（如 Entity）
├── 变更可扩展性要求
└── 跨 SIG 的架构决策

不适用场景:
├── Bug 修复
├── 文档 typo 修正
├── 单一语言实现的内部重构
└── 不影响其他实现的变更
```

### 2.2 OTEP 生命周期

```text
OTEP 生命周期:

1. 构思 (Idea)
   ├── 在 SIG 会议或 Slack 中讨论想法
   └── 收集初步反馈

2. 起草 (Draft)
   ├── 在 oteps 仓库提交 PR
   ├── 使用模板: text/0000-template.md
   └── 分配临时编号（如 0000-my-proposal.md）

3. 评审 (Review)
   ├── 社区讨论（通常 2-4 周）
   ├── 根据反馈修改
   └── 需要至少 2 名 TC 成员或 SIG 维护者批准

4. 接受 (Accepted)
   ├── 分配正式编号（如 0256-entities-data-model.md）
   └── 进入实施阶段

5. 实施 (Implementing)
   ├── 在对应仓库提交实现 PR
   ├── 规范更新 PR 进入 opentelemetry-specification
   └── 实现与规范同步更新

6. 完成 (Implemented)
   ├── 规范合并
   ├── 参考实现完成
   └── OTEP 状态标记为 Implemented

7. 废弃 (Deprecated/Superseded)
   └── 如有新 OTEP 替代，标记为 Superseded
```

### 2.3 OTEP 模板结构

```markdown
# OTEP-XXXX: 标题

## 背景
说明问题和动机

## 目标
明确本提案要解决的问题

## 详细设计
技术细节、API 变更、数据模型

## 替代方案
考虑过但放弃的其他方案

## 影响分析
对性能、兼容性、生态的影响

## 实现计划
时间表和里程碑

## 开放问题
尚未解决的问题
```

---

## 三、如何参与社区

### 3.1 新贡献者入门路径

```text
入门路径:

第1步: 加入社区
├── 加入 OpenTelemetry Slack (cloud-native.slack.com #opentelemetry)
├── 订阅邮件列表 (opentelemetry-community Google Group)
└── 关注 GitHub 组织 (github.com/open-telemetry)

第2步: 选择兴趣领域
├── 查看 SIG 日历 (opentelemetry.io/community)
├── 参加感兴趣的 SIG 会议
└── 阅读 SIG 的 README 和贡献指南

第3步: 从小任务开始
├── 标记 "good first issue" 的 issue
├── 文档改进、测试用例补充
└── 单一语言 SDK 的 bug 修复

第4步: 深入参与
├── 参与代码审查
├── 提交 OTEP 草案
└── 成为 SIG 成员或维护者
```

### 3.2 中文社区参与建议

| 挑战 | 建议 |
|------|------|
| 语言障碍 | 会议有录音和纪要，可先阅读再参与；关键提案可书面反馈 |
| 时差问题 | SIG 会议多在美西时间上午（北京时间凌晨），优先参与异步讨论（GitHub、Slack）|
| 技术深度 | 从 Semantic Conventions 或 Documentation 切入，门槛相对较低 |
| 文化差异 | 国际社区强调"书面记录"，重要观点建议通过 GitHub issue/PR 表达 |

---

## 四、决策机制

### 4.1 Lazy Consensus

OpenTelemetry 采用**惰性共识**决策模式：

```text
Lazy Consensus 原则:
├── 提案公开讨论一段时间（通常 1-2 周）
├── 如果没有明确的反对意见，视为达成共识
├── 反对意见必须是"可解决的技术问题"而非个人偏好
├── 如有重大分歧，升级至 TC 或 GC 裁决
└── 所有决策过程在 GitHub 上公开留痕
```

### 4.2 投票机制

| 决策类型 | 投票门槛 | 参与者 |
|---------|---------|--------|
| OTEP 接受 | 2 名 TC/SIG 维护者批准 | TC 成员、SIG 维护者 |
| 规范变更 | Lazy Consensus 或简单多数 | 规范贡献者 |
| 新 SIG 成立 | GC 批准 | GC |
| 重大架构变更 | TC 多数批准 | TC |
| 版本发布 | 发布经理批准 | 发布团队 |

---

## 五、参考资源

- OpenTelemetry Community Repository: github.com/open-telemetry/community
- OTEP Repository: github.com/open-telemetry/oteps
- OpenTelemetry Governance Charter
- CNCF Code of Conduct

---

> **总结**: OpenTelemetry 是一个开放、透明、社区驱动的项目。理解其治理结构（GC → TC → SIG）和 OTEP 流程，是有效参与社区贡献的前提。对于中文开发者，建议从文档贡献和 Semantic Conventions 讨论切入，逐步深入到核心技术领域。
