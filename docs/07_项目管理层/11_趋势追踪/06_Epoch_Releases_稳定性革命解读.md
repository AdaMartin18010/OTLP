# Epoch Releases 与 stable-by-default 趋势解读

> **标准来源**: OpenTelemetry Stability Proposal (2025-11) + Governance Committee 博客
> **分析性质**: 趋势追踪与影响评估
> **核心目标**: 从项目管理和用户 adoption 的角度，解读稳定性革命对生态的影响

---

## 一、事件回顾

### 1.1 Stability Proposal 发布

2025 年 11 月，OpenTelemetry 治理委员会发布 Stability Proposal，标志着项目从"高速创新"转向"稳定交付"。这不是技术变更，而是**发布哲学和组织文化**的变革。

### 1.2 核心要点

```text
三大支柱:
├── stable-by-default: 默认仅启用稳定功能
├── Epoch Releases: 定期发布经过验证的组合包
└── Stabilization Criteria: 统一的稳定化标准

影响范围:
├── 最终用户: 升级更安全、更可预测
├── 平台工程师: 组件组合更可靠
├── 库作者: 稳定化路径更清晰
├── 厂商: 兼容性声明更标准化
└── 社区贡献者: 代码审查更严格
```

---

## 二、对各类用户的影响评估

### 2.1 最终用户（应用开发者）

| 维度 | 过去 | 未来 |
|------|------|------|
| 功能发现 | 实验性功能默认可见，容易误用 | 实验性功能需显式启用，降低误用风险 |
| 升级信心 | 小版本可能引入意外变更 | Epoch Release 提供更高置信度 |
| 文档质量 | 各组件文档版本不一致 | Epoch 提供文档快照，一致性提升 |
| 问题排查 | 难以判断是 bug 还是预期变更 | 稳定性等级帮助定位问题性质 |

### 2.2 平台工程师 / SRE

| 维度 | 过去 | 未来 |
|------|------|------|
| 升级节奏 | 每月评估多个组件更新 | 每季度评估一个 Epoch 更新 |
| 兼容性验证 | 自行验证多组件组合 | Epoch 已预验证 |
| 回滚策略 | 各组件独立回滚，状态复杂 | Epoch 整体回滚，状态一致 |
| 安全补丁 | 跟踪数十个组件公告 | Epoch 提供统一安全更新通道 |

### 2.3 可观测性厂商

| 维度 | 过去 | 未来 |
|------|------|------|
| 兼容性声明 | 模糊，难以量化 | 可声明"支持 Epoch 2026.2" |
| 功能支持 | 需测试所有组合 | 只需测试 Epoch 组合 |
| 客户支持 | 面对大量版本组合问题 | 版本矩阵简化，支持成本降低 |

---

## 三、生态反应

### 3.1 云厂商响应

| 云厂商 | 响应动作 |
|--------|---------|
| **AWS** | ADOT 计划对齐 Epoch Release，提供稳定的 Collector 发行版 |
| **Google Cloud** | Managed OpenTelemetry for GKE 承诺基于 Epoch 发布 |
| **Microsoft Azure** | Azure Monitor OpenTelemetry Distro 计划提供 Epoch 兼容版本 |
| **Datadog** | 声明支持 OpenTelemetry Epoch Releases，简化集成测试 |
| **Honeycomb** | 欢迎稳定性改进，认为将降低用户入门门槛 |

### 3.2 社区项目响应

```text
积极跟进的项目:
├── OpenTelemetry Operator (K8s): 计划支持 Epoch 版本管理
├── OpenTelemetry Helm Charts: 提供 Epoch 版本锁定选项
├── OpenTelemetry Demo: 将基于最新 Epoch 构建
└── OpenTelemetry Collector Contrib: 按稳定性等级标记组件

观望中的项目:
├── 部分小众语言 SDK: 资源有限，跟进速度可能较慢
└── 社区 Instrumentation 库: 稳定化标准尚未完全落地
```

---

## 四、对本项目的影响

### 4.1 文档策略调整

| 当前策略 | 建议调整 |
|---------|---------|
| 跟踪每个组件的最新版本 | 增加 Epoch Release 作为文档基线 |
| 所有功能同等深度覆盖 | 按稳定性等级差异化覆盖 |
| 版本更新以组件为单位 | 版本更新以 Epoch 为单位 |

### 4.2 具体行动

- [ ] 在版本对齐检查清单中增加 Epoch Release 跟踪项
- [ ] 在文档中标注内容的稳定性等级（Stable/Experimental/Development）
- [ ] 优先覆盖 Stable 内容，Experimental 内容标注风险
- [ ] 当首个 Epoch Release 发布时，发布专项解读文档

---

## 五、风险与不确定性

| 风险 | 可能性 | 影响 | 缓解措施 |
|------|--------|------|---------|
| Epoch Release 延迟 | 中 | 中 | 继续跟踪组件独立版本 |
| 社区资源不足 | 中 | 高 | 鼓励企业贡献者参与 Release SIG |
| 与现有发行版冲突 | 低 | 高 | Epoch Release 不替代组件独立发布 |
| 用户误解 Epoch 为强制 | 中 | 低 | 文档明确说明 Epoch 是推荐而非强制 |

---

## 六、参考资源

- OpenTelemetry Stability Proposal Blog (2025-11)
- OpenTelemetry Governance Committee 会议纪要
- OpenTelemetry Roadmap

---

> **总结**: Epoch Releases 和 stable-by-default 是 OpenTelemetry 迈向企业级成熟的关键一步。对于本项目而言，这意味着文档基线将从"组件版本"升级为"Epoch 版本"，内容覆盖策略需要按稳定性等级差异化处理。建议密切关注首个 Epoch Release 的发布动态，并准备相应的解读和迁移指南。
