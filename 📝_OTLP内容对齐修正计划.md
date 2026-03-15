# OTLP内容对齐修正计划

> **计划制定**: 2026年3月16日  
> **目标**: 本项目所有内容与网络权威标准充分、最新、全面对齐  
> **策略**: 专注内容对齐，去除发布/开源任务  
> **范围**: docs/ 目录251篇文档全面检查更新

---

## 🎯 修正后目标

### ✅ 要做的 (内容对齐)
- [ ] 与官方最新标准版本对齐
- [ ] 更新所有技术文档到最新版本
- [ ] 补充缺失的新特性内容
- [ ] 修正过时/错误内容
- [ ] 统一术语和规范

### ❌ 不做 (已去除)
- [x] ~~论文发布~~ - 已去除
- [x] ~~开源发布~~ - 已去除
- [x] ~~社区推广~~ - 已去除

---

## 📊 最新权威标准版本 (2026年3月)

| 组件 | 当前版本 | 最新版本 | 差距 | 优先级 |
|:-----|:--------:|:--------:|:----:|:------:|
| **Semantic Conventions** | v1.39.0 | **v1.40.0** | -1 | 🔴 P0 |
| **OTLP Protocol** | v1.9.0 | v1.9.0 | 0 | 🟢 已对齐 |
| **Collector** | v0.147.0 | v0.147.0 | 0 | 🟢 已对齐 |
| **Declarative Config** | 未明确 | **v1.0.0稳定** | 需更新 | 🔴 P0 |
| **GenAI Semantic Conv** | v1.39 | **Development持续更新** | 需跟踪 | 🟡 P1 |
| **eBPF/OBI** | 2026目标 | 2026目标 | 需更新 | 🟡 P1 |
| **OTLP Arrow** | 开发中 | 开发中 | 需跟踪 | 🟢 已新增 |

---

## 🔴 P0 - 最高优先级 (必须对齐)

### 任务1: Semantic Conventions v1.40.0 更新

**发现差距**: 
- 当前: v1.39.0 (2025年11月)
- 最新: v1.40.0 (2026年2月)

**需要更新**:
- [ ] 创建 `版本更新日志_v1.39_to_v1.40.md`
- [ ] 更新所有引用v1.39的文档为v1.40
- [ ] 检查v1.40新增内容

**参考来源**:
- https://github.com/open-telemetry/semantic-conventions/releases/tag/v1.40.0
- https://newreleases.io/project/github/open-telemetry/opentelemetry-js/release/semconv%2Fv1.40.0

---

### 任务2: 声明式配置 (Declarative Configuration) v1.0.0

**重要发现**: 
2026年3月5日，声明式配置标记为**稳定版v1.0.0**

**需要新增/更新**:
- [ ] 创建 `docs/04_核心组件/声明式配置完整指南_v1.0.md`
- [ ] 更新Collector配置文档
- [ ] 添加JSON Schema说明

**参考来源**:
- https://opentelemetry.io/blog/2026/declarative-config-stable/

---

### 任务3: GenAI语义约定持续更新

**状态**: Development (持续更新中)

**最新发现**:
- GenAI语义约定仍在快速发展
- Agent相关约定仍在Draft阶段
- Cost tracking尚未标准化

**需要更新**:
- [ ] 更新 `docs/13_GenAI可观测性/01_GenAI语义约定完整指南.md`
- [ ] 添加Agent spans (draft)说明
- [ ] 添加Cost tracking现状说明

**参考来源**:
- https://rhesis.ai/post/tracing-agentic-applications-developers-guide
- https://oneuptime.com/blog/post/2026-02-06-monitor-llm-opentelemetry-genai-semantic-conventions/view

---

## 🟡 P1 - 重要对齐 (期望完成)

### 任务4: SDK多语言版本对齐

**检查各语言SDK最新版本**:
- [ ] Go SDK - 检查最新版本
- [ ] Python SDK - 检查最新版本
- [ ] Java SDK - 检查最新版本
- [ ] Node.js SDK - 检查最新版本

**更新内容**:
- [ ] 更新各语言SDK文档
- [ ] 更新示例代码

---

### 任务5: eBPF/OBI最新进展

**状态**: 2026目标持续跟踪

**需要更新**:
- [ ] 更新 `docs/15_eBPF自动插桩/OBI_2026年目标更新.md`
- [ ] 添加最新进展

---

### 任务6: Profiles信号完善

**状态**: OTLP v1.9.0已支持

**需要检查**:
- [ ] `docs/14_Profiles信号/` 内容完整性
- [ ] 补充生产配置示例

---

## 🟢 P2 - 持续跟踪 (可选)

### 任务7: OTLP Arrow跟踪

**状态**: 开发中

**已有文档**: `docs/12_前沿技术/OTLP_Arrow完整指南_2026.md`

**需要**: 持续跟踪最新进展

---

### 任务8: 术语统一

**检查整个docs目录**:
- [ ] 统一中英文术语
- [ ] 统一命名规范
- [ ] 统一链接格式

---

## 📅 执行时间表

### 第1天 (今天 - 3/16)

| 时间 | 任务 | 产出 |
|------|------|------|
| 2h | Semantic Conventions v1.40.0 | 更新日志文档 |
| 2h | 声明式配置v1.0.0 | 新文档 |
| 2h | GenAI更新 | 更新现有文档 |

### 第2天 (3/17)

| 时间 | 任务 | 产出 |
|------|------|------|
| 3h | SDK版本检查 | 版本对比表 |
| 3h | SDK文档更新 | 更新文档 |

### 第3天 (3/18)

| 时间 | 任务 | 产出 |
|------|------|------|
| 2h | eBPF/OBI更新 | 更新路线图 |
| 2h | Profiles检查 | 补充内容 |
| 2h | 术语统一 | 修正文档 |

---

## 📋 对齐验证清单

### 版本对齐验证

- [ ] Semantic Conventions: v1.40.0
- [ ] OTLP Protocol: v1.9.0
- [ ] Collector: v0.147.0
- [ ] Declarative Config: v1.0.0

### 内容完整性验证

- [ ] GenAI语义约定: 覆盖最新属性
- [ ] SDK文档: 覆盖4种语言
- [ ] 部署文档: 覆盖Docker/K8s
- [ ] 前沿技术: 覆盖Arrow/eBPF/Profiles

### 权威来源验证

- [ ] 所有技术内容有官方来源
- [ ] 所有版本号有官方发布链接
- [ ] 所有示例代码可验证

---

## 📚 权威来源清单

### 必须跟踪的官方源

| 来源 | URL | 检查频率 |
|:-----|:-----|:--------:|
| Semantic Conventions Releases | https://github.com/open-telemetry/semantic-conventions/releases | 每周 |
| OTLP Protocol | https://github.com/open-telemetry/opentelemetry-proto/releases | 每月 |
| Collector Releases | https://github.com/open-telemetry/opentelemetry-collector/releases | 每周 |
| OpenTelemetry Blog | https://opentelemetry.io/blog/ | 每周 |
| GenAI Conventions | https://opentelemetry.io/docs/specs/semconv/gen-ai/ | 每周 |

---

## ✅ 完成标准

### 100%对齐定义

```
✅ 版本对齐:
   - Semantic Conventions: v1.40.0
   - OTLP Protocol: v1.9.0
   - Collector: v0.147.0
   - Declarative Config: v1.0.0

✅ 内容完整:
   - 所有技术文档与官方一致
   - 所有示例代码最新可运行
   - 所有术语规范统一

✅ 权威来源:
   - 每个技术点有官方来源
   - 每个版本号可验证
   - 持续更新机制建立
```

---

**计划制定**: 2026年3月16日  
**开始执行**: 立即  
**目标完成**: 2026年3月18日

---

> 📝 **内容对齐修正计划已制定！专注内容，去除发布任务，立即开始执行！**
