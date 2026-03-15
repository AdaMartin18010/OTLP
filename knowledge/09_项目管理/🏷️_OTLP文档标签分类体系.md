# 🏷️ OTLP文档标签分类体系

> **设计目标**: 建立统一的标签系统，支持多维度检索  
> **标签维度**: 6大维度，50+标签  
> **更新日期**: 2026年3月16日

---

## 🎯 标签维度设计

```
┌─────────────────────────────────────────────────────────────┐
│                    六维标签体系                              │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│ 📚 知识维度  │ 👤 角色维度  │ 🏗️ 架构维度  │ 🔧 技术维度        │
├─────────────┼─────────────┼─────────────┼───────────────────┤
│ 理论/实践   │ 开发/运维   │ 采集/处理   │ Go/Python/Java    │
│ 基础/进阶   │ 架构/管理   │ 存储/展示   │ K8s/Docker/eBPF   │
├─────────────┼─────────────┴─────────────┴───────────────────┤
│ 📊 难度维度  │ 🏢 场景维度   │ 📅 时效维度                    │
├─────────────┼─────────────┼────────────────────────────────┤
│ 初级/中级   │ 云原生/传统 │ 稳定/前沿                      │
│ 高级/专家   │ 金融/电商   │ 实验性                         │
└─────────────┴─────────────┴────────────────────────────────┘
```

---

## 📚 D1: 知识维度标签

### 1.1 知识类型

| 标签 | 代码 | 说明 | 示例文档 |
|:-----|:----:|:-----|:---------|
| `type:theory` | 理论 | 数学基础、形式化方法 | 形式化验证框架 |
| `type:standard` | 标准 | 协议规范、语义约定 | OTLP协议概述 |
| `type:practice` | 实践 | 实战指南、案例研究 | Docker部署指南 |
| `type:reference` | 参考 | 速查手册、API文档 | Collector配置速查 |
| `type:tutorial` | 教程 | 手把手教学 | 5分钟快速入门 |

### 1.2 知识深度

| 标签 | 代码 | 适合人群 | 前置要求 |
|:-----|:----:|:---------|:---------|
| `level:beginner` | 初级 | 新手 | 无 |
| `level:intermediate` | 中级 | 有经验的开发者 | 基础概念 |
| `level:advanced` | 高级 | 专家 | 深入理解 |
| `level:expert` | 专家 | 研究人员 | 理论基础 |

### 1.3 知识领域

| 标签 | 代码 | 所属层级 | 文档数 |
|:-----|:----:|:---------|:------:|
| `domain:math` | 数学 | L1 | 4 |
| `domain:formal` | 形式化 | L1 | 16 |
| `domain:protocol` | 协议 | L2 | 6 |
| `domain:semantic` | 语义 | L2 | 27 |
| `domain:model` | 数据模型 | L2 | 39 |
| `domain:sdk` | SDK | L3 | 10 |
| `domain:collector` | Collector | L3 | 9 |
| `domain:sampling` | 采样 | L3 | 5 |
| `domain:deployment` | 部署 | L4 | 3 |
| `domain:observability` | 可观测性 | L4 | 8 |
| `domain:genai` | GenAI | L5 | 2 |
| `domain:ebpf` | eBPF | L5 | 4 |
| `domain:profiles` | Profiles | L5 | 2 |
| `domain:edge` | 边缘计算 | L5 | 1 |
| `domain:wasm` | WebAssembly | L5 | 1 |
| `domain:industry` | 行业 | L6 | 33 |

---

## 👤 D2: 角色维度标签

### 2.1 目标角色

| 标签 | 代码 | 关注点 | 推荐入口 |
|:-----|:----:|:-------|:---------|
| `role:developer` | 开发者 | SDK使用、代码集成 | L3核心实现 |
| `role:operator` | 运维 | 部署、监控、故障 | L4部署运维 |
| `role:architect` | 架构师 | 设计、选型、标准 | L2标准规范 |
| `role:researcher` | 研究员 | 理论、证明、论文 | L8学术资源 |
| `role:manager` | 管理者 | 决策、ROI、规划 | 项目仪表板 |
| `role:beginner` | 新手 | 入门、概念、示例 | 快速入门 |

### 2.2 工作场景

| 标签 | 代码 | 场景描述 |
|:-----|:----:|:---------|
| `scene:daily` | 日常运维 | 监控告警、故障处理 |
| `scene:deploy` | 部署实施 | 新环境搭建、升级 |
| `scene:optimize` | 性能优化 | 调优、成本控制 |
| `scene:develop` | 开发集成 | SDK集成、代码开发 |
| `scene:research` | 研究探索 | 新技术、论文研究 |
| `scene:troubleshoot` | 故障排查 | 问题诊断、修复 |

---

## 🏗️ D3: 架构维度标签

### 3.1 系统组件

| 标签 | 代码 | 组件说明 | 相关文档 |
|:-----|:----:|:---------|:---------|
| `comp:sdk` | SDK | 应用侧SDK | SDK实现 |
| `comp:collector` | Collector | 数据收集器 | Collector架构 |
| `comp:receiver` | Receiver | 接收器 | Receiver配置 |
| `comp:processor` | Processor | 处理器 | Processor配置 |
| `comp:exporter` | Exporter | 导出器 | Exporter配置 |
| `comp:backend` | 后端 | 存储分析 | 工具生态 |
| `comp:ui` | UI | 可视化 | Grafana集成 |

### 3.2 数据流向

| 标签 | 代码 | 流程阶段 |
|:-----|:----:|:---------|
| `flow:instrument` | 插桩 | 应用 instrumentation |
| `flow:collect` | 采集 | 数据收集 |
| `flow:process` | 处理 | 数据处理增强 |
| `flow:transmit` | 传输 | 网络传输 |
| `flow:store` | 存储 | 数据持久化 |
| `flow:analyze` | 分析 | 查询分析 |
| `flow:visualize` | 可视化 | 展示告警 |

### 3.3 信号类型

| 标签 | 代码 | 信号说明 | 文档位置 |
|:-----|:----:|:---------|:---------|
| `signal:traces` | Traces | 分布式追踪 | L2.3数据模型 |
| `signal:metrics` | Metrics | 指标 | L2.3数据模型 |
| `signal:logs` | Logs | 日志 | L2.3数据模型 |
| `signal:profiles` | Profiles | 性能剖析 | L5.3Profiles |
| `signal:baggage` | Baggage | 上下文传播 | L3.4上下文 |

---

## 🔧 D4: 技术维度标签

### 4.1 编程语言

| 标签 | 代码 | 支持状态 | 示例代码 |
|:-----|:----:|:---------|:--------:|
| `lang:go` | Go | ✅ 稳定 | 3个 |
| `lang:python` | Python | ✅ 稳定 | 3个 |
| `lang:java` | Java | ✅ 稳定 | 8个 |
| `lang:nodejs` | Node.js | ✅ 稳定 | 7个 |
| `lang:rust` | Rust | 🔄 开发中 | - |
| `lang:dotnet` | .NET | ⏳ 计划中 | - |

### 4.2 基础设施

| 标签 | 代码 | 类型 | 文档数 |
|:-----|:----:|:-----|:------:|
| `infra:docker` | Docker | 容器化 | 1 |
| `infra:kubernetes` | Kubernetes | 编排 | 1 |
| `infra:linux` | Linux | 操作系统 | 多 |
| `infra:cloud` | 云 | 云平台 | 7 |

### 4.3 相关技术

| 标签 | 代码 | 技术说明 | 热度 |
|:-----|:----:|:---------|:----:|
| `tech:ebpf` | eBPF | 内核可观测性 | 🔥🔥🔥 |
| `tech:genai` | GenAI | AI可观测性 | 🔥🔥🔥 |
| `tech:service-mesh` | Service Mesh | Istio/Linkerd | 🔥🔥 |
| `tech:wasm` | WebAssembly | Wasm插件 | 🔥 |
| `tech:serverless` | Serverless | 无服务器 | 🔥 |
| `tech:edge` | 边缘计算 | 边缘可观测 | 🔥 |

---

## 📊 D5: 难度维度标签

### 5.1 学习曲线

| 标签 | 星级 | 学习时间 | 前置知识 |
|:-----|:----:|:---------|:---------|
| `difficulty:⭐` | ⭐ | < 1小时 | 无 |
| `difficulty:⭐⭐` | ⭐⭐ | 1-4小时 | 基础概念 |
| `difficulty:⭐⭐⭐` | ⭐⭐⭐ | 1-2天 | 实践经验 |
| `difficulty:⭐⭐⭐⭐` | ⭐⭐⭐⭐ | 1周 | 深入理解 |
| `difficulty:⭐⭐⭐⭐⭐` | ⭐⭐⭐⭐⭐ | 1月+ | 专家级 |

### 5.2 实施复杂度

| 标签 | 说明 | 典型场景 |
|:-----|:-----|:---------|
| `complexity:simple` | 简单配置 | Docker Compose一键部署 |
| `complexity:medium` | 中等配置 | Kubernetes生产部署 |
| `complexity:complex` | 复杂配置 | 多集群、多租户架构 |
| `complexity:custom` | 定制开发 | 自定义Processor/Exporter |

---

## 🏢 D6: 场景维度标签

### 6.1 行业领域

| 标签 | 行业 | 案例数 | 文档位置 |
|:-----|:-----|:------:|:---------|
| `industry:finance` | 金融 | 3 | L6.2企业案例 |
| `industry:ecommerce` | 电商 | 3 | L6.2企业案例 |
| `industry:iot` | 物联网 | 2 | L6.2企业案例 |
| `industry:healthcare` | 医疗 | 1 | L6.2企业案例 |
| `industry:education` | 教育 | 1 | L6.2企业案例 |
| `industry:media` | 媒体 | 1 | L6.2企业案例 |
| `industry:manufacturing` | 制造 | 1 | L6.2企业案例 |

### 6.2 应用类型

| 标签 | 类型 | 特点 |
|:-----|:-----|:-----|
| `app:microservices` | 微服务 | 分布式追踪核心场景 |
| `app:monolith` | 单体应用 | 传统应用监控 |
| `app:serverless` | 无服务器 | Lambda/Function |
| `app:mobile` | 移动端 | App可观测性 |
| `app:iot` | IoT设备 | 边缘设备监控 |
| `app:ai` | AI应用 | LLM可观测性 |

### 6.3 部署环境

| 标签 | 环境 | 特点 |
|:-----|:-----|:-----|
| `env:onpremise` | 本地部署 | 自主可控 |
| `env:cloud` | 公有云 | 弹性扩展 |
| `env:hybrid` | 混合云 | 多云架构 |
| `env:edge` | 边缘 | 低延迟 |
| `env:k8s` | Kubernetes | 云原生 |

---

## 📅 D7: 时效维度标签

### 7.1 内容时效

| 标签 | 状态 | 维护频率 |
|:-----|:----:|:---------|
| `status:stable` | 稳定 | 按标准更新 |
| `status:active` | 活跃 | 持续更新 |
| `status:preview` | 预览 | 实验性 |
| `status:deprecated` | 废弃 | 不再维护 |

### 7.2 标准版本

| 标签 | 版本 | 更新时间 |
|:-----|:----:|:---------|
| `version:v1.9.0` | OTLP v1.9.0 | 2026-03 |
| `version:sc-v1.38.0` | SC v1.38.0 | 2026-03 |
| `version:latest` | 最新 | 实时 |

---

## 🏷️ 标签使用规范

### 文档头部标签格式

```markdown
---
tags:
  - type:tutorial
  - level:beginner
  - role:developer
  - comp:sdk
  - lang:go
  - difficulty:⭐⭐
  - status:stable
  - version:latest
---

# 文档标题
...
```

### 标签组合示例

| 文档类型 | 推荐标签组合 |
|:---------|:-------------|
| 新手入门教程 | `type:tutorial` + `level:beginner` + `role:beginner` + `difficulty:⭐` |
| Go SDK实战 | `type:practice` + `role:developer` + `lang:go` + `comp:sdk` |
| K8s生产部署 | `type:practice` + `role:operator` + `infra:kubernetes` + `difficulty:⭐⭐⭐` |
| 形式化证明 | `type:theory` + `level:expert` + `role:researcher` + `domain:formal` |
| GenAI前沿 | `type:reference` + `tech:genai` + `status:preview` + `difficulty:⭐⭐⭐⭐` |
| 金融案例 | `type:practice` + `industry:finance` + `scene:daily` |

---

## 🔍 标签检索示例

### 按角色检索
```
role:operator AND type:practice → 运维实战指南
role:developer AND lang:python → Python开发者资源
```

### 按技术检索
```
tech:ebpf AND level:intermediate → eBPF进阶文档
infra:kubernetes AND type:tutorial → K8s教程
```

### 按难度检索
```
difficulty:⭐⭐ AND status:stable → 简单稳定文档
domain:formal AND difficulty:⭐⭐⭐⭐⭐ → 形式化专家级
```

---

## 📊 标签覆盖率目标

| 维度 | 目标覆盖率 | 当前状态 |
|:-----|:----------:|:--------:|
| 知识维度 | 100% | 🟡 80% |
| 角色维度 | 100% | 🟡 70% |
| 架构维度 | 100% | 🟡 75% |
| 技术维度 | 100% | 🟡 85% |
| 难度维度 | 100% | 🟡 60% |
| 场景维度 | 100% | 🟡 65% |
| 时效维度 | 100% | 🟡 90% |

---

## 🎯 标签应用计划

### 阶段1: 核心文档打标签 (1周)
- [ ] TOP50核心文档添加标签
- [ ] 建立标签索引

### 阶段2: 全面覆盖 (2周)
- [ ] 所有L2/L3/L4文档打标签
- [ ] 建立标签云

### 阶段3: 检索系统 (1周)
- [ ] 实现标签检索功能
- [ ] 添加相关推荐

---

**标签体系版本**: v1.0  
**维护团队**: OTLP项目团队  
**扩展规则**: 新标签需评审后添加

---

> 🏷️ **用好标签，快速找到你需要的文档！**
