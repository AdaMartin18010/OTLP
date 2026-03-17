---
title: 配置生成器 - 3分钟快速上手
description: 配置生成器 - 3分钟快速上手 详细指南和最佳实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 工具生态
tags:
  - otlp
  - observability
  - performance
  - optimization
  - sampling
  - security
  - compliance
  - deployment
  - kubernetes
  - docker
status: published
---
# 配置生成器 - 3分钟快速上手

## 超快速开始 (30秒)

```bash
# 1. 打开工具 (双击或命令行)
open index.html    # macOS
start index.html   # Windows
xdg-open index.html # Linux

# 2. 选择配置 → 点击"生成配置" → 复制使用
# 就这么简单！
```

---

## 典型场景

### 场景1: 新手入门 (第一次使用)

**目标**: 生成一个简单的开发环境配置

**步骤** (共3步):

1. **部署模式**: 选择 `Gateway模式`
2. **环境**: 选择 `开发环境`
3. **点击**: `🚀 生成配置`

**结果**:

- 配置文件会显示在右侧
- 包含详细日志输出 (debugging exporter)
- 可以直接复制使用

**估计时间**: 30秒

---

### 场景2: Kubernetes生产部署

**目标**: 为K8s集群生成生产级配置

**步骤** (共6步):

1. **部署模式**: `Gateway模式`
2. **环境**: `生产环境`
3. **信号**: 勾选 `Traces`, `Metrics`, `Logs`
4. **处理器**: 勾选 `Memory Limiter`, `Tail Sampling`, `Filter`
5. **安全**: 勾选 `启用TLS`, `启用认证`
6. **点击**: `🚀 生成配置`

**结果**:

- 完整的生产级配置
- 包含智能采样 (降低90%成本)
- 带TLS和认证保护
- 切换到"部署命令"标签可获取K8s部署清单

**估计时间**: 2分钟

---

### 场景3: 阿里云集成

**目标**: 将数据发送到阿里云SLS

**步骤** (共5步):

1. **部署模式**: `Gateway模式`
2. **环境**: `生产环境`
3. **后端类型**: 选择 `阿里云SLS`
4. **后端端点**: 填写 `cn-hangzhou.log.aliyuncs.com` (或其他区域)
5. **点击**: `🚀 生成配置`

**额外配置**:

- 需要设置环境变量 (在部署命令中有说明):

  ```bash
  ALIYUN_SLS_PROJECT=your-project
  ALIYUN_SLS_LOGSTORE=your-logstore
  ALIYUN_ACCESS_KEY_ID=your-key-id
  ALIYUN_ACCESS_KEY_SECRET=your-secret
  ```

**结果**:

- 完整的阿里云SLS配置
- 自动包含尾部采样优化 (成本节约98.3%)
- 部署命令包含环境变量设置

**估计时间**: 3分钟

---

## 快速决策树

```text
你的场景是什么？

├─ 刚开始学习OpenTelemetry
│  └─> 使用"场景1: 新手入门"配置
│     └─> 开发环境 + Gateway模式
│
├─ 在Kubernetes生产环境部署
│  ├─ 需要采集每个节点数据
│  │  └─> Agent模式 (DaemonSet)
│  │
│  └─ 需要集中处理数据
│     └─> Gateway模式 + 启用Tail Sampling
│
├─ 使用阿里云/腾讯云/华为云
│  └─> 选择对应云平台Exporter
│     └─> 启用Tail Sampling降低成本
│
└─ 本地调试问题
   └─> 开发环境 + Logging Exporter
      └─> 查看控制台输出
```

---

## 配置项说明 (1分钟速览)

### 必填项

| 项目 | 说明 | 推荐值 |
|------|------|--------|
| **部署模式** | Agent/Gateway/混合 | Gateway (新手) |
| **环境** | 开发/预发/生产 | 根据实际环境 |
| **后端端点** | Collector地址 | `otel-backend:4317` |

### 可选项 (影响性能和成本)

| 项目 | 说明 | 推荐值 |
|------|------|--------|
| **批处理大小** | 批次越大,吞吐越高 | 8192 (生产) |
| **内存限制** | 防止OOM | 2048 MiB (Gateway) |
| **压缩算法** | 减少带宽 | gzip (推荐) |
| **Tail Sampling** | 智能采样,降低成本 | 生产环境勾选 |

---

## � 常见问题 (FAQ)

### Q1: 生成的配置可以直接用吗?

**A**: 几乎可以!只需要:

1. 修改后端端点地址 (如果不是默认值)
2. 如果启用了TLS,配置证书路径
3. 如果使用云平台,设置访问凭证

### Q2: 如何验证配置正确性?

**A**: 切换到"验证脚本"标签,复制脚本并运行:

```bash
# 保存脚本
cat > validate.sh <<'EOF'
(复制验证脚本内容)
EOF

# 运行验证
chmod +x validate.sh
./validate.sh
```

### Q3: Agent模式和Gateway模式有什么区别?

**A**:

- **Agent**: 每个节点/Pod运行一个Collector,轻量级 (512MB)
- **Gateway**: 集中式Collector,处理所有数据,功能强大 (2GB+)
- **推荐**: K8s环境使用 Agent + Gateway 混合模式

### Q4: 如何降低云平台成本?

**A**: 启用 **Tail Sampling** 处理器:

- ✅ 保留100%错误和慢请求
- ✅ 采样10%正常流量
- ✅ 总体成本降低 **~90%**

### Q5: 生成的Kubernetes部署清单需要修改吗?

**A**: 根据实际情况调整:

- `namespace`: 改为你的命名空间
- `resources`: 根据实际负载调整CPU/内存
- `replicas`: Gateway副本数 (推荐3个)

---

## � 下一步

完成配置生成后:

1. **保存配置**: 复制到 `config.yaml`
2. **验证配置**: 运行验证脚本
3. **部署**: 使用部署命令
4. **监控**: 访问 `http://localhost:8888/metrics` 查看指标

**详细文档**: [README.md](./README.md)

---

## � 完成

你已经掌握了配置生成器的基本用法!

**用时**: 3分钟
**生成**: 生产级配置
**节约**: 手动配置30分钟 → 工具3分钟 = **10倍提升**

**开始使用**:

```bash
open index.html  # 立即开始!
```
