---
title: Semantic Conventions v1.40.0迁移指南
description: 从旧版本迁移到OpenTelemetry Semantic Conventions v1.40.0的完整指南，包括破坏性变更、双发策略和兼容性处理
version: Semantic Conventions v1.40.0
date: 2026-03-17
category: 核心协议
tags:
  - semantic-conventions
  - migration
  - breaking-changes
  - compatibility
  - v1.40.0
status: published
---

# Semantic Conventions v1.40.0迁移指南

> **目标版本**: v1.40.0  
> **迁移难度**: ⭐⭐⭐ (中级)  
> **最后更新**: 2026-03-17  

---

## 1. v1.40.0主要变更

### 1.1 稳定化声明

```
v1.40.0重大变更摘要:

已稳定的约定 (Stable):
├── HTTP Spans - 生产就绪
│   └── http.request.method, http.response.status_code
├── Database Spans - 生产就绪
│   └── db.system, db.statement
└── General Attributes - 生产就绪

已弃用的指标 (Deprecated):
├── rpc.client.request.size
├── rpc.client.response.size
├── rpc.server.request.size
└── rpc.server.response.size
    └── 替代: 使用对应traces属性

新增实验性约定:
├── GenAI语义约定
│   └── gen_ai.system, gen_ai.prompt.tokens
├── Feature Flags约定
│   └── feature_flag.key, feature_flag.result
└── CICD Pipeline约定
    └── cicd.pipeline.name, cicd.task.name
```

### 1.2 破坏性变更清单

| 旧名称 | 新名称 | 影响 | 迁移方式 |
|--------|--------|------|----------|
| `http.method` | `http.request.method` | Breaking | 双发 |
| `http.status_code` | `http.response.status_code` | Breaking | 双发 |
| `net.peer.name` | `server.address` | Breaking | 双发 |
| `net.peer.port` | `server.port` | Breaking | 双发 |
| `http.url` | `url.full` | Breaking | 双发 |

---

## 2. 双发策略 (Dual-Emission)

### 2.1 什么是双发策略

```
双发策略原理:

        应用代码
            │
            ▼
    ┌───────────────┐
    │   Resource    │
    │   Attributes  │
    └───────┬───────┘
            │
    ┌───────┴───────┐
    ▼               ▼
 旧属性名         新属性名
  (stable)      (upcoming)
    │               │
    ▼               ▼
 后端系统        后端系统
 (当前版本)     (新版本)

目的: 在迁移期间同时支持新旧属性名，确保兼容性
```

### 2.2 环境变量配置

```bash
# 启用双发策略
export OTEL_SEMCONV_STABILITY_OPT_IN=http/dup

# 可选值:
# - "" (空): 仅发送新属性名 (默认)
# - "http/dup": HTTP相关属性同时发送新旧名称
# - "database/dup": Database相关属性双发

# 在Kubernetes中配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-config
data:
  OTEL_SEMCONV_STABILITY_OPT_IN: "http/dup"
```

### 2.3 SDK配置

```java
// Java SDK双发配置
import io.opentelemetry.sdk.resources.Resource;

Resource resource = Resource.getDefault()
    .merge(Resource.builder()
        .put("otel.semconv-stability.opt-in", "http/dup")
        .build());
```

```go
// Go SDK双发配置
os.Setenv("OTEL_SEMCONV_STABILITY_OPT_IN", "http/dup")
```

---

## 3. 迁移步骤

### 3.1 迁移检查清单

```yaml
迁移前准备:
  - [ ] 审计当前使用的语义约定版本
  - [ ] 识别受影响的属性和指标
  - [ ] 评估后端系统兼容性
  - [ ] 制定回滚计划

迁移实施:
  - [ ] 更新SDK到支持v1.40.0的版本
  - [ ] 启用双发策略 (http/dup)
  - [ ] 验证数据正确性
  - [ ] 更新Dashboard和告警规则
  - [ ] 通知下游消费者

迁移后清理:
  - [ ] 确认下游系统完成迁移
  - [ ] 移除双发配置
  - [ ] 清理旧属性相关的代码
  - [ ] 更新文档
```

### 3.2 代码迁移示例

```java
// 迁移前 (旧约定)
Span span = tracer.spanBuilder("HTTP GET")
    .setAttribute("http.method", "GET")
    .setAttribute("http.url", "https://api.example.com/users")
    .setAttribute("http.status_code", 200)
    .setAttribute("net.peer.name", "api.example.com")
    .setAttribute("net.peer.port", 443)
    .startSpan();

// 迁移后 (v1.40.0新约定)
Span span = tracer.spanBuilder("HTTP GET")
    .setAttribute("http.request.method", "GET")
    .setAttribute("url.full", "https://api.example.com/users")
    .setAttribute("http.response.status_code", 200)
    .setAttribute("server.address", "api.example.com")
    .setAttribute("server.port", 443)
    .startSpan();

// 双发模式 (兼容期)
Span span = tracer.spanBuilder("HTTP GET")
    // 新属性名 (推荐)
    .setAttribute("http.request.method", "GET")
    .setAttribute("url.full", "https://api.example.com/users")
    .setAttribute("http.response.status_code", 200)
    .setAttribute("server.address", "api.example.com")
    .setAttribute("server.port", 443)
    // 旧属性名 (兼容)
    .setAttribute("http.method", "GET")
    .setAttribute("http.url", "https://api.example.com/users")
    .setAttribute("http.status_code", 200)
    .setAttribute("net.peer.name", "api.example.com")
    .setAttribute("net.peer.port", 443)
    .startSpan();
```

---

## 4. 后端适配

### 4.1 Collector配置

```yaml
processors:
  # 属性转换处理器
  transform/semconv:
    trace_statements:
      - context: span
        statements:
          # 旧 -> 新转换
          - set(attributes["http.request.method"], attributes["http.method"]) where attributes["http.method"] != nil
          - set(attributes["http.response.status_code"], attributes["http.status_code"]) where attributes["http.status_code"] != nil
          - set(attributes["server.address"], attributes["net.peer.name"]) where attributes["net.peer.name"] != nil
          - set(attributes["server.port"], attributes["net.peer.port"]) where attributes["net.peer.port"] != nil
          
          # 新 -> 旧转换 (反向兼容)
          - set(attributes["http.method"], attributes["http.request.method"]) where attributes["http.request.method"] != nil
          - set(attributes["http.status_code"], attributes["http.response.status_code"]) where attributes["http.response.status_code"] != nil

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [transform/semconv, batch]
      exporters: [otlp/backend]
```

---

## 5. 常见问题

### 5.1 FAQ

**Q: 双发会增加多少开销？**
A: 通常增加10-20%的网络开销，建议监控评估。

**Q: 迁移期间可以部分服务用旧版本吗？**
A: 可以，Collector可以配置同时处理新旧属性。

**Q: 废弃的指标还能用多久？**
A: 通常保留6-12个月，建议尽快迁移。

---

**最后更新**: 2026-03-17  
**维护者**: OTLP语义约定团队  
**状态**: Published
