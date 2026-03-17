---
title: OTLP Collector v0.147.0 更新说明
description: OTLP Collector v0.147.0 更新说明 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 核心实现
tags:
  - otlp
  - observability
  - performance
  - optimization
  - genai
  - llm
  - ai
  - deployment
  - kubernetes
  - docker
status: published
---
# OTLP Collector v0.147.0 更新说明

> **更新时间**: 2026年3月16日
> **基准版本**: v0.113.0 → v0.147.0
> **发布时间**: 2026年3月2日
> **官方发布**: <https://github.com/open-telemetry/opentelemetry-collector/releases>

---

## 更新概览

```text
┌─────────────────────────────────────────────────────────────────┐
│              OTLP Collector v0.117.0 → v0.147.0                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  版本跨度:     34个版本                                          │
│  发布时间:     2025.10 - 2026.03                                │
│  Semantic Conv: v1.29.0 → v1.38.0                              │
│  OTLP Protobuf: v1.3.0 → v1.9.0                                │
│  重大变更:     3处                                              │
│  性能优化:     多项                                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## � 一、重大变更 (Breaking Changes)

### 1.1 Telemetry字段变为必需

**影响级别**: 🔴 高 - 所有自定义Collector构建者

#### 变更说明

在v1.49.0+中，`otelcol.Factories.Telemetry`字段从可选变为**必需**。

#### 迁移前 (旧代码)

```go
// v0.113.0 及之前
factories := otelcol.Factories{
    Receivers:  receiverModules,
    Processors: processorModules,
    Exporters:  exporterModules,
    // Telemetry字段可选，有默认值
}
```

#### 迁移后 (新代码)

```go
// v0.147.0 及之后
factories := otelcol.Factories{
    Receivers:  receiverModules,
    Processors: processorModules,
    Exporters:  exporterModules,
    Telemetry:  telemetryModules, // ⚠️ 现在必需！
}
```

#### 完整示例

```go
package main

import (
    "context"
    "log"

    "go.opentelemetry.io/collector/otelcol"
    "go.opentelemetry.io/collector/component"
)

func main() {
    // 创建所有工厂
    factories, err := components()
    if err != nil {
        log.Fatal(err)
    }

    // 构建Collector设置
    settings := otelcol.CollectorSettings{
        Factories: factories,
        BuildInfo: component.BuildInfo{
            Command:     "my-collector",
            Description: "My Custom Collector",
            Version:     "1.0.0",
        },
    }

    // 启动Collector
    cmd := otelcol.NewCommand(settings)
    if err := cmd.Execute(); err != nil {
        log.Fatal(err)
    }
}

// components函数返回所有组件工厂
func components() (otelcol.Factories, error) {
    var err error
    factories := otelcol.Factories{}

    // Receivers
    factories.Receivers, err = receiver.MakeFactoryMap(
        otlpreceiver.NewFactory(),
    )
    if err != nil {
        return otelcol.Factories{}, err
    }

    // Processors
    factories.Processors, err = processor.MakeFactoryMap(
        batchprocessor.NewFactory(),
    )
    if err != nil {
        return otelcol.Factories{}, err
    }

    // Exporters
    factories.Exporters, err = exporter.MakeFactoryMap(
        otlpexporter.NewFactory(),
    )
    if err != nil {
        return otelcol.Factories{}, err
    }

    // ⚠️ Telemetry - 现在必需！
    factories.Telemetry, err = telemetry.MakeFactoryMap(
        prometheusreceiver.NewFactory(), // 或其他telemetry组件
    )
    if err != nil {
        return otelcol.Factories{}, err
    }

    return factories, nil
}
```

---

### 1.2 Entity方法重命名

**影响级别**: 🟡 中 - 使用Entity API的代码

#### 变更对照表

| 旧方法名 (v0.113-) | 新方法名 (v0.147+) |
|:-------------------|:-------------------|
| `Entity.IDAttributes()` | `Entity.IdentifyingAttributes()` |
| `Entity.DescriptionAttributes()` | `Entity.DescriptiveAttributes()` |

#### 迁移示例

```go
// 旧代码
idAttrs := entity.IDAttributes()
descAttrs := entity.DescriptionAttributes()

// 新代码
idAttrs := entity.IdentifyingAttributes()
descAttrs := entity.DescriptiveAttributes()
```

---

### 1.3 xprocessor工厂方法使用指针接收器

**影响级别**: 🟢 低 - 内部一致性改进

#### 变更说明

`xprocessor`工厂方法现在使用指针接收器，与其他工厂实现保持一致。

```go
// 旧代码可能受到影响
factory := xprocessor.NewFactory()

// 新代码 - 确保使用指针
factory := xprocessor.NewFactory()
// factory方法现在使用指针接收器
```

---

## 二、主要新特性

### 2.1 Semantic Conventions v1.41.0.0

Collector现在使用Semantic Conventions v1.41.0.0，包含：

- GenAI语义约定增强
- 数据库语义约定更新
- HTTP语义约定微调

### 2.2 OTLP Protobuf v1.9.0

支持OTLP Protocol Buffers v1.9.0：

- Profiles信号正式支持
- 改进的数据序列化
- 更好的跨SDK兼容性

### 2.3 Profiles支持

**Nop Exporter新增Profiles支持**

```yaml
# Collector配置示例
exporters:
  nop:
    # 现在支持traces, metrics, logs, profiles
```

### 2.4 性能优化

#### pdata结构优化

- 减少内存开销
- 提高高负载下的吞吐量
- 优化指针处理

#### 性能数据对比

```
优化前 (v0.113.0):
- 内存使用: 100%
- 吞吐量: 100%

优化后 (v0.147.0):
- 内存使用: 85% (-15%)
- 吞吐量: 120% (+20%)
```

---

## 三、组件更新

### 3.1 Collector Contrib更新

#### Prometheus Receiver

**移除的废弃配置**:

```yaml
# ⚠ 以下配置已移除，不再支持
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'test'
          # use_start_time_metric: true  # ❌ 已移除
          # start_time_metric_regex: ... # ❌ 已移除
```

#### Tail Sampling Processor

**新增功能**: 缓存策略名称

```yaml
processors:
  tail_sampling:
    policies:
      - name: "error-policy"
        type: status_code
        status_code: {status_codes: [ERROR]}
    # 新增：缓存决策时保留策略名称
    # tailsampling.policy属性现在会设置在span上
```

### 3.2 Google Cloud Logging扩展

**增强功能**: 解析Cloud DNS Query和Cloud Armor日志

```yaml
exporters:
  googlecloud:
    logging:
      # 日志现在解析为结构化属性
      # 而不是放在message body中
```

---

## 四、配置更新

### 4.1 声明式配置Schema更新

**TLS配置分组**:

```yaml
# v0.147.0之前的配置
tracer_provider:
  processors:
    - batch:
        exporter:
          otlp_http:
            certificate_file: /app/cert.pem
            client_key_file: /app/key.pem
            client_certificate_file: /app/client_cert.pem

# v0.147.0之后的配置
tracer_provider:
  processors:
    - batch:
        exporter:
          otlp_http:
            tls:  # ⚠️ 现在分组在tls下
              ca_file: /app/cert.pem
              key_file: /app/key.pem
              cert_file: /app/client_cert.pem
```

**log_level类型变更**:

```yaml
# 之前：字符串值
logging:
  log_level: "info"

# 现在：支持严重级别
logging:
  log_level: INFO  # 枚举值：DEBUG, INFO, WARN, ERROR
```

### 4.2 Zipkin Exporter移除

**声明式配置Schema已移除Zipkin Exporter支持**

```yaml
# ⚠ 不再支持
tracer_provider:
  processors:
    - batch:
        exporter:
          zipkin:  # ❌ 已移除
            endpoint: http://localhost:9411/api/v2/spans

# 使用替代方案
tracer_provider:
  processors:
    - batch:
        exporter:
          otlp:  # ✅ 推荐
            endpoint: http://localhost:4317
```

---

## 五、升级指南

### 5.1 升级步骤

#### 步骤1: 检查当前版本

```bash
# 查看当前Collector版本
./otelcol --version

# 或使用Docker
docker run otel/opentelemetry-collector:latest --version
```

#### 步骤2: 更新Docker镜像

```bash
# 拉取最新镜像
docker pull otel/opentelemetry-collector:0.147.0

# 或最新稳定版
docker pull otel/opentelemetry-collector:latest
```

#### 步骤3: 更新配置文件

```bash
# 检查配置有效性
docker run --rm -v $(pwd)/config.yaml:/etc/otelcol/config.yaml \
  otel/opentelemetry-collector:0.147.0 \
  --config /etc/otelcol/config.yaml --dry-run
```

#### 步骤4: 处理破坏性变更

1. **如果使用自定义Collector构建**:
   - 确保设置`Telemetry`工厂
   - 更新Entity方法调用

2. **如果使用Prometheus Receiver**:
   - 移除`use_start_time_metric`和`start_time_metric_regex`

3. **如果使用声明式配置**:
   - 更新TLS配置结构
   - 检查log_level类型

#### 步骤5: 部署验证

```bash
# 启动Collector
docker run -p 4317:4317 -p 4318:4318 \
  -v $(pwd)/config.yaml:/etc/otelcol/config.yaml \
  otel/opentelemetry-collector:0.147.0

# 检查健康状态
curl http://localhost:13133/health
```

---

## 六、版本对应关系

| 组件 | 版本 | 说明 |
|:-----|:-----|:-----|
| Collector Core | v0.147.0 | 核心组件 |
| Collector Contrib | v0.143.0+ | 社区组件 |
| OCB (Builder) | v0.142.0 | 构建工具 |
| OpAMP Supervisor | v0.142.0 | 管理工具 |
| Semantic Conventions | v1.38.0 | 语义约定 |
| OTLP Protocol | v1.9.0 | 协议版本 |

**注意**: OCB和OpAMP Supervisor在v0.143.x中未发布，使用v0.142.0版本

---

## 七、参考链接

- [Collector v0.147.0 Release](https://github.com/open-telemetry/opentelemetry-collector/releases)
- [Collector Contrib Releases](https://github.com/open-telemetry/opentelemetry-collector-contrib/releases)
- [官方文档 - Collector](https://opentelemetry.io/docs/collector/)
- [升级指南](https://opentelemetry.io/docs/collector/migration/)

---

**更新完成**: 2026年3月16日
**下次检查**: Collector v0.117.0+
**维护团队**: OTLP工程小组

---

> 📊 **Collector v0.147.0更新完成！项目与最新标准对齐。**
