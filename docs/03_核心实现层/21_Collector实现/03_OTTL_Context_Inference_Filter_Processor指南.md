---
title: OTTL Context Inference in Filter Processor 完整指南
description: OTTL Context Inference 功能详解，简化 Filter Processor 配置，提升可维护性
version: Collector v0.148.0+
date: 2026-03-18
author: OTLP项目团队
category: 核心实现
tags:
  - collector
  - processor
  - ottl
  - filter
  - context-inference
  - transformation
status: published
---

# OTTL Context Inference in Filter Processor 完整指南

> **引入版本**: Collector Contrib v0.148.0
> **稳定性**: Beta
> **官方博客**: [OTTL context inference comes to the Filter Processor](https://opentelemetry.io/blog/2026/) (2026-03-02)
> **最后更新**: 2026-03-18

---

## 1. 概述

### 什么是 Context Inference?

Context Inference 是 OTTL (OpenTelemetry Transformation Language) 的新特性，允许在 **Filter Processor** 中编写条件表达式时**自动推断**遥测数据的上下文类型（span、resource、metric 等），无需显式指定。

### 解决的问题

```yaml
# ❌ 旧配置 (v0.147.0 及之前) - 冗长且容易出错
processors:
  filter:
    traces:
      span:                    # 必须显式指定 span
        - 'attributes["http.status_code"] == 200'
      resource:                # 必须显式指定 resource
        - 'attributes["service.name"] == "health-check"'
      scope:                   # 必须显式指定 scope
        - 'name == "my-library"'

# ✅ 新配置 (v0.148.0+) - 简洁直观
processors:
  filter:
    traces:
      # 自动推断上下文，无需显式指定
      - 'attributes["http.status_code"] == 200'
      - 'resource.attributes["service.name"] == "health-check"'
      - 'scope.name == "my-library"'
```

---

## 2. 核心概念

### 2.1 上下文类型

| 上下文 | 访问方式 | 适用信号 |
|--------|----------|----------|
| `span` | `attributes`, `name`, `status`, `kind` | traces |
| `resource` | `resource.attributes` | all |
| `scope` | `scope.name`, `scope.version` | all |
| `metric` | `metric.name`, `metric.type` | metrics |
| `log` | `severity_number`, `body` | logs |
| `data_point` | `value`, `attributes` | metrics |

### 2.2 推断规则

```
┌─────────────────────────────────────────────────────────────────┐
│                    Context Inference 规则                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 直接访问属性 (attributes)                                    │
│     → 推断为当前信号的默认上下文                                 │
│     → traces: span, metrics: data_point, logs: log              │
│                                                                 │
│  2. 显式前缀访问 (resource.attributes)                           │
│     → 使用指定的上下文                                          │
│                                                                 │
│  3. 特殊字段访问 (severity_number)                               │
│     → 根据字段名推断上下文                                      │
│     → severity_number → log                                     │
│     → metric.name → metric                                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. 配置详解

### 3.1 基础配置

```yaml
processors:
  filter:
    # Traces - 使用 Context Inference
    traces:
      # 自动推断为 span 上下文
      - 'attributes["http.route"] == "/health"'
      - 'status.code == 1'  # ERROR
      - 'kind == 2'  # Server

      # 显式访问 resource
      - 'resource.attributes["deployment.environment"] == "production"'

      # 显式访问 scope
      - 'scope.name == "my-instrumentation"'

    # Metrics - 使用 Context Inference
    metrics:
      # 自动推断为 data_point 上下文
      - 'attributes["cpu"] == "cpu0"'
      - 'value > 100'

      # 显式访问 metric
      - 'metric.name == "http.requests"'

      # 显式访问 resource
      - 'resource.attributes["service.name"] == "api-gateway"'

    # Logs - 使用 Context Inference
    logs:
      # 自动推断为 log 上下文
      - 'severity_number >= 17'  # ERROR
      - 'body matches "Exception"'

      # 显式访问 resource
      - 'resource.attributes["service.name"] == "payment-service"'
```

### 3.2 新旧配置对比

#### Traces 配置

```yaml
# ❌ 旧配置 (v0.147.0)
processors:
  filter/old:
    traces:
      span:
        - 'attributes["http.method"] == "GET"'
        - 'attributes["http.route"] == "/api/v1/users"'
        - 'status.code == 2'
      resource:
        - 'attributes["service.name"] == "user-service"'
      scope:
        - 'name == "io.opentelemetry.instrumentation"'

# ✅ 新配置 (v0.148.0+)
processors:
  filter/new:
    traces:
      # 自动推断 span 上下文
      - 'attributes["http.method"] == "GET"'
      - 'attributes["http.route"] == "/api/v1/users"'
      - 'status.code == 2'
      # 显式前缀访问其他上下文
      - 'resource.attributes["service.name"] == "user-service"'
      - 'scope.name == "io.opentelemetry.instrumentation"'
```

#### Metrics 配置

```yaml
# ❌ 旧配置 (v0.147.0)
processors:
  filter/old:
    metrics:
      metric:
        - 'name == "cpu.usage"'
        - 'type == 1'  # GAUGE
      data_point:
        - 'attributes["cpu"] == "cpu0"'
        - 'value > 80'
      resource:
        - 'attributes["host.name"] == "server-01"'

# ✅ 新配置 (v0.148.0+)
processors:
  filter/new:
    metrics:
      # 自动推断 data_point 上下文
      - 'attributes["cpu"] == "cpu0"'
      - 'value > 80'
      # 显式前缀访问其他上下文
      - 'metric.name == "cpu.usage"'
      - 'metric.type == 1'
      - 'resource.attributes["host.name"] == "server-01"'
```

#### Logs 配置

```yaml
# ❌ 旧配置 (v0.147.0)
processors:
  filter/old:
    logs:
      log_record:
        - 'severity_number >= 17'
        - 'body == "Connection timeout"'
      resource:
        - 'attributes["service.name"] == "api-service"'

# ✅ 新配置 (v0.148.0+)
processors:
  filter/new:
    logs:
      # 自动推断 log 上下文
      - 'severity_number >= 17'
      - 'body == "Connection timeout"'
      # 显式前缀访问其他上下文
      - 'resource.attributes["service.name"] == "api-service"'
```

---

## 4. 高级用法

### 4.1 复杂条件

```yaml
processors:
  filter:
    traces:
      # 组合条件 - AND
      - 'attributes["http.route"] == "/health" and attributes["http.method"] == "GET"'

      # 组合条件 - OR
      - 'status.code == 2 or status.code == 0'

      # 嵌套条件
      - '(attributes["http.status_code"] >= 200 and attributes["http.status_code"] < 300) and resource.attributes["environment"] == "production"'

      # 正则匹配
      - 'attributes["http.route"] matches "/api/v[0-9]+/.*"'

      # 列表包含
      - 'attributes["http.method"] in ["GET", "HEAD", "OPTIONS"]'
```

### 4.2 跨上下文条件

```yaml
processors:
  filter:
    traces:
      # 同时访问多个上下文
      - 'attributes["http.status_code"] == 500 and resource.attributes["environment"] == "production"'
      - 'name == "GET /api/users" and scope.version != "1.0.0"'

    metrics:
      # 跨 metric 和 data_point
      - 'metric.name == "http.duration" and value > 1000'
      - 'metric.name matches "system.*" and attributes["device"] == "sda1"'
```

### 4.3 实用过滤场景

```yaml
processors:
  filter/production:
    # 生产环境: 只保留错误和慢请求
    traces:
      - 'status.code == 2'  # ERROR
      - 'attributes["http.duration_ms"] > 1000'
      - 'attributes["http.status_code"] >= 500'
      - 'resource.attributes["service.name"] == "critical-service"'

  filter/healthcheck:
    # 过滤掉健康检查日志
    traces:
      - 'attributes["http.route"] == "/health"'
      - 'attributes["http.route"] == "/ready"'
      - 'attributes["http.route"] == "/live"'
      - 'attributes["user_agent"] matches "health-checker|kube-probe"'

  filter/noise-reduction:
    # 降噪: 过滤掉低价值数据
    metrics:
      # 过滤掉系统指标
      - 'metric.name matches "system.cpu.*|system.memory.*" and resource.attributes["host.type"] == "k8s-node"'
    logs:
      # 过滤掉调试日志
      - 'severity_number < 9'  # DEBUG
      # 过滤掉特定消息
      - 'body matches "heartbeat|ping|keepalive"'
```

---

## 5. 与 Transform Processor 对比

### 5.1 功能对比

| 特性 | Filter Processor | Transform Processor |
|------|------------------|---------------------|
| 主要用途 | 过滤/丢弃数据 | 转换/修改数据 |
| Context Inference | ✅ v0.148.0+ | ✅ 已支持 |
| 条件复杂度 | 中等 | 高 |
| 性能 | 高 | 中等 |
| 使用场景 | 简单的包含/排除 | 复杂的转换逻辑 |

### 5.2 选择指南

```yaml
# ✅ 使用 Filter Processor - 简单过滤场景
processors:
  filter:
    traces:
      - 'attributes["http.route"] == "/health"'  # 简单条件

# ✅ 使用 Transform Processor - 复杂转换场景
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # 复杂转换
          - set(attributes["duration_ms"], duration / 1000000)
          - set(status.code, 2) where attributes["error"] == true
```

---

## 6. 生产环境配置

### 6.1 完整 Pipeline 配置

```yaml
processors:
  # 1. 内存限制
  memory_limiter:
    limit_mib: 1500
    spike_limit_mib: 300

  # 2. 资源属性处理
  resource:
    attributes:
      - key: environment
        value: production
        action: upsert

  # 3. 过滤 (使用 Context Inference)
  filter:
    traces:
      # 过滤健康检查
      - 'attributes["http.route"] matches "/health|/ready|/live"'
      # 过滤特定用户代理
      - 'attributes["http.user_agent"] matches "kube-probe|Prometheus"'
    logs:
      # 过滤调试日志
      - 'severity_number < 9'
      # 过滤心跳消息
      - 'body matches "heartbeat|keepalive|ping"'
    metrics:
      # 过滤低价值系统指标
      - 'metric.name matches "system.cpu.*" and resource.attributes["host.type"] == "k8s-node"'

  # 4. 批处理
  batch:
    timeout: 5s
    send_batch_size: 1024

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, filter, batch]
      exporters: [otlp]
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, resource, filter, batch]
      exporters: [otlp]
    logs:
      receivers: [otlp, filelog]
      processors: [memory_limiter, resource, filter, batch]
      exporters: [otlp]
```

### 6.2 多环境配置

```yaml
# development.yaml - 开发环境 (不过滤)
processors:
  filter:
    traces: []  # 不过滤
    logs: []    # 不过滤

---
# staging.yaml - 测试环境 (轻度过滤)
processors:
  filter:
    traces:
      - 'attributes["http.route"] == "/health"'
    logs:
      - 'severity_number < 5'  # 只过滤 TRACE

---
# production.yaml - 生产环境 (严格过滤)
processors:
  filter:
    traces:
      - 'attributes["http.route"] matches "/health|/ready|/live"'
      - 'attributes["http.user_agent"] matches "kube-probe|health-checker"'
    logs:
      - 'severity_number < 9'  # 过滤 DEBUG
      - 'body matches "heartbeat|keepalive|ping|health"'
    metrics:
      - 'metric.name matches "system.cpu.*|system.memory.*" and resource.attributes["host.type"] == "k8s-node"'
```

---

## 7. 故障排查

### 7.1 常见问题

**问题 1: 条件不生效**

```yaml
# ❌ 错误 - 属性名拼写错误
- 'attributes["http.status-code"] == 200'  # 应该是 http.status_code

# ✅ 正确
- 'attributes["http.status_code"] == 200'
```

**问题 2: 条件语法错误**

```yaml
# ❌ 错误 - 缺少引号
- 'attributes[http.route] == /health'

# ✅ 正确
- 'attributes["http.route"] == "/health"'
```

**问题 3: 复杂条件优先级**

```yaml
# ❌ 歧义
- 'status.code == 2 or status.code == 1 and attributes["important"] == true'

# ✅ 明确使用括号
- '(status.code == 2 or status.code == 1) and attributes["important"] == true'
```

### 7.2 调试技巧

```yaml
# 1. 使用 Transform Processor 添加调试信息
processors:
  transform/debug:
    trace_statements:
      - context: span
        statements:
          - set(attributes["filter.debug"], true) where attributes["http.route"] == "/health"

# 2. 分阶段过滤
processors:
  filter/health:
    traces:
      - 'attributes["http.route"] == "/health"'

  filter/status:
    traces:
      - 'status.code == 0'  # UNSET
```

---

## 8. 迁移指南

### 8.1 从旧配置迁移

```bash
# 1. 备份现有配置
cp config.yaml config.yaml.backup

# 2. 更新配置格式
# 将显式上下文改为推断格式

# 3. 验证配置
kubectl exec -it <collector-pod> -- /otelcol-contrib --config /etc/otel/config.yaml --dry-run

# 4. 灰度发布
# 先在小范围验证，再全量推广
```

### 8.2 配置转换脚本 (伪代码)

```python
# 简单转换示例
def migrate_config(old_config):
    new_config = old_config.copy()

    # 转换 traces
    if 'traces' in old_config['filter']:
        traces = old_config['filter']['traces']
        new_traces = []

        # 合并所有上下文的条件
        for context in ['span', 'resource', 'scope']:
            if context in traces:
                for condition in traces[context]:
                    # 添加显式前缀
                    if context == 'resource':
                        condition = condition.replace(
                            'attributes[', 'resource.attributes[')
                    elif context == 'scope':
                        condition = condition.replace(
                            'name ==', 'scope.name ==')
                    new_traces.append(condition)

        new_config['filter']['traces'] = new_traces

    return new_config
```

---

## 9. 参考资源

- [OTTL Documentation](https://opentelemetry.io/docs/collector/transformations/)
- [Filter Processor Documentation](https://opentelemetry.io/docs/collector/processors/filter/)
- [官方博客: OTTL Context Inference](https://opentelemetry.io/blog/2026/)
- [OTTL Functions Reference](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl)

---

**最后更新**: 2026-03-18
**维护团队**: OTLP项目团队
**状态**: 已发布

---

> 💡 **提示**: OTTL Context Inference 显著简化了 Filter Processor 的配置，建议在新配置中使用新格式，并逐步迁移旧配置。**
