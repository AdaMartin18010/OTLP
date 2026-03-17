---
title: OTLP v1.10.0 新特性解析
description: OpenTelemetry Protocol v1.10.0最新版本特性详解，包括Profiles信号增强、属性值限制移除等关键变更
version: OTLP v1.10.0
category: 核心协议
tags:
  - otlp
  - v1.10.0
  - profiles
  - attributes
  - changelog
status: published
date: 2026-03-17
---

# OTLP v1.10.0 新特性解析

> **发布日期**: 2026-03-09  
> **变更类型**: 稳定版更新  
> **最后更新**: 2026-03-17  

---

## 1. v1.10.0 概述

根据官方CHANGELOG，v1.10.0是继v1.9.0之后的最新稳定版本，主要增强了Profiles信号并改进了文档清晰度。

---

## 2. 主要变更

### 2.1 Profiles: 基于引用的属性 ([#733](https://github.com/open-telemetry/opentelemetry-proto/pull/733))

**重要变更**: Profiles信号引入了基于引用的属性机制，优化内存使用。

```protobuf
// v1.10.0之前: 直接嵌入属性
message Sample {
  repeated KeyValue attributes = 1;  // 重复存储
}

// v1.10.0: 引用式属性
message ProfilesData {
  Dictionary dictionary = 1;  // 全局字典
  // ...
}

message Sample {
  repeated int64 attribute_strindices = 1;  // 引用字典索引
}
```

**优势**:
- 减少重复属性存储
- 降低内存占用
- 提升传输效率

### 2.2 Common: 重命名 ref 后缀为 strindex ([#768](https://github.com/open-telemetry/opentelemetry-proto/pull/768))

**破坏性变更**: 字段命名规范化

| 旧名称 | 新名称 |
|--------|--------|
| `attribute_ref` | `attribute_strindex` |
| `string_ref` | `string_strindex` |

**迁移建议**:
- 更新proto生成代码
- 检查依赖该字段的处理逻辑

### 2.3 Logs: severity_number 可选性澄清 ([#736](https://github.com/open-telemetry/opentelemetry-proto/pull/736))

**规范澄清**: `SEVERITY_NUMBER_UNSPECIFIED`现在可以作为有效的`severity_number`值使用。

```protobuf
// 明确说明 severity_number 是可选的
message LogRecord {
  // 可选字段
  SeverityNumber severity_number = 1;
  // ...
}
```

### 2.4 Profiles: 文档改进

**文档增强**:
- Sample消息使用指导更清晰
- Profile和Sample时间戳关系更明确
- 字典使用指南完善

---

## 3. 与 v1.9.0 对比

| 特性 | v1.9.0 | v1.10.0 |
|------|--------|---------|
| Profiles属性 | 内联 | 引用式 ✅ |
| 字段命名 | ref后缀 | strindex后缀 ✅ |
| 日志级别 | 必选 | 可选 ✅ |
| 文档完整度 | 良好 | 更完善 ✅ |

---

## 4. 升级建议

### 4.1 SDK升级

```yaml
# Python
pip install opentelemetry-proto>=1.10.0

# Go
go get go.opentelemetry.io/proto/otlp@v1.10.0

# Java
<dependency>
    <groupId>io.opentelemetry.proto</groupId>
    <artifactId>opentelemetry-proto</artifactId>
    <version>1.10.0</version>
</dependency>
```

### 4.2 向后兼容性

v1.10.0保持向后兼容，主要变更是:
- Profiles信号仍在开发中 (development状态)
- 其他信号(trace/metrics/logs)保持稳定

---

## 5. 参考链接

- [官方CHANGELOG](https://github.com/open-telemetry/opentelemetry-proto/blob/main/CHANGELOG.md)
- [v1.10.0 Release](https://github.com/open-telemetry/opentelemetry-proto/releases/tag/v1.10.0)

---

**最后更新**: 2026-03-17  
**维护者**: OTLP协议团队  
**状态**: Published
