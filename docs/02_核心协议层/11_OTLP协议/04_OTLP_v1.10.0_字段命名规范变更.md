---
title: OTLP v1.10.0 字段命名规范变更
description: OTLP v1.10.0中字段命名规范的破坏性变更详解，从ref后缀到strindex后缀的迁移指南
version: OTLP v1.10.0
category: 核心协议
tags:
  - otlp
  - v1.10.0
  - breaking-changes
  - naming-convention
  - migration
status: published
date: 2026-03-17
---

# OTLP v1.10.0 字段命名规范变更

> **变更类型**: 破坏性变更 (Breaking Change)  
> **影响范围**: Profiles信号  
> **最后更新**: 2026-03-17  

---

## 1. 变更概述

### 1.1 为什么要变更？

```
问题背景:
├── "ref"后缀含义模糊
│   └── 不清楚是"reference"还是"refinement"
├── 新命名更清晰
│   └── "strindex"明确表示"string index"
└── 与其他字段保持一致
    └── 如 attribute_strindices
```

### 1.2 变更清单

| 旧字段名 (v1.9.0) | 新字段名 (v1.10.0) | 所在消息 |
|-------------------|--------------------|----------|
| `attribute_ref` | `attribute_strindex` | Sample |
| `string_ref` | `string_strindex` | Various |
| `key_ref` | `key_strindex` | Attribute |
| `value_ref` | `value_strindex` | Attribute |

---

## 2. 详细变更说明

### 2.1 Sample消息变更

```protobuf
// v1.9.0
message Sample {
  // 引用属性表的索引
  repeated int64 attribute_ref = 1;  // ❌ 旧命名
  
  // 其他字段...
}

// v1.10.0
message Sample {
  // 引用属性表的索引
  repeated int64 attribute_strindex = 1;  // ✅ 新命名
  
  // 其他字段...
}
```

### 2.2 Dictionary属性表变更

```protobuf
// v1.9.0
message Attribute {
  int32 key_ref = 1;      // ❌ 旧命名
  int32 value_ref = 2;    // ❌ 旧命名
}

// v1.10.0
message Attribute {
  int32 key_strindex = 1;     // ✅ 新命名 - 字符串表索引
  int32 value_strindex = 2;   // ✅ 新命名 - 字符串表索引
}
```

---

## 3. 迁移指南

### 3.1 代码迁移示例 (Go)

```go
// v1.9.0 旧代码
func encodeSampleV1(sample Sample) *pb.Sample {
    return &pb.Sample{
        AttributeRef: []int64{1, 2, 3},  // ❌ 旧字段名
    }
}

func decodeSampleV1(pbSample *pb.Sample) {
    for _, ref := range pbSample.AttributeRef {  // ❌ 旧字段名
        // 处理属性
    }
}

// v1.10.0 新代码
func encodeSampleV2(sample Sample) *pb.Sample {
    return &pb.Sample{
        AttributeStrindex: []int64{1, 2, 3},  // ✅ 新字段名
    }
}

func decodeSampleV2(pbSample *pb.Sample) {
    for _, strindex := range pbSample.AttributeStrindex {  // ✅ 新字段名
        // 处理属性
    }
}
```

### 3.2 兼容性处理

```go
// 支持双版本的适配器
func decodeSampleUniversal(pbSample *pb.Sample) []int64 {
    // 优先使用新字段名
    if len(pbSample.AttributeStrindex) > 0 {
        return pbSample.AttributeStrindex
    }
    
    // 回退到旧字段名 (向后兼容)
    return pbSample.AttributeRef
}
```

---

## 4. 影响分析

### 4.1 影响组件

```
受影响组件:
├── SDK实现
│   └── 需要更新proto生成代码
├── Collector
│   └── 需要更新Profiles处理器
├── 后端存储
│   └── 可能需要更新查询逻辑
└── 可视化工具
    └── 需要更新字段映射
```

### 4.2 升级建议

| 组件类型 | 升级策略 | 时间窗口 |
|----------|----------|----------|
| SDK | 同步升级所有服务 | 维护窗口 |
| Collector | 滚动升级 | 零停机 |
| 后端 | 双字段兼容 | 过渡期 |

---

## 5. 最佳实践

### 5.1 版本检测

```go
// 在运行时检测版本
func detectProfilesVersion(data []byte) string {
    // 检查字段编号和类型
    // v1.10.0 使用新的字段编号
    // ...
    return "v1.10.0"
}
```

### 5.2 字段映射工具

```yaml
# Collector字段映射配置
processors:
  transform:
    profile_statements:
      - context: sample
        statements:
          # 将旧字段映射到新字段
          - set(attribute_strindex, attribute_ref) where attribute_ref != nil
```

---

**参考链接**:
- [PR #768: Rename ref suffix to strindex](https://github.com/open-telemetry/opentelemetry-proto/pull/768)

**最后更新**: 2026-03-17  
**状态**: Published
