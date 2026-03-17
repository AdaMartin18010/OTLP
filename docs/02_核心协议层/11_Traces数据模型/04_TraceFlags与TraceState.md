---
title: TraceFlags与TraceState详解
description: OTLP Trace上下文传播的核心概念TraceFlags和TraceState的完整规范与实现指南
version: OTLP v1.10.0 / W3C Trace Context v1
date: 2026-03-17
author: OTLP项目团队
category: 数据模型
tags:
  - traceflags
  - tracestate
  - trace-context
  - propagation
  - w3c
status: published
---

# TraceFlags与TraceState详解

> **版本**: OTLP v1.10.0 / W3C Trace Context Level 1
> **最后更新**: 2026-03-17
> **阅读时间**: 约25分钟

---

## 1. 概述

### 1.1 什么是TraceFlags和TraceState

TraceFlags和TraceState是**W3C Trace Context**标准定义的两个重要字段，用于在分布式系统中传播追踪上下文：

```
┌─────────────────────────────────────────────────────────────────┐
│                  Trace Context结构                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  traceparent (必需)                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ version  trace-id                    parent-id  flags  │   │
│  │ 00       0af7651916cd43dd8448eb211c80319c b7ad6b7169203331 01│
│  │ ↑        ↑                           ↑        ↑        │   │
│  │ 2字节    16字节(32hex)               8字节    1字节    │   │
│  │          (128-bit)                   (64-bit) (8-bit)  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  tracestate (可选)                                              │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ vendor1=value1,vendor2=value2,vendor3=value3           │   │
│  │ ↑                                                      │   │
│  │ 逗号分隔的键值对列表，最多32个条目                     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 字段定义

| 字段 | 大小 | 说明 |
|------|------|------|
| **TraceFlags** | 1字节 (8位) | 控制追踪行为的标志位 |
| **TraceState** | 可变 | 厂商特定的扩展信息 |

---

## 2. TraceFlags详解

### 2.1 TraceFlags结构

```
TraceFlags: 1字节 (8位)

┌─────────────────────────────────────────────────────────────────┐
│  Bit 7  │ Bit 6  │ Bit 5  │ Bit 4  │ Bit 3  │ Bit 2  │ Bit 1  │ Bit 0  │
├─────────┼─────────┼─────────┼─────────┼─────────┼─────────┼─────────┼─────────┤
│ Reserved│ Reserved│ Reserved│ Reserved│ Reserved│ Reserved│ Random  │ Sampled │
│  (将来) │  (将来) │  (将来) │  (将来) │  (将来) │  (将来) │ Trace   │         │
│         │         │         │         │         │         │ (将来)  │         │
└─────────┴─────────┴─────────┴─────────┴─────────┴─────────┴─────────┴─────────┘

当前定义的标志位:
  • Bit 0 (Sampled): 是否采样 (1=采样, 0=未采样)
  • Bit 1 (Random): 随机Trace (未来使用)
  • Bit 2-7: 保留供将来使用
```

### 2.2 Sampled标志位

**Sampled (Bit 0)** 是最重要的标志位：

```
┌─────────────────────────────────────────────────────────────────┐
│                    Sampled标志位含义                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Sampled = 0 (未采样)                                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • 调用链可能被记录，但不一定上报                         │   │
│  │ • 下游服务可以选择是否采样                               │   │
│  │ • 通常用于传播上下文但不产生成本                         │   │
│  │ • 调试时仍可查看Trace ID关联的日志                       │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  Sampled = 1 (已采样)                                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ • 调用链被记录并上报到收集器                             │   │
│  │ • 下游服务应该继续采样                                   │   │
│  │ • 所有Span都应该被记录                                   │   │
│  │ • 产生存储和传输成本                                     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.3 TraceFlags值

```go
// TraceFlags常量定义
const (
    // TraceFlagsNone - 无标志位设置
    TraceFlagsNone = 0x00

    // TraceFlagsSampled - 已采样
    TraceFlagsSampled = 0x01

    // TraceFlagsRandom - 随机Trace (保留)
    TraceFlagsRandom = 0x02
)

// 常见组合
// 0x00 (00000000) - 未采样
// 0x01 (00000001) - 已采样
// 0x03 (00000011) - 已采样 + 随机 (将来)
```

### 2.4 TraceFlags实现

```go
// Go实现示例
package trace

// TraceFlags表示8位追踪标志
type TraceFlags byte

// IsSampled返回是否已采样
func (tf TraceFlags) IsSampled() bool {
    return tf&TraceFlagsSampled == TraceFlagsSampled
}

// WithSampled返回设置了采样标志的新TraceFlags
func (tf TraceFlags) WithSampled(sampled bool) TraceFlags {
    if sampled {
        return tf | TraceFlagsSampled
    }
    return tf &^ TraceFlagsSampled
}

// String返回十六进制表示
func (tf TraceFlags) String() string {
    return fmt.Sprintf("%02x", byte(tf))
}

// 使用示例
func main() {
    // 创建未采样的TraceFlags
    flags := TraceFlags(0x00)
    fmt.Println(flags.IsSampled()) // false

    // 设置为采样
    flags = flags.WithSampled(true)
    fmt.Println(flags.IsSampled()) // true
    fmt.Println(flags.String())    // "01"
}
```

```python
# Python实现示例
class TraceFlags:
    """TraceFlags实现"""

    NONE = 0x00
    SAMPLED = 0x01
    RANDOM = 0x02

    def __init__(self, flags: int = 0):
        self._flags = flags & 0xFF  # 确保只有8位

    @property
    def is_sampled(self) -> bool:
        """是否已采样"""
        return (self._flags & self.SAMPLED) == self.SAMPLED

    def with_sampled(self, sampled: bool) -> 'TraceFlags':
        """设置采样标志"""
        if sampled:
            return TraceFlags(self._flags | self.SAMPLED)
        return TraceFlags(self._flags & ~self.SAMPLED)

    def __str__(self) -> str:
        return f"{self._flags:02x}"

    def __int__(self) -> int:
        return self._flags

# 使用示例
flags = TraceFlags(0x00)
print(flags.is_sampled)  # False

flags = flags.with_sampled(True)
print(flags.is_sampled)  # True
print(str(flags))        # "01"
```

---

## 3. TraceState详解

### 3.1 TraceState概述

**TraceState** 用于传播厂商特定的追踪信息：

```
┌─────────────────────────────────────────────────────────────────┐
│                    TraceState格式                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  格式: vendor=value,vendor2=value2,...                          │
│                                                                 │
│  限制:                                                          │
│  • 最多32个键值对                                               │
│  • 总长度不超过512字符                                          │
│  • 键名只能包含小写字母、数字、下划线、连字符、星号           │
│  • 值可以是任意可见ASCII字符                                    │
│                                                                 │
│  示例:                                                          │
│  congo=t61rcWkgMzE,rojo=00f067aa0ba902b7                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 TraceState键命名规范

```
键命名规则:

1. 格式: <tenant_id>@<vendor_id> 或 <vendor_id>

2. 字符限制:
   • 只能包含: a-z, 0-9, _, -, *
   • 必须以字母开头
   • 长度: 1-256字符

3. 多租户格式:
   • 格式: tenant@vendor
   • 示例: acme@congo, shop@rojo

4. 保留键:
   • 以ot-开头的键保留给OpenTelemetry官方使用
   • 示例: ot-sampled, ot-tenant

有效示例:
  ✅ congo
  ✅ rojo
  ✅ my-vendor
  ✅ acme@congo

无效示例:
  ❌ 123vendor    (不能以数字开头)
  ❌ MyVendor     (不能有大写字母)
  ❌ vendor.name  (不能有小数点)
```

### 3.3 TraceState实现

```go
// Go实现示例
package trace

import (
    "fmt"
    "strings"
    "regexp"
)

// TraceState表示厂商特定的追踪状态
type TraceState struct {
    entries map[string]string
}

// NewTraceState创建新的TraceState
func NewTraceState() *TraceState {
    return &TraceState{
        entries: make(map[string]string),
    }
}

// Get获取指定键的值
func (ts *TraceState) Get(key string) (string, bool) {
    val, ok := ts.entries[key]
    return val, ok
}

// Set设置键值对
func (ts *TraceState) Set(key, value string) error {
    // 验证键名
    if !isValidKey(key) {
        return fmt.Errorf("invalid trace state key: %s", key)
    }

    // 验证值
    if !isValidValue(value) {
        return fmt.Errorf("invalid trace state value: %s", value)
    }

    // 检查大小限制
    if len(ts.entries) >= 32 {
        return fmt.Errorf("trace state exceeded maximum entries (32)")
    }

    ts.entries[key] = value
    return nil
}

// Delete删除键
func (ts *TraceState) Delete(key string) {
    delete(ts.entries, key)
}

// String返回W3C格式字符串
func (ts *TraceState) String() string {
    var parts []string
    for k, v := range ts.entries {
        parts = append(parts, fmt.Sprintf("%s=%s", k, v))
    }
    return strings.Join(parts, ",")
}

// ParseTraceState从字符串解析
func ParseTraceState(s string) (*TraceState, error) {
    ts := NewTraceState()

    if s == "" {
        return ts, nil
    }

    pairs := strings.Split(s, ",")
    for _, pair := range pairs {
        kv := strings.SplitN(pair, "=", 2)
        if len(kv) != 2 {
            continue // 忽略无效条目
        }

        key := strings.TrimSpace(kv[0])
        value := strings.TrimSpace(kv[1])

        if err := ts.Set(key, value); err != nil {
            return nil, err
        }
    }

    return ts, nil
}

// 验证函数
var keyRegex = regexp.MustCompile(`^[a-z][a-z0-9_\-\*]*$`)

func isValidKey(key string) bool {
    if len(key) == 0 || len(key) > 256 {
        return false
    }
    return keyRegex.MatchString(key)
}

func isValidValue(value string) bool {
    // 值可以是任意可见ASCII字符，长度限制
    if len(value) > 256 {
        return false
    }

    for _, c := range value {
        if c < 0x20 || c > 0x7E {
            return false // 不可见字符
        }
    }
    return true
}

// 使用示例
func main() {
    ts := NewTraceState()

    // 设置值
    ts.Set("congo", "t61rcWkgMzE")
    ts.Set("rojo", "00f067aa0ba902b7")

    // 获取值
    if val, ok := ts.Get("congo"); ok {
        fmt.Println("congo:", val)
    }

    // 输出W3C格式
    fmt.Println(ts.String())
    // 输出: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

    // 从字符串解析
    parsed, _ := ParseTraceState("vendor1=value1,vendor2=value2")
    fmt.Println(parsed.String())
}
```

```python
# Python实现示例
import re
from typing import Dict, Optional

class TraceState:
    """TraceState实现"""

    MAX_ENTRIES = 32
    MAX_KEY_LEN = 256
    MAX_VALUE_LEN = 256

    _key_pattern = re.compile(r'^[a-z][a-z0-9_\-\*]*$')

    def __init__(self):
        self._entries: Dict[str, str] = {}

    def get(self, key: str) -> Optional[str]:
        """获取指定键的值"""
        return self._entries.get(key)

    def set(self, key: str, value: str) -> None:
        """设置键值对"""
        if not self._is_valid_key(key):
            raise ValueError(f"Invalid trace state key: {key}")

        if not self._is_valid_value(value):
            raise ValueError(f"Invalid trace state value: {value}")

        if len(self._entries) >= self.MAX_ENTRIES and key not in self._entries:
            raise ValueError(f"Trace state exceeded maximum entries ({self.MAX_ENTRIES})")

        self._entries[key] = value

    def delete(self, key: str) -> None:
        """删除键"""
        self._entries.pop(key, None)

    def __str__(self) -> str:
        """返回W3C格式字符串"""
        return ",".join(f"{k}={v}" for k, v in self._entries.items())

    @classmethod
    def parse(cls, s: str) -> 'TraceState':
        """从字符串解析"""
        ts = cls()
        if not s:
            return ts

        for pair in s.split(","):
            if "=" not in pair:
                continue
            key, value = pair.split("=", 1)
            ts.set(key.strip(), value.strip())

        return ts

    def _is_valid_key(self, key: str) -> bool:
        """验证键名"""
        if not key or len(key) > self.MAX_KEY_LEN:
            return False
        return bool(self._key_pattern.match(key))

    def _is_valid_value(self, value: str) -> bool:
        """验证值"""
        if len(value) > self.MAX_VALUE_LEN:
            return False
        return all(0x20 <= ord(c) <= 0x7E for c in value)

# 使用示例
ts = TraceState()
ts.set("congo", "t61rcWkgMzE")
ts.set("rojo", "00f067aa0ba902b7")

print(ts.get("congo"))  # t61rcWkgMzE
print(str(ts))          # congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

# 解析
parsed = TraceState.parse("vendor1=value1,vendor2=value2")
print(str(parsed))      # vendor1=value1,vendor2=value2
```

---

## 4. 传播规则

### 4.1 TraceFlags传播

```
┌─────────────────────────────────────────────────────────────────┐
│                    TraceFlags传播规则                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 采样决策                                                     │
│     • 如果父Span的Sampled=1，子Span应该继续采样                │
│     • 如果父Span的Sampled=0，子Span可以独立决策                │
│                                                                 │
│  2. 修改规则                                                     │
│     • 可以将0改为1 (从不采样改为采样)                          │
│     • 不能将1改为0 (一旦采样必须继续)                          │
│                                                                 │
│  3. 传播示例                                                     │
│     ┌─────────┐        ┌─────────┐        ┌─────────┐         │
│     │ Service │        │ Service │        │ Service │         │
│     │    A    │ ─────→ │    B    │ ─────→ │    C    │         │
│     │ 0x01    │        │ 0x01    │        │ 0x01    │         │
│     └─────────┘        └─────────┘        └─────────┘         │
│        Sampled          Sampled           Sampled              │
│        = 1              = 1               = 1                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 TraceState传播

```
┌─────────────────────────────────────────────────────────────────┐
│                    TraceState传播规则                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 传播原则                                                     │
│     • TraceState必须向下游传播                                 │
│     • 每个服务可以添加/修改自己的条目                          │
│     • 总大小不能超过512字符                                    │
│                                                                 │
│  2. 修改规则                                                     │
│     • 可以添加新条目                                           │
│     • 可以修改自己的条目                                       │
│     • 不应该删除其他厂商的条目                                 │
│     • 如果超出大小限制，应该删除最老的条目                     │
│                                                                 │
│  3. 传播示例                                                     │
│     ┌──────────────────────────────────────────────────────┐   │
│     │ Service A                                              │   │
│     │   tracestate: congo=t61rcWkgMzE                        │   │
│     │                                                        │   │
│     │   ↓ 传播                                               │   │
│     │                                                        │   │
│     │ Service B                                              │   │
│     │   tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7  │   │
│     │              ↑ 新增条目                                │   │
│     │                                                        │   │
│     │   ↓ 传播                                               │   │
│     │                                                        │   │
│     │ Service C                                              │   │
│     │   tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7  │   │
│     │                                                        │   │
│     └──────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 5. 最佳实践

### 5.1 TraceFlags使用建议

```markdown
1. 采样决策
   - 在入口处(如API Gateway)做采样决策
   - 使用概率采样或基于特征的采样
   - 重要请求(如支付)应该强制采样

2. 性能考虑
   - 即使Sampled=0，也应该传播Trace ID
   - 这样可以在日志中关联，但不产生Span成本

3. 调试场景
   - 支持按Trace ID强制采样
   - 方便排查特定问题
```

### 5.2 TraceState使用建议

```markdown
1. 使用场景
   - 传递租户信息: tenant@platform=value
   - 传递版本信息: version=1.2.3
   - 传递特性标志: feature_flag=enabled

2. 避免滥用
   - 不要在TraceState中传递大体积数据
   - 不要在TraceState中传递敏感信息
   - 条目数量不要超过10个

3. 命名规范
   - 使用反向域名: com.example.feature
   - 多租户使用@分隔: tenant@platform
```

---

## 6. 常见问题

### Q1: TraceFlags和TraceState的区别是什么?

```
TraceFlags:
  • 标准行为控制 (采样等)
  • 所有厂商必须支持
  • 固定的8位格式

TraceState:
  • 厂商特定扩展
  • 可选支持
  • 灵活的键值对格式
```

### Q2: 如何实现强制采样?

```go
// 方式1: 通过TraceFlags
func ForceSample(ctx context.Context) context.Context {
    spanContext := trace.SpanContextFromContext(ctx)
    newSpanContext := spanContext.WithTraceFlags(
        spanContext.TraceFlags() | trace.TraceFlagsSampled
    )
    return trace.ContextWithSpanContext(ctx, newSpanContext)
}

// 方式2: 通过TraceState
ts := trace.TraceState{}
ts.Set("ot-force-sample", "true")
```

### Q3: TraceState超出大小限制怎么办?

```go
// 删除最老的条目直到满足限制
func TrimTraceState(ts *trace.TraceState, maxLen int) {
    for len(ts.String()) > maxLen && ts.Len() > 0 {
        // 删除第一个条目(最老的)
        ts.RemoveOldest()
    }
}
```

---

**参考资源**:

- [W3C Trace Context Specification](https://www.w3.org/TR/trace-context/)
- [OpenTelemetry Trace Context](https://opentelemetry.io/docs/concepts/signals/traces/#propagation)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
