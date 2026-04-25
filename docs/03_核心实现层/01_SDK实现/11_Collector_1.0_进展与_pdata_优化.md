# Collector 1.0 进展与 pdata 优化跟踪

> **标准来源**: OpenTelemetry Collector SIG (2026-Q1 进展报告)
> **核心目标**: 跟踪 Collector 1.0 里程碑的进展、pdata API 的最新优化，以及对用户的影响

---

## 一、Collector 1.0 里程碑

### 1.1 为什么 1.0 重要？

OpenTelemetry Collector 自 2019 年发布以来，一直以 `v0.x` 版本迭代。1.0 版本标志着：

```text
Collector 1.0 的意义:
├── 稳定性承诺: API 和配置格式进入稳定状态
├── 企业采纳: 消除"beta 软件"的顾虑
├── 生态成熟: 插件市场、发行版、工具链完善
├── 长期支持: 提供明确的 LTS（长期支持）版本
└── 与 OpenTelemetry 整体 Graduation 申请协同
```

### 1.2 1.0 的准入标准

Collector SIG 定义的 1.0 发布标准：

| 标准 | 状态（2026-Q1） | 说明 |
|------|----------------|------|
| 核心组件稳定 | 🟡 接近完成 | Collector Core API 基本稳定 |
| 配置格式稳定 | 🟢 稳定 | OpenTelemetry Collector Configuration 已稳定 |
| 性能基准 | 🟢 完成 | 定义了标准性能测试套件 |
| 安全审查 | 🟡 进行中 | 第三方安全审计 |
| 文档完备 | 🟡 接近完成 | 用户文档和迁移指南 |
| 向后兼容策略 | 🟢 确定 | 稳定组件的废弃和移除策略已定义 |
| 关键 bug 清零 | 🟡 进行中 | P0/P1 级别 bug 修复 |

### 1.3 时间线预测

```text
Collector 版本演进:

2025 Q4:  v0.114.0 - v0.117.0
          └── 功能冻结准备，pdata API 重大优化

2026 Q1:  v0.118.0 - v0.121.0
          ├── Profiles 信号全面集成
          ├── pdata v2 API 发布
          └── 1.0 RC（Release Candidate）候选

2026 Q2:  v1.0.0 (预计)
          ├── 首个稳定版发布
          ├── 核心 API 稳定性保证
          └── 长期支持 (LTS) 通道开启

2026 H2:  v1.1.0+
          └── 新功能在 v1.x 中继续演进
```

---

## 二、pdata API 优化

### 2.1 什么是 pdata？

`pdata`（Protocol Buffers Data）是 Collector 内部使用的内存数据模型，对应 OTLP Protobuf 结构：

```text
数据流:

OTLP Protobuf (wire format)
    │
    ▼ decode
pdata (in-memory model)
    │
    ▼ process (processors)
pdata (modified)
    │
    ▼ encode
OTLP Protobuf / Other format
```

### 2.2 pdata v1 的问题

```text
pdata v1 的性能痛点:
├── 大量小对象分配: 每个 Attribute、Span 都单独分配
├── 深拷贝开销: Processor 修改数据时复制整个结构
├── 反射开销: 部分操作依赖反射
├── 内存碎片: 频繁的分配和释放导致 GC 压力
└── 缓存不友好: 数据结构分散，CPU 缓存命中率低
```

### 2.3 pdata v2 的优化

```text
pdata v2 的核心改进:

1. 对象池化 (Object Pooling)
   ├── 复用 AttributeMap、SpanSlice 等对象
   ├── 减少 GC 压力
   └── 性能提升: 10-30%

2. 写时复制优化 (Copy-on-Write)
   ├── 多个 Processor 读取相同数据时共享底层存储
   ├── 仅在修改时复制需要变更的部分
   └── 性能提升: 20-50%（读取密集型场景）

3. 扁平化存储 (Flat Buffer-like Layout)
   ├── 连续内存布局，提升 CPU 缓存命中率
   ├── 减少指针追踪
   └── 性能提升: 15-25%

4. 零拷贝解析 (Zero-Copy Parsing)
   ├── 从 Protobuf 解码时减少中间复制
   ├── 延迟数据解析（懒加载）
   └── 性能提升: 显著（尤其在过滤场景）

5. 不可变视图 (Immutable Views)
   ├── 提供只读接口，防止意外修改
   ├── 简化并发安全
   └── 更清晰的 API 契约
```

### 2.4 对用户的影响

| 用户类型 | 影响 | 行动 |
|---------|------|------|
| **Collector 用户** | 吞吐量提升，内存占用降低 | 升级到 1.0 即可获益 |
| **Processor 开发者** | API 可能有变化 | 阅读 pdata v2 迁移指南 |
| **Exporter 开发者** | 可能需要适配新 API | 关注 Collector Contrib 更新 |
| **自定义 Collector 构建者** | OCB 配置可能需要更新 | 测试构建流程 |

---

## 三、关键变更与迁移

### 3.1 配置变更

```yaml
# 旧配置 (v0.114 之前可能废弃)
exporters:
  otlp:
    endpoint: "http://localhost:4317"
    insecure: true  # ← 已废弃

# 新配置 (v0.115+)
exporters:
  otlp:
    endpoint: "http://localhost:4317"
    tls:
      insecure: true
```

### 3.2 自定义 Processor 迁移

```go
// pdata v1 (旧)
import "go.opentelemetry.io/collector/pdata/ptrace"

func (p *myProcessor) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 深拷贝可能发生在内部
    for i := 0; i < td.ResourceSpans().Len(); i++ {
        rs := td.ResourceSpans().At(i)
        // ...
    }
    return p.nextConsumer.ConsumeTraces(ctx, td)
}

// pdata v2 (新)
import "go.opentelemetry.io/collector/pdata/ptrace"

func (p *myProcessor) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 明确控制复制行为
    mutator := td.Mutator()  // 获取可修改视图

    for i := 0; i < mutator.ResourceSpans().Len(); i++ {
        rs := mutator.ResourceSpans().At(i)
        // 修改操作...
    }

    return p.nextConsumer.ConsumeTraces(ctx, mutator.Freeze())
}
```

---

## 四、升级建议

### 4.1 升级路径

```text
升级策略:

阶段1: 评估（1-2 周）
├── 审查当前的 Collector 配置
├── 列出使用的 Receiver / Processor / Exporter
├── 检查每个组件的稳定性等级
└── 在测试环境部署最新 v0.14x 版本

阶段2: 测试（2-4 周）
├── 运行功能测试
├── 性能基准对比（吞吐量、内存、延迟）
├── 验证所有 pipeline 正常工作
└── 测试配置热重载（如有使用）

阶段3: 生产升级（1-2 周）
├── 蓝绿部署或金丝雀升级
├── 监控关键指标：丢包率、延迟、错误率
├── 准备回滚方案
└── 全量切换
```

### 4.2 兼容性矩阵

| Collector 版本 | 推荐 SDK 版本 | OTLP 协议版本 | 稳定性 |
|---------------|--------------|--------------|--------|
| v0.110.0 - v0.113.0 | 1.4x+ | v1.0.0 - v1.1.0 | 稳定使用 |
| v0.114.0 - v0.117.0 | 1.4x+ | v1.0.0 - v1.3.0 | 功能冻结期 |
| v0.118.0+ (1.0 RC) | 1.4x+ | v1.0.0 - v1.10.0 | RC 测试 |
| v1.0.0 | 1.4x+ | v1.10.0 | 生产就绪 |

---

## 五、检查清单

- [ ] 跟踪 Collector SIG 的 1.0 进展公告
- [ ] 在测试环境验证最新 RC 版本
- [ ] 审查并更新自定义 Processor/Exporter 的 pdata 使用
- [ ] 验证 Collector 配置格式兼容性
- [ ] 性能基准测试对比（v0.11x vs v1.0）
- [ ] 准备生产升级的回滚方案
- [ ] 更新内部文档和 Runbook 中的 Collector 版本信息

---

## 六、参考资源

- OpenTelemetry Collector SIG Meeting Notes
- OpenTelemetry Collector Releases (GitHub)
- Collector 1.0 Progress Report (2026-Q1)
- pdata v2 Design Document

---

> **总结**: Collector 1.0 是 OpenTelemetry 生态成熟的关键标志。pdata v2 的优化将显著提升 Collector 的性能和可扩展性。建议用户在 1.0 RC 阶段即开始在测试环境验证，为正式版的生产部署做好准备。
