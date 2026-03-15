# OpenTelemetry Collector v0.147.0 更新摘要

> **状态**: 内容对齐中
> **目标版本**: v0.147.0 (2026年3月发布)
> **当前项目版本**: v0.113.0 → v0.147.0

## 版本跨度

本次更新覆盖 **34个版本** (v0.113.0 → v0.147.0)，跨越约4个月开发周期。

## 关键更新内容

### 1. 声明式配置 GA (1.0.0)

- **状态**: Stable (正式版)
- **影响**: 配置文件格式可能不再向后兼容
- **迁移指南**: 参见官方文档

### 2. OTTL 上下文推断增强

- **新增**: 跨信号属性访问
- **场景**: 在span上下文中直接访问resource属性

### 3. 组件稳定性升级

| 组件 | v0.113.0 | v0.147.0 | 变化 |
|:-----|:--------:|:--------:|:----:|
| filelog receiver | Beta | **Stable** | ⬆️ |
| hostmetrics receiver | Beta | **Stable** | ⬆️ |
| k8sattributes processor | Beta | **Stable** | ⬆️ |
| prometheus exporter | Beta | **Stable** | ⬆️ |
| loadbalancing exporter | Alpha | **Beta** | ⬆️ |

### 4. 性能优化

- **pprof扩展**: 增强性能分析能力
- **内存分配**: 减少processor链中的内存拷贝
- **批处理**: 改进batch processor的调度算法

## 破坏性变更

1. **声明式配置**: 配置文件schema变更
2. **组件废弃**: 部分Alpha组件移除
3. **默认端口**: 部分receiver默认端口调整

## 参考资源

- [v0.147.0 Release Notes](https://github.com/open-telemetry/opentelemetry-collector/releases/tag/v0.147.0)
- [Migration Guide](https://opentelemetry.io/docs/collector/migration/)

---
**更新日期**: 2026年3月16日
