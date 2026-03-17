---
title: SLO设计与错误预算管理
description: 系统化的SLO设计方法论，包含SLI/SLO/SLA概念解析、错误预算计算与管理、多层级SLO体系设计以及可靠性工程实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 数据分析与洞察
tags:
  - slo
  - sli
  - sla
  - error-budget
  - reliability-engineering
status: published
---

# SLO设计与错误预算管理

> **版本**: OTLP v1.9.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约45分钟

---

## 1. SRE核心概念解析

### 1.1 SLI/SLO/SLA 概念区分

```
┌─────────────────────────────────────────────────────────────────┐
│              SLI / SLO / SLA 概念金字塔                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                         ┌───────────┐                          │
│                         │    SLA    │  ← 对外承诺              │
│                         │  服务等级 │    法律/商业约束         │
│                         │   协议    │    违约有后果            │
│                         └─────┬─────┘                          │
│                               │                                 │
│                    ┌──────────┴──────────┐                     │
│                    │                     │                     │
│              ┌─────┴─────┐         ┌─────┴─────┐              │
│              │    SLO    │         │   缓冲带   │              │
│              │  服务等级 │    ←    │  (Margin) │              │
│              │   目标    │         │           │              │
│              └─────┬─────┘         └───────────┘              │
│                    │                                            │
│              ┌─────┴─────┐                                      │
│              │    SLI    │  ← 测量指标                          │
│              │  服务等级 │    客观可测量                        │
│              │   指标    │                                      │
│              └───────────┘                                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

关系说明:
- SLI是SLO的基础，SLO是SLA的基础
- SLO通常比SLA更严格（留有余量）
- 一个SLA可能包含多个SLO
- 违反SLO会触发内部改进，违反SLA可能产生赔偿
```

### 1.2 概念详解

```yaml
# SLI (Service Level Indicator) 服务等级指标
定义: 系统某个方面健康状况的定量测量
特点:
  - 客观可测量
  - 与用户满意度相关
  - 长期保持稳定定义

常见SLI类型:
  可用性:
    定义: 服务可正常响应请求的时间比例
    计算: 可用时间 / 总时间
    示例: "99.99%的可用性"

  延迟:
    定义: 请求从发起到响应的时间
    计算: 分位值（P50, P95, P99）
    示例: "P99延迟 < 200ms"

  吞吐量:
    定义: 单位时间处理的请求量
    计算: 请求数 / 时间窗口
    示例: "支持10000 QPS"

  错误率:
    定义: 失败请求占总请求的比例
    计算: 错误请求数 / 总请求数
    示例: "错误率 < 0.1%"

  新鲜度:
    定义: 数据更新的及时程度
    计算: 当前时间 - 最后更新时间
    示例: "数据延迟 < 5分钟"

# SLO (Service Level Objective) 服务等级目标
定义: 对SLI设定的目标值
特点:
  - 可达成（Achievable）
  - 可测量（Measurable）
  - 有意义（Meaningful）
  - 可行动（Actionable）

示例SLO:
  - "月度可用性 >= 99.95%"
  - "P99延迟 < 300ms（24小时滚动窗口）"
  - "错误率 < 0.5%（7天滚动窗口）"

# SLA (Service Level Agreement) 服务等级协议
定义: 服务提供方与用户的正式协议
内容:
  - 承诺的SLO
  - 违约后果（赔偿、服务积分等）
  - 免责条款
  - 争议解决机制

示例SLA条款:
  - "月度可用性 >= 99.9%，否则赔偿月费10%"
  - "P99延迟 < 500ms，否则服务积分"
```

---

## 2. SLI设计方法论

### 2.1 SLI设计流程

```
┌─────────────────────────────────────────────────────────────────┐
│                    SLI设计五步流程                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Step 1: 识别关键用户旅程                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  系统功能分解 → 用户场景识别 → 关键路径确定              │   │
│  │                                                          │   │
│  │  示例：电商平台                                           │   │
│  │  • 浏览商品 → 加入购物车 → 下单 → 支付 → 查看订单        │   │
│  │  • 用户注册 → 登录 → 个人信息管理                        │   │
│  │  • 搜索 → 筛选 → 比较 → 购买                            │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Step 2: 确定系统边界                                          │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  明确控制范围 vs 依赖范围                                │   │
│  │                                                          │   │
│  │  用户请求 ──→ [我们的系统] ──→ 依赖服务                  │   │
│  │                  ↑                                        │   │
│  │              SLI测量点                                   │   │
│  │                                                          │   │
│  │  原则: SLI应反映用户真实体验                             │   │
│  │        区分可控与不可控因素                              │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Step 3: 选择SLI类型                                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  基于用户旅程选择指标类型                                │   │
│  │                                                          │   │
│  │  请求-响应型: 延迟、可用性、错误率                       │   │
│  │  数据处理型: 吞吐量、新鲜度、正确性                      │   │
│  │  存储型: 持久性、可用性、一致性                          │   │
│  │  流处理型: 延迟、完整性、有序性                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Step 4: 定义测量规范                                          │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  明确测量细节:                                           │   │
│  │  • 数据来源（Logs/Metrics/Traces）                       │   │
│  │  • 计算方法（成功/总数，分位值计算）                     │   │
│  │  • 时间窗口（1分钟/1小时/28天）                          │   │
│  │  • 采样策略（全量/采样）                                 │   │
│  │  • 异常处理（超时、重试、批处理）                        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Step 5: 验证与迭代                                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  验证SLI有效性:                                          │   │
│  │  • 与用户满意度相关性                                    │   │
│  │  • 可达成性验证                                          │   │
│  │  • 可操作性测试                                          │   │
│  │                                                          │   │
│  │  迭代优化:                                               │   │
│  │  • 根据数据调整阈值                                      │   │
│  │  • 补充遗漏场景                                          │   │
│  │  • 优化测量方法                                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 不同服务类型的SLI设计

```yaml
# 按服务类型设计SLI

API服务 (请求-响应型):
  用户旅程: 发送请求 → 接收响应

  SLI-1 可用性:
    定义: 成功响应比例
    成功条件: HTTP 2xx/3xx 且 在超时时间内
    计算: successful_requests / total_requests

  SLI-2 延迟:
    定义: 响应时间分位值
    分位: P50, P95, P99
    计算: histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))

  SLI-3 错误率:
    定义: 错误响应比例
    错误条件: HTTP 5xx 或 超时
    计算: error_requests / total_requests

数据处理服务 (批处理型):
  用户旅程: 提交任务 → 等待处理 → 获取结果

  SLI-1 吞吐量:
    定义: 单位时间处理记录数
    计算: processed_records / time_window

  SLI-2 新鲜度:
    定义: 数据处理的延迟
    计算: processing_time - event_time

  SLI-3 正确性:
    定义: 正确处理比例
    计算: successful_jobs / total_jobs

  SLI-4 覆盖率:
    定义: 应处理数据实际被处理的比例
    计算: processed_records / expected_records
```

### 2.3 SLI测量实现

```python
"""
SLI测量实现示例
"""
from typing import Dict
import numpy as np

class SLIMeasurer:
    """SLI测量器"""

    def measure_availability(self,
                            successful_requests: int,
                            total_requests: int) -> Dict:
        """测量可用性SLI"""
        if total_requests == 0:
            return {'value': 1.0, 'valid': False, 'reason': 'no_data'}

        availability = successful_requests / total_requests

        return {
            'value': availability,
            'successful': successful_requests,
            'total': total_requests,
            'valid': True,
            'percentage': f"{availability * 100:.4f}%"
        }

    def measure_latency(self,
                       latencies: list,
                       percentiles: list = [50, 95, 99]) -> Dict:
        """测量延迟SLI"""
        if not latencies:
            return {'valid': False, 'reason': 'no_data'}

        sorted_latencies = sorted(latencies)
        n = len(sorted_latencies)

        results = {
            'valid': True,
            'count': n,
            'min_ms': sorted_latencies[0],
            'max_ms': sorted_latencies[-1],
            'mean_ms': np.mean(latencies),
            'percentiles': {}
        }

        for p in percentiles:
            idx = int(n * p / 100)
            idx = min(idx, n - 1)
            results['percentiles'][f'P{p}'] = sorted_latencies[idx]

        return results
```

---

## 3. 错误预算管理

### 3.1 错误预算计算

```python
"""
错误预算计算与管理
"""
from dataclasses import dataclass
from typing import Dict

@dataclass
class ErrorBudget:
    """错误预算"""
    total_requests: int
    slo_target: float  # 例如 0.999
    window_days: int

    @property
    def error_budget_percent(self) -> float:
        """错误预算百分比"""
        return (1 - self.slo_target) * 100

    @property
    def error_budget_requests(self) -> int:
        """错误预算请求数"""
        return int(self.total_requests * (1 - self.slo_target))

    @property
    def error_budget_minutes(self) -> float:
        """错误预算分钟数（用于可用性）"""
        total_minutes = self.window_days * 24 * 60
        return total_minutes * (1 - self.slo_target)

    def calculate_consumption(self,
                             actual_errors: int,
                             actual_requests: int) -> Dict:
        """计算错误预算消耗"""
        if actual_requests == 0:
            return {'valid': False, 'reason': 'no_data'}

        actual_error_rate = actual_errors / actual_requests
        budget_consumed = actual_errors / self.error_budget_requests if self.error_budget_requests > 0 else 0

        return {
            'valid': True,
            'error_budget_percent': self.error_budget_percent,
            'error_budget_requests': self.error_budget_requests,
            'actual_errors': actual_errors,
            'actual_error_rate': actual_error_rate,
            'budget_consumed': budget_consumed,
            'budget_consumed_percent': budget_consumed * 100,
            'budget_remaining': 1 - budget_consumed,
            'budget_remaining_percent': (1 - budget_consumed) * 100,
            'status': 'healthy' if budget_consumed < 0.5 else 'at_risk' if budget_consumed < 1.0 else 'exhausted'
        }
```

### 3.2 PromQL错误预算查询

```promql
# ===== 错误预算计算查询 =====

# 1. 计算月度错误预算消耗
(
  sum(increase(http_requests_total{status=~"5.."}[30d]))
  /
  (
    sum(increase(http_requests_total[30d]))
    * (1 - 0.999)  # SLO目标 99.9%
  )
) * 100

# 2. 错误预算消耗速率（1小时窗口）
(
  sum(increase(http_requests_total{status=~"5.."}[1h]))
  /
  (
    sum(increase(http_requests_total[1h]))
    * (1 - 0.999)
  )
) * 100

# 3. 预计耗尽时间（基于当前消耗速率）
# 如果消耗速率 > 1，计算剩余天数
(
  (1 -
    sum(increase(http_requests_total{status=~"5.."}[30d]))
    /
    (sum(increase(http_requests_total[30d])) * (1 - 0.999))
  )
  /
  (
    sum(increase(http_requests_total{status=~"5.."}[1h]))
    /
    (sum(increase(http_requests_total[1h])) * (1 - 0.999))
  )
  * (1/24)  # 转换为天
)

# 4. SLO合规状态
(
  sum(rate(http_requests_total{status=~"2..|3.."}[30d]))
  /
  sum(rate(http_requests_total[30d]))
) >= 0.999
```

---

## 4. 多层级SLO体系

### 4.1 组织级SLO架构

```
┌─────────────────────────────────────────────────────────────────┐
│                    多层级SLO体系架构                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Level 1: 业务SLO                                                │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  目标: 反映最终用户体验                                  │   │
│  │  示例:                                                   │   │
│  │  • 订单完成率 >= 99.5%                                   │   │
│  │  • 支付成功率 >= 99.9%                                   │   │
│  │  • 页面加载时间 P99 < 2s                                 │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Level 2: 产品/应用SLO                                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  目标: 支撑业务SLO的应用层指标                           │   │
│  │  示例:                                                   │   │
│  │  • 订单服务可用性 >= 99.95%                              │   │
│  │  • 支付API P99延迟 < 200ms                               │   │
│  │  • 用户服务错误率 < 0.1%                                 │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Level 3: 服务SLO                                                │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  目标: 单个服务的可靠性指标                              │   │
│  │  示例:                                                   │   │
│  │  • 订单服务实例可用性 >= 99.99%                          │   │
│  │  • 数据库查询P99 < 10ms                                  │   │
│  │  • 缓存命中率 >= 95%                                     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Level 4: 基础设施SLO                                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  目标: 支撑上层服务的基础设施指标                        │   │
│  │  示例:                                                   │   │
│  │  • 节点可用性 >= 99.99%                                  │   │
│  │  • 网络延迟P99 < 1ms                                     │   │
│  │  • 存储IO P99 < 5ms                                      │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  层级关系:                                                       │
│  • 下层SLO支撑上层SLO                                           │
│  • 违反下层SLO可能导致违反上层SLO                               │
│  • 故障传播: 基础设施 → 服务 → 产品 → 业务                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 SLO依赖管理

```yaml
# SLO依赖关系定义

service: "order-service"
slos:
  - name: "订单创建可用性"
    target: 99.95%
    dependencies:
      - service: "payment-service"
        slo: "支付处理可用性"
        target: 99.99%
        criticality: high  # 强依赖

      - service: "inventory-service"
        slo: "库存查询可用性"
        target: 99.9%
        criticality: high

      - service: "user-service"
        slo: "用户验证可用性"
        target: 99.5%
        criticality: medium  # 弱依赖（有降级方案）

      - service: "notification-service"
        slo: "通知发送可用性"
        target: 99%
        criticality: low  # 异步，不影响主流程

# 依赖风险计算
risk_analysis:
  # 强依赖故障对本服务的影响
  strong_dependency_impact: "级联故障风险高"

  # 计算理论最大可用性
  theoretical_max_availability: |
    99.95% * 99.99% * 99.9% * 99.5% ≈ 99.34%

  # 建议
  recommendations:
    - "考虑增加payment-service的冗余"
    - "inventory-service需要缓存降级方案"
    - "user-service认证可本地缓存"
```

---

## 5. 可靠性指标设计

### 5.1 四大黄金信号

```python
"""
四大黄金信号监控实现
"""

# ===== PromQL黄金信号查询 =====

LATENCY_GOLDEN_SIGNAL = """
# 延迟 - 四大黄金信号之一
# 请求处理所需时间

# P50延迟
histogram_quantile(0.50,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)

# P95延迟
histogram_quantile(0.95,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)

# P99延迟
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)
"""

TRAFFIC_GOLDEN_SIGNAL = """
# 流量 - 四大黄金信号之一
# 系统承受的请求量

# HTTP请求速率 (QPS)
sum(rate(http_requests_total[5m])) by (service, method)

# 并发连接数
count(increase(http_requests_total[1m])) by (service)

# 网络带宽
sum(rate(container_network_transmit_bytes_total[5m])) by (pod)
"""

ERRORS_GOLDEN_SIGNAL = """
# 错误 - 四大黄金信号之一
# 请求失败率

# HTTP错误率
sum(rate(http_requests_total{status=~"5.."}[5m])) by (service)
/
sum(rate(http_requests_total[5m])) by (service)

# gRPC错误率
sum(rate(grpc_server_handled_total{grpc_code!="OK"}[5m])) by (service)
/
sum(rate(grpc_server_handled_total[5m])) by (service)

# 应用错误率
sum(rate(application_exceptions_total[5m])) by (service, type)
"""

SATURATION_GOLDEN_SIGNAL = """
# 饱和度 - 四大黄金信号之一
# 资源使用接近上限的程度

# CPU使用率
100 - (avg by (instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)

# 内存使用率
(
  node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes
) / node_memory_MemTotal_bytes * 100

# 磁盘使用率
(
  node_filesystem_size_bytes - node_filesystem_avail_bytes
) / node_filesystem_size_bytes * 100

# 连接数饱和度
count(increase(http_requests_total[1m])) / <configured_max_connections> * 100
"""
```

### 5.2 USE方法实践

```python
"""
USE方法: Utilization, Saturation, Errors
适用于资源类指标设计
"""

USE_METHOD_QUERIES = {
    "cpu": {
        "utilization": """
            # CPU使用率
            100 - (avg by (instance) (
              irate(node_cpu_seconds_total{mode="idle"}[5m])
            ) * 100)
        """,
        "saturation": """
            # CPU饱和度（运行队列长度）
            node_load1 / count without(cpu, mode) (
              node_cpu_seconds_total{mode="idle"}
            )
        """,
        "errors": """
            # CPU错误（通常很少）
            # 可关注thermal throttling
            node_thermal_throttle_count
        """
    },

    "memory": {
        "utilization": """
            # 内存使用率
            (
              node_memory_MemTotal_bytes
              - node_memory_MemAvailable_bytes
            ) / node_memory_MemTotal_bytes * 100
        """,
        "saturation": """
            # 内存饱和度（交换使用）
            (
              node_memory_SwapTotal_bytes
              - node_memory_SwapFree_bytes
            ) / node_memory_SwapTotal_bytes * 100
        """,
        "errors": """
            # OOM错误
            increase(node_vmstat_oom_kill[5m])
        """
    },

    "disk": {
        "utilization": """
            # 磁盘空间使用率
            (
              node_filesystem_size_bytes
              - node_filesystem_avail_bytes
            ) / node_filesystem_size_bytes * 100
        """,
        "saturation": """
            # IO饱和度（等待时间）
            rate(node_disk_io_time_weighted_seconds_total[5m])
        """,
        "errors": """
            # 磁盘错误
            node_disk_io_errors_total
        """
    }
}
```

---

## 6. 实战案例

### 6.1 电商系统SLO设计案例

```yaml
# 电商平台SLO设计

business:
  name: "电商平台"

  level_1_business_slos:
    - name: "订单完成率"
      target: 99.5%
      description: "用户成功完成订单的比例"
      measurement: |
        completed_orders / initiated_checkouts

    - name: "支付成功率"
      target: 99.9%
      measurement: |
        successful_payments / payment_attempts

    - name: "首页加载时间"
      target: "P99 < 1.5s"
      measurement: |
        histogram_quantile(0.99, page_load_duration)

services:
  order-service:
    slos:
      - type: availability
        target: 99.95%
        window: 30d

      - type: latency
        target: "P99 < 200ms"
        endpoint: "POST /api/orders"

      - type: error_rate
        target: "< 0.1%"

    error_budget_policy:
      healthy:
        action: "正常发布"

      at_risk:
        condition: "50% <= budget < 75%"
        action: "谨慎发布，增加监控"

      critical:
        condition: "75% <= budget < 100%"
        action: "暂停非紧急发布"

      exhausted:
        action: "暂停所有发布，启动事故响应"

  payment-service:
    slos:
      - type: availability
        target: 99.99%

      - type: latency
        target: "P99 < 100ms"

    dependencies:
      - "payment-gateway (第三方)"
      - "fraud-detection-service"

  product-catalog:
    slos:
      - type: availability
        target: 99.9%

      - type: latency
        target: "P99 < 50ms"
        # 允许缓存命中的高延迟

      - type: freshness
        target: "price update < 1min"
```

### 6.2 SLO监控Dashboard

```python
"""
Grafana SLO监控Dashboard配置
"""

SLO_DASHBOARD = {
    "title": "SLO监控大屏",
    "panels": [
        {
            "title": "可用性SLO",
            "type": "stat",
            "targets": [{
                "expr": """
                sum(rate(http_requests_total{status=~"2..|3.."}[30d]))
                /
                sum(rate(http_requests_total[30d]))
                """,
                "legendFormat": "可用性"
            }],
            "thresholds": [
                {"color": "red", "value": 0},
                {"color": "yellow", "value": 0.999},
                {"color": "green", "value": 0.9995}
            ]
        },
        {
            "title": "错误预算剩余",
            "type": "gauge",
            "targets": [{
                "expr": """
                100 - (
                  sum(increase(http_requests_total{status=~"5.."}[30d]))
                  /
                  (sum(increase(http_requests_total[30d])) * 0.001)
                  * 100
                )
                """,
                "legendFormat": "剩余预算 %"
            }],
            "fieldConfig": {
                "max": 100,
                "min": 0,
                "thresholds": [
                    {"color": "red", "value": 0},
                    {"color": "yellow", "value": 25},
                    {"color": "green", "value": 50}
                ]
            }
        },
        {
            "title": "延迟SLO趋势",
            "type": "timeseries",
            "targets": [
                {
                    "expr": "histogram_quantile(0.99, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
                    "legendFormat": "P99"
                },
                {
                    "expr": "histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
                    "legendFormat": "P95"
                }
            ],
            "alert": {
                "name": "延迟SLO告警",
                "condition": "P99 > 0.3",
                "for": "5m"
            }
        }
    ]
}
```

---

## 7. 最佳实践总结

### 7.1 SLO实施检查清单

```markdown
## SLO设计与实施检查清单

### 设计阶段
- [ ] 识别关键用户旅程
- [ ] 与业务方确认SLI与业务目标关联
- [ ] 评估历史数据，确保SLO可达成
- [ ] 设计多层级SLO体系
- [ ] 定义明确的测量方法和数据来源

### 实施阶段
- [ ] 配置Prometheus指标采集
- [ ] 编写准确的SLI PromQL查询
- [ ] 创建SLO监控Dashboard
- [ ] 配置错误预算告警规则
- [ ] 建立错误预算消耗政策

### 运营阶段
- [ ] 定期（建议每周）审查SLO达成情况
- [ ] 分析错误预算消耗模式
- [ ] 基于数据调整SLO（季度审查）
- [ ] 更新Runbook，记录SLO违规处理流程
- [ ] 培训团队，建立SLO文化

### 持续改进
- [ ] 收集反馈，优化SLI定义
- [ ] 逐步提高SLO目标（如有余量）
- [ ] 引入新的SLI覆盖遗漏场景
- [ ] 自动化SLO报告生成
```

### 7.2 常见陷阱与规避

```yaml
# SLO设计常见陷阱

陷阱1: 过度工程
  表现: 追求99.999%可用性，但业务只需要99.9%
  成本: 10倍成本提升，边际收益递减
  规避:
    - 与业务确认真实需求
    - 使用错误预算理念
    - 成本-收益分析

陷阱2: SLI与用户体验脱节
  表现: 监控CPU使用率，但用户关心的是响应时间
  问题: 系统指标正常，但用户体验差
  规避:
    - 从用户视角定义SLI
    - 使用RUM（真实用户监控）数据
    - 定期进行用户满意度调研

陷阱3: SLO数量过多
  表现: 一个服务定义20+个SLO
  问题: 注意力分散，难以维护
  规避:
    - 每个服务2-5个核心SLO
    - 区分SLO和监控指标
    - 优先级排序

陷阱4: 忽视依赖关系
  表现: 强依赖服务故障导致本服务SLO违规
  问题: 责任边界不清，改进方向错误
  规避:
    - 明确SLO依赖关系
    - 设计降级方案
    - 与依赖方对齐SLO

陷阱5: SLO一成不变
  表现: 3年不调整SLO
  问题: 无法反映系统演进和业务变化
  规避:
    - 季度SLO审查
    - 基于历史数据调整
    - 记录调整理由
```

---

## 总结

本指南系统介绍了SLO设计与错误预算管理的完整方法论：

1. **核心概念**: 明确区分SLI/SLO/SLA，建立正确的SRE理念
2. **SLI设计**: 基于用户旅程选择指标，确保可测量、有意义
3. **SLO设定**: 遵循可达成、有挑战、有余量的原则
4. **错误预算**: 量化可靠性风险，平衡创新与稳定性
5. **多层体系**: 建立从基础设施到业务的完整SLO架构

关键成功因素：

- 从用户体验出发定义SLO
- 保持SLO数量精简（2-5个/服务）
- 建立错误预算驱动的发布决策
- 持续迭代优化SLO定义
- 培养团队的SRE文化
