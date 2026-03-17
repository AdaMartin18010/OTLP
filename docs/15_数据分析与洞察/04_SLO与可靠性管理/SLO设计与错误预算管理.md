# SLO设计与错误预算管理

## 目录

- [SLO设计与错误预算管理](#slo设计与错误预算管理)
  - [目录](#目录)
  - [一、SLO/SLI/SLA概念体系](#一sloslisla概念体系)
    - [1.1 核心概念定义](#11-核心概念定义)
      - [SLI (Service Level Indicator)](#sli-service-level-indicator)
      - [SLO (Service Level Objective)](#slo-service-level-objective)
      - [SLA (Service Level Agreement)](#sla-service-level-agreement)
    - [1.2 可用性等级对照表](#12-可用性等级对照表)
  - [二、SLO设计方法论](#二slo设计方法论)
    - [2.1 用户旅程映射法](#21-用户旅程映射法)
    - [2.2 SLO设计模板](#22-slo设计模板)
  - [三、错误预算计算与管理](#三错误预算计算与管理)
    - [3.1 错误预算概念](#31-错误预算概念)
    - [3.2 错误预算计算](#32-错误预算计算)
    - [3.3 错误预算策略](#33-错误预算策略)
  - [四、SLO监控与告警](#四slo监控与告警)
    - [4.1 Burn Rate告警机制](#41-burn-rate告警机制)
    - [4.2 Prometheus告警规则](#42-prometheus告警规则)
    - [4.3 Grafana仪表板配置](#43-grafana仪表板配置)
  - [五、生产环境最佳实践](#五生产环境最佳实践)
    - [5.1 SLO实施检查清单](#51-slo实施检查清单)
    - [5.2 工具推荐](#52-工具推荐)

---

## 一、SLO/SLI/SLA概念体系

### 1.1 核心概念定义

```
┌─────────────────────────────────────────────────────────────────┐
│                    可靠性工程核心概念金字塔                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                           ┌─────────┐                           │
│                           │   SLA   │  ← 对外承诺(商业合同)       │
│                           │ 99.95%  │                           │
│                           └────┬────┘                           │
│                                │                                │
│                      ┌─────────┴─────────┐                      │
│                      │       SLO         │  ← 内部目标           │
│                      │     99.99%        │                      │
│                      └─────────┬─────────┘                      │
│                                │                                │
│              ┌─────────────────┼─────────────────┐              │
│              │                 │                 │              │
│        ┌─────┴─────┐     ┌─────┴─────┐     ┌─────┴─────┐       │
│        │    SLI    │     │    SLI    │     │    SLI    │       │
│        │ 可用性    │     │  延迟     │     │ 错误率    │       │
│        │ 99.99%   │     │  <100ms   │     │  <0.01%   │       │
│        └───────────┘     └───────────┘     └───────────┘       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

#### SLI (Service Level Indicator)

SLI是**可量化**的服务质量测量指标。

**常见SLI分类：**

| 类别 | 指标示例 | 适用场景 |
|------|----------|----------|
| 可用性 | 服务正常运行时间比例 | 所有在线服务 |
| 延迟 | P50/P90/P99/P99.9 | API服务、数据库 |
| 吞吐量 | 每秒处理请求数(RPS) | 高并发服务 |
| 错误率 | 失败请求百分比 | 所有HTTP服务 |
| 新鲜度 | 数据更新时间延迟 | 数据管道、缓存 |
| 正确性 | 数据准确性 | 金融系统 |

#### SLO (Service Level Objective)

SLO是**目标值**，定义了SLI在特定时间段内应达到的水平。

```yaml
# SLO定义示例
slo_definition:
  service_name: "payment-api"
  sli:
    metric: "http_request_success_rate"
  target: 0.9999  # 99.99%
  time_window: "30d"
```

#### SLA (Service Level Agreement)

SLA是**具有法律效力的合同承诺**，通常比SLO更保守。

### 1.2 可用性等级对照表

| 可用性等级 | 可用性目标 | 年度停机时间 | 适用场景 |
|-----------|-----------|-------------|----------|
| 两个9 | 99% | 3.65天 | 内部工具 |
| 三个9 | 99.9% | 8.76小时 | 一般业务系统 |
| 四个9 | 99.99% | 52.6分钟 | 关键业务系统 |
| 五个9 | 99.999% | 5.26分钟 | 金融核心系统 |

---

## 二、SLO设计方法论

### 2.1 用户旅程映射法

```
┌─────────────────────────────────────────────────────────────────┐
│                      电商平台用户旅程地图                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  浏览商品 → 加入购物车 → 结算支付 → 订单追踪 → 售后服务           │
│     │          │          │          │          │               │
│     ▼          ▼          ▼          ▼          ▼               │
│  搜索延迟    添加延迟    支付成功率   查询延迟    响应时间         │
│  结果准确    库存准确    交易延迟    状态准确    解决率          │
│                                                                 │
│  关键路径: 支付流程 (浏览→购物车→支付→确认) - 直接影响收入        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 SLO设计模板

```yaml
# 完整的SLO定义模板
service_level_objective:
  metadata:
    name: "payment-service-availability"
    service: "payment-service"
    team: "payments-platform"

  sli:
    description: "支付API的可用性"
    metric_source: "prometheus"
    query: |
      sum(rate(http_requests_total{status=~"2..|3.."}[5m]))
      /
      sum(rate(http_requests_total[5m]))

  objective:
    target: 0.9999
    window:
      type: "rolling"
      duration: "30d"

  alerting:
    burn_rate:
      fast_burn:
        multiplier: 14.4
        duration: "1h"
        severity: "critical"
      slow_burn:
        multiplier: 2
        duration: "6h"
        severity: "warning"

  error_budget:
    initial: 0.0001
    alert_at: [0.25, 0.5, 0.75, 0.9, 1.0]
```

---

## 三、错误预算计算与管理

### 3.1 错误预算概念

```
┌─────────────────────────────────────────────────────────────────┐
│                        错误预算概念图解                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  SLO = 99.9%                                                    │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │███████████████████████████████████████████████████████│   │
│  │                                                       │   │
│  │  可用性: 99.9% = 43,156.8分钟  │  错误预算: 0.1% = 43.2分钟│
│  │  (正常服务时间)                 │  (允许停机时间)            │
│  │                                                       │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  错误预算消耗:                                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │████████████████████████████████████████░░░░░░░░░░░░░░░░░│   │
│  │                                        │                │   │
│  │              已使用 75%                 │   剩余 25%     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 错误预算计算

```python
class ErrorBudget:
    """错误预算计算与管理"""

    def __init__(self, slo_target: float, time_window_days: int):
        self.slo_target = slo_target
        self.time_window_days = time_window_days

    def calculate_budget(self) -> dict:
        """计算错误预算"""
        total_minutes = self.time_window_days * 24 * 60
        error_budget_ratio = 1 - self.slo_target
        error_budget_minutes = total_minutes * error_budget_ratio

        return {
            "slo_target": f"{self.slo_target*100:.4f}%",
            "error_budget_ratio": f"{error_budget_ratio*100:.4f}%",
            "error_budget_minutes": round(error_budget_minutes, 2),
            "daily_allowance": round(error_budget_minutes / self.time_window_days, 2)
        }

# 不同SLO等级的错误预算对比
for slo in [0.99, 0.999, 0.9999]:
    eb = ErrorBudget(slo, 30)
    budget = eb.calculate_budget()
    print(f"SLO {budget['slo_target']}: 允许停机 {budget['error_budget_minutes']} 分钟/月")
```

### 3.3 错误预算策略

```yaml
# 错误预算管理策略
error_budget_policies:

  consumption_stages:
    healthy:  # 0-50%
      status: "正常"
      actions: ["正常发布节奏"]
      freeze_releases: false

    warning:  # 75-90%
      status: "警告"
      actions: ["暂停非关键发布", "每日状态同步"]
      require_approval: true

    critical:  # 90-100%
      status: "严重"
      actions: ["暂停所有发布", "仅允许紧急修复"]
      freeze_releases: true

    depleted:  # 100%+
      status: "已耗尽"
      actions: ["完全发布冻结", "全员投入稳定性"]
      war_room: true

  fast_burn_detection:
    - name: "1小时快速消耗"
      condition: "1小时内消耗 > 2% 月度预算"
      multiplier: 14.4
      action: "立即告警，暂停发布"
```

---

## 四、SLO监控与告警

### 4.1 Burn Rate告警机制

```python
class BurnRateCalculator:
    """
    Burn Rate = 当前错误率 / 允许错误率

    示例:
    - SLO = 99.9% (允许错误率 = 0.1%)
    - 当前1小时错误率 = 1%
    - Burn Rate = 1% / 0.1% = 10x
    """

    def __init__(self, slo_target: float):
        self.slo_target = slo_target
        self.allowed_error_rate = 1 - slo_target

    def calculate(self, current_error_rate: float) -> dict:
        burn_rate = current_error_rate / self.allowed_error_rate

        return {
            "burn_rate": round(burn_rate, 2),
            "severity": self._get_severity(burn_rate)
        }

    def _get_severity(self, burn_rate: float) -> str:
        if burn_rate >= 14.4: return "CRITICAL"
        elif burn_rate >= 6: return "HIGH"
        elif burn_rate >= 2: return "MEDIUM"
        else: return "LOW"
```

### 4.2 Prometheus告警规则

```yaml
# prometheus-slo-alerts.yml
groups:
  - name: slo_availability_alerts
    interval: 60s
    rules:
      # SLI记录规则
      - record: slo:sli:availability:ratio_rate5m
        expr: |
          sum(rate(http_requests_total{status=~"2..|3.."}[5m]))
          /
          sum(rate(http_requests_total[5m]))

      # 快速燃烧告警 (14.4x)
      - alert: SLOFastBurnRate
        expr: |
          slo:sli:availability:ratio_rate1h < 0.999
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "SLO快速燃烧告警"
          action: "暂停非紧急发布，检查服务状态"

      # 错误预算告警
      - alert: SLOErrorBudgetExhaustion
        expr: |
          (1 - slo:sli:availability:ratio_rate30d) / (1 - 0.999) > 0.75
        labels:
          severity: warning
        annotations:
          summary: "错误预算即将耗尽"
```

### 4.3 Grafana仪表板配置

```json
{
  "dashboard": {
    "title": "SLO监控仪表板",
    "panels": [
      {
        "title": "可用性",
        "type": "stat",
        "targets": [{
          "expr": "slo:sli:availability:ratio_rate30d"
        }],
        "fieldConfig": {
          "defaults": {
            "unit": "percentunit",
            "thresholds": {
              "steps": [
                {"color": "red", "value": 0},
                {"color": "yellow", "value": 0.99},
                {"color": "green", "value": 0.999}
              ]
            }
          }
        }
      },
      {
        "title": "错误预算消耗",
        "type": "gauge",
        "targets": [{
          "expr": "(1 - slo:sli:availability:ratio_rate30d) / (1 - 0.999)"
        }],
        "fieldConfig": {
          "defaults": {
            "thresholds": {
              "steps": [
                {"color": "green", "value": 0},
                {"color": "yellow", "value": 0.5},
                {"color": "red", "value": 0.9}
              ]
            }
          }
        }
      }
    ]
  }
}
```

---

## 五、生产环境最佳实践

### 5.1 SLO实施检查清单

```yaml
设计阶段:
  - [ ] 识别所有关键用户旅程
  - [ ] 为每个旅程定义SLI
  - [ ] 基于历史数据设定初始SLO
  - [ ] 设计错误预算计算方式
  - [ ] 制定发布冻结策略

实施阶段:
  - [ ] 部署指标采集系统
  - [ ] 配置SLI计算规则
  - [ ] 部署SLO监控仪表板
  - [ ] 配置Burn Rate告警
  - [ ] 编写SLO运行手册

运营阶段:
  - [ ] 定期审查SLO达成情况
  - [ ] 每月发布错误预算报告
  - [ ] 每季度回顾并调整SLO
```

### 5.2 工具推荐

| 工具 | 功能 | 链接 |
|------|------|------|
| Sloth | SLO代码生成 | github.com/slok/sloth |
| Pyrra | K8s原生SLO管理 | github.com/pyrra-dev/pyrra |
| OpenSLO | SLO标准规范 | openslo.com |

---

*文档版本: 1.0.0*
*维护团队: OTLP项目数据分析与洞察模块*
