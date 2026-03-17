---
title: Collector日常运维指南
description: OpenTelemetry Collector日常运维管理，包含监控告警、日志管理、备份策略、证书管理
version: OTLP v1.10.0
collector_version: v0.147.0
date: 2026-03-17
category: 部署运维
tags:
  - operations
  - monitoring
  - alerting
  - maintenance
status: published
---

# Collector日常运维指南

> **运维等级**: 生产级
> **适用场景**: 大规模Collector集群运维
> **最后更新**: 2026-03-17

---

## 1. 运维架构

### 1.1 Collector运维层次

```
┌─────────────────────────────────────────────────────────────────┐
│                    Collector运维架构                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    应用层                                │   │
│  │  • 配置管理 (ConfigMap/GitOps)                          │   │
│  │  • 服务发现 (Service Discovery)                         │   │
│  │  • 流量管理 (Traffic Management)                        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│  ┌───────────────────────────▼───────────────────────────┐     │
│  │                    监控告警层                           │     │
│  │  • 指标收集 (Metrics)                                   │     │
│  │  • 告警规则 (Alerting)                                  │     │
│  │  • 日志聚合 (Logging)                                   │     │
│  │  • 链路追踪 (Tracing)                                   │     │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│  ┌───────────────────────────▼───────────────────────────┐     │
│  │                    基础设施层                           │     │
│  │  • 资源管理 (CPU/Memory/Storage)                        │     │
│  │  • 网络管理 (Network/DNS)                               │     │
│  │  • 证书管理 (TLS Certificates)                          │     │
│  │  • 备份恢复 (Backup/Restore)                            │     │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 监控指标

### 2.1 关键性能指标

| 指标名称 | 类型 | 告警阈值 | 说明 |
|----------|------|----------|------|
| `otelcol_receiver_accepted_spans` | Counter | - | 接收Span数 |
| `otelcol_receiver_refused_spans` | Counter | > 0 | 拒绝Span数 |
| `otelcol_exporter_queue_size` | Gauge | > 80% | 发送队列大小 |
| `otelcol_exporter_send_failed_spans` | Counter | > 0 | 发送失败数 |
| `otelcol_process_memory_rss` | Gauge | > 80% | 内存使用 |
| `otelcol_process_cpu_seconds` | Counter | > 80% | CPU使用 |
| `otelcol_processor_tail_sampling_decision_count` | Counter | - | 采样决策数 |
| `otelcol_processor_batch_send_size` | Histogram | - | 批次大小 |
| `otelcol_collector_uptime` | Gauge | - | 运行时间 |

### 2.2 Prometheus告警规则

```yaml
# collector-alerts.yml
groups:
  - name: collector-health
    rules:
      # 数据接收异常
      - alert: CollectorHighRefusalRate
        expr: |
          (
            sum(rate(otelcol_receiver_refused_spans_total[5m]))
            /
            sum(rate(otelcol_receiver_accepted_spans_total[5m]))
          ) > 0.01
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Collector拒绝率过高"
          description: "Collector {{ $labels.instance }} 拒绝率超过1%"

      # 发送队列积压
      - alert: CollectorQueueBackingUp
        expr: |
          otelcol_exporter_queue_size / otelcol_exporter_queue_capacity > 0.8
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Collector发送队列积压"
          description: "队列使用率超过80%，可能导致数据丢失"

      # 发送失败
      - alert: CollectorSendErrors
        expr: |
          sum(rate(otelcol_exporter_send_failed_spans_total[5m])) > 0
        for: 2m
        labels:
          severity: warning
        annotations:
          summary: "Collector发送失败"
          description: "无法发送数据到后端，请检查网络连接"

      # 内存使用过高
      - alert: CollectorHighMemoryUsage
        expr: |
          otelcol_process_memory_rss / otelcol_process_memory_limit > 0.85
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Collector内存使用过高"
          description: "内存使用率超过85%"

      # CPU使用过高
      - alert: CollectorHighCPUUsage
        expr: |
          rate(otelcol_process_cpu_seconds_total[5m]) > 0.8
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Collector CPU使用过高"
          description: "CPU使用率超过80%"

      # 实例宕机
      - alert: CollectorInstanceDown
        expr: |
          up{job="otel-collector"} == 0
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "Collector实例宕机"
          description: "实例 {{ $labels.instance }} 已宕机"

      # 批次过大
      - alert: CollectorLargeBatches
        expr: |
          histogram_quantile(0.99,
            sum(rate(otelcol_processor_batch_send_size_bucket[5m])) by (le)
          ) > 10000
        for: 10m
        labels:
          severity: info
        annotations:
          summary: "Collector批次过大"
          description: "P99批次大小超过10000，建议调整batch配置"
```

### 2.3 Grafana Dashboard

```json
{
  "dashboard": {
    "title": "Collector运维监控",
    "panels": [
      {
        "title": "数据吞吐量",
        "type": "stat",
        "targets": [
          {
            "expr": "sum(rate(otelcol_receiver_accepted_spans_total[5m]))",
            "legendFormat": "Spans/秒"
          },
          {
            "expr": "sum(rate(otelcol_receiver_accepted_metric_points_total[5m]))",
            "legendFormat": "Metrics/秒"
          }
        ]
      },
      {
        "title": "队列状态",
        "type": "gauge",
        "targets": [
          {
            "expr": "otelcol_exporter_queue_size / otelcol_exporter_queue_capacity",
            "legendFormat": "队列使用率"
          }
        ],
        "fieldConfig": {
          "thresholds": {
            "steps": [
              {"color": "green", "value": 0},
              {"color": "yellow", "value": 0.6},
              {"color": "red", "value": 0.8}
            ]
          }
        }
      },
      {
        "title": "错误率",
        "type": "timeseries",
        "targets": [
          {
            "expr": "sum(rate(otelcol_exporter_send_failed_spans_total[5m]))",
            "legendFormat": "发送失败/秒"
          },
          {
            "expr": "sum(rate(otelcol_receiver_refused_spans_total[5m]))",
            "legendFormat": "拒绝接收/秒"
          }
        ]
      },
      {
        "title": "资源使用",
        "type": "timeseries",
        "targets": [
          {
            "expr": "otelcol_process_memory_rss / 1024 / 1024",
            "legendFormat": "内存 (MiB)"
          },
          {
            "expr": "rate(otelcol_process_cpu_seconds_total[5m]) * 100",
            "legendFormat": "CPU (%)"
          }
        ]
      }
    ]
  }
}
```

---

## 3. 日志管理

### 3.1 Collector日志配置

```yaml
# 配置日志级别
service:
  telemetry:
    logs:
      level: info          # debug, info, warn, error
      development: false
      encoding: json       # json, console
      output_paths:
        - stdout
        - /var/log/otel/collector.log
      error_output_paths:
        - stderr
        - /var/log/otel/collector.error.log
      sampling:
        initial: 2
        thereafter: 500

      # 日志轮转 (使用file exporter)
      rotate:
        max_size_mb: 100
        max_age_days: 7
        max_backups: 3
        compress: true
```

### 3.2 日志收集与聚合

```yaml
# Fluent Bit配置收集Collector日志
[INPUT]
    Name tail
    Path /var/log/otel/collector.log
    Tag otel.collector
    Parser json

[FILTER]
    Name kubernetes
    Match otel.collector
    Merge_Log On
    Keep_Log Off

[OUTPUT]
    Name es
    Match otel.collector
    Host elasticsearch
    Port 9200
    Index otel-logs
    Type collector
```

### 3.3 关键日志模式

| 日志级别 | 模式 | 说明 | 处理建议 |
|----------|------|------|----------|
| ERROR | `Exporting failed` | 导出失败 | 检查后端连接 |
| ERROR | `Memory limit exceeded` | 内存超限 | 扩容或调优 |
| WARN | `Batch size too large` | 批次过大 | 调整batch配置 |
| WARN | `Queue is full` | 队列满 | 增加队列大小或消费者 |
| INFO | `Config updated` | 配置更新 | 正常操作 |

---

## 4. 证书管理

### 4.1 证书自动续期

```bash
#!/bin/bash
# cert-renewal.sh

CERT_DIR="/etc/otel/certs"
RENEWAL_DAYS=30

# 检查证书过期时间
for cert in $CERT_DIR/*.crt; do
    expiry_date=$(openssl x509 -enddate -noout -in "$cert" | cut -d= -f2)
    expiry_epoch=$(date -d "$expiry_date" +%s)
    current_epoch=$(date +%s)
    days_until_expiry=$(( (expiry_epoch - current_epoch) / 86400 ))

    if [ $days_until_expiry -lt $RENEWAL_DAYS ]; then
        echo "Certificate $cert expires in $days_until_expiry days. Renewing..."

        # 使用cert-manager或手动续期
        kubectl certificate approve $cert

        # 重启Collector加载新证书
        kubectl rollout restart deployment/otel-collector -n monitoring
    fi
done
```

### 4.2 Kubernetes证书管理

```yaml
apiVersion: cert-manager.io/v1
kind: Certificate
metadata:
  name: otel-collector-tls
  namespace: monitoring
spec:
  secretName: otel-collector-tls
  issuerRef:
    name: internal-ca
    kind: ClusterIssuer
  dnsNames:
    - otel-collector.monitoring.svc
    - otel-collector.monitoring.svc.cluster.local
    - "*.otel-collector.monitoring.svc.cluster.local"
  usages:
    - server auth
    - client auth
  privateKey:
    algorithm: RSA
    encoding: PKCS1
    size: 4096
  duration: 2160h      # 90天
  renewBefore: 360h    # 15天前续期
```

### 4.3 证书监控

```yaml
# 证书过期告警
- alert: CollectorCertificateExpiring
  expr: |
    (
      ssl_certificate_expiry_seconds{job="otel-collector"}
      - time()
    ) / 86400 < 14
  for: 1h
  labels:
    severity: warning
  annotations:
    summary: "Collector证书即将过期"
    description: "证书将在14天内过期"
```

---

## 5. 备份与恢复

### 5.1 配置备份

```bash
#!/bin/bash
# backup-collector.sh

BACKUP_DIR="/backup/otel/$(date +%Y%m%d)"
mkdir -p $BACKUP_DIR

# 备份配置文件
kubectl get configmap otel-collector-config -n monitoring -o yaml > $BACKUP_DIR/configmap.yaml

# 备份Secrets
kubectl get secret otel-collector-tls -n monitoring -o yaml > $BACKUP_DIR/tls-secret.yaml

# 备份部署配置
kubectl get deployment otel-collector -n monitoring -o yaml > $BACKUP_DIR/deployment.yaml

# 加密敏感数据
tar -czf - $BACKUP_DIR | gpg --symmetric --cipher-algo AES256 > $BACKUP_DIR.tar.gz.gpg

# 清理旧备份 (保留30天)
find /backup/otel -type d -mtime +30 -exec rm -rf {} \;
```

### 5.2 数据持久化

```yaml
# 使用file_storage扩展持久化队列数据
extensions:
  file_storage:
    directory: /var/lib/otel/storage
    timeout: 1s
    compaction:
      on_rebound: true
      rebound_needed_threshold_mib: 100
      rebound_trigger_threshold_mib: 10
      check_interval: 5s

exporters:
  otlp:
    endpoint: backend:4317
    sending_queue:
      enabled: true
      storage: file_storage    # 使用文件存储持久化队列
```

### 5.3 灾难恢复

```bash
#!/bin/bash
# restore-collector.sh

BACKUP_FILE=$1
RESTORE_DIR="/tmp/otel-restore"

# 解密备份
gpg --decrypt $BACKUP_FILE | tar -xzf - -C $RESTORE_DIR

# 恢复配置
kubectl apply -f $RESTORE_DIR/configmap.yaml
kubectl apply -f $RESTORE_DIR/tls-secret.yaml

# 重启Collector
kubectl rollout restart deployment/otel-collector -n monitoring

# 验证恢复
kubectl rollout status deployment/otel-collector -n monitoring
```

---

## 6. 容量管理

### 6.1 容量规划公式

```
Collector资源估算:

内存需求 = 基础内存 + 队列内存 + 处理缓冲区
         = 500MB + (队列大小 × 平均Span大小) + 处理缓冲区

         示例:
         = 500MB + (10000 × 2KB) + 500MB
         = 500MB + 20MB + 500MB
         = ~1GB

CPU需求 = 基础CPU + 处理CPU + 导出CPU
        = 0.1核 + (每秒Span数 × 处理成本) + (每秒Span数 × 导出成本)

        示例 (10K spans/sec):
        = 0.1 + (10000 × 0.00001) + (10000 × 0.00002)
        = 0.1 + 0.1 + 0.2
        = 0.4核

网络带宽 = 每秒数据量 × 复制因子
         = (每秒Span数 × 平均Span大小) × 复制因子

         示例:
         = (10000 × 2KB) × 2
         = 20MB/s × 2
         = 40MB/s
```

### 6.2 水平扩展策略

```yaml
# HPA配置
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: monitoring
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
  minReplicas: 3
  maxReplicas: 20
  metrics:
    - type: Pods
      pods:
        metric:
          name: otelcol_exporter_queue_size
        target:
          type: AverageValue
          averageValue: "5000"
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
        - type: Percent
          value: 100
          periodSeconds: 15
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
        - type: Percent
          value: 10
          periodSeconds: 60
```

### 6.3 容量监控仪表板

```yaml
# 容量监控指标
- record: collector:capacity:utilization
  expr: |
    (
      otelcol_process_memory_rss
      /
      otelcol_process_memory_limit
    ) * 100

- record: collector:throughput:spans_per_second
  expr: |
    sum(rate(otelcol_receiver_accepted_spans_total[5m]))

- record: collector:queue:utilization
  expr: |
    otelcol_exporter_queue_size
    /
    otelcol_exporter_queue_capacity
```

---

## 7. 故障排查

### 7.1 常见问题诊断

| 症状 | 可能原因 | 诊断命令 | 解决方案 |
|------|----------|----------|----------|
| 数据丢失 | 队列满、后端不可用 | `curl localhost:8888/metrics \| grep refused` | 增加队列、检查后端的 |
| 内存泄漏 | 配置错误、bug | `kubectl top pod` | 重启、调整limit |
| CPU过高 | 处理复杂、采样不足 | `curl localhost:1777/debug/pprof` | 优化processor、增加采样 |
| 发送失败 | 网络、认证问题 | `curl localhost:13133/health` | 检查网络、证书 |
| 启动失败 | 配置错误 | `kubectl logs` | 检查配置文件语法 |

### 7.2 调试工具

```bash
# 1. 健康检查
curl http://localhost:13133/health

# 2. 指标查看
curl http://localhost:8888/metrics

# 3. pprof性能分析
go tool pprof http://localhost:1777/debug/pprof/profile
go tool pprof http://localhost:1777/debug/pprof/heap

# 4. zpages调试
curl http://localhost:55679/debug/tracez
curl http://localhost:55679/debug/rpcz

# 5. 日志查看
kubectl logs -f deployment/otel-collector -n monitoring

# 6. 配置验证
otelcol validate --config config.yaml
```

### 7.3 故障恢复流程

```
┌─────────────────────────────────────────────────────────────────┐
│                    故障恢复流程                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 发现问题                                                    │
│     └── 告警触发 / 用户反馈 / 监控异常                         │
│              │                                                  │
│              ▼                                                  │
│  2. 诊断分析                                                    │
│     └── 查看日志 → 检查指标 → 分析配置                         │
│              │                                                  │
│              ▼                                                  │
│  3. 快速恢复                                                    │
│     ├── 重启Collector (临时恢复)                               │
│     ├── 切换到备份Collector (高可用)                           │
│     └── 调整采样率 (降低负载)                                  │
│              │                                                  │
│              ▼                                                  │
│  4. 根因修复                                                    │
│     └── 修复配置 / 扩容资源 / 升级版本                         │
│              │                                                  │
│              ▼                                                  │
│  5. 验证恢复                                                    │
│     └── 检查指标正常 / 确认数据完整                            │
│              │                                                  │
│              ▼                                                  │
│  6. 事后分析                                                    │
│     └── 更新文档 / 改进监控 / 优化流程                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 8. 日常运维检查清单

### 8.1 每日检查

- [ ] 检查告警事件
- [ ] 查看数据吞吐量趋势
- [ ] 确认资源使用率正常
- [ ] 检查错误日志

### 8.2 每周检查

- [ ] 审查采样率效果
- [ ] 检查队列积压情况
- [ ] 验证证书有效期
- [ ] 备份配置检查

### 8.3 每月检查

- [ ] 容量规划审查
- [ ] 性能基准测试
- [ ] 安全补丁更新
- [ ] 文档更新

---

**最后更新**: 2026-03-17
**维护者**: OTLP部署运维团队
**状态**: Production Ready
