---
title: OTLP业务集成实战：OTLP与业务系统融合案例
description: OTLP业务集成实战：OTLP与业务系统融合案例 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 核心实现
tags:
  - otlp
  - observability
  - performance
  - optimization
  - case-study
  - production
  - sampling
status: published
---
# OTLP业务集成实战：OTLP与业务系统融合案例

> **OTLP版本**: v1.0.0 (Stable)
> **最后更新**: 2025年10月11日
> **集成目标**: 电商、金融、物流、制造四大行业完整集成方案
> **文档状态**: ✅ 完成

---

## 目录

- [OTLP业务集成实战：OTLP与业务系统融合案例](#otlp业务集成实战otlp与业务系统融合案例)
  - [目录](#目录)
  - [执行摘要](#执行摘要)
  - [业务集成框架](#业务集成框架)
    - [集成层次](#集成层次)
    - [集成模式](#集成模式)
  - [� 电商系统集成](#-电商系统集成)
    - [1. 订单处理追踪](#1-订单处理追踪)
    - [2. 电商业务指标](#2-电商业务指标)
  - [� 金融系统集成](#-金融系统集成)
    - [1. 交易处理追踪](#1-交易处理追踪)
  - [� 物流系统集成](#-物流系统集成)
    - [1. 订单配送追踪](#1-订单配送追踪)
  - [� 最佳实践](#-最佳实践)
    - [1. 业务集成最佳实践](#1-业务集成最佳实践)
    - [2. 性能优化建议](#2-性能优化建议)
  - [参考资源](#参考资源)

---

## 执行摘要

**OTLP业务集成实战**提供了四大行业的完整集成方案，展示如何将OTLP与业务系统深度融合：

```text
集成目标:
┌─────────────────────────────────────────────────┐
│          业务集成四大目标                         │
├─────────────────────────────────────────────────┤
│                                                 │
│  📊 业务追踪: 端到端业务追踪                      │
│  🔍 问题定位: 快速定位业务问题                    │
│  📈 性能优化: 识别性能瓶颈                        │
│  💰 成本控制: 优化可观测性成本                    │
│                                                 │
└─────────────────────────────────────────────────┘
```

**集成行业**：

1. **电商系统**：订单处理、支付、库存管理
2. **金融系统**：交易处理、风控、合规检查
3. **物流系统**：订单配送、仓储管理、运输追踪
4. **制造系统**：生产计划、质量控制、设备监控

---

## 业务集成框架

### 集成层次

```text
OTLP业务集成层次:
┌─────────────────────────────────────────────────┐
│             业务层集成                           │
│  - 业务事件追踪 (Business Event Tracing)         │
│  - 业务流程监控 (Business Process Monitoring)    │
│  - 业务指标统计 (Business Metrics)               │
├─────────────────────────────────────────────────┤
│             应用层集成                           │
│  - 业务属性注入 (Business Attributes)            │
│  - 业务语义约定 (Business Semantics)             │
│  - 业务模型映射 (Business Model Mapping)         │
├─────────────────────────────────────────────────┤
│             数据层集成                           │
│  - OTLP数据模型 (OTLP Data Model)                │
│  - 业务数据模型 (Business Data Model)            │
│  - 数据转换层 (Data Transformation Layer)        │
├─────────────────────────────────────────────────┤
│             存储层集成                           │
│  - OTLP存储 (OTLP Storage)                       │
│  - 业务数据存储 (Business Data Storage)          │
│  - 数据关联 (Data Correlation)                   │
└─────────────────────────────────────────────────┘
```

### 集成模式

```text
定义 (业务集成模式):
BusinessIntegrationPattern = {
  event_tracing: bool,      // 事件追踪
  process_monitoring: bool, // 流程监控
  metrics_collection: bool, // 指标收集
  log_correlation: bool     // 日志关联
}

集成模式:
✅ 事件追踪: 追踪关键业务事件
✅ 流程监控: 监控业务流程状态
✅ 指标收集: 收集业务指标
✅ 日志关联: 关联业务日志
```

---

## � 电商系统集成

### 1. 订单处理追踪

**订单处理流程**：

```text
订单处理流程:
┌─────────────────────────────────────────────────┐
│  用户下单 → 库存检查 → 支付处理 → 订单确认 → 发货│
├─────────────────────────────────────────────────┤
│                                                 │
│  1. 用户下单 (order-service)                    │
│     ├─ 创建订单                                 │
│     ├─ 验证商品                                 │
│     └─ 计算金额                                 │
│                                                 │
│  2. 库存检查 (inventory-service)                │
│     ├─ 检查库存                                 │
│     ├─ 锁定库存                                 │
│     └─ 更新库存                                 │
│                                                 │
│  3. 支付处理 (payment-service)                  │
│     ├─ 创建支付订单                             │
│     ├─ 调用支付网关                             │
│     └─ 确认支付                                 │
│                                                 │
│  4. 订单确认 (order-service)                    │
│     ├─ 更新订单状态                             │
│     ├─ 发送通知                                 │
│     └─ 触发发货                                 │
│                                                 │
│  5. 发货处理 (shipping-service)                 │
│     ├─ 生成运单                                 │
│     ├─ 安排配送                                 │
│     └─ 更新物流状态                             │
│                                                 │
└─────────────────────────────────────────────────┘
```

**订单处理追踪实现**：

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 订单服务
type OrderService struct {
    tracer trace.Tracer
}

func NewOrderService() *OrderService {
    return &OrderService{
        tracer: otel.Tracer("order-service"),
    }
}

// 创建订单
func (s *OrderService) CreateOrder(ctx context.Context, req *CreateOrderRequest) (*Order, error) {
    ctx, span := s.tracer.Start(ctx, "order.create",
        trace.WithAttributes(
            attribute.String("business.order.user_id", req.UserID),
            attribute.Int("business.order.item_count", len(req.Items)),
            attribute.Float64("business.order.total_amount", req.TotalAmount),
            attribute.String("business.order.currency", "CNY"),
        ),
    )
    defer span.End()

    // 1. 验证订单
    if err := s.validateOrder(ctx, req); err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("business.order.status", "validation_failed"),
        )
        return nil, err
    }

    // 2. 检查库存
    inventoryService := NewInventoryService()
    if err := inventoryService.CheckStock(ctx, req.Items); err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("business.order.status", "stock_unavailable"),
        )
        return nil, err
    }

    // 3. 创建订单
    order := &Order{
        ID:          generateOrderID(),
        UserID:      req.UserID,
        Items:       req.Items,
        TotalAmount: req.TotalAmount,
        Status:      OrderStatusPending,
        CreatedAt:   time.Now(),
    }

    span.SetAttributes(
        attribute.String("business.order.id", order.ID),
        attribute.String("business.order.status", string(order.Status)),
    )

    // 4. 处理支付
    paymentService := NewPaymentService()
    if err := paymentService.ProcessPayment(ctx, order); err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("business.order.status", "payment_failed"),
        )
        return nil, err
    }

    // 5. 确认订单
    order.Status = OrderStatusConfirmed
    span.SetAttributes(
        attribute.String("business.order.status", string(order.Status)),
    )

    return order, nil
}

// 库存服务
type InventoryService struct {
    tracer trace.Tracer
}

func NewInventoryService() *InventoryService {
    return &InventoryService{
        tracer: otel.Tracer("inventory-service"),
    }
}

// 检查库存
func (s *InventoryService) CheckStock(ctx context.Context, items []OrderItem) error {
    ctx, span := s.tracer.Start(ctx, "inventory.check_stock")
    defer span.End()

    for _, item := range items {
        itemSpan := s.tracer.Start(ctx, "inventory.check_item",
            trace.WithAttributes(
                attribute.String("business.product.id", item.ProductID),
                attribute.Int("business.product.quantity", item.Quantity),
            ),
        )

        // 检查库存
        stock, err := s.getStock(ctx, item.ProductID)
        if err != nil {
            itemSpan.RecordError(err)
            itemSpan.End()
            return err
        }

        if stock < item.Quantity {
            itemSpan.SetAttributes(
                attribute.String("business.product.stock_status", "insufficient"),
            )
            itemSpan.End()
            return fmt.Errorf("insufficient stock for product %s", item.ProductID)
        }

        itemSpan.SetAttributes(
            attribute.Int("business.product.stock", stock),
            attribute.String("business.product.stock_status", "sufficient"),
        )
        itemSpan.End()
    }

    return nil
}

// 支付服务
type PaymentService struct {
    tracer trace.Tracer
}

func NewPaymentService() *PaymentService {
    return &PaymentService{
        tracer: otel.Tracer("payment-service"),
    }
}

// 处理支付
func (s *PaymentService) ProcessPayment(ctx context.Context, order *Order) error {
    ctx, span := s.tracer.Start(ctx, "payment.process",
        trace.WithAttributes(
            attribute.String("business.order.id", order.ID),
            attribute.Float64("business.payment.amount", order.TotalAmount),
            attribute.String("business.payment.method", "credit_card"),
        ),
    )
    defer span.End()

    // 1. 创建支付订单
    paymentOrder := &PaymentOrder{
        OrderID: order.ID,
        Amount:  order.TotalAmount,
        Method:  "credit_card",
    }

    // 2. 调用支付网关
    gatewaySpan := s.tracer.Start(ctx, "payment.gateway.call")

    transactionID, err := s.callPaymentGateway(ctx, paymentOrder)
    if err != nil {
        gatewaySpan.RecordError(err)
        gatewaySpan.End()

        span.SetAttributes(
            attribute.String("business.payment.status", "failed"),
        )
        return err
    }

    gatewaySpan.SetAttributes(
        attribute.String("business.payment.transaction_id", transactionID),
    )
    gatewaySpan.End()

    // 3. 确认支付
    span.SetAttributes(
        attribute.String("business.payment.transaction_id", transactionID),
        attribute.String("business.payment.status", "success"),
    )

    return nil
}
```

### 2. 电商业务指标

**业务指标收集**：

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel/metric"
)

// 电商业务指标
type ECommerceMetrics struct {
    orderCounter        metric.Int64Counter
    orderAmount         metric.Float64Histogram
    orderDuration       metric.Float64Histogram
    paymentCounter      metric.Int64Counter
    paymentAmount       metric.Float64Histogram
    inventoryStock      metric.Int64Gauge
}

func NewECommerceMetrics(meter metric.Meter) (*ECommerceMetrics, error) {
    orderCounter, err := meter.Int64Counter(
        "business.order.count",
        metric.WithDescription("Total number of orders"),
        metric.WithUnit("1"),
    )
    if err != nil {
        return nil, err
    }

    orderAmount, err := meter.Float64Histogram(
        "business.order.amount",
        metric.WithDescription("Order amount distribution"),
        metric.WithUnit("CNY"),
    )
    if err != nil {
        return nil, err
    }

    orderDuration, err := meter.Float64Histogram(
        "business.order.duration",
        metric.WithDescription("Order processing duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }

    paymentCounter, err := meter.Int64Counter(
        "business.payment.count",
        metric.WithDescription("Total number of payments"),
        metric.WithUnit("1"),
    )
    if err != nil {
        return nil, err
    }

    paymentAmount, err := meter.Float64Histogram(
        "business.payment.amount",
        metric.WithDescription("Payment amount distribution"),
        metric.WithUnit("CNY"),
    )
    if err != nil {
        return nil, err
    }

    inventoryStock, err := meter.Int64Gauge(
        "business.inventory.stock",
        metric.WithDescription("Product stock level"),
        metric.WithUnit("1"),
    )
    if err != nil {
        return nil, err
    }

    return &ECommerceMetrics{
        orderCounter:   orderCounter,
        orderAmount:    orderAmount,
        orderDuration:  orderDuration,
        paymentCounter: paymentCounter,
        paymentAmount:  paymentAmount,
        inventoryStock: inventoryStock,
    }, nil
}

// 记录订单指标
func (m *ECommerceMetrics) RecordOrder(ctx context.Context, order *Order, duration time.Duration) {
    attrs := []attribute.KeyValue{
        attribute.String("business.order.status", string(order.Status)),
        attribute.String("business.order.currency", order.Currency),
    }

    m.orderCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
    m.orderAmount.Record(ctx, order.TotalAmount, metric.WithAttributes(attrs...))
    m.orderDuration.Record(ctx, float64(duration.Milliseconds()), metric.WithAttributes(attrs...))
}

// 记录支付指标
func (m *ECommerceMetrics) RecordPayment(ctx context.Context, payment *Payment) {
    attrs := []attribute.KeyValue{
        attribute.String("business.payment.method", payment.Method),
        attribute.String("business.payment.status", string(payment.Status)),
    }

    m.paymentCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
    m.paymentAmount.Record(ctx, payment.Amount, metric.WithAttributes(attrs...))
}

// 更新库存指标
func (m *ECommerceMetrics) UpdateStock(ctx context.Context, productID string, stock int64) {
    attrs := []attribute.KeyValue{
        attribute.String("business.product.id", productID),
    }

    m.inventoryStock.Record(ctx, stock, metric.WithAttributes(attrs...))
}
```

---

## � 金融系统集成

### 1. 交易处理追踪

**交易处理流程**：

```text
交易处理流程:
┌─────────────────────────────────────────────────┐
│  交易请求 → 风控检查 → 合规检查 → 执行交易 → 确认│
├─────────────────────────────────────────────────┤
│                                                 │
│  1. 交易请求 (transaction-service)              │
│     ├─ 验证交易参数                             │
│     ├─ 检查账户状态                             │
│     └─ 计算交易金额                             │
│                                                 │
│  2. 风控检查 (risk-service)                     │
│     ├─ 计算风险分数                             │
│     ├─ 检查风险规则                             │
│     └─ 生成风控报告                             │
│                                                 │
│  3. 合规检查 (compliance-service)               │
│     ├─ 反洗钱检查                               │
│     ├─ 制裁名单检查                             │
│     └─ 大额交易报告                             │
│                                                 │
│  4. 执行交易 (transaction-service)               │
│     ├─ 扣减转出账户                             │
│     ├─ 增加转入账户                             │
│     └─ 记录交易日志                             │
│                                                 │
│  5. 交易确认 (transaction-service)               │
│     ├─ 发送通知                                 │
│     ├─ 更新账户余额                             │
│     └─ 生成交易凭证                             │
│                                                 │
└─────────────────────────────────────────────────┘
```

**交易处理追踪实现**：

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 交易服务
type TransactionService struct {
    tracer trace.Tracer
}

func NewTransactionService() *TransactionService {
    return &TransactionService{
        tracer: otel.Tracer("transaction-service"),
    }
}

// 处理交易
func (s *TransactionService) ProcessTransaction(ctx context.Context, req *TransactionRequest) (*Transaction, error) {
    ctx, span := s.tracer.Start(ctx, "transaction.process",
        trace.WithAttributes(
            attribute.String("finance.transaction.type", string(req.Type)),
            attribute.String("finance.account.from", req.FromAccount),
            attribute.String("finance.account.to", req.ToAccount),
            attribute.Float64("finance.transaction.amount", req.Amount),
            attribute.String("finance.transaction.currency", req.Currency),
        ),
    )
    defer span.End()

    // 1. 风控检查
    riskService := NewRiskService()
    riskScore, err := riskService.CheckRisk(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("finance.transaction.status", "risk_check_failed"),
        )
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("finance.risk.score", riskScore),
    )

    if riskScore > 80 {
        span.SetAttributes(
            attribute.String("finance.risk.level", "high"),
            attribute.String("finance.transaction.status", "blocked"),
        )
        return nil, fmt.Errorf("high risk transaction")
    }

    // 2. 合规检查
    complianceService := NewComplianceService()
    complianceStatus, err := complianceService.CheckCompliance(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("finance.transaction.status", "compliance_check_failed"),
        )
        return nil, err
    }

    span.SetAttributes(
        attribute.String("finance.compliance.status", complianceStatus),
    )

    // 3. 执行交易
    transaction := &Transaction{
        ID:          generateTransactionID(),
        Type:        req.Type,
        FromAccount: req.FromAccount,
        ToAccount:   req.ToAccount,
        Amount:      req.Amount,
        Currency:    req.Currency,
        Status:      TransactionStatusPending,
        CreatedAt:   time.Now(),
    }

    span.SetAttributes(
        attribute.String("finance.transaction.id", transaction.ID),
    )

    // 4. 更新账户
    accountService := NewAccountService()
    if err := accountService.UpdateAccounts(ctx, transaction); err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("finance.transaction.status", "execution_failed"),
        )
        return nil, err
    }

    // 5. 确认交易
    transaction.Status = TransactionStatusCompleted
    span.SetAttributes(
        attribute.String("finance.transaction.status", string(transaction.Status)),
    )

    return transaction, nil
}

// 风控服务
type RiskService struct {
    tracer trace.Tracer
}

func NewRiskService() *RiskService {
    return &RiskService{
        tracer: otel.Tracer("risk-service"),
    }
}

// 检查风险
func (s *RiskService) CheckRisk(ctx context.Context, req *TransactionRequest) (int, error) {
    ctx, span := s.tracer.Start(ctx, "risk.check",
        trace.WithAttributes(
            attribute.String("finance.transaction.type", string(req.Type)),
            attribute.Float64("finance.transaction.amount", req.Amount),
        ),
    )
    defer span.End()

    // 计算风险分数
    riskScore := s.calculateRiskScore(ctx, req)

    span.SetAttributes(
        attribute.Int("finance.risk.score", riskScore),
    )

    if riskScore > 80 {
        span.SetAttributes(
            attribute.String("finance.risk.level", "high"),
        )
    } else if riskScore > 50 {
        span.SetAttributes(
            attribute.String("finance.risk.level", "medium"),
        )
    } else {
        span.SetAttributes(
            attribute.String("finance.risk.level", "low"),
        )
    }

    return riskScore, nil
}

// 合规服务
type ComplianceService struct {
    tracer trace.Tracer
}

func NewComplianceService() *ComplianceService {
    return &ComplianceService{
        tracer: otel.Tracer("compliance-service"),
    }
}

// 检查合规
func (s *ComplianceService) CheckCompliance(ctx context.Context, req *TransactionRequest) (string, error) {
    ctx, span := s.tracer.Start(ctx, "compliance.check",
        trace.WithAttributes(
            attribute.String("finance.transaction.type", string(req.Type)),
            attribute.Float64("finance.transaction.amount", req.Amount),
        ),
    )
    defer span.End()

    // 1. 反洗钱检查
    amlSpan := s.tracer.Start(ctx, "compliance.aml_check")
    if err := s.checkAML(ctx, req); err != nil {
        amlSpan.RecordError(err)
        amlSpan.End()

        span.SetAttributes(
            attribute.String("finance.compliance.status", "aml_failed"),
        )
        return "failed", err
    }
    amlSpan.End()

    // 2. 制裁名单检查
    sanctionsSpan := s.tracer.Start(ctx, "compliance.sanctions_check")
    if err := s.checkSanctions(ctx, req); err != nil {
        sanctionsSpan.RecordError(err)
        sanctionsSpan.End()

        span.SetAttributes(
            attribute.String("finance.compliance.status", "sanctions_failed"),
        )
        return "failed", err
    }
    sanctionsSpan.End()

    // 3. 大额交易报告
    if req.Amount > 50000 {
        reportSpan := s.tracer.Start(ctx, "compliance.large_transaction_report")
        s.reportLargeTransaction(ctx, req)
        reportSpan.End()
    }

    span.SetAttributes(
        attribute.String("finance.compliance.status", "passed"),
    )

    return "passed", nil
}
```

---

## � 物流系统集成

### 1. 订单配送追踪

**订单配送流程**：

```text
订单配送流程:
┌─────────────────────────────────────────────────┐
│  订单接收 → 仓库拣货 → 打包 → 发货 → 配送 → 签收│
├─────────────────────────────────────────────────┤
│                                                 │
│  1. 订单接收 (order-service)                    │
│     ├─ 接收订单                                 │
│     ├─ 分配仓库                                 │
│     └─ 生成拣货单                               │
│                                                 │
│  2. 仓库拣货 (warehouse-service)                │
│     ├─ 拣货任务分配                             │
│     ├─ 商品拣货                                 │
│     └─ 拣货完成确认                             │
│                                                 │
│  3. 打包 (packaging-service)                    │
│     ├─ 商品打包                                 │
│     ├─ 生成运单                                 │
│     └─ 打印标签                                 │
│                                                 │
│  4. 发货 (shipping-service)                     │
│     ├─ 安排物流                                 │
│     ├─ 生成运单                                 │
│     └─ 更新物流状态                             │
│                                                 │
│  5. 配送 (delivery-service)                     │
│     ├─ 配送员分配                               │
│     ├─ 配送路线规划                             │
│     └─ 实时位置追踪                             │
│                                                 │
│  6. 签收 (delivery-service)                     │
│     ├─ 确认收货                                 │
│     ├─ 更新订单状态                             │
│     └─ 发送通知                                 │
│                                                 │
└─────────────────────────────────────────────────┘
```

**订单配送追踪实现**：

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 配送服务
type DeliveryService struct {
    tracer trace.Tracer
}

func NewDeliveryService() *DeliveryService {
    return &DeliveryService{
        tracer: otel.Tracer("delivery-service"),
    }
}

// 处理订单配送
func (s *DeliveryService) ProcessDelivery(ctx context.Context, order *Order) error {
    ctx, span := s.tracer.Start(ctx, "delivery.process",
        trace.WithAttributes(
            attribute.String("business.order.id", order.ID),
            attribute.String("business.order.status", string(order.Status)),
            attribute.String("logistics.delivery.type", "standard"),
        ),
    )
    defer span.End()

    // 1. 分配仓库
    warehouseService := NewWarehouseService()
    warehouse, err := warehouseService.AssignWarehouse(ctx, order)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("logistics.delivery.status", "warehouse_assignment_failed"),
        )
        return err
    }

    span.SetAttributes(
        attribute.String("logistics.warehouse.id", warehouse.ID),
        attribute.String("logistics.warehouse.location", warehouse.Location),
    )

    // 2. 拣货
    pickingTask, err := warehouseService.CreatePickingTask(ctx, order, warehouse)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("logistics.delivery.status", "picking_failed"),
        )
        return err
    }

    span.SetAttributes(
        attribute.String("logistics.picking.task_id", pickingTask.ID),
    )

    // 3. 打包
    packagingService := NewPackagingService()
    packageInfo, err := packagingService.PackageOrder(ctx, order, pickingTask)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("logistics.delivery.status", "packaging_failed"),
        )
        return err
    }

    span.SetAttributes(
        attribute.String("logistics.package.id", packageInfo.ID),
        attribute.Float64("logistics.package.weight", packageInfo.Weight),
        attribute.Float64("logistics.package.volume", packageInfo.Volume),
    )

    // 4. 发货
    shippingService := NewShippingService()
    waybill, err := shippingService.CreateWaybill(ctx, order, packageInfo)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("logistics.delivery.status", "shipping_failed"),
        )
        return err
    }

    span.SetAttributes(
        attribute.String("logistics.waybill.id", waybill.ID),
        attribute.String("logistics.carrier.name", waybill.CarrierName),
    )

    // 5. 配送
    deliveryTask, err := shippingService.AssignDelivery(ctx, waybill)
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(
            attribute.String("logistics.delivery.status", "delivery_assignment_failed"),
        )
        return err
    }

    span.SetAttributes(
        attribute.String("logistics.delivery.task_id", deliveryTask.ID),
        attribute.String("logistics.delivery.driver_id", deliveryTask.DriverID),
    )

    // 6. 追踪配送
    go s.trackDelivery(ctx, deliveryTask)

    span.SetAttributes(
        attribute.String("logistics.delivery.status", "in_transit"),
    )

    return nil
}

// 追踪配送
func (s *DeliveryService) trackDelivery(ctx context.Context, task *DeliveryTask) {
    tracer := otel.Tracer("delivery-tracker")

    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()

    for {
        select {
        case <-ctx.Done():
            return

        case <-ticker.C:
            ctx, span := tracer.Start(ctx, "delivery.track",
                trace.WithAttributes(
                    attribute.String("logistics.delivery.task_id", task.ID),
                ),
            )

            // 获取当前位置
            location, err := s.getCurrentLocation(ctx, task)
            if err != nil {
                span.RecordError(err)
                span.End()
                continue
            }

            span.SetAttributes(
                attribute.Float64("logistics.location.latitude", location.Latitude),
                attribute.Float64("logistics.location.longitude", location.Longitude),
            )

            // 检查是否到达
            if s.isArrived(ctx, task, location) {
                span.SetAttributes(
                    attribute.String("logistics.delivery.status", "arrived"),
                )
                span.End()
                return
            }

            span.End()
        }
    }
}
```

---

## � 最佳实践

### 1. 业务集成最佳实践

```text
业务集成最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 推荐做法                                      │
├─────────────────────────────────────────────────┤
│                                                 │
│  1. 定义清晰的业务语义约定                                    │
│     business.order.*                           │
│     finance.transaction.*                      │
│                                                 │
│  2. 追踪关键业务事件                           │
│     订单创建、支付、发货等                      │
│                                                 │
│  3. 收集业务指标                               │
│     订单量、交易额、库存等                      │
│                                                 │
│  4. 关联业务日志                               │
│     使用TraceID关联日志                        │
│                                                 │
│  5. 避免敏感信息                                │
│     ❌ business.user.password                   │
│     ✅ business.user.id                         │
│                                                 │
│  6. 优化追踪开销                               │
│     采样率 1-10%                               │
│                                                 │
└─────────────────────────────────────────────────┘
```

### 2. 性能优化建议

```text
性能优化建议:
┌─────────────────────────────────────────────────┐
│  优化项         │ 建议值          │ 说明           │
├─────────────────────────────────────────────────┤
│  追踪深度       │ ≤ 10层         │ 避免过深       │
│  属性数量       │ ≤ 20个/Span    │ 避免过多       │
│  采样率         │ 1-10%          │ 生产环境       │
│  批量大小       │ 100-1000条     │ 批量传输       │
│  追踪开销       │ < 5%           │ CPU开销        │
└─────────────────────────────────────────────────┘
```

---

## 参考资源

- [OpenTelemetry业务追踪](https://opentelemetry.io/docs/instrumentation/go/getting-started/)
- [业务语义约定](https://opentelemetry.io/docs/specs/semconv/general/attributes/)
- [OTLP业务集成](https://opentelemetry.io/docs/specs/otel/overview/)

---

**最后更新**: 2025年10月11日
**维护者**: OTLP深度梳理团队
**版本**: 1.0.0
