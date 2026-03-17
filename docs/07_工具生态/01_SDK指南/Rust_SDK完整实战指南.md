---
title: Rust SDK完整实战指南
description: OpenTelemetry Rust SDK的完整实战指南，包含Tokio集成、性能优化等
version: Rust 1.70+ / OTel Rust v0.21.0
date: 2026-03-17
author: OTLP项目团队
category: SDK指南
tags:
  - rust
  - tokio
  - sdk
  - otlp
  - opentelemetry
  - performance
status: published
---

# Rust SDK完整实战指南

> **版本**: Rust 1.70+ / OpenTelemetry Rust v0.21.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约40分钟

---

## 1. 环境准备

### 1.1 添加依赖

```toml
# Cargo.toml

[package]
name = "my-otel-service"
version = "1.0.0"
edition = "2021"
rust-version = "1.70"

[dependencies]
# 基础SDK
opentelemetry = "0.21"
opentelemetry_sdk = "0.21"
opentelemetry-semantic-conventions = "0.13"

# OTLP导出器
opentelemetry-otlp = { version = "0.14", features = ["grpc-tonic", "trace", "metrics"] }

# HTTP导出器（可选）
opentelemetry-http = "0.10"

# 日志集成
opentelemetry-appender-log = "0.2"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.22"

# HTTP客户端集成（reqwest）
opentelemetry-http-reqwest = { version = "0.11", optional = true }

# Actix Web集成
actix-web = "4"
actix-web-opentelemetry = { version = "0.16", features = ["metrics", "metrics-prometheus"] }

# Axum集成
axum = "0.7"
tower = "0.4"

# Tokio运行时
tokio = { version = "1", features = ["full"] }

# 其他常用库
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"
once_cell = "1.19"

[features]
default = ["otlp-grpc"]
otlp-grpc = ["opentelemetry-otlp/grpc-tonic"]
otlp-http = ["opentelemetry-otlp/http-proto"]

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

### 1.2 项目结构

```
myapp/
├── Cargo.toml
├── Cargo.lock
├── src/
│   ├── main.rs                 # 应用入口
│   ├── lib.rs                  # 库入口
│   ├── telemetry/
│   │   ├── mod.rs              # 模块入口
│   │   ├── init.rs             # 初始化逻辑
│   │   ├── tracing_config.rs   # 追踪配置
│   │   └── metrics_config.rs   # 指标配置
│   ├── handlers/
│   │   └── order_handler.rs
│   ├── services/
│   │   └── order_service.rs
│   └── middleware/
│       └── tracing.rs
├── tests/
│   └── integration_tests.rs
└── Dockerfile
```

---

## 2. 基础配置

### 2.1 初始化OpenTelemetry

```rust
// src/telemetry/mod.rs

pub mod init;
pub mod tracing_config;
pub mod metrics_config;

use opentelemetry::global;
use std::sync::OnceLock;

static TELEMETRY_INITIALIZED: OnceLock<bool> = OnceLock::new();

/// 检查遥测是否已初始化
pub fn is_initialized() -> bool {
    TELEMETRY_INITIALIZED.get().copied().unwrap_or(false)
}

/// 标记遥测已初始化
pub fn mark_initialized() {
    let _ = TELEMETRY_INITIALIZED.set(true);
}

/// 优雅关闭遥测
pub async fn shutdown() {
    global::shutdown_tracer_provider();
    global::shutdown_meter_provider();
    tracing::info!("OpenTelemetry shutdown completed");
}
```

```rust
// src/telemetry/init.rs

use std::time::Duration;
use opentelemetry::global;
use opentelemetry::trace::TracerProvider;
use opentelemetry::metrics::MeterProvider;
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, Resource};
use opentelemetry_sdk::trace::{Config, Tracer, RandomIdGenerator, Sampler};
use opentelemetry_sdk::metrics::MeterProvider as SdkMeterProvider;
use opentelemetry_sdk::trace::BatchConfig;
use opentelemetry_semantic_conventions::resource::{
    SERVICE_NAME, SERVICE_VERSION, DEPLOYMENT_ENVIRONMENT,
};

use crate::telemetry::{mark_initialized, tracing_config, metrics_config};

/// 遥测配置
#[derive(Debug, Clone)]
pub struct TelemetryConfig {
    pub service_name: String,
    pub service_version: String,
    pub environment: String,
    pub otlp_endpoint: String,
    pub otlp_timeout_secs: u64,
    pub trace_sampler_ratio: f64,
    pub metric_export_interval_secs: u64,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            service_name: std::env::var("OTEL_SERVICE_NAME")
                .unwrap_or_else(|_| "rust-service".to_string()),
            service_version: std::env::var("OTEL_SERVICE_VERSION")
                .unwrap_or_else(|_| "1.0.0".to_string()),
            environment: std::env::var("OTEL_ENVIRONMENT")
                .unwrap_or_else(|_| "development".to_string()),
            otlp_endpoint: std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            otlp_timeout_secs: std::env::var("OTEL_EXPORTER_OTLP_TIMEOUT")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(10),
            trace_sampler_ratio: std::env::var("OTEL_TRACES_SAMPLER_RATIO")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1.0),
            metric_export_interval_secs: std::env::var("OTEL_METRIC_EXPORT_INTERVAL")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(60),
        }
    }
}

/// 创建Resource
fn create_resource(config: &TelemetryConfig) -> Resource {
    Resource::new(vec![
        SERVICE_NAME.string(config.service_name.clone()),
        SERVICE_VERSION.string(config.service_version.clone()),
        DEPLOYMENT_ENVIRONMENT.string(config.environment.clone()),
        opentelemetry::KeyValue::new("host.name", gethostname::gethostname().to_string_lossy().to_string()),
        opentelemetry::KeyValue::new("process.runtime.name", "rustc"),
        opentelemetry::KeyValue::new("process.runtime.version", env!("CARGO_PKG_RUST_VERSION").to_string()),
    ])
}

/// 初始化链路追踪
pub fn init_tracing(config: &TelemetryConfig) -> anyhow::Result<Tracer> {
    let resource = create_resource(config);

    // 创建OTLP导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&config.otlp_endpoint)
        .with_timeout(Duration::from_secs(config.otlp_timeout_secs));

    // 配置采样器
    let sampler = if config.trace_sampler_ratio >= 1.0 {
        Sampler::AlwaysOn
    } else if config.trace_sampler_ratio <= 0.0 {
        Sampler::AlwaysOff
    } else {
        Sampler::TraceIdRatioBased(config.trace_sampler_ratio)
    };

    // 创建TracerProvider
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_trace_config(
            Config::default()
                .with_resource(resource.clone())
                .with_sampler(sampler)
                .with_id_generator(RandomIdGenerator::default()),
        )
        .with_batch_config(
            BatchConfig::default()
                .with_max_queue_size(2048)
                .with_max_export_batch_size(512)
                .with_scheduled_delay(Duration::from_secs(5))
                .with_max_export_timeout(Duration::from_secs(30)),
        )
        .install_batch(runtime::Tokio)?;

    global::set_tracer_provider(tracer_provider.clone());

    tracing::info!(
        service_name = %config.service_name,
        "Tracing initialized"
    );

    Ok(tracer_provider.tracer(config.service_name.clone()))
}

/// 初始化指标
pub fn init_metrics(config: &TelemetryConfig) -> anyhow::Result<SdkMeterProvider> {
    let resource = create_resource(config);

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&config.otlp_endpoint)
        .with_timeout(Duration::from_secs(config.otlp_timeout_secs));

    let meter_provider = opentelemetry_otlp::new_pipeline()
        .metrics(runtime::Tokio)
        .with_exporter(exporter)
        .with_resource(resource)
        .with_period(Duration::from_secs(config.metric_export_interval_secs))
        .build()?;

    global::set_meter_provider(meter_provider.clone());

    tracing::info!(
        service_name = %config.service_name,
        "Metrics initialized"
    );

    Ok(meter_provider)
}

/// 初始化所有遥测组件
pub async fn init_telemetry() -> anyhow::Result<()> {
    let config = TelemetryConfig::default();

    // 初始化Tracing
    let _tracer = init_tracing(&config)?;

    // 初始化Metrics
    let _meter_provider = init_metrics(&config)?;

    // 初始化日志
    init_logging(&config)?;

    mark_initialized();

    Ok(())
}

/// 初始化日志
fn init_logging(config: &TelemetryConfig) -> anyhow::Result<()> {
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(global::tracer(config.service_name.clone()));

    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer().json())
        .with(telemetry_layer)
        .init();

    Ok(())
}
```

### 2.2 Tracing配置

```rust
// src/telemetry/tracing_config.rs

use opentelemetry::trace::{SpanKind, Status, Tracer};
use opentelemetry::Context;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context as TaskContext, Poll};
use std::time::Instant;
use tracing::{instrument, Span as TracingSpan};

/// 便捷宏：创建instrumented函数
#[macro_export]
macro_rules! traced_fn {
    ($name:expr, $func:expr) => {{
        let tracer = opentelemetry::global::tracer("rust-service");
        let mut span = tracer.start($name);

        let ctx = opentelemetry::Context::current_with_span(span);
        let _guard = ctx.attach();

        let result = $func;

        opentelemetry::trace::TraceContextExt::span(&ctx).end();
        result
    }};
}

/// Span扩展trait
pub trait SpanExt {
    fn set_ok(&self);
    fn set_error(&self, message: impl Into<std::borrow::Cow<'static, str>>);
}

impl SpanExt for opentelemetry::trace::SpanRef<'_> {
    fn set_ok(&self) {
        self.set_status(Status::Ok);
    }

    fn set_error(&self, message: impl Into<std::borrow::Cow<'static, str>>) {
        self.set_status(Status::error(message));
    }
}

/// 计时Future
pub struct TimedFuture<F> {
    inner: F,
    start: Instant,
    span: TracingSpan,
}

impl<F: Future> Future for TimedFuture<F> {
    type Output = (F::Output, std::time::Duration);

    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };
        let inner = unsafe { Pin::new_unchecked(&mut this.inner) };

        match inner.poll(cx) {
            Poll::Ready(output) => {
                let duration = this.start.elapsed();
                tracing::debug!(duration_ms = %duration.as_millis(), "Future completed");
                Poll::Ready((output, duration))
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

/// 为Future添加计时
pub trait FutureTimer: Future + Sized {
    fn timed(self) -> TimedFuture<Self>;
}

impl<F: Future> FutureTimer for F {
    fn timed(self) -> TimedFuture<Self> {
        TimedFuture {
            inner: self,
            start: Instant::now(),
            span: tracing::Span::current(),
        }
    }
}
```

---

## 3. 核心使用示例

### 3.1 创建Span

```rust
// src/services/order_service.rs

use opentelemetry::trace::{SpanKind, Status, Tracer};
use opentelemetry::KeyValue;
use tracing::{info, instrument};
use anyhow::Result;
use uuid::Uuid;

use crate::telemetry::tracing_config::SpanExt;

#[derive(Debug, Clone)]
pub struct Order {
    pub order_id: String,
    pub user_id: String,
    pub amount: f64,
    pub status: String,
}

pub struct OrderService;

impl OrderService {
    pub fn new() -> Self {
        Self
    }

    /// 创建订单 - 使用opentelemetry API
    pub async fn create_order(&self, user_id: String, amount: f64) -> Result<Order> {
        let tracer = opentelemetry::global::tracer("order-service");

        // 创建Span
        let mut span = tracer.start("OrderService.create_order");
        span.set_attribute(KeyValue::new("order.user_id", user_id.clone()));
        span.set_attribute(KeyValue::new("order.amount", amount));

        // 创建Context并附加
        let ctx = opentelemetry::Context::current_with_span(span);
        let _guard = ctx.attach();

        let result = async {
            // 验证订单
            self.validate_order(&user_id, amount).await?;

            // 生成订单ID
            let order_id = format!("ORD-{}", Uuid::new_v4());

            // 获取当前Span并添加属性
            if let Some(span) = ctx.span() {
                span.set_attribute(KeyValue::new("order.id", order_id.clone()));
                span.add_event("Order validated".to_string(), vec![]);
            }

            // 处理支付
            self.process_payment(&order_id, amount).await?;

            // 设置成功状态
            if let Some(span) = ctx.span() {
                span.set_ok();
            }

            Ok(Order {
                order_id,
                user_id,
                amount,
                status: "created".to_string(),
            })
        }.await;

        // 结束Span
        if let Some(span) = ctx.span() {
            if let Err(ref e) = result {
                span.record_error(e);
                span.set_error(e.to_string());
            }
            span.end();
        }

        result
    }

    /// 验证订单 - 嵌套Span
    async fn validate_order(&self, user_id: &str, amount: f64) -> Result<()> {
        let tracer = opentelemetry::global::tracer("order-service");
        let mut span = tracer.start("OrderService.validate_order");
        span.set_attribute(KeyValue::new("validation.user_id", user_id.to_string()));

        let ctx = opentelemetry::Context::current_with_span(span);
        let _guard = ctx.attach();

        if amount <= 0.0 {
            if let Some(span) = ctx.span() {
                span.set_error("Invalid amount");
            }
            return Err(anyhow::anyhow!("Amount must be greater than 0"));
        }

        if let Some(span) = ctx.span() {
            span.set_attribute(KeyValue::new("validation.passed", true));
            span.set_ok();
            span.end();
        }

        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(())
    }

    /// 处理支付
    async fn process_payment(&self, order_id: &str, amount: f64) -> Result<()> {
        let tracer = opentelemetry::global::tracer("order-service");
        let mut span = tracer
            .span_builder("OrderService.process_payment")
            .with_kind(SpanKind::Internal)
            .start(&tracer);

        span.set_attribute(KeyValue::new("payment.order_id", order_id.to_string()));
        span.set_attribute(KeyValue::new("payment.amount", amount));
        span.set_attribute(KeyValue::new("payment.gateway", "stripe"));

        // 模拟支付处理
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

        span.add_event("Payment processed".to_string(), vec![
            KeyValue::new("payment.transaction_id", format!("txn_{}", order_id)),
        ]);
        span.set_ok();
        span.end();

        Ok(())
    }

    /// 获取订单
    pub async fn get_order(&self, order_id: &str) -> Result<Option<Order>> {
        let tracer = opentelemetry::global::tracer("order-service");
        let mut span = tracer.start("OrderService.get_order");
        span.set_attribute(KeyValue::new("order.id", order_id.to_string()));

        // 模拟数据库查询
        tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;

        let order = Some(Order {
            order_id: order_id.to_string(),
            user_id: "user123".to_string(),
            amount: 99.99,
            status: "completed".to_string(),
        });

        span.set_attribute(KeyValue::new("order.found", order.is_some()));
        span.set_ok();
        span.end();

        Ok(order)
    }

    /// 批量处理订单 - 父Span和子Span
    pub async fn process_bulk_orders(&self, order_ids: Vec<String>) -> Result<Vec<Order>> {
        let tracer = opentelemetry::global::tracer("order-service");
        let mut parent_span = tracer.start("OrderService.process_bulk_orders");
        parent_span.set_attribute(KeyValue::new("order.count", order_ids.len() as i64));

        let parent_ctx = opentelemetry::Context::current_with_span(parent_span);
        let _parent_guard = parent_ctx.attach();

        let mut results = Vec::new();

        for order_id in order_ids {
            // 创建子Span，使用父Context
            let mut child_span = tracer
                .span_builder("OrderService.process_single_order")
                .with_parent_context(parent_ctx.clone())
                .start(&tracer);

            child_span.set_attribute(KeyValue::new("order.id", order_id.clone()));

            match self.get_order(&order_id).await {
                Ok(Some(order)) => {
                    child_span.set_attribute(KeyValue::new("order.status", order.status.clone()));
                    child_span.set_ok();
                    results.push(order);
                }
                Ok(None) => {
                    child_span.set_attribute(KeyValue::new("order.found", false));
                }
                Err(e) => {
                    child_span.record_error(&e);
                    child_span.set_error(e.to_string());
                }
            }

            child_span.end();
        }

        if let Some(span) = parent_ctx.span() {
            span.set_attribute(KeyValue::new("order.processed_count", results.len() as i64));
            span.set_ok();
            span.end();
        }

        Ok(results)
    }
}

/// 使用tracing宏的方式
impl OrderService {
    #[instrument(skip(self), fields(order.user_id = %user_id, order.amount = amount))]
    pub async fn create_order_tracing(&self, user_id: String, amount: f64) -> Result<Order> {
        info!("Creating order for user {}", user_id);

        self.validate_order_tracing(&user_id, amount).await?;

        let order_id = format!("ORD-{}", Uuid::new_v4());

        tracing::Span::current()
            .record("order.id", &order_id);

        self.process_payment_tracing(&order_id, amount).await?;

        Ok(Order {
            order_id,
            user_id,
            amount,
            status: "created".to_string(),
        })
    }

    #[instrument(skip(self))]
    async fn validate_order_tracing(&self, user_id: &str, amount: f64) -> Result<()> {
        if amount <= 0.0 {
            return Err(anyhow::anyhow!("Invalid amount"));
        }
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(())
    }

    #[instrument(skip(self))]
    async fn process_payment_tracing(&self, order_id: &str, amount: f64) -> Result<()> {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        info!("Payment processed for order {}", order_id);
        Ok(())
    }
}
```

### 3.2 记录指标

```rust
// src/metrics/order_metrics.rs

use opentelemetry::metrics::{Counter, Histogram, ObservableGauge, UpDownCounter, Meter};
use opentelemetry::KeyValue;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

pub struct OrderMetrics {
    order_counter: Counter<u64>,
    order_error_counter: Counter<u64>,
    order_value_histogram: Histogram<f64>,
    order_processing_time: Histogram<f64>,
    queue_size: Arc<AtomicI64>,
    active_connections: UpDownCounter<i64>,
}

impl OrderMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("order-service");

        let order_counter = meter
            .u64_counter("orders.total")
            .with_description("Total number of orders")
            .init();

        let order_error_counter = meter
            .u64_counter("orders.errors")
            .with_description("Total number of order errors")
            .init();

        let order_value_histogram = meter
            .f64_histogram("order.value")
            .with_description("Order value distribution")
            .with_unit("USD")
            .init();

        let order_processing_time = meter
            .f64_histogram("order.processing.duration")
            .with_description("Order processing time")
            .with_unit("ms")
            .init();

        let queue_size = Arc::new(AtomicI64::new(0));
        let queue_size_clone = queue_size.clone();

        let _queue_size_gauge: ObservableGauge<i64> = meter
            .i64_observable_gauge("queue.size")
            .with_description("Current queue size")
            .with_callback(move |observer| {
                observer.observe(
                    queue_size_clone.load(Ordering::Relaxed),
                    &[],
                );
            })
            .init();

        let active_connections = meter
            .i64_up_down_counter("connections.active")
            .with_description("Number of active connections")
            .init();

        Self {
            order_counter,
            order_error_counter,
            order_value_histogram,
            order_processing_time,
            queue_size,
            active_connections,
        }
    }

    pub fn record_order_created(&self, amount: f64, status: &str) {
        self.order_counter.add(
            1,
            &[
                KeyValue::new("status", status.to_string()),
                KeyValue::new("service", "order-service"),
            ],
        );

        self.order_value_histogram.record(
            amount,
            &[KeyValue::new("currency", "USD")],
        );
    }

    pub fn record_order_error(&self, error_type: &str) {
        self.order_error_counter.add(
            1,
            &[KeyValue::new("error.type", error_type.to_string())],
        );
    }

    pub fn record_processing_time(&self, duration_ms: f64, method: &str) {
        self.order_processing_time.record(
            duration_ms,
            &[KeyValue::new("method", method.to_string())],
        );
    }

    pub fn increment_active_connections(&self) {
        self.active_connections.add(1, &[]);
    }

    pub fn decrement_active_connections(&self) {
        self.active_connections.add(-1, &[]);
    }

    pub fn update_queue_size(&self, size: i64) {
        self.queue_size.store(size, Ordering::Relaxed);
    }
}

use std::future::Future;
use std::time::Instant;

pub async fn timed<F, Fut, R>(metrics: &OrderMetrics, method: &str, f: F) -> R
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = R>,
{
    let start = Instant::now();
    let result = f().await;
    let duration = start.elapsed().as_millis() as f64;

    metrics.record_processing_time(duration, method);

    result
}
```

---

## 4. 框架集成

### 4.1 Axum集成

```rust
// src/handlers/order_handler.rs

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::Instant;
use tracing::{info, instrument};

use crate::metrics::order_metrics::OrderMetrics;
use crate::services::order_service::{Order, OrderService};

#[derive(Clone)]
pub struct AppState {
    pub order_service: OrderService,
    pub metrics: Arc<OrderMetrics>,
}

#[derive(Deserialize)]
pub struct CreateOrderRequest {
    user_id: String,
    amount: f64,
}

#[derive(Serialize)]
pub struct CreateOrderResponse {
    order_id: String,
    user_id: String,
    amount: f64,
    status: String,
}

#[derive(Serialize)]
pub struct ErrorResponse {
    error: String,
}

#[derive(Deserialize)]
pub struct BulkProcessRequest {
    order_ids: Vec<String>,
}

/// 健康检查
pub async fn health_check() -> StatusCode {
    StatusCode::OK
}

/// 创建订单
#[instrument(skip(state, request))]
pub async fn create_order(
    State(state): State<Arc<AppState>>,
    Json(request): Json<CreateOrderRequest>,
) -> Result<Json<CreateOrderResponse>, (StatusCode, Json<ErrorResponse>)> {
    let start = Instant::now();
    state.metrics.increment_active_connections();

    let result = async {
        match state
            .order_service
            .create_order(request.user_id.clone(), request.amount)
            .await
        {
            Ok(order) => {
                state.metrics.record_order_created(request.amount, "success");

                info!(order_id = %order.order_id, "Order created successfully");

                Ok(Json(CreateOrderResponse {
                    order_id: order.order_id,
                    user_id: order.user_id,
                    amount: order.amount,
                    status: order.status,
                }))
            }
            Err(e) => {
                state.metrics.record_order_error(&e.to_string());

                Err((
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(ErrorResponse {
                        error: e.to_string(),
                    }),
                ))
            }
        }
    }
    .await;

    state.metrics.decrement_active_connections();
    let duration = start.elapsed().as_millis() as f64;
    state.metrics.record_processing_time(duration, "POST /api/orders");

    result
}

/// 获取订单
#[instrument(skip(state))]
pub async fn get_order(
    State(state): State<Arc<AppState>>,
    Path(order_id): Path<String>,
) -> Result<Json<Order>, (StatusCode, Json<ErrorResponse>)> {
    match state.order_service.get_order(&order_id).await {
        Ok(Some(order)) => Ok(Json(order)),
        Ok(None) => Err((
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "Order not found".to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )),
    }
}

/// 批量处理订单
#[instrument(skip(state, request))]
pub async fn bulk_process_orders(
    State(state): State<Arc<AppState>>,
    Json(request): Json<BulkProcessRequest>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    match state
        .order_service
        .process_bulk_orders(request.order_ids)
        .await
    {
        Ok(results) => Ok(Json(serde_json::json!({
            "results": results,
            "count": results.len(),
        }))),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )),
    }
}

/// 调用下游服务示例
#[instrument(skip(state))]
pub async fn call_downstream(
    State(state): State<Arc<AppState>>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    use reqwest;
    use opentelemetry::propagation::TextMapPropagator;
    use opentelemetry_sdk::propagation::TraceContextPropagator;

    let client = reqwest::Client::new();

    // 注入当前Trace上下文到请求头
    let mut headers = reqwest::header::HeaderMap::new();
    let propagator = TraceContextPropagator::new();
    let ctx = opentelemetry::Context::current();
    propagator.inject_context(&ctx, &mut HeaderMapCarrier(&mut headers));

    match client
        .get("http://downstream-service/api/data")
        .headers(headers)
        .send()
        .await
    {
        Ok(response) => {
            let data: serde_json::Value = response.json().await.unwrap_or_default();
            Ok(Json(serde_json::json!({
                "downstream_response": data,
            })))
        }
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )),
    }
}

/// 用于传播请求头的carrier
struct HeaderMapCarrier<'a>(&'a mut reqwest::header::HeaderMap);

impl<'a> opentelemetry::propagation::Injector for HeaderMapCarrier<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}

/// 创建路由
pub fn create_routes(state: Arc<AppState>) -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/api/orders", post(create_order))
        .route("/api/orders/:order_id", get(get_order))
        .route("/api/orders/bulk", post(bulk_process_orders))
        .route("/api/call-downstream", get(call_downstream))
        .with_state(state)
}
```

```rust
// src/main.rs

mod handlers;
mod metrics;
mod services;
mod telemetry;

use std::sync::Arc;
use axum::Server;
use tokio::signal;
use tracing::info;

use crate::handlers::order_handler::{create_routes, AppState};
use crate::metrics::order_metrics::OrderMetrics;
use crate::services::order_service::OrderService;
use crate::telemetry::init::init_telemetry;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化遥测
    init_telemetry().await?;

    let state = Arc::new(AppState {
        order_service: OrderService::new(),
        metrics: Arc::new(OrderMetrics::new()),
    });

    let app = create_routes(state);

    let addr = std::net::SocketAddr::from(([0, 0, 0, 0], 3000));
    info!("Server starting on {}", addr);

    Server::bind(&addr)
        .serve(app.into_make_service())
        .with_graceful_shutdown(shutdown_signal())
        .await?;

    // 优雅关闭
    telemetry::shutdown().await;

    Ok(())
}

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    info!("Shutdown signal received, starting graceful shutdown");
}
```

### 4.2 Actix Web集成

```rust
// src/handlers/actix_handlers.rs

use actix_web::{get, post, web, HttpResponse, Responder, Error};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::metrics::order_metrics::OrderMetrics;
use crate::services::order_service::{Order, OrderService};

pub struct AppState {
    pub order_service: OrderService,
    pub metrics: Arc<OrderMetrics>,
}

#[derive(Deserialize)]
pub struct CreateOrderRequest {
    user_id: String,
    amount: f64,
}

#[derive(Serialize)]
pub struct CreateOrderResponse {
    order_id: String,
    user_id: String,
    amount: f64,
    status: String,
}

#[get("/health")]
pub async fn health_check() -> impl Responder {
    HttpResponse::Ok().json(serde_json::json!({"status": "healthy"}))
}

#[post("/api/orders")]
pub async fn create_order(
    state: web::Data<AppState>,
    request: web::Json<CreateOrderRequest>,
) -> Result<impl Responder, Error> {
    state.metrics.increment_active_connections();

    let result = state
        .order_service
        .create_order(request.user_id.clone(), request.amount)
        .await;

    state.metrics.decrement_active_connections();

    match result {
        Ok(order) => {
            state.metrics.record_order_created(request.amount, "success");
            Ok(HttpResponse::Created().json(CreateOrderResponse {
                order_id: order.order_id,
                user_id: order.user_id,
                amount: order.amount,
                status: order.status,
            }))
        }
        Err(e) => {
            state.metrics.record_order_error(&e.to_string());
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": e.to_string()
            })))
        }
    }
}

// 使用actix-web-opentelemetry中间件
pub fn configure_app(cfg: &mut web::ServiceConfig) {
    cfg.service(health_check)
       .service(create_order);
}

// main.rs中使用
/*
use actix_web::{App, HttpServer};
use actix_web_opentelemetry::RequestTracing;

HttpServer::new(move || {
    App::new()
        .wrap(RequestTracing::new())
        .app_data(web::Data::new(state.clone()))
        .configure(configure_app)
})
.bind("0.0.0.0:8080")?
.run()
.await
*/
```

---

## 5. 生产环境最佳实践

### 5.1 采样配置

```rust
// src/telemetry/sampling.rs

use opentelemetry::trace::{Sampler, SamplingDecision, SamplingResult, TraceContextExt, TraceState};
use opentelemetry::Context;

/// 自定义采样器
pub struct CustomSampler {
    base_ratio: f64,
}

impl CustomSampler {
    pub fn new(ratio: f64) -> Self {
        Self { base_ratio: ratio }
    }
}

impl Sampler for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 对健康检查不采样
        if name.contains("health") {
            return SamplingResult {
                decision: SamplingDecision::Drop,
                trace_state: TraceState::default(),
                attributes: Vec::new(),
            };
        }

        // 对错误全量采样
        if name.contains("error") || name.contains("Exception") {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                trace_state: TraceState::default(),
                attributes: Vec::new(),
            };
        }

        // 对关键操作全量采样
        if name.contains("payment") || name.contains("order/create") {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                trace_state: TraceState::default(),
                attributes: Vec::new(),
            };
        }

        // 使用基础采样率
        let trace_id_bytes = trace_id.to_bytes();
        let trace_id_u64 = u64::from_le_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);

        let threshold = (self.base_ratio * u64::MAX as f64) as u64;

        let decision = if trace_id_u64 < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };

        SamplingResult {
            decision,
            trace_state: TraceState::default(),
            attributes: Vec::new(),
        }
    }

    fn description(&self) -> String {
        format!("CustomSampler{{ratio={}}}", self.base_ratio)
    }
}
```

### 5.2 性能优化

```rust
// src/telemetry/performance.rs

use std::sync::Arc;
use opentelemetry::trace::{Span, Tracer};

/// 对象池用于Span属性
pub struct AttributePool {
    // 可以预分配常用属性
}

/// 避免在热路径分配内存的Span包装器
pub struct FastSpan {
    inner: Box<dyn Span>,
}

/// 使用静态分发而非动态分发的Tracer
pub struct StaticTracer<T: Tracer> {
    inner: T,
}

impl<T: Tracer> StaticTracer<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }

    pub fn start_fast<S: Into<std::borrow::Cow<'static, str>>>(
        &self,
        name: S,
    ) -> FastSpan {
        FastSpan {
            inner: Box::new(self.inner.start(name)),
        }
    }
}

/// 条件编译优化
#[cfg(feature = "telemetry")]
macro_rules! span_if_enabled {
    ($name:expr) => {
        Some(opentelemetry::global::tracer("rust-service").start($name))
    };
}

#[cfg(not(feature = "telemetry"))]
macro_rules! span_if_enabled {
    ($name:expr) => {
        None::<()>
    };
}

/// 批量属性设置
pub fn set_span_attributes_batch(span: &mut dyn Span, attrs: &[(opentelemetry::Key, opentelemetry::Value)]) {
    for (key, value) in attrs {
        span.set_attribute(opentelemetry::KeyValue::new(key.clone(), value.clone()));
    }
}

/// 使用Arc减少克隆
pub type SharedTracer = Arc<dyn Tracer + Send + Sync>;

/// 零成本抽象：如果遥测被禁用，编译时优化掉
#[inline(always)]
pub fn trace_if_enabled<F>(name: &str, f: F)
where
    F: FnOnce(),
{
    if opentelemetry::global::tracer_provider().version().is_some() {
        let tracer = opentelemetry::global::tracer("rust-service");
        let mut span = tracer.start(name);
        f();
        span.end();
    } else {
        f();
    }
}
```

---

## 6. 调试技巧

### 6.1 本地开发配置

```rust
// src/telemetry/dev_config.rs

use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::{Config, TracerProvider as SdkTracerProvider};
use opentelemetry_stdout::SpanExporter;

pub fn init_dev_telemetry() -> SdkTracerProvider {
    let exporter = SpanExporter::default();

    let provider = SdkTracerProvider::builder()
        .with_simple_exporter(exporter)
        .with_config(Config::default())
        .build();

    opentelemetry::global::set_tracer_provider(provider.clone());

    provider
}
```

### 6.2 验证Trace传播

```rust
// src/telemetry/verify.rs

use opentelemetry::trace::TraceContextExt;
use opentelemetry::Context;
use tracing::info;

pub fn log_current_trace_info() {
    let current_span = opentelemetry::global::tracer("rust-service")
        .start("verify");
    let ctx = Context::current_with_span(current_span);

    let span = ctx.span();
    let span_context = span.span_context();

    if span_context.is_valid() {
        info!(
            trace_id = %span_context.trace_id(),
            span_id = %span_context.span_id(),
            trace_flags = ?span_context.trace_flags(),
            "Current trace context"
        );
    } else {
        info!("No valid trace context");
    }

    span.end();
}
```

### 6.3 测试Span创建

```rust
// tests/telemetry_tests.rs

use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::{TracerProvider as SdkTracerProvider, InMemorySpanExporter, SimpleSpanProcessor};

#[tokio::test]
async fn test_create_order_creates_span() {
    // 创建内存导出器
    let exporter = InMemorySpanExporter::default();

    let provider = SdkTracerProvider::builder()
        .with_span_processor(SimpleSpanProcessor::new(Box::new(exporter.clone())))
        .build();

    opentelemetry::global::set_tracer_provider(provider.clone());

    // 执行
    let service = order_service::OrderService::new();
    let _ = service.create_order("user123".to_string(), 99.99).await;

    // 验证
    let spans = exporter.get_finished_spans().unwrap();
    assert!(!spans.is_empty());

    let main_span = spans.iter()
        .find(|s| s.name.as_ref() == "OrderService.create_order");
    assert!(main_span.is_some());
}
```

---

## 7. 参考资源

- [OpenTelemetry Rust官方文档](https://opentelemetry.io/docs/languages/rust/)
- [OpenTelemetry Rust SDK GitHub](https://github.com/open-telemetry/opentelemetry-rust)
- [Tokio官方文档](https://tokio.rs/)
- [Axum文档](https://docs.rs/axum/latest/axum/)
- [Actix Web文档](https://actix.rs/)
- [Tracing文档](https://docs.rs/tracing/latest/tracing/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
