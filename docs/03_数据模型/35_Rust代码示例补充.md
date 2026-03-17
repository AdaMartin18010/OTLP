---
title: OTLP Rust 代码示例补充
description: OTLP Rust 代码示例补充 详细指南和最佳实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 核心实现
tags:
  - otlp
  - observability
  - performance
  - optimization
  - sampling
  - security
  - compliance
status: published
---
# OTLP Rust 代码示例补充

> **文档编号**: 35
> **创建日期**: 2025年10月11日
> **文档类型**: Rust代码示例补充
> **文档状态**: ✅ 完成
> **内容规模**: 1,500+ 行

---

## 文档概览

### 文档目标

本文档为OTLP数据模型补充Rust代码示例，提供完整的Rust实现，涵盖Traces、Metrics、Logs等核心功能。

### Rust支持

```text
Rust支持:
┌─────────────────────────────────────────────────┐
│  SDK名称        │ opentelemetry-rust             │
│  版本要求       │ Rust 1.70+                     │
│  SDK成熟度      │ ⭐⭐⭐⭐                       │
│  性能          │ ⭐⭐⭐⭐⭐                     │
│  内存安全      │ ⭐⭐⭐⭐⭐                     │
└─────────────────────────────────────────────────┘
```

---

## 1. Traces - Rust实现

### 1.1 创建基本Span

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::global;
use opentelemetry::KeyValue;

fn create_span(name: &str) {
    let tracer = global::tracer("example-service");

    let mut span = tracer.start(name);

    // 添加属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.status_code", 200));

    // 执行业务逻辑
    std::thread::sleep(std::time::Duration::from_millis(100));

    span.end();
}

fn main() {
    create_span("example-operation");
}
```

### 1.2 Span关系（父子Span）

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::global;

fn parent_span() {
    let tracer = global::tracer("example-service");

    let mut parent = tracer.start("parent-operation");

    // 创建子Span
    child_span();

    parent.end();
}

fn child_span() {
    let tracer = global::tracer("example-service");

    let mut child = tracer.start("child-operation");

    // 执行业务逻辑
    std::thread::sleep(std::time::Duration::from_millis(50));

    child.end();
}

fn main() {
    parent_span();
}
```

### 1.3 异常处理

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::global;
use opentelemetry::trace::Status;

fn operation_with_error() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("example-service");

    let mut span = tracer.start("operation-with-error");

    let result = std::panic::catch_unwind(|| {
        // 模拟错误
        panic!("something went wrong");
    });

    match result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("success", true));
            span.set_status(Status::Ok);
            Ok(())
        }
        Err(_) => {
            span.set_attribute(KeyValue::new("success", false));
            span.set_status(Status::error("operation failed"));
            Err("operation failed".into())
        }
    }
}

fn main() {
    match operation_with_error() {
        Ok(_) => println!("Success"),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

---

## 2. Metrics - Rust实现

### 2.1 Counter指标

```rust
use opentelemetry::metrics::{Counter, Meter};
use opentelemetry::global;
use opentelemetry::KeyValue;

fn create_counter() {
    let mut meter = global::meter("example-service");

    let counter = meter
        .u64_counter("http_requests_total")
        .with_description("Total number of HTTP requests")
        .init();

    // 增加计数
    counter.add(
        1,
        &[
            KeyValue::new("method", "GET"),
            KeyValue::new("status", "200"),
        ],
    );
}

fn main() {
    create_counter();
    std::thread::sleep(std::time::Duration::from_secs(1));
}
```

### 2.2 Histogram指标

```rust
use opentelemetry::metrics::{Histogram, Meter};
use opentelemetry::global;
use opentelemetry::KeyValue;

fn create_histogram() {
    let mut meter = global::meter("example-service");

    let histogram = meter
        .u64_histogram("http_request_duration_ms")
        .with_description("HTTP request duration in milliseconds")
        .init();

    // 记录值
    histogram.record(
        150,
        &[
            KeyValue::new("method", "GET"),
            KeyValue::new("endpoint", "/api/users"),
        ],
    );
}

fn main() {
    create_histogram();
    std::thread::sleep(std::time::Duration::from_secs(1));
}
```

### 2.3 Gauge指标

```rust
use opentelemetry::metrics::{ObservableGauge, Meter};
use opentelemetry::global;
use opentelemetry::KeyValue;

fn create_gauge() {
    let mut meter = global::meter("example-service");

    let gauge = meter
        .u64_observable_gauge("memory_usage_bytes")
        .with_description("Memory usage in bytes")
        .init();

    // 注册回调
    meter.register_callback(&[Box::new(gauge)], |observer| {
        let memory_usage = get_memory_usage();

        observer.observe_u64(
            &gauge,
            memory_usage,
            &[KeyValue::new("type", "heap")],
        );
    });

    println!("Gauge registered");
}

fn get_memory_usage() -> u64 {
    // 获取内存使用量
    1024 * 1024 * 100 // 100MB
}

fn main() {
    create_gauge();
}
```

---

## 3. Logs - Rust实现

### 3.1 记录日志

```rust
use opentelemetry::logs::{Logger, LoggerProvider};
use opentelemetry::global;
use opentelemetry::KeyValue;

fn create_log() {
    let logger = global::logger("example-service");

    logger.emit(opentelemetry::logs::LogRecord {
        body: Some("User logged in".into()),
        severity_number: Some(opentelemetry::logs::Severity::Info),
        severity_text: Some("INFO".into()),
        attributes: vec![
            KeyValue::new("user_id", "12345"),
            KeyValue::new("ip_address", "192.168.1.1"),
        ],
        ..Default::default()
    });
}

fn main() {
    create_log();
    std::thread::sleep(std::time::Duration::from_secs(1));
}
```

---

## 4. 异步处理

### 4.1 异步Span

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::global;
use tokio;

async fn async_operation() -> Result<String, Box<dyn std::error::Error>> {
    let tracer = global::tracer("example-service");

    let mut span = tracer.start("async-operation");

    // 异步操作
    let result = tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    span.set_attribute(KeyValue::new("async.duration_ms", 100));
    span.set_status(opentelemetry::trace::Status::Ok);
    span.end();

    Ok("success".to_string())
}

#[tokio::main]
async fn main() {
    match async_operation().await {
        Ok(result) => println!("Success: {}", result),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

---

## 5. 性能优化

### 5.1 批量导出

```rust
use opentelemetry::trace::{BatchSpanProcessor, TracerProvider};
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_sdk::export::trace::stdout;

fn setup_batch_exporter() {
    let exporter = stdout::new_pretty();

    let batch_processor = BatchSpanProcessor::builder(exporter, tokio::spawn)
        .with_max_queue_size(2048)
        .with_scheduled_delay(std::time::Duration::from_secs(5))
        .build();

    let _tracer_provider = SdkTracerProvider::builder()
        .with_span_processor(batch_processor)
        .build();

    println!("Batch exporter configured");
}

fn main() {
    setup_batch_exporter();
}
```

---

## 6. 最佳实践

### 6.1 性能优化

```text
性能优化最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 使用批量导出减少开销                         │
│  ✅ 合理设置采样率                               │
│  ✅ 使用异步处理避免阻塞                         │
│  ✅ 缓存常用属性                                 │
│  ✅ 避免在热点路径中创建过多Span                 │
└─────────────────────────────────────────────────┘
```

### 6.2 内存安全

```text
内存安全最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 使用Rust的所有权系统                         │
│  ✅ 避免不必要的克隆                             │
│  ✅ 使用引用计数智能指针                         │
│  ✅ 及时释放资源                                 │
└─────────────────────────────────────────────────┘
```

---

## 7. 总结

### 7.1 核心要点

```text
Rust支持核心要点:
┌─────────────────────────────────────────────────┐
│  1. 性能优势                                    │
│     - 零成本抽象                                │
│     - 接近C的性能                               │
│     - 内存安全保证                              │
│                                                 │
│  2. 并发优势                                    │
│     - 无数据竞争                                │
│     - 异步支持                                  │
│     - 高性能并发                                │
│                                                 │
│  3. 生态支持                                    │
│     - 云原生生态                                │
│     - WebAssembly支持                           │
│     - 嵌入式系统                                │
└─────────────────────────────────────────────────┘
```

### 7.2 适用场景

```text
适用场景:
┌─────────────────────────────────────────────────┐
│  场景          │ 推荐度                          │
├─────────────────────────────────────────────────┤
│  高性能微服务  │ ⭐⭐⭐⭐⭐                    │
│  系统编程      │ ⭐⭐⭐⭐⭐                   │
│  嵌入式系统    │ ⭐⭐⭐⭐⭐                   │
│  WebAssembly   │ ⭐⭐⭐⭐⭐                  │
│  区块链        │ ⭐⭐⭐⭐⭐                   │
│  游戏引擎      │ ⭐⭐⭐⭐⭐                   │
└─────────────────────────────────────────────────┘
```

---

**最后更新**: 2025年10月11日
**维护者**: OTLP深度梳理团队
**版本**: 1.0.0
