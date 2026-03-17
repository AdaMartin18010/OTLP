---
title: WebAssembly OTLP观测技术
description: WebAssembly/WASM环境下的OpenTelemetry观测方案，包含浏览器WASM、WASI服务端和边缘计算场景
version: OTLP v1.9.0 / WASI Preview 2
date: 2026-03-17
author: OTLP项目团队
category: 移动端可观测性
tags:
  - webassembly
  - wasm
  - wasi
  - rust
  - golang
  - otlp
status: published
---

# WebAssembly OTLP观测技术

> **版本**: OTLP v1.10.0 / WASI Preview 2
> **最后更新**: 2026-03-17
> **阅读时间**: 约25分钟

---

## 1. 概述

### 1.1 WebAssembly可观测性特点

WebAssembly (WASM) 作为新兴的运行时技术，其可观测性面临独特挑战：

| 挑战 | 描述 | 解决方案 |
|------|------|----------|
| 沙箱隔离 | 无法直接访问系统资源 | WASI抽象、宿主函数 |
| 单线程模型 | 无原生多线程支持 | 异步运行时、Web Workers |
| 模块边界 | Host ↔ Guest通信开销 | 共享内存、批量导出 |
| 体积小 | 对代码体积敏感 | 选择性编译、tree-shaking |
| 多语言 | Rust/Go/C++/TinyGo等 | 语言特定SDK |

### 1.2 WASM应用场景

```
┌─────────────────────────────────────────────────────────────────┐
│                     WASM应用场景分类                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  浏览器端                                                       │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │ 图像处理    │  │ 视频编解码  │  │ 游戏引擎    │             │
│  │ (WebGL)     │  │ (WebCodecs) │  │ (Unity)     │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
│                                                                 │
│  服务端 (WASI)                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │ 微服务      │  │ Serverless  │  │ 边缘计算    │             │
│  │ (Wasmtime)  │  │ (Fermyon)   │  │ (Cloudflare)│             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
│                                                                 │
│  嵌入式/IoT                                                     │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │ 边缘设备    │  │ 工业控制    │  │ 车载系统    │             │
│  │ (Wasm3)     │  │ (WAMR)      │  │ (WASM Edge) │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.3 架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                     WASM OTLP Architecture                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                      Host Environment                    │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐      │   │
│  │  │  Browser    │  │  Wasmtime   │  │  WasmEdge   │      │   │
│  │  │  (V8)       │  │  (Runtime)  │  │  (Cloud)    │      │   │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘      │   │
│  │         │                │                │              │   │
│  │         └────────────────┴────────────────┘              │   │
│  │                          │                               │   │
│  │              ┌───────────▼───────────┐                   │   │
│  │              │    WASI Interface      │                   │   │
│  │              │  (wasi-http, wasi-logs)│                   │   │
│  │              └───────────┬───────────┘                   │   │
│  └──────────────────────────┼───────────────────────────────┘   │
│                             │                                   │
│  ═══════════════════════════╪═════════════════════════════════  │
│                             │                                   │
│  ┌──────────────────────────┼───────────────────────────────┐   │
│  │              WASM Module (Guest)                          │   │
│  │  ┌───────────────────────┼───────────────────────┐       │   │
│  │  │                       ▼                       │       │   │
│  │  │              ┌─────────────────┐              │       │   │
│  │  │              │  opentelemetry  │              │       │   │
│  │  │              │  (Rust/Go SDK)  │              │       │   │
│  │  │              └────────┬────────┘              │       │   │
│  │  │                       │                       │       │   │
│  │  │       ┌───────────────┼───────────────┐       │       │   │
│  │  │       ▼               ▼               ▼       │       │   │
│  │  │  ┌─────────┐    ┌─────────┐    ┌─────────┐   │       │   │
│  │  │  │ Traces  │    │ Metrics │    │  Logs   │   │       │   │
│  │  │  └────┬────┘    └────┬────┘    └────┬────┘   │       │   │
│  │  │       │              │              │        │       │   │
│  │  │       └──────────────┼──────────────┘        │       │   │
│  │  │                      │                       │       │   │
│  │  │           ┌──────────▼──────────┐            │       │   │
│  │  │           │   OTLP Exporter     │            │       │   │
│  │  │           │  (wasi-http export) │            │       │   │
│  │  │           └──────────┬──────────┘            │       │   │
│  │  └──────────────────────┼───────────────────────┘       │   │
│  └─────────────────────────┼───────────────────────────────┘   │
│                            │                                   │
└────────────────────────────┼───────────────────────────────────┘
                             │
                    ┌────────▼────────┐
                    │  OTLP Collector │
                    └─────────────────┘
```

---

## 2. Rust WASM实现

### 2.1 环境准备

```toml
# Cargo.toml
[package]
name = "wasm-otel"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry
opentelemetry = { version = "0.27", default-features = false }
opentelemetry_sdk = { version = "0.27", default-features = false }
opentelemetry-otlp = { version = "0.27", default-features = false, features = ["http-proto", "trace"] }

# WASM支持
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
js-sys = "0.3"
web-sys = { version = "0.3", features = ["console", "Window", "Request", "RequestInit", "RequestMode", "Response"] }

# WASI支持 (服务端WASM)
wasi = "0.13"

[lib]
crate-type = ["cdylib", "rlib"]

[features]
default = ["browser"]
browser = ["wasm-bindgen", "wasm-bindgen-futures", "js-sys", "web-sys"]
wasi = ["wasi"]
```

### 2.2 浏览器端实现

```rust
// src/lib.rs
use wasm_bindgen::prelude::*;
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider},
    Context, KeyValue,
};
use opentelemetry_sdk::{
    runtime::Tokio,
    trace::{BatchConfig, BatchSpanProcessor, TracerProvider as SdkTracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;

// 初始化WASM模块
#[wasm_bindgen(start)]
pub fn main() {
    console_error_panic_hook::set_once();
}

/// 初始化OpenTelemetry
#[wasm_bindgen]
pub async fn initialize_otel(collector_url: &str) -> Result<(), JsValue> {
    // 配置资源
    let resource = Resource::new([
        KeyValue::new("service.name", "wasm-browser-app"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("telemetry.sdk.language", "rust"),
        KeyValue::new("telemetry.sdk.name", "opentelemetry-wasm"),
    ]);

    // 创建OTLP导出器（使用web-sys的fetch）
    let exporter = create_wasm_exporter(collector_url)?;

    // 配置TracerProvider
    let provider = SdkTracerProvider::builder()
        .with_resource(resource)
        .with_span_processor(
            BatchSpanProcessor::builder(exporter)
                .with_batch_config(
                    BatchConfig::default()
                        .with_max_queue_size(2048)
                        .with_max_export_batch_size(512)
                        .with_scheduled_delay(std::time::Duration::from_secs(5))
                )
                .build()
        )
        .build();

    global::set_tracer_provider(provider);

    Ok(())
}

/// WASM自定义Exporter，使用web-sys fetch
struct WasmHttpExporter {
    endpoint: String,
}

#[async_trait::async_trait(?Send)]
impl opentelemetry_sdk::export::trace::SpanExporter for WasmHttpExporter {
    async fn export(&mut self, batch: Vec<opentelemetry_sdk::export::trace::SpanData>) -> opentelemetry::trace::TraceResult<()> {
        // 序列化为OTLP Protobuf
        let proto_data = serialize_spans_to_proto(batch)?;

        // 使用web-sys发起HTTP请求
        let window = web_sys::window().ok_or("No window available")?;

        let mut opts = web_sys::RequestInit::new();
        opts.method("POST");
        opts.mode(web_sys::RequestMode::Cors);

        // 创建Uint8Array从数据
        let array = js_sys::Uint8Array::from(&proto_data[..]);
        opts.body(Some(&array));

        let request = web_sys::Request::new_with_str_and_init(
            &self.endpoint,
            &opts
        ).map_err(|e| format!("Request creation failed: {:?}", e))?;

        request.headers().set("Content-Type", "application/x-protobuf")?;

        // 发送请求
        let resp_value = wasm_bindgen_futures::JsFuture::from(
            window.fetch_with_request(&request)
        ).await.map_err(|e| format!("Fetch failed: {:?}", e))?;

        let resp: web_sys::Response = resp_value.dyn_into().unwrap();

        if resp.ok() {
            Ok(())
        } else {
            Err(opentelemetry::trace::TraceError::from(
                format!("HTTP error: {}", resp.status())
            ))
        }
    }

    fn shutdown(&mut self) {}
}

/// 创建带追踪的函数
#[wasm_bindgen]
pub fn traced_operation(operation_name: &str) {
    let tracer = global::tracer("wasm-tracer");

    let mut span = tracer.start(operation_name);

    // 执行业务逻辑
    span.set_attribute(KeyValue::new("operation.timestamp", get_timestamp()));

    span.end();
}

/// 带返回值和错误的追踪
#[wasm_bindgen]
pub async fn process_data(input: &str) -> Result<String, JsValue> {
    let tracer = global::tracer("wasm-tracer");
    let mut span = tracer.start("process_data");

    span.set_attribute(KeyValue::new("input.length", input.len() as i64));

    // 模拟异步处理
    let result = async {
        // 处理逻辑...
        if input.is_empty() {
            return Err(JsValue::from_str("Empty input"));
        }

        Ok(format!("Processed: {}", input.to_uppercase()))
    }.await;

    match &result {
        Ok(_) => span.set_status(opentelemetry::trace::Status::Ok),
        Err(e) => {
            span.set_status(opentelemetry::trace::Status::error(e.as_string().unwrap_or_default()));
            span.record_error(&std::io::Error::new(std::io::ErrorKind::Other, "Processing failed"));
        }
    }

    span.end();
    result
}

// 辅助函数
fn get_timestamp() -> i64 {
    js_sys::Date::now() as i64
}

fn serialize_spans_to_proto(_batch: Vec<opentelemetry_sdk::export::trace::SpanData>)
    -> Result<Vec<u8>, opentelemetry::trace::TraceError> {
    // 实现protobuf序列化
    todo!("Protobuf serialization")
}

fn create_wasm_exporter(endpoint: &str) -> Result<WasmHttpExporter, JsValue> {
    Ok(WasmHttpExporter {
        endpoint: endpoint.to_string(),
    })
}
```

### 2.3 JavaScript集成

```javascript
// wasm-otel.js
import init, { initialize_otel, traced_operation, process_data } from './pkg/wasm_otel.js';

class WasmOpenTelemetry {
    constructor() {
        this.initialized = false;
    }

    async initialize(config) {
        // 加载WASM模块
        await init();

        // 初始化OTel
        await initialize_otel(config.endpoint);

        this.initialized = true;
        console.log('✅ WASM OpenTelemetry initialized');
    }

    traced(fn, name) {
        return async (...args) => {
            if (!this.initialized) {
                return fn(...args);
            }

            const spanName = name || fn.name || 'anonymous';

            try {
                traced_operation(`${spanName}.start`);
                const result = await fn(...args);
                traced_operation(`${spanName}.success`);
                return result;
            } catch (error) {
                traced_operation(`${spanName}.error`);
                throw error;
            }
        };
    }

    async processData(input) {
        return await process_data(input);
    }
}

// 使用示例
const wasmOtel = new WasmOpenTelemetry();

async function setup() {
    await wasmOtel.initialize({
        endpoint: 'https://collector.example.com:4318/v1/traces'
    });

    // 包装函数
    const heavyComputation = wasmOtel.traced(
        async (data) => {
            // 复杂计算...
            return data.map(x => x * 2);
        },
        'heavyComputation'
    );

    const result = await heavyComputation([1, 2, 3, 4, 5]);
    console.log(result);
}

setup();
```

---

## 3. WASI服务端实现

### 3.1 WASI HTTP组件

```rust
// wasi-otel.rs
#![allow(unused)]

use std::collections::HashMap;
use wasi::http::outgoing_handler;
use wasi::http::types::{
    Fields, Method, OutgoingBody, OutgoingRequest, Scheme,
};
use wasi::io::streams::OutputStream;

/// WASI原生OTLP导出器
pub struct WasiOtlpExporter {
    collector_url: String,
    headers: HashMap<String, String>,
}

impl WasiOtlpExporter {
    pub fn new(collector_url: impl Into<String>) -> Self {
        Self {
            collector_url: collector_url.into(),
            headers: HashMap::new(),
        }
    }

    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// 使用WASI HTTP接口发送OTLP数据
    pub async fn export_traces(&self, proto_data: Vec<u8>) -> Result<(), OtlpError> {
        // 解析URL
        let url = url::Url::parse(&self.collector_url)
            .map_err(|e| OtlpError::InvalidUrl(e.to_string()))?;

        // 创建请求
        let headers = Fields::new();

        // 设置标准头
        headers.set(&"Content-Type".to_string(), &["application/x-protobuf".to_string()])
            .map_err(|e| OtlpError::HeaderError(format!("{:?}", e)))?;

        headers.set(&"Content-Length".to_string(), &[proto_data.len().to_string()])
            .map_err(|e| OtlpError::HeaderError(format!("{:?}", e)))?;

        // 设置自定义头
        for (key, value) in &self.headers {
            headers.set(&key.clone(), &[value.clone()])
                .map_err(|e| OtlpError::HeaderError(format!("{:?}", e)))?;
        }

        // 构建请求
        let req = OutgoingRequest::new(headers);

        req.set_method(&Method::Post)
            .map_err(|_| OtlpError::RequestError("Failed to set method".into()))?;

        // 设置scheme
        let scheme = match url.scheme() {
            "https" => Scheme::Https,
            _ => Scheme::Http,
        };
        req.set_scheme(Some(&scheme))
            .map_err(|_| OtlpError::RequestError("Failed to set scheme".into()))?;

        // 设置authority和path
        req.set_authority(Some(url.authority()))
            .map_err(|_| OtlpError::RequestError("Failed to set authority".into()))?;

        req.set_path_with_query(Some(url.path()))
            .map_err(|_| OtlpError::RequestError("Failed to set path".into()))?;

        // 获取请求体并写入数据
        let body = req.body()
            .map_err(|_| OtlpError::RequestError("Failed to get body".into()))?;

        let stream = body.write()
            .map_err(|_| OtlpError::RequestError("Failed to get stream".into()))?;

        // 写入protobuf数据
        let mut offset = 0;
        while offset < proto_data.len() {
            let chunk = &proto_data[offset..];
            match stream.write(chunk) {
                Ok(n) => offset += n,
                Err(_) => return Err(OtlpError::WriteError),
            }
        }

        // 刷新并关闭stream
        stream.flush().map_err(|_| OtlpError::WriteError)?;
        drop(stream);

        OutgoingBody::finish(body, None)
            .map_err(|_| OtlpError::RequestError("Failed to finish body".into()))?;

        // 发送请求
        let resp = outgoing_handler::handle(req, None)
            .map_err(|e| OtlpError::NetworkError(format!("{:?}", e)))?;

        // 获取响应
        let resp = resp.subscribe().get()
            .map_err(|e| OtlpError::NetworkError(format!("{:?}", e)))?;

        // 检查状态码
        let status = resp.status();
        if status < 200 || status >= 300 {
            return Err(OtlpError::HttpError(status));
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum OtlpError {
    InvalidUrl(String),
    HeaderError(String),
    RequestError(String),
    WriteError,
    NetworkError(String),
    HttpError(u16),
}
```

### 3.2 TinyGo实现

```go
// wasm-otel.go
package main

import (
    "bytes"
    "context"
    "encoding/json"
    "fmt"
    "net/http"
    "time"

    "github.com/open-telemetry/opentelemetry-go/otel"
    "github.com/open-telemetry/opentelemetry-go/otel/attribute"
    "github.com/open-telemetry/opentelemetry-go/otel/exporters/otlp/otlptrace"
    "github.com/open-telemetry/opentelemetry-go/otel/exporters/otlp/otlptrace/otlptracehttp"
    "github.com/open-telemetry/opentelemetry-go/otel/sdk/resource"
    sdktrace "github.com/open-telemetry/opentelemetry-go/otel/sdk/trace"
    semconv "github.com/open-telemetry/opentelemetry-go/otel/semconv/v1.24.0"
    "github.com/open-telemetry/opentelemetry-go/otel/trace"
)

//export initialize
func initialize(collectorEndpoint *byte, endpointLen int32) int32 {
    endpoint := string(bytesFromPtr(collectorEndpoint, endpointLen))

    ctx := context.Background()

    // 创建OTLP HTTP导出器
    client := otlptracehttp.NewClient(
        otlptracehttp.WithEndpoint(endpoint),
        otlptracehttp.WithInsecure(), // WASI环境中使用insecure
    )

    exporter, err := otlptrace.New(ctx, client)
    if err != nil {
        fmt.Println("Failed to create exporter:", err)
        return 1
    }

    // 配置资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String("wasm-go-service"),
            semconv.ServiceVersionKey.String("1.0.0"),
            attribute.String("wasm.runtime", "wasi"),
        ),
    )
    if err != nil {
        fmt.Println("Failed to create resource:", err)
        return 1
    }

    // 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)

    return 0
}

//export startSpan
func startSpan(namePtr *byte, nameLen int32, parentSpanIDPtr *byte, parentSpanIDLen int32) int64 {
    name := string(bytesFromPtr(namePtr, nameLen))

    tracer := otel.Tracer("wasm-tracer")

    var opts []trace.SpanStartOption

    // 如果有父Span，设置父Context
    if parentSpanIDLen > 0 {
        parentID := string(bytesFromPtr(parentSpanIDPtr, parentSpanIDLen))
        // 解析并设置父Span...
    }

    ctx, span := tracer.Start(context.Background(), name, opts...)

    // 存储span上下文，返回handle
    spanHandle := storeSpan(span, ctx)
    return spanHandle
}

//export endSpan
func endSpan(handle int64, status int32) {
    span, _ := retrieveSpan(handle)
    if span == nil {
        return
    }

    if status != 0 {
        span.SetStatus(trace.ErrorStatus, "error")
    } else {
        span.SetStatus(trace.OkStatus, "")
    }

    span.End()
    removeSpan(handle)
}

//export addAttribute
func addAttribute(handle int64, keyPtr *byte, keyLen int32, valuePtr *byte, valueLen int32) {
    span, _ := retrieveSpan(handle)
    if span == nil {
        return
    }

    key := string(bytesFromPtr(keyPtr, keyLen))
    value := string(bytesFromPtr(valuePtr, valueLen))

    span.SetAttributes(attribute.String(key, value))
}

// 辅助函数
func bytesFromPtr(ptr *byte, length int32) []byte {
    if ptr == nil || length <= 0 {
        return nil
    }
    // TinyGo/WASM内存操作
    return unsafe.Slice(ptr, length)
}

var spanStore = make(map[int64]struct {
    span trace.Span
    ctx  context.Context
})
var spanCounter int64

func storeSpan(span trace.Span, ctx context.Context) int64 {
    handle := atomic.AddInt64(&spanCounter, 1)
    spanStore[handle] = struct {
        span trace.Span
        ctx  context.Context
    }{span, ctx}
    return handle
}

func retrieveSpan(handle int64) (trace.Span, context.Context) {
    if s, ok := spanStore[handle]; ok {
        return s.span, s.ctx
    }
    return nil, nil
}

func removeSpan(handle int64) {
    delete(spanStore, handle)
}

func main() {}
```

---

## 4. 边缘计算场景

### 4.1 Cloudflare Workers实现

```typescript
// worker.ts - Cloudflare Workers with WASM
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-http';
import { NodeSDK } from '@opentelemetry/sdk-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';

// WASM模块类型定义
declare module '*.wasm' {
    const value: WebAssembly.Module;
    export default value;
}

// 加载WASM模块
import wasmModule from '../pkg/edge_processor.wasm';

export interface Env {
    OTLP_ENDPOINT: string;
    OTLP_HEADERS: string;
}

export default {
    async fetch(
        request: Request,
        env: Env,
        ctx: ExecutionContext
    ): Promise<Response> {
        // 初始化OTel SDK
        const sdk = new NodeSDK({
            resource: new Resource({
                [SemanticResourceAttributes.SERVICE_NAME]: 'cloudflare-edge-worker',
                [SemanticResourceAttributes.SERVICE_VERSION]: '1.0.0',
                'cf.colo': request.cf?.colo || 'unknown',
                'cf.country': request.cf?.country || 'unknown',
            }),
            traceExporter: new OTLPTraceExporter({
                url: env.OTLP_ENDPOINT,
                headers: JSON.parse(env.OTLP_HEADERS || '{}'),
            }),
        });

        await sdk.start();

        // 创建根Span
        const tracer = sdk.getTracer('edge-worker');
        const span = tracer.startSpan('edge_request', {
            attributes: {
                'http.method': request.method,
                'http.url': request.url,
                'http.user_agent': request.headers.get('user-agent') || '',
            },
        });

        try {
            // 实例化WASM模块
            const wasm = await WebAssembly.instantiate(wasmModule, {
                env: {
                    // WASI imports
                    memory: new WebAssembly.Memory({ initial: 256 }),
                },
            });

            // 调用WASM处理函数
            const { process_request } = wasm.exports as {
                process_request: (ptr: number, len: number) => number;
            };

            // 准备输入数据
            const inputData = new TextEncoder().encode(
                JSON.stringify({ url: request.url, method: request.method })
            );

            // 分配WASM内存并复制数据
            const memory = (wasm.exports.memory as WebAssembly.Memory);
            const ptr = (wasm.exports.alloc as Function)(inputData.length);
            const wasmMemory = new Uint8Array(memory.buffer);
            wasmMemory.set(inputData, ptr);

            // 调用WASM函数
            const resultPtr = process_request(ptr, inputData.length);

            // 读取结果
            const resultView = new DataView(memory.buffer);
            const resultLen = resultView.getInt32(resultPtr - 4, true);
            const resultData = wasmMemory.slice(resultPtr, resultPtr + resultLen);
            const result = JSON.parse(new TextDecoder().decode(resultData));

            // 记录处理指标
            span.setAttribute('wasm.processing_time_ms', result.processingTime);
            span.setAttribute('wasm.cache_hit', result.cacheHit);

            // 构建响应
            const response = new Response(JSON.stringify(result), {
                headers: { 'Content-Type': 'application/json' },
            });

            span.setStatus({ code: 1 }); // OK

            // 确保Span被导出
            ctx.waitUntil(sdk.shutdown());

            return response;

        } catch (error) {
            span.recordException(error as Error);
            span.setStatus({ code: 2, message: (error as Error).message }); // ERROR

            ctx.waitUntil(sdk.shutdown());

            return new Response(
                JSON.stringify({ error: (error as Error).message }),
                { status: 500, headers: { 'Content-Type': 'application/json' } }
            );
        } finally {
            span.end();
        }
    },
};
```

### 4.2 Fermyon Spin组件

```rust
// spin-otel.rs - Fermyon Spin with OpenTelemetry
use spin_sdk::{
    http::{Request, Response, Router},
    http_component,
    key_value::Store,
};
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider},
    Context, KeyValue,
};

#[http_component]
fn handle_route(req: Request) -> Response {
    let mut router = Router::new();
    router.get("/api/process", handle_process);
    router.handle(req)
}

fn handle_process(req: Request) -> Response {
    // 初始化OTel（Spin应用中保持单例）
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        initialize_otel();
    });

    let tracer = global::tracer("spin-component");
    let mut span = tracer.start("process_request");

    // 解析请求
    let body = req.body().clone().unwrap_or_default();
    span.set_attribute(KeyValue::new("request.body_size", body.len() as i64));

    // 业务处理
    let result = process_with_tracing(&body, &tracer);

    match result {
        Ok(data) => {
            span.set_attribute(KeyValue::new("response.size", data.len() as i64));
            span.set_status(opentelemetry::trace::Status::Ok);
            span.end();

            Response::builder()
                .status(200)
                .header("Content-Type", "application/json")
                .body(Some(data.into()))
                .build()
        }
        Err(e) => {
            span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            span.record_error(&std::io::Error::new(std::io::ErrorKind::Other, &e));
            span.end();

            Response::builder()
                .status(500)
                .body(Some(e.into()))
                .build()
        }
    }
}

fn process_with_tracing(body: &[u8], tracer: &dyn Tracer) -> Result<String, String> {
    let mut span = tracer.start("process_data");
    defer! { span.end() }

    // 子操作1：验证
    let mut validate_span = tracer.start("validate");
    let validated = validate_input(body)?;
    validate_span.set_attribute(KeyValue::new("validation.passed", true));
    validate_span.end();

    // 子操作2：转换
    let mut transform_span = tracer.start("transform");
    let transformed = transform_data(&validated)?;
    transform_span.set_attribute(KeyValue::new("transform.records", transformed.len() as i64));
    transform_span.end();

    // 子操作3：存储
    let mut store_span = tracer.start("store");
    match store_result(&transformed) {
        Ok(_) => {
            store_span.set_status(opentelemetry::trace::Status::Ok);
            store_span.end();
        }
        Err(e) => {
            store_span.set_status(opentelemetry::trace::Status::error(e.clone()));
            store_span.end();
            return Err(e);
        }
    }

    span.set_status(opentelemetry::trace::Status::Ok);
    Ok(transformed)
}

fn initialize_otel() {
    // Spin使用stdout导出器，由Spin运行时收集
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(opentelemetry_stdout::SpanExporter::default())
        .with_resource(opentelemetry_sdk::Resource::new([
            KeyValue::new("service.name", "spin-otel-service"),
            KeyValue::new("service.version", "1.0.0"),
        ]))
        .build();

    global::set_tracer_provider(provider);
}

fn validate_input(body: &[u8]) -> Result<Vec<u8>, String> {
    if body.is_empty() {
        return Err("Empty body".to_string());
    }
    Ok(body.to_vec())
}

fn transform_data(data: &[u8]) -> Result<String, String> {
    String::from_utf8(data.to_vec())
        .map_err(|e| format!("UTF-8 decode error: {}", e))
}

fn store_result(data: &str) -> Result<(), String> {
    let store = Store::open_default()
        .map_err(|e| format!("Store error: {:?}", e))?;

    let key = format!("result:{}", chrono::Utc::now().timestamp());
    store.set(&key, data.as_bytes())
        .map_err(|e| format!("Store set error: {:?}", e))?;

    Ok(())
}
```

---

## 5. 性能优化

### 5.1 WASM代码体积优化

```toml
# Cargo.toml - 优化配置
[profile.release]
opt-level = "z"      # 优化体积
lto = true           # 链接时优化
codegen-units = 1    # 单代码生成单元
panic = "abort"      # 移除panic处理
strip = true         # 移除符号

[profile.wasm]
inherits = "release"
opt-level = "z"
lto = true
```

```bash
# 使用wasm-opt进一步优化
wasm-opt -Oz -o optimized.wasm original.wasm
```

### 5.2 内存管理

```rust
// 使用wee_alloc减少内存分配器体积
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

// 对象池复用
use std::cell::RefCell;

thread_local! {
    static BUFFER_POOL: RefCell<Vec<Vec<u8>>> = RefCell::new(Vec::new());
}

fn get_buffer(size: usize) -> Vec<u8> {
    BUFFER_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        if let Some(buf) = pool.pop() {
            if buf.capacity() >= size {
                return buf;
            }
        }
        Vec::with_capacity(size)
    })
}

fn return_buffer(buf: Vec<u8>) {
    BUFFER_POOL.with(|pool| {
        pool.borrow_mut().push(buf);
    });
}
```

### 5.3 批量导出策略

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

pub struct BatchedExporter {
    buffer: Arc<Mutex<VecDeque<SpanData>>>,
    batch_size: usize,
    flush_interval: Duration,
    exporter: Box<dyn SpanExporter>,
}

impl BatchedExporter {
    pub fn new(exporter: Box<dyn SpanExporter>) -> Self {
        let buffer = Arc::new(Mutex::new(VecDeque::new()));
        let buffer_clone = buffer.clone();

        // 启动定时刷新任务
        wasm_bindgen_futures::spawn_local(async move {
            let mut interval = gloo_timers::future::IntervalStream::new(5000); // 5秒

            while interval.next().await.is_some() {
                let batch: Vec<_> = {
                    let mut buf = buffer_clone.lock().unwrap();
                    buf.drain(..).collect()
                };

                if !batch.is_empty() {
                    // 导出批次
                    Self::export_batch(&exporter, batch).await;
                }
            }
        });

        Self {
            buffer,
            batch_size: 100,
            flush_interval: Duration::from_secs(5),
            exporter,
        }
    }

    pub fn export(&self, span: SpanData) {
        let mut buf = self.buffer.lock().unwrap();
        buf.push_back(span);

        if buf.len() >= self.batch_size {
            let batch: Vec<_> = buf.drain(..).collect();
            drop(buf); // 释放锁

            wasm_bindgen_futures::spawn_local(async move {
                Self::export_batch(&self.exporter, batch).await;
            });
        }
    }

    async fn export_batch(exporter: &dyn SpanExporter, batch: Vec<SpanData>) {
        if let Err(e) = exporter.export(batch).await {
            web_sys::console::error_1(&format!("Export error: {:?}", e).into());
        }
    }
}
```

---

## 6. 最佳实践

### 6.1 开发检查清单

| 检查项 | 建议 | 说明 |
|--------|------|------|
| 代码体积 | <100KB | WASM文件大小限制 |
| 内存使用 | <16MB | 浏览器/WASI限制 |
| 导出批大小 | 50-100 spans | 平衡延迟和吞吐量 |
| 采样率 | 5-10% | 减少数据量 |
| 错误处理 | 优雅降级 | WASM失败不中断Host |

### 6.2 调试技巧

```rust
// 浏览器控制台调试
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);

    #[wasm_bindgen(js_namespace = console)]
    fn error(s: &str);
}

// WASI调试输出
#[cfg(target_arch = "wasm32")]
fn debug_log(msg: &str) {
    unsafe {
        wasi::fd_write(
            1, // stdout
            &[wasi::Ciovec {
                buf: msg.as_ptr(),
                buf_len: msg.len(),
            }],
        );
    }
}
```

### 6.3 测试策略

```rust
// WASM测试
#[cfg(test)]
mod tests {
    use wasm_bindgen_test::*;

    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    async fn test_span_creation() {
        initialize_otel("http://localhost:4318").await.unwrap();

        let tracer = global::tracer("test");
        let span = tracer.start("test_span");

        assert!(!span.span_context().trace_id().to_hex().is_empty());

        span.end();
    }
}
```

---

## 总结

WebAssembly OTLP观测要点：

1. **架构选择**: 浏览器用wasm-bindgen，服务端用WASI
2. **体积优化**: 使用wee_alloc、wasm-opt、LTO
3. **批量导出**: 减少Bridge/WASI调用开销
4. **内存管理**: 使用对象池，避免频繁分配
5. **错误隔离**: WASM失败不影响Host应用

---

**参考资源**:

- [WebAssembly Component Model](https://component-model.bytecodealliance.org/)
- [WASI Preview 2](https://github.com/WebAssembly/WASI/tree/main/preview2)
- [Wasmtime](https://wasmtime.dev/)
- [Fermyon Spin](https://developer.fermyon.com/spin/)
- [Cloudflare Workers WASM](https://developers.cloudflare.com/workers/runtime-apis/webassembly/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
