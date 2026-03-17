---
title: React Native跨平台OTLP方案
description: React Native应用集成OpenTelemetry的跨平台方案，包含Native Bridge、Expo支持和性能优化
version: OTLP v1.10.0 / React Native v0.73+
date: 2026-03-17
author: OTLP项目团队
category: 移动端可观测性
tags:
  - react-native
  - cross-platform
  - mobile
  - javascript
  - otlp
status: published
---

# React Native跨平台OTLP方案

> **版本**: OTLP v1.10.0 / React Native v0.73+
> **最后更新**: 2026-03-17
> **阅读时间**: 约20分钟

---

## 1. 概述

### 1.1 React Native可观测性挑战

React Native作为跨平台框架，其可观测性面临独特挑战：

| 挑战 | 描述 | 解决方案 |
|------|------|----------|
| 双端差异 | iOS/Android实现不同 | 统一Bridge接口 |
| JS/Native通信 | Bridge性能开销 | 批量上报、异步处理 |
| Metro打包 | 代码分割影响 | 初始化时序控制 |
| Hermes引擎 | 性能分析差异 | 专用Hermes Profiler |
| 第三方库 | 插桩覆盖不全 | 手动补全关键路径 |

### 1.2 架构选择

```
┌─────────────────────────────────────────────────────────────────┐
│                     React Native App                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    JavaScript Layer                      │   │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐ │   │
│  │  │  React   │  │  Redux   │  │  React   │  │  Custom  │ │   │
│  │  │Components│  │  Store   │  │ Navigation│  │  Hooks   │ │   │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘ │   │
│  │       │             │             │             │        │   │
│  │       └─────────────┴─────────────┴─────────────┘        │   │
│  │                         │                                 │   │
│  │              ┌──────────▼──────────┐                     │   │
│  │              │  @opentelemetry/api │                     │   │
│  │              │  (JS SDK Core)      │                     │   │
│  │              └──────────┬──────────┘                     │   │
│  │                         │                                 │   │
│  │              ┌──────────▼──────────┐                     │   │
│  │              │   Native Bridge     │                     │   │
│  │              │   (TurboModules)    │                     │   │
│  │              └──────────┬──────────┘                     │   │
│  └─────────────────────────┼─────────────────────────────────┘   │
│                            │                                      │
│  ══════════════════════════╪══════════════════════════════════   │
│                            │                                      │
│  ┌─────────────────────────┼─────────────────────────────────┐   │
│  │              Native Layer (iOS & Android)                  │   │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │   │
│  │  │iOS Swift │  │ Android  │  │  Network │  │  Device  │   │   │
│  │  │   SDK    │  │  Kotlin  │  │  Layer   │  │  Info    │   │   │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │   │
│  │       │             │             │             │          │   │
│  │       └─────────────┴─────────────┴─────────────┘          │   │
│  │                         │                                   │   │
│  │              ┌──────────▼──────────┐                       │   │
│  │              │   OTLP Exporter     │                       │   │
│  │              │   (gRPC/HTTP)       │                       │   │
│  │              └──────────┬──────────┘                       │   │
│  └─────────────────────────┼─────────────────────────────────┘   │
│                            │                                      │
└────────────────────────────┼──────────────────────────────────────┘
                             │
                    ┌────────▼────────┐
                    │  OTLP Collector │
                    │   (Backend)     │
                    └─────────────────┘
```

---

## 2. 方案选型

### 2.1 方案对比

| 方案 | 优点 | 缺点 | 适用场景 |
|------|------|------|----------|
| **纯JS SDK** | 跨平台一致、易集成 | 缺少Native信息、Bridge开销 | Web/简单应用 |
| **Native Bridge** | 完整Native信息、性能优化 | 双端开发、维护复杂 | 生产级应用 |
| **混合方案** | 平衡灵活性和功能 | 架构复杂 | 大多数场景 |
| **Expo插件** | 零配置、快速集成 | 定制受限 | Expo项目 |

### 2.2 推荐方案：Native Bridge

本文档采用**Native Bridge方案**，原因：

- 完整捕获Native层性能数据
- 支持离线缓存和后台导出
- 更好的电量和性能优化

---

## 3. 环境准备

### 3.1 安装依赖

```bash
# JavaScript依赖
npm install @opentelemetry/api @opentelemetry/sdk-trace-base
npm install @opentelemetry/sdk-trace-react-native
npm install @opentelemetry/exporter-trace-otlp-http

# React Native特定
npm install react-native-otel-bridge  # 自定义Native Module
```

### 3.2 iOS配置

```ruby
# ios/Podfile
pod 'OpenTelemetrySwiftApi', '~> 1.9.0'
pod 'OpenTelemetrySdk', '~> 1.9.0'
pod 'OTLPExporter', '~> 1.9.0'
pod 'URLSessionInstrumentation', '~> 1.9.0'
```

```swift
// ios/OtelBridge.swift
import Foundation
import React
import OpenTelemetryApi
import OpenTelemetrySdk
import OTLPExporter

@objc(OtelBridge)
class OtelBridge: NSObject, RCTBridgeModule {
    static func moduleName() -> String! {
        return "OtelBridge"
    }

    private var tracerProvider: TracerProvider?

    @objc
    func initialize(_ config: NSDictionary, resolver: @escaping RCTPromiseResolveBlock, rejecter: @escaping RCTPromiseRejectBlock) {
        DispatchQueue.global(qos: .utility).async {
            do {
                let serviceName = config["serviceName"] as? String ?? "ReactNativeApp"
                let endpoint = config["endpoint"] as? String ?? "http://localhost:4318"

                // 初始化iOS SDK
                let resource = Resource(
                    attributes: [
                        "service.name": AttributeValue.string(serviceName),
                        "service.version": AttributeValue.string(Bundle.main.infoDictionary?["CFBundleShortVersionString"] as? String ?? "1.0.0"),
                        "device.model": AttributeValue.string(UIDevice.current.model),
                        "os.name": AttributeValue.string("iOS"),
                        "os.version": AttributeValue.string(UIDevice.current.systemVersion),
                    ]
                )

                let exporter = OtlpTraceExporter(
                    endpoint: URL(string: endpoint)!,
                    config: OtlpConfiguration(),
                    resource: resource
                )

                let processor = BatchSpanProcessor(
                    spanExporter: exporter,
                    scheduleDelay: 5
                )

                self.tracerProvider = TracerProviderBuilder()
                    .add(spanProcessor: processor)
                    .with(resource: resource)
                    .build()

                OpenTelemetry.registerTracerProvider(tracerProvider: self.tracerProvider!)

                resolver(["status": "initialized"])
            } catch {
                rejecter("INIT_ERROR", error.localizedDescription, error)
            }
        }
    }

    @objc
    func startSpan(_ spanData: NSDictionary, resolver: @escaping RCTPromiseResolveBlock, rejecter: @escaping RCTPromiseRejectBlock) {
        let spanName = spanData["name"] as? String ?? "unnamed"
        let traceId = spanData["traceId"] as? String
        let parentSpanId = spanData["parentSpanId"] as? String

        let tracer = OpenTelemetry.instance.tracerProvider.get(
            instrumentationName: "ReactNativeBridge",
            instrumentationVersion: "1.0.0"
        )

        var spanBuilder = tracer.spanBuilder(spanName: spanName)

        // 设置父Span
        if let traceId = traceId, let parentSpanId = parentSpanId {
            let spanContext = SpanContext.create(
                traceId: TraceId(id: traceId),
                spanId: SpanId(id: parentSpanId),
                traceFlags: TraceFlags().settingSampled(true),
                traceState: TraceState()
            )
            spanBuilder = spanBuilder.setParent(spanContext)
        }

        let span = spanBuilder.startSpan()
        let spanId = span.context.spanId.hexString

        // 存储Span供后续操作
        SpanStore.shared.store(span: span, withId: spanId)

        resolver(["spanId": spanId])
    }

    @objc
    func endSpan(_ data: NSDictionary, resolver: @escaping RCTPromiseResolveBlock, rejecter: @escaping RCTPromiseRejectBlock) {
        let spanId = data["spanId"] as? String ?? ""

        if let span = SpanStore.shared.retrieve(spanId: spanId) {
            // 设置属性
            if let attributes = data["attributes"] as? [String: Any] {
                for (key, value) in attributes {
                    if let stringValue = value as? String {
                        span.setAttribute(key: key, value: stringValue)
                    } else if let intValue = value as? Int {
                        span.setAttribute(key: key, value: intValue)
                    }
                }
            }

            // 设置状态
            if let status = data["status"] as? String {
                span.setStatus(status == "ok" ? .ok : .error)
            }

            span.end()
            SpanStore.shared.remove(spanId: spanId)
        }

        resolver(["status": "ended"])
    }

    @objc
    func flush(_ resolver: @escaping RCTPromiseResolveBlock, rejecter: @escaping RCTPromiseRejectBlock) {
        OpenTelemetry.instance.tracerProvider.forceFlush()
        resolver(["status": "flushed"])
    }
}

// Span存储管理
class SpanStore {
    static let shared = SpanStore()
    private var spans: [String: Span] = [:]
    private let lock = NSLock()

    func store(span: Span, withId id: String) {
        lock.lock()
        spans[id] = span
        lock.unlock()
    }

    func retrieve(spanId: String) -> Span? {
        lock.lock()
        defer { lock.unlock() }
        return spans[spanId]
    }

    func remove(spanId: String) {
        lock.lock()
        spans.removeValue(forKey: spanId)
        lock.unlock()
    }
}
```

### 3.3 Android配置

```kotlin
// android/app/src/main/java/com/yourapp/OtelBridgeModule.kt
package com.yourapp

import com.facebook.react.bridge.*
import io.opentelemetry.api.GlobalOpenTelemetry
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.SpanKind
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.context.Context
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter
import java.util.concurrent.ConcurrentHashMap

class OtelBridgeModule(reactContext: ReactApplicationContext) :
    ReactContextBaseJavaModule(reactContext) {

    override fun getName(): String = "OtelBridge"

    private val spanStore = ConcurrentHashMap<String, Span>()
    private var tracerProvider: SdkTracerProvider? = null

    @ReactMethod
    fun initialize(config: ReadableMap, promise: Promise) {
        try {
            val serviceName = config.getString("serviceName") ?: "ReactNativeApp"
            val endpoint = config.getString("endpoint") ?: "http://localhost:4318/v1/traces"

            val exporter = OtlpHttpSpanExporter.builder()
                .setEndpoint(endpoint)
                .build()

            tracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(
                    BatchSpanProcessor.builder(exporter)
                        .setScheduleDelay(5000)
                        .build()
                )
                .setResource(
                    io.opentelemetry.sdk.resources.Resource.builder()
                        .put("service.name", serviceName)
                        .put("service.version", BuildConfig.VERSION_NAME)
                        .put("device.model", Build.MODEL)
                        .put("os.name", "Android")
                        .put("os.version", Build.VERSION.RELEASE)
                        .build()
                )
                .build()

            OpenTelemetrySdk.builder()
                .setTracerProvider(tracerProvider!!)
                .buildAndRegisterGlobal()

            promise.resolve(Arguments.createMap().apply {
                putString("status", "initialized")
            })
        } catch (e: Exception) {
            promise.reject("INIT_ERROR", e.message, e)
        }
    }

    @ReactMethod
    fun startSpan(spanData: ReadableMap, promise: Promise) {
        val spanName = spanData.getString("name") ?: "unnamed"
        val traceId = spanData.getString("traceId")
        val parentSpanId = spanData.getString("parentSpanId")

        val tracer = GlobalOpenTelemetry.getTracer("ReactNativeBridge", "1.0.0")

        var spanBuilder = tracer.spanBuilder(spanName)
            .setSpanKind(SpanKind.INTERNAL)

        // 设置父Span
        if (traceId != null && parentSpanId != null) {
            val parentContext = Context.current().with(
                Span.wrap(
                    io.opentelemetry.api.trace.SpanContext.createFromRemoteParent(
                        traceId,
                        parentSpanId,
                        io.opentelemetry.api.trace.TraceFlags.getSampled(),
                        io.opentelemetry.api.trace.TraceState.getDefault()
                    )
                )
            )
            spanBuilder = spanBuilder.setParent(parentContext)
        }

        val span = spanBuilder.startSpan()
        val spanId = span.spanContext.spanId

        spanStore[spanId] = span

        promise.resolve(Arguments.createMap().apply {
            putString("spanId", spanId)
        })
    }

    @ReactMethod
    fun endSpan(data: ReadableMap, promise: Promise) {
        val spanId = data.getString("spanId") ?: ""
        val span = spanStore.remove(spanId)

        span?.let {
            // 设置属性
            if (data.hasKey("attributes")) {
                val attributes = data.getMap("attributes")
                attributes?.entryIterator?.forEach { entry ->
                    when (val value = entry.value) {
                        is String -> it.setAttribute(entry.key, value)
                        is Number -> it.setAttribute(entry.key, value.toLong())
                        is Boolean -> it.setAttribute(entry.key, value)
                    }
                }
            }

            // 设置状态
            if (data.hasKey("status")) {
                val status = data.getString("status")
                it.setStatus(if (status == "ok") StatusCode.OK else StatusCode.ERROR)
            }

            it.end()
        }

        promise.resolve(Arguments.createMap().apply {
            putString("status", "ended")
        })
    }

    @ReactMethod
    fun flush(promise: Promise) {
        tracerProvider?.forceFlush()
        promise.resolve(Arguments.createMap().apply {
            putString("status", "flushed")
        })
    }
}

// OtelBridgePackage.kt
package com.yourapp

import com.facebook.react.ReactPackage
import com.facebook.react.bridge.NativeModule
import com.facebook.react.bridge.ReactApplicationContext
import com.facebook.react.uimanager.ViewManager

class OtelBridgePackage : ReactPackage {
    override fun createNativeModules(reactContext: ReactApplicationContext):
        List<NativeModule> = listOf(OtelBridgeModule(reactContext))

    override fun createViewManagers(reactContext: ReactApplicationContext):
        List<ViewManager<*, *>> = emptyList()
}
```

---

## 4. JavaScript层实现

### 4.1 Bridge接口封装

```typescript
// src/otel/NativeOtelBridge.ts
import { NativeModules, Platform } from 'react-native';

const { OtelBridge } = NativeModules;

interface OtelConfig {
  serviceName: string;
  endpoint: string;
  sampleRate?: number;
}

interface SpanOptions {
  name: string;
  traceId?: string;
  parentSpanId?: string;
  attributes?: Record<string, string | number | boolean>;
}

class NativeOtelBridge {
  private initialized = false;

  async initialize(config: OtelConfig): Promise<void> {
    if (this.initialized) return;

    await OtelBridge.initialize({
      serviceName: config.serviceName,
      endpoint: config.endpoint,
    });

    this.initialized = true;
  }

  async startSpan(options: SpanOptions): Promise<string> {
    if (!this.initialized) {
      throw new Error('OTel Bridge not initialized');
    }

    const result = await OtelBridge.startSpan({
      name: options.name,
      traceId: options.traceId,
      parentSpanId: options.parentSpanId,
    });

    return result.spanId;
  }

  async endSpan(
    spanId: string,
    options: {
      attributes?: Record<string, string | number | boolean>;
      status?: 'ok' | 'error';
    } = {}
  ): Promise<void> {
    await OtelBridge.endSpan({
      spanId,
      attributes: options.attributes,
      status: options.status,
    });
  }

  async flush(): Promise<void> {
    await OtelBridge.flush();
  }
}

export const nativeBridge = new NativeOtelBridge();
```

### 4.2 OpenTelemetry SDK集成

```typescript
// src/otel/ReactNativeTracerProvider.ts
import {
  TracerProvider,
  BatchSpanProcessor,
  ConsoleSpanExporter,
} from '@opentelemetry/sdk-trace-base';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-http';
import { WebTracerProvider } from '@opentelemetry/sdk-trace-web';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { nativeBridge } from './NativeOtelBridge';

// 自定义Exporter，使用Native Bridge
class NativeBridgeExporter {
  private activeSpans = new Map<string, { name: string; startTime: number }>();

  export(spans: any[], resultCallback: (result: { code: number }) => void): void {
    spans.forEach((span) => {
      const spanId = span.spanContext().spanId;
      const traceId = span.spanContext().traceId;
      const parentSpanId = span.parentSpanId;

      // 使用Native Bridge发送Span
      nativeBridge
        .startSpan({
          name: span.name,
          traceId,
          parentSpanId,
        })
        .then((nativeSpanId) => {
          const attributes: Record<string, any> = {};
          span.attributes && span.attributes.forEach((value: any, key: string) => {
            attributes[key] = value;
          });

          // 添加JS层特有的属性
          attributes['telemetry.source'] = 'javascript';
          attributes['telemetry.platform'] = 'react-native';

          return nativeBridge.endSpan(nativeSpanId, {
            attributes,
            status: span.status.code === 0 ? 'ok' : 'error',
          });
        })
        .catch((error) => {
          console.error('Failed to export span:', error);
        });
    });

    resultCallback({ code: 0 }); // Success
  }

  shutdown(): Promise<void> {
    return nativeBridge.flush();
  }
}

// 创建TracerProvider
export function createReactNativeTracerProvider(config: {
  serviceName: string;
  endpoint: string;
  debug?: boolean;
}): TracerProvider {
  const resource = new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: config.serviceName,
    [SemanticResourceAttributes.SERVICE_VERSION]: '1.0.0',
    [SemanticResourceAttributes.TELEMETRY_SDK_LANGUAGE]: 'javascript',
    'platform': 'react-native',
  });

  const provider = new WebTracerProvider({ resource });

  // 添加Native Bridge Exporter
  provider.addSpanProcessor(
    new BatchSpanProcessor(new NativeBridgeExporter())
  );

  // Debug模式添加Console Exporter
  if (config.debug) {
    provider.addSpanProcessor(
      new BatchSpanProcessor(new ConsoleSpanExporter())
    );
  }

  return provider;
}
```

### 4.3 React Hooks集成

```typescript
// src/otel/useTracer.ts
import { useCallback, useRef, useEffect } from 'react';
import { trace, context, SpanStatusCode } from '@opentelemetry/api';
import { nativeBridge } from './NativeOtelBridge';

interface UseTracerOptions {
  componentName: string;
}

export function useTracer({ componentName }: UseTracerOptions) {
  const tracer = trace.getTracer('react-native-components');

  const traceFunction = useCallback(
    async <T extends (...args: any[]) => any>(
      name: string,
      fn: T,
      ...args: Parameters<T>
    ): Promise<ReturnType<T>> => {
      const span = tracer.startSpan(`${componentName}.${name}`);

      try {
        const result = await context.with(
          trace.setSpan(context.active(), span),
          () => fn(...args)
        );

        span.setStatus({ code: SpanStatusCode.OK });
        return result;
      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({
          code: SpanStatusCode.ERROR,
          message: (error as Error).message,
        });
        throw error;
      } finally {
        span.end();
      }
    },
    [tracer, componentName]
  );

  const traceAsync = useCallback(
    (name: string) => {
      return function (
        target: any,
        propertyKey: string,
        descriptor: PropertyDescriptor
      ) {
        const originalMethod = descriptor.value;

        descriptor.value = async function (...args: any[]) {
          return traceFunction(name, originalMethod.bind(this), ...args);
        };

        return descriptor;
      };
    },
    [traceFunction]
  );

  return { traceFunction, traceAsync };
}

// 组件生命周期追踪
export function useComponentTracer(componentName: string) {
  const tracer = trace.getTracer('react-native-lifecycle');
  const spanRef = useRef<any>(null);

  useEffect(() => {
    spanRef.current = tracer.startSpan(`${componentName}.mount`);
    spanRef.current.setAttribute('component.name', componentName);

    return () => {
      if (spanRef.current) {
        spanRef.current.end();
      }
    };
  }, [componentName, tracer]);

  const traceEvent = useCallback(
    (eventName: string, attributes?: Record<string, any>) => {
      const span = tracer.startSpan(`${componentName}.${eventName}`);
      if (attributes) {
        Object.entries(attributes).forEach(([key, value]) => {
          span.setAttribute(key, value);
        });
      }
      span.end();
    },
    [componentName, tracer]
  );

  return { traceEvent };
}
```

### 4.4 导航追踪

```typescript
// src/otel/navigation.ts
import {
  NavigationContainer,
  useNavigationContainerRef,
} from '@react-navigation/native';
import { trace } from '@opentelemetry/api';

export function createTracedNavigationContainer() {
  const navigationRef = useNavigationContainerRef();
  const tracer = trace.getTracer('react-navigation');

  return (
    <NavigationContainer
      ref={navigationRef}
      onStateChange={(state) => {
        const currentRoute = navigationRef.getCurrentRoute();
        if (currentRoute) {
          const span = tracer.startSpan('navigation.state_change');
          span.setAttribute('navigation.route_name', currentRoute.name);
          span.setAttribute('navigation.route_params', JSON.stringify(currentRoute.params));
          span.end();
        }
      }}
      onReady={() => {
        const span = tracer.startSpan('navigation.ready');
        span.end();
      }}
    >
      {/* ... */}
    </NavigationContainer>
  );
}
```

---

## 5. 性能优化

### 5.1 Bridge批处理

```typescript
// src/otel/BatchBridgeExporter.ts
import { nativeBridge } from './NativeOtelBridge';

export class BatchBridgeExporter {
  private buffer: any[] = [];
  private flushTimer: NodeJS.Timeout | null = null;
  private readonly maxBatchSize = 100;
  private readonly flushInterval = 5000; // 5秒

  export(spans: any[]): void {
    this.buffer.push(...spans);

    if (this.buffer.length >= this.maxBatchSize) {
      this.flush();
    } else {
      this.scheduleFlush();
    }
  }

  private scheduleFlush(): void {
    if (this.flushTimer) return;

    this.flushTimer = setTimeout(() => {
      this.flush();
    }, this.flushInterval);
  }

  private flush(): void {
    if (this.buffer.length === 0) return;

    if (this.flushTimer) {
      clearTimeout(this.flushTimer);
      this.flushTimer = null;
    }

    const batch = this.buffer.splice(0, this.maxBatchSize);

    // 批量发送到Native
    Promise.all(
      batch.map((span) => this.exportSingleSpan(span))
    ).catch((error) => {
      console.error('Batch export failed:', error);
    });

    // 如果还有剩余，继续处理
    if (this.buffer.length > 0) {
      this.scheduleFlush();
    }
  }

  private async exportSingleSpan(span: any): Promise<void> {
    // 实现单Span导出
  }

  shutdown(): Promise<void> {
    this.flush();
    return Promise.resolve();
  }
}
```

### 5.2 采样策略

```typescript
// src/otel/sampling.ts
import { Sampler, SamplingDecision } from '@opentelemetry/sdk-trace-base';

export class ReactNativeSampler implements Sampler {
  private readonly sampleRate: number;
  private readonly alwaysSampleOperations: string[];

  constructor(
    sampleRate = 0.1,
    alwaysSampleOperations: string[] = ['error', 'crash', 'purchase']
  ) {
    this.sampleRate = sampleRate;
    this.alwaysSampleOperations = alwaysSampleOperations;
  }

  shouldSample(context: any, traceId: string, spanName: string): {
    decision: SamplingDecision;
  } {
    // 关键操作全量采样
    if (this.alwaysSampleOperations.some((op) => spanName.includes(op))) {
      return { decision: SamplingDecision.RECORD_AND_SAMPLED };
    }

    // 按比例采样
    const isSampled = this.hashTraceId(traceId) < this.sampleRate;

    return {
      decision: isSampled
        ? SamplingDecision.RECORD_AND_SAMPLED
        : SamplingDecision.NOT_RECORD,
    };
  }

  private hashTraceId(traceId: string): number {
    // 简单的traceId哈希用于采样决策
    let hash = 0;
    for (let i = 0; i < traceId.length; i++) {
      const char = traceId.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash;
    }
    return Math.abs(hash) % 10000 / 10000;
  }

  toString(): string {
    return `ReactNativeSampler{rate=${this.sampleRate}}`;
  }
}
```

---

## 6. 最佳实践

### 6.1 初始化时序

```typescript
// App.tsx
import { useEffect } from 'react';
import { nativeBridge } from './src/otel/NativeOtelBridge';
import { createReactNativeTracerProvider } from './src/otel/ReactNativeTracerProvider';
import { trace } from '@opentelemetry/api';

export default function App() {
  useEffect(() => {
    // 1. 初始化Native Bridge
    await nativeBridge.initialize({
      serviceName: 'MyReactNativeApp',
      endpoint: 'https://collector.example.com:4318',
    });

    // 2. 初始化JS TracerProvider
    const provider = createReactNativeTracerProvider({
      serviceName: 'MyReactNativeApp',
      endpoint: 'https://collector.example.com:4318',
      debug: __DEV__,
    });

    // 3. 注册全局Provider
    trace.setGlobalTracerProvider(provider);
  }, []);

  return (
    <NavigationContainer>
      {/* ... */}
    </NavigationContainer>
  );
}
```

### 6.2 错误边界集成

```typescript
// src/components/ErrorBoundary.tsx
import React from 'react';
import { trace } from '@opentelemetry/api';

export class TelemetryErrorBoundary extends React.Component<
  { children: React.ReactNode },
  { hasError: boolean }
> {
  private tracer = trace.getTracer('error-boundary');

  static getDerivedStateFromError() {
    return { hasError: true };
  }

  componentDidCatch(error: Error, errorInfo: React.ErrorInfo) {
    const span = this.tracer.startSpan('react.error');
    span.recordException(error);
    span.setAttribute('error.component_stack', errorInfo.componentStack);
    span.end();
  }

  render() {
    if (this.state?.hasError) {
      return <FallbackUI />;
    }
    return this.props.children;
  }
}
```

---

## 总结

React Native OTLP集成要点：

1. **Native Bridge方案**: 双端SDK提供完整功能
2. **时序控制**: Native先于JS初始化
3. **批量导出**: 减少Bridge通信开销
4. **采样策略**: 平衡数据完整性与性能
5. **错误边界**: 捕获React渲染错误

---

**参考资源**:

- [OpenTelemetry JavaScript](https://github.com/open-telemetry/opentelemetry-js)
- [React Native TurboModules](https://reactnative.dev/docs/the-new-architecture/pillars-turbomodules)
- [React Native New Architecture](https://reactnative.dev/docs/the-new-architecture/landing-page)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
