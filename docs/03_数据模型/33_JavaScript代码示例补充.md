---
title: OTLP JavaScript/TypeScript 代码示例补充
description: OTLP JavaScript/TypeScript 代码示例补充 详细指南和最佳实践
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
# OTLP JavaScript/TypeScript 代码示例补充

> **文档编号**: 33
> **创建日期**: 2025年10月11日
> **文档类型**: JavaScript代码示例补充
> **文档状态**: ✅ 完成
> **内容规模**: 2,000+ 行

---

## 文档概览

### 文档目标

本文档为OTLP数据模型的关键文档补充JavaScript和TypeScript代码示例，提供完整的Node.js和浏览器端实现。

### 适用场景

```text
适用场景:
┌─────────────────────────────────────────────────┐
│  ✅ Node.js后端服务                             │
│  ✅ Express/Fastify Web框架                     │
│  ✅ React/Vue前端应用                          │
│  ✅ 微服务架构                                  │
│  ✅ Serverless函数                             │
│  ✅ 浏览器端追踪                               │
└─────────────────────────────────────────────────┘
```

---

## 1. Span结构 - JavaScript实现

### 1.1 创建基本Span

#### Node.js实现

```javascript
const { trace, context } = require('@opentelemetry/api');

// 创建Tracer
const tracer = trace.getTracer('example-service');

// 创建Span
function createSpan(name) {
    const span = tracer.startSpan(name);

    try {
        // 设置属性
        span.setAttributes({
            'http.method': 'GET',
            'http.url': '/api/users',
            'http.status_code': 200
        });

        // 执行业务逻辑
        console.log(`Executing ${name}`);

        return span;
    } finally {
        span.end();
    }
}

// 使用
const span = createSpan('get-user');
```

#### TypeScript实现

```typescript
import { trace, Span, SpanStatusCode } from '@opentelemetry/api';

const tracer = trace.getTracer('example-service');

function createSpan(name: string): Span {
    const span = tracer.startSpan(name);

    try {
        // 设置属性
        span.setAttributes({
            'http.method': 'GET',
            'http.url': '/api/users',
            'http.status_code': 200
        });

        // 执行业务逻辑
        console.log(`Executing ${name}`);

        return span;
    } finally {
        span.end();
    }
}

// 使用
const span = createSpan('get-user');
```

### 1.2 Span关系（父子Span）

#### Node.js实现1

```javascript
const { trace } = require('@opentelemetry/api');

const tracer = trace.getTracer('example-service');

function parentSpan() {
    const parent = tracer.startSpan('parent-operation');

    try {
        // 创建子Span
        childSpan();
    } finally {
        parent.end();
    }
}

function childSpan() {
    const child = tracer.startSpan('child-operation');

    try {
        // 执行业务逻辑
        console.log('Child operation');
    } finally {
        child.end();
    }
}

parentSpan();
```

#### TypeScript实现1

```typescript
import { trace, Span } from '@opentelemetry/api';

const tracer = trace.getTracer('example-service');

function parentSpan(): void {
    const parent = tracer.startSpan('parent-operation');

    try {
        childSpan();
    } finally {
        parent.end();
    }
}

function childSpan(): void {
    const child = tracer.startSpan('child-operation');

    try {
        console.log('Child operation');
    } finally {
        child.end();
    }
}

parentSpan();
```

### 1.3 异步Span处理

#### Node.js实现2

```javascript
const { trace } = require('@opentelemetry/api');

const tracer = trace.getTracer('example-service');

async function asyncOperation() {
    const span = tracer.startSpan('async-operation');

    try {
        // 异步操作
        const result = await fetch('https://api.example.com/data');
        const data = await result.json();

        span.setAttributes({
            'http.status_code': result.status,
            'data.size': JSON.stringify(data).length
        });

        return data;
    } catch (error) {
        span.recordException(error);
        span.setStatus({ code: 2, message: error.message });
        throw error;
    } finally {
        span.end();
    }
}

// 使用
asyncOperation()
    .then(data => console.log('Success:', data))
    .catch(error => console.error('Error:', error));
```

#### TypeScript实现2

```typescript
import { trace, Span, SpanStatusCode } from '@opentelemetry/api';

const tracer = trace.getTracer('example-service');

async function asyncOperation(): Promise<any> {
    const span = tracer.startSpan('async-operation');

    try {
        const result = await fetch('https://api.example.com/data');
        const data = await result.json();

        span.setAttributes({
            'http.status_code': result.status,
            'data.size': JSON.stringify(data).length
        });

        return data;
    } catch (error) {
        span.recordException(error as Error);
        span.setStatus({
            code: SpanStatusCode.ERROR,
            message: (error as Error).message
        });
        throw error;
    } finally {
        span.end();
    }
}

asyncOperation()
    .then(data => console.log('Success:', data))
    .catch(error => console.error('Error:', error));
```

---

## 2. Metrics - JavaScript实现

### 2.1 Counter指标

#### Node.js实现3

```javascript
const { metrics } = require('@opentelemetry/api');

const meter = metrics.getMeter('example-service');

// 创建Counter
const counter = meter.createCounter('http_requests_total', {
    description: 'Total number of HTTP requests'
});

// 增加计数
function incrementCounter(method, status) {
    counter.add(1, {
        method: method,
        status: status
    });
}

// 使用
incrementCounter('GET', '200');
incrementCounter('POST', '201');
```

#### TypeScript实现3

```typescript
import { metrics, Counter } from '@opentelemetry/api';

const meter = metrics.getMeter('example-service');

const counter: Counter = meter.createCounter('http_requests_total', {
    description: 'Total number of HTTP requests'
});

function incrementCounter(method: string, status: string): void {
    counter.add(1, {
        method,
        status
    });
}

incrementCounter('GET', '200');
incrementCounter('POST', '201');
```

### 2.2 Histogram指标

#### Node.js实现4

```javascript
const { metrics } = require('@opentelemetry/api');

const meter = metrics.getMeter('example-service');

// 创建Histogram
const histogram = meter.createHistogram('http_request_duration_ms', {
    description: 'HTTP request duration in milliseconds'
});

// 记录值
function recordDuration(method, endpoint, duration) {
    histogram.record(duration, {
        method: method,
        endpoint: endpoint
    });
}

// 使用
recordDuration('GET', '/api/users', 150);
recordDuration('POST', '/api/orders', 320);
```

#### TypeScript实现4

```typescript
import { metrics, Histogram } from '@opentelemetry/api';

const meter = metrics.getMeter('example-service');

const histogram: Histogram = meter.createHistogram('http_request_duration_ms', {
    description: 'HTTP request duration in milliseconds'
});

function recordDuration(method: string, endpoint: string, duration: number): void {
    histogram.record(duration, {
        method,
        endpoint
    });
}

recordDuration('GET', '/api/users', 150);
recordDuration('POST', '/api/orders', 320);
```

### 2.3 Gauge指标

#### Node.js实现5

```javascript
const { metrics } = require('@opentelemetry/api');

const meter = metrics.getMeter('example-service');

// 创建Gauge
const gauge = meter.createObservableGauge('memory_usage_bytes', {
    description: 'Memory usage in bytes'
});

// 注册回调
meter.addBatchObservableCallback(() => {
    const memoryUsage = process.memoryUsage();

    gauge.observe(memoryUsage.heapUsed, {
        type: 'heap'
    });
});

console.log('Gauge registered');
```

#### TypeScript实现5

```typescript
import { metrics, ObservableGauge } from '@opentelemetry/api';

const meter = metrics.getMeter('example-service');

const gauge: ObservableGauge = meter.createObservableGauge('memory_usage_bytes', {
    description: 'Memory usage in bytes'
});

meter.addBatchObservableCallback(() => {
    const memoryUsage = process.memoryUsage();

    gauge.observe(memoryUsage.heapUsed, {
        type: 'heap'
    });
});

console.log('Gauge registered');
```

---

## 3. Logs - JavaScript实现

### 3.1 记录日志

#### Node.js实现6

```javascript
const { logs } = require('@opentelemetry/api');

const logger = logs.getLogger('example-service');

// 记录INFO日志
function logInfo(message, attributes) {
    logger.emit({
        severityNumber: 9, // INFO
        severityText: 'INFO',
        body: message,
        attributes: attributes
    });
}

// 记录ERROR日志
function logError(message, error, attributes) {
    logger.emit({
        severityNumber: 17, // ERROR
        severityText: 'ERROR',
        body: message,
        attributes: {
            ...attributes,
            'error.type': error.name,
            'error.message': error.message,
            'error.stack': error.stack
        }
    });
}

// 使用
logInfo('User logged in', {
    user_id: '12345',
    ip_address: '192.168.1.1'
});

try {
    throw new Error('Something went wrong');
} catch (error) {
    logError('Operation failed', error, {
        operation: 'process-payment'
    });
}
```

#### TypeScript实现6

```typescript
import { logs, SeverityNumber, LogRecord } from '@opentelemetry/api';

const logger = logs.getLogger('example-service');

function logInfo(message: string, attributes: Record<string, any>): void {
    logger.emit({
        severityNumber: SeverityNumber.INFO,
        severityText: 'INFO',
        body: message,
        attributes
    });
}

function logError(
    message: string,
    error: Error,
    attributes: Record<string, any>
): void {
    logger.emit({
        severityNumber: SeverityNumber.ERROR,
        severityText: 'ERROR',
        body: message,
        attributes: {
            ...attributes,
            'error.type': error.name,
            'error.message': error.message,
            'error.stack': error.stack
        }
    });
}

logInfo('User logged in', {
    user_id: '12345',
    ip_address: '192.168.1.1'
});

try {
    throw new Error('Something went wrong');
} catch (error) {
    logError('Operation failed', error as Error, {
        operation: 'process-payment'
    });
}
```

---

## 4. Express集成示例

### 4.1 Express中间件

#### Node.js实现7

```javascript
const express = require('express');
const { trace } = require('@opentelemetry/api');

const app = express();
const tracer = trace.getTracer('express-app');

// 追踪中间件
function tracingMiddleware(req, res, next) {
    const span = tracer.startSpan(`${req.method} ${req.path}`);

    // 设置属性
    span.setAttributes({
        'http.method': req.method,
        'http.url': req.url,
        'http.route': req.route?.path || req.path
    });

    // 在响应结束时结束Span
    res.on('finish', () => {
        span.setAttributes({
            'http.status_code': res.statusCode
        });

        if (res.statusCode >= 400) {
            span.setStatus({ code: 2, message: 'HTTP Error' });
        }

        span.end();
    });

    next();
}

// 使用中间件
app.use(tracingMiddleware);

// 路由
app.get('/api/users', (req, res) => {
    res.json({ users: [] });
});

app.listen(3000, () => {
    console.log('Server running on port 3000');
});
```

#### TypeScript实现7

```typescript
import express, { Request, Response, NextFunction } from 'express';
import { trace, Span } from '@opentelemetry/api';

const app = express();
const tracer = trace.getTracer('express-app');

function tracingMiddleware(req: Request, res: Response, next: NextFunction): void {
    const span: Span = tracer.startSpan(`${req.method} ${req.path}`);

    span.setAttributes({
        'http.method': req.method,
        'http.url': req.url,
        'http.route': req.route?.path || req.path
    });

    res.on('finish', () => {
        span.setAttributes({
            'http.status_code': res.statusCode
        });

        if (res.statusCode >= 400) {
            span.setStatus({ code: 2, message: 'HTTP Error' });
        }

        span.end();
    });

    next();
}

app.use(tracingMiddleware);

app.get('/api/users', (req: Request, res: Response) => {
    res.json({ users: [] });
});

app.listen(3000, () => {
    console.log('Server running on port 3000');
});
```

---

## 5. 浏览器端追踪

### 5.1 浏览器端实现

#### JavaScript实现

```javascript
// 浏览器端OpenTelemetry设置
const { trace, metrics } = require('@opentelemetry/api');

const tracer = trace.getTracer('web-app');

// 追踪用户交互
function trackUserInteraction(action, details) {
    const span = tracer.startSpan('user-interaction');

    span.setAttributes({
        'user.action': action,
        'user.details': JSON.stringify(details),
        'user.agent': navigator.userAgent,
        'user.url': window.location.href
    });

    span.end();
}

// 追踪页面加载
function trackPageLoad() {
    const span = tracer.startSpan('page-load');

    window.addEventListener('load', () => {
        const loadTime = performance.now();

        span.setAttributes({
            'page.load_time': loadTime,
            'page.url': window.location.href,
            'page.referrer': document.referrer
        });

        span.end();
    });
}

// 追踪AJAX请求
function trackAjaxRequest(url, method) {
    const span = tracer.startSpan('ajax-request');

    span.setAttributes({
        'http.method': method,
        'http.url': url
    });

    fetch(url, { method })
        .then(response => {
            span.setAttributes({
                'http.status_code': response.status
            });
            span.end();
            return response.json();
        })
        .catch(error => {
            span.recordException(error);
            span.setStatus({ code: 2, message: error.message });
            span.end();
        });
}

// 使用
trackPageLoad();
trackUserInteraction('click', { button: 'submit' });
trackAjaxRequest('/api/data', 'GET');
```

#### TypeScript实现8

```typescript
import { trace, Span } from '@opentelemetry/api';

const tracer = trace.getTracer('web-app');

function trackUserInteraction(action: string, details: Record<string, any>): void {
    const span: Span = tracer.startSpan('user-interaction');

    span.setAttributes({
        'user.action': action,
        'user.details': JSON.stringify(details),
        'user.agent': navigator.userAgent,
        'user.url': window.location.href
    });

    span.end();
}

function trackPageLoad(): void {
    const span: Span = tracer.startSpan('page-load');

    window.addEventListener('load', () => {
        const loadTime = performance.now();

        span.setAttributes({
            'page.load_time': loadTime,
            'page.url': window.location.href,
            'page.referrer': document.referrer
        });

        span.end();
    });
}

function trackAjaxRequest(url: string, method: string): void {
    const span: Span = tracer.startSpan('ajax-request');

    span.setAttributes({
        'http.method': method,
        'http.url': url
    });

    fetch(url, { method })
        .then(response => {
            span.setAttributes({
                'http.status_code': response.status
            });
            span.end();
            return response.json();
        })
        .catch(error => {
            span.recordException(error);
            span.setStatus({ code: 2, message: error.message });
            span.end();
        });
}

trackPageLoad();
trackUserInteraction('click', { button: 'submit' });
trackAjaxRequest('/api/data', 'GET');
```

---

## 6. Serverless函数示例

### 6.1 AWS Lambda函数

#### Node.js实现8

```javascript
const { trace } = require('@opentelemetry/api');

const tracer = trace.getTracer('lambda-function');

exports.handler = async (event, context) => {
    const span = tracer.startSpan('lambda-handler');

    try {
        span.setAttributes({
            'lambda.function_name': context.functionName,
            'lambda.request_id': context.requestId,
            'lambda.memory_limit': context.memoryLimitInMB
        });

        // 处理业务逻辑
        const result = await processEvent(event);

        span.setStatus({ code: 1 });
        span.end();

        return {
            statusCode: 200,
            body: JSON.stringify(result)
        };
    } catch (error) {
        span.recordException(error);
        span.setStatus({ code: 2, message: error.message });
        span.end();

        return {
            statusCode: 500,
            body: JSON.stringify({ error: error.message })
        };
    }
};

async function processEvent(event) {
    const span = tracer.startSpan('process-event');

    try {
        // 处理事件
        return { processed: true };
    } finally {
        span.end();
    }
}
```

#### TypeScript实现9

```typescript
import { trace, Span } from '@opentelemetry/api';
import { Context, APIGatewayProxyEvent, APIGatewayProxyResult } from 'aws-lambda';

const tracer = trace.getTracer('lambda-function');

export const handler = async (
    event: APIGatewayProxyEvent,
    context: Context
): Promise<APIGatewayProxyResult> => {
    const span: Span = tracer.startSpan('lambda-handler');

    try {
        span.setAttributes({
            'lambda.function_name': context.functionName,
            'lambda.request_id': context.requestId,
            'lambda.memory_limit': context.memoryLimitInMB
        });

        const result = await processEvent(event);

        span.setStatus({ code: 1 });
        span.end();

        return {
            statusCode: 200,
            body: JSON.stringify(result)
        };
    } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: 2, message: (error as Error).message });
        span.end();

        return {
            statusCode: 500,
            body: JSON.stringify({ error: (error as Error).message })
        };
    }
};

async function processEvent(event: APIGatewayProxyEvent): Promise<any> {
    const span: Span = tracer.startSpan('process-event');

    try {
        return { processed: true };
    } finally {
        span.end();
    }
}
```

---

## 7. 最佳实践

### 7.1 性能优化

```text
性能优化最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 使用批量导出减少网络开销                     │
│  ✅ 合理设置采样率避免性能影响                   │
│  ✅ 异步处理避免阻塞主线程                       │
│  ✅ 缓存常用属性减少内存分配                     │
│  ✅ 避免在热点路径中创建过多Span                 │
└─────────────────────────────────────────────────┘
```

### 7.2 错误处理

```text
错误处理最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 使用try-catch捕获异常                        │
│  ✅ 记录异常到Span                               │
│  ✅ 设置适当的Span状态                           │
│  ✅ 避免记录敏感信息                             │
│  ✅ 提供有意义的错误消息                         │
└─────────────────────────────────────────────────┘
```

### 7.3 安全考虑

```text
安全考虑最佳实践:
┌─────────────────────────────────────────────────┐
│  ✅ 避免记录敏感信息（密码、令牌等）             │
│  ✅ 使用数据脱敏处理用户输入                     │
│  ✅ 限制Span属性的数量和大小                     │
│  ✅ 使用HTTPS传输追踪数据                       │
│  ✅ 实现访问控制和认证                           │
└─────────────────────────────────────────────────┘
```

---

## 8. 总结

### 8.1 核心要点

```text
JavaScript/TypeScript支持核心要点:
┌─────────────────────────────────────────────────┐
│  1. 平台支持                                    │
│     - Node.js后端服务                           │
│     - 浏览器前端应用                            │
│     - Serverless函数                            │
│                                                 │
│  2. 框架集成                                    │
│     - Express/Fastify                           │
│     - React/Vue                                │
│     - AWS Lambda                               │
│                                                 │
│  3. 类型安全                                    │
│     - TypeScript类型定义                        │
│     - 编译时检查                                │
│     - IDE智能提示                               │
│                                                 │
│  4. 性能优化                                    │
│     - 批量导出                                  │
│     - 异步处理                                  │
│     - 采样策略                                  │
└─────────────────────────────────────────────────┘
```

### 8.2 适用场景

```text
适用场景:
┌─────────────────────────────────────────────────┐
│  场景          │ 推荐方案                         │
├─────────────────────────────────────────────────┤
│  Web后端      │ Express + Node.js               │
│  前端应用      │ React + TypeScript              │
│  微服务        │ Node.js + gRPC                 │
│  Serverless    │ AWS Lambda                      │
│  实时应用      │ WebSocket + Node.js             │
└─────────────────────────────────────────────────┘
```

---

**最后更新**: 2025年10月11日
**维护者**: OTLP深度梳理团队
**版本**: 1.0.0
