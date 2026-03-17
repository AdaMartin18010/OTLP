---
title: JavaScript SDK完整实战指南
description: OpenTelemetry JavaScript SDK的完整实战指南，包含Node.js/浏览器、Express/NestJS集成等
version: Node.js 16+ / OTel JS v1.19.0
date: 2026-03-17
author: OTLP项目团队
category: SDK指南
tags:
  - javascript
  - nodejs
  - browser
  - express
  - nestjs
  - sdk
  - otlp
  - opentelemetry
status: published
---

# JavaScript SDK完整实战指南

> **版本**: Node.js 16+ / OpenTelemetry JavaScript v1.19.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约40分钟

---

## 1. 环境准备

### 1.1 安装依赖

```bash
# 基础SDK
npm install @opentelemetry/api @opentelemetry/sdk-node @opentelemetry/core

# OTLP导出器
npm install @opentelemetry/exporter-trace-otlp-grpc
npm install @opentelemetry/exporter-trace-otlp-http
npm install @opentelemetry/exporter-metrics-otlp-grpc
npm install @opentelemetry/exporter-metrics-otlp-http

# 自动Instrumentation
npm install @opentelemetry/auto-instrumentations-node

# 框架特定Instrumentation
npm install @opentelemetry/instrumentation-express
npm install @opentelemetry/instrumentation-http
npm install @opentelemetry/instrumentation-https
npm install @opentelemetry/instrumentation-fs
npm install @opentelemetry/instrumentation-net
npm install @opentelemetry/instrumentation-dns

# 数据库Instrumentation
npm install @opentelemetry/instrumentation-mongodb
npm install @opentelemetry/instrumentation-mysql
npm install @opentelemetry/instrumentation-pg
npm install @opentelemetry/instrumentation-redis
npm install @opentelemetry/instrumentation-ioredis

# 消息队列Instrumentation
npm install @opentelemetry/instrumentation-amqplib
npm install @opentelemetry/instrumentation-kafkajs

# 其他工具
npm install @opentelemetry/instrumentation-winston
npm install @opentelemetry/resources
npm install @opentelemetry/semantic-conventions

# 浏览器SDK（如果是前端应用）
npm install @opentelemetry/sdk-trace-web
npm install @opentelemetry/context-zone
npm install @opentelemetry/instrumentation-document-load
npm install @opentelemetry/instrumentation-fetch
npm install @opentelemetry/instrumentation-xml-http-request
npm install @opentelemetry/exporter-trace-otlp-http
```

### 1.2 package.json示例

```json
{
  "name": "my-otel-service",
  "version": "1.0.0",
  "description": "OpenTelemetry instrumented service",
  "main": "src/index.js",
  "scripts": {
    "start": "node src/index.js",
    "start:otel": "node --require ./src/telemetry.js src/index.js",
    "dev": "nodemon --require ./src/telemetry.js src/index.js",
    "test": "jest"
  },
  "dependencies": {
    "@opentelemetry/api": "^1.7.0",
    "@opentelemetry/sdk-node": "^0.45.0",
    "@opentelemetry/auto-instrumentations-node": "^0.40.0",
    "express": "^4.18.2"
  },
  "devDependencies": {
    "nodemon": "^3.0.2"
  }
}
```

### 1.3 项目结构

```
myapp/
├── src/
│   ├── telemetry.js          # 遥测配置入口
│   ├── config/
│   │   └── tracing.js        # 链路追踪配置
│   │   └── metrics.js        # 指标配置
│   ├── controllers/
│   │   └── orderController.js
│   ├── services/
│   │   └── orderService.js
│   ├── routes/
│   │   └── index.js
│   ├── middleware/
│   │   └── tracing.js        # 自定义追踪中间件
│   └── index.js              # 应用入口
├── public/                   # 前端资源（浏览器SDK）
│   └── otel.js
├── tests/
│   └── telemetry.test.js
├── package.json
└── Dockerfile
```

---

## 2. 基础配置

### 2.1 Node.js程序化配置

```javascript
// src/telemetry.js

'use strict';

const { NodeSDK } = require('@opentelemetry/sdk-node');
const { getNodeAutoInstrumentations } = require('@opentelemetry/auto-instrumentations-node');
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');
const { OTLPMetricExporter } = require('@opentelemetry/exporter-metrics-otlp-grpc');
const { PeriodicExportingMetricReader } = require('@opentelemetry/sdk-metrics');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');
const { diag, DiagConsoleLogger, DiagLogLevel } = require('@opentelemetry/api');

// 配置诊断日志（开发环境使用）
if (process.env.NODE_ENV === 'development') {
  diag.setLogger(new DiagConsoleLogger(), DiagLogLevel.DEBUG);
}

// 创建资源属性
const resource = Resource.default().merge(
  new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: process.env.OTEL_SERVICE_NAME || 'nodejs-service',
    [SemanticResourceAttributes.SERVICE_VERSION]: process.env.OTEL_SERVICE_VERSION || '1.0.0',
    [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: process.env.NODE_ENV || 'development',
    'host.name': require('os').hostname(),
    'process.runtime.name': 'nodejs',
    'process.runtime.version': process.version,
  })
);

// 创建Trace导出器
const traceExporter = new OTLPTraceExporter({
  url: process.env.OTEL_EXPORTER_OTLP_TRACES_ENDPOINT || 'http://localhost:4317',
  credentials: process.env.OTEL_EXPORTER_OTLP_INSECURE === 'true'
    ? require('@grpc/grpc-js').credentials.createInsecure()
    : undefined,
});

// 创建Metrics导出器
const metricExporter = new OTLPMetricExporter({
  url: process.env.OTEL_EXPORTER_OTLP_METRICS_ENDPOINT || 'http://localhost:4317',
});

// 创建Metric Reader
const metricReader = new PeriodicExportingMetricReader({
  exporter: metricExporter,
  exportIntervalMillis: parseInt(process.env.OTEL_METRIC_EXPORT_INTERVAL) || 60000,
});

// 初始化SDK
const sdk = new NodeSDK({
  traceExporter,
  metricReader,
  instrumentations: [
    getNodeAutoInstrumentations({
      // 配置特定Instrumentation
      '@opentelemetry/instrumentation-fs': {
        enabled: false, // 关闭文件系统追踪以减少噪音
      },
      '@opentelemetry/instrumentation-http': {
        enabled: true,
        applyCustomAttributesOnSpan: (span, request, response) => {
          span.setAttribute('http.custom.attribute', 'value');
        },
      },
    }),
  ],
  resource,
});

// 启动SDK
sdk.start();
console.log('OpenTelemetry SDK initialized');

// 优雅关闭
process.on('SIGTERM', async () => {
  console.log('SIGTERM received, shutting down OpenTelemetry SDK...');
  try {
    await sdk.shutdown();
    console.log('OpenTelemetry SDK shut down successfully');
  } catch (err) {
    console.error('Error shutting down OpenTelemetry SDK:', err);
  } finally {
    process.exit(0);
  }
});

module.exports = { sdk };
```

### 2.2 模块化配置方式

```javascript
// src/config/tracing.js

'use strict';

const { NodeTracerProvider, BatchSpanProcessor } = require('@opentelemetry/sdk-trace-node');
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');
const { trace } = require('@opentelemetry/api');

class TracingConfig {
  constructor(options = {}) {
    this.serviceName = options.serviceName || process.env.OTEL_SERVICE_NAME || 'nodejs-service';
    this.serviceVersion = options.serviceVersion || process.env.OTEL_SERVICE_VERSION || '1.0.0';
    this.endpoint = options.endpoint || process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'http://localhost:4317';
    this.samplerRatio = options.samplerRatio || parseFloat(process.env.OTEL_TRACES_SAMPLER_RATIO) || 1.0;

    this.provider = null;
    this.tracer = null;
  }

  init() {
    // 创建资源
    const resource = new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: this.serviceName,
      [SemanticResourceAttributes.SERVICE_VERSION]: this.serviceVersion,
      [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: process.env.NODE_ENV || 'development',
    });

    // 创建导出器
    const exporter = new OTLPTraceExporter({
      url: this.endpoint,
    });

    // 创建Provider
    this.provider = new NodeTracerProvider({
      resource,
      spanProcessors: [
        new BatchSpanProcessor(exporter, {
          maxQueueSize: 2048,
          maxExportBatchSize: 512,
          scheduledDelayMillis: 5000,
          exportTimeoutMillis: 30000,
        }),
      ],
    });

    // 注册为全局Provider
    this.provider.register();

    // 获取Tracer
    this.tracer = trace.getTracer(this.serviceName, this.serviceVersion);

    console.log(`Tracing initialized for service: ${this.serviceName}`);
    return this;
  }

  getTracer(name, version) {
    return trace.getTracer(name || this.serviceName, version || this.serviceVersion);
  }

  shutdown() {
    if (this.provider) {
      return this.provider.shutdown();
    }
    return Promise.resolve();
  }
}

module.exports = { TracingConfig };
```

```javascript
// src/config/metrics.js

'use strict';

const { MeterProvider, PeriodicExportingMetricReader } = require('@opentelemetry/sdk-metrics');
const { OTLPMetricExporter } = require('@opentelemetry/exporter-metrics-otlp-grpc');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');
const { metrics } = require('@opentelemetry/api');

class MetricsConfig {
  constructor(options = {}) {
    this.serviceName = options.serviceName || process.env.OTEL_SERVICE_NAME || 'nodejs-service';
    this.serviceVersion = options.serviceVersion || process.env.OTEL_SERVICE_VERSION || '1.0.0';
    this.endpoint = options.endpoint || process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'http://localhost:4317';
    this.exportInterval = options.exportInterval || 60000;

    this.provider = null;
    this.meter = null;
  }

  init() {
    // 创建资源
    const resource = new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: this.serviceName,
      [SemanticResourceAttributes.SERVICE_VERSION]: this.serviceVersion,
    });

    // 创建导出器
    const exporter = new OTLPMetricExporter({
      url: this.endpoint,
    });

    // 创建Reader
    const reader = new PeriodicExportingMetricReader({
      exporter,
      exportIntervalMillis: this.exportInterval,
    });

    // 创建Provider
    this.provider = new MeterProvider({
      resource,
      readers: [reader],
    });

    // 设置为全局Provider
    metrics.setGlobalMeterProvider(this.provider);

    // 获取Meter
    this.meter = metrics.getMeter(this.serviceName, this.serviceVersion);

    console.log(`Metrics initialized for service: ${this.serviceName}`);
    return this;
  }

  getMeter(name, version) {
    return metrics.getMeter(name || this.serviceName, version || this.serviceVersion);
  }

  shutdown() {
    if (this.provider) {
      return this.provider.shutdown();
    }
    return Promise.resolve();
  }
}

module.exports = { MetricsConfig };
```

### 2.3 自动注入（零代码方式）

```bash
# 使用 --require 参数启动
node --require ./src/telemetry.js src/index.js

# 或使用环境变量
export OTEL_SERVICE_NAME=order-service
export OTEL_SERVICE_VERSION=1.0.0
export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
export OTEL_TRACES_EXPORTER=otlp
export OTEL_METRICS_EXPORTER=otlp
export OTEL_LOGS_EXPORTER=otlp
export OTEL_NODE_RESOURCE_DETECTORS=env,host,os,process
export OTEL_INSTRUMENTATION_HTTP_ENABLED=true
export NODE_OPTIONS="--require @opentelemetry/auto-instrumentations-node/register"

node src/index.js
```

---

## 3. 核心使用示例

### 3.1 创建Span

```javascript
// src/services/orderService.js

'use strict';

const { trace, SpanStatusCode } = require('@opentelemetry/api');
const { TracingConfig } = require('../config/tracing');

// 初始化追踪
const tracing = new TracingConfig().init();
const tracer = tracing.getTracer('order-service');

class OrderService {
  /**
   * 创建订单
   */
  async createOrder(userId, amount) {
    // 方式1: 使用 startActiveSpan 自动管理上下文
    return tracer.startActiveSpan('order.create', {
      attributes: {
        'order.user_id': userId,
        'order.amount': amount,
      },
    }, async (span) => {
      try {
        // 记录事件
        span.addEvent('Order validation started');
        await this.validateOrder(userId, amount);
        span.addEvent('Order validation completed');

        // 生成订单ID
        const orderId = `ORD-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
        span.setAttribute('order.id', orderId);

        // 处理支付
        span.addEvent('Payment processing started');
        const paymentSuccess = await this.processPayment(orderId, amount);

        if (!paymentSuccess) {
          throw new Error('Payment processing failed');
        }

        span.addEvent('Payment completed', {
          'payment.transaction_id': `txn_${orderId}`,
          'payment.amount': amount,
        });

        // 设置成功状态
        span.setStatus({ code: SpanStatusCode.OK });

        return {
          orderId,
          userId,
          amount,
          status: 'created',
        };

      } catch (error) {
        // 记录异常
        span.recordException(error);
        span.setStatus({
          code: SpanStatusCode.ERROR,
          message: error.message,
        });
        throw error;
      } finally {
        // 结束Span
        span.end();
      }
    });
  }

  /**
   * 验证订单 - 嵌套Span
   */
  async validateOrder(userId, amount) {
    return tracer.startActiveSpan('order.validate', async (span) => {
      span.setAttribute('validation.user_id', userId);

      if (amount <= 0) {
        span.setStatus({
          code: SpanStatusCode.ERROR,
          message: 'Invalid amount',
        });
        throw new Error('Amount must be greater than 0');
      }

      span.setAttribute('validation.passed', true);
      await new Promise(resolve => setTimeout(resolve, 10));

      span.end();
    });
  }

  /**
   * 处理支付
   */
  async processPayment(orderId, amount) {
    return tracer.startActiveSpan('payment.process', async (span) => {
      span.setAttribute('payment.order_id', orderId);
      span.setAttribute('payment.amount', amount);
      span.setAttribute('payment.gateway', 'stripe');

      // 模拟支付处理
      await new Promise(resolve => setTimeout(resolve, 50));

      span.addEvent('Payment processed successfully');
      span.end();

      return true;
    });
  }

  /**
   * 获取订单详情
   */
  async getOrder(orderId) {
    // 方式2: 使用 startSpan 手动管理上下文
    const span = tracer.startSpan('order.get', {
      attributes: { 'order.id': orderId },
    });

    try {
      // 模拟数据库查询
      await new Promise(resolve => setTimeout(resolve, 20));

      const order = {
        orderId,
        userId: 'user123',
        amount: 99.99,
        status: 'completed',
      };

      span.setAttribute('order.found', true);
      span.setAttribute('order.status', order.status);
      span.setStatus({ code: SpanStatusCode.OK });

      return order;

    } catch (error) {
      span.recordException(error);
      span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
      throw error;
    } finally {
      span.end();
    }
  }

  /**
   * 批量处理订单 - 创建父Span和多个子Span
   */
  async processBulkOrders(orderIds) {
    return tracer.startActiveSpan('order.bulk_process', {
      attributes: { 'order.count': orderIds.length },
    }, async (parentSpan) => {
      const results = [];

      for (const orderId of orderIds) {
        // 创建子Span
        const childSpan = tracer.startSpan('order.process_single', {
          parent: parentSpan,
          attributes: { 'order.id': orderId },
        });

        try {
          const result = await this.getOrder(orderId);
          childSpan.setAttribute('order.status', result.status);
          childSpan.setStatus({ code: SpanStatusCode.OK });
          results.push(result);
        } catch (error) {
          childSpan.recordException(error);
          childSpan.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
        } finally {
          childSpan.end();
        }
      }

      parentSpan.setAttribute('order.processed_count', results.length);
      parentSpan.setStatus({ code: SpanStatusCode.OK });

      return results;
    });
  }
}

module.exports = { OrderService };
```

### 3.2 记录指标

```javascript
// src/metrics/orderMetrics.js

'use strict';

const { metrics } = require('@opentelemetry/api');
const { MetricsConfig } = require('../config/metrics');

// 初始化指标
const metricsConfig = new MetricsConfig().init();
const meter = metricsConfig.getMeter('order-service');

// 创建计数器
const orderCounter = meter.createCounter('orders.total', {
  description: 'Total number of orders',
  unit: '1',
});

const orderErrorCounter = meter.createCounter('orders.errors', {
  description: 'Total number of order errors',
  unit: '1',
});

// 创建直方图
const orderValueHistogram = meter.createHistogram('order.value', {
  description: 'Order value distribution',
  unit: 'USD',
});

const orderProcessingTime = meter.createHistogram('order.processing.duration', {
  description: 'Order processing time',
  unit: 'ms',
});

// 创建Observable Gauge
let queueSize = 0;
const queueSizeGauge = meter.createObservableGauge('queue.size', {
  description: 'Current queue size',
  unit: '1',
}, (observableResult) => {
  observableResult.observe(queueSize);
});

// 创建UpDownCounter
const activeConnections = meter.createUpDownCounter('connections.active', {
  description: 'Number of active connections',
  unit: '1',
});

class OrderMetrics {
  /**
   * 记录订单创建
   */
  static recordOrderCreated(amount, status = 'success') {
    orderCounter.add(1, {
      status,
      service: 'order-service',
    });
    orderValueHistogram.record(amount, {
      currency: 'USD',
    });
  }

  /**
   * 记录订单错误
   */
  static recordOrderError(errorType) {
    orderErrorCounter.add(1, {
      'error.type': errorType,
    });
  }

  /**
   * 记录处理时间
   */
  static recordProcessingTime(durationMs, method) {
    orderProcessingTime.record(durationMs, {
      method,
    });
  }

  /**
   * 增加活动连接数
   */
  static incrementActiveConnections() {
    activeConnections.add(1);
  }

  /**
   * 减少活动连接数
   */
  static decrementActiveConnections() {
    activeConnections.add(-1);
  }

  /**
   * 更新队列大小
   */
  static updateQueueSize(size) {
    queueSize = size;
  }
}

module.exports = { OrderMetrics };
```

---

## 4. 框架集成

### 4.1 Express集成

```javascript
// src/app.js

'use strict';

const express = require('express');
const { trace } = require('@opentelemetry/api');

// 必须先初始化遥测
require('./telemetry');

const { OrderService } = require('./services/orderService');
const { OrderMetrics } = require('./metrics/orderMetrics');

const app = express();
app.use(express.json());

const orderService = new OrderService();
const tracer = trace.getTracer('express-app');

// 健康检查（不追踪）
app.get('/health', (req, res) => {
  res.json({ status: 'healthy' });
});

// 创建订单
app.post('/api/orders', async (req, res) => {
  const startTime = Date.now();
  OrderMetrics.incrementActiveConnections();

  try {
    const { userId, amount } = req.body;

    if (!userId || amount === undefined) {
      return res.status(400).json({ error: 'Missing required fields' });
    }

    // 手动创建Span添加额外属性
    const span = trace.getActiveSpan();
    if (span) {
      span.setAttribute('http.request.body_size', JSON.stringify(req.body).length);
    }

    const result = await orderService.createOrder(userId, amount);
    OrderMetrics.recordOrderCreated(amount);

    res.status(201).json(result);

  } catch (error) {
    OrderMetrics.recordOrderError(error.name);
    res.status(500).json({ error: error.message });
  } finally {
    OrderMetrics.decrementActiveConnections();
    const duration = Date.now() - startTime;
    OrderMetrics.recordProcessingTime(duration, 'POST /api/orders');
  }
});

// 获取订单
app.get('/api/orders/:orderId', async (req, res) => {
  try {
    const { orderId } = req.params;
    const result = await orderService.getOrder(orderId);
    res.json(result);
  } catch (error) {
    res.status(404).json({ error: 'Order not found' });
  }
});

// 批量处理订单
app.post('/api/orders/bulk', async (req, res) => {
  try {
    const { orderIds } = req.body;
    const results = await orderService.processBulkOrders(orderIds);
    res.json({ results, count: results.length });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// 调用下游服务示例 - 传播Trace上下文
app.get('/api/call-downstream', async (req, res) => {
  const axios = require('axios');
  const { context, propagation } = require('@opentelemetry/api');

  return tracer.startActiveSpan('call.downstream', async (span) => {
    try {
      // 获取当前上下文并注入到请求头
      const headers = {};
      propagation.inject(context.active(), headers);

      span.setAttribute('downstream.url', 'http://downstream-service/api/data');

      const response = await axios.get('http://downstream-service/api/data', {
        headers,
        timeout: 5000,
      });

      span.setAttribute('downstream.status_code', response.status);
      span.setStatus({ code: trace.SpanStatusCode.OK });

      res.json({ downstreamResponse: response.data });

    } catch (error) {
      span.recordException(error);
      span.setStatus({ code: trace.SpanStatusCode.ERROR, message: error.message });
      res.status(500).json({ error: error.message });
    } finally {
      span.end();
    }
  });
});

// 错误处理中间件
app.use((err, req, res, next) => {
  const span = trace.getActiveSpan();
  if (span) {
    span.recordException(err);
    span.setStatus({ code: trace.SpanStatusCode.ERROR, message: err.message });
  }
  res.status(500).json({ error: err.message });
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});

module.exports = { app };
```

### 4.2 NestJS集成

```typescript
// src/telemetry.ts

import { NodeSDK } from '@opentelemetry/sdk-node';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';

const resource = Resource.default().merge(
  new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: process.env.OTEL_SERVICE_NAME || 'nestjs-service',
    [SemanticResourceAttributes.SERVICE_VERSION]: process.env.OTEL_SERVICE_VERSION || '1.0.0',
  }),
);

export const otelSDK = new NodeSDK({
  traceExporter: new OTLPTraceExporter(),
  instrumentations: [getNodeAutoInstrumentations()],
  resource,
});

// 启动SDK
otelSDK.start();

// 优雅关闭
process.on('SIGTERM', () => {
  otelSDK.shutdown()
    .then(() => console.log('OpenTelemetry SDK shut down'))
    .catch((err) => console.error('Error shutting down OpenTelemetry SDK', err))
    .finally(() => process.exit(0));
});
```

```typescript
// src/main.ts

import { NestFactory } from '@nestjs/core';
import { AppModule } from './app.module';

// 必须先加载telemetry
import './telemetry';

async function bootstrap() {
  const app = await NestFactory.create(AppModule);
  await app.listen(3000);
}
bootstrap();
```

```typescript
// src/orders/orders.controller.ts

import { Controller, Get, Post, Body, Param } from '@nestjs/common';
import { Trace, Span } from 'nestjs-otel';
import { OrdersService } from './orders.service';
import { CreateOrderDto } from './dto/create-order.dto';

@Controller('orders')
export class OrdersController {
  constructor(private readonly ordersService: OrdersService) {}

  @Post()
  @Span('OrdersController.createOrder')
  async create(@Body() createOrderDto: CreateOrderDto) {
    return this.ordersService.create(createOrderDto);
  }

  @Get(':id')
  @Span('OrdersController.getOrder')
  async findOne(@Param('id') id: string) {
    return this.ordersService.findOne(id);
  }
}
```

```typescript
// src/orders/orders.service.ts

import { Injectable } from '@nestjs/common';
import { Span, TraceService } from 'nestjs-otel';
import { CreateOrderDto } from './dto/create-order.dto';

@Injectable()
export class OrdersService {
  constructor(private readonly traceService: TraceService) {}

  @Span('OrdersService.create')
  async create(createOrderDto: CreateOrderDto) {
    const span = this.traceService.getSpan();

    span?.setAttribute('order.user_id', createOrderDto.userId);
    span?.setAttribute('order.amount', createOrderDto.amount);

    // 业务逻辑...
    const orderId = `ORD-${Date.now()}`;

    span?.addEvent('Order created', { orderId });

    return {
      orderId,
      ...createOrderDto,
      status: 'created',
    };
  }

  async findOne(id: string) {
    return this.traceService.getTracer().startActiveSpan(
      'OrdersService.findOne',
      async (span) => {
        span.setAttribute('order.id', id);

        // 查询逻辑...
        const order = { id, status: 'completed' };

        span.setStatus({ code: SpanStatusCode.OK });
        span.end();

        return order;
      }
    );
  }
}
```

```typescript
// src/app.module.ts

import { Module } from '@nestjs/common';
import { OpenTelemetryModule } from 'nestjs-otel';
import { OrdersModule } from './orders/orders.module';

@Module({
  imports: [
    OpenTelemetryModule.forRoot({
      metrics: {
        hostMetrics: true,
        defaultMetrics: true,
        apiMetrics: {
          enable: true,
        },
      },
    }),
    OrdersModule,
  ],
})
export class AppModule {}
```

### 4.3 浏览器SDK集成

```javascript
// public/otel.js

import { WebTracerProvider } from '@opentelemetry/sdk-trace-web';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-http';
import { BatchSpanProcessor } from '@opentelemetry/sdk-trace-base';
import { ZoneContextManager } from '@opentelemetry/context-zone';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { registerInstrumentations } from '@opentelemetry/instrumentation';
import { DocumentLoadInstrumentation } from '@opentelemetry/instrumentation-document-load';
import { FetchInstrumentation } from '@opentelemetry/instrumentation-fetch';
import { XMLHttpRequestInstrumentation } from '@opentelemetry/instrumentation-xml-http-request';

// 创建资源
const resource = new Resource({
  [SemanticResourceAttributes.SERVICE_NAME]: 'browser-app',
  [SemanticResourceAttributes.SERVICE_VERSION]: '1.0.0',
});

// 创建导出器
const collectorOptions = {
  url: 'http://localhost:4318/v1/traces',
  headers: {},
};

const exporter = new OTLPTraceExporter(collectorOptions);

// 创建Provider
const provider = new WebTracerProvider({
  resource,
  spanProcessors: [
    new BatchSpanProcessor(exporter, {
      maxQueueSize: 100,
      maxExportBatchSize: 10,
      scheduledDelayMillis: 500,
    }),
  ],
});

// 注册Provider
provider.register({
  contextManager: new ZoneContextManager(),
});

// 注册自动Instrumentation
registerInstrumentations({
  instrumentations: [
    new DocumentLoadInstrumentation(),
    new FetchInstrumentation({
      propagateTraceHeaderCorsUrls: [
        /.+/g, // 向所有URL传播Trace头
      ],
    }),
    new XMLHttpRequestInstrumentation({
      propagateTraceHeaderCorsUrls: [
        /.+/g,
      ],
    }),
  ],
});

// 导出tracer供应用使用
export const tracer = provider.getTracer('browser-app');
```

```html
<!-- public/index.html -->
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OpenTelemetry Browser Demo</title>
    <script type="module" src="./otel.js"></script>
</head>
<body>
    <h1>OpenTelemetry Browser Demo</h1>
    <button id="fetchBtn">Make Traced Request</button>
    <div id="result"></div>

    <script type="module">
        import { tracer } from './otel.js';

        document.getElementById('fetchBtn').addEventListener('click', async () => {
            // 手动创建Span
            await tracer.startActiveSpan('user.click', async (span) => {
                span.setAttribute('button.id', 'fetchBtn');
                span.setAttribute('button.text', 'Make Traced Request');

                try {
                    // 这个请求会自动追踪
                    const response = await fetch('/api/data');
                    const data = await response.json();

                    document.getElementById('result').textContent = JSON.stringify(data);

                    span.setStatus({ code: SpanStatusCode.OK });
                } catch (error) {
                    span.recordException(error);
                    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
                } finally {
                    span.end();
                }
            });
        });
    </script>
</body>
</html>
```

---

## 5. 生产环境最佳实践

### 5.1 采样配置

```javascript
// src/config/sampling.js

'use strict';

const { ParentBasedSampler, TraceIdRatioBasedSampler } = require('@opentelemetry/sdk-trace-node');
const { SamplingDecision } = require('@opentelemetry/sdk-trace-base');

/**
 * 自定义采样器
 */
class CustomSampler {
  constructor(baseRatio = 0.1) {
    this.baseSampler = new TraceIdRatioBasedSampler(baseRatio);
  }

  shouldSample(context, traceId, spanName, spanKind, attributes, links) {
    // 对健康检查不采样
    if (spanName.includes('health') || spanName.includes('/health')) {
      return { decision: SamplingDecision.NOT_RECORD };
    }

    // 对错误全量采样
    if (spanName.includes('error') || spanName.includes('Exception')) {
      return { decision: SamplingDecision.RECORD_AND_SAMPLED };
    }

    // 对关键操作全量采样
    const criticalOperations = ['payment', 'order/create', 'checkout'];
    if (criticalOperations.some(op => spanName.includes(op))) {
      return { decision: SamplingDecision.RECORD_AND_SAMPLED };
    }

    // 其他按基础采样率
    return this.baseSampler.shouldSample(context, traceId, spanName, spanKind, attributes, links);
  }

  toString() {
    return 'CustomSampler';
  }
}

/**
 * 创建基于父Span的采样器
 */
function createParentBasedSampler(baseRatio = 0.1) {
  return new ParentBasedSampler({
    root: new TraceIdRatioBasedSampler(baseRatio),
    remoteParentSampled: new TraceIdRatioBasedSampler(1.0),
    remoteParentNotSampled: new TraceIdRatioBasedSampler(0.0),
    localParentSampled: new TraceIdRatioBasedSampler(1.0),
    localParentNotSampled: new TraceIdRatioBasedSampler(baseRatio),
  });
}

module.exports = { CustomSampler, createParentBasedSampler };
```

### 5.2 优雅关闭和错误处理

```javascript
// src/utils/gracefulShutdown.js

'use strict';

class GracefulShutdownManager {
  constructor() {
    this.providers = [];
    this.hooks = [];
    this.isShuttingDown = false;

    // 注册信号处理器
    process.on('SIGTERM', () => this.shutdown('SIGTERM'));
    process.on('SIGINT', () => this.shutdown('SIGINT'));
  }

  registerProvider(provider) {
    this.providers.push(provider);
  }

  registerHook(hook) {
    this.hooks.push(hook);
  }

  async shutdown(signal) {
    if (this.isShuttingDown) {
      return;
    }
    this.isShuttingDown = true;

    console.log(`\nReceived ${signal}, initiating graceful shutdown...`);

    // 执行自定义钩子
    for (const hook of this.hooks) {
      try {
        await hook();
      } catch (err) {
        console.error('Error in shutdown hook:', err);
      }
    }

    // 关闭所有Provider
    for (const provider of this.providers) {
      try {
        if (typeof provider.shutdown === 'function') {
          await provider.shutdown();
          console.log(`Shutdown ${provider.constructor.name} completed`);
        }
      } catch (err) {
        console.error(`Error shutting down ${provider.constructor.name}:`, err);
      }
    }

    console.log('Graceful shutdown completed');
    process.exit(0);
  }
}

// 创建全局实例
const shutdownManager = new GracefulShutdownManager();

module.exports = { shutdownManager, GracefulShutdownManager };
```

### 5.3 日志集成

```javascript
// src/utils/logger.js

'use strict';

const winston = require('winston');
const { trace, context } = require('@opentelemetry/api');

// 自定义格式：添加Trace上下文
const traceContextFormat = winston.format((info) => {
  const currentSpan = trace.getSpan(context.active());

  if (currentSpan) {
    const spanContext = currentSpan.spanContext();
    info.trace_id = spanContext.traceId;
    info.span_id = spanContext.spanId;
    info.trace_flags = spanContext.traceFlags;
  }

  return info;
});

const logger = winston.createLogger({
  level: process.env.LOG_LEVEL || 'info',
  format: winston.format.combine(
    winston.format.timestamp(),
    traceContextFormat(),
    winston.format.json()
  ),
  defaultMeta: { service: process.env.OTEL_SERVICE_NAME || 'nodejs-service' },
  transports: [
    new winston.transports.Console(),
  ],
});

// 开发环境添加彩色输出
if (process.env.NODE_ENV === 'development') {
  logger.add(new winston.transports.Console({
    format: winston.format.combine(
      winston.format.colorize(),
      winston.format.simple()
    ),
  }));
}

module.exports = { logger };
```

---

## 6. 调试技巧

### 6.1 本地开发配置

```javascript
// src/config/devTelemetry.js

'use strict';

const { NodeSDK } = require('@opentelemetry/sdk-node');
const { ConsoleSpanExporter, SimpleSpanProcessor } = require('@opentelemetry/sdk-trace-node');
const { ConsoleMetricExporter, PeriodicExportingMetricReader } = require('@opentelemetry/sdk-metrics');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');

function initDevTelemetry() {
  const resource = new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: 'dev-service',
  });

  // 控制台Trace导出
  const traceExporter = new ConsoleSpanExporter();

  // 控制台Metrics导出
  const metricReader = new PeriodicExportingMetricReader({
    exporter: new ConsoleMetricExporter(),
    exportIntervalMillis: 5000,
  });

  const sdk = new NodeSDK({
    traceExporter,
    metricReader,
    resource,
  });

  sdk.start();
  console.log('Development telemetry initialized (console output)');

  return sdk;
}

module.exports = { initDevTelemetry };
```

### 6.2 验证Trace传播

```javascript
// src/utils/traceVerifier.js

'use strict';

const { trace, context } = require('@opentelemetry/api');
const { logger } = require('./logger');

function logCurrentTraceInfo() {
  const currentSpan = trace.getSpan(context.active());

  if (currentSpan) {
    const spanContext = currentSpan.spanContext();

    logger.info('Current Trace Context:', {
      traceId: spanContext.traceId,
      spanId: spanContext.spanId,
      sampled: spanContext.isRemote,
      traceFlags: spanContext.traceFlags,
    });
  } else {
    logger.warn('No active trace context');
  }
}

function verifyPropagation(carrier) {
  const { propagation } = require('@opentelemetry/api');

  // 提取上下文
  const extractedContext = propagation.extract(context.active(), carrier);
  const span = trace.getSpan(extractedContext);

  if (span && span.spanContext().traceId) {
    logger.info('Propagation verified successfully:', {
      traceId: span.spanContext().traceId,
      spanId: span.spanContext().spanId,
    });
    return true;
  } else {
    logger.error('Propagation verification failed - invalid span context');
    return false;
  }
}

module.exports = { logCurrentTraceInfo, verifyPropagation };
```

---

## 7. 参考资源

- [OpenTelemetry JavaScript官方文档](https://opentelemetry.io/docs/languages/js/)
- [OpenTelemetry JS SDK GitHub](https://github.com/open-telemetry/opentelemetry-js)
- [OpenTelemetry JS Contrib](https://github.com/open-telemetry/opentelemetry-js-contrib)
- [Express官方文档](https://expressjs.com/)
- [NestJS官方文档](https://docs.nestjs.com/)
- [nestjs-otel包](https://github.com/MetinSeylan/Nestjs-OpenTelemetry)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
