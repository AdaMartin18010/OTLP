#!/usr/bin/env node

/**
 * OpenTelemetry JavaScript 最小示例
 * 
 * 演示如何使用OpenTelemetry JavaScript SDK进行：
 * 1. 分布式追踪 (Distributed Tracing)
 * 2. 指标监控 (Metrics)
 * 3. 资源检测 (Resource Detection)
 * 4. 数据导出 (Data Export)
 * 
 * 支持协议：
 * - gRPC (默认端口 4317)
 * - HTTP/Protobuf (默认端口 4318)
 * 
 * @author OpenTelemetry JavaScript Team
 * @version 1.0.0
 * @since 2025-09-17
 */

import { NodeSDK } from '@opentelemetry/sdk-node';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { trace, metrics, context, SpanKind, SpanStatusCode } from '@opentelemetry/api';
import { OTLPTraceExporter } from '@opentelemetry/exporter-otlp-http';
import { OTLPMetricExporter } from '@opentelemetry/exporter-otlp-http';
import { PeriodicExportingMetricReader } from '@opentelemetry/sdk-metrics';
import { BatchSpanProcessor } from '@opentelemetry/sdk-trace-base';
import express from 'express';
import axios from 'axios';
import winston from 'winston';

// 配置参数
const CONFIG = {
  serviceName: 'minimal-javascript-service',
  serviceVersion: '1.0.0',
  otlpEndpoint: process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'http://localhost:4318',
  otlpProtocol: process.env.OTEL_EXPORTER_OTLP_PROTOCOL || 'http/protobuf',
  logLevel: process.env.LOG_LEVEL || 'info'
};

// 创建日志记录器
const logger = winston.createLogger({
  level: CONFIG.logLevel,
  format: winston.format.combine(
    winston.format.timestamp(),
    winston.format.errors({ stack: true }),
    winston.format.json()
  ),
  transports: [
    new winston.transports.Console({
      format: winston.format.combine(
        winston.format.colorize(),
        winston.format.simple()
      )
    })
  ]
});

// 初始化OpenTelemetry
function initializeOpenTelemetry() {
  logger.info('初始化 OpenTelemetry SDK...');
  logger.info(`服务名称: ${CONFIG.serviceName}`);
  logger.info(`服务版本: ${CONFIG.serviceVersion}`);
  logger.info(`OTLP端点: ${CONFIG.otlpEndpoint}`);
  logger.info(`OTLP协议: ${CONFIG.otlpProtocol}`);

  // 创建资源
  const resource = new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: CONFIG.serviceName,
    [SemanticResourceAttributes.SERVICE_VERSION]: CONFIG.serviceVersion,
    [SemanticResourceAttributes.SERVICE_NAMESPACE]: 'opentelemetry-examples',
    [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: 'development'
  });

  // 创建OTLP导出器
  const traceExporter = new OTLPTraceExporter({
    url: `${CONFIG.otlpEndpoint}/v1/traces`,
    headers: {
      'Content-Type': 'application/x-protobuf'
    }
  });

  const metricExporter = new OTLPMetricExporter({
    url: `${CONFIG.otlpEndpoint}/v1/metrics`,
    headers: {
      'Content-Type': 'application/x-protobuf'
    }
  });

  // 创建SDK
  const sdk = new NodeSDK({
    resource,
    traceExporter,
    spanProcessor: new BatchSpanProcessor(traceExporter, {
      maxExportBatchSize: 512,
      exportTimeoutMillis: 30000,
      scheduledDelayMillis: 1000
    }),
    metricReader: new PeriodicExportingMetricReader({
      exporter: metricExporter,
      exportIntervalMillis: 10000
    }),
    instrumentations: [
      getNodeAutoInstrumentations({
        '@opentelemetry/instrumentation-fs': {
          enabled: false
        }
      })
    ]
  });

  // 启动SDK
  sdk.start();

  logger.info('OpenTelemetry SDK 初始化完成');
  return sdk;
}

// 获取Tracer和Meter
const tracer = trace.getTracer('minimal-javascript', '1.0.0');
const meter = metrics.getMeter('minimal-javascript', '1.0.0');

// 创建指标
const requestCounter = meter.createCounter('http_requests_total', {
  description: 'Total number of HTTP requests',
  unit: '1'
});

const errorCounter = meter.createCounter('http_errors_total', {
  description: 'Total number of HTTP errors',
  unit: '1'
});

const responseTimeHistogram = meter.createHistogram('http_request_duration_ms', {
  description: 'HTTP request duration in milliseconds',
  unit: 'ms'
});

// 基本追踪示例
async function runBasicTracingExample() {
  logger.info('运行基本追踪示例...');

  const span = tracer.startSpan('basic-operation', {
    kind: SpanKind.INTERNAL
  });

  try {
    await context.with(trace.setSpan(context.active(), span), async () => {
      // 模拟业务逻辑
      await new Promise(resolve => setTimeout(resolve, 100));

      // 记录属性
      span.setAttributes({
        'operation.type': 'basic',
        'operation.duration_ms': 100,
        'operation.success': true
      });

      logger.info('基本操作完成');
    });
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
    logger.error('基本操作失败', error);
  } finally {
    span.end();
  }
}

// 嵌套追踪示例
async function runNestedTracingExample() {
  logger.info('运行嵌套追踪示例...');

  const parentSpan = tracer.startSpan('parent-operation', {
    kind: SpanKind.INTERNAL
  });

  try {
    await context.with(trace.setSpan(context.active(), parentSpan), async () => {
      // 记录父级属性
      parentSpan.setAttributes({
        'operation.type': 'parent',
        'operation.level': 'parent'
      });

      // 创建子级Span
      const childSpan = tracer.startSpan('child-operation', {
        kind: SpanKind.INTERNAL
      });

      try {
        await context.with(trace.setSpan(context.active(), childSpan), async () => {
          // 记录子级属性
          childSpan.setAttributes({
            'operation.type': 'child',
            'operation.level': 'child',
            'operation.parent_id': parentSpan.spanContext().spanId
          });

          // 模拟子级操作
          await new Promise(resolve => setTimeout(resolve, 50));

          logger.info('子级操作完成');
        });
      } finally {
        childSpan.end();
      }

      // 模拟父级操作
      await new Promise(resolve => setTimeout(resolve, 50));

      logger.info('父级操作完成');
    });
  } catch (error) {
    parentSpan.recordException(error);
    parentSpan.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
    logger.error('嵌套操作失败', error);
  } finally {
    parentSpan.end();
  }
}

// 错误追踪示例
async function runErrorTracingExample() {
  logger.info('运行错误追踪示例...');

  const span = tracer.startSpan('error-operation', {
    kind: SpanKind.INTERNAL
  });

  try {
    await context.with(trace.setSpan(context.active(), span), async () => {
      // 记录属性
      span.setAttributes({
        'operation.type': 'error',
        'operation.expected_error': true
      });

      // 模拟错误
      try {
        throw new Error('模拟的业务错误');
      } catch (error) {
        // 记录异常
        span.recordException(error);
        span.setStatus({ code: SpanStatusCode.ERROR, message: '业务操作失败' });

        // 记录错误指标
        errorCounter.add(1, {
          'error.type': 'business_error',
          'error.message': error.message
        });

        logger.warn('捕获到预期错误', { error: error.message });
      }
    });
  } finally {
    span.end();
  }
}

// 指标记录示例
async function runMetricsExample() {
  logger.info('运行指标记录示例...');

  // 记录请求指标
  for (let i = 0; i < 10; i++) {
    requestCounter.add(1, {
      'http.method': 'GET',
      'http.status_code': 200,
      'endpoint': '/api/example'
    });

    // 模拟一些错误请求
    if (i % 3 === 0) {
      requestCounter.add(1, {
        'http.method': 'GET',
        'http.status_code': 500,
        'endpoint': '/api/example'
      });

      errorCounter.add(1, {
        'error.type': 'server_error',
        'endpoint': '/api/example'
      });
    }
  }

  // 记录一些延迟数据
  for (let i = 0; i < 20; i++) {
    const duration = 50 + Math.random() * 200; // 50-250ms
    responseTimeHistogram.record(duration, {
      'http.method': 'GET',
      'endpoint': '/api/example'
    });
  }

  logger.info('指标记录完成');
}

// 属性记录示例
async function runAttributesExample() {
  logger.info('运行属性记录示例...');

  const span = tracer.startSpan('attributes-operation', {
    kind: SpanKind.INTERNAL
  });

  try {
    await context.with(trace.setSpan(context.active(), span), async () => {
      // 记录各种类型的属性
      span.setAttributes({
        // 字符串属性
        'user.id': 'user123',
        'user.name': '张三',
        'user.email': 'zhangsan@example.com',

        // 数值属性
        'request.size_bytes': 1024,
        'response.size_bytes': 2048,
        'cpu.usage_percent': 75.5,

        // 布尔属性
        'request.cached': true,
        'response.compressed': false,

        // 数组属性
        'request.headers': 'Content-Type: application/json, User-Agent: JavaScript-Client',
        'response.cookies': 'session_id=abc123, csrf_token=xyz789'
      });

      // 模拟操作
      await new Promise(resolve => setTimeout(resolve, 100));

      logger.info('属性记录完成');
    });
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
    logger.error('属性记录失败', error);
  } finally {
    span.end();
  }
}

// 事件记录示例
async function runEventsExample() {
  logger.info('运行事件记录示例...');

  const span = tracer.startSpan('events-operation', {
    kind: SpanKind.INTERNAL
  });

  try {
    await context.with(trace.setSpan(context.active(), span), async () => {
      // 记录开始事件
      span.addEvent('operation.started', {
        timestamp: Date.now(),
        'operation.id': 'op_001'
      });

      // 模拟处理步骤
      await new Promise(resolve => setTimeout(resolve, 50));

      // 记录中间事件
      span.addEvent('operation.processing', {
        step: 'validation',
        'progress_percent': 25
      });

      await new Promise(resolve => setTimeout(resolve, 50));

      span.addEvent('operation.processing', {
        step: 'business_logic',
        'progress_percent': 50
      });

      await new Promise(resolve => setTimeout(resolve, 50));

      span.addEvent('operation.processing', {
        step: 'data_persistence',
        'progress_percent': 75
      });

      await new Promise(resolve => setTimeout(resolve, 50));

      // 记录完成事件
      span.addEvent('operation.completed', {
        timestamp: Date.now(),
        'operation.id': 'op_001',
        result: 'success',
        'total_duration_ms': 200
      });

      logger.info('事件记录完成');
    });
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
    logger.error('事件记录失败', error);
  } finally {
    span.end();
  }
}

// HTTP请求示例
async function runHttpRequestExample() {
  logger.info('运行HTTP请求示例...');

  const span = tracer.startSpan('http-request-operation', {
    kind: SpanKind.CLIENT
  });

  try {
    await context.with(trace.setSpan(context.active(), span), async () => {
      const startTime = Date.now();

      // 记录请求属性
      span.setAttributes({
        'http.method': 'GET',
        'http.url': 'https://httpbin.org/json',
        'http.scheme': 'https',
        'http.host': 'httpbin.org',
        'http.target': '/json'
      });

      // 发送HTTP请求
      const response = await axios.get('https://httpbin.org/json', {
        timeout: 5000
      });

      const duration = Date.now() - startTime;

      // 记录响应属性
      span.setAttributes({
        'http.status_code': response.status,
        'http.response.size_bytes': JSON.stringify(response.data).length,
        'http.request.duration_ms': duration
      });

      // 记录指标
      requestCounter.add(1, {
        'http.method': 'GET',
        'http.status_code': response.status,
        'http.host': 'httpbin.org'
      });

      responseTimeHistogram.record(duration, {
        'http.method': 'GET',
        'http.host': 'httpbin.org'
      });

      logger.info('HTTP请求完成', {
        status: response.status,
        duration: duration
      });
    });
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });

    // 记录错误指标
    errorCounter.add(1, {
      'error.type': 'http_error',
      'error.message': error.message
    });

    logger.error('HTTP请求失败', error);
  } finally {
    span.end();
  }
}

// Express应用示例
function createExpressApp() {
  const app = express();

  // 中间件
  app.use(express.json());

  // 路由
  app.get('/health', (req, res) => {
    res.json({ status: 'healthy', timestamp: new Date().toISOString() });
  });

  app.get('/api/example', async (req, res) => {
    const span = tracer.startSpan('api-example', {
      kind: SpanKind.SERVER
    });

    try {
      await context.with(trace.setSpan(context.active(), span), async () => {
        // 记录请求属性
        span.setAttributes({
          'http.method': req.method,
          'http.url': req.url,
          'http.user_agent': req.get('User-Agent') || 'unknown'
        });

        // 模拟业务逻辑
        await new Promise(resolve => setTimeout(resolve, 100));

        // 记录响应
        span.setAttributes({
          'http.status_code': 200
        });

        res.json({
          message: 'Hello from OpenTelemetry JavaScript!',
          timestamp: new Date().toISOString(),
          traceId: span.spanContext().traceId
        });
      });
    } catch (error) {
      span.recordException(error);
      span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
      res.status(500).json({ error: error.message });
    } finally {
      span.end();
    }
  });

  return app;
}

// 运行所有示例
async function runExamples() {
  logger.info('开始运行示例...');

  try {
    // 示例1: 基本追踪
    await runBasicTracingExample();

    // 示例2: 嵌套追踪
    await runNestedTracingExample();

    // 示例3: 错误追踪
    await runErrorTracingExample();

    // 示例4: 指标记录
    await runMetricsExample();

    // 示例5: 属性记录
    await runAttributesExample();

    // 示例6: 事件记录
    await runEventsExample();

    // 示例7: HTTP请求
    await runHttpRequestExample();

    logger.info('所有示例执行完成');
  } catch (error) {
    logger.error('示例执行失败', error);
    throw error;
  }
}

// 启动Express服务器
function startExpressServer() {
  const app = createExpressApp();
  const port = process.env.PORT || 3000;

  app.listen(port, () => {
    logger.info(`Express服务器启动在端口 ${port}`);
    logger.info(`健康检查: http://localhost:${port}/health`);
    logger.info(`API示例: http://localhost:${port}/api/example`);
  });

  return app;
}

// 主函数
async function main() {
  logger.info('启动 OpenTelemetry JavaScript 最小示例...');

  try {
    // 初始化OpenTelemetry
    const sdk = initializeOpenTelemetry();

    // 运行示例
    await runExamples();

    // 启动Express服务器
    const app = startExpressServer();

    // 等待数据导出
    logger.info('等待数据导出完成...');
    await new Promise(resolve => setTimeout(resolve, 5000));

    logger.info('示例执行完成！');
    logger.info('请查看以下地址查看结果：');
    logger.info('- Jaeger UI: http://localhost:16686');
    logger.info('- Prometheus: http://localhost:9090');
    logger.info('- Express服务器: http://localhost:3000');

    // 优雅关闭
    process.on('SIGINT', async () => {
      logger.info('收到关闭信号，正在优雅关闭...');
      await sdk.shutdown();
      process.exit(0);
    });

    process.on('SIGTERM', async () => {
      logger.info('收到终止信号，正在优雅关闭...');
      await sdk.shutdown();
      process.exit(0);
    });

  } catch (error) {
    logger.error('示例执行失败', error);
    process.exit(1);
  }
}

// 执行主函数
if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(error => {
    logger.error('主函数执行失败', error);
    process.exit(1);
  });
}

export {
  runBasicTracingExample,
  runNestedTracingExample,
  runErrorTracingExample,
  runMetricsExample,
  runAttributesExample,
  runEventsExample,
  runHttpRequestExample,
  createExpressApp
};
