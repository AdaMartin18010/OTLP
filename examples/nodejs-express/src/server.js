/**
 * Express服务器 - OTLP示例应用
 */

// 必须首先初始化OpenTelemetry SDK
require('./tracing');

const express = require('express');
const { trace, context, SpanStatusCode } = require('@opentelemetry/api');
const logger = require('./logger');
const {
  requestCounter,
  requestDuration,
  activeRequests,
  greetingCounter,
  errorCounter,
} = require('./metrics');

const app = express();
const port = process.env.PORT || 3000;
const tracer = trace.getTracer('otlp-nodejs-express-demo', '1.0.0');

// 中间件：解析JSON
app.use(express.json());

// 中间件：记录所有请求
app.use((req, res, next) => {
  const start = Date.now();
  
  // 增加活跃请求计数
  activeRequests.add(1, {
    method: req.method,
    route: req.route?.path || req.path,
  });
  
  // 请求完成后的处理
  res.on('finish', () => {
    const duration = (Date.now() - start) / 1000; // 秒
    
    const attributes = {
      method: req.method,
      route: req.route?.path || req.path,
      status_code: res.statusCode,
    };
    
    // 记录请求指标
    requestCounter.add(1, attributes);
    requestDuration.record(duration, attributes);
    
    // 减少活跃请求计数
    activeRequests.add(-1, attributes);
    
    logger.info(`${req.method} ${req.path} - ${res.statusCode} (${duration.toFixed(3)}s)`);
  });
  
  next();
});

/**
 * GET /api/hello - 基本问候端点
 */
app.get('/api/hello', (req, res) => {
  const span = tracer.startSpan('handle-hello-request');
  
  return context.with(trace.setSpan(context.active(), span), () => {
    try {
      const name = req.query.name || 'World';
      
      // 添加span属性
      span.setAttribute('request.name', name);
      span.setAttribute('request.name.length', name.length);
      
      logger.info(`Processing hello request for: ${name}`);
      
      // 模拟业务逻辑
      const greeting = processGreeting(name);
      
      // 记录业务指标
      greetingCounter.add(1, { name_length: name.length.toString() });
      
      // 添加span事件
      span.addEvent('greeting_processed', {
        result: greeting,
      });
      
      const response = {
        message: greeting,
        timestamp: Date.now(),
        trace_id: span.spanContext().traceId,
        span_id: span.spanContext().spanId,
      };
      
      logger.info('Hello request completed successfully');
      span.setStatus({ code: SpanStatusCode.OK });
      
      res.json(response);
    } catch (error) {
      span.recordException(error);
      span.setStatus({
        code: SpanStatusCode.ERROR,
        message: error.message,
      });
      
      logger.error('Error processing hello request:', error);
      errorCounter.add(1, { endpoint: '/api/hello' });
      
      res.status(500).json({ error: error.message });
    } finally {
      span.end();
    }
  });
});

/**
 * GET /api/slow - 慢请求端点
 */
app.get('/api/slow', async (req, res) => {
  const span = tracer.startSpan('slow-operation');
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      logger.info('Starting slow operation');
      
      // 模拟慢操作（1-3秒）
      const delay = 1000 + Math.floor(Math.random() * 2000);
      span.setAttribute('delay_ms', delay);
      
      await sleep(delay);
      
      logger.info(`Slow operation completed (${delay}ms)`);
      span.setStatus({ code: SpanStatusCode.OK });
      
      res.json({
        duration_ms: delay,
        message: 'Operation completed',
      });
    } catch (error) {
      span.recordException(error);
      span.setStatus({ code: SpanStatusCode.ERROR });
      logger.error('Error in slow operation:', error);
      res.status(500).json({ error: error.message });
    } finally {
      span.end();
    }
  });
});

/**
 * GET /api/error - 错误端点
 */
app.get('/api/error', (req, res) => {
  const span = tracer.startSpan('error-operation');
  
  return context.with(trace.setSpan(context.active(), span), () => {
    try {
      logger.warn('Simulating error condition');
      
      span.setAttribute('error.type', 'simulated');
      
      // 抛出模拟错误
      throw new Error('Simulated error for testing');
    } catch (error) {
      span.recordException(error);
      span.setStatus({
        code: SpanStatusCode.ERROR,
        message: error.message,
      });
      
      logger.error('Error in error endpoint:', error);
      errorCounter.add(1, { endpoint: '/api/error' });
      
      res.status(500).json({
        error: error.message,
        trace_id: span.spanContext().traceId,
      });
    } finally {
      span.end();
    }
  });
});

/**
 * GET /api/chain - 链式调用端点
 */
app.get('/api/chain', async (req, res) => {
  const parentSpan = tracer.startSpan('chained-operations');
  
  return context.with(trace.setSpan(context.active(), parentSpan), async () => {
    try {
      logger.info('Starting chained operations');
      
      // 执行三个子操作
      await operation1();
      await operation2();
      await operation3();
      
      logger.info('All chained operations completed');
      parentSpan.setStatus({ code: SpanStatusCode.OK });
      
      res.json({
        status: 'success',
        operations: 3,
        trace_id: parentSpan.spanContext().traceId,
      });
    } catch (error) {
      parentSpan.recordException(error);
      parentSpan.setStatus({ code: SpanStatusCode.ERROR });
      logger.error('Error in chained operations:', error);
      res.status(500).json({ error: error.message });
    } finally {
      parentSpan.end();
    }
  });
});

/**
 * GET /api/health - 健康检查
 */
app.get('/api/health', (req, res) => {
  res.json({ status: 'UP' });
});

/**
 * GET /api/metrics - 查看指标（简化版）
 */
app.get('/api/metrics', (req, res) => {
  res.json({
    message: 'Metrics are exported to OTLP Collector',
    endpoint: process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'localhost:4317',
  });
});

/**
 * 辅助函数：处理问候
 */
function processGreeting(name) {
  const span = tracer.startSpan('process-greeting');
  
  return context.with(trace.setSpan(context.active(), span), () => {
    try {
      span.setAttribute('name', name);
      
      logger.debug(`Processing greeting for: ${name}`);
      
      // 模拟处理延迟
      const delay = 50 + Math.floor(Math.random() * 100);
      sleepSync(delay);
      
      const result = `Hello, ${name}!`;
      span.setAttribute('result.length', result.length);
      
      return result;
    } finally {
      span.end();
    }
  });
}

/**
 * 辅助函数：操作1（模拟数据库查询）
 */
async function operation1() {
  const span = tracer.startSpan('operation-1');
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      logger.info('Executing operation 1');
      
      // 模拟数据库查询
      await simulateDatabaseQuery('users');
      
      await sleep(100);
      span.addEvent('operation_1_completed');
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 辅助函数：操作2（模拟外部API调用）
 */
async function operation2() {
  const span = tracer.startSpan('operation-2');
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      logger.info('Executing operation 2');
      
      // 模拟外部API调用
      await simulateExternalApiCall('https://api.example.com/data');
      
      await sleep(150);
      span.addEvent('operation_2_completed');
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 辅助函数：操作3（模拟缓存查询）
 */
async function operation3() {
  const span = tracer.startSpan('operation-3');
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      logger.info('Executing operation 3');
      
      // 模拟缓存查询
      await simulateCacheQuery('user:123');
      
      await sleep(50);
      span.addEvent('operation_3_completed');
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 模拟数据库查询
 */
async function simulateDatabaseQuery(table) {
  const span = tracer.startSpan('db.query', {
    kind: 1, // CLIENT
  });
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      span.setAttribute('db.system', 'postgresql');
      span.setAttribute('db.table', table);
      span.setAttribute('db.operation', 'SELECT');
      
      logger.debug(`Querying database table: ${table}`);
      
      await sleep(20 + Math.floor(Math.random() * 30));
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 模拟外部API调用
 */
async function simulateExternalApiCall(url) {
  const span = tracer.startSpan('http.request', {
    kind: 1, // CLIENT
  });
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      span.setAttribute('http.method', 'GET');
      span.setAttribute('http.url', url);
      span.setAttribute('http.status_code', 200);
      
      logger.debug(`Calling external API: ${url}`);
      
      await sleep(100 + Math.floor(Math.random() * 100));
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 模拟缓存查询
 */
async function simulateCacheQuery(key) {
  const span = tracer.startSpan('cache.get', {
    kind: 1, // CLIENT
  });
  
  return context.with(trace.setSpan(context.active(), span), async () => {
    try {
      span.setAttribute('cache.system', 'redis');
      span.setAttribute('cache.key', key);
      span.setAttribute('cache.hit', true);
      
      logger.debug(`Getting from cache: ${key}`);
      
      await sleep(5 + Math.floor(Math.random() * 10));
      span.setStatus({ code: SpanStatusCode.OK });
    } finally {
      span.end();
    }
  });
}

/**
 * 工具函数：异步sleep
 */
function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * 工具函数：同步sleep（使用阻塞方式，仅用于演示）
 */
function sleepSync(ms) {
  const start = Date.now();
  while (Date.now() - start < ms) {
    // 空循环
  }
}

// 启动服务器
app.listen(port, () => {
  logger.info(`🚀 Server is running on port ${port}`);
  logger.info(`📊 Service: ${process.env.OTEL_SERVICE_NAME || 'otlp-nodejs-express-demo'}`);
  logger.info(`📡 OTLP Endpoint: ${process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'localhost:4317'}`);
  logger.info('');
  logger.info('Available endpoints:');
  logger.info('  GET http://localhost:' + port + '/api/hello?name=World');
  logger.info('  GET http://localhost:' + port + '/api/slow');
  logger.info('  GET http://localhost:' + port + '/api/error');
  logger.info('  GET http://localhost:' + port + '/api/chain');
  logger.info('  GET http://localhost:' + port + '/api/health');
  logger.info('  GET http://localhost:' + port + '/api/metrics');
});

// 优雅关闭
process.on('SIGTERM', () => {
  logger.info('SIGTERM signal received: closing HTTP server');
  process.exit(0);
});

process.on('SIGINT', () => {
  logger.info('SIGINT signal received: closing HTTP server');
  process.exit(0);
});

