/**
 * 自定义指标定义
 */

const { metrics } = require('@opentelemetry/api');

// 获取meter
const meter = metrics.getMeter('otlp-nodejs-express-demo', '1.0.0');

// 请求计数器
const requestCounter = meter.createCounter('http_requests_total', {
  description: 'Total number of HTTP requests',
});

// 请求耗时直方图
const requestDuration = meter.createHistogram('http_request_duration_seconds', {
  description: 'HTTP request duration in seconds',
  unit: 'seconds',
});

// 活跃请求数
const activeRequests = meter.createUpDownCounter('http_requests_active', {
  description: 'Number of active HTTP requests',
});

// 业务指标：问候次数
const greetingCounter = meter.createCounter('business_greetings_total', {
  description: 'Total number of greetings processed',
});

// 业务指标：错误计数
const errorCounter = meter.createCounter('business_errors_total', {
  description: 'Total number of business errors',
});

// 系统指标：观察CPU使用率
const cpuUsage = meter.createObservableGauge('system_cpu_usage', {
  description: 'Current CPU usage percentage',
});

cpuUsage.addCallback((observableResult) => {
  const usage = process.cpuUsage();
  const percent = (usage.user + usage.system) / 1000000; // 转换为秒
  observableResult.observe(percent, { type: 'user_system' });
});

// 系统指标：观察内存使用
const memoryUsage = meter.createObservableGauge('system_memory_usage_bytes', {
  description: 'Current memory usage in bytes',
});

memoryUsage.addCallback((observableResult) => {
  const mem = process.memoryUsage();
  observableResult.observe(mem.heapUsed, { type: 'heap_used' });
  observableResult.observe(mem.heapTotal, { type: 'heap_total' });
  observableResult.observe(mem.rss, { type: 'rss' });
  observableResult.observe(mem.external, { type: 'external' });
});

module.exports = {
  requestCounter,
  requestDuration,
  activeRequests,
  greetingCounter,
  errorCounter,
};

