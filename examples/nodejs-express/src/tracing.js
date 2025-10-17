/**
 * OpenTelemetry配置 - Traces, Metrics, Logs
 */

const { NodeSDK } = require('@opentelemetry/sdk-node');
const { getNodeAutoInstrumentations } = require('@opentelemetry/auto-instrumentations-node');
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');
const { OTLPMetricExporter } = require('@opentelemetry/exporter-metrics-otlp-grpc');
const { OTLPLogExporter } = require('@opentelemetry/exporter-logs-otlp-grpc');
const { PeriodicExportingMetricReader } = require('@opentelemetry/sdk-metrics');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');
const { diag, DiagConsoleLogger, DiagLogLevel } = require('@opentelemetry/api');

// 启用OpenTelemetry调试日志（可选）
// diag.setLogger(new DiagConsoleLogger(), DiagLogLevel.DEBUG);

// 配置Resource - 服务元数据
const resource = Resource.default().merge(
  new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: process.env.OTEL_SERVICE_NAME || 'otlp-nodejs-express-demo',
    [SemanticResourceAttributes.SERVICE_VERSION]: process.env.OTEL_SERVICE_VERSION || '1.0.0',
    [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: process.env.NODE_ENV || 'development',
    [SemanticResourceAttributes.HOST_NAME]: process.env.HOSTNAME || require('os').hostname(),
  })
);

// OTLP Collector端点
const otlpEndpoint = process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'localhost:4317';

// 配置Trace Exporter
const traceExporter = new OTLPTraceExporter({
  url: `grpc://${otlpEndpoint}`,
});

// 配置Metric Exporter
const metricExporter = new OTLPMetricExporter({
  url: `grpc://${otlpEndpoint}`,
});

// 配置Log Exporter
const logExporter = new OTLPLogExporter({
  url: `grpc://${otlpEndpoint}`,
});

// 创建NodeSDK实例
const sdk = new NodeSDK({
  resource,
  
  // Traces配置
  traceExporter,
  
  // Metrics配置
  metricReader: new PeriodicExportingMetricReader({
    exporter: metricExporter,
    exportIntervalMillis: 10000, // 10秒导出一次
  }),
  
  // Logs配置
  logRecordProcessor: require('@opentelemetry/sdk-logs').BatchLogRecordProcessor.prototype.constructor
    ? new (require('@opentelemetry/sdk-logs').BatchLogRecordProcessor)(logExporter)
    : undefined,
  
  // 自动埋点配置
  instrumentations: [
    getNodeAutoInstrumentations({
      // 自定义配置每个埋点
      '@opentelemetry/instrumentation-http': {
        enabled: true,
      },
      '@opentelemetry/instrumentation-express': {
        enabled: true,
      },
      '@opentelemetry/instrumentation-fs': {
        enabled: false, // 禁用文件系统埋点
      },
    }),
  ],
});

// 启动SDK
sdk.start();

console.log('✅ OpenTelemetry SDK initialized');
console.log(`📡 Exporting to: ${otlpEndpoint}`);

// 优雅关闭
process.on('SIGTERM', () => {
  sdk
    .shutdown()
    .then(() => console.log('🛑 OpenTelemetry SDK shut down successfully'))
    .catch((error) => console.error('❌ Error shutting down OpenTelemetry SDK', error))
    .finally(() => process.exit(0));
});

module.exports = sdk;

