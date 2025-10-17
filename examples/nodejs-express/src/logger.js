/**
 * Winston日志配置 - 自动关联trace context
 */

const winston = require('winston');
const { trace, context } = require('@opentelemetry/api');

// 自定义格式：添加trace_id和span_id
const traceFormat = winston.format((info) => {
  const span = trace.getSpan(context.active());
  if (span) {
    const spanContext = span.spanContext();
    info.trace_id = spanContext.traceId;
    info.span_id = spanContext.spanId;
    info.trace_flags = spanContext.traceFlags;
  }
  return info;
});

// 创建logger
const logger = winston.createLogger({
  level: process.env.LOG_LEVEL || 'info',
  format: winston.format.combine(
    winston.format.timestamp({
      format: 'YYYY-MM-DD HH:mm:ss',
    }),
    traceFormat(),
    winston.format.errors({ stack: true }),
    winston.format.splat(),
    winston.format.json()
  ),
  defaultMeta: {
    service: process.env.OTEL_SERVICE_NAME || 'otlp-nodejs-express-demo',
  },
  transports: [
    // 控制台输出
    new winston.transports.Console({
      format: winston.format.combine(
        winston.format.colorize(),
        winston.format.printf(
          (info) =>
            `${info.timestamp} [${info.level}] [${info.trace_id || 'no-trace'}/${info.span_id || 'no-span'}] ${info.message} ${
              info.stack ? '\n' + info.stack : ''
            }`
        )
      ),
    }),
    
    // 文件输出（可选）
    // new winston.transports.File({ filename: 'logs/error.log', level: 'error' }),
    // new winston.transports.File({ filename: 'logs/combined.log' }),
  ],
});

module.exports = logger;

