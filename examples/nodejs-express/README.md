# OTLP Node.js Express Demo

完整的OpenTelemetry Node.js Express示例，展示Traces、Metrics和Logs的集成。

## 📋 目录

- [功能特性](#功能特性)
- [技术栈](#技术栈)
- [快速开始](#快速开始)
- [API端点](#api端点)
- [配置说明](#配置说明)
- [查看数据](#查看数据)
- [故障排查](#故障排查)

## 功能特性

### ✅ 完整的三大信号支持

- **Traces (追踪)**: OpenTelemetry API手动创建span + 自动埋点
- **Metrics (指标)**: OpenTelemetry Metrics API定义自定义指标
- **Logs (日志)**: Winston日志库 + 自动trace context关联

### ✅ 实用场景演示

1. **基本追踪**: `/api/hello` - 简单的请求-响应追踪
2. **嵌套Span**: `/api/chain` - 展示多层调用关系
3. **慢请求追踪**: `/api/slow` - 性能分析
4. **错误追踪**: `/api/error` - 异常处理和错误追踪
5. **数据库/缓存模拟**: 展示不同类型的客户端操作

### ✅ 最佳实践

- 自动埋点（HTTP, Express）
- 结构化日志（包含trace_id/span_id）
- 自定义span属性和事件
- 异常记录
- 批量导出配置
- 资源属性配置
- 系统指标（CPU, Memory）

## 技术栈

| 组件 | 版本 | 用途 |
|------|------|------|
| Node.js | 18+ | 运行时 |
| Express | 4.18+ | Web框架 |
| OpenTelemetry SDK | 1.7+ | 遥测SDK |
| OpenTelemetry Auto-Instrumentations | 0.40+ | 自动埋点 |
| Winston | 3.11+ | 日志库 |
| prom-client | 15+ | Prometheus指标（可选） |

## 快速开始

### 方式一：本地运行

#### 前置条件

- Node.js 18+
- npm 9+
- Docker (用于运行OTLP Collector和Jaeger)

#### 步骤

1. **启动基础设施**

```bash
# 在项目根目录
cd ../..
docker-compose up -d
```

2. **安装依赖**

```bash
cd examples/nodejs-express
npm install
```

3. **运行应用**

```bash
# 开发模式（使用nodemon）
npm run dev

# 生产模式
npm start
```

4. **验证**

```bash
# 健康检查
curl http://localhost:3000/api/health

# 测试追踪
curl "http://localhost:3000/api/hello?name=OpenTelemetry"

# 测试慢请求
curl http://localhost:3000/api/slow
```

### 方式二：Docker运行

```bash
# 构建镜像
docker build -t otlp-nodejs-express-demo .

# 运行容器
docker run -d \
  --name nodejs-demo \
  --network otlp_default \
  -p 3000:3000 \
  -e OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317 \
  otlp-nodejs-express-demo

# 查看日志
docker logs -f nodejs-demo
```

### 方式三：Docker Compose (推荐)

在项目根目录的`docker-compose.yml`中已包含此服务配置。

```bash
cd ../..
docker-compose up -d nodejs-app
```

## API端点

### 1. Hello端点

**基本用法**：

```bash
curl "http://localhost:3000/api/hello?name=World"
```

**响应**：

```json
{
  "message": "Hello, World!",
  "timestamp": 1697558400000,
  "trace_id": "8a3c60f7d188f8fa79d48a391a778fa6",
  "span_id": "79d48a391a778fa6"
}
```

**追踪层级**：
```
handle-hello-request (SERVER)
  └─ process-greeting (INTERNAL)
```

### 2. Slow端点

**用法**：

```bash
curl http://localhost:3000/api/slow
```

**响应**：

```json
{
  "duration_ms": 1523,
  "message": "Operation completed"
}
```

**功能**：
- 模拟慢操作（1-3秒）
- 在span中记录延迟时长
- 适合测试性能监控

### 3. Error端点

**用法**：

```bash
curl http://localhost:3000/api/error
```

**响应**：500错误

**功能**：
- 模拟异常场景
- 记录异常到span
- 记录错误日志
- 测试错误追踪

### 4. Chain端点

**用法**：

```bash
curl http://localhost:3000/api/chain
```

**响应**：

```json
{
  "status": "success",
  "operations": 3,
  "trace_id": "..."
}
```

**追踪层级**：
```
chained-operations
  ├─ operation-1
  │   └─ db.query (CLIENT)
  ├─ operation-2
  │   └─ http.request (CLIENT)
  └─ operation-3
      └─ cache.get (CLIENT)
```

### 5. Health端点

```bash
curl http://localhost:3000/api/health
```

**响应**：
```json
{
  "status": "UP"
}
```

### 6. Metrics端点

```bash
curl http://localhost:3000/api/metrics
```

**注意**: 指标实际通过OTLP导出，此端点仅显示配置信息。

## 配置说明

### 环境变量

```bash
# 服务配置
export OTEL_SERVICE_NAME=otlp-nodejs-express-demo
export OTEL_SERVICE_VERSION=1.0.0
export NODE_ENV=production
export PORT=3000

# OpenTelemetry配置
export OTEL_EXPORTER_OTLP_ENDPOINT=localhost:4317

# 日志级别
export LOG_LEVEL=info

# 运行应用
node src/server.js
```

### 代码中的配置

#### Traces配置 (`src/tracing.js`)

```javascript
const traceExporter = new OTLPTraceExporter({
  url: `grpc://${otlpEndpoint}`,
});

const sdk = new NodeSDK({
  resource,
  traceExporter,
  instrumentations: [
    getNodeAutoInstrumentations({
      '@opentelemetry/instrumentation-http': {
        enabled: true,
      },
      '@opentelemetry/instrumentation-express': {
        enabled: true,
      },
    }),
  ],
});
```

#### Metrics配置 (`src/metrics.js`)

```javascript
const meter = metrics.getMeter('otlp-nodejs-express-demo', '1.0.0');

const requestCounter = meter.createCounter('http_requests_total', {
  description: 'Total number of HTTP requests',
});

const requestDuration = meter.createHistogram('http_request_duration_seconds', {
  description: 'HTTP request duration in seconds',
  unit: 'seconds',
});
```

#### Logs配置 (`src/logger.js`)

```javascript
const traceFormat = winston.format((info) => {
  const span = trace.getSpan(context.active());
  if (span) {
    const spanContext = span.spanContext();
    info.trace_id = spanContext.traceId;
    info.span_id = spanContext.spanId;
  }
  return info;
});
```

## 查看数据

### Jaeger UI

打开浏览器访问：<http://localhost:16686>

**查看Traces**：
1. Service下拉选择 `otlp-nodejs-express-demo`
2. 点击"Find Traces"
3. 选择任意追踪查看详情

**典型追踪结构**：

```text
chained-operations (300ms)
  ├─ operation-1 (100ms)
  │   └─ db.query [postgresql] (20ms)
  ├─ operation-2 (150ms)
  │   └─ http.request [https://api.example.com/data] (100ms)
  └─ operation-3 (50ms)
      └─ cache.get [redis:user:123] (5ms)
```

### 控制台日志

查看应用日志，trace_id会自动注入：

```text
2025-10-17 10:30:15 [info] [8a3c60f7d188f8fa79d48a391a778fa6/79d48a391a778fa6] Processing hello request for: World
2025-10-17 10:30:15 [info] [8a3c60f7d188f8fa79d48a391a778fa6/79d48a391a778fa6] Hello request completed successfully
2025-10-17 10:30:15 [info] [8a3c60f7d188f8fa79d48a391a778fa6/79d48a391a778fa6] GET /api/hello - 200 (0.125s)
```

### Prometheus (可选)

如果需要Prometheus格式的指标，可以添加`prom-client`集成。

## 故障排查

### 问题1：无法连接到OTLP Collector

**症状**：

```text
Error: 14 UNAVAILABLE: No connection established
```

**解决方案**：

1. 检查Collector是否运行：

```bash
docker ps | grep otel-collector
curl http://localhost:13133/  # Collector健康检查
```

2. 检查endpoint配置（gRPC端口4317，HTTP端口4318）：

```bash
# 对于gRPC（默认）
export OTEL_EXPORTER_OTLP_ENDPOINT=localhost:4317

# 对于HTTP
export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318
```

3. 确认Docker网络（如果在容器中运行）：

```bash
docker network inspect otlp_default
```

### 问题2：没有看到Traces

**可能原因**：

1. **SDK未正确初始化**: 确保`require('./tracing')`在最顶部
2. **异步导出延迟**: 等待几秒后刷新Jaeger UI
3. **Collector未配置**: 检查`otel-config.yaml`

**调试**：

启用OpenTelemetry调试日志（在`src/tracing.js`中）：

```javascript
const { diag, DiagConsoleLogger, DiagLogLevel } = require('@opentelemetry/api');
diag.setLogger(new DiagConsoleLogger(), DiagLogLevel.DEBUG);
```

### 问题3：npm install失败

**症状**：

```text
npm ERR! code ERESOLVE
npm ERR! ERESOLVE could not resolve
```

**解决方案**：

1. 清理npm缓存：

```bash
npm cache clean --force
rm -rf node_modules package-lock.json
npm install
```

2. 使用`--legacy-peer-deps`：

```bash
npm install --legacy-peer-deps
```

3. 使用淘宝镜像（中国用户）：

```bash
npm config set registry https://registry.npmmirror.com
npm install
```

### 问题4：日志中没有trace_id

**可能原因**：

- Winston格式配置错误
- Span未正确传播

**解决方案**：

确保在span context中执行日志记录：

```javascript
const span = tracer.startSpan('my-operation');
return context.with(trace.setSpan(context.active(), span), () => {
  logger.info('This log will have trace_id');
  // ... your code ...
});
```

## 高级主题

### 1. 自定义采样策略

修改`src/tracing.js`：

```javascript
const { TraceIdRatioBasedSampler, ParentBasedSampler } = require('@opentelemetry/sdk-trace-base');

const sampler = new ParentBasedSampler({
  root: new TraceIdRatioBasedSampler(0.1), // 10%采样率
});

const sdk = new NodeSDK({
  // ...
  sampler,
});
```

### 2. 添加全局属性

```javascript
const resource = Resource.default().merge(
  new Resource({
    'custom.attribute': 'value',
    'environment': 'production',
  })
);
```

### 3. 禁用特定自动埋点

```javascript
instrumentations: [
  getNodeAutoInstrumentations({
    '@opentelemetry/instrumentation-fs': {
      enabled: false, // 禁用文件系统埋点
    },
    '@opentelemetry/instrumentation-dns': {
      enabled: false, // 禁用DNS埋点
    },
  }),
],
```

### 4. 添加Span处理器

```javascript
const { SimpleSpanProcessor } = require('@opentelemetry/sdk-trace-base');

// 添加自定义span处理器
const customProcessor = new SimpleSpanProcessor({
  onStart(span) {
    // 处理span开始
  },
  onEnd(span) {
    // 处理span结束
  },
});

tracerProvider.addSpanProcessor(customProcessor);
```

## 开发工具

### 运行linting

```bash
npm run lint
```

### 格式化代码

```bash
npm run format
```

### 测试

```bash
npm test
```

## 参考资源

- [OpenTelemetry JavaScript文档](https://opentelemetry.io/docs/languages/js/)
- [Express文档](https://expressjs.com/)
- [Winston文档](https://github.com/winstonjs/winston)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)

## 贡献

欢迎提交Issue和Pull Request！

## 许可证

MIT License

