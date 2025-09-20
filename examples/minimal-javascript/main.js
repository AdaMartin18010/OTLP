/**
 * OpenTelemetry JavaScript 最小示例
 * 演示如何使用 OpenTelemetry Node.js SDK 进行分布式追踪、指标监控和日志记录
 */

import { NodeSDK } from '@opentelemetry/sdk-node';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { OTLPTraceExporter } from '@opentelemetry/exporter-otlp-http';
import { OTLPMetricExporter } from '@opentelemetry/exporter-metrics-otlp-http';
import { OTLPLogExporter } from '@opentelemetry/exporter-logs-otlp-http';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { trace, metrics, logs } from '@opentelemetry/api';
import { MeterProvider } from '@opentelemetry/sdk-metrics';
import { LoggerProvider, SimpleLogRecordProcessor } from '@opentelemetry/sdk-logs';
import express from 'express';
import axios from 'axios';

// 服务配置
const SERVICE_NAME = 'minimal-javascript-service';
const SERVICE_VERSION = '1.0.0';
const SERVICE_ENVIRONMENT = 'development';

/**
 * 创建 OpenTelemetry SDK
 */
function createOpenTelemetrySDK() {
    console.log('🔧 初始化 OpenTelemetry SDK...');
    
    // 创建资源
    const resource = new Resource({
        [SemanticResourceAttributes.SERVICE_NAME]: SERVICE_NAME,
        [SemanticResourceAttributes.SERVICE_VERSION]: SERVICE_VERSION,
        [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: SERVICE_ENVIRONMENT,
        [SemanticResourceAttributes.SERVICE_INSTANCE_ID]: process.env.HOSTNAME || 'localhost',
    });
    
    // 创建 OTLP 导出器
    const traceExporter = new OTLPTraceExporter({
        url: 'http://localhost:4318/v1/traces',
        headers: {
            'Content-Type': 'application/x-protobuf',
        },
    });
    
    const metricExporter = new OTLPMetricExporter({
        url: 'http://localhost:4318/v1/metrics',
        headers: {
            'Content-Type': 'application/x-protobuf',
        },
    });
    
    const logExporter = new OTLPLogExporter({
        url: 'http://localhost:4318/v1/logs',
        headers: {
            'Content-Type': 'application/x-protobuf',
        },
    });
    
    // 创建 NodeSDK
    const sdk = new NodeSDK({
        resource,
        traceExporter,
        instrumentations: [
            getNodeAutoInstrumentations({
                // 启用所有自动检测
                '@opentelemetry/instrumentation-fs': {
                    enabled: true,
                },
                '@opentelemetry/instrumentation-http': {
                    enabled: true,
                },
                '@opentelemetry/instrumentation-express': {
                    enabled: true,
                },
                '@opentelemetry/instrumentation-dns': {
                    enabled: true,
                },
                '@opentelemetry/instrumentation-net': {
                    enabled: true,
                },
            }),
        ],
    });
    
    // 创建 MeterProvider
    const meterProvider = new MeterProvider({
        resource,
        readers: [metricExporter],
    });
    
    // 创建 LoggerProvider
    const loggerProvider = new LoggerProvider({
        resource,
        processors: [new SimpleLogRecordProcessor(logExporter)],
    });
    
    // 注册全局提供者
    metrics.setGlobalMeterProvider(meterProvider);
    logs.setGlobalLoggerProvider(loggerProvider);
    
    return { sdk, meterProvider, loggerProvider };
}

/**
 * 业务逻辑类
 */
class BusinessService {
    constructor() {
        this.tracer = trace.getTracer(SERVICE_NAME, SERVICE_VERSION);
        this.meter = metrics.getMeter(SERVICE_NAME, SERVICE_VERSION);
        this.logger = logs.getLogger(SERVICE_NAME, SERVICE_VERSION);
        
        // 创建指标
        this.requestCounter = this.meter.createCounter('requests_total', {
            description: 'Total number of requests',
            unit: '1',
        });
        
        this.requestDuration = this.meter.createHistogram('request_duration_ms', {
            description: 'Request duration in milliseconds',
            unit: 'ms',
        });
        
        this.activeConnections = this.meter.createUpDownCounter('active_connections', {
            description: 'Number of active connections',
            unit: '1',
        });
    }
    
    /**
     * 模拟业务操作
     */
    async performBusinessOperation(operationName, durationMs = 100) {
        const span = this.tracer.startSpan(operationName, {
            attributes: {
                'operation.type': 'business',
                'operation.duration_ms': durationMs,
                'service.name': SERVICE_NAME,
            },
        });
        
        try {
            // 记录日志
            this.logger.info('开始执行业务操作', {
                operationName,
                durationMs,
                timestamp: new Date().toISOString(),
            });
            
            // 增加计数器
            this.requestCounter.add(1, {
                operation: operationName,
                status: 'success',
            });
            
            // 记录开始时间
            const startTime = Date.now();
            
            // 模拟业务处理
            await this.simulateProcessing(durationMs);
            
            // 记录持续时间
            const duration = Date.now() - startTime;
            this.requestDuration.record(duration, {
                operation: operationName,
                status: 'success',
            });
            
            // 添加事件
            span.addEvent('业务操作完成', {
                result: 'success',
                duration_ms: duration,
            });
            
            // 设置状态
            span.setStatus({ code: 1 }); // OK
            
            this.logger.info('业务操作完成', {
                operationName,
                duration,
                result: 'success',
            });
            
        } catch (error) {
            // 设置错误状态
            span.setStatus({ code: 2, message: error.message }); // ERROR
            span.recordException(error);
            
            // 记录错误日志
            this.logger.error('业务操作失败', {
                operationName,
                error: error.message,
                stack: error.stack,
            });
            
            // 增加错误计数器
            this.requestCounter.add(1, {
                operation: operationName,
                status: 'error',
            });
            
            throw error;
        } finally {
            span.end();
        }
    }
    
    /**
     * 模拟嵌套操作
     */
    async performNestedOperation() {
        const parentSpan = this.tracer.startSpan('parent-operation', {
            attributes: {
                'operation.type': 'parent',
                'service.name': SERVICE_NAME,
            },
        });
        
        try {
            this.logger.info('开始执行父操作');
            
            // 执行子操作
            await this.performChildOperation('child-operation-1', 50);
            await this.performChildOperation('child-operation-2', 100);
            await this.performChildOperation('child-operation-3', 75);
            
            parentSpan.setStatus({ code: 1 }); // OK
            this.logger.info('父操作完成');
            
        } catch (error) {
            parentSpan.setStatus({ code: 2, message: error.message }); // ERROR
            parentSpan.recordException(error);
            this.logger.error('父操作失败', { error: error.message });
            throw error;
        } finally {
            parentSpan.end();
        }
    }
    
    /**
     * 执行子操作
     */
    async performChildOperation(operationName, durationMs) {
        const childSpan = this.tracer.startSpan(operationName, {
            attributes: {
                'operation.type': 'child',
                'operation.duration_ms': durationMs,
            },
        });
        
        try {
            this.logger.debug(`开始执行子操作: ${operationName}`);
            
            // 模拟处理时间
            await this.simulateProcessing(durationMs);
            
            // 添加属性
            childSpan.setAttributes({
                'operation.result': 'success',
                'operation.completed_at': new Date().toISOString(),
            });
            
            childSpan.setStatus({ code: 1 }); // OK
            this.logger.debug(`子操作完成: ${operationName}`);
            
        } catch (error) {
            childSpan.setStatus({ code: 2, message: error.message }); // ERROR
            childSpan.recordException(error);
            this.logger.error(`子操作失败: ${operationName}`, { error: error.message });
            throw error;
        } finally {
            childSpan.end();
        }
    }
    
    /**
     * 模拟异步处理
     */
    async simulateProcessing(durationMs) {
        return new Promise((resolve) => {
            setTimeout(resolve, durationMs);
        });
    }
    
    /**
     * 模拟HTTP请求
     */
    async performHttpRequest(url) {
        const span = this.tracer.startSpan('http-request', {
            attributes: {
                'http.method': 'GET',
                'http.url': url,
                'service.name': SERVICE_NAME,
            },
        });
        
        try {
            this.logger.info('发起HTTP请求', { url });
            
            const response = await axios.get(url, {
                timeout: 5000,
            });
            
            span.setAttributes({
                'http.status_code': response.status,
                'http.response.size': response.data.length,
            });
            
            span.setStatus({ code: 1 }); // OK
            this.logger.info('HTTP请求成功', {
                url,
                status: response.status,
                size: response.data.length,
            });
            
            return response.data;
            
        } catch (error) {
            span.setStatus({ code: 2, message: error.message }); // ERROR
            span.recordException(error);
            
            this.logger.error('HTTP请求失败', {
                url,
                error: error.message,
            });
            
            throw error;
        } finally {
            span.end();
        }
    }
}

/**
 * 创建Express应用
 */
function createExpressApp(businessService) {
    const app = express();
    
    // 中间件
    app.use(express.json());
    
    // 健康检查端点
    app.get('/health', (req, res) => {
        res.json({
            status: 'healthy',
            service: SERVICE_NAME,
            version: SERVICE_VERSION,
            timestamp: new Date().toISOString(),
        });
    });
    
    // 业务操作端点
    app.get('/api/operation/:name', async (req, res) => {
        try {
            const operationName = req.params.name;
            const duration = parseInt(req.query.duration) || 100;
            
            await businessService.performBusinessOperation(operationName, duration);
            
            res.json({
                success: true,
                operation: operationName,
                duration,
                timestamp: new Date().toISOString(),
            });
        } catch (error) {
            res.status(500).json({
                success: false,
                error: error.message,
                timestamp: new Date().toISOString(),
            });
        }
    });
    
    // 嵌套操作端点
    app.get('/api/nested', async (req, res) => {
        try {
            await businessService.performNestedOperation();
            
            res.json({
                success: true,
                operation: 'nested',
                timestamp: new Date().toISOString(),
            });
        } catch (error) {
            res.status(500).json({
                success: false,
                error: error.message,
                timestamp: new Date().toISOString(),
            });
        }
    });
    
    // HTTP请求端点
    app.get('/api/http/:url', async (req, res) => {
        try {
            const url = decodeURIComponent(req.params.url);
            const data = await businessService.performHttpRequest(url);
            
            res.json({
                success: true,
                url,
                dataLength: data.length,
                timestamp: new Date().toISOString(),
            });
        } catch (error) {
            res.status(500).json({
                success: false,
                error: error.message,
                timestamp: new Date().toISOString(),
            });
        }
    });
    
    return app;
}

/**
 * 主函数
 */
async function main() {
    console.log('🚀 OpenTelemetry JavaScript 最小示例启动');
    
    try {
        // 创建 OpenTelemetry SDK
        const { sdk, meterProvider, loggerProvider } = createOpenTelemetrySDK();
        
        // 启动 SDK
        sdk.start();
        console.log('✅ OpenTelemetry SDK 启动成功');
        
        // 创建业务服务
        const businessService = new BusinessService();
        
        // 记录启动日志
        businessService.logger.info('OpenTelemetry JavaScript 示例启动', {
            serviceName: SERVICE_NAME,
            serviceVersion: SERVICE_VERSION,
            environment: SERVICE_ENVIRONMENT,
            nodeVersion: process.version,
            platform: process.platform,
        });
        
        // 创建Express应用
        const app = createExpressApp(businessService);
        
        // 启动服务器
        const port = process.env.PORT || 3000;
        const server = app.listen(port, () => {
            console.log(`🌐 服务器启动在端口 ${port}`);
            console.log(`📊 健康检查: http://localhost:${port}/health`);
            console.log(`🔧 业务操作: http://localhost:${port}/api/operation/test`);
            console.log(`🔗 嵌套操作: http://localhost:${port}/api/nested`);
        });
        
        // 执行一些初始业务操作
        console.log('📊 执行业务操作...');
        await businessService.performBusinessOperation('user-login', 50);
        await businessService.performBusinessOperation('data-processing', 100);
        await businessService.performBusinessOperation('cache-update', 30);
        
        // 执行嵌套操作
        console.log('🔗 执行嵌套操作...');
        await businessService.performNestedOperation();
        
        // 执行HTTP请求（如果可能）
        try {
            console.log('🌐 执行HTTP请求...');
            await businessService.performHttpRequest('https://httpbin.org/json');
        } catch (error) {
            console.log('⚠️ HTTP请求失败（这是正常的，如果网络不可用）:', error.message);
        }
        
        // 等待一段时间确保数据被导出
        console.log('⏳ 等待数据导出...');
        await new Promise(resolve => setTimeout(resolve, 5000));
        
        console.log('✅ 示例执行完成');
        console.log('📈 请查看以下地址查看追踪数据:');
        console.log('   - Jaeger UI: http://localhost:16686');
        console.log('   - Prometheus: http://localhost:9090');
        console.log('   - Grafana: http://localhost:3000');
        console.log(`   - 应用服务: http://localhost:${port}`);
        
        // 优雅关闭
        process.on('SIGINT', () => {
            console.log('\n🛑 收到关闭信号，正在优雅关闭...');
            server.close(() => {
                console.log('✅ 服务器已关闭');
                sdk.shutdown().then(() => {
                    console.log('✅ OpenTelemetry SDK 已关闭');
                    process.exit(0);
                });
            });
        });
        
    } catch (error) {
        console.error('❌ 示例执行失败:', error.message);
        console.error(error.stack);
        process.exit(1);
    }
}

// 启动应用
main().catch(console.error);