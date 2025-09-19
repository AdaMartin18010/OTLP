package com.opentelemetry.minimal;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.metrics.Meter;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.api.trace.TracerProvider;
import io.opentelemetry.context.Scope;
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter;
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporterBuilder;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.metrics.SdkMeterProvider;
import io.opentelemetry.sdk.metrics.export.PeriodicMetricReader;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.semconv.ResourceAttributes;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.util.concurrent.TimeUnit;

/**
 * OpenTelemetry Java 最小示例
 * 
 * 演示如何使用OpenTelemetry Java SDK进行：
 * 1. 分布式追踪 (Distributed Tracing)
 * 2. 指标监控 (Metrics)
 * 3. 资源检测 (Resource Detection)
 * 4. 数据导出 (Data Export)
 * 
 * 支持协议：
 * - gRPC (默认端口 4317)
 * - HTTP/Protobuf (默认端口 4318)
 * 
 * @author OpenTelemetry Java Team
 * @version 1.0.0
 * @since 2025-09-17
 */
public class Main {
    
    private static final Logger logger = LoggerFactory.getLogger(Main.class);
    
    // OpenTelemetry组件
    private static OpenTelemetry openTelemetry;
    private static Tracer tracer;
    private static Meter meter;
    private static LongCounter requestCounter;
    private static LongCounter errorCounter;
    
    // 配置参数
    private static final String SERVICE_NAME = "minimal-java-service";
    private static final String SERVICE_VERSION = "1.0.0";
    private static final String OTLP_ENDPOINT = System.getProperty("otel.exporter.otlp.endpoint", 
                                                                  "http://localhost:4318");
    private static final String OTLP_PROTOCOL = System.getProperty("otel.exporter.otlp.protocol", 
                                                                   "http/protobuf");
    
    public static void main(String[] args) {
        logger.info("启动 OpenTelemetry Java 最小示例...");
        logger.info("服务名称: {}", SERVICE_NAME);
        logger.info("服务版本: {}", SERVICE_VERSION);
        logger.info("OTLP端点: {}", OTLP_ENDPOINT);
        logger.info("OTLP协议: {}", OTLP_PROTOCOL);
        
        try {
            // 初始化OpenTelemetry
            initializeOpenTelemetry();
            
            // 运行示例
            runExamples();
            
            // 等待数据导出
            logger.info("等待数据导出完成...");
            Thread.sleep(5000);
            
            logger.info("示例执行完成！");
            logger.info("请查看以下地址查看结果：");
            logger.info("- Jaeger UI: http://localhost:16686");
            logger.info("- Prometheus: http://localhost:9090");
            
        } catch (Exception e) {
            logger.error("示例执行失败", e);
            System.exit(1);
        } finally {
            // 关闭OpenTelemetry
            shutdownOpenTelemetry();
        }
    }
    
    /**
     * 初始化OpenTelemetry SDK
     */
    private static void initializeOpenTelemetry() {
        logger.info("初始化 OpenTelemetry SDK...");
        
        // 创建资源
        Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.of(
                ResourceAttributes.SERVICE_NAME, SERVICE_NAME,
                ResourceAttributes.SERVICE_VERSION, SERVICE_VERSION,
                ResourceAttributes.SERVICE_NAMESPACE, "opentelemetry-examples",
                ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "development"
            )));
        
        // 创建OTLP导出器
        OtlpHttpSpanExporterBuilder spanExporterBuilder = OtlpHttpSpanExporter.builder()
            .setEndpoint(OTLP_ENDPOINT + "/v1/traces");
        
        // 根据协议配置导出器
        if ("grpc".equals(OTLP_PROTOCOL)) {
            // 使用gRPC导出器
            spanExporterBuilder = OtlpHttpSpanExporter.builder()
                .setEndpoint(OTLP_ENDPOINT.replace("4318", "4317") + "/v1/traces");
        }
        
        OtlpHttpSpanExporter spanExporter = spanExporterBuilder.build();
        
        // 创建TracerProvider
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(BatchSpanProcessor.builder(spanExporter)
                .setMaxExportBatchSize(512)
                .setExportTimeout(Duration.ofSeconds(30))
                .setScheduleDelay(Duration.ofSeconds(1))
                .build())
            .setResource(resource)
            .build();
        
        // 创建MeterProvider
        SdkMeterProvider meterProvider = SdkMeterProvider.builder()
            .registerMetricReader(PeriodicMetricReader.builder(
                io.opentelemetry.exporter.otlp.http.metrics.OtlpHttpMetricExporter.builder()
                    .setEndpoint(OTLP_ENDPOINT + "/v1/metrics")
                    .build())
                .setInterval(Duration.ofSeconds(10))
                .build())
            .setResource(resource)
            .build();
        
        // 创建OpenTelemetry实例
        openTelemetry = OpenTelemetrySdk.builder()
            .setTracerProvider(tracerProvider)
            .setMeterProvider(meterProvider)
            .build();
        
        // 获取Tracer和Meter
        tracer = openTelemetry.getTracer("minimal-java", "1.0.0");
        meter = openTelemetry.getMeter("minimal-java", "1.0.0");
        
        // 创建指标
        requestCounter = meter.counterBuilder("http_requests_total")
            .setDescription("Total number of HTTP requests")
            .setUnit("1")
            .build();
        
        errorCounter = meter.counterBuilder("http_errors_total")
            .setDescription("Total number of HTTP errors")
            .setUnit("1")
            .build();
        
        logger.info("OpenTelemetry SDK 初始化完成");
    }
    
    /**
     * 运行示例
     */
    private static void runExamples() throws InterruptedException {
        logger.info("开始运行示例...");
        
        // 示例1: 基本追踪
        runBasicTracingExample();
        
        // 示例2: 嵌套追踪
        runNestedTracingExample();
        
        // 示例3: 错误追踪
        runErrorTracingExample();
        
        // 示例4: 指标记录
        runMetricsExample();
        
        // 示例5: 属性记录
        runAttributesExample();
        
        // 示例6: 事件记录
        runEventsExample();
        
        logger.info("所有示例执行完成");
    }
    
    /**
     * 基本追踪示例
     */
    private static void runBasicTracingExample() {
        logger.info("运行基本追踪示例...");
        
        Span span = tracer.spanBuilder("basic-operation")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 模拟业务逻辑
            Thread.sleep(100);
            
            // 记录属性
            span.setAttributes(Attributes.of(
                "operation.type", "basic",
                "operation.duration_ms", 100,
                "operation.success", true
            ));
            
            logger.info("基本操作完成");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            span.recordException(e);
            span.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, "操作被中断");
        } finally {
            span.end();
        }
    }
    
    /**
     * 嵌套追踪示例
     */
    private static void runNestedTracingExample() {
        logger.info("运行嵌套追踪示例...");
        
        Span parentSpan = tracer.spanBuilder("parent-operation")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();
        
        try (Scope parentScope = parentSpan.makeCurrent()) {
            // 记录父级属性
            parentSpan.setAttributes(Attributes.of(
                "operation.type", "parent",
                "operation.level", "parent"
            ));
            
            // 创建子级Span
            Span childSpan = tracer.spanBuilder("child-operation")
                .setSpanKind(SpanKind.INTERNAL)
                .startSpan();
            
            try (Scope childScope = childSpan.makeCurrent()) {
                // 记录子级属性
                childSpan.setAttributes(Attributes.of(
                    "operation.type", "child",
                    "operation.level", "child",
                    "operation.parent_id", parentSpan.getSpanContext().getSpanId()
                ));
                
                // 模拟子级操作
                Thread.sleep(50);
                
                logger.info("子级操作完成");
            } finally {
                childSpan.end();
            }
            
            // 模拟父级操作
            Thread.sleep(50);
            
            logger.info("父级操作完成");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            parentSpan.recordException(e);
            parentSpan.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, "操作被中断");
        } finally {
            parentSpan.end();
        }
    }
    
    /**
     * 错误追踪示例
     */
    private static void runErrorTracingExample() {
        logger.info("运行错误追踪示例...");
        
        Span span = tracer.spanBuilder("error-operation")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 记录属性
            span.setAttributes(Attributes.of(
                "operation.type", "error",
                "operation.expected_error", true
            ));
            
            // 模拟错误
            try {
                throw new RuntimeException("模拟的业务错误");
            } catch (RuntimeException e) {
                // 记录异常
                span.recordException(e);
                span.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, "业务操作失败");
                
                // 记录错误指标
                errorCounter.add(1, Attributes.of(
                    "error.type", "business_error",
                    "error.message", e.getMessage()
                ));
                
                logger.warn("捕获到预期错误: {}", e.getMessage());
            }
        } finally {
            span.end();
        }
    }
    
    /**
     * 指标记录示例
     */
    private static void runMetricsExample() {
        logger.info("运行指标记录示例...");
        
        // 记录请求指标
        for (int i = 0; i < 10; i++) {
            requestCounter.add(1, Attributes.of(
                "http.method", "GET",
                "http.status_code", 200,
                "endpoint", "/api/example"
            ));
            
            // 模拟一些错误请求
            if (i % 3 == 0) {
                requestCounter.add(1, Attributes.of(
                    "http.method", "GET",
                    "http.status_code", 500,
                    "endpoint", "/api/example"
                ));
                
                errorCounter.add(1, Attributes.of(
                    "error.type", "server_error",
                    "endpoint", "/api/example"
                ));
            }
        }
        
        // 创建并记录直方图指标
        var histogram = meter.histogramBuilder("http_request_duration_ms")
            .setDescription("HTTP request duration in milliseconds")
            .setUnit("ms")
            .build();
        
        // 记录一些延迟数据
        for (int i = 0; i < 20; i++) {
            long duration = 50 + (long) (Math.random() * 200); // 50-250ms
            histogram.record(duration, Attributes.of(
                "http.method", "GET",
                "endpoint", "/api/example"
            ));
        }
        
        logger.info("指标记录完成");
    }
    
    /**
     * 属性记录示例
     */
    private static void runAttributesExample() {
        logger.info("运行属性记录示例...");
        
        Span span = tracer.spanBuilder("attributes-operation")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 记录各种类型的属性
            span.setAttributes(Attributes.of(
                // 字符串属性
                "user.id", "user123",
                "user.name", "张三",
                "user.email", "zhangsan@example.com",
                
                // 数值属性
                "request.size_bytes", 1024L,
                "response.size_bytes", 2048L,
                "cpu.usage_percent", 75.5,
                
                // 布尔属性
                "request.cached", true,
                "response.compressed", false,
                
                // 数组属性
                "request.headers", "Content-Type: application/json, User-Agent: Java-Client",
                "response.cookies", "session_id=abc123, csrf_token=xyz789"
            ));
            
            // 模拟操作
            Thread.sleep(100);
            
            logger.info("属性记录完成");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            span.recordException(e);
            span.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, "操作被中断");
        } finally {
            span.end();
        }
    }
    
    /**
     * 事件记录示例
     */
    private static void runEventsExample() {
        logger.info("运行事件记录示例...");
        
        Span span = tracer.spanBuilder("events-operation")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 记录开始事件
            span.addEvent("operation.started", Attributes.of(
                "timestamp", System.currentTimeMillis(),
                "operation.id", "op_001"
            ));
            
            // 模拟处理步骤
            Thread.sleep(50);
            
            // 记录中间事件
            span.addEvent("operation.processing", Attributes.of(
                "step", "validation",
                "progress_percent", 25
            ));
            
            Thread.sleep(50);
            
            span.addEvent("operation.processing", Attributes.of(
                "step", "business_logic",
                "progress_percent", 50
            ));
            
            Thread.sleep(50);
            
            span.addEvent("operation.processing", Attributes.of(
                "step", "data_persistence",
                "progress_percent", 75
            ));
            
            Thread.sleep(50);
            
            // 记录完成事件
            span.addEvent("operation.completed", Attributes.of(
                "timestamp", System.currentTimeMillis(),
                "operation.id", "op_001",
                "result", "success",
                "total_duration_ms", 200
            ));
            
            logger.info("事件记录完成");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            span.recordException(e);
            span.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, "操作被中断");
        } finally {
            span.end();
        }
    }
    
    /**
     * 关闭OpenTelemetry
     */
    private static void shutdownOpenTelemetry() {
        logger.info("关闭 OpenTelemetry SDK...");
        
        if (openTelemetry instanceof OpenTelemetrySdk) {
            OpenTelemetrySdk sdk = (OpenTelemetrySdk) openTelemetry;
            sdk.close();
        }
        
        logger.info("OpenTelemetry SDK 已关闭");
    }
}
