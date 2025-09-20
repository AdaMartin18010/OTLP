package com.example.otlp;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.logs.Logger;
import io.opentelemetry.api.logs.LoggerProvider;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.metrics.Meter;
import io.opentelemetry.api.metrics.MeterProvider;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.api.trace.TracerProvider;
import io.opentelemetry.context.Scope;
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter;
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.logs.SdkLoggerProvider;
import io.opentelemetry.sdk.logs.export.BatchLogRecordProcessor;
import io.opentelemetry.sdk.metrics.SdkMeterProvider;
import io.opentelemetry.sdk.metrics.export.PeriodicMetricReader;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.semconv.ResourceAttributes;

import java.time.Duration;
import java.util.concurrent.TimeUnit;

/**
 * OpenTelemetry Java 最小示例
 * 演示如何使用 OpenTelemetry Java SDK 进行分布式追踪、指标监控和日志记录
 */
public class MinimalExample {
    
    private static final String SERVICE_NAME = "minimal-java-service";
    private static final String SERVICE_VERSION = "1.0.0";
    
    private final Tracer tracer;
    private final Meter meter;
    private final Logger logger;
    private final LongCounter requestCounter;
    
    public MinimalExample(OpenTelemetry openTelemetry) {
        // 获取 Tracer
        TracerProvider tracerProvider = openTelemetry.getTracerProvider();
        this.tracer = tracerProvider.get("minimal-java-service", "1.0.0");
        
        // 获取 Meter
        MeterProvider meterProvider = openTelemetry.getMeterProvider();
        this.meter = meterProvider.get("minimal-java-service", "1.0.0");
        
        // 创建计数器
        this.requestCounter = meter.counterBuilder("requests_total")
                .setDescription("Total number of requests")
                .setUnit("1")
                .build();
        
        // 获取 Logger
        LoggerProvider loggerProvider = openTelemetry.getLogsBridge().getLoggerProvider();
        this.logger = loggerProvider.get("minimal-java-service", "1.0.0");
    }
    
    /**
     * 创建 OpenTelemetry 实例
     */
    public static OpenTelemetry createOpenTelemetry() {
        // 创建资源
        Resource resource = Resource.getDefault()
                .merge(Resource.create(Attributes.of(
                        ResourceAttributes.SERVICE_NAME, SERVICE_NAME,
                        ResourceAttributes.SERVICE_VERSION, SERVICE_VERSION,
                        ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "development"
                )));
        
        // 创建 OTLP HTTP 导出器
        OtlpHttpSpanExporter httpExporter = OtlpHttpSpanExporter.builder()
                .setEndpoint("http://localhost:4318/v1/traces")
                .setTimeout(Duration.ofSeconds(10))
                .build();
        
        // 创建 OTLP gRPC 导出器
        OtlpGrpcSpanExporter grpcExporter = OtlpGrpcSpanExporter.builder()
                .setEndpoint("http://localhost:4317")
                .setTimeout(Duration.ofSeconds(10))
                .build();
        
        // 创建 TracerProvider
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(BatchSpanProcessor.builder(httpExporter)
                        .setMaxExportBatchSize(512)
                        .setExportTimeout(Duration.ofSeconds(30))
                        .setScheduleDelay(Duration.ofSeconds(1))
                        .build())
                .addSpanProcessor(BatchSpanProcessor.builder(grpcExporter)
                        .setMaxExportBatchSize(512)
                        .setExportTimeout(Duration.ofSeconds(30))
                        .setScheduleDelay(Duration.ofSeconds(1))
                        .build())
                .setResource(resource)
                .build();
        
        // 创建 MeterProvider
        SdkMeterProvider meterProvider = SdkMeterProvider.builder()
                .setResource(resource)
                .registerMetricReader(PeriodicMetricReader.builder(
                        io.opentelemetry.exporter.otlp.metrics.OtlpGrpcMetricExporter.builder()
                                .setEndpoint("http://localhost:4317")
                                .setTimeout(Duration.ofSeconds(10))
                                .build())
                        .setInterval(Duration.ofSeconds(10))
                        .build())
                .build();
        
        // 创建 LoggerProvider
        SdkLoggerProvider loggerProvider = SdkLoggerProvider.builder()
                .setResource(resource)
                .addLogRecordProcessor(BatchLogRecordProcessor.builder(
                        io.opentelemetry.exporter.otlp.logs.OtlpGrpcLogRecordExporter.builder()
                                .setEndpoint("http://localhost:4317")
                                .setTimeout(Duration.ofSeconds(10))
                                .build())
                        .setMaxExportBatchSize(512)
                        .setExportTimeout(Duration.ofSeconds(30))
                        .setScheduleDelay(Duration.ofSeconds(1))
                        .build())
                .build();
        
        // 创建 OpenTelemetry SDK
        return OpenTelemetrySdk.builder()
                .setTracerProvider(tracerProvider)
                .setMeterProvider(meterProvider)
                .setLoggerProvider(loggerProvider)
                .buildAndRegisterGlobal();
    }
    
    /**
     * 模拟业务操作
     */
    public void performBusinessOperation(String operationName, int durationMs) {
        // 创建 span
        Span span = tracer.spanBuilder(operationName)
                .setSpanKind(SpanKind.INTERNAL)
                .setAttribute("operation.type", "business")
                .setAttribute("operation.duration_ms", durationMs)
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 记录日志
            logger.info("开始执行业务操作: " + operationName, 
                    Attributes.of(
                            AttributeKey.stringKey("operation.name"), operationName,
                            AttributeKey.longKey("operation.duration_ms"), (long) durationMs
                    ));
            
            // 增加计数器
            requestCounter.add(1, Attributes.of(
                    AttributeKey.stringKey("operation"), operationName,
                    AttributeKey.stringKey("status"), "success"
            ));
            
            // 模拟业务处理时间
            Thread.sleep(durationMs);
            
            // 添加事件
            span.addEvent("业务操作完成", Attributes.of(
                    AttributeKey.stringKey("result"), "success",
                    AttributeKey.longKey("duration_ms"), (long) durationMs
            ));
            
            // 设置状态
            span.setStatus(StatusCode.OK);
            
        } catch (InterruptedException e) {
            // 设置错误状态
            span.setStatus(StatusCode.ERROR, "操作被中断: " + e.getMessage());
            span.recordException(e);
            
            // 记录错误日志
            logger.error("业务操作被中断: " + operationName, e,
                    Attributes.of(
                            AttributeKey.stringKey("operation.name"), operationName,
                            AttributeKey.stringKey("error.type"), "InterruptedException"
                    ));
            
            // 增加错误计数器
            requestCounter.add(1, Attributes.of(
                    AttributeKey.stringKey("operation"), operationName,
                    AttributeKey.stringKey("status"), "error"
            ));
            
            Thread.currentThread().interrupt();
        } catch (Exception e) {
            // 设置错误状态
            span.setStatus(StatusCode.ERROR, "操作失败: " + e.getMessage());
            span.recordException(e);
            
            // 记录错误日志
            logger.error("业务操作失败: " + operationName, e,
                    Attributes.of(
                            AttributeKey.stringKey("operation.name"), operationName,
                            AttributeKey.stringKey("error.type"), e.getClass().getSimpleName()
                    ));
            
            // 增加错误计数器
            requestCounter.add(1, Attributes.of(
                    AttributeKey.stringKey("operation"), operationName,
                    AttributeKey.stringKey("status"), "error"
            ));
        } finally {
            span.end();
        }
    }
    
    /**
     * 模拟嵌套操作
     */
    public void performNestedOperation() {
        Span parentSpan = tracer.spanBuilder("parent-operation")
                .setSpanKind(SpanKind.INTERNAL)
                .startSpan();
        
        try (Scope parentScope = parentSpan.makeCurrent()) {
            logger.info("开始执行父操作");
            
            // 执行子操作1
            performChildOperation("child-operation-1", 100);
            
            // 执行子操作2
            performChildOperation("child-operation-2", 200);
            
            // 执行子操作3
            performChildOperation("child-operation-3", 150);
            
            parentSpan.setStatus(StatusCode.OK);
            logger.info("父操作完成");
            
        } catch (Exception e) {
            parentSpan.setStatus(StatusCode.ERROR, "父操作失败: " + e.getMessage());
            parentSpan.recordException(e);
            logger.error("父操作失败", e);
        } finally {
            parentSpan.end();
        }
    }
    
    /**
     * 执行子操作
     */
    private void performChildOperation(String operationName, int durationMs) {
        Span childSpan = tracer.spanBuilder(operationName)
                .setSpanKind(SpanKind.INTERNAL)
                .setAttribute("operation.type", "child")
                .startSpan();
        
        try (Scope childScope = childSpan.makeCurrent()) {
            logger.debug("开始执行子操作: " + operationName);
            
            // 模拟处理时间
            Thread.sleep(durationMs);
            
            // 添加属性
            childSpan.setAttribute("operation.duration_ms", durationMs);
            childSpan.setAttribute("operation.result", "success");
            
            childSpan.setStatus(StatusCode.OK);
            logger.debug("子操作完成: " + operationName);
            
        } catch (InterruptedException e) {
            childSpan.setStatus(StatusCode.ERROR, "子操作被中断: " + e.getMessage());
            childSpan.recordException(e);
            logger.error("子操作被中断: " + operationName, e);
            Thread.currentThread().interrupt();
        } catch (Exception e) {
            childSpan.setStatus(StatusCode.ERROR, "子操作失败: " + e.getMessage());
            childSpan.recordException(e);
            logger.error("子操作失败: " + operationName, e);
        } finally {
            childSpan.end();
        }
    }
    
    /**
     * 主方法
     */
    public static void main(String[] args) {
        System.out.println("🚀 OpenTelemetry Java 最小示例启动");
        
        try {
            // 创建 OpenTelemetry 实例
            OpenTelemetry openTelemetry = createOpenTelemetry();
            
            // 创建示例实例
            MinimalExample example = new MinimalExample(openTelemetry);
            
            // 记录启动日志
            example.logger.info("OpenTelemetry Java 示例启动",
                    Attributes.of(
                            AttributeKey.stringKey("service.name"), SERVICE_NAME,
                            AttributeKey.stringKey("service.version"), SERVICE_VERSION
                    ));
            
            // 执行一些业务操作
            System.out.println("📊 执行业务操作...");
            example.performBusinessOperation("user-login", 50);
            example.performBusinessOperation("data-processing", 100);
            example.performBusinessOperation("cache-update", 30);
            
            // 执行嵌套操作
            System.out.println("🔗 执行嵌套操作...");
            example.performNestedOperation();
            
            // 等待一段时间确保数据被导出
            System.out.println("⏳ 等待数据导出...");
            Thread.sleep(5000);
            
            System.out.println("✅ 示例执行完成");
            System.out.println("📈 请查看以下地址查看追踪数据:");
            System.out.println("   - Jaeger UI: http://localhost:16686");
            System.out.println("   - Prometheus: http://localhost:9090");
            System.out.println("   - Grafana: http://localhost:3000");
            
        } catch (Exception e) {
            System.err.println("❌ 示例执行失败: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
