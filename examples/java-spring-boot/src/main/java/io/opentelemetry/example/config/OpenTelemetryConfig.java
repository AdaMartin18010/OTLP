package io.opentelemetry.example.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.propagation.ContextPropagators;
import io.opentelemetry.exporter.otlp.logs.OtlpGrpcLogRecordExporter;
import io.opentelemetry.exporter.otlp.metrics.OtlpGrpcMetricExporter;
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.logs.SdkLoggerProvider;
import io.opentelemetry.sdk.logs.export.BatchLogRecordProcessor;
import io.opentelemetry.sdk.metrics.SdkMeterProvider;
import io.opentelemetry.sdk.metrics.export.PeriodicMetricReader;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.sdk.trace.samplers.Sampler;
import io.opentelemetry.semconv.ResourceAttributes;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.time.Duration;

/**
 * OpenTelemetry配置类
 * 配置Traces, Metrics, Logs的导出到OTLP Collector
 */
@Configuration
public class OpenTelemetryConfig {

    @Value("${otel.exporter.otlp.endpoint:http://localhost:4317}")
    private String otlpEndpoint;

    @Value("${otel.service.name:otlp-spring-boot-demo}")
    private String serviceName;

    @Value("${otel.service.version:1.0.0}")
    private String serviceVersion;

    /**
     * 创建Resource - 定义服务的元数据
     */
    @Bean
    public Resource otelResource() {
        return Resource.getDefault().merge(
            Resource.create(
                Attributes.builder()
                    .put(ResourceAttributes.SERVICE_NAME, serviceName)
                    .put(ResourceAttributes.SERVICE_VERSION, serviceVersion)
                    .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "development")
                    .put(ResourceAttributes.HOST_NAME, getHostName())
                    .build()
            )
        );
    }

    /**
     * 配置Trace Exporter - 导出追踪数据
     */
    @Bean
    public SdkTracerProvider sdkTracerProvider(Resource resource) {
        OtlpGrpcSpanExporter spanExporter = OtlpGrpcSpanExporter.builder()
            .setEndpoint(otlpEndpoint)
            .setTimeout(Duration.ofSeconds(10))
            .build();

        return SdkTracerProvider.builder()
            .setResource(resource)
            .addSpanProcessor(
                BatchSpanProcessor.builder(spanExporter)
                    .setScheduleDelay(Duration.ofSeconds(1))
                    .setMaxQueueSize(2048)
                    .setMaxExportBatchSize(512)
                    .build()
            )
            .setSampler(Sampler.alwaysOn()) // 生产环境应使用采样策略
            .build();
    }

    /**
     * 配置Metric Exporter - 导出指标数据
     */
    @Bean
    public SdkMeterProvider sdkMeterProvider(Resource resource) {
        OtlpGrpcMetricExporter metricExporter = OtlpGrpcMetricExporter.builder()
            .setEndpoint(otlpEndpoint)
            .setTimeout(Duration.ofSeconds(10))
            .build();

        return SdkMeterProvider.builder()
            .setResource(resource)
            .registerMetricReader(
                PeriodicMetricReader.builder(metricExporter)
                    .setInterval(Duration.ofSeconds(10))
                    .build()
            )
            .build();
    }

    /**
     * 配置Log Exporter - 导出日志数据
     */
    @Bean
    public SdkLoggerProvider sdkLoggerProvider(Resource resource) {
        OtlpGrpcLogRecordExporter logExporter = OtlpGrpcLogRecordExporter.builder()
            .setEndpoint(otlpEndpoint)
            .setTimeout(Duration.ofSeconds(10))
            .build();

        return SdkLoggerProvider.builder()
            .setResource(resource)
            .addLogRecordProcessor(
                BatchLogRecordProcessor.builder(logExporter)
                    .setScheduleDelay(Duration.ofSeconds(1))
                    .setMaxQueueSize(2048)
                    .setMaxExportBatchSize(512)
                    .build()
            )
            .build();
    }

    /**
     * 创建OpenTelemetry实例
     */
    @Bean
    public OpenTelemetry openTelemetry(
        SdkTracerProvider sdkTracerProvider,
        SdkMeterProvider sdkMeterProvider,
        SdkLoggerProvider sdkLoggerProvider
    ) {
        OpenTelemetrySdk sdk = OpenTelemetrySdk.builder()
            .setTracerProvider(sdkTracerProvider)
            .setMeterProvider(sdkMeterProvider)
            .setLoggerProvider(sdkLoggerProvider)
            .setPropagators(ContextPropagators.noop()) // 使用默认传播器
            .buildAndRegisterGlobal();

        // 注册关闭钩子
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            sdkTracerProvider.close();
            sdkMeterProvider.close();
            sdkLoggerProvider.close();
        }));

        return sdk;
    }

    /**
     * 创建Tracer实例
     */
    @Bean
    public Tracer tracer(OpenTelemetry openTelemetry) {
        return openTelemetry.getTracer(
            "io.opentelemetry.example",
            "1.0.0"
        );
    }

    private String getHostName() {
        try {
            return java.net.InetAddress.getLocalHost().getHostName();
        } catch (Exception e) {
            return "unknown";
        }
    }
}

