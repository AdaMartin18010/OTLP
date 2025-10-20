package io.opentelemetry.example.fintech.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.semconv.ResourceAttributes;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

/**
 * OpenTelemetry Configuration for FinTech Application
 * 
 * Configures OTLP exporter with appropriate resource attributes
 * for a financial services application.
 */
@Configuration
public class OpenTelemetryConfig {

    @Value("${otel.exporter.otlp.endpoint:http://localhost:4318/v1/traces}")
    private String otlpEndpoint;

    @Value("${otel.service.name:fintech-transaction-service}")
    private String serviceName;

    @Value("${otel.service.version:1.0.0}")
    private String serviceVersion;

    @Value("${spring.profiles.active:production}")
    private String environment;

    /**
     * Configure OpenTelemetry SDK with OTLP HTTP exporter
     */
    @Bean
    public OpenTelemetry openTelemetry() {
        // Create Resource with service information
        Resource resource = Resource.getDefault()
                .merge(Resource.create(Attributes.builder()
                        // Standard service attributes
                        .put(ResourceAttributes.SERVICE_NAME, serviceName)
                        .put(ResourceAttributes.SERVICE_VERSION, serviceVersion)
                        .put(ResourceAttributes.SERVICE_NAMESPACE, "fintech")
                        .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, environment)
                        
                        // Custom fintech resource attributes
                        .put("fintech.service.tier", "critical")
                        .put("fintech.service.category", "payment-processing")
                        .put("fintech.compliance.level", "pci-dss-level-1")
                        .put("fintech.region", "us-east-1")
                        .build()));

        // Create OTLP HTTP exporter
        OtlpHttpSpanExporter spanExporter = OtlpHttpSpanExporter.builder()
                .setEndpoint(otlpEndpoint)
                .build();

        // Create SdkTracerProvider with batch processor
        SdkTracerProvider sdkTracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(BatchSpanProcessor.builder(spanExporter)
                        .setMaxQueueSize(2048)
                        .setMaxExportBatchSize(512)
                        .setExporterTimeout(java.time.Duration.ofSeconds(30))
                        .build())
                .setResource(resource)
                .build();

        // Build OpenTelemetry SDK
        OpenTelemetrySdk openTelemetry = OpenTelemetrySdk.builder()
                .setTracerProvider(sdkTracerProvider)
                .buildAndRegisterGlobal();

        // Add shutdown hook
        Runtime.getRuntime().addShutdownHook(new Thread(sdkTracerProvider::close));

        return openTelemetry;
    }

    /**
     * Provide Tracer bean
     */
    @Bean
    public Tracer tracer(OpenTelemetry openTelemetry) {
        return openTelemetry.getTracer("fintech.transaction-service", serviceVersion);
    }
}

