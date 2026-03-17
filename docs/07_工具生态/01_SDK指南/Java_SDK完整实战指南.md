---
title: Java SDK完整实战指南
description: OpenTelemetry Java SDK的完整实战指南，包含Spring Boot集成、Micrometer兼容、自动配置等
version: Java 11+ / OTel Java v1.32.0 / Spring Boot 3.x
date: 2026-03-17
author: OTLP项目团队
category: SDK指南
tags:
  - java
  - spring-boot
  - sdk
  - otlp
  - opentelemetry
status: published
---

# Java SDK完整实战指南

> **版本**: Java 11+ / OpenTelemetry Java v1.32.0 / Spring Boot 3.x
> **最后更新**: 2026-03-17
> **阅读时间**: 约40分钟

---

## 1. 环境准备

### 1.1 Maven依赖配置

```xml
<!-- pom.xml -->
<properties>
    <opentelemetry.version>1.32.0</opentelemetry.version>
    <opentelemetry-instrumentation.version>1.32.0-alpha</opentelemetry-instrumentation.version>
    <spring-boot.version>3.2.0</spring-boot.version>
</properties>

<dependencies>
    <!-- OpenTelemetry API -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-api</artifactId>
        <version>${opentelemetry.version}</version>
    </dependency>

    <!-- OpenTelemetry SDK -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-sdk</artifactId>
        <version>${opentelemetry.version}</version>
    </dependency>

    <!-- OTLP Exporters -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-exporter-otlp</artifactId>
        <version>${opentelemetry.version}</version>
    </dependency>

    <!-- OpenTelemetry Instrumentation Annotations -->
    <dependency>
        <groupId>io.opentelemetry.instrumentation</groupId>
        <artifactId>opentelemetry-instrumentation-annotations</artifactId>
        <version>${opentelemetry-instrumentation.version}</version>
    </dependency>

    <!-- Spring Boot Starter -->
    <dependency>
        <groupId>org.springframework.boot</groupId>
        <artifactId>spring-boot-starter-web</artifactId>
    </dependency>

    <!-- Micrometer Bridge to OpenTelemetry -->
    <dependency>
        <groupId>io.opentelemetry.instrumentation</groupId>
        <artifactId>opentelemetry-micrometer-1.5</artifactId>
        <version>${opentelemetry-instrumentation.version}</version>
    </dependency>

    <!-- Logback MDC Integration -->
    <dependency>
        <groupId>io.opentelemetry.instrumentation</groupId>
        <artifactId>opentelemetry-logback-mdc-1.0</artifactId>
        <version>${opentelemetry-instrumentation.version}</version>
    </dependency>

    <!-- gRPC Netty (for OTLP gRPC) -->
    <dependency>
        <groupId>io.grpc</groupId>
        <artifactId>grpc-netty-shaded</artifactId>
        <version>1.59.0</version>
    </dependency>
</dependencies>
```

### 1.2 Gradle依赖配置

```groovy
// build.gradle
plugins {
    id 'java'
    id 'org.springframework.boot' version '3.2.0'
    id 'io.spring.dependency-management' version '1.1.4'
}

ext {
    openTelemetryVersion = '1.32.0'
    openTelemetryInstrumentationVersion = '1.32.0-alpha'
}

dependencies {
    // OpenTelemetry
    implementation "io.opentelemetry:opentelemetry-api:${openTelemetryVersion}"
    implementation "io.opentelemetry:opentelemetry-sdk:${openTelemetryVersion}"
    implementation "io.opentelemetry:opentelemetry-exporter-otlp:${openTelemetryVersion}"
    implementation "io.opentelemetry.instrumentation:opentelemetry-instrumentation-annotations:${openTelemetryInstrumentationVersion}"

    // Spring Boot
    implementation 'org.springframework.boot:spring-boot-starter-web'
    implementation 'org.springframework.boot:spring-boot-starter-actuator'

    // Micrometer Bridge
    implementation "io.opentelemetry.instrumentation:opentelemetry-micrometer-1.5:${openTelemetryInstrumentationVersion}"

    // gRPC
    implementation 'io.grpc:grpc-netty-shaded:1.59.0'
}
```

### 1.3 项目结构

```
myapp/
├── src/
│   ├── main/
│   │   ├── java/
│   │   │   └── com/example/myapp/
│   │   │       ├── MyAppApplication.java
│   │   │       ├── config/
│   │   │       │   ├── OpenTelemetryConfig.java    # 核心配置
│   │   │       │   ├── TracingConfig.java          # 链路追踪配置
│   │   │       │   └── MetricsConfig.java          # 指标配置
│   │   │       ├── controller/
│   │   │       │   └── OrderController.java
│   │   │       ├── service/
│   │   │       │   ├── OrderService.java
│   │   │       │   └── PaymentService.java
│   │   │       ├── repository/
│   │   │       │   └── OrderRepository.java
│   │   │       └── interceptor/
│   │   │           └── TracingInterceptor.java     # 自定义拦截器
│   │   └── resources/
│   │       ├── application.yml
│   │       └── logback-spring.xml
│   └── test/
├── pom.xml (或 build.gradle)
└── Dockerfile
```

---

## 2. 基础配置

### 2.1 程序化配置OpenTelemetry

```java
// config/OpenTelemetryConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.api.trace.propagation.W3CTraceContextPropagator;
import io.opentelemetry.context.propagation.ContextPropagators;
import io.opentelemetry.exporter.otlp.http.trace.OtlpHttpSpanExporter;
import io.opentelemetry.exporter.otlp.metrics.OtlpGrpcMetricExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.metrics.SdkMeterProvider;
import io.opentelemetry.sdk.metrics.export.PeriodicMetricReader;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.semconv.ResourceAttributes;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.time.Duration;
import java.util.concurrent.TimeUnit;

@Configuration
public class OpenTelemetryConfig {

    @Value("${otel.service.name:my-service}")
    private String serviceName;

    @Value("${otel.service.version:1.0.0}")
    private String serviceVersion;

    @Value("${otel.exporter.otlp.endpoint:http://localhost:4318}")
    private String otlpEndpoint;

    @Value("${otel.exporter.otlp.timeout:10000}")
    private long timeout;

    @Bean
    public OpenTelemetry openTelemetry() {
        // 创建Resource
        Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.builder()
                .put(ResourceAttributes.SERVICE_NAME, serviceName)
                .put(ResourceAttributes.SERVICE_VERSION, serviceVersion)
                .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, System.getenv().getOrDefault("ENV", "development"))
                .build()));

        // 配置Trace Exporter
        OtlpHttpSpanExporter spanExporter = OtlpHttpSpanExporter.builder()
            .setEndpoint(otlpEndpoint + "/v1/traces")
            .setTimeout(timeout, TimeUnit.MILLISECONDS)
            .build();

        // 配置Tracer Provider
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(BatchSpanProcessor.builder(spanExporter)
                .setScheduleDelay(100, TimeUnit.MILLISECONDS)
                .setMaxQueueSize(2048)
                .setMaxExportBatchSize(512)
                .setExportTimeout(timeout, TimeUnit.MILLISECONDS)
                .build())
            .setResource(resource)
            .build();

        // 配置Metric Exporter
        OtlpGrpcMetricExporter metricExporter = OtlpGrpcMetricExporter.builder()
            .setEndpoint(otlpEndpoint.replace("http://", "").replace("https://", ""))
            .setTimeout(timeout, TimeUnit.MILLISECONDS)
            .build();

        // 配置Meter Provider
        SdkMeterProvider meterProvider = SdkMeterProvider.builder()
            .registerMetricReader(PeriodicMetricReader.builder(metricExporter)
                .setInterval(Duration.ofSeconds(60))
                .build())
            .setResource(resource)
            .build();

        // 构建OpenTelemetry SDK
        return OpenTelemetrySdk.builder()
            .setTracerProvider(tracerProvider)
            .setMeterProvider(meterProvider)
            .setPropagators(ContextPropagators.create(W3CTraceContextPropagator.getInstance()))
            .buildAndRegisterGlobal();
    }

    @Bean
    public Tracer tracer(OpenTelemetry openTelemetry) {
        return openTelemetry.getTracer(serviceName, serviceVersion);
    }
}
```

### 2.2 Spring Boot自动配置方式

```java
// 使用Spring Boot Starter简化配置

// build.gradle 添加依赖
implementation 'io.opentelemetry.instrumentation:opentelemetry-spring-boot-starter:1.32.0-alpha'

// application.yml
```yaml
otel:
  service:
    name: order-service
    version: 1.0.0
  exporter:
    otlp:
      endpoint: http://localhost:4318
      timeout: 10s
  traces:
    sampler:
      probability: 0.1  # 10%采样
  metrics:
    export:
      interval: 60000ms

spring:
  application:
    name: ${otel.service.name}
```

### 2.3 使用Java Agent自动注入

```bash
# 下载Java Agent
wget https://github.com/open-telemetry/opentelemetry-java-instrumentation/releases/download/v1.32.0/opentelemetry-javaagent.jar

# 启动应用
java -javaagent:opentelemetry-javaagent.jar \
     -Dotel.service.name=order-service \
     -Dotel.exporter.otlp.endpoint=http://localhost:4318 \
     -Dotel.traces.sampler.probability=0.1 \
     -jar myapp.jar
```

---

## 3. 核心使用示例

### 3.1 创建Span（程序化方式）

```java
// service/OrderService.java

package com.example.myapp.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.instrumentation.annotations.WithSpan;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.UUID;

@Service
public class OrderService {

    private final Tracer tracer;
    private final PaymentService paymentService;

    @Autowired
    public OrderService(Tracer tracer, PaymentService paymentService) {
        this.tracer = tracer;
        this.paymentService = paymentService;
    }

    // 方式1: 使用注解自动创建Span
    @WithSpan("OrderService.createOrder")
    public Order createOrder(String userId, double amount) {
        Span span = Span.current();

        try {
            // 设置属性
            span.setAttribute("order.user_id", userId);
            span.setAttribute("order.amount", amount);

            // 生成订单ID
            String orderId = UUID.randomUUID().toString();
            span.setAttribute("order.id", orderId);

            // 记录事件
            span.addEvent("Order validation started");
            validateOrder(userId, amount);
            span.addEvent("Order validation completed");

            // 处理支付
            span.addEvent("Payment processing started");
            boolean paymentSuccess = paymentService.processPayment(orderId, amount);

            if (!paymentSuccess) {
                span.setStatus(StatusCode.ERROR, "Payment failed");
                throw new RuntimeException("Payment processing failed");
            }

            span.addEvent("Payment completed",
                Attributes.of(AttributeKey.stringKey("payment.transaction_id"), "txn_" + orderId));

            // 创建订单
            Order order = new Order(orderId, userId, amount, "CREATED");
            span.setAttribute("order.status", order.getStatus());
            span.setStatus(StatusCode.OK);

            return order;

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        }
    }

    // 方式2: 手动创建Span
    public Order getOrder(String orderId) {
        // 创建新的Span
        Span span = tracer.spanBuilder("OrderService.getOrder")
            .setSpanKind(SpanKind.INTERNAL)
            .setAttribute("order.id", orderId)
            .startSpan();

        // 必须使用try-with-resources确保Span正确结束
        try (Scope scope = span.makeCurrent()) {

            // 模拟数据库查询
            span.addEvent("Database query started");
            Order order = queryOrderFromDatabase(orderId);
            span.addEvent("Database query completed");

            if (order != null) {
                span.setAttribute("order.found", true);
                span.setAttribute("order.user_id", order.getUserId());
                span.setStatus(StatusCode.OK);
            } else {
                span.setAttribute("order.found", false);
                span.setStatus(StatusCode.ERROR, "Order not found");
            }

            return order;

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }

    // 方式3: 嵌套Span
    public void processBulkOrders(List<String> orderIds) {
        Span parentSpan = tracer.spanBuilder("OrderService.processBulkOrders")
            .setAttribute("order.count", orderIds.size())
            .startSpan();

        try (Scope parentScope = parentSpan.makeCurrent()) {

            for (String orderId : orderIds) {
                // 创建子Span
                Span childSpan = tracer.spanBuilder("OrderService.processSingleOrder")
                    .setParent(io.opentelemetry.context.Context.current().with(parentSpan))
                    .setAttribute("order.id", orderId)
                    .startSpan();

                try (Scope childScope = childSpan.makeCurrent()) {
                    processOrder(orderId);
                    childSpan.setStatus(StatusCode.OK);
                } catch (Exception e) {
                    childSpan.recordException(e);
                    childSpan.setStatus(StatusCode.ERROR, e.getMessage());
                } finally {
                    childSpan.end();
                }
            }

            parentSpan.setStatus(StatusCode.OK);

        } finally {
            parentSpan.end();
        }
    }

    private void validateOrder(String userId, double amount) {
        if (amount <= 0) {
            throw new IllegalArgumentException("Invalid amount");
        }
    }

    private Order queryOrderFromDatabase(String orderId) {
        // 数据库查询逻辑
        return new Order(orderId, "user123", 99.99, "CREATED");
    }

    private void processOrder(String orderId) {
        // 处理单个订单
    }
}
```

### 3.2 记录指标

```java
// config/MetricsConfig.java

package com.example.myapp.config;

import io.micrometer.core.instrument.Counter;
import io.micrometer.core.instrument.MeterRegistry;
import io.micrometer.core.instrument.Timer;
import io.micrometer.core.instrument.Gauge;
import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.metrics.LongHistogram;
import io.opentelemetry.api.metrics.Meter;
import io.opentelemetry.api.metrics.ObservableLongGauge;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.util.concurrent.atomic.AtomicLong;

@Configuration
public class MetricsConfig {

    @Bean
    public Meter meter(OpenTelemetry openTelemetry) {
        return openTelemetry.getMeter("order-service");
    }

    // OpenTelemetry原生指标
    @Bean
    public LongCounter orderCounter(Meter meter) {
        return meter.counterBuilder("orders.total")
            .setDescription("Total number of orders")
            .setUnit("1")
            .build();
    }

    @Bean
    public LongHistogram orderValueHistogram(Meter meter) {
        return meter.histogramBuilder("order.value")
            .setDescription("Order value distribution")
            .setUnit("USD")
            .ofLongs()
            .build();
    }

    @Bean
    public ObservableLongGauge queueSizeGauge(Meter meter) {
        AtomicLong queueSize = new AtomicLong(0);

        return meter.gaugeBuilder("queue.size")
            .setDescription("Current queue size")
            .setUnit("1")
            .buildWithCallback(measurement -> {
                measurement.record(queueSize.get());
            });
    }

    // Micrometer指标（自动桥接到OpenTelemetry）
    @Bean
    public Counter micrometerOrderCounter(MeterRegistry meterRegistry) {
        return Counter.builder("orders.created")
            .description("Total orders created")
            .register(meterRegistry);
    }

    @Bean
    public Timer orderProcessingTimer(MeterRegistry meterRegistry) {
        return Timer.builder("order.processing.duration")
            .description("Order processing time")
            .register(meterRegistry);
    }
}
```

```java
// 使用指标

@Service
public class OrderService {

    private final LongCounter orderCounter;
    private final LongHistogram orderValueHistogram;
    private final Counter micrometerOrderCounter;
    private final Timer orderProcessingTimer;
    private final MeterRegistry meterRegistry;

    @Autowired
    public OrderService(
            LongCounter orderCounter,
            LongHistogram orderValueHistogram,
            Counter micrometerOrderCounter,
            Timer orderProcessingTimer,
            MeterRegistry meterRegistry) {
        this.orderCounter = orderCounter;
        this.orderValueHistogram = orderValueHistogram;
        this.micrometerOrderCounter = micrometerOrderCounter;
        this.orderProcessingTimer = orderProcessingTimer;
        this.meterRegistry = meterRegistry;
    }

    @WithSpan("OrderService.createOrder")
    public Order createOrder(String userId, double amount) {
        // 记录OpenTelemetry计数器
        orderCounter.add(1,
            io.opentelemetry.api.common.Attributes.builder()
                .put("status", "created")
                .put("user_type", "premium")
                .build());

        // 记录直方图
        orderValueHistogram.record((long) amount);

        // 记录Micrometer计数器
        micrometerOrderCounter.increment();

        // 使用Timer记录耗时
        return orderProcessingTimer.recordCallable(() -> {
            // 业务逻辑
            return new Order(UUID.randomUUID().toString(), userId, amount, "CREATED");
        });
    }
}
```

---

## 4. 框架集成

### 4.1 Spring Boot Web MVC集成

```java
// config/WebMvcConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.context.Scope;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Configuration;
import org.springframework.web.servlet.config.annotation.InterceptorRegistry;
import org.springframework.web.servlet.config.annotation.WebMvcConfigurer;
import org.springframework.web.servlet.HandlerInterceptor;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

@Configuration
public class WebMvcConfig implements WebMvcConfigurer {

    private final OpenTelemetry openTelemetry;

    @Autowired
    public WebMvcConfig(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @Override
    public void addInterceptors(InterceptorRegistry registry) {
        registry.addInterceptor(new TracingInterceptor(openTelemetry));
    }
}

// 自定义拦截器
@Component
public class TracingInterceptor implements HandlerInterceptor {

    private final OpenTelemetry openTelemetry;
    private static final String SPAN_KEY = "opentelemetry.span";
    private static final String SCOPE_KEY = "opentelemetry.scope";

    public TracingInterceptor(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @Override
    public boolean preHandle(HttpServletRequest request, HttpServletResponse response, Object handler) {
        // 提取上游Trace上下文
        io.opentelemetry.context.Context parentContext = openTelemetry.getPropagators()
            .getTextMapPropagator()
            .extract(io.opentelemetry.context.Context.current(), request, new HttpServletRequestGetter());

        // 创建Span
        Span span = openTelemetry.getTracer("http-server")
            .spanBuilder(request.getMethod() + " " + request.getRequestURI())
            .setParent(parentContext)
            .setSpanKind(io.opentelemetry.api.trace.SpanKind.SERVER)
            .setAttribute("http.method", request.getMethod())
            .setAttribute("http.url", request.getRequestURL().toString())
            .setAttribute("http.target", request.getRequestURI())
            .setAttribute("http.host", request.getServerName())
            .setAttribute("http.scheme", request.getScheme())
            .setAttribute("http.client_ip", request.getRemoteAddr())
            .setAttribute("http.user_agent", request.getHeader("User-Agent"))
            .startSpan();

        // 存储到request属性
        Scope scope = span.makeCurrent();
        request.setAttribute(SPAN_KEY, span);
        request.setAttribute(SCOPE_KEY, scope);

        return true;
    }

    @Override
    public void afterCompletion(HttpServletRequest request, HttpServletResponse response,
                                Object handler, Exception ex) {
        Span span = (Span) request.getAttribute(SPAN_KEY);
        Scope scope = (Scope) request.getAttribute(SCOPE_KEY);

        if (span != null) {
            span.setAttribute("http.status_code", response.getStatus());

            if (ex != null) {
                span.recordException(ex);
                span.setStatus(StatusCode.ERROR, ex.getMessage());
            } else if (response.getStatus() >= 500) {
                span.setStatus(StatusCode.ERROR, "Server Error");
            } else if (response.getStatus() >= 400) {
                span.setStatus(StatusCode.ERROR, "Client Error");
            } else {
                span.setStatus(StatusCode.OK);
            }

            span.end();
        }

        if (scope != null) {
            scope.close();
        }
    }
}

// 提取器实现
class HttpServletRequestGetter implements io.opentelemetry.context.propagation.TextMapGetter<HttpServletRequest> {
    @Override
    public Iterable<String> keys(HttpServletRequest carrier) {
        return java.util.Collections.list(carrier.getHeaderNames());
    }

    @Override
    public String get(HttpServletRequest carrier, String key) {
        return carrier.getHeader(key);
    }
}
```

### 4.2 Spring WebClient集成

```java
// config/WebClientConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.instrumentation.spring.webflux.v5_3.SpringWebfluxTelemetry;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.web.reactive.function.client.WebClient;

@Configuration
public class WebClientConfig {

    private final OpenTelemetry openTelemetry;

    @Autowired
    public WebClientConfig(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @Bean
    public WebClient.Builder webClientBuilder() {
        SpringWebfluxTelemetry telemetry = SpringWebfluxTelemetry.create(openTelemetry);

        return WebClient.builder()
            .filter(telemetry.createWebClientExchangeFilterFunction());
    }
}

// 使用WebClient
@Service
public class PaymentClient {

    private final WebClient webClient;

    public PaymentClient(WebClient.Builder webClientBuilder) {
        this.webClient = webClientBuilder
            .baseUrl("http://payment-service")
            .build();
    }

    public Mono<PaymentResult> processPayment(String orderId, double amount) {
        return webClient.post()
            .uri("/api/payments")
            .bodyValue(new PaymentRequest(orderId, amount))
            .retrieve()
            .bodyToMono(PaymentResult.class);
    }
}
```

### 4.3 JDBC集成

```java
// 添加依赖
// <dependency>
//     <groupId>io.opentelemetry.instrumentation</groupId>
//     <artifactId>opentelemetry-jdbc</artifactId>
// </dependency>

// config/DataSourceConfig.java

package com.example.myapp.config;

import com.zaxxer.hikari.HikariConfig;
import com.zaxxer.hikari.HikariDataSource;
import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.instrumentation.jdbc.datasource.JdbcTelemetry;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import javax.sql.DataSource;

@Configuration
public class DataSourceConfig {

    private final OpenTelemetry openTelemetry;

    @Autowired
    public DataSourceConfig(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @Bean
    public DataSource dataSource() {
        HikariConfig config = new HikariConfig();
        config.setJdbcUrl("jdbc:mysql://localhost:3306/mydb");
        config.setUsername("user");
        config.setPassword("password");
        config.setMaximumPoolSize(10);

        DataSource dataSource = new HikariDataSource(config);

        // 包装以启用自动追踪
        return JdbcTelemetry.create(openTelemetry).wrap(dataSource);
    }
}
```

---

## 5. 生产环境最佳实践

### 5.1 采样配置

```java
// config/SamplingConfig.java

package com.example.myapp.config;

import io.opentelemetry.sdk.trace.samplers.Sampler;
import io.opentelemetry.sdk.trace.samplers.SamplingResult;
import io.opentelemetry.sdk.trace.samplers.ParentBasedSampler;
import io.opentelemetry.sdk.trace.samplers.TraceIdRatioBasedSampler;
import io.opentelemetry.sdk.trace.data.LinkData;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.context.Context;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.util.List;

@Configuration
public class SamplingConfig {

    @Bean
    public Sampler customSampler() {
        // 基于父Span的采样器
        Sampler baseSampler = TraceIdRatioBasedSampler.create(0.1); // 10%采样

        return Sampler.parentBased(
            Sampler.root(baseSampler),
            Sampler.alwaysOn(),    // 父Span采样时总是采样
            Sampler.alwaysOff(),   // 父Span未采样时跳过
            Sampler.alwaysOn(),    // 远程父Span采样时总是采样
            Sampler.alwaysOff()    // 远程父Span未采样时跳过
        );
    }

    // 自定义采样器：对错误和慢请求全量采样
    @Bean
    public Sampler errorAndSlowRequestSampler() {
        return new Sampler() {
            private final Sampler baseSampler = TraceIdRatioBasedSampler.create(0.1);

            @Override
            public SamplingResult shouldSample(
                    Context parentContext,
                    String traceId,
                    String name,
                    SpanKind spanKind,
                    Attributes attributes,
                    List<LinkData> parentLinks) {

                // 对错误请求全量采样
                if (name.contains("error") || name.contains("Exception")) {
                    return SamplingResult.recordAndSample();
                }

                // 对健康检查不采样
                if (name.contains("health") || name.contains("/health")) {
                    return SamplingResult.drop();
                }

                // 对关键路径全量采样
                if (name.contains("payment") || name.contains("order/create")) {
                    return SamplingResult.recordAndSample();
                }

                // 其他按基础采样率
                return baseSampler.shouldSample(parentContext, traceId, name, spanKind, attributes, parentLinks);
            }

            @Override
            public String getDescription() {
                return "ErrorAndSlowRequestSampler";
            }
        };
    }
}
```

### 5.2 优雅关闭和错误处理

```java
// config/GracefulShutdownConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import org.springframework.beans.factory.DisposableBean;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Configuration;

import java.util.concurrent.TimeUnit;

@Configuration
public class GracefulShutdownConfig implements DisposableBean {

    private final OpenTelemetry openTelemetry;

    @Autowired
    public GracefulShutdownConfig(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @Override
    public void destroy() throws Exception {
        if (openTelemetry instanceof OpenTelemetrySdk) {
            OpenTelemetrySdk sdk = (OpenTelemetrySdk) openTelemetry;

            // 关闭TracerProvider，等待导出完成
            sdk.getSdkTracerProvider().shutdown().get(10, TimeUnit.SECONDS);

            // 关闭MeterProvider
            sdk.getSdkMeterProvider().shutdown().get(10, TimeUnit.SECONDS);

            System.out.println("OpenTelemetry SDK shutdown completed");
        }
    }
}

// 安全包装Tracer
@Component
public class SafeTracer {

    private final Tracer tracer;
    private static final org.slf4j.Logger logger = org.slf4j.LoggerFactory.getLogger(SafeTracer.class);

    public SafeTracer(Tracer tracer) {
        this.tracer = tracer;
    }

    public Span startSafeSpan(String name) {
        try {
            return tracer.spanBuilder(name).startSpan();
        } catch (Exception e) {
            logger.warn("Failed to start span: {}", name, e);
            return Span.getInvalid();
        }
    }

    public void endSafeSpan(Span span) {
        try {
            if (span != null && span.isRecording()) {
                span.end();
            }
        } catch (Exception e) {
            logger.warn("Failed to end span", e);
        }
    }
}
```

### 5.3 日志集成（MDC）

```xml
<!-- logback-spring.xml -->
<configuration>
    <appender name="CONSOLE" class="ch.qos.logback.core.ConsoleAppender">
        <encoder>
            <pattern>%d{yyyy-MM-dd HH:mm:ss} [%thread] [%X{trace_id}] [%X{span_id}] %-5level %logger{36} - %msg%n</pattern>
        </encoder>
    </appender>

    <appender name="JSON" class="ch.qos.logback.core.ConsoleAppender">
        <encoder class="net.logstash.logback.encoder.LogstashEncoder">
            <provider class="io.opentelemetry.instrumentation.logback.mdc.v1_0.OpenTelemetryAppender">
                <addTraceId>true</addTraceId>
                <addSpanId>true</addSpanId>
                <addTraceFlags>true</addTraceFlags>
            </provider>
        </encoder>
    </appender>

    <root level="INFO">
        <appender-ref ref="CONSOLE" />
    </root>
</configuration>
```

```java
// config/LoggingConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.instrumentation.logback.mdc.v1_0.OpenTelemetryAppender;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Configuration;

import javax.annotation.PostConstruct;

@Configuration
public class LoggingConfig {

    private final OpenTelemetry openTelemetry;

    @Autowired
    public LoggingConfig(OpenTelemetry openTelemetry) {
        this.openTelemetry = openTelemetry;
    }

    @PostConstruct
    public void init() {
        // 安装OpenTelemetry MDC集成
        OpenTelemetryAppender.install(openTelemetry);
    }
}
```

---

## 6. 完整示例

### 6.1 完整Spring Boot应用

```java
// MyAppApplication.java

package com.example.myapp;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

@SpringBootApplication
public class MyAppApplication {
    public static void main(String[] args) {
        SpringApplication.run(MyAppApplication.class, args);
    }
}
```

```java
// controller/OrderController.java

package com.example.myapp.controller;

import com.example.myapp.model.Order;
import com.example.myapp.service.OrderService;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.instrumentation.annotations.WithSpan;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.*;

@RestController
@RequestMapping("/api/orders")
public class OrderController {

    private final OrderService orderService;

    @Autowired
    public OrderController(OrderService orderService) {
        this.orderService = orderService;
    }

    @PostMapping
    @WithSpan("OrderController.createOrder")
    public ResponseEntity<Order> createOrder(
            @RequestParam String userId,
            @RequestParam double amount) {

        // 获取当前Span并添加属性
        Span.current().setAttribute("http.request.user_id", userId);
        Span.current().setAttribute("http.request.amount", amount);

        Order order = orderService.createOrder(userId, amount);
        return ResponseEntity.ok(order);
    }

    @GetMapping("/{orderId}")
    public ResponseEntity<Order> getOrder(@PathVariable String orderId) {
        Order order = orderService.getOrder(orderId);
        if (order != null) {
            return ResponseEntity.ok(order);
        }
        return ResponseEntity.notFound().build();
    }

    @GetMapping("/health")
    public ResponseEntity<String> health() {
        return ResponseEntity.ok("OK");
    }
}
```

```yaml
# application.yml
server:
  port: 8080

spring:
  application:
    name: order-service
  datasource:
    url: jdbc:mysql://localhost:3306/orders
    username: ${DB_USER:user}
    password: ${DB_PASSWORD:password}

otel:
  service:
    name: ${spring.application.name}
    version: 1.0.0
  exporter:
    otlp:
      endpoint: ${OTEL_EXPORTER_OTLP_ENDPOINT:http://localhost:4318}
      timeout: 10s
  traces:
    sampler:
      probability: ${OTEL_TRACES_SAMPLER_PROBABILITY:0.1}
  logs:
    export:
      enabled: true

management:
  endpoints:
    web:
      exposure:
        include: health,info,metrics,prometheus
  metrics:
    export:
      prometheus:
        enabled: true
```

---

## 7. 调试技巧

### 7.1 本地开发配置

```java
// config/DevOpenTelemetryConfig.java

package com.example.myapp.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.exporter.logging.LoggingSpanExporter;
import io.opentelemetry.exporter.logging.LoggingMetricExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor;
import io.opentelemetry.sdk.metrics.SdkMeterProvider;
import io.opentelemetry.sdk.metrics.export.PeriodicMetricReader;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.Profile;

import java.time.Duration;

@Configuration
@Profile("dev")
public class DevOpenTelemetryConfig {

    @Bean
    public OpenTelemetry devOpenTelemetry() {
        // 开发环境使用Logging Exporter
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(SimpleSpanProcessor.create(LoggingSpanExporter.create()))
            .build();

        SdkMeterProvider meterProvider = SdkMeterProvider.builder()
            .registerMetricReader(PeriodicMetricReader.builder(LoggingMetricExporter.create())
                .setInterval(Duration.ofSeconds(10))
                .build())
            .build();

        return OpenTelemetrySdk.builder()
            .setTracerProvider(tracerProvider)
            .setMeterProvider(meterProvider)
            .buildAndRegisterGlobal();
    }
}
```

### 7.2 验证Trace传播

```java
// util/TraceVerifier.java

package com.example.myapp.util;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanContext;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TraceVerifier {

    private static final Logger logger = LoggerFactory.getLogger(TraceVerifier.class);

    public static void logCurrentTraceInfo() {
        Span span = Span.current();
        SpanContext spanContext = span.getSpanContext();

        if (spanContext.isValid()) {
            logger.info("Current Trace Info:");
            logger.info("  TraceId: {}", spanContext.getTraceId());
            logger.info("  SpanId: {}", spanContext.getSpanId());
            logger.info("  Sampled: {}", spanContext.isSampled());
            logger.info("  TraceFlags: {}", spanContext.getTraceFlags());
        } else {
            logger.warn("No valid trace context found");
        }
    }
}
```

### 7.3 测试Span创建

```java
// test/OrderServiceTest.java

package com.example.myapp.service;

import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.data.SpanData;
import io.opentelemetry.sdk.trace.export.InMemorySpanExporter;
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class OrderServiceTest {

    private InMemorySpanExporter spanExporter;
    private OrderService orderService;

    @BeforeEach
    void setUp() {
        spanExporter = InMemorySpanExporter.create();

        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(SimpleSpanProcessor.create(spanExporter))
            .build();

        OpenTelemetrySdk openTelemetry = OpenTelemetrySdk.builder()
            .setTracerProvider(tracerProvider)
            .build();

        orderService = new OrderService(
            openTelemetry.getTracer("test"),
            mock(PaymentService.class)
        );
    }

    @Test
    void testCreateOrderCreatesSpan() {
        // 执行
        orderService.createOrder("user123", 99.99);

        // 验证
        List<SpanData> spans = spanExporter.getFinishedSpanItems();
        assertEquals(1, spans.size());

        SpanData span = spans.get(0);
        assertEquals("OrderService.createOrder", span.getName());
        assertNotNull(span.getAttributes().get(io.opentelemetry.api.common.AttributeKey.stringKey("order.id")));
    }
}
```

---

## 8. 参考资源

- [OpenTelemetry Java官方文档](https://opentelemetry.io/docs/languages/java/)
- [OpenTelemetry Java SDK GitHub](https://github.com/open-telemetry/opentelemetry-java)
- [OpenTelemetry Java Instrumentation](https://github.com/open-telemetry/opentelemetry-java-instrumentation)
- [Micrometer文档](https://micrometer.io/docs)
- [Spring Boot Actuator文档](https://docs.spring.io/spring-boot/docs/current/reference/html/actuator.html)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
