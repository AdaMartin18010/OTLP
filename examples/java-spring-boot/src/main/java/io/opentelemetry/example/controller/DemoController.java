package io.opentelemetry.example.controller;

import io.micrometer.core.instrument.Counter;
import io.micrometer.core.instrument.MeterRegistry;
import io.micrometer.core.instrument.Timer;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.service.BusinessService;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.*;

import java.time.Duration;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

/**
 * 演示控制器 - 展示Traces, Metrics, Logs的集成
 */
@Slf4j
@RestController
@RequestMapping("/api")
public class DemoController {

    @Autowired
    private Tracer tracer;

    @Autowired
    private BusinessService businessService;

    @Autowired
    private MeterRegistry meterRegistry;

    private final Counter requestCounter;
    private final Timer requestTimer;
    private final Random random = new Random();

    public DemoController(MeterRegistry meterRegistry) {
        this.meterRegistry = meterRegistry;
        
        // 创建自定义指标
        this.requestCounter = Counter.builder("api.requests.total")
            .description("Total number of API requests")
            .tag("endpoint", "/api/hello")
            .register(meterRegistry);
        
        this.requestTimer = Timer.builder("api.request.duration")
            .description("API request duration")
            .tag("endpoint", "/api/hello")
            .register(meterRegistry);
    }

    /**
     * Hello端点 - 演示基本的Trace和Metric
     */
    @GetMapping("/hello")
    public Map<String, Object> hello(@RequestParam(defaultValue = "World") String name) {
        // 记录指标
        requestCounter.increment();
        
        return requestTimer.record(() -> {
            // 创建span
            Span span = tracer.spanBuilder("handle-hello-request")
                .setSpanKind(io.opentelemetry.api.trace.SpanKind.SERVER)
                .startSpan();
            
            try (Scope scope = span.makeCurrent()) {
                // 添加span属性
                span.setAttribute("request.name", name);
                span.setAttribute("request.length", name.length());
                
                // 记录日志（会自动关联到当前trace）
                log.info("Processing hello request for name: {}", name);
                
                // 调用业务逻辑
                String result = businessService.processGreeting(name);
                
                // 记录事件
                span.addEvent("greeting_processed");
                
                Map<String, Object> response = new HashMap<>();
                response.put("message", result);
                response.put("timestamp", System.currentTimeMillis());
                response.put("traceId", span.getSpanContext().getTraceId());
                
                log.info("Hello request completed successfully");
                return response;
                
            } catch (Exception e) {
                span.recordException(e);
                span.setAttribute("error", true);
                log.error("Error processing hello request", e);
                throw e;
            } finally {
                span.end();
            }
        });
    }

    /**
     * Slow端点 - 演示慢请求追踪
     */
    @GetMapping("/slow")
    public Map<String, Object> slowEndpoint() {
        Span span = tracer.spanBuilder("slow-operation")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            log.info("Starting slow operation");
            
            // 模拟慢操作
            int delay = 1000 + random.nextInt(2000);
            span.setAttribute("delay_ms", delay);
            
            Thread.sleep(delay);
            
            log.info("Slow operation completed");
            
            Map<String, Object> response = new HashMap<>();
            response.put("duration_ms", delay);
            response.put("message", "Operation completed");
            
            return response;
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
            throw new RuntimeException("Operation interrupted", e);
        } finally {
            span.end();
        }
    }

    /**
     * Error端点 - 演示错误追踪
     */
    @GetMapping("/error")
    public Map<String, Object> errorEndpoint() {
        Span span = tracer.spanBuilder("error-operation")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            log.warn("Simulating error condition");
            
            span.setAttribute("error.type", "simulated");
            
            // 模拟错误
            throw new RuntimeException("Simulated error for testing");
            
        } catch (Exception e) {
            // 记录异常到span
            span.recordException(e);
            span.setAttribute("error", true);
            
            // 记录错误日志
            log.error("Error occurred in error endpoint", e);
            
            // 重新抛出
            throw e;
            
        } finally {
            span.end();
        }
    }

    /**
     * Chain端点 - 演示嵌套span和分布式追踪
     */
    @GetMapping("/chain")
    public Map<String, Object> chainedOperations() {
        Span parentSpan = tracer.spanBuilder("chained-operation")
            .startSpan();
        
        try (Scope parentScope = parentSpan.makeCurrent()) {
            log.info("Starting chained operations");
            
            // 第一个子操作
            businessService.operation1();
            
            // 第二个子操作
            businessService.operation2();
            
            // 第三个子操作
            businessService.operation3();
            
            log.info("All chained operations completed");
            
            Map<String, Object> response = new HashMap<>();
            response.put("status", "success");
            response.put("operations", 3);
            
            return response;
            
        } finally {
            parentSpan.end();
        }
    }

    /**
     * Metrics端点 - 查看当前指标
     */
    @GetMapping("/metrics")
    public Map<String, Object> getMetrics() {
        Map<String, Object> metrics = new HashMap<>();
        metrics.put("request_count", requestCounter.count());
        metrics.put("request_duration_mean", requestTimer.mean(java.util.concurrent.TimeUnit.MILLISECONDS));
        metrics.put("request_duration_max", requestTimer.max(java.util.concurrent.TimeUnit.MILLISECONDS));
        
        return metrics;
    }

    /**
     * Health端点
     */
    @GetMapping("/health")
    public Map<String, String> health() {
        return Map.of("status", "UP");
    }
}

