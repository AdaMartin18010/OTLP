package io.opentelemetry.example.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.Random;

/**
 * 业务服务 - 演示嵌套span和业务逻辑追踪
 */
@Slf4j
@Service
public class BusinessService {

    @Autowired
    private Tracer tracer;

    private final Random random = new Random();

    /**
     * 处理问候逻辑
     */
    public String processGreeting(String name) {
        Span span = tracer.spanBuilder("process-greeting")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("name", name);
            
            log.debug("Processing greeting for: {}", name);
            
            // 模拟处理延迟
            Thread.sleep(50 + random.nextInt(100));
            
            String result = "Hello, " + name + "!";
            span.setAttribute("result.length", result.length());
            
            return result;
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
            throw new RuntimeException("Interrupted", e);
        } finally {
            span.end();
        }
    }

    /**
     * 第一个操作
     */
    public void operation1() {
        Span span = tracer.spanBuilder("operation-1")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            log.info("Executing operation 1");
            
            // 模拟数据库查询
            simulateDatabaseQuery("users");
            
            Thread.sleep(100);
            span.addEvent("operation_1_completed");
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }

    /**
     * 第二个操作
     */
    public void operation2() {
        Span span = tracer.spanBuilder("operation-2")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            log.info("Executing operation 2");
            
            // 模拟外部API调用
            simulateExternalApiCall("https://api.example.com/data");
            
            Thread.sleep(150);
            span.addEvent("operation_2_completed");
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }

    /**
     * 第三个操作
     */
    public void operation3() {
        Span span = tracer.spanBuilder("operation-3")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            log.info("Executing operation 3");
            
            // 模拟缓存查询
            simulateCacheQuery("user:123");
            
            Thread.sleep(50);
            span.addEvent("operation_3_completed");
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }

    /**
     * 模拟数据库查询
     */
    private void simulateDatabaseQuery(String table) {
        Span span = tracer.spanBuilder("db.query")
            .setSpanKind(io.opentelemetry.api.trace.SpanKind.CLIENT)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("db.system", "postgresql");
            span.setAttribute("db.table", table);
            span.setAttribute("db.operation", "SELECT");
            
            log.debug("Querying database table: {}", table);
            
            Thread.sleep(20 + random.nextInt(30));
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }

    /**
     * 模拟外部API调用
     */
    private void simulateExternalApiCall(String url) {
        Span span = tracer.spanBuilder("http.request")
            .setSpanKind(io.opentelemetry.api.trace.SpanKind.CLIENT)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("http.method", "GET");
            span.setAttribute("http.url", url);
            span.setAttribute("http.status_code", 200);
            
            log.debug("Calling external API: {}", url);
            
            Thread.sleep(100 + random.nextInt(100));
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }

    /**
     * 模拟缓存查询
     */
    private void simulateCacheQuery(String key) {
        Span span = tracer.spanBuilder("cache.get")
            .setSpanKind(io.opentelemetry.api.trace.SpanKind.CLIENT)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("cache.system", "redis");
            span.setAttribute("cache.key", key);
            span.setAttribute("cache.hit", true);
            
            log.debug("Getting from cache: {}", key);
            
            Thread.sleep(5 + random.nextInt(10));
            
        } catch (InterruptedException e) {
            span.recordException(e);
            Thread.currentThread().interrupt();
        } finally {
            span.end();
        }
    }
}

