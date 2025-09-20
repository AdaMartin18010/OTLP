package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
    "go.opentelemetry.io/otel/trace"
)

// eBPF 跟踪器模拟
type eBPFTracer struct {
    tracer trace.Tracer
}

func NeweBPFTracer(tracer trace.Tracer) *eBPFTracer {
    return &eBPFTracer{tracer: tracer}
}

func (e *eBPFTracer) TraceFunctionCall(funcName string) {
    ctx, span := e.tracer.Start(context.Background(), fmt.Sprintf("ebpf_trace_%s", funcName))
    defer span.End()
    
    span.SetAttributes(
        attribute.String("ebpf.function", funcName),
        attribute.String("ebpf.trace_type", "zero_code"),
        attribute.Bool("ebpf.automatic", true),
    )
    
    // 模拟 eBPF 跟踪逻辑
    time.Sleep(10 * time.Millisecond)
    
    span.AddEvent("ebpf_trace_completed", trace.WithAttributes(
        attribute.String("ebpf.status", "success"),
    ))
}

func main() {
    // 配置资源
    res, err := resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceName("crosstrace-demo"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("development"),
        ),
    )
    if err != nil {
        log.Fatalf("创建资源失败: %v", err)
    }

    // 配置导出器
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatalf("创建导出器失败: %v", err)
    }

    // 配置 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)),
    )
    defer tp.Shutdown(context.Background())

    otel.SetTracerProvider(tp)
    tracer := otel.Tracer("crosstrace-demo")

    // 创建 eBPF 跟踪器
    ebpfTracer := NeweBPFTracer(tracer)

    // 模拟函数调用跟踪
    functions := []string{"http_handler", "database_query", "cache_get", "external_api_call"}
    
    for _, funcName := range functions {
        ebpfTracer.TraceFunctionCall(funcName)
        time.Sleep(100 * time.Millisecond)
    }

    fmt.Println("CrossTrace 演示完成")
}
