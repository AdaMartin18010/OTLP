package main

import (
	"context"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.27.0"
)

func main() {
	ctx := context.Background()

	// 创建OTLP gRPC导出器
	// 连接到本地运行的OpenTelemetry Collector (端口4317)
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint("localhost:4317"),
		otlptracegrpc.WithInsecure(), // 开发环境使用非加密连接
	)
	if err != nil {
		log.Fatalf("Failed to create OTLP trace exporter: %v", err)
	}

	// 创建Resource，描述服务的元数据
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("hello-trace-go"),
			semconv.ServiceVersion("1.0.0"),
			attribute.String("environment", "development"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	// 创建TracerProvider
	// TracerProvider是创建Tracer的工厂
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter), // 使用批处理导出器
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()), // 采样策略：全量采样
	)
	defer func() {
		if err := tp.Shutdown(ctx); err != nil {
			log.Printf("Error shutting down tracer provider: %v", err)
		}
	}()

	// 设置全局TracerProvider
	otel.SetTracerProvider(tp)

	log.Println("Starting hello trace example...")

	// 获取Tracer
	tracer := tp.Tracer("hello-trace")

	// 创建根Span
	ctx, span := tracer.Start(ctx, "hello-operation")
	span.SetAttributes(
		attribute.String("greeting", "Hello OTLP!"),
		attribute.String("language", "Go"),
		attribute.Int("example.version", 1),
	)

	// 模拟一些工作
	log.Println("Doing some work...")
	time.Sleep(100 * time.Millisecond)

	// 创建子Span
	_, childSpan := tracer.Start(ctx, "sub-operation")
	childSpan.SetAttributes(
		attribute.String("operation", "processing"),
		attribute.Bool("success", true),
	)
	time.Sleep(50 * time.Millisecond)
	childSpan.End()

	// 结束根Span
	span.End()

	log.Println("Trace sent successfully!")
	log.Println("View traces at: http://localhost:16686")

	// 等待确保所有span都已导出
	time.Sleep(2 * time.Second)
}
