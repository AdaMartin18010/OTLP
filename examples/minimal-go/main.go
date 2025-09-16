package main

import (
	"context"
	"log"
	"os"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	metricSDK "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

func initTracer(ctx context.Context) (func(context.Context) error, error) {
	endpoint := getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317")
	protocol := getenv("OTEL_EXPORTER_OTLP_PROTOCOL", "grpc")
	insecure := getenv("OTEL_EXPORTER_OTLP_INSECURE", "true") == "true"

	var (
		exp sdktrace.SpanExporter
		err error
	)

	if protocol == "http" || protocol == "http/protobuf" {
		exp, err = otlptracehttp.New(ctx,
			otlptracehttp.WithEndpoint(endpoint),
			otlptracehttp.WithInsecure(),
		)
	} else {
		addr := stripScheme(endpoint)
		opts := []otlptracegrpc.Option{otlptracegrpc.WithEndpoint(addr)}
		if insecure {
			opts = append(opts, otlptracegrpc.WithInsecure())
		}
		exp, err = otlptracegrpc.New(ctx, opts...)
	}
	if err != nil {
		return nil, err
	}
	serviceName := getenv("OTEL_SERVICE_NAME", "minimal-go")
	res, _ := resource.Merge(resource.Default(), resource.NewWithAttributes(
		"",
		attribute.String("service.name", serviceName),
	))
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exp),
		sdktrace.WithResource(res),
	)
	otel.SetTracerProvider(tp)
	otel.SetTextMapPropagator(propagation.TraceContext{})
	return tp.Shutdown, nil
}

func initMeter() (*metricSDK.MeterProvider, metric.Int64Counter) {
	serviceName := getenv("OTEL_SERVICE_NAME", "minimal-go")
	mp := metricSDK.NewMeterProvider()
	meter := mp.Meter(serviceName)
	counter, _ := meter.Int64Counter("demo_requests")
	return mp, counter
}

func main() {
	ctx := context.Background()
	shutdown, err := initTracer(ctx)
	if err != nil {
		log.Fatal(err)
	}
	defer func() { _ = shutdown(context.Background()) }()

	mp, counter := initMeter()
	defer func() { _ = mp.Shutdown(context.Background()) }()

	serviceName := getenv("OTEL_SERVICE_NAME", "minimal-go")
	tr := otel.Tracer(serviceName)
	ctx, span := tr.Start(ctx, "demo-span", trace.WithSpanKind(trace.SpanKindServer))
	span.SetAttributes(attribute.String("demo.attr", "value"))
	counter.Add(ctx, 1)
	time.Sleep(100 * time.Millisecond)
	span.End()

	log.Printf("sent one span and one metric via OTLP to %s using %s\n", getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317"), getenv("OTEL_EXPORTER_OTLP_PROTOCOL", "grpc"))
}

func getenv(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

func stripScheme(s string) string {
	if len(s) >= 7 && s[:7] == "http://" {
		return s[7:]
	}
	if len(s) >= 8 && s[:8] == "https://" {
		return s[8:]
	}
	return s
}
