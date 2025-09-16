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
	metricSDK "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

type UserData struct {
	ID    string `json:"id"`
	Name  string `json:"name"`
	Email string `json:"email"`
	Role  string `json:"role"`
}

type BusinessResult struct {
	UserID      string    `json:"user_id"`
	ProcessedAt time.Time `json:"processed_at"`
	Status      string    `json:"status"`
	Data        string    `json:"data"`
}

type ApiResponse struct {
	Status  int    `json:"status"`
	Message string `json:"message"`
	Data    string `json:"data"`
}

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
			otlptracehttp.WithTimeout(10*time.Second),
			otlptracehttp.WithHeaders(map[string]string{
				"Authorization": "Bearer token",
			}),
		)
	} else {
		addr := stripScheme(endpoint)
		opts := []otlptracegrpc.Option{
			otlptracegrpc.WithEndpoint(addr),
			otlptracegrpc.WithTimeout(10 * time.Second),
			otlptracegrpc.WithHeaders(map[string]string{
				"Authorization": "Bearer token",
			}),
		}
		if insecure {
			opts = append(opts, otlptracegrpc.WithInsecure())
		}
		exp, err = otlptracegrpc.New(ctx, opts...)
	}
	if err != nil {
		return nil, err
	}

	// 配置资源
	res, err := resource.Merge(resource.Default(), resource.NewWithAttributes(
		semconv.SchemaURL,
		semconv.ServiceName("advanced-go-service"),
		semconv.ServiceVersion("1.0.0"),
		semconv.ServiceInstanceID("instance-1"),
		semconv.DeploymentEnvironment("production"),
		semconv.HostName("go-server"),
		semconv.HostArch("amd64"),
		semconv.OSName("linux"),
		semconv.OSVersion("5.4.0"),
	))
	if err != nil {
		return nil, err
	}

	// 配置采样器
	sampler := sdktrace.TraceIDRatioBased(0.1) // 10%采样率

	// 配置TracerProvider
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exp, sdktrace.WithBatchTimeout(time.Second)),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sampler),
		sdktrace.WithSpanLimits(sdktrace.SpanLimits{
			AttributeCountLimit:       128,
			EventCountLimit:           128,
			LinkCountLimit:            128,
			AttributeValueLengthLimit: 1024,
			EventAttributeCountLimit:  128,
			LinkAttributeCountLimit:   128,
		}),
	)

	otel.SetTracerProvider(tp)
	return tp.Shutdown, nil
}

func initMeter() (*metricSDK.MeterProvider, metric.Int64Counter, metric.Float64Histogram) {
	serviceName := getenv("OTEL_SERVICE_NAME", "advanced-go-service")
	mp := metricSDK.NewMeterProvider()
	meter := mp.Meter(serviceName)

	counter, _ := meter.Int64Counter("business_operations_total")
	histogram, _ := meter.Float64Histogram("business_operation_duration_seconds")

	return mp, counter, histogram
}

func main() {
	ctx := context.Background()
	shutdown, err := initTracer(ctx)
	if err != nil {
		log.Fatal(err)
	}
	defer func() { _ = shutdown(context.Background()) }()

	mp, counter, histogram := initMeter()
	defer func() { _ = mp.Shutdown(context.Background()) }()

	serviceName := getenv("OTEL_SERVICE_NAME", "advanced-go-service")
	tr := otel.Tracer(serviceName)

	// 模拟业务逻辑
	simulateBusinessLogic(ctx, tr, counter, histogram)
}

func simulateBusinessLogic(ctx context.Context, tr trace.Tracer, counter metric.Int64Counter, histogram metric.Float64Histogram) {
	ctx, span := tr.Start(ctx, "business_logic", trace.WithSpanKind(trace.SpanKindServer))
	defer span.End()

	span.SetAttributes(
		attribute.String("operation", "main"),
		attribute.String("service.name", "advanced-go-service"),
	)

	log.Println("开始业务逻辑处理")

	// 模拟用户认证
	authResult := authenticateUser(ctx, tr, "user123", "password")
	if !authResult {
		log.Println("用户认证失败")
		return
	}

	// 模拟数据库查询
	userData := queryUserData(ctx, tr, "user123")
	log.Printf("查询用户数据完成: %s", userData.Name)

	// 模拟业务处理
	result := processBusinessLogic(ctx, tr, &userData)
	log.Printf("业务处理完成: %s", result.Status)

	// 模拟外部API调用
	apiResponse := callExternalAPI(ctx, tr, &result)
	log.Printf("外部API调用完成: %d", apiResponse.Status)

	// 记录指标
	counter.Add(ctx, 1, attribute.String("operation", "business_logic"))
	histogram.Record(ctx, time.Since(time.Now()).Seconds())

	log.Println("业务逻辑处理完成")
}

func authenticateUser(ctx context.Context, tr trace.Tracer, username, password string) bool {
	ctx, span := tr.Start(ctx, "authenticate_user", trace.WithSpanKind(trace.SpanKindInternal))
	defer span.End()

	span.SetAttributes(
		attribute.String("user", username),
		attribute.String("auth.method", "password"),
	)

	log.Println("开始用户认证")

	// 模拟认证延迟
	time.Sleep(100 * time.Millisecond)

	// 模拟认证逻辑
	isValid := username == "user123" && password == "password"

	span.SetAttributes(
		attribute.Bool("auth.success", isValid),
		attribute.String("auth.result", func() string {
			if isValid {
				return "success"
			}
			return "failure"
		}()),
	)

	if isValid {
		log.Println("用户认证成功")
	} else {
		log.Println("用户认证失败")
	}

	return isValid
}

func queryUserData(ctx context.Context, tr trace.Tracer, userID string) UserData {
	ctx, span := tr.Start(ctx, "query_user_data", trace.WithSpanKind(trace.SpanKindClient))
	defer span.End()

	span.SetAttributes(
		attribute.String("user.id", userID),
		attribute.String("db.system", "postgresql"),
		attribute.String("db.operation", "SELECT"),
		attribute.String("db.sql.table", "users"),
	)

	log.Println("开始查询用户数据")

	// 模拟数据库查询延迟
	time.Sleep(200 * time.Millisecond)

	// 模拟数据库查询
	userData := UserData{
		ID:    userID,
		Name:  "John Doe",
		Email: "john@example.com",
		Role:  "user",
	}

	span.SetAttributes(
		attribute.String("user.name", userData.Name),
		attribute.String("user.email", userData.Email),
		attribute.String("user.role", userData.Role),
	)

	log.Printf("用户数据查询完成: %s", userData.Name)

	return userData
}

func processBusinessLogic(ctx context.Context, tr trace.Tracer, userData *UserData) BusinessResult {
	ctx, span := tr.Start(ctx, "process_business_logic", trace.WithSpanKind(trace.SpanKindInternal))
	defer span.End()

	span.SetAttributes(
		attribute.String("user.id", userData.ID),
		attribute.String("business.operation", "process"),
	)

	log.Println("开始业务逻辑处理")

	// 模拟业务处理延迟
	time.Sleep(300 * time.Millisecond)

	// 模拟业务逻辑
	result := BusinessResult{
		UserID:      userData.ID,
		ProcessedAt: time.Now(),
		Status:      "success",
		Data:        "processed_data",
	}

	span.SetAttributes(
		attribute.String("business.status", result.Status),
		attribute.String("business.data", result.Data),
	)

	log.Printf("业务逻辑处理完成: %s", result.Status)

	return result
}

func callExternalAPI(ctx context.Context, tr trace.Tracer, data *BusinessResult) ApiResponse {
	ctx, span := tr.Start(ctx, "call_external_api", trace.WithSpanKind(trace.SpanKindClient))
	defer span.End()

	span.SetAttributes(
		attribute.String("user.id", data.UserID),
		attribute.String("http.method", "POST"),
		attribute.String("http.url", "https://api.example.com/process"),
		attribute.String("http.scheme", "https"),
		attribute.String("http.host", "api.example.com"),
	)

	log.Println("开始调用外部API")

	// 模拟API调用延迟
	time.Sleep(150 * time.Millisecond)

	// 模拟API调用
	response := ApiResponse{
		Status:  200,
		Message: "success",
		Data:    "api_response_data",
	}

	span.SetAttributes(
		attribute.Int("http.status_code", response.Status),
		attribute.String("http.response.message", response.Message),
	)

	log.Printf("外部API调用完成: %d", response.Status)

	return response
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
