package main

import (
	"context"
	"fmt"
	"log"
	"math/rand"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
)

// Order represents an e-commerce order
type Order struct {
	ID            string
	Status        OrderStatus
	TotalAmount   float64
	ItemCount     int
	UserTier      UserTier
	PromotionCode string
}

// OrderStatus represents the status of an order
type OrderStatus string

const (
	OrderStatusPending   OrderStatus = "pending"
	OrderStatusPaid      OrderStatus = "paid"
	OrderStatusShipped   OrderStatus = "shipped"
	OrderStatusDelivered OrderStatus = "delivered"
	OrderStatusCancelled OrderStatus = "cancelled"
)

// UserTier represents user membership tiers
type UserTier string

const (
	UserTierFree     UserTier = "free"
	UserTierSilver   UserTier = "silver"
	UserTierGold     UserTier = "gold"
	UserTierPlatinum UserTier = "platinum"
)

var tracer trace.Tracer

func main() {
	// Initialize OpenTelemetry
	ctx := context.Background()
	shutdown, err := initTracer(ctx)
	if err != nil {
		log.Fatal(err)
	}
	defer shutdown(ctx)

	// Get tracer
	tracer = otel.Tracer("myshop.order-service")

	log.Println("🛒 E-commerce Order Tracking Example Started")
	log.Println("📊 Sending order processing traces to OTLP Collector...")
	log.Println("🔗 Connect to http://localhost:16686 to view traces (Jaeger UI)")
	log.Println()

	// Simulate order processing
	for i := 1; i <= 5; i++ {
		order := generateRandomOrder(i)
		fmt.Printf("Processing Order %d: ID=%s, Amount=$%.2f, User=%s\n",
			i, order.ID, order.TotalAmount, order.UserTier)

		if err := processOrder(ctx, order); err != nil {
			log.Printf("Error processing order %s: %v\n", order.ID, err)
		}

		time.Sleep(2 * time.Second)
	}

	log.Println()
	log.Println("✅ All orders processed successfully!")
	log.Println("📊 Check Jaeger UI to see the traces")
}

// initTracer initializes OpenTelemetry tracer with OTLP exporter
func initTracer(ctx context.Context) (func(context.Context) error, error) {
	// Create OTLP trace exporter
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint("localhost:4317"),
		otlptracegrpc.WithInsecure(),
		otlptracegrpc.WithDialOption(grpc.WithTransportCredentials(insecure.NewCredentials())),
	)
	if err != nil {
		return nil, fmt.Errorf("failed to create OTLP trace exporter: %w", err)
	}

	// Create resource with service information
	res, err := resource.New(ctx,
		resource.WithAttributes(
			// Standard service attributes
			semconv.ServiceName("order-service"),
			semconv.ServiceVersion("1.2.3"),
			semconv.ServiceNamespace("myshop"),
			semconv.DeploymentEnvironment("production"),

			// Custom resource attributes
			attribute.String("service.team", "e-commerce"),
			attribute.String("service.region", "us-east-1"),
		),
	)
	if err != nil {
		return nil, fmt.Errorf("failed to create resource: %w", err)
	}

	// Create trace provider
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()), // For demo, always sample
	)

	// Set global trace provider
	otel.SetTracerProvider(tp)

	// Return shutdown function
	return tp.Shutdown, nil
}

// processOrder processes an e-commerce order with full OpenTelemetry instrumentation
func processOrder(ctx context.Context, order *Order) error {
	// Start root span for order processing
	ctx, span := tracer.Start(ctx, "process_order",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			// Standard HTTP attributes (simulated)
			semconv.HTTPMethod("POST"),
			semconv.HTTPRoute("/api/orders"),
			semconv.HTTPStatusCode(201),
			semconv.HTTPTarget("/api/orders"),

			// Custom business attributes (with vendor prefix)
			attribute.String("myshop.order.id", order.ID),
			attribute.String("myshop.order.status", string(order.Status)),
			attribute.Float64("myshop.order.total_amount", order.TotalAmount),
			attribute.Int("myshop.order.item_count", order.ItemCount),
			attribute.String("myshop.user.tier", string(order.UserTier)),
		),
	)
	defer span.End()

	// Add promotion code if exists (conditional attribute)
	if order.PromotionCode != "" {
		span.SetAttributes(
			attribute.String("myshop.promotion.code", order.PromotionCode),
			attribute.Float64("myshop.promotion.discount_percent", 20.0),
		)
	}

	// Record event: Order created
	span.AddEvent("order_created", trace.WithAttributes(
		attribute.String("myshop.order.id", order.ID),
		attribute.Int("myshop.order.item_count", order.ItemCount),
	))

	// Step 1: Validate order
	if err := validateOrder(ctx, order); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "Order validation failed")
		return fmt.Errorf("validation failed: %w", err)
	}

	// Step 2: Process payment
	if err := processPayment(ctx, order); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "Payment processing failed")
		return fmt.Errorf("payment failed: %w", err)
	}

	// Step 3: Update inventory
	if err := updateInventory(ctx, order); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "Inventory update failed")
		return fmt.Errorf("inventory update failed: %w", err)
	}

	// Step 4: Send notification
	if err := sendNotification(ctx, order); err != nil {
		// Non-critical error, log but don't fail
		span.AddEvent("notification_failed", trace.WithAttributes(
			attribute.String("error", err.Error()),
		))
	}

	// Update order status
	order.Status = OrderStatusPaid
	span.SetAttributes(attribute.String("myshop.order.status", string(order.Status)))

	// Record event: Order completed
	span.AddEvent("order_completed", trace.WithAttributes(
		attribute.String("myshop.order.id", order.ID),
		attribute.String("myshop.order.status", string(order.Status)),
	))

	span.SetStatus(codes.Ok, "Order processed successfully")
	return nil
}

// validateOrder validates the order
func validateOrder(ctx context.Context, order *Order) error {
	_, span := tracer.Start(ctx, "validate_order",
		trace.WithAttributes(
			attribute.String("myshop.order.id", order.ID),
			attribute.Float64("myshop.order.total_amount", order.TotalAmount),
		),
	)
	defer span.End()

	// Simulate validation
	time.Sleep(50 * time.Millisecond)

	// Validate amount
	if order.TotalAmount <= 0 {
		err := fmt.Errorf("invalid order amount: $%.2f", order.TotalAmount)
		span.RecordError(err)
		span.SetStatus(codes.Error, "Invalid amount")
		return err
	}

	// Validate item count
	if order.ItemCount <= 0 {
		err := fmt.Errorf("invalid item count: %d", order.ItemCount)
		span.RecordError(err)
		span.SetStatus(codes.Error, "Invalid item count")
		return err
	}

	span.AddEvent("validation_complete", trace.WithAttributes(
		attribute.String("validation.result", "success"),
	))
	span.SetStatus(codes.Ok, "Validation passed")
	return nil
}

// processPayment processes payment for the order
func processPayment(ctx context.Context, order *Order) error {
	_, span := tracer.Start(ctx, "process_payment",
		trace.WithAttributes(
			attribute.String("myshop.order.id", order.ID),
			attribute.Float64("myshop.payment.amount", order.TotalAmount),
			attribute.String("myshop.payment.method", "credit_card"),
		),
	)
	defer span.End()

	// Simulate payment processing
	time.Sleep(100 * time.Millisecond)

	// Simulate payment gateway call
	if err := callPaymentGateway(ctx, order); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "Payment gateway error")
		return err
	}

	span.AddEvent("payment_authorized", trace.WithAttributes(
		attribute.String("myshop.payment.transaction_id", fmt.Sprintf("TXN-%s", order.ID)),
		attribute.String("myshop.payment.status", "authorized"),
	))

	span.SetStatus(codes.Ok, "Payment processed")
	return nil
}

// callPaymentGateway simulates calling an external payment gateway
func callPaymentGateway(ctx context.Context, order *Order) error {
	_, span := tracer.Start(ctx, "call_payment_gateway",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			// Standard HTTP client attributes
			semconv.HTTPMethod("POST"),
			semconv.HTTPTarget("/v1/payments"),
			semconv.HTTPHost("payment-gateway.example.com"),
			semconv.HTTPScheme("https"),
			semconv.HTTPStatusCode(200),

			// Payment specific attributes
			attribute.Float64("myshop.payment.amount", order.TotalAmount),
			attribute.String("myshop.payment.currency", "USD"),
		),
	)
	defer span.End()

	// Simulate network call
	time.Sleep(150 * time.Millisecond)

	span.SetStatus(codes.Ok, "Gateway call successful")
	return nil
}

// updateInventory updates inventory after order
func updateInventory(ctx context.Context, order *Order) error {
	_, span := tracer.Start(ctx, "update_inventory",
		trace.WithAttributes(
			attribute.String("myshop.order.id", order.ID),
			attribute.Int("myshop.order.item_count", order.ItemCount),
		),
	)
	defer span.End()

	// Simulate database update
	_, dbSpan := tracer.Start(ctx, "db.update",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			// Standard database attributes
			semconv.DBSystem("postgresql"),
			semconv.DBName("myshop"),
			semconv.DBOperation("UPDATE"),
			semconv.DBSQLTable("inventory"),
			attribute.String("db.statement", "UPDATE inventory SET quantity = quantity - ? WHERE product_id = ?"),

			// Database connection info
			attribute.String("server.address", "db.myshop.com"),
			attribute.Int("server.port", 5432),
		),
	)
	time.Sleep(80 * time.Millisecond)
	dbSpan.SetStatus(codes.Ok, "Inventory updated")
	dbSpan.End()

	span.AddEvent("inventory_updated", trace.WithAttributes(
		attribute.Int("myshop.inventory.items_deducted", order.ItemCount),
	))

	span.SetStatus(codes.Ok, "Inventory updated")
	return nil
}

// sendNotification sends order confirmation notification
func sendNotification(ctx context.Context, order *Order) error {
	_, span := tracer.Start(ctx, "send_notification",
		trace.WithAttributes(
			attribute.String("myshop.order.id", order.ID),
			attribute.String("myshop.notification.type", "order_confirmation"),
			attribute.String("myshop.notification.channel", "email"),
		),
	)
	defer span.End()

	// Simulate notification service call
	_, kafkaSpan := tracer.Start(ctx, "publish_to_kafka",
		trace.WithSpanKind(trace.SpanKindProducer),
		trace.WithAttributes(
			// Standard messaging attributes
			semconv.MessagingSystem("kafka"),
			semconv.MessagingDestinationName("order-notifications"),
			semconv.MessagingOperation("publish"),
			attribute.String("messaging.message.id", fmt.Sprintf("MSG-%s", order.ID)),

			// Kafka specific attributes
			attribute.String("kafka.message.key", order.ID),
			attribute.Int("kafka.partition", 3),
		),
	)
	time.Sleep(30 * time.Millisecond)
	kafkaSpan.SetStatus(codes.Ok, "Message published")
	kafkaSpan.End()

	span.AddEvent("notification_sent", trace.WithAttributes(
		attribute.String("myshop.notification.status", "sent"),
	))

	span.SetStatus(codes.Ok, "Notification sent")
	return nil
}

// generateRandomOrder generates a random order for demo
func generateRandomOrder(id int) *Order {
	rand.Seed(time.Now().UnixNano())

	// Random user tiers
	tiers := []UserTier{UserTierFree, UserTierSilver, UserTierGold, UserTierPlatinum}
	tier := tiers[rand.Intn(len(tiers))]

	// Random order amount based on tier
	var amount float64
	switch tier {
	case UserTierPlatinum:
		amount = 100 + rand.Float64()*400 // $100-500
	case UserTierGold:
		amount = 50 + rand.Float64()*150 // $50-200
	case UserTierSilver:
		amount = 20 + rand.Float64()*80 // $20-100
	default:
		amount = 10 + rand.Float64()*40 // $10-50
	}

	// Random promotion code (30% chance)
	promotionCode := ""
	if rand.Float64() < 0.3 {
		promotionCode = "SUMMER2024"
	}

	return &Order{
		ID:            fmt.Sprintf("ORDER-2024-%06d", id),
		Status:        OrderStatusPending,
		TotalAmount:   amount,
		ItemCount:     rand.Intn(5) + 1, // 1-5 items
		UserTier:      tier,
		PromotionCode: promotionCode,
	}
}
