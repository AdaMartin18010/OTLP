use opentelemetry::trace::TracerProvider as _;
use opentelemetry_sdk::{trace::SdkTracerProvider, Resource};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use tracing::{info, span, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter, Registry};
use std::env;

#[tokio::main]
async fn main() {
    let endpoint = env::var("OTEL_EXPORTER_OTLP_ENDPOINT").unwrap_or_else(|_| "http://localhost:4317".to_string());
    let service_name = env::var("OTEL_SERVICE_NAME").unwrap_or_else(|_| "minimal-rust".to_string());

    let exporter = SpanExporter::builder()
        .with_http()
        .with_endpoint(endpoint)
        .build()
        .expect("build otlp exporter");

    let provider = SdkTracerProvider::builder()
        .with_resource(Resource::builder().with_service_name(service_name).build())
        .with_batch_exporter(exporter)
        .build();

    let tracer = provider.tracer("minimal-rust");

    let otel_layer = tracing_opentelemetry::layer().with_tracer(tracer);
    let fmt_layer = tracing_subscriber::fmt::layer();
    Registry::default()
        .with(EnvFilter::new("info"))
        .with(fmt_layer)
        .with(otel_layer)
        .init();

    let s = span!(Level::INFO, "demo-span");
    let _enter = s.enter();
    info!(demo_attr = "value", "hello from rust");

    // Ensure spans are exported before process exit
    provider.shutdown().ok();
}

