use opentelemetry::{
    global,
    trace::{Span, Tracer},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::SpanExporter;
use std::time::Duration;
use tracing::{info, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[instrument]
async fn process_trace_data() {
    info!("处理跟踪数据");
    
    // 模拟压缩处理
    let data = b"sample trace data for compression";
    let compressed = flate2::read::GzEncoder::new(
        std::io::Cursor::new(data),
        flate2::Compression::default(),
    );
    
    info!("数据压缩完成，压缩率: {:.2}%", 
          (1.0 - compressed.get_ref().len() as f64 / data.len() as f64) * 100.0);
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "tracezip-demo"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("compression.type", "gzip"),
    ]);

    // 配置导出器
    let exporter = SpanExporter::builder()
        .with_http()
        .with_endpoint("http://localhost:4318")
        .with_timeout(Duration::from_secs(10))
        .build()
        .expect("build otlp exporter");

    // 配置采样器
    let sampler = Sampler::TraceIdRatioBased(0.1);

    // 配置TracerProvider
    let provider = trace::TracerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter)
        .with_sampler(sampler)
        .with_id_generator(RandomIdGenerator::default())
        .build();

    let tracer = provider.tracer("tracezip-demo");

    // 配置tracing
    let otel_layer = tracing_opentelemetry::layer().with_tracer(tracer);
    let fmt_layer = tracing_subscriber::fmt::layer();
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(fmt_layer)
        .with(otel_layer)
        .init();

    // 运行示例
    process_trace_data().await;

    // 确保所有数据都被导出
    provider.shutdown().ok();
    Ok(())
}
