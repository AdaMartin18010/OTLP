use opentelemetry::{
    global,
    trace::{Span, Tracer, TracerProvider as _},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler, TracerProvider},
    Resource,
};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_semantic_conventions as semconv;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, span, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter, Registry};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置资源
    let resource = Resource::new(vec![
        semconv::resource::SERVICE_NAME.string("advanced-rust-service"),
        semconv::resource::SERVICE_VERSION.string("1.0.0"),
        semconv::resource::SERVICE_INSTANCE_ID.string("instance-1"),
        semconv::resource::DEPLOYMENT_ENVIRONMENT.string("production"),
        semconv::resource::HOST_NAME.string("rust-server"),
        semconv::resource::HOST_ARCH.string("amd64"),
        semconv::resource::OS_NAME.string("linux"),
        semconv::resource::OS_VERSION.string("5.4.0"),
    ]);

    // 配置导出器
    let exporter = SpanExporter::builder()
        .with_http()
        .with_endpoint("http://localhost:4318")
        .with_timeout(Duration::from_secs(10))
        .with_headers([("Authorization", "Bearer token")])
        .build()
        .expect("build otlp exporter");

    // 配置采样器
    let sampler = trace::Sampler::TraceIdRatioBased(0.1); // 10%采样率

    // 配置TracerProvider
    let provider = TracerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter)
        .with_sampler(sampler)
        .with_id_generator(RandomIdGenerator::default())
        .with_span_limits(trace::SpanLimits {
            max_attributes_per_span: 128,
            max_events_per_span: 128,
            max_links_per_span: 128,
            max_attributes_per_event: 128,
            max_attributes_per_link: 128,
            max_attribute_length: 1024,
        })
        .build();

    let tracer = provider.tracer("advanced-rust-service");

    // 配置tracing
    let otel_layer = tracing_opentelemetry::layer().with_tracer(tracer);
    let fmt_layer = tracing_subscriber::fmt::layer();
    Registry::default()
        .with(EnvFilter::new("info"))
        .with(fmt_layer)
        .with(otel_layer)
        .init();

    // 模拟业务逻辑
    simulate_business_logic().await;

    // 确保所有数据都被导出
    provider.shutdown().ok();
    Ok(())
}

async fn simulate_business_logic() {
    let root_span = span!(Level::INFO, "business_logic", "operation" = "main");
    let _enter = root_span.enter();

    info!("开始业务逻辑处理");

    // 模拟用户认证
    let auth_result = authenticate_user("user123", "password").await;
    if !auth_result {
        info!("用户认证失败");
        return;
    }

    // 模拟数据库查询
    let user_data = query_user_data("user123").await;
    info!(user_id = "user123", "查询用户数据完成");

    // 模拟业务处理
    let result = process_business_logic(&user_data).await;
    info!(result = ?result, "业务处理完成");

    // 模拟外部API调用
    let api_response = call_external_api(&result).await;
    info!(response_status = api_response.status, "外部API调用完成");

    info!("业务逻辑处理完成");
}

async fn authenticate_user(username: &str, password: &str) -> bool {
    let span = span!(Level::INFO, "authenticate_user", "user" = username);
    let _enter = span.enter();

    info!("开始用户认证");
    
    // 模拟认证延迟
    sleep(Duration::from_millis(100)).await;
    
    // 模拟认证逻辑
    let is_valid = username == "user123" && password == "password";
    
    if is_valid {
        info!("用户认证成功");
    } else {
        info!("用户认证失败");
    }
    
    is_valid
}

async fn query_user_data(user_id: &str) -> UserData {
    let span = span!(Level::INFO, "query_user_data", "user_id" = user_id);
    let _enter = span.enter();

    info!("开始查询用户数据");
    
    // 模拟数据库查询延迟
    sleep(Duration::from_millis(200)).await;
    
    // 模拟数据库查询
    let user_data = UserData {
        id: user_id.to_string(),
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
        role: "user".to_string(),
    };
    
    info!(user_name = user_data.name, "用户数据查询完成");
    
    user_data
}

async fn process_business_logic(user_data: &UserData) -> BusinessResult {
    let span = span!(Level::INFO, "process_business_logic", "user_id" = user_data.id);
    let _enter = span.enter();

    info!("开始业务逻辑处理");
    
    // 模拟业务处理延迟
    sleep(Duration::from_millis(300)).await;
    
    // 模拟业务逻辑
    let result = BusinessResult {
        user_id: user_data.id.clone(),
        processed_at: chrono::Utc::now(),
        status: "success".to_string(),
        data: "processed_data".to_string(),
    };
    
    info!(status = result.status, "业务逻辑处理完成");
    
    result
}

async fn call_external_api(data: &BusinessResult) -> ApiResponse {
    let span = span!(Level::INFO, "call_external_api", "user_id" = data.user_id);
    let _enter = span.enter();

    info!("开始调用外部API");
    
    // 模拟API调用延迟
    sleep(Duration::from_millis(150)).await;
    
    // 模拟API调用
    let response = ApiResponse {
        status: 200,
        message: "success".to_string(),
        data: "api_response_data".to_string(),
    };
    
    info!(status = response.status, "外部API调用完成");
    
    response
}

#[derive(Debug, Clone)]
struct UserData {
    id: String,
    name: String,
    email: String,
    role: String,
}

#[derive(Debug, Clone)]
struct BusinessResult {
    user_id: String,
    processed_at: chrono::DateTime<chrono::Utc>,
    status: String,
    data: String,
}

#[derive(Debug, Clone)]
struct ApiResponse {
    status: u16,
    message: String,
    data: String,
}
