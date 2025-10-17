# OTLP Spring Boot Demo

完整的OpenTelemetry Spring Boot示例，展示Traces、Metrics和Logs的集成。

## 📋 目录

- [功能特性](#功能特性)
- [技术栈](#技术栈)
- [快速开始](#快速开始)
- [API端点](#api端点)
- [配置说明](#配置说明)
- [查看数据](#查看数据)
- [故障排查](#故障排查)

## 功能特性

### ✅ 完整的三大信号支持

- **Traces (追踪)**: 使用OpenTelemetry SDK手动创建span
- **Metrics (指标)**: 使用Micrometer与OpenTelemetry集成
- **Logs (日志)**: 使用Logback appender自动关联trace context

### ✅ 实用场景演示

1. **基本追踪**: `/api/hello` - 简单的请求-响应追踪
2. **嵌套Span**: `/api/chain` - 展示多层调用关系
3. **慢请求追踪**: `/api/slow` - 性能分析
4. **错误追踪**: `/api/error` - 异常处理和错误追踪
5. **数据库/缓存模拟**: 展示不同类型的客户端操作

### ✅ 最佳实践

- 结构化日志（包含trace_id/span_id）
- 自定义span属性
- 异常记录
- 批量导出配置
- 资源属性配置

## 技术栈

| 组件 | 版本 | 用途 |
|------|------|------|
| Spring Boot | 3.2.0 | Web框架 |
| Java | 17 | 编程语言 |
| OpenTelemetry SDK | 1.32.0 | 遥测SDK |
| OpenTelemetry Instrumentation | 2.0.0 | 自动埋点 |
| Micrometer | (Spring Boot管理) | 指标收集 |
| Lombok | (最新) | 代码简化 |
| Maven | 3.9+ | 构建工具 |

## 快速开始

### 方式一：本地运行

#### 前置条件

- Java 17+
- Maven 3.9+
- Docker (用于运行OTLP Collector和Jaeger)

#### 步骤

1. **启动基础设施**

    ```bash
    # 在项目根目录
    cd ../..
    docker-compose up -d
    ```

2. **构建项目**

    ```bash
    cd examples/java-spring-boot
    mvn clean package
    ```

3. **运行应用**

    ```bash
    java -jar target/otlp-spring-boot-demo-1.0.0.jar
    ```

    或直接使用Maven:

    ```bash
    mvn spring-boot:run
    ```

4. **验证**

```bash
# 健康检查
curl http://localhost:8080/api/health

# 测试追踪
curl http://localhost:8080/api/hello?name=OpenTelemetry

# 查看指标
curl http://localhost:8080/api/metrics
```

### 方式二：Docker运行

```bash
# 构建镜像
docker build -t otlp-spring-boot-demo .

# 运行容器
docker run -d \
  --name spring-boot-demo \
  --network otlp_default \
  -p 8080:8080 \
  -e OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317 \
  otlp-spring-boot-demo

# 查看日志
docker logs -f spring-boot-demo
```

### 方式三：Docker Compose (推荐)

在项目根目录的`docker-compose.yml`中已包含此服务配置。

```bash
cd ../..
docker-compose up -d java-app
```

## API端点

### 1. Hello端点

**基本用法**：

```bash
curl "http://localhost:8080/api/hello?name=World"
```

**响应**：

```json
{
  "message": "Hello, World!",
  "timestamp": 1697558400000,
  "traceId": "8a3c60f7d188f8fa79d48a391a778fa6"
}
```

**功能**：

- 创建根span
- 调用业务逻辑（嵌套span）
- 记录结构化日志
- 增加请求计数器
- 记录请求耗时

### 2. Slow端点

**用法**：

```bash
curl http://localhost:8080/api/slow
```

**响应**：

```json
{
  "duration_ms": 1523,
  "message": "Operation completed"
}
```

**功能**：

- 模拟慢操作（1-3秒）
- 在span中记录延迟时长
- 适合测试性能监控

### 3. Error端点

**用法**：

```bash
curl http://localhost:8080/api/error
```

**响应**：500错误

**功能**：

- 模拟异常场景
- 记录异常到span
- 记录错误日志
- 测试错误追踪

### 4. Chain端点

**用法**：

```bash
curl http://localhost:8080/api/chain
```

**响应**：

```json
{
  "status": "success",
  "operations": 3
}
```

**功能**：

- 展示嵌套span结构
- 模拟数据库查询
- 模拟外部API调用
- 模拟缓存查询

### 5. Metrics端点

**用法**：

```bash
curl http://localhost:8080/api/metrics
```

**响应**：

```json
{
  "request_count": 42.0,
  "request_duration_mean": 125.5,
  "request_duration_max": 350.2
}
```

**功能**：

- 查看当前应用指标
- 请求计数和耗时统计

### 6. Health端点

```bash
curl http://localhost:8080/api/health
```

## 配置说明

### application.yml配置

```yaml
otel:
  service:
    name: otlp-spring-boot-demo  # 服务名称
    version: 1.0.0                # 服务版本
  exporter:
    otlp:
      endpoint: http://localhost:4317  # OTLP Collector地址
  traces:
    sampler: always_on           # 采样策略
  metrics:
    export:
      interval: 10s              # 指标导出间隔
  logs:
    export:
      interval: 1s               # 日志导出间隔
```

### 环境变量覆盖

```bash
# 修改OTLP端点
export OTEL_EXPORTER_OTLP_ENDPOINT=http://custom-collector:4317

# 修改服务名
export OTEL_SERVICE_NAME=my-custom-service

# 修改采样率
export OTEL_TRACES_SAMPLER=traceidratio
export OTEL_TRACES_SAMPLER_ARG=0.1  # 10%采样率

# 运行应用
java -jar target/otlp-spring-boot-demo-1.0.0.jar
```

### 代码中的配置

参见`OpenTelemetryConfig.java`：

```java
@Bean
public SdkTracerProvider sdkTracerProvider(Resource resource) {
    OtlpGrpcSpanExporter spanExporter = OtlpGrpcSpanExporter.builder()
        .setEndpoint(otlpEndpoint)
        .setTimeout(Duration.ofSeconds(10))
        .build();

    return SdkTracerProvider.builder()
        .setResource(resource)
        .addSpanProcessor(
            BatchSpanProcessor.builder(spanExporter)
                .setScheduleDelay(Duration.ofSeconds(1))
                .setMaxQueueSize(2048)
                .setMaxExportBatchSize(512)
                .build()
        )
        .setSampler(Sampler.alwaysOn())
        .build();
}
```

## 查看数据

### Jaeger UI

打开浏览器访问：<http://localhost:16686>

**查看Traces**：

1. Service下拉选择 `otlp-spring-boot-demo`
2. 点击"Find Traces"
3. 选择任意追踪查看详情

**追踪结构示例**：

```text
chained-operation (200ms)
  ├─ operation-1 (100ms)
  │   └─ db.query (20ms)
  ├─ operation-2 (150ms)
  │   └─ http.request (100ms)
  └─ operation-3 (50ms)
      └─ cache.get (5ms)
```

### Prometheus (指标)

如果配置了Prometheus Exporter：

```bash
curl http://localhost:8080/actuator/prometheus
```

### 日志关联

查看应用日志，trace_id会自动注入：

```text
2025-10-17 10:30:15 [http-nio-8080-exec-1] [8a3c60f7d188f8fa79d48a391a778fa6/79d48a391a778fa6] INFO  i.o.e.controller.DemoController - Processing hello request for name: World
```

## 故障排查

### 问题1：无法连接到OTLP Collector

**症状**：

```text
UNAVAILABLE: io exception
```

**解决方案**：

1. 检查Collector是否运行：

    ```bash
    docker ps | grep otel-collector
    ```

2. 检查endpoint配置：

    ```bash
    curl http://localhost:13133/  # Collector健康检查
    ```

3. 确认网络连接（Docker网络）：

    ```bash
    docker network inspect otlp_default
    ```

### 问题2：没有看到Traces

**可能原因**：

1. **Sampler配置为never**: 检查`application.yml`中的`otel.traces.sampler`
2. **异步导出延迟**: 等待几秒后刷新Jaeger UI
3. **时钟不同步**: 确保容器和主机时间同步

**调试**：

启用OpenTelemetry调试日志：

```yaml
logging:
  level:
    io.opentelemetry: DEBUG
```

### 问题3：Maven构建失败

**症状**：

```text
[ERROR] Failed to execute goal ... dependency not found
```

**解决方案**：

1. 清理本地仓库：

    ```bash
    rm -rf ~/.m2/repository/io/opentelemetry
    mvn clean install
    ```

2. 使用阿里云镜像（中国用户）：

在`pom.xml`中添加：

```xml
<repositories>
    <repository>
        <id>aliyun</id>
        <url>https://maven.aliyun.com/repository/public</url>
    </repository>
</repositories>
```

### 问题4：内存不足

**症状**：

```text
java.lang.OutOfMemoryError: Java heap space
```

**解决方案**：

增加JVM内存：

```bash
export JAVA_OPTS="-Xms512m -Xmx1024m"
java $JAVA_OPTS -jar target/otlp-spring-boot-demo-1.0.0.jar
```

或在Dockerfile中修改`ENV JAVA_OPTS`。

## 高级主题

### 1. 自定义采样策略

```java
@Bean
public Sampler customSampler() {
    return Sampler.parentBased(
        Sampler.traceIdRatioBased(0.1) // 10%采样率
    );
}
```

### 2. 添加全局属性

```java
Resource.create(
    Attributes.builder()
        .put("custom.attribute", "value")
        .put("environment", "production")
        .build()
);
```

### 3. 自定义Exporter

```java
SpanExporter customExporter = new SpanExporter() {
    @Override
    public CompletableResultCode export(Collection<SpanData> spans) {
        // 自定义导出逻辑
        return CompletableResultCode.ofSuccess();
    }
};
```

## 参考资源

- [OpenTelemetry Java文档](https://opentelemetry.io/docs/languages/java/)
- [Spring Boot Actuator](https://docs.spring.io/spring-boot/docs/current/reference/html/actuator.html)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)

## 贡献

欢迎提交Issue和Pull Request！

## 许可证

MIT License
