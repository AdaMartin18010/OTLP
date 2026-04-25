# Configuration 规范完整解析

> **标准来源**: OpenTelemetry Specification v1.56.0 — Configuration
> **状态更新**: 声明式配置（Declarative Configuration）已于 **2026 年 2 月进入 Stable**
> **核心主题**: OpenTelemetry SDK 的三层配置体系——程序化配置、环境变量配置、声明式配置

---

## 一、配置体系总览

OpenTelemetry 规范定义了三种正交且互补的配置机制，构成完整的配置金字塔：

```text
                    ┌─────────────────────┐
                    │   程序化配置         │  ← 最灵活，代码内完成
                    │  (Programmatic)     │     适合框架封装和动态场景
                    └─────────────────────┘
                              ▲
                              │ 构建于之上
                              ▼
                    ┌─────────────────────┐
                    │   声明式配置         │  ← 最表达力，文件驱动
                    │  (Declarative)      │     适合运维管理和 GitOps
                    └─────────────────────┘
                              ▲
                              │ 构建于之上
                              ▼
                    ┌─────────────────────┐
                    │   环境变量配置       │  ← 最便携，12-Factor 友好
                    │  (Environment)      │     适合容器和云原生部署
                    └─────────────────────┘
```

**核心原则**: 所有配置机制最终都映射到 SDK 的程序化接口。程序化接口是根基，其他机制是对此接口的封装。

---

## 二、程序化配置（Programmatic Configuration）

### 2.1 规范要求

**必须（MUST）** 要求：

- SDK **必须** 提供程序化接口用于所有配置
- 接口应使用 SDK 自身的编程语言编写
- 所有其他配置机制**应该**构建于此接口之上

### 2.2 典型实现模式

#### Java SDK — Builder 模式

```java
// 通过 TracerProvider 的 Builder 进行完整配置
TracerProvider tracerProvider = SdkTracerProvider.builder()
    // 添加 Span Processor
    .addSpanProcessor(BatchSpanProcessor.builder(
        OtlpGrpcSpanExporter.builder()
            .setEndpoint("http://collector:4317")
            .setTimeout(30, TimeUnit.SECONDS)
            .build()
    ).setMaxQueueSize(2048).build())
    // 设置 Resource
    .setResource(Resource.create(Attributes.builder()
        .put(ResourceAttributes.SERVICE_NAME, "payment-service")
        .put(ResourceAttributes.SERVICE_VERSION, "2.1.0")
        .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production")
        .build()))
    // 设置 Sampler
    .setSampler(Sampler.traceIdRatioBased(0.1))
    // 设置 ID Generator
    .setIdGenerator(new RandomIdGenerator())
    .build();

// 将配置好的 Provider 设置为全局
OpenTelemetrySdk.builder()
    .setTracerProvider(tracerProvider)
    .buildAndRegisterGlobal();
```

#### Python SDK — 类与参数模式

```python
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource, SERVICE_NAME, SERVICE_VERSION

# 程序化创建所有组件
resource = Resource.create({
    SERVICE_NAME: "payment-service",
    SERVICE_VERSION: "2.1.0",
})

exporter = OTLPSpanExporter(
    endpoint="http://collector:4317",
    timeout=30,
)

processor = BatchSpanProcessor(
    exporter,
    max_queue_size=2048,
    max_export_batch_size=512,
)

provider = TracerProvider(
    resource=resource,
    active_span_processor=processor,
)
```

#### Go SDK — 函数选项模式（Functional Options）

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.40.0"
)

// 程序化配置 TracerProvider
 tp, err := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(otlptracegrpc.NewClient(
        otlptracegrpc.WithEndpoint("collector:4317"),
        otlptracegrpc.WithTimeout(30 * time.Second),
    )),
    sdktrace.WithResource(resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceNameKey.String("payment-service"),
        semconv.ServiceVersionKey.String("2.1.0"),
    )),
    sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)),
)
```

### 2.3 程序化配置的优势与局限

| 优势 | 局限 |
|------|------|
| 完全灵活，支持条件逻辑和动态调整 | 需要修改代码并重新部署 |
| 可在框架中封装预设配置模板 | 不同语言语法差异大，难以统一 |
| 可利用 IDE 自动补全和类型检查 | 运维人员难以直接修改 |
| 适合单元测试中的 Mock 配置注入 | 不适合 GitOps 和配置管理中心化 |

---

## 三、环境变量配置（Environment Variable Configuration）

### 3.1 规范要求

规范定义了一组**语言无关**的环境变量，用于常见的配置目标。所有语言 SDK **应该**支持这些环境变量。

### 3.2 核心环境变量速查表

#### 服务身份与资源

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_SERVICE_NAME` | 服务名称 | `payment-service` |
| `OTEL_RESOURCE_ATTRIBUTES` | 通用资源属性（逗号分隔键值对） | `service.version=2.1.0,deployment.environment=production` |

#### 导出器端点

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_EXPORTER_OTLP_ENDPOINT` | OTLP 统一端点 | `http://localhost:4317` |
| `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT` | Traces 专用端点 | `http://collector:4317/v1/traces` |
| `OTEL_EXPORTER_OTLP_METRICS_ENDPOINT` | Metrics 专用端点 | `http://collector:4318/v1/metrics` |
| `OTEL_EXPORTER_OTLP_LOGS_ENDPOINT` | Logs 专用端点 | `http://collector:4318/v1/logs` |

#### 导出器协议与认证

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_EXPORTER_OTLP_PROTOCOL` | 协议类型 | `grpc` 或 `http/protobuf` |
| `OTEL_EXPORTER_OTLP_HEADERS` | 额外 HTTP 头 | `Authorization=Bearer token123,x-api-key=abc` |
| `OTEL_EXPORTER_OTLP_CERTIFICATE` | TLS 证书路径 | `/etc/ssl/cert.pem` |
| `OTEL_EXPORTER_OTLP_CLIENT_KEY` | mTLS 客户端密钥路径 | `/etc/ssl/key.pem` |
| `OTEL_EXPORTER_OTLP_CLIENT_CERTIFICATE` | mTLS 客户端证书路径 | `/etc/ssl/client.pem` |

#### 采样策略

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_TRACES_SAMPLER` | 采样器名称 | `traceidratio`、`parentbased_traceidratio`、`always_on`、`always_off` |
| `OTEL_TRACES_SAMPLER_ARG` | 采样器参数 | `0.1`（对应 10% 采样率）|

#### 批处理与超时

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_BSP_SCHEDULE_DELAY` | Batch Span Processor 导出间隔（毫秒）| `5000` |
| `OTEL_BSP_MAX_QUEUE_SIZE` | 队列最大长度 | `2048` |
| `OTEL_BSP_MAX_EXPORT_BATCH_SIZE` | 单次导出最大 Span 数 | `512` |
| `OTEL_EXPORTER_OTLP_TIMEOUT` | 导出超时（毫秒）| `10000` |

#### 日志级别与诊断

| 环境变量 | 说明 | 示例 |
|---------|------|------|
| `OTEL_LOG_LEVEL` | SDK 内部日志级别 | `debug`、`info`、`warn`、`error` |
| `OTEL_PROPAGATORS` | 传播器列表 | `tracecontext,baggage` 或 `tracecontext,baggage,b3` |

### 3.3 环境变量的优先级

环境变量配置**可以被**程序化配置覆盖。优先级从高到低：

```text
1. 代码中的程序化配置（最高优先级）
2. 环境变量配置
3. 语言/框架内置默认值（最低优先级）
```

这意味着：如果代码中显式设置了 `endpoint`，则 `OTEL_EXPORTER_OTLP_ENDPOINT` 会被忽略。

### 3.4 容器与 Kubernetes 中的实践

```yaml
# Kubernetes Deployment 示例
apiVersion: apps/v1
kind: Deployment
metadata:
  name: payment-service
spec:
  template:
    spec:
      containers:
      - name: app
        image: payment-service:2.1.0
        env:
        # 身份标识
        - name: OTEL_SERVICE_NAME
          value: "payment-service"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "service.version=2.1.0,deployment.environment=production,k8s.namespace=$(POD_NAMESPACE)"
        # 导出目标
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector.monitoring:4317"
        - name: OTEL_EXPORTER_OTLP_PROTOCOL
          value: "grpc"
        # 采样
        - name: OTEL_TRACES_SAMPLER
          value: "parentbased_traceidratio"
        - name: OTEL_TRACES_SAMPLER_ARG
          value: "0.1"
        # 传播器
        - name: OTEL_PROPAGATORS
          value: "tracecontext,baggage"
```

---

## 四、声明式配置（Declarative Configuration）

### 4.1 背景与演进

声明式配置是 OpenTelemetry 社区近年来最重要的配置创新。它解决了程序化配置和环境变量配置的核心痛点：

| 痛点 | 声明式配置的解决方案 |
|------|-------------------|
| 环境变量表达能力弱（仅支持字符串键值对） | 支持结构化数据模型（对象、数组、嵌套） |
| 程序化配置需要修改代码并重编译 | 基于文件，支持热加载（未来） |
| 跨语言配置无法复用 | 语言无关的数据模型，同一份配置可用于任何语言 SDK |
| 复杂配置（如多 Exporter、Processor 链）难以用环境变量表达 | 原生支持管道、链式结构、条件逻辑 |

### 4.2 数据模型

声明式配置定义了一套标准化的数据结构，允许用户以文件（YAML/JSON）形式描述期望的 SDK 组件配置。

#### 配置文件结构（YAML 示例）

```yaml
# opentelemetry-configuration.yaml
file_format: "0.3"

# 资源属性
resource:
  attributes:
    - name: service.name
      value: "payment-service"
    - name: service.version
      value: "2.1.0"
    - name: deployment.environment
      value: "production"

# Tracer Provider 配置
tracer_provider:
  # 采样器
  sampler:
    parent_based:
      root:
        trace_id_ratio_based:
          ratio: 0.1
      remote_parent_sampled:
        always_on: {}
      remote_parent_not_sampled:
        always_off: {}

  # Span Processor 列表
  processors:
    - batch:
        exporter:
          otlp:
            protocol: http/protobuf
            endpoint: "http://otel-collector:4318/v1/traces"
            headers:
              - name: "x-api-key"
                value: "${API_KEY}"  # 支持环境变量插值
        schedule_delay: 5000
        max_queue_size: 2048
        max_export_batch_size: 512

    # 第二个 Processor：输出到控制台（调试用）
    - simple:
        exporter:
          console: {}

  # 限制器
  limits:
    max_attribute_count: 128
    max_attribute_value_length: 4096
    max_event_count: 128
    max_link_count: 32

# Meter Provider 配置
meter_provider:
  readers:
    - periodic:
        exporter:
          otlp:
            protocol: grpc
            endpoint: "http://otel-collector:4317"
        interval: 60000

# Logger Provider 配置
logger_provider:
  processors:
    - batch:
        exporter:
          otlp:
            protocol: http/protobuf
            endpoint: "http://otel-collector:4318/v1/logs"

# 传播器配置
propagators:
  - tracecontext
  - baggage
```

### 4.3 Instrumentation Configuration API

声明式配置不仅配置 SDK，还可以向 Instrumentation 库传递配置：

```yaml
# 为特定 Instrumentation 库提供配置
instrumentation:
  http:
    capture_headers:
      request:
        - "x-request-id"
        - "x-user-id"
      response:
        - "x-correlation-id"
    capture_body:
      request: false
      response: false

  db:
    statement_capture: "sanitized"  # none / sanitized / raw

  genai:
    capture_prompt_content: true
    capture_completion_content: false
```

### 4.4 配置文件解析 SDK

OpenTelemetry 提供了 Configuration SDK，负责：

| 功能 | 说明 |
|------|------|
| 文件解析 | 加载 YAML/JSON 配置文件，验证格式 |
| 内存模型 | 将配置转换为语言内的结构化对象 |
| 插件引用 | 支持引用配置文件外的自定义组件（通过名称或路径）|
| 环境变量插值 | 支持 `${ENV_VAR}` 或 `${ENV_VAR:default}` 语法 |
| 配置合并 | 支持多配置文件按优先级合并 |

### 4.5 与程序化配置的关系

```text
声明式配置文件
       │
       ▼
┌──────────────────┐
│ Configuration SDK │  ← 解析文件，构建内存模型
│   (文件 → 对象)   │
└──────────────────┘
       │
       ▼
┌──────────────────┐
│  Programmatic    │  ← 将内存模型转换为对 SDK Builder 的调用
│   Interface      │
└──────────────────┘
       │
       ▼
┌──────────────────┐
│   SDK 实例化      │  ← 最终构建出 TracerProvider / MeterProvider
└──────────────────┘
```

这意味着：即使使用声明式配置，底层仍然是程序化接口。声明式配置是程序化配置的**声明式前端**。

### 4.6 多语言支持状态

| 语言 | 声明式配置支持状态 | 说明 |
|------|-------------------|------|
| Java | ✅ Stable | 通过 `opentelemetry-sdk-extension-autoconfigure` 支持 |
| .NET | ✅ Stable | 通过 `OpenTelemetry.Configuration` 支持 |
| Go | 🟡 开发中 | 社区贡献中，部分功能可用 |
| Python | 🟡 开发中 | 正在集成到 `opentelemetry-sdk` |
| Node.js | 🟡 开发中 | 实验性支持 |

---

## 五、三层配置对比与选型指南

| 维度 | 程序化配置 | 环境变量配置 | 声明式配置 |
|------|-----------|-------------|-----------|
| **灵活性** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ |
| **表达力** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ |
| **可移植性** | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **运维友好度** | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **GitOps 支持** | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **动态调整** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ (未来支持热加载) |
| **类型安全** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ (schema 验证) |
| **跨语言复用** | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

### 选型决策树

```text
是否需要运行时动态调整配置？
├── 是 → 使用程序化配置（代码内条件逻辑）
└── 否 → 配置是否复杂（多 Exporter、Processor 链、Instrumentation 参数）？
    ├── 是 → 使用声明式配置（YAML 文件）
    └── 否 → 是否容器化/云原生部署？
        ├── 是 → 使用环境变量配置（12-Factor 原则）
        └── 否 → 使用声明式配置（统一配置管理）
```

### 组合使用模式

实践中，三层配置经常组合使用：

```text
基础默认值（代码内）
    ↓
环境变量覆盖（容器编排层）
    ↓
声明式文件细化（应用配置层）
    ↓
程序化微调（框架适配层）
```

**示例**：

- 代码中设置默认的 Resource 属性（服务框架名称）
- Kubernetes 中通过环境变量设置端点和采样率
- 声明式文件中配置复杂的 Processor 链和 Instrumentation 参数
- 代码中根据运行时特征动态调整 Sampler

---

## 六、配置安全与最佳实践

### 6.1 敏感信息处理

| 敏感信息 | 推荐方式 | 不推荐方式 |
|---------|---------|-----------|
| API Key / Token | 环境变量插值 `${API_KEY}` | 硬编码在配置文件 |
| mTLS 证书路径 | 环境变量或配置管理注入 | 提交到 Git 仓库 |
| 密码 | 通过 Secret 管理机制 | 明文存储 |

### 6.2 配置验证

```yaml
# 使用 schema 验证工具（未来社区将提供官方验证器）
# 建议在 CI/CD 中增加配置验证步骤

# 示例：Makefile 或 CI 脚本
validate-otel-config:
    otel-config-validator --schema 0.3 --file opentelemetry-configuration.yaml
```

### 6.3 配置版本管理

- 声明式配置文件应纳入版本控制（排除敏感值）
- 使用 `${}` 语法将敏感值外置到 Secret 管理
- 不同环境（dev/staging/prod）使用不同的配置文件或配置覆盖

---

## 七、参考资源

- OpenTelemetry Specification: Configuration
- OpenTelemetry Declarative Configuration Data Model (Stable)
- OpenTelemetry Environment Variable Specification
- 各语言 SDK 的 Configuration 扩展文档

---

> **总结**: OpenTelemetry 的配置体系从单一的环境变量，演进为"程序化 + 环境变量 + 声明式"的三层金字塔。声明式配置的 Stable 标志着 OpenTelemetry 在运维友好性和配置管理成熟度上迈出了关键一步。建议生产环境用户逐步从纯环境变量配置迁移到声明式配置，以获得更好的表达力和可维护性。
