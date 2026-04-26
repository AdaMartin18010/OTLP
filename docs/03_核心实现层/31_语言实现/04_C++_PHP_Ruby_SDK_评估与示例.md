# C++ / PHP / Ruby SDK 评估与示例

> **核心目标**: 评估 OpenTelemetry C++、PHP、Ruby SDK 的成熟度，提供接入示例和选型建议

---

## 一、SDK 成熟度总览

### 1.1 多语言 SDK 状态矩阵

| 语言 | API 稳定性 | SDK 稳定性 | Exporter 成熟度 | 自动插桩 | 生产就绪度 | 社区活跃度 |
|------|-----------|-----------|----------------|---------|-----------|-----------|
| **Java** | Stable | Stable | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ✅ 生产就绪 | 极高 |
| **Go** | Stable | Stable | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ✅ 生产就绪 | 极高 |
| **Python** | Stable | Stable | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ✅ 生产就绪 | 极高 |
| **Node.js** | Stable | Stable | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ✅ 生产就绪 | 极高 |
| **.NET** | Stable | Stable | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ✅ 生产就绪 | 高 |
| **Rust** | Stable | Beta | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⚠️ 谨慎使用 | 中 |
| **C++** | Stable | Beta | ⭐⭐⭐ | ⭐⭐ | ⚠️ 谨慎使用 | 中 |
| **PHP** | Stable | Beta | ⭐⭐⭐ | ⭐⭐ | ⚠️ 谨慎使用 | 中 |
| **Ruby** | Stable | Beta | ⭐⭐⭐ | ⭐⭐ | ⚠️ 谨慎使用 | 中 |
| **Swift** | Development | Development | ⭐⭐ | ⭐ | 🚧 实验阶段 | 低 |
| **Erlang/Elixir** | Development | Development | ⭐⭐ | ⭐ | 🚧 实验阶段 | 低 |

### 1.2 C++ / PHP / Ruby 定位

```text
这三种语言的共同特征:
├── API 已标记为 Stable（规范接口基本确定）
├── SDK 处于 Beta（实现仍在完善）
├── 自动插桩覆盖有限（主要框架支持不足）
├── 社区贡献者相对较少
└── 适合早期采用者（Early Adopters），不建议核心业务直接使用
```

---

## 二、C++ SDK

### 2.1 状态评估

| 维度 | 状态 | 说明 |
|------|------|------|
| **仓库** | github.com/open-telemetry/opentelemetry-cpp | 活跃维护 |
| **构建系统** | CMake + Bazel | C++ 生态标准 |
| **依赖管理** | 较复杂 | 需要 gRPC、Protobuf、Thrift 等 |
| **exporter** | OTLP/gRPC, OTLP/HTTP, Jaeger, Zipkin | 基本覆盖 |
| **自动插桩** | 有限 | 无主流 Web 框架的自动插桩 |
| **性能** | 高 | C++ 原生性能优势 |

### 2.2 适用场景

- **高性能服务**: 游戏后端、高频交易系统、嵌入式设备
- **遗留 C++ 系统**: 需要为现有 C++ 服务添加可观测性
- **跨语言 SDK 基础**: 作为其他语言（如 Python C-extension）的底层实现

### 2.3 基础示例

```cpp
// C++: 基础追踪示例
#include "opentelemetry/sdk/trace/tracer_provider.h"
#include "opentelemetry/exporters/otlp/otlp_grpc_exporter.h"
#include "opentelemetry/sdk/resource/resource.h"
#include "opentelemetry/sdk/trace/simple_processor.h"

using namespace opentelemetry;

int main() {
    // 创建 OTLP gRPC Exporter
    auto exporter = std::make_unique<exporter::otlp::OtlpGrpcExporter>();

    // 创建 Processor
    auto processor = std::make_unique<sdk::trace::SimpleSpanProcessor>(std::move(exporter));

    // 创建 Resource
    auto resource = sdk::resource::Resource::Create({
        {sdk::resource::SemanticConventions::kServiceName, "cpp-service"},
        {sdk::resource::SemanticConventions::kServiceVersion, "1.0.0"},
    });

    // 创建 Provider
    auto provider = nostd::shared_ptr<sdk::trace::TracerProvider>(
        new sdk::trace::TracerProvider(std::move(processor), resource)
    );

    // 设置为全局 Provider
    trace::Provider::SetTracerProvider(provider);

    // 获取 Tracer 并创建 Span
    auto tracer = provider->GetTracer("my-library", "1.0.0");
    auto span = tracer->StartSpan("processOrder");

    span->SetAttribute("order.id", "12345");
    span->SetAttribute("order.amount", 199.99);

    // 业务逻辑
    processOrder();

    span->End();

    return 0;
}
```

### 2.4 接入建议

```text
推荐策略:
├── 新 C++ 项目:
│   └── 可以试用，但建议封装一层抽象，便于未来切换
├── 遗留 C++ 项目:
│   └── 在关键路径手动插桩，避免大规模改造
├── 自动插桩期望:
│   └── 短期内不要期待完善的自动插桩
└── 替代方案:
    └── 考虑 Sidecar 模式（Collector Agent）收集日志和指标
```

---

## 三、PHP SDK

### 2.1 状态评估

| 维度 | 状态 | 说明 |
|------|------|------|
| **仓库** | github.com/open-telemetry/opentelemetry-php | 活跃维护 |
| **扩展方式** | PHP 扩展（C）+ PHP 库 | 双轨实现 |
| **框架支持** | Laravel, Symfony, WordPress（实验性）| 自动插桩有限 |
| **Exporter** | OTLP/HTTP, Jaeger, Zipkin | 基本覆盖 |
| **Packagist** | 可用 | `open-telemetry/sdk` |

### 2.2 适用场景

- **PHP Web 应用**: Laravel、Symfony 项目
- **CMS 系统**: WordPress、Drupal 的可观测性
- **遗留 PHP 系统**: 电商平台、内容网站

### 2.3 基础示例

```php
<?php
// PHP: Laravel 中间件示例

use OpenTelemetry\API\Trace\SpanKind;
use OpenTelemetry\Contrib\Otlp\OtlpHttpTransportFactory;
use OpenTelemetry\SDK\Trace\TracerProvider;
use OpenTelemetry\SDK\Trace\SpanProcessor\BatchSpanProcessor;

class OpenTelemetryMiddleware
{
    private $tracer;

    public function __construct()
    {
        $transport = (new OtlpHttpTransportFactory())->create('http://collector:4318/v1/traces');
        $exporter = new SpanExporter($transport);
        $processor = new BatchSpanProcessor($exporter);
        $provider = new TracerProvider([$processor]);

        $this->tracer = $provider->getTracer('laravel-app', '1.0.0');
    }

    public function handle($request, Closure $next)
    {
        $span = $this->tracer->spanBuilder($request->method() . ' ' . $request->path())
            ->setSpanKind(SpanKind::KIND_SERVER)
            ->setAttribute('http.method', $request->method())
            ->setAttribute('http.target', $request->path())
            ->startSpan();

        try {
            $response = $next($request);
            $span->setAttribute('http.status_code', $response->getStatusCode());
            return $response;
        } catch (\Exception $e) {
            $span->recordException($e);
            $span->setStatus('error', $e->getMessage());
            throw $e;
        } finally {
            $span->end();
        }
    }
}
```

### 2.4 接入建议

```text
推荐策略:
├── 新 Laravel/Symfony 项目:
│   └── 可以使用社区中间件包，快速获得 HTTP 追踪
├── 遗留 PHP 项目:
│   └── 在入口文件手动初始化，关键函数手动插桩
├── WordPress:
│   └── 实验性插件可用，不建议生产环境
└── 性能注意:
    └── PHP 的 OTel SDK 开销相对明显，建议开启采样
```

---

## 四、Ruby SDK

### 2.1 状态评估

| 维度 | 状态 | 说明 |
|------|------|------|
| **仓库** | github.com/open-telemetry/opentelemetry-ruby | 活跃维护 |
| **Gem 可用性** | 可用 | `opentelemetry-sdk` |
| **框架支持** | Rails, Sinatra, Rack | Rack 中间件较成熟 |
| **Exporter** | OTLP/HTTP, Jaeger, Zipkin | 基本覆盖 |
| **自动插桩** | 有限 | Rack、HTTP、Redis、MySQL 有基础支持 |

### 2.2 适用场景

- **Ruby on Rails 应用**: Web 服务、API 后端
- **Sinatra 应用**: 轻量级服务
- **Ruby 微服务**: 与现有 Ruby 生态集成

### 2.3 基础示例

```ruby
# Ruby: Rails 初始化配置
# config/initializers/opentelemetry.rb

require 'opentelemetry/sdk'
require 'opentelemetry/exporter/otlp'
require 'opentelemetry/instrumentation/all'

OpenTelemetry::SDK.configure do |c|
  c.service_name = 'rails-app'
  c.service_version = '1.0.0'

  # 添加 OTLP Exporter
  c.add_span_processor(
    OpenTelemetry::SDK::Trace::Export::BatchSpanProcessor.new(
      OpenTelemetry::Exporter::OTLP::Exporter.new(endpoint: 'http://collector:4318')
    )
  )

  # 启用自动插桩
  c.use_all({ 'OpenTelemetry::Instrumentation::Rack' => { enabled: true } })
end
```

```ruby
# Ruby: 手动插桩示例
require 'opentelemetry'

tracer = OpenTelemetry.tracer_provider.tracer('my-service')

tracer.in_span('process_order', attributes: { 'order.id' => '12345' }) do |span|
  # 业务逻辑
  result = process_order(order_id)

  span.set_attribute('order.status', result.status)
rescue StandardError => e
  span.record_exception(e)
  span.status = OpenTelemetry::Trace::Status.error(e.message)
  raise
end
```

### 2.4 接入建议

```text
推荐策略:
├── 新 Rails 项目:
│   └── 可以直接使用 auto-instrumentation gem
├── 遗留 Rails 项目:
│   └── 先启用 Rack 中间件，获得 HTTP 层追踪
│   └── 然后逐步为关键业务逻辑添加手动插桩
├── 性能注意:
│   └── Ruby 的 GC 可能与 BatchSpanProcessor 竞争
│   └── 建议调整 batch size 和 queue size
└── 社区支持:
    └── Ruby 社区相对小，遇到问题可能需要自行排查
```

---

## 五、三种语言对比总结

| 维度 | C++ | PHP | Ruby |
|------|-----|-----|------|
| **生产就绪度** | ⚠️ Beta | ⚠️ Beta | ⚠️ Beta |
| **安装复杂度** | 高（CMake/Bazel）| 中（Composer）| 低（Gem）|
| **自动插桩** | 弱 | 弱 | 中（Rack）|
| **性能开销** | 极低 | 中 | 中 |
| **适用场景** | 高性能/嵌入式 | Web/CMS | Web/API |
| **社区支持** | 中 | 中 | 中 |
| **推荐行动** | 谨慎试用 | 框架项目可试用 | Rack 项目可试用 |

---

## 六、统一建议

### 6.1 是否应在项目中使用？

```text
决策树:

项目是否使用 C++ / PHP / Ruby？
├── 否 → 使用对应语言的成熟 SDK（Java/Go/Python/Node.js）
│
└── 是 → 项目的可观测性是否关键路径？
    ├── 是（核心业务依赖）
    │   └── 建议:
    │       ├── 短期: 使用 Collector + 日志/指标桥接
    │       ├── 中期: 关键路径手动插桩
    │       └── 长期: 跟进 SDK 成熟后全面替换
    │
    └── 否（辅助/内部工具）
        └── 建议:
            ├── 直接试用对应语言的 OTel SDK
            └── 为社区贡献 issue 和 PR，加速成熟
```

### 6.2 对社区的贡献方向

- **C++**: 完善文档、提供更多示例、增加主流框架集成
- **PHP**: 完善 Laravel/Symfony 自动插桩、WordPress 插件稳定化
- **Ruby**: 完善 Rails 集成、增加数据库和缓存插桩

---

## 七、参考资源

- OpenTelemetry C++: github.com/open-telemetry/opentelemetry-cpp
- OpenTelemetry PHP: github.com/open-telemetry/opentelemetry-php
- OpenTelemetry Ruby: github.com/open-telemetry/opentelemetry-ruby
- 各语言官方文档: opentelemetry.io/docs

---

> **总结**: C++、PHP、Ruby 的 OpenTelemetry SDK 均处于 Beta 阶段，API 已稳定但 SDK 实现和自动插桩覆盖仍有不足。建议非核心系统可以试用，核心系统建议先通过 Collector + 日志桥接获取基础可观测性，等待 SDK 进一步成熟后全面迁移。社区的试用反馈和贡献是加速这些 SDK 成熟的关键。
