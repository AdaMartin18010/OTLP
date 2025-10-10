# Python OTLP Trace Example

这是一个简单的Python示例，展示如何使用OpenTelemetry SDK发送trace数据到OTLP Collector。

## 功能

- 创建OTLP gRPC导出器
- 配置TracerProvider和Resource
- 创建根Span和多个子Span
- 添加属性、事件和状态
- 错误处理和异常记录
- 批量导出到Collector

## 前置要求

- Python 3.8+
- pip
- Docker 和 Docker Compose (运行Collector和Jaeger)

## 快速开始

### 1. 启动基础设施

首先启动OpenTelemetry Collector和Jaeger：

```bash
# 在项目根目录
docker-compose up -d
```

验证服务运行：
```bash
docker-compose ps
```

### 2. 安装依赖

```bash
cd examples/python

# 推荐：创建虚拟环境
python -m venv venv
source venv/bin/activate  # Linux/Mac
# 或
venv\Scripts\activate  # Windows

# 安装依赖
pip install -r requirements.txt
```

### 3. 运行示例

```bash
python hello_trace.py
```

### 4. 查看Trace

打开浏览器访问Jaeger UI：
```
http://localhost:16686
```

在Service下拉菜单选择 `hello-trace-python`，点击 "Find Traces" 即可看到发送的trace。

## 代码说明

### 核心组件

1. **Resource** - 服务元数据
   ```python
   resource = Resource(attributes={
       SERVICE_NAME: "hello-trace-python",
       SERVICE_VERSION: "1.0.0",
   })
   ```

2. **OTLP Exporter** - 导出器
   ```python
   otlp_exporter = OTLPSpanExporter(
       endpoint="localhost:4317",
       insecure=True
   )
   ```

3. **BatchSpanProcessor** - 批处理器
   ```python
   processor = BatchSpanProcessor(otlp_exporter)
   provider.add_span_processor(processor)
   ```

4. **Span操作** - 创建和操作span
   ```python
   with tracer.start_as_current_span("operation") as span:
       span.set_attribute("key", "value")
       span.add_event("event_name")
       span.set_status(Status(StatusCode.OK))
   ```

## 特性演示

### 1. 层级Span

示例创建了一个三层的span树：
```
hello-operation (root)
├── sub-operation
└── error-handling
```

### 2. 属性 (Attributes)

为span添加键值对元数据：
```python
span.set_attribute("greeting", "Hello OTLP!")
span.set_attribute("language", "Python")
span.set_attribute("example.version", 1)
```

### 3. 事件 (Events)

在span生命周期中记录时间点事件：
```python
span.add_event("processing_started", 
               attributes={"item_count": 10})
```

### 4. 状态 (Status)

标记操作结果：
```python
# 成功
span.set_status(Status(StatusCode.OK))

# 失败
span.set_status(Status(StatusCode.ERROR, "error message"))
```

### 5. 异常记录

记录Python异常到span：
```python
try:
    # 可能出错的代码
    pass
except Exception as e:
    span.record_exception(e)
    span.set_status(Status(StatusCode.ERROR, str(e)))
```

## 配置选项

### Endpoint配置

```python
# 开发环境 - 非加密
OTLPSpanExporter(
    endpoint="localhost:4317",
    insecure=True
)

# 生产环境 - TLS加密
OTLPSpanExporter(
    endpoint="collector.example.com:4317",
    insecure=False,
    credentials=ChannelCredentials(
        root_certificates=open("ca.pem", "rb").read()
    )
)
```

### 批处理配置

```python
processor = BatchSpanProcessor(
    otlp_exporter,
    max_queue_size=2048,      # 最大队列大小
    schedule_delay_millis=5000,  # 延迟5秒发送
    max_export_batch_size=512,   # 每批最多512个span
)
```

### 采样配置

```python
from opentelemetry.sdk.trace.sampling import (
    TraceIdRatioBased, 
    ParentBased
)

# 10%采样率
sampler = TraceIdRatioBased(0.1)

# 或基于父Span的采样决策
sampler = ParentBased(root=TraceIdRatioBased(0.1))

provider = TracerProvider(
    resource=resource,
    sampler=sampler
)
```

## 故障排除

### 导入错误

如果遇到 `ModuleNotFoundError`：
```bash
pip install --upgrade -r requirements.txt
```

### 连接失败

如果看到 `connection refused` 错误：
1. 确认Collector正在运行: `docker-compose ps`
2. 检查端口: `netstat -an | grep 4317` (Linux) 或 `netstat -an | findstr 4317` (Windows)
3. 查看Collector日志: `docker-compose logs otel-collector`

### Trace未显示

1. 等待2-5秒，批处理器有延迟
2. 检查程序输出是否有错误
3. 查看Jaeger UI的时间范围设置

## 生产环境建议

1. **使用环境变量配置**
   ```python
   import os
   endpoint = os.getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "localhost:4317")
   ```

2. **启用TLS**
   ```python
   insecure = os.getenv("OTEL_EXPORTER_OTLP_INSECURE", "false").lower() == "true"
   ```

3. **配置采样率**
   ```python
   sample_rate = float(os.getenv("OTEL_TRACES_SAMPLER_ARG", "0.1"))
   ```

4. **添加错误处理**
   ```python
   try:
       provider = TracerProvider(resource=resource)
   except Exception as e:
       logger.error(f"Failed to initialize tracing: {e}")
       # 降级：不使用tracing
   ```

## 更多示例

查看 [examples/README.md](../README.md) 了解更多示例。

## 参考文档

- [OpenTelemetry Python SDK](https://opentelemetry.io/docs/languages/python/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Python API Reference](https://opentelemetry-python.readthedocs.io/)

