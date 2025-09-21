# OTLP协议实现

## 📊 概述

OTLP（OpenTelemetry Protocol）是OpenTelemetry的核心协议，用于在可观测性数据收集器、SDK和后端系统之间传输遥测数据。本文档详细描述了OTLP协议的实现细节、性能优化和最佳实践。

## 🔢 核心概念

### 1. 协议规范

#### 协议版本和特性

```yaml
OTLP协议规范:
  协议版本: "1.0.0"
  支持的数据类型:
    - 追踪数据 (Traces)
    - 指标数据 (Metrics)
    - 日志数据 (Logs)
  
  传输协议:
    gRPC:
      - 默认传输协议
      - 支持流式传输
      - 支持压缩
      - 支持认证和授权
    
    HTTP:
      - HTTP/1.1支持
      - HTTP/2支持
      - HTTP/3支持
      - 支持JSON和Protobuf格式
    
    WebSocket:
      - 实时双向通信
      - 支持浏览器环境
      - 支持自动重连
  
  数据格式:
    Protocol Buffers:
      - 默认序列化格式
      - 高效二进制格式
      - 向后兼容
      - 跨语言支持
    
    JSON:
      - 人类可读格式
      - 调试友好
      - 支持HTTP传输
      - 易于集成
  
  压缩算法:
    gzip:
      - 通用压缩算法
      - 平衡压缩率和速度
      - 广泛支持
    
    deflate:
      - 快速压缩算法
      - 低CPU使用率
      - 适合实时传输
    
    zstd:
      - 高效压缩算法
      - 高压缩率
      - 快速解压
```

#### 数据模型

```yaml
数据模型:
  追踪数据模型:
    资源 (Resource):
      - 服务名称
      - 服务版本
      - 部署环境
      - 主机信息
      - 自定义属性
    
    追踪 (Trace):
      - 追踪ID
      - 跨度列表
      - 状态信息
      - 属性信息
    
    跨度 (Span):
      - 跨度ID
      - 父跨度ID
      - 操作名称
      - 开始时间
      - 结束时间
      - 状态信息
      - 属性信息
      - 事件列表
      - 链接列表
  
  指标数据模型:
    资源指标 (Resource Metrics):
      - 资源信息
      - 作用域指标列表
    
    作用域指标 (Scope Metrics):
      - 作用域信息
      - 指标列表
    
    指标 (Metric):
      - 指标名称
      - 指标描述
      - 指标单位
      - 数据类型
      - 数据点列表
  
  日志数据模型:
    资源日志 (Resource Logs):
      - 资源信息
      - 作用域日志列表
    
    作用域日志 (Scope Logs):
      - 作用域信息
      - 日志记录列表
    
    日志记录 (Log Record):
      - 时间戳
      - 严重程度
      - 消息内容
      - 属性信息
      - 资源信息
```

### 2. 协议实现

#### gRPC传输实现

```python
class OTLPGRPCTransport:
    def __init__(self, endpoint, credentials=None, compression=None):
        self.endpoint = endpoint
        self.credentials = credentials
        self.compression = compression
        self.channel = None
        self.stub = None
        self._setup_grpc_connection()
    
    def _setup_grpc_connection(self):
        """设置gRPC连接"""
        # 配置gRPC选项
        options = [
            ('grpc.max_send_message_length', 4 * 1024 * 1024),  # 4MB
            ('grpc.max_receive_message_length', 4 * 1024 * 1024),  # 4MB
            ('grpc.keepalive_time_ms', 30000),  # 30秒
            ('grpc.keepalive_timeout_ms', 5000),  # 5秒
            ('grpc.keepalive_permit_without_calls', True),
            ('grpc.http2.max_pings_without_data', 0),
            ('grpc.http2.min_time_between_pings_ms', 10000),
            ('grpc.http2.min_ping_interval_without_data_ms', 300000)
        ]
        
        # 创建gRPC通道
        if self.credentials:
            self.channel = grpc.secure_channel(
                self.endpoint, 
                self.credentials, 
                options=options
            )
        else:
            self.channel = grpc.insecure_channel(
                self.endpoint, 
                options=options
            )
        
        # 创建gRPC存根
        self.stub = trace_service_pb2_grpc.TraceServiceStub(self.channel)
    
    def export_traces(self, traces):
        """导出追踪数据"""
        try:
            # 构建导出请求
            request = trace_service_pb2.ExportTraceServiceRequest(
                resource_spans=traces
            )
            
            # 发送请求
            response = self.stub.Export(request)
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except grpc.RpcError as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def export_metrics(self, metrics):
        """导出指标数据"""
        try:
            # 构建导出请求
            request = metrics_service_pb2.ExportMetricsServiceRequest(
                resource_metrics=metrics
            )
            
            # 发送请求
            response = self.stub.Export(request)
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except grpc.RpcError as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def export_logs(self, logs):
        """导出日志数据"""
        try:
            # 构建导出请求
            request = logs_service_pb2.ExportLogsServiceRequest(
                resource_logs=logs
            )
            
            # 发送请求
            response = self.stub.Export(request)
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except grpc.RpcError as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def close(self):
        """关闭连接"""
        if self.channel:
            self.channel.close()
```

#### HTTP传输实现

```python
class OTLPHTTPTransport:
    def __init__(self, endpoint, headers=None, timeout=30, compression=None):
        self.endpoint = endpoint
        self.headers = headers or {}
        self.timeout = timeout
        self.compression = compression
        self.session = requests.Session()
        self._setup_http_session()
    
    def _setup_http_session(self):
        """设置HTTP会话"""
        # 设置默认头部
        default_headers = {
            'Content-Type': 'application/x-protobuf',
            'User-Agent': 'OpenTelemetry-Python/1.0.0'
        }
        
        if self.compression:
            default_headers['Content-Encoding'] = self.compression
        
        self.headers.update(default_headers)
        self.session.headers.update(self.headers)
        
        # 配置连接池
        adapter = HTTPAdapter(
            pool_connections=10,
            pool_maxsize=20,
            max_retries=3,
            pool_block=False
        )
        
        self.session.mount('http://', adapter)
        self.session.mount('https://', adapter)
    
    def export_traces(self, traces):
        """导出追踪数据"""
        try:
            # 序列化数据
            serialized_data = self._serialize_traces(traces)
            
            # 压缩数据
            if self.compression:
                serialized_data = self._compress_data(serialized_data)
            
            # 发送请求
            response = self.session.post(
                f"{self.endpoint}/v1/traces",
                data=serialized_data,
                timeout=self.timeout
            )
            
            response.raise_for_status()
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except requests.RequestException as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def export_metrics(self, metrics):
        """导出指标数据"""
        try:
            # 序列化数据
            serialized_data = self._serialize_metrics(metrics)
            
            # 压缩数据
            if self.compression:
                serialized_data = self._compress_data(serialized_data)
            
            # 发送请求
            response = self.session.post(
                f"{self.endpoint}/v1/metrics",
                data=serialized_data,
                timeout=self.timeout
            )
            
            response.raise_for_status()
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except requests.RequestException as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def export_logs(self, logs):
        """导出日志数据"""
        try:
            # 序列化数据
            serialized_data = self._serialize_logs(logs)
            
            # 压缩数据
            if self.compression:
                serialized_data = self._compress_data(serialized_data)
            
            # 发送请求
            response = self.session.post(
                f"{self.endpoint}/v1/logs",
                data=serialized_data,
                timeout=self.timeout
            )
            
            response.raise_for_status()
            
            return {
                'success': True,
                'response': response,
                'error': None
            }
        except requests.RequestException as e:
            return {
                'success': False,
                'response': None,
                'error': str(e)
            }
    
    def _serialize_traces(self, traces):
        """序列化追踪数据"""
        # 使用Protocol Buffers序列化
        request = trace_service_pb2.ExportTraceServiceRequest(
            resource_spans=traces
        )
        return request.SerializeToString()
    
    def _serialize_metrics(self, metrics):
        """序列化指标数据"""
        # 使用Protocol Buffers序列化
        request = metrics_service_pb2.ExportMetricsServiceRequest(
            resource_metrics=metrics
        )
        return request.SerializeToString()
    
    def _serialize_logs(self, logs):
        """序列化日志数据"""
        # 使用Protocol Buffers序列化
        request = logs_service_pb2.ExportLogsServiceRequest(
            resource_logs=logs
        )
        return request.SerializeToString()
    
    def _compress_data(self, data):
        """压缩数据"""
        if self.compression == 'gzip':
            return gzip.compress(data)
        elif self.compression == 'deflate':
            return zlib.compress(data)
        elif self.compression == 'zstd':
            return zstd.compress(data)
        else:
            return data
```

### 3. 数据序列化

#### Protocol Buffers序列化

```python
class OTLPProtobufSerializer:
    def __init__(self):
        self.serializers = {
            'traces': self._serialize_traces,
            'metrics': self._serialize_metrics,
            'logs': self._serialize_logs
        }
    
    def serialize(self, data_type, data):
        """序列化数据"""
        serializer = self.serializers.get(data_type)
        if not serializer:
            raise ValueError(f"Unsupported data type: {data_type}")
        
        return serializer(data)
    
    def _serialize_traces(self, traces):
        """序列化追踪数据"""
        resource_spans = []
        
        for trace in traces:
            # 构建资源跨度
            resource_span = resource_pb2.ResourceSpans(
                resource=self._build_resource(trace.get('resource', {})),
                scope_spans=self._build_scope_spans(trace.get('spans', []))
            )
            resource_spans.append(resource_span)
        
        # 构建导出请求
        request = trace_service_pb2.ExportTraceServiceRequest(
            resource_spans=resource_spans
        )
        
        return request.SerializeToString()
    
    def _serialize_metrics(self, metrics):
        """序列化指标数据"""
        resource_metrics = []
        
        for metric in metrics:
            # 构建资源指标
            resource_metric = metrics_pb2.ResourceMetrics(
                resource=self._build_resource(metric.get('resource', {})),
                scope_metrics=self._build_scope_metrics(metric.get('metrics', []))
            )
            resource_metrics.append(resource_metric)
        
        # 构建导出请求
        request = metrics_service_pb2.ExportMetricsServiceRequest(
            resource_metrics=resource_metrics
        )
        
        return request.SerializeToString()
    
    def _serialize_logs(self, logs):
        """序列化日志数据"""
        resource_logs = []
        
        for log in logs:
            # 构建资源日志
            resource_log = logs_pb2.ResourceLogs(
                resource=self._build_resource(log.get('resource', {})),
                scope_logs=self._build_scope_logs(log.get('logs', []))
            )
            resource_logs.append(resource_log)
        
        # 构建导出请求
        request = logs_service_pb2.ExportLogsServiceRequest(
            resource_logs=resource_logs
        )
        
        return request.SerializeToString()
    
    def _build_resource(self, resource_data):
        """构建资源对象"""
        attributes = []
        
        for key, value in resource_data.get('attributes', {}).items():
            attribute = common_pb2.KeyValue(
                key=key,
                value=self._build_any_value(value)
            )
            attributes.append(attribute)
        
        return resource_pb2.Resource(attributes=attributes)
    
    def _build_any_value(self, value):
        """构建AnyValue对象"""
        if isinstance(value, str):
            return common_pb2.AnyValue(string_value=value)
        elif isinstance(value, bool):
            return common_pb2.AnyValue(bool_value=value)
        elif isinstance(value, int):
            return common_pb2.AnyValue(int_value=value)
        elif isinstance(value, float):
            return common_pb2.AnyValue(double_value=value)
        elif isinstance(value, list):
            array_value = common_pb2.ArrayValue(
                values=[self._build_any_value(item) for item in value]
            )
            return common_pb2.AnyValue(array_value=array_value)
        elif isinstance(value, dict):
            kvlist_value = common_pb2.KeyValueList(
                values=[
                    common_pb2.KeyValue(key=k, value=self._build_any_value(v))
                    for k, v in value.items()
                ]
            )
            return common_pb2.AnyValue(kvlist_value=kvlist_value)
        else:
            return common_pb2.AnyValue(string_value=str(value))
```

#### JSON序列化

```python
class OTLPJSONSerializer:
    def __init__(self):
        self.serializers = {
            'traces': self._serialize_traces,
            'metrics': self._serialize_metrics,
            'logs': self._serialize_logs
        }
    
    def serialize(self, data_type, data):
        """序列化数据"""
        serializer = self.serializers.get(data_type)
        if not serializer:
            raise ValueError(f"Unsupported data type: {data_type}")
        
        return json.dumps(serializer(data), default=self._json_serializer)
    
    def _serialize_traces(self, traces):
        """序列化追踪数据"""
        resource_spans = []
        
        for trace in traces:
            resource_span = {
                'resource': self._build_resource(trace.get('resource', {})),
                'scopeSpans': self._build_scope_spans(trace.get('spans', []))
            }
            resource_spans.append(resource_span)
        
        return {
            'resourceSpans': resource_spans
        }
    
    def _serialize_metrics(self, metrics):
        """序列化指标数据"""
        resource_metrics = []
        
        for metric in metrics:
            resource_metric = {
                'resource': self._build_resource(metric.get('resource', {})),
                'scopeMetrics': self._build_scope_metrics(metric.get('metrics', []))
            }
            resource_metrics.append(resource_metric)
        
        return {
            'resourceMetrics': resource_metrics
        }
    
    def _serialize_logs(self, logs):
        """序列化日志数据"""
        resource_logs = []
        
        for log in logs:
            resource_log = {
                'resource': self._build_resource(log.get('resource', {})),
                'scopeLogs': self._build_scope_logs(log.get('logs', []))
            }
            resource_logs.append(resource_log)
        
        return {
            'resourceLogs': resource_logs
        }
    
    def _build_resource(self, resource_data):
        """构建资源对象"""
        attributes = []
        
        for key, value in resource_data.get('attributes', {}).items():
            attribute = {
                'key': key,
                'value': self._build_any_value(value)
            }
            attributes.append(attribute)
        
        return {
            'attributes': attributes
        }
    
    def _build_any_value(self, value):
        """构建AnyValue对象"""
        if isinstance(value, str):
            return {'stringValue': value}
        elif isinstance(value, bool):
            return {'boolValue': value}
        elif isinstance(value, int):
            return {'intValue': str(value)}
        elif isinstance(value, float):
            return {'doubleValue': value}
        elif isinstance(value, list):
            return {
                'arrayValue': {
                    'values': [self._build_any_value(item) for item in value]
                }
            }
        elif isinstance(value, dict):
            return {
                'kvlistValue': {
                    'values': [
                        {'key': k, 'value': self._build_any_value(v)}
                        for k, v in value.items()
                    ]
                }
            }
        else:
            return {'stringValue': str(value)}
    
    def _json_serializer(self, obj):
        """JSON序列化器"""
        if hasattr(obj, 'isoformat'):
            return obj.isoformat()
        elif hasattr(obj, '__dict__'):
            return obj.__dict__
        else:
            return str(obj)
```

## 🎯 应用场景

### 1. 高性能数据传输

#### 批量传输优化

```python
class OTLPBatchExporter:
    def __init__(self, transport, batch_size=1000, export_timeout=30):
        self.transport = transport
        self.batch_size = batch_size
        self.export_timeout = export_timeout
        self.batch_buffer = {
            'traces': [],
            'metrics': [],
            'logs': []
        }
        self.lock = threading.Lock()
        self.export_thread = None
        self.stop_event = threading.Event()
    
    def add_trace(self, trace):
        """添加追踪数据"""
        with self.lock:
            self.batch_buffer['traces'].append(trace)
            
            if len(self.batch_buffer['traces']) >= self.batch_size:
                self._export_batch('traces')
    
    def add_metric(self, metric):
        """添加指标数据"""
        with self.lock:
            self.batch_buffer['metrics'].append(metric)
            
            if len(self.batch_buffer['metrics']) >= self.batch_size:
                self._export_batch('metrics')
    
    def add_log(self, log):
        """添加日志数据"""
        with self.lock:
            self.batch_buffer['logs'].append(log)
            
            if len(self.batch_buffer['logs']) >= self.batch_size:
                self._export_batch('logs')
    
    def _export_batch(self, data_type):
        """导出批次数据"""
        with self.lock:
            batch_data = self.batch_buffer[data_type].copy()
            self.batch_buffer[data_type].clear()
        
        if not batch_data:
            return
        
        # 异步导出
        if data_type == 'traces':
            self.transport.export_traces(batch_data)
        elif data_type == 'metrics':
            self.transport.export_metrics(batch_data)
        elif data_type == 'logs':
            self.transport.export_logs(batch_data)
    
    def start_periodic_export(self, interval=5):
        """启动定期导出"""
        self.export_thread = threading.Thread(
            target=self._periodic_export,
            args=(interval,)
        )
        self.export_thread.daemon = True
        self.export_thread.start()
    
    def _periodic_export(self, interval):
        """定期导出"""
        while not self.stop_event.is_set():
            time.sleep(interval)
            
            with self.lock:
                for data_type in ['traces', 'metrics', 'logs']:
                    if self.batch_buffer[data_type]:
                        self._export_batch(data_type)
    
    def stop(self):
        """停止导出"""
        self.stop_event.set()
        
        # 导出剩余数据
        with self.lock:
            for data_type in ['traces', 'metrics', 'logs']:
                if self.batch_buffer[data_type]:
                    self._export_batch(data_type)
        
        if self.export_thread:
            self.export_thread.join()
```

#### 流式传输优化

```python
class OTLPStreamingExporter:
    def __init__(self, transport, stream_size=100):
        self.transport = transport
        self.stream_size = stream_size
        self.streams = {
            'traces': asyncio.Queue(maxsize=stream_size),
            'metrics': asyncio.Queue(maxsize=stream_size),
            'logs': asyncio.Queue(maxsize=stream_size)
        }
        self.stream_tasks = {}
        self.running = False
    
    async def start(self):
        """启动流式导出"""
        self.running = True
        
        # 启动流式任务
        self.stream_tasks['traces'] = asyncio.create_task(
            self._stream_export('traces')
        )
        self.stream_tasks['metrics'] = asyncio.create_task(
            self._stream_export('metrics')
        )
        self.stream_tasks['logs'] = asyncio.create_task(
            self._stream_export('logs')
        )
    
    async def stop(self):
        """停止流式导出"""
        self.running = False
        
        # 等待所有任务完成
        for task in self.stream_tasks.values():
            task.cancel()
        
        await asyncio.gather(*self.stream_tasks.values(), return_exceptions=True)
    
    async def add_trace(self, trace):
        """添加追踪数据"""
        try:
            await self.streams['traces'].put(trace)
        except asyncio.QueueFull:
            # 队列满时丢弃最旧的数据
            try:
                self.streams['traces'].get_nowait()
                await self.streams['traces'].put(trace)
            except asyncio.QueueEmpty:
                pass
    
    async def add_metric(self, metric):
        """添加指标数据"""
        try:
            await self.streams['metrics'].put(metric)
        except asyncio.QueueFull:
            # 队列满时丢弃最旧的数据
            try:
                self.streams['metrics'].get_nowait()
                await self.streams['metrics'].put(metric)
            except asyncio.QueueEmpty:
                pass
    
    async def add_log(self, log):
        """添加日志数据"""
        try:
            await self.streams['logs'].put(log)
        except asyncio.QueueFull:
            # 队列满时丢弃最旧的数据
            try:
                self.streams['logs'].get_nowait()
                await self.streams['logs'].put(log)
            except asyncio.QueueEmpty:
                pass
    
    async def _stream_export(self, data_type):
        """流式导出"""
        batch = []
        
        while self.running:
            try:
                # 等待数据
                data = await asyncio.wait_for(
                    self.streams[data_type].get(),
                    timeout=1.0
                )
                
                batch.append(data)
                
                # 达到批次大小时导出
                if len(batch) >= self.stream_size:
                    await self._export_batch(data_type, batch)
                    batch = []
                
            except asyncio.TimeoutError:
                # 超时时导出剩余数据
                if batch:
                    await self._export_batch(data_type, batch)
                    batch = []
            except Exception as e:
                print(f"Error in stream export: {e}")
    
    async def _export_batch(self, data_type, batch):
        """导出批次数据"""
        try:
            if data_type == 'traces':
                await self.transport.export_traces(batch)
            elif data_type == 'metrics':
                await self.transport.export_metrics(batch)
            elif data_type == 'logs':
                await self.transport.export_logs(batch)
        except Exception as e:
            print(f"Error exporting {data_type}: {e}")
```

### 2. 错误处理和重试

#### 智能重试机制

```python
class OTLPRetryHandler:
    def __init__(self, max_retries=3, base_delay=1.0, max_delay=60.0, backoff_factor=2.0):
        self.max_retries = max_retries
        self.base_delay = base_delay
        self.max_delay = max_delay
        self.backoff_factor = backoff_factor
        self.retryable_errors = {
            'ConnectionError',
            'TimeoutError',
            'ServiceUnavailable',
            'InternalServerError',
            'BadGateway',
            'GatewayTimeout'
        }
    
    def should_retry(self, error):
        """判断是否应该重试"""
        error_type = type(error).__name__
        return error_type in self.retryable_errors
    
    def calculate_delay(self, attempt):
        """计算重试延迟"""
        delay = self.base_delay * (self.backoff_factor ** attempt)
        return min(delay, self.max_delay)
    
    async def execute_with_retry(self, func, *args, **kwargs):
        """执行带重试的函数"""
        last_error = None
        
        for attempt in range(self.max_retries + 1):
            try:
                return await func(*args, **kwargs)
            except Exception as e:
                last_error = e
                
                if attempt == self.max_retries or not self.should_retry(e):
                    raise e
                
                delay = self.calculate_delay(attempt)
                await asyncio.sleep(delay)
        
        raise last_error
    
    def execute_with_retry_sync(self, func, *args, **kwargs):
        """执行带重试的同步函数"""
        last_error = None
        
        for attempt in range(self.max_retries + 1):
            try:
                return func(*args, **kwargs)
            except Exception as e:
                last_error = e
                
                if attempt == self.max_retries or not self.should_retry(e):
                    raise e
                
                delay = self.calculate_delay(attempt)
                time.sleep(delay)
        
        raise last_error
```

#### 错误恢复策略

```python
class OTLPErrorRecovery:
    def __init__(self):
        self.recovery_strategies = {
            'ConnectionError': self._recover_connection_error,
            'TimeoutError': self._recover_timeout_error,
            'ServiceUnavailable': self._recover_service_unavailable,
            'InternalServerError': self._recover_internal_server_error,
            'BadGateway': self._recover_bad_gateway,
            'GatewayTimeout': self._recover_gateway_timeout
        }
        self.circuit_breaker = CircuitBreaker()
    
    async def recover_from_error(self, error, context):
        """从错误中恢复"""
        error_type = type(error).__name__
        recovery_strategy = self.recovery_strategies.get(error_type)
        
        if recovery_strategy:
            return await recovery_strategy(error, context)
        else:
            return await self._default_recovery(error, context)
    
    async def _recover_connection_error(self, error, context):
        """恢复连接错误"""
        # 检查电路断路器状态
        if self.circuit_breaker.is_open():
            return {'success': False, 'error': 'Circuit breaker is open'}
        
        # 尝试重新连接
        try:
            await context['transport'].reconnect()
            return {'success': True, 'error': None}
        except Exception as e:
            self.circuit_breaker.record_failure()
            return {'success': False, 'error': str(e)}
    
    async def _recover_timeout_error(self, error, context):
        """恢复超时错误"""
        # 增加超时时间
        context['transport'].timeout *= 2
        
        # 尝试重新发送
        try:
            return await context['transport'].export(context['data'])
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    async def _recover_service_unavailable(self, error, context):
        """恢复服务不可用错误"""
        # 等待服务恢复
        await asyncio.sleep(5)
        
        # 尝试重新发送
        try:
            return await context['transport'].export(context['data'])
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    async def _recover_internal_server_error(self, error, context):
        """恢复内部服务器错误"""
        # 记录错误并尝试重新发送
        self._log_error(error, context)
        
        try:
            return await context['transport'].export(context['data'])
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    async def _recover_bad_gateway(self, error, context):
        """恢复坏网关错误"""
        # 尝试使用备用端点
        if 'backup_endpoints' in context:
            for endpoint in context['backup_endpoints']:
                try:
                    context['transport'].endpoint = endpoint
                    return await context['transport'].export(context['data'])
                except Exception:
                    continue
        
        return {'success': False, 'error': 'All endpoints failed'}
    
    async def _recover_gateway_timeout(self, error, context):
        """恢复网关超时错误"""
        # 减少数据大小并重试
        if 'data' in context:
            context['data'] = self._reduce_data_size(context['data'])
        
        try:
            return await context['transport'].export(context['data'])
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    async def _default_recovery(self, error, context):
        """默认恢复策略"""
        # 记录错误
        self._log_error(error, context)
        
        # 返回失败
        return {'success': False, 'error': str(error)}
    
    def _log_error(self, error, context):
        """记录错误"""
        error_info = {
            'error_type': type(error).__name__,
            'error_message': str(error),
            'context': context,
            'timestamp': datetime.now().isoformat()
        }
        
        # 这里可以添加日志记录逻辑
        print(f"Error logged: {error_info}")
    
    def _reduce_data_size(self, data):
        """减少数据大小"""
        # 这里可以实现数据大小减少逻辑
        # 例如：采样、压缩、删除非关键字段等
        return data
```

## 🔧 性能优化

### 1. 连接池优化

#### 连接池管理

```python
class OTLPConnectionPool:
    def __init__(self, max_connections=10, max_keepalive=30):
        self.max_connections = max_connections
        self.max_keepalive = max_keepalive
        self.connections = []
        self.available_connections = []
        self.used_connections = set()
        self.lock = threading.Lock()
        self.cleanup_thread = None
        self.running = False
    
    def start(self):
        """启动连接池"""
        self.running = True
        self.cleanup_thread = threading.Thread(target=self._cleanup_connections)
        self.cleanup_thread.daemon = True
        self.cleanup_thread.start()
    
    def stop(self):
        """停止连接池"""
        self.running = False
        
        with self.lock:
            for connection in self.connections:
                connection.close()
            
            self.connections.clear()
            self.available_connections.clear()
            self.used_connections.clear()
        
        if self.cleanup_thread:
            self.cleanup_thread.join()
    
    def get_connection(self, endpoint, credentials=None):
        """获取连接"""
        with self.lock:
            # 尝试从可用连接中获取
            for connection in self.available_connections:
                if connection.endpoint == endpoint and connection.credentials == credentials:
                    self.available_connections.remove(connection)
                    self.used_connections.add(connection)
                    return connection
            
            # 创建新连接
            if len(self.connections) < self.max_connections:
                connection = self._create_connection(endpoint, credentials)
                self.connections.append(connection)
                self.used_connections.add(connection)
                return connection
            
            # 等待可用连接
            return None
    
    def return_connection(self, connection):
        """归还连接"""
        with self.lock:
            if connection in self.used_connections:
                self.used_connections.remove(connection)
                self.available_connections.append(connection)
    
    def _create_connection(self, endpoint, credentials):
        """创建连接"""
        if credentials:
            return OTLPGRPCTransport(endpoint, credentials)
        else:
            return OTLPGRPCTransport(endpoint)
    
    def _cleanup_connections(self):
        """清理连接"""
        while self.running:
            time.sleep(10)  # 每10秒清理一次
            
            with self.lock:
                current_time = time.time()
                connections_to_remove = []
                
                for connection in self.available_connections:
                    if current_time - connection.last_used > self.max_keepalive:
                        connections_to_remove.append(connection)
                
                for connection in connections_to_remove:
                    self.available_connections.remove(connection)
                    self.connections.remove(connection)
                    connection.close()
```

### 2. 数据压缩优化

#### 智能压缩选择

```python
class OTLPCompressionOptimizer:
    def __init__(self):
        self.compression_algorithms = {
            'gzip': GzipCompressor(),
            'deflate': DeflateCompressor(),
            'zstd': ZstdCompressor()
        }
        self.performance_metrics = {
            'gzip': {'compression_ratio': 0.3, 'speed': 1.0},
            'deflate': {'compression_ratio': 0.25, 'speed': 1.2},
            'zstd': {'compression_ratio': 0.2, 'speed': 0.8}
        }
    
    def select_optimal_compression(self, data_size, latency_requirement, bandwidth_constraint):
        """选择最优压缩算法"""
        candidates = []
        
        for algorithm, metrics in self.performance_metrics.items():
            compressed_size = data_size * metrics['compression_ratio']
            compression_time = data_size / metrics['speed']
            
            if (compression_time <= latency_requirement and 
                compressed_size <= bandwidth_constraint):
                candidates.append((algorithm, compressed_size, compression_time))
        
        if not candidates:
            return 'none'
        
        # 选择压缩后大小最小的算法
        return min(candidates, key=lambda x: x[1])[0]
    
    def compress_data(self, data, algorithm):
        """压缩数据"""
        if algorithm == 'none':
            return data
        
        compressor = self.compression_algorithms.get(algorithm)
        if not compressor:
            raise ValueError(f"Unsupported compression algorithm: {algorithm}")
        
        return compressor.compress(data)
    
    def decompress_data(self, data, algorithm):
        """解压缩数据"""
        if algorithm == 'none':
            return data
        
        compressor = self.compression_algorithms.get(algorithm)
        if not compressor:
            raise ValueError(f"Unsupported compression algorithm: {algorithm}")
        
        return compressor.decompress(data)
```

## 🧪 测试与验证

### 1. 协议测试

```python
import unittest

class TestOTLPProtocol(unittest.TestCase):
    def setUp(self):
        self.grpc_transport = OTLPGRPCTransport('localhost:4317')
        self.http_transport = OTLPHTTPTransport('http://localhost:4318')
        self.protobuf_serializer = OTLPProtobufSerializer()
        self.json_serializer = OTLPJSONSerializer()
    
    def test_grpc_transport_connection(self):
        """测试gRPC传输连接"""
        self.assertIsNotNone(self.grpc_transport.channel)
        self.assertIsNotNone(self.grpc_transport.stub)
    
    def test_http_transport_connection(self):
        """测试HTTP传输连接"""
        self.assertIsNotNone(self.http_transport.session)
        self.assertIn('Content-Type', self.http_transport.headers)
    
    def test_protobuf_serialization(self):
        """测试Protocol Buffers序列化"""
        test_data = {
            'resource': {'service.name': 'test-service'},
            'spans': [{'name': 'test-span', 'start_time': 1234567890}]
        }
        
        serialized = self.protobuf_serializer.serialize('traces', test_data)
        self.assertIsInstance(serialized, bytes)
        self.assertGreater(len(serialized), 0)
    
    def test_json_serialization(self):
        """测试JSON序列化"""
        test_data = {
            'resource': {'service.name': 'test-service'},
            'spans': [{'name': 'test-span', 'start_time': 1234567890}]
        }
        
        serialized = self.json_serializer.serialize('traces', test_data)
        self.assertIsInstance(serialized, str)
        self.assertGreater(len(serialized), 0)
    
    def test_batch_exporter(self):
        """测试批量导出器"""
        batch_exporter = OTLPBatchExporter(self.grpc_transport, batch_size=10)
        
        # 添加测试数据
        for i in range(15):
            batch_exporter.add_trace({'name': f'test-span-{i}'})
        
        # 验证批次导出
        self.assertEqual(len(batch_exporter.batch_buffer['traces']), 5)
    
    def test_compression_optimization(self):
        """测试压缩优化"""
        optimizer = OTLPCompressionOptimizer()
        
        # 测试压缩算法选择
        optimal_algorithm = optimizer.select_optimal_compression(
            data_size=1000,
            latency_requirement=100,
            bandwidth_constraint=500
        )
        
        self.assertIn(optimal_algorithm, ['gzip', 'deflate', 'zstd', 'none'])
```

### 2. 性能测试

```python
def benchmark_otlp_protocol():
    """OTLP协议性能测试"""
    # 测试序列化性能
    test_data = generate_test_trace_data(1000)
    
    protobuf_serializer = OTLPProtobufSerializer()
    json_serializer = OTLPJSONSerializer()
    
    # Protocol Buffers序列化性能
    start_time = time.time()
    protobuf_data = protobuf_serializer.serialize('traces', test_data)
    protobuf_time = time.time() - start_time
    
    # JSON序列化性能
    start_time = time.time()
    json_data = json_serializer.serialize('traces', test_data)
    json_time = time.time() - start_time
    
    print(f"Protocol Buffers serialization: {protobuf_time:.4f}s, size: {len(protobuf_data)} bytes")
    print(f"JSON serialization: {json_time:.4f}s, size: {len(json_data)} bytes")
    
    # 测试压缩性能
    compression_optimizer = OTLPCompressionOptimizer()
    
    for algorithm in ['gzip', 'deflate', 'zstd']:
        start_time = time.time()
        compressed_data = compression_optimizer.compress_data(protobuf_data, algorithm)
        compression_time = time.time() - start_time
        
        compression_ratio = len(compressed_data) / len(protobuf_data)
        print(f"{algorithm} compression: {compression_time:.4f}s, ratio: {compression_ratio:.2f}")

def benchmark_transport_performance():
    """传输性能测试"""
    grpc_transport = OTLPGRPCTransport('localhost:4317')
    http_transport = OTLPHTTPTransport('http://localhost:4318')
    
    test_data = generate_test_trace_data(100)
    
    # gRPC传输性能
    start_time = time.time()
    grpc_result = grpc_transport.export_traces(test_data)
    grpc_time = time.time() - start_time
    
    # HTTP传输性能
    start_time = time.time()
    http_result = http_transport.export_traces(test_data)
    http_time = time.time() - start_time
    
    print(f"gRPC transport: {grpc_time:.4f}s, success: {grpc_result['success']}")
    print(f"HTTP transport: {http_time:.4f}s, success: {http_result['success']}")
```

## 📚 参考文献

1. **OpenTelemetry Specification** (2023). *OpenTelemetry Protocol (OTLP)*.
2. **Protocol Buffers** (2023). *Protocol Buffers Language Guide*.
3. **gRPC Documentation** (2023). *gRPC Core Concepts*.
4. **HTTP/3 Specification** (2022). *RFC 9114: HTTP/3*.
5. **QUIC Protocol** (2021). *RFC 9000: QUIC: A UDP-Based Multiplexed and Secure Transport*.

## 🔗 相关资源

- [语义约定实现](语义约定实现.md)
- [数据模型实现](数据模型实现.md)
- [传输协议实现](传输协议实现.md)
- [多语言SDK开发](../SDK开发/多语言SDK开发.md)

---

*本文档是OpenTelemetry 2025年知识体系技术实现层的一部分*  
*最后更新: 2025年1月*  
*版本: 1.0.0*
