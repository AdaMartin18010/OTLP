---
title: Python SDK完整实战指南
description: OpenTelemetry Python SDK的完整实战指南，包含Flask/Django/FastAPI集成、异步支持等
version: Python 3.8+ / OTel Python v1.21.0
date: 2026-03-17
author: OTLP项目团队
category: SDK指南
tags:
  - python
  - flask
  - django
  - fastapi
  - sdk
  - otlp
  - opentelemetry
  - async
status: published
---

# Python SDK完整实战指南

> **版本**: Python 3.8+ / OpenTelemetry Python v1.21.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约40分钟

---

## 1. 环境准备

### 1.1 安装依赖

```bash
# 基础SDK
pip install opentelemetry-api opentelemetry-sdk

# OTLP导出器
pip install opentelemetry-exporter-otlp-proto-grpc opentelemetry-exporter-otlp-proto-http

# 自动Instrumentation工具
pip install opentelemetry-distro opentelemetry-instrumentation

# 框架特定Instrumentation
pip install opentelemetry-instrumentation-flask
pip install opentelemetry-instrumentation-django
pip install opentelemetry-instrumentation-fastapi
pip install opentelemetry-instrumentation-requests
pip install opentelemetry-instrumentation-sqlalchemy
pip install opentelemetry-instrumentation-celery
pip install opentelemetry-instrumentation-asyncio
pip install opentelemetry-instrumentation-httpx

# 日志集成
pip install opentelemetry-instrumentation-logging
```

### 1.2 使用requirements.txt

```txt
# requirements.txt
opentelemetry-api>=1.21.0
opentelemetry-sdk>=1.21.0
opentelemetry-exporter-otlp-proto-grpc>=1.21.0
opentelemetry-exporter-otlp-proto-http>=1.21.0
opentelemetry-distro>=0.42b0
opentelemetry-instrumentation>=0.42b0
opentelemetry-instrumentation-flask>=0.42b0
opentelemetry-instrumentation-django>=0.42b0
opentelemetry-instrumentation-fastapi>=0.42b0
opentelemetry-instrumentation-requests>=0.42b0
opentelemetry-instrumentation-sqlalchemy>=0.42b0
opentelemetry-instrumentation-celery>=0.42b0
opentelemetry-instrumentation-asyncio>=0.42b0
opentelemetry-instrumentation-httpx>=0.42b0
opentelemetry-instrumentation-logging>=0.42b0
```

### 1.3 项目结构

```
myapp/
├── app/
│   ├── __init__.py
│   ├── telemetry.py          # 遥测配置
│   ├── config.py             # 应用配置
│   ├── models.py
│   ├── views.py              # 或 controllers.py
│   └── tasks.py              # 后台任务
├── tests/
│   └── test_telemetry.py
├── manage.py                 # Django使用
├── app.py                    # Flask/FastAPI使用
├── requirements.txt
└── Dockerfile
```

---

## 2. 基础配置

### 2.1 程序化配置OpenTelemetry

```python
# app/telemetry.py

import os
import logging
from typing import Optional

from opentelemetry import trace, metrics
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor, ConsoleSpanExporter
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.sdk.metrics.view import View
from opentelemetry.sdk.resources import Resource, SERVICE_NAME, SERVICE_VERSION, DEPLOYMENT_ENVIRONMENT
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter as HTTPSpanExporter
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator
from opentelemetry.metrics import set_meter_provider
from opentelemetry.trace import set_tracer_provider

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class TelemetryConfig:
    """遥测配置类"""

    def __init__(
        self,
        service_name: str = "python-service",
        service_version: str = "1.0.0",
        environment: str = "development",
        otlp_endpoint: str = "http://localhost:4317",
        otlp_insecure: bool = True,
        trace_sampler_ratio: float = 1.0,
        metric_export_interval: int = 60000,
    ):
        self.service_name = service_name
        self.service_version = service_version
        self.environment = environment
        self.otlp_endpoint = otlp_endpoint
        self.otlp_insecure = otlp_insecure
        self.trace_sampler_ratio = trace_sampler_ratio
        self.metric_export_interval = metric_export_interval

        self._tracer_provider: Optional[TracerProvider] = None
        self._meter_provider: Optional[MeterProvider] = None
        self._resource: Optional[Resource] = None

    def _create_resource(self) -> Resource:
        """创建资源属性"""
        return Resource.create({
            SERVICE_NAME: self.service_name,
            SERVICE_VERSION: self.service_version,
            DEPLOYMENT_ENVIRONMENT: self.environment,
            "host.name": os.uname().nodename if hasattr(os, 'uname') else "unknown",
            "process.runtime.name": "CPython",
            "process.runtime.version": os.sys.version,
        })

    def init_tracing(self) -> TracerProvider:
        """初始化链路追踪"""
        self._resource = self._create_resource()

        # 创建OTLP导出器
        span_exporter = OTLPSpanExporter(
            endpoint=self.otlp_endpoint,
            insecure=self.otlp_insecure,
            timeout=10,
        )

        # 创建TracerProvider
        self._tracer_provider = TracerProvider(
            resource=self._resource,
            active_span_processor=BatchSpanProcessor(
                span_exporter,
                max_queue_size=2048,
                max_export_batch_size=512,
                schedule_delay_millis=5000,
                export_timeout_millis=30000,
            ),
        )

        # 设置全局TracerProvider
        set_tracer_provider(self._tracer_provider)

        logger.info(f"Tracing initialized for service: {self.service_name}")
        return self._tracer_provider

    def init_metrics(self) -> MeterProvider:
        """初始化指标"""
        if self._resource is None:
            self._resource = self._create_resource()

        # 创建OTLP指标导出器
        metric_exporter = OTLPMetricExporter(
            endpoint=self.otlp_endpoint,
            insecure=self.otlp_insecure,
            timeout=10,
        )

        # 创建MetricReader
        reader = PeriodicExportingMetricReader(
            metric_exporter,
            export_interval_millis=self.metric_export_interval,
        )

        # 创建MeterProvider
        self._meter_provider = MeterProvider(
            resource=self._resource,
            metric_readers=[reader],
        )

        # 设置全局MeterProvider
        set_meter_provider(self._meter_provider)

        logger.info(f"Metrics initialized for service: {self.service_name}")
        return self._meter_provider

    def get_tracer(self, name: str = None) -> trace.Tracer:
        """获取Tracer实例"""
        name = name or self.service_name
        return trace.get_tracer(name, self.service_version)

    def get_meter(self, name: str = None) -> metrics.Meter:
        """获取Meter实例"""
        name = name or self.service_name
        return metrics.get_meter(name, self.service_version)

    def shutdown(self):
        """优雅关闭"""
        if self._tracer_provider:
            self._tracer_provider.shutdown()
            logger.info("TracerProvider shutdown completed")

        if self._meter_provider:
            self._meter_provider.shutdown()
            logger.info("MeterProvider shutdown completed")


# 全局配置实例
telemetry_config = TelemetryConfig(
    service_name=os.getenv("OTEL_SERVICE_NAME", "python-service"),
    service_version=os.getenv("OTEL_SERVICE_VERSION", "1.0.0"),
    environment=os.getenv("OTEL_ENVIRONMENT", "development"),
    otlp_endpoint=os.getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317"),
    otlp_insecure=os.getenv("OTEL_EXPORTER_OTLP_INSECURE", "true").lower() == "true",
    trace_sampler_ratio=float(os.getenv("OTEL_TRACES_SAMPLER_RATIO", "1.0")),
    metric_export_interval=int(os.getenv("OTEL_METRIC_EXPORT_INTERVAL", "60000")),
)


def init_telemetry():
    """初始化所有遥测组件"""
    telemetry_config.init_tracing()
    telemetry_config.init_metrics()
    return telemetry_config
```

### 2.2 使用opentelemetry-instrument自动注入

```bash
# 安装 instrumentation 包
opentelemetry-bootstrap -a install

# 启动应用（自动注入）
opentelemetry-instrument \
    --traces_exporter otlp \
    --metrics_exporter otlp \
    --service_name order-service \
    --exporter_otlp_endpoint http://localhost:4317 \
    --exporter_otlp_insecure true \
    python app.py

# 或使用环境变量
export OTEL_SERVICE_NAME=order-service
export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
export OTEL_EXPORTER_OTLP_INSECURE=true
export OTEL_TRACES_EXPORTER=otlp
export OTEL_METRICS_EXPORTER=otlp
export OTEL_LOGS_EXPORTER=otlp
export OTEL_PYTHON_LOGGING_AUTO_INSTRUMENTATION_ENABLED=true

opentelemetry-instrument python app.py
```

---

## 3. 核心使用示例

### 3.1 创建Span

```python
# app/services.py

import time
import random
from typing import Dict, Any
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator

from app.telemetry import telemetry_config

tracer = telemetry_config.get_tracer("order-service")


class OrderService:
    """订单服务"""

    @staticmethod
    def create_order(user_id: str, amount: float) -> Dict[str, Any]:
        """创建订单 - 使用装饰器方式"""
        # 方式1: 使用上下文管理器
        with tracer.start_as_current_span(
            "order.create",
            kind=trace.SpanKind.INTERNAL,
            attributes={
                "order.user_id": user_id,
                "order.amount": amount,
            }
        ) as span:
            try:
                # 记录事件
                span.add_event("Order validation started")
                OrderService._validate_order(user_id, amount)
                span.add_event("Order validation completed")

                # 生成订单ID
                order_id = f"ORD-{random.randint(1000, 9999)}"
                span.set_attribute("order.id", order_id)

                # 处理支付
                span.add_event("Payment processing started")
                payment_success = OrderService._process_payment(order_id, amount)

                if not payment_success:
                    raise Exception("Payment processing failed")

                span.add_event("Payment completed", {
                    "payment.transaction_id": f"txn_{order_id}",
                    "payment.amount": amount,
                })

                # 设置成功状态
                span.set_status(Status(StatusCode.OK))

                return {
                    "order_id": order_id,
                    "user_id": user_id,
                    "amount": amount,
                    "status": "created"
                }

            except Exception as e:
                # 记录异常
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR, str(e)))
                raise

    @staticmethod
    def _validate_order(user_id: str, amount: float):
        """验证订单 - 嵌套Span"""
        with tracer.start_as_current_span("order.validate") as span:
            span.set_attribute("validation.user_id", user_id)

            if amount <= 0:
                raise ValueError("Amount must be greater than 0")

            span.set_attribute("validation.passed", True)
            time.sleep(0.01)  # 模拟处理时间

    @staticmethod
    def _process_payment(order_id: str, amount: float) -> bool:
        """处理支付"""
        with tracer.start_as_current_span("payment.process") as span:
            span.set_attribute("payment.order_id", order_id)
            span.set_attribute("payment.amount", amount)
            span.set_attribute("payment.gateway", "stripe")

            time.sleep(0.05)  # 模拟处理时间
            return True

    @staticmethod
    def get_order(order_id: str) -> Dict[str, Any]:
        """获取订单详情"""
        with tracer.start_as_current_span(
            "order.get",
            attributes={"order.id": order_id}
        ) as span:
            # 模拟数据库查询
            time.sleep(0.02)

            order = {
                "order_id": order_id,
                "user_id": "user123",
                "amount": 99.99,
                "status": "completed"
            }

            span.set_attribute("order.found", True)
            span.set_attribute("order.status", order["status"])

            return order

    @staticmethod
    def process_bulk_orders(order_ids: list):
        """批量处理订单 - 创建父Span和多个子Span"""
        with tracer.start_as_current_span(
            "order.bulk_process",
            attributes={"order.count": len(order_ids)}
        ) as parent_span:

            results = []
            for order_id in order_ids:
                # 创建子Span
                with tracer.start_as_current_span(
                    "order.process_single",
                    attributes={"order.id": order_id}
                ) as child_span:
                    try:
                        result = OrderService.get_order(order_id)
                        child_span.set_attribute("order.status", result["status"])
                        child_span.set_status(Status(StatusCode.OK))
                        results.append(result)
                    except Exception as e:
                        child_span.record_exception(e)
                        child_span.set_status(Status(StatusCode.ERROR, str(e)))

            parent_span.set_attribute("order.processed_count", len(results))
            return results
```

### 3.2 记录指标

```python
# app/metrics.py

from opentelemetry import metrics
from opentelemetry.metrics import CallbackOptions, Observation
from app.telemetry import telemetry_config

meter = telemetry_config.get_meter("order-service")

# 计数器
order_counter = meter.create_counter(
    name="orders.total",
    description="Total number of orders",
    unit="1"
)

order_error_counter = meter.create_counter(
    name="orders.errors",
    description="Total number of order errors",
    unit="1"
)

# 直方图
order_value_histogram = meter.create_histogram(
    name="order.value",
    description="Order value distribution",
    unit="USD"
)

order_processing_time = meter.create_histogram(
    name="order.processing.duration",
    description="Order processing time",
    unit="ms"
)

# 可观测Gauge（异步指标）
queue_size_gauge = meter.create_observable_gauge(
    name="queue.size",
    description="Current queue size",
    unit="1",
    callbacks=[lambda options: [Observation(value=get_queue_size())]]
)

# UpDownCounter
active_connections = meter.create_up_down_counter(
    name="connections.active",
    description="Number of active connections",
    unit="1"
)

# 模拟队列大小
_queue_size = 0

def get_queue_size() -> int:
    return _queue_size

def update_queue_size(delta: int):
    global _queue_size
    _queue_size += delta


class OrderMetrics:
    """订单指标工具类"""

    @staticmethod
    def record_order_created(amount: float, status: str = "success"):
        """记录订单创建"""
        order_counter.add(1, {
            "status": status,
            "service": "order-service"
        })
        order_value_histogram.record(amount, {
            "currency": "USD"
        })

    @staticmethod
    def record_order_error(error_type: str):
        """记录订单错误"""
        order_error_counter.add(1, {
            "error.type": error_type
        })

    @staticmethod
    def record_processing_time(duration_ms: float, method: str):
        """记录处理时间"""
        order_processing_time.record(duration_ms, {
            "method": method
        })

    @staticmethod
    def increment_active_connections():
        """增加活动连接数"""
        active_connections.add(1)

    @staticmethod
    def decrement_active_connections():
        """减少活动连接数"""
        active_connections.add(-1)
```

---

## 4. 框架集成

### 4.1 Flask集成

```python
# app/flask_app.py

from flask import Flask, request, jsonify
import time
import os

from opentelemetry.instrumentation.flask import FlaskInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from opentelemetry.propagate import extract, inject, set_global_textmap
from opentelemetry.propagators.composite import CompositePropagator
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator
from opentelemetry.baggage.propagation import W3CBaggagePropagator

from app.telemetry import init_telemetry, telemetry_config
from app.services import OrderService
from app.metrics import OrderMetrics

# 初始化遥测
telemetry = init_telemetry()
tracer = telemetry_config.get_tracer("flask-app")

def create_app():
    """创建Flask应用"""
    app = Flask(__name__)

    # 自动Instrument Flask
    FlaskInstrumentor().instrument_app(app)

    # 自动Instrument Requests库
    RequestsInstrumentor().instrument()

    @app.before_request
    def before_request():
        """请求前处理"""
        OrderMetrics.increment_active_connections()
        request.start_time = time.time()

    @app.after_request
    def after_request(response):
        """请求后处理"""
        OrderMetrics.decrement_active_connections()

        # 记录请求处理时间
        duration = (time.time() - request.start_time) * 1000
        OrderMetrics.record_processing_time(duration, request.endpoint or "unknown")

        return response

    @app.route("/health")
    def health_check():
        return jsonify({"status": "healthy"}), 200

    @app.route("/api/orders", methods=["POST"])
    def create_order():
        """创建订单"""
        data = request.get_json()
        user_id = data.get("user_id")
        amount = data.get("amount")

        if not user_id or amount is None:
            return jsonify({"error": "Missing required fields"}), 400

        try:
            with tracer.start_as_current_span("flask.create_order") as span:
                span.set_attribute("http.request.body_size", len(request.data))

                result = OrderService.create_order(user_id, amount)
                OrderMetrics.record_order_created(amount)

                return jsonify(result), 201

        except Exception as e:
            OrderMetrics.record_order_error(type(e).__name__)
            return jsonify({"error": str(e)}), 500

    @app.route("/api/orders/<order_id>", methods=["GET"])
    def get_order(order_id):
        """获取订单"""
        try:
            result = OrderService.get_order(order_id)
            return jsonify(result), 200
        except Exception as e:
            return jsonify({"error": str(e)}), 404

    @app.route("/api/orders/bulk", methods=["POST"])
    def bulk_process_orders():
        """批量处理订单"""
        data = request.get_json()
        order_ids = data.get("order_ids", [])

        results = OrderService.process_bulk_orders(order_ids)
        return jsonify({"results": results}), 200

    @app.route("/api/call-downstream")
    def call_downstream():
        """调用下游服务示例 - 传播Trace上下文"""
        import requests

        with tracer.start_as_current_span("call.downstream") as span:
            # 创建请求头并注入当前Trace上下文
            headers = {}
            inject(headers)

            span.set_attribute("downstream.url", "http://downstream-service/api/data")

            # 发送请求（自动传播Trace上下文）
            response = requests.get(
                "http://downstream-service/api/data",
                headers=headers,
                timeout=5
            )

            span.set_attribute("downstream.status_code", response.status_code)

            return jsonify({"downstream_response": response.json()}), 200

    return app


if __name__ == "__main__":
    app = create_app()
    app.run(host="0.0.0.0", port=5000, debug=False)
```

### 4.2 FastAPI集成

```python
# app/fastapi_app.py

import time
from typing import List, Optional
from contextlib import asynccontextmanager

from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import JSONResponse
from pydantic import BaseModel

from opentelemetry.instrumentation.fastapi import FastAPIInstrumentor
from opentelemetry.instrumentation.httpx import HTTPXClientInstrumentor
from opentelemetry import trace

from app.telemetry import init_telemetry, telemetry_config
from app.services import OrderService
from app.metrics import OrderMetrics

# 初始化遥测
telemetry = init_telemetry()
tracer = telemetry_config.get_tracer("fastapi-app")


class OrderCreateRequest(BaseModel):
    user_id: str
    amount: float


class OrderResponse(BaseModel):
    order_id: str
    user_id: str
    amount: float
    status: str


class BulkProcessRequest(BaseModel):
    order_ids: List[str]


@asynccontextmanager
async def lifespan(app: FastAPI):
    """应用生命周期管理"""
    # 启动时
    print("FastAPI app starting...")
    yield
    # 关闭时
    print("FastAPI app shutting down...")
    telemetry_config.shutdown()


app = FastAPI(
    title="Order Service API",
    description="Order management service with OpenTelemetry",
    version="1.0.0",
    lifespan=lifespan
)

# 自动Instrument FastAPI
FastAPIInstrumentor.instrument_app(app)

# Instrument HTTPX客户端
HTTPXClientInstrumentor().instrument()


@app.middleware("http")
async def metrics_middleware(request: Request, call_next):
    """指标收集中间件"""
    start_time = time.time()
    OrderMetrics.increment_active_connections()

    try:
        response = await call_next(request)

        # 记录处理时间
        duration = (time.time() - start_time) * 1000
        OrderMetrics.record_processing_time(
            duration,
            request.url.path
        )

        return response
    finally:
        OrderMetrics.decrement_active_connections()


@app.get("/health")
async def health_check():
    """健康检查"""
    return {"status": "healthy"}


@app.post("/api/orders", response_model=OrderResponse, status_code=201)
async def create_order(order_req: OrderCreateRequest, request: Request):
    """创建新订单"""
    try:
        with tracer.start_as_current_span("fastapi.create_order") as span:
            span.set_attribute("http.request.body_size", len(await request.body()))

            result = OrderService.create_order(
                order_req.user_id,
                order_req.amount
            )

            OrderMetrics.record_order_created(order_req.amount)

            return OrderResponse(**result)

    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        OrderMetrics.record_order_error(type(e).__name__)
        raise HTTPException(status_code=500, detail=str(e))


@app.get("/api/orders/{order_id}", response_model=OrderResponse)
async def get_order(order_id: str):
    """获取订单详情"""
    try:
        result = OrderService.get_order(order_id)
        return OrderResponse(**result)
    except Exception as e:
        raise HTTPException(status_code=404, detail="Order not found")


@app.post("/api/orders/bulk")
async def bulk_process_orders(request: BulkProcessRequest):
    """批量处理订单"""
    results = OrderService.process_bulk_orders(request.order_ids)
    return {"results": results, "count": len(results)}


@app.get("/api/async-operation")
async def async_operation():
    """异步操作示例"""
    import asyncio

    with tracer.start_as_current_span("async.operation") as span:
        span.set_attribute("operation.type", "async_io")

        # 模拟异步操作
        await asyncio.sleep(0.1)

        span.add_event("Async operation completed")

        return {"status": "completed"}


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
```

### 4.3 Django集成

```python
# app/django_app.py

# settings.py

INSTALLED_APPS = [
    # ... 其他应用
    'opentelemetry.instrumentation.django',
]

MIDDLEWARE = [
    'opentelemetry.instrumentation.django.middleware.OpenTelemetryMiddleware',
    # ... 其他中间件
]

# OpenTelemetry配置
OTEL_PYTHON_DJANGO_INSTRUMENT = True
OTEL_SERVICE_NAME = 'django-order-service'


# app/views.py

import json
import time
from django.http import JsonResponse
from django.views import View
from django.views.decorators.csrf import csrf_exempt
from django.utils.decorators import method_decorator

from opentelemetry import trace
from opentelemetry.instrumentation.django import DjangoInstrumentor

from app.telemetry import init_telemetry, telemetry_config
from app.services import OrderService
from app.metrics import OrderMetrics

# 初始化遥测
telemetry = init_telemetry()
tracer = telemetry_config.get_tracer("django-app")

# 自动Instrument Django
DjangoInstrumentor().instrument()


@csrf_exempt
def health_check(request):
    """健康检查"""
    return JsonResponse({"status": "healthy"})


@csrf_exempt
def create_order(request):
    """创建订单"""
    if request.method != "POST":
        return JsonResponse({"error": "Method not allowed"}, status=405)

    try:
        data = json.loads(request.body)
        user_id = data.get("user_id")
        amount = data.get("amount")

        if not user_id or amount is None:
            return JsonResponse({"error": "Missing required fields"}, status=400)

        with tracer.start_as_current_span("django.create_order") as span:
            span.set_attribute("http.request.body_size", len(request.body))

            result = OrderService.create_order(user_id, amount)
            OrderMetrics.record_order_created(amount)

            return JsonResponse(result, status=201)

    except Exception as e:
        OrderMetrics.record_order_error(type(e).__name__)
        return JsonResponse({"error": str(e)}, status=500)


@csrf_exempt
def get_order(request, order_id):
    """获取订单"""
    if request.method != "GET":
        return JsonResponse({"error": "Method not allowed"}, status=405)

    try:
        result = OrderService.get_order(order_id)
        return JsonResponse(result)
    except Exception as e:
        return JsonResponse({"error": "Order not found"}, status=404)


class OrderView(View):
    """基于类的视图示例"""

    def get(self, request, order_id=None):
        with tracer.start_as_current_span("django.OrderView.get"):
            if order_id:
                result = OrderService.get_order(order_id)
                return JsonResponse(result)
            return JsonResponse({"orders": []})

    def post(self, request):
        with tracer.start_as_current_span("django.OrderView.post"):
            data = json.loads(request.body)
            result = OrderService.create_order(
                data.get("user_id"),
                data.get("amount")
            )
            return JsonResponse(result, status=201)


# urls.py
from django.urls import path
from . import views

urlpatterns = [
    path('health/', views.health_check, name='health'),
    path('api/orders/', views.create_order, name='create_order'),
    path('api/orders/<str:order_id>/', views.get_order, name='get_order'),
]
```

---

## 5. 异步支持

### 5.1 异步Span创建

```python
# app/async_services.py

import asyncio
from typing import List
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode

from app.telemetry import telemetry_config

tracer = telemetry_config.get_tracer("async-service")


class AsyncOrderService:
    """异步订单服务"""

    @staticmethod
    async def async_create_order(user_id: str, amount: float) -> dict:
        """异步创建订单"""
        # 在异步函数中使用start_as_current_span
        with tracer.start_as_current_span(
            "async_order.create",
            attributes={
                "order.user_id": user_id,
                "order.amount": amount,
            }
        ) as span:
            try:
                # 模拟异步数据库操作
                await asyncio.sleep(0.01)

                order_id = f"ASYNC-ORD-{hash(user_id) % 10000}"
                span.set_attribute("order.id", order_id)

                # 模拟异步支付处理
                await AsyncOrderService._async_process_payment(order_id, amount)

                span.set_status(Status(StatusCode.OK))

                return {
                    "order_id": order_id,
                    "user_id": user_id,
                    "amount": amount,
                    "status": "created"
                }

            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR, str(e)))
                raise

    @staticmethod
    async def _async_process_payment(order_id: str, amount: float):
        """异步处理支付"""
        with tracer.start_as_current_span("async_payment.process") as span:
            span.set_attribute("payment.order_id", order_id)
            span.set_attribute("payment.amount", amount)

            # 模拟异步支付API调用
            await asyncio.sleep(0.05)

            span.add_event("Payment completed")

    @staticmethod
    async def process_orders_concurrently(order_ids: List[str]) -> List[dict]:
        """并发处理多个订单"""
        with tracer.start_as_current_span(
            "async_order.bulk_process",
            attributes={"order.count": len(order_ids)}
        ) as parent_span:

            # 创建并发任务
            tasks = [
                AsyncOrderService._process_single_order(order_id)
                for order_id in order_ids
            ]

            # 并发执行
            results = await asyncio.gather(*tasks, return_exceptions=True)

            # 过滤异常
            successful_results = [
                r for r in results if not isinstance(r, Exception)
            ]

            parent_span.set_attribute(
                "order.processed_count",
                len(successful_results)
            )

            return successful_results

    @staticmethod
    async def _process_single_order(order_id: str) -> dict:
        """处理单个订单"""
        with tracer.start_as_current_span(
            "async_order.process_single",
            attributes={"order.id": order_id}
        ) as span:
            try:
                # 模拟处理
                await asyncio.sleep(0.02)

                result = {
                    "order_id": order_id,
                    "status": "processed"
                }

                span.set_status(Status(StatusCode.OK))
                return result

            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR, str(e)))
                raise


# 异步上下文传播示例
async def async_context_propagation_example():
    """异步上下文传播示例"""
    from opentelemetry.propagate import extract, inject
    from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator

    # 创建父Span
    with tracer.start_as_current_span("parent.async_operation") as parent_span:

        # 将上下文注入carrier
        carrier = {}
        inject(carrier)

        # 模拟异步任务分发
        async def async_task(task_id: int, carrier: dict):
            # 从carrier提取上下文
            ctx = extract(carrier)

            # 使用提取的上下文创建子Span
            with tracer.start_as_current_span(
                f"async_task.{task_id}",
                context=ctx
            ) as span:
                span.set_attribute("task.id", task_id)
                await asyncio.sleep(0.01)
                return f"Task {task_id} completed"

        # 并发执行多个任务
        tasks = [
            async_task(i, carrier.copy())
            for i in range(3)
        ]

        results = await asyncio.gather(*tasks)
        return results
```

### 5.2 异步HTTP客户端集成

```python
# app/async_http_client.py

import httpx
from opentelemetry import trace
from opentelemetry.instrumentation.httpx import HTTPXClientInstrumentor

from app.telemetry import telemetry_config

tracer = telemetry_config.get_tracer("async-http-client")

# 自动Instrument HTTPX
HTTPXClientInstrumentor().instrument()


class AsyncHttpClient:
    """异步HTTP客户端"""

    def __init__(self, base_url: str):
        self.base_url = base_url
        self.client = httpx.AsyncClient(base_url=base_url, timeout=30.0)

    async def get(self, path: str, **kwargs):
        """GET请求"""
        with tracer.start_as_current_span(
            "httpx.get",
            attributes={
                "http.url": f"{self.base_url}{path}",
                "http.method": "GET",
            }
        ) as span:
            response = await self.client.get(path, **kwargs)
            span.set_attribute("http.status_code", response.status_code)
            return response

    async def post(self, path: str, **kwargs):
        """POST请求"""
        with tracer.start_as_current_span(
            "httpx.post",
            attributes={
                "http.url": f"{self.base_url}{path}",
                "http.method": "POST",
            }
        ) as span:
            response = await self.client.post(path, **kwargs)
            span.set_attribute("http.status_code", response.status_code)
            return response

    async def close(self):
        """关闭客户端"""
        await self.client.aclose()


# 使用示例
async def fetch_user_data(user_id: str):
    """获取用户数据"""
    client = AsyncHttpClient("http://user-service:8080")

    try:
        response = await client.get(f"/api/users/{user_id}")
        return response.json()
    finally:
        await client.close()
```

---

## 6. 生产环境最佳实践

### 6.1 采样配置

```python
# app/sampling.py

from opentelemetry.sdk.trace.sampling import (
    Sampler,
    SamplingResult,
    Decision,
    TraceIdRatioBased,
    ParentBased,
)
from opentelemetry.trace import SpanKind
from opentelemetry.context import Context
from opentelemetry.sdk.trace import TracerProvider


class CustomSampler(Sampler):
    """自定义采样器"""

    def __init__(self, base_ratio: float = 0.1):
        self.base_sampler = TraceIdRatioBased(base_ratio)

    def should_sample(
        self,
        parent_context: Context,
        trace_id: int,
        name: str,
        kind: SpanKind,
        attributes: dict,
        links: tuple,
        trace_state,
    ) -> SamplingResult:

        # 对健康检查不采样
        if "health" in name.lower():
            return SamplingResult(Decision.DROP)

        # 对错误全量采样
        if "error" in name.lower() or name.endswith("Exception"):
            return SamplingResult(Decision.RECORD_AND_SAMPLE)

        # 对关键操作全量采样
        if any(keyword in name for keyword in ["payment", "order/create", "checkout"]):
            return SamplingResult(Decision.RECORD_AND_SAMPLE)

        # 其他按基础采样率
        return self.base_sampler.should_sample(
            parent_context, trace_id, name, kind, attributes, links, trace_state
        )

    def get_description(self) -> str:
        return "CustomSampler"


# 创建基于父Span的采样器
def create_parent_based_sampler(base_ratio: float = 0.1) -> Sampler:
    """创建基于父Span的采样器"""
    root_sampler = TraceIdRatioBased(base_ratio)

    return ParentBased(
        root=root_sampler,
        remote_parent_sampled=TraceIdRatioBased(1.0),   # 远程父Span采样时总是采样
        remote_parent_not_sampled=TraceIdRatioBased(0.0),  # 远程父Span未采样时不采样
        local_parent_sampled=TraceIdRatioBased(1.0),    # 本地父Span采样时总是采样
        local_parent_not_sampled=root_sampler,          # 本地父Span未采样时按基础采样率
    )


# 应用到配置
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.resources import Resource

tracer_provider = TracerProvider(
    sampler=CustomSampler(base_ratio=0.1),
    resource=Resource.create({"service.name": "order-service"}),
)
```

### 6.2 优雅关闭和错误处理

```python
# app/shutdown.py

import atexit
import signal
import sys
from typing import List

from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.metrics import MeterProvider


class GracefulShutdownManager:
    """优雅关闭管理器"""

    def __init__(self):
        self._providers: List[object] = []
        self._shutdown_hooks: List[callable] = []
        self._is_shutting_down = False

        # 注册信号处理器
        signal.signal(signal.SIGTERM, self._signal_handler)
        signal.signal(signal.SIGINT, self._signal_handler)

        # 注册atexit
        atexit.register(self.shutdown)

    def register_provider(self, provider):
        """注册遥测提供者"""
        self._providers.append(provider)

    def register_shutdown_hook(self, hook: callable):
        """注册关闭钩子"""
        self._shutdown_hooks.append(hook)

    def _signal_handler(self, signum, frame):
        """信号处理器"""
        print(f"\nReceived signal {signum}, initiating graceful shutdown...")
        self.shutdown()
        sys.exit(0)

    def shutdown(self):
        """执行关闭"""
        if self._is_shutting_down:
            return

        self._is_shutting_down = True
        print("Shutting down OpenTelemetry...")

        # 执行自定义关闭钩子
        for hook in self._shutdown_hooks:
            try:
                hook()
            except Exception as e:
                print(f"Error in shutdown hook: {e}")

        # 关闭所有提供者
        for provider in self._providers:
            try:
                if hasattr(provider, 'shutdown'):
                    provider.shutdown()
                    print(f"Shutdown {type(provider).__name__} completed")
            except Exception as e:
                print(f"Error shutting down {type(provider).__name__}: {e}")

        print("OpenTelemetry shutdown completed")


# 安全包装Tracer
class SafeTracer:
    """安全Tracer包装"""

    def __init__(self, tracer):
        self._tracer = tracer

    def start_as_current_span(self, name, **kwargs):
        """安全地启动Span"""
        try:
            return self._tracer.start_as_current_span(name, **kwargs)
        except Exception as e:
            import logging
            logging.getLogger(__name__).warning(f"Failed to start span {name}: {e}")

            # 返回一个虚拟的上下文管理器
            from contextlib import contextmanager

            @contextmanager
            def noop_context():
                yield None

            return noop_context()

    def start_span(self, name, **kwargs):
        """安全地创建Span"""
        try:
            return self._tracer.start_span(name, **kwargs)
        except Exception as e:
            import logging
            logging.getLogger(__name__).warning(f"Failed to create span {name}: {e}")
            from opentelemetry.trace import INVALID_SPAN
            return INVALID_SPAN


# 使用示例
shutdown_manager = GracefulShutdownManager()

# 在初始化遥测时注册
# shutdown_manager.register_provider(tracer_provider)
# shutdown_manager.register_provider(meter_provider)
```

### 6.3 日志集成

```python
# app/logging_config.py

import logging
import sys
from pythonjsonlogger import jsonlogger

from opentelemetry import trace
from opentelemetry.instrumentation.logging import LoggingInstrumentor


def setup_logging(service_name: str, log_level: str = "INFO"):
    """配置结构化日志"""

    # 自动Instrument logging
    LoggingInstrumentor().instrument(
        set_logging_format=True,
        logging_format="%(asctime)s - %(name)s - %(levelname)s - %(message)s [trace_id=%(otelTraceID)s span_id=%(otelSpanID)s]"
    )

    # 创建JSON格式处理器
    formatter = jsonlogger.JsonFormatter(
        fmt='%(asctime)s %(name)s %(levelname)s %(message)s %(otelTraceID)s %(otelSpanID)s',
        rename_fields={
            'otelTraceID': 'trace_id',
            'otelSpanID': 'span_id',
        }
    )

    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(formatter)

    # 配置根日志器
    root_logger = logging.getLogger()
    root_logger.setLevel(getattr(logging, log_level.upper()))
    root_logger.handlers = []  # 清除现有处理器
    root_logger.addHandler(handler)

    # 设置第三方库日志级别
    logging.getLogger("urllib3").setLevel(logging.WARNING)
    logging.getLogger("requests").setLevel(logging.WARNING)

    return root_logger


class TraceContextFilter(logging.Filter):
    """添加Trace上下文到日志记录"""

    def filter(self, record):
        current_span = trace.get_current_span()
        span_context = current_span.get_span_context()

        if span_context.is_valid:
            record.trace_id = span_context.trace_id
            record.span_id = span_context.span_id
            record.trace_flags = span_context.trace_flags
        else:
            record.trace_id = None
            record.span_id = None
            record.trace_flags = None

        return True


# 使用示例
logger = logging.getLogger(__name__)

def example_function():
    """示例函数"""
    logger.info("Processing started")

    try:
        # 业务逻辑
        result = 1 / 1
        logger.info("Processing completed", extra={"result": result})
    except Exception as e:
        logger.error("Processing failed", exc_info=True)
```

---

## 7. 调试技巧

### 7.1 本地开发配置

```python
# app/dev_telemetry.py

import os
from opentelemetry import trace, metrics
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import ConsoleSpanExporter, SimpleSpanProcessor
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import ConsoleMetricExporter, PeriodicExportingMetricReader


def init_dev_telemetry():
    """初始化开发环境遥测（输出到控制台）"""

    # 控制台Trace导出
    tracer_provider = TracerProvider()
    tracer_provider.add_span_processor(
        SimpleSpanProcessor(ConsoleSpanExporter())
    )
    trace.set_tracer_provider(tracer_provider)

    # 控制台Metrics导出
    metric_reader = PeriodicExportingMetricReader(
        ConsoleMetricExporter(),
        export_interval_millis=5000,
    )
    meter_provider = MeterProvider(metric_readers=[metric_reader])
    metrics.set_meter_provider(meter_provider)

    print("Development telemetry initialized (console output)")
    return tracer_provider, meter_provider


# 开发环境使用
if os.getenv("ENV") == "development":
    init_dev_telemetry()
```

### 7.2 验证Trace传播

```python
# app/trace_verifier.py

from opentelemetry import trace
from opentelemetry.propagate import extract, inject

def log_current_trace_info(logger=None):
    """记录当前Trace信息"""
    import logging
    logger = logger or logging.getLogger(__name__)

    current_span = trace.get_current_span()
    span_context = current_span.get_span_context()

    if span_context.is_valid:
        logger.info("Current Trace Context:")
        logger.info(f"  TraceID: {span_context.trace_id:032x}")
        logger.info(f"  SpanID: {span_context.span_id:016x}")
        logger.info(f"  Sampled: {span_context.is_sampled}")
        logger.info(f"  TraceFlags: {span_context.trace_flags}")
    else:
        logger.warning("No valid trace context found")


def verify_propagation(carrier: dict) -> bool:
    """验证Trace传播"""
    import logging
    logger = logging.getLogger(__name__)

    # 提取上下文
    ctx = extract(carrier)

    # 从上下文中获取Span
    span = trace.Span.from_context(ctx)
    span_context = span.get_span_context()

    if span_context.is_valid:
        logger.info("Propagation verified successfully:")
        logger.info(f"  Extracted TraceID: {span_context.trace_id:032x}")
        logger.info(f"  Extracted SpanID: {span_context.span_id:016x}")
        return True
    else:
        logger.error("Propagation verification failed - invalid span context")
        return False
```

### 7.3 测试Span创建

```python
# tests/test_telemetry.py

import unittest
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export.in_memory_span_exporter import InMemorySpanExporter
from opentelemetry.sdk.trace.export import SimpleSpanProcessor

from app.services import OrderService


class TestTelemetry(unittest.TestCase):
    """遥测测试"""

    def setUp(self):
        """测试前置"""
        self.exporter = InMemorySpanExporter()

        tracer_provider = TracerProvider()
        tracer_provider.add_span_processor(
            SimpleSpanProcessor(self.exporter)
        )
        trace.set_tracer_provider(tracer_provider)

        self.tracer = trace.get_tracer("test")

    def tearDown(self):
        """测试后置"""
        self.exporter.clear()

    def test_create_order_creates_span(self):
        """测试创建订单生成Span"""
        # 执行
        OrderService.create_order("user123", 99.99)

        # 验证
        spans = self.exporter.get_finished_spans()
        self.assertTrue(len(spans) > 0)

        # 查找主Span
        main_spans = [s for s in spans if "order.create" in s.name]
        self.assertEqual(len(main_spans), 1)

        main_span = main_spans[0]
        self.assertEqual(
            main_span.attributes["order.user_id"],
            "user123"
        )
        self.assertEqual(
            main_span.attributes["order.amount"],
            99.99
        )

    def test_span_hierarchy(self):
        """测试Span层级关系"""
        OrderService.create_order("user123", 50.0)

        spans = self.exporter.get_finished_spans()

        # 验证存在父子关系
        span_names = [s.name for s in spans]
        self.assertIn("order.create", span_names)
        self.assertIn("order.validate", span_names)
        self.assertIn("payment.process", span_names)


if __name__ == "__main__":
    unittest.main()
```

---

## 8. 参考资源

- [OpenTelemetry Python官方文档](https://opentelemetry.io/docs/languages/python/)
- [OpenTelemetry Python SDK GitHub](https://github.com/open-telemetry/opentelemetry-python)
- [OpenTelemetry Python Contrib](https://github.com/open-telemetry/opentelemetry-python-contrib)
- [Flask官方文档](https://flask.palletsprojects.com/)
- [FastAPI官方文档](https://fastapi.tiangolo.com/)
- [Django官方文档](https://docs.djangoproject.com/)

**文档维护**: OTLP项目团队
**最后更新**: 2026-03-17
