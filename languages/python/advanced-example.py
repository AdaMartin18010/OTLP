import asyncio
import time
import logging
from typing import Dict, Any, Optional
from dataclasses import dataclass
from datetime import datetime

from opentelemetry import trace, metrics
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter as GrpcSpanExporter
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter as HttpSpanExporter
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter as GrpcMetricExporter
from opentelemetry.exporter.otlp.proto.http.metric_exporter import OTLPMetricExporter as HttpMetricExporter
from opentelemetry.trace import SpanKind
from opentelemetry.semantic_conventions.resource import ResourceAttributes
from opentelemetry.semantic_conventions.trace import SpanAttributes
from opentelemetry.semantic_conventions.db import DbSystemValues
from opentelemetry.semantic_conventions.http import HttpMethodValues
import os

@dataclass
class UserData:
    id: str
    name: str
    email: str
    role: str

@dataclass
class BusinessResult:
    user_id: str
    processed_at: datetime
    status: str
    data: str

@dataclass
class ApiResponse:
    status: int
    message: str
    data: str

class AdvancedOpenTelemetryExample:
    def __init__(self):
        self.endpoint = os.getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317")
        self.protocol = os.getenv("OTEL_EXPORTER_OTLP_PROTOCOL", "grpc").lower()
        self.insecure = os.getenv("OTEL_EXPORTER_OTLP_INSECURE", "true").lower() == "true"
        self.service_name = os.getenv("OTEL_SERVICE_NAME", "advanced-python-service")
        
        self.setup_tracing()
        self.setup_metrics()
        self.setup_logging()
    
    def setup_tracing(self):
        """设置分布式追踪"""
        # 配置资源
        resource = Resource.create({
            ResourceAttributes.SERVICE_NAME: self.service_name,
            ResourceAttributes.SERVICE_VERSION: "1.0.0",
            ResourceAttributes.SERVICE_INSTANCE_ID: "instance-1",
            ResourceAttributes.DEPLOYMENT_ENVIRONMENT: "production",
            ResourceAttributes.HOST_NAME: "python-server",
            ResourceAttributes.HOST_ARCH: "amd64",
            ResourceAttributes.OS_NAME: "linux",
            ResourceAttributes.OS_VERSION: "5.4.0",
        })
        
        # 配置导出器
        if self.protocol.startswith("http"):
            span_exporter = HttpSpanExporter(
                endpoint=self.endpoint,
                insecure=self.insecure,
                timeout=10,
                headers={"Authorization": "Bearer token"}
            )
        else:
            span_exporter = GrpcSpanExporter(
                endpoint=self.endpoint,
                insecure=self.insecure,
                timeout=10,
                headers={"Authorization": "Bearer token"}
            )
        
        # 配置TracerProvider
        tp = TracerProvider(resource=resource)
        tp.add_span_processor(BatchSpanProcessor(span_exporter))
        trace.set_tracer_provider(tp)
        
        self.tracer = trace.get_tracer(self.service_name)
    
    def setup_metrics(self):
        """设置指标监控"""
        # 配置资源
        resource = Resource.create({
            ResourceAttributes.SERVICE_NAME: self.service_name,
            ResourceAttributes.SERVICE_VERSION: "1.0.0",
            ResourceAttributes.SERVICE_INSTANCE_ID: "instance-1",
            ResourceAttributes.DEPLOYMENT_ENVIRONMENT: "production",
        })
        
        # 配置导出器
        if self.protocol.startswith("http"):
            metric_exporter = HttpMetricExporter(
                endpoint=self.endpoint,
                insecure=self.insecure,
                timeout=10,
                headers={"Authorization": "Bearer token"}
            )
        else:
            metric_exporter = GrpcMetricExporter(
                endpoint=self.endpoint,
                insecure=self.insecure,
                timeout=10,
                headers={"Authorization": "Bearer token"}
            )
        
        # 配置MeterProvider
        reader = PeriodicExportingMetricReader(metric_exporter, export_interval_millis=10000)
        mp = MeterProvider(resource=resource, metric_readers=[reader])
        metrics.set_meter_provider(mp)
        
        self.meter = metrics.get_meter(self.service_name)
        self.counter = self.meter.create_counter("business_operations_total")
        self.histogram = self.meter.create_histogram("business_operation_duration_seconds")
    
    def setup_logging(self):
        """设置日志记录"""
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        self.logger = logging.getLogger(self.service_name)
    
    async def simulate_business_logic(self):
        """模拟业务逻辑"""
        with self.tracer.start_as_current_span("business_logic", kind=SpanKind.SERVER) as span:
            span.set_attributes({
                "operation": "main",
                "service.name": self.service_name,
            })
            
            self.logger.info("开始业务逻辑处理")
            
            # 模拟用户认证
            auth_result = await self.authenticate_user("user123", "password")
            if not auth_result:
                self.logger.error("用户认证失败")
                return
            
            # 模拟数据库查询
            user_data = await self.query_user_data("user123")
            self.logger.info(f"查询用户数据完成: {user_data.name}")
            
            # 模拟业务处理
            result = await self.process_business_logic(user_data)
            self.logger.info(f"业务处理完成: {result.status}")
            
            # 模拟外部API调用
            api_response = await self.call_external_api(result)
            self.logger.info(f"外部API调用完成: {api_response.status}")
            
            # 记录指标
            self.counter.add(1, {"operation": "business_logic"})
            self.histogram.record(time.time(), {"operation": "business_logic"})
            
            self.logger.info("业务逻辑处理完成")
    
    async def authenticate_user(self, username: str, password: str) -> bool:
        """模拟用户认证"""
        with self.tracer.start_as_current_span("authenticate_user", kind=SpanKind.INTERNAL) as span:
            span.set_attributes({
                "user": username,
                "auth.method": "password",
            })
            
            self.logger.info("开始用户认证")
            
            # 模拟认证延迟
            await asyncio.sleep(0.1)
            
            # 模拟认证逻辑
            is_valid = username == "user123" and password == "password"
            
            span.set_attributes({
                "auth.success": is_valid,
                "auth.result": "success" if is_valid else "failure",
            })
            
            if is_valid:
                self.logger.info("用户认证成功")
            else:
                self.logger.error("用户认证失败")
            
            return is_valid
    
    async def query_user_data(self, user_id: str) -> UserData:
        """模拟数据库查询"""
        with self.tracer.start_as_current_span("query_user_data", kind=SpanKind.CLIENT) as span:
            span.set_attributes({
                SpanAttributes.DB_SYSTEM: DbSystemValues.POSTGRESQL,
                SpanAttributes.DB_OPERATION: "SELECT",
                SpanAttributes.DB_SQL_TABLE: "users",
                "user.id": user_id,
            })
            
            self.logger.info("开始查询用户数据")
            
            # 模拟数据库查询延迟
            await asyncio.sleep(0.2)
            
            # 模拟数据库查询
            user_data = UserData(
                id=user_id,
                name="John Doe",
                email="john@example.com",
                role="user"
            )
            
            span.set_attributes({
                "user.name": user_data.name,
                "user.email": user_data.email,
                "user.role": user_data.role,
            })
            
            self.logger.info(f"用户数据查询完成: {user_data.name}")
            
            return user_data
    
    async def process_business_logic(self, user_data: UserData) -> BusinessResult:
        """模拟业务处理"""
        with self.tracer.start_as_current_span("process_business_logic", kind=SpanKind.INTERNAL) as span:
            span.set_attributes({
                "user.id": user_data.id,
                "business.operation": "process",
            })
            
            self.logger.info("开始业务逻辑处理")
            
            # 模拟业务处理延迟
            await asyncio.sleep(0.3)
            
            # 模拟业务逻辑
            result = BusinessResult(
                user_id=user_data.id,
                processed_at=datetime.now(),
                status="success",
                data="processed_data"
            )
            
            span.set_attributes({
                "business.status": result.status,
                "business.data": result.data,
            })
            
            self.logger.info(f"业务逻辑处理完成: {result.status}")
            
            return result
    
    async def call_external_api(self, data: BusinessResult) -> ApiResponse:
        """模拟外部API调用"""
        with self.tracer.start_as_current_span("call_external_api", kind=SpanKind.CLIENT) as span:
            span.set_attributes({
                SpanAttributes.HTTP_METHOD: HttpMethodValues.POST,
                SpanAttributes.HTTP_URL: "https://api.example.com/process",
                SpanAttributes.HTTP_SCHEME: "https",
                SpanAttributes.HTTP_HOST: "api.example.com",
                "user.id": data.user_id,
            })
            
            self.logger.info("开始调用外部API")
            
            # 模拟API调用延迟
            await asyncio.sleep(0.15)
            
            # 模拟API调用
            response = ApiResponse(
                status=200,
                message="success",
                data="api_response_data"
            )
            
            span.set_attributes({
                SpanAttributes.HTTP_STATUS_CODE: response.status,
                "http.response.message": response.message,
            })
            
            self.logger.info(f"外部API调用完成: {response.status}")
            
            return response

async def main():
    """主函数"""
    example = AdvancedOpenTelemetryExample()
    await example.simulate_business_logic()

if __name__ == "__main__":
    asyncio.run(main())
