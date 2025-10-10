#!/usr/bin/env python3
"""
OpenTelemetry Python OTLP Trace Example

这个示例展示如何使用OpenTelemetry Python SDK发送trace数据到OTLP Collector。
"""

import time
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import SERVICE_NAME, SERVICE_VERSION, Resource
from opentelemetry.trace import Status, StatusCode


def main():
    """主函数：设置OpenTelemetry并创建示例trace"""
    
    # 1. 创建Resource - 描述服务的元数据
    resource = Resource(attributes={
        SERVICE_NAME: "hello-trace-python",
        SERVICE_VERSION: "1.0.0",
        "environment": "development",
        "team": "observability"
    })
    
    # 2. 创建TracerProvider
    provider = TracerProvider(resource=resource)
    
    # 3. 创建OTLP导出器
    # 连接到本地Collector的gRPC端点(端口4317)
    otlp_exporter = OTLPSpanExporter(
        endpoint="localhost:4317",
        insecure=True  # 开发环境使用非加密连接
    )
    
    # 4. 创建批处理Span处理器
    # 批处理可以减少网络请求，提高性能
    processor = BatchSpanProcessor(otlp_exporter)
    provider.add_span_processor(processor)
    
    # 5. 设置全局TracerProvider
    trace.set_tracer_provider(provider)
    
    print("Starting hello trace example...")
    
    # 6. 获取Tracer
    tracer = trace.get_tracer(__name__)
    
    # 7. 创建根Span
    with tracer.start_as_current_span("hello-operation") as span:
        # 添加属性
        span.set_attribute("greeting", "Hello OTLP!")
        span.set_attribute("language", "Python")
        span.set_attribute("example.version", 1)
        
        print("Doing some work...")
        time.sleep(0.1)  # 模拟工作
        
        # 8. 创建子Span
        with tracer.start_as_current_span("sub-operation") as child_span:
            child_span.set_attribute("operation", "processing")
            child_span.set_attribute("success", True)
            
            # 添加事件
            child_span.add_event(
                "processing_started",
                attributes={"item_count": 10}
            )
            
            time.sleep(0.05)  # 模拟处理
            
            child_span.add_event("processing_completed")
            
            # 设置状态
            child_span.set_status(Status(StatusCode.OK))
        
        # 9. 再创建一个子Span演示错误处理
        with tracer.start_as_current_span("error-handling") as error_span:
            try:
                # 模拟一个可能的错误
                error_span.set_attribute("attempting", "risky_operation")
                time.sleep(0.03)
                
                # 一切正常
                error_span.set_status(Status(StatusCode.OK))
                
            except Exception as e:
                # 如果出错，记录异常
                error_span.set_status(Status(StatusCode.ERROR, str(e)))
                error_span.record_exception(e)
    
    print("Trace sent successfully!")
    print("View traces at: http://localhost:16686")
    
    # 10. 关闭TracerProvider，确保所有span都已导出
    provider.shutdown()
    
    # 额外等待确保数据已发送
    time.sleep(2)
    print("Example completed!")


if __name__ == "__main__":
    main()

