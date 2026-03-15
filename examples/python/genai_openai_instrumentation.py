"""
OpenAI GenAI Instrumentation Example
基于OpenTelemetry GenAI Semantic Conventions v1.37+

功能:
- 完整的GenAI语义约定实现
- Token使用监控
- 成本计算
- 延迟追踪
- 错误处理
"""

import os
import time
import json
from typing import List, Dict, Any, Optional
from openai import OpenAI
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource, SERVICE_NAME
from opentelemetry.trace import Status, StatusCode
from dotenv import load_dotenv

# 加载环境变量
load_dotenv()

# 初始化OpenTelemetry
def init_telemetry():
    resource = Resource(attributes={
        SERVICE_NAME: "genai-openai-demo"
    })
    provider = TracerProvider(resource=resource)
    processor = BatchSpanProcessor(OTLPSpanExporter())
    provider.add_span_processor(processor)
    trace.set_tracer_provider(provider)
    return trace.get_tracer("genai-openai-demo")

tracer = init_telemetry()

# 模型定价 (每1M tokens)
MODEL_PRICING = {
    "gpt-4o": {"input": 2.50, "output": 10.00},
    "gpt-4o-mini": {"input": 0.15, "output": 0.60},
    "gpt-4-turbo": {"input": 10.00, "output": 30.00},
}


class OpenAIInstrumentedClient:
    """带完整OpenTelemetry仪器化的OpenAI客户端"""
    
    def __init__(self, api_key: Optional[str] = None):
        self.client = OpenAI(api_key=api_key or os.getenv("OPENAI_API_KEY"))
    
    def _calculate_cost(self, model: str, input_tokens: int, output_tokens: int) -> float:
        """计算API调用成本"""
        pricing = MODEL_PRICING.get(model, MODEL_PRICING["gpt-4o"])
        input_cost = (input_tokens / 1_000_000) * pricing["input"]
        output_cost = (output_tokens / 1_000_000) * pricing["output"]
        return round(input_cost + output_cost, 6)
    
    def chat_completion(
        self,
        messages: List[Dict[str, str]],
        model: str = "gpt-4o",
        temperature: float = 0.7,
        max_tokens: int = 4096,
        session_id: Optional[str] = None,
        user_id: Optional[str] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        执行带完整仪器化的Chat Completion
        
        Args:
            messages: 对话消息列表
            model: 模型名称
            temperature: 温度参数
            max_tokens: 最大token数
            session_id: 会话ID
            user_id: 用户ID
            **kwargs: 其他OpenAI参数
        
        Returns:
            包含响应内容、使用统计、成本等的字典
        """
        
        with tracer.start_as_current_span("gen_ai.chat") as span:
            # ===== 必需属性 =====
            span.set_attribute("gen_ai.system", "openai")
            span.set_attribute("gen_ai.operation.name", "chat")
            span.set_attribute("gen_ai.request.model", model)
            
            # ===== 业务上下文 =====
            if session_id:
                span.set_attribute("session.id", session_id)
            if user_id:
                span.set_attribute("user.id", user_id)
            
            # ===== 请求参数 =====
            span.set_attribute("gen_ai.request.temperature", temperature)
            span.set_attribute("gen_ai.request.max_tokens", max_tokens)
            span.set_attribute("gen_ai.request.message_count", len(messages))
            
            # 记录其他参数
            for key, value in kwargs.items():
                span.set_attribute(f"gen_ai.request.{key}", value)
            
            start_time = time.time()
            
            try:
                # 调用OpenAI API
                response = self.client.chat.completions.create(
                    model=model,
                    messages=messages,
                    temperature=temperature,
                    max_tokens=max_tokens,
                    **kwargs
                )
                
                latency_ms = (time.time() - start_time) * 1000
                
                # ===== 响应属性 =====
                span.set_attribute("gen_ai.response.model", response.model)
                span.set_attribute("gen_ai.response.id", response.id)
                span.set_attribute("gen_ai.response.finish_reason", 
                                 response.choices[0].finish_reason)
                
                # ===== Token使用统计 =====
                input_tokens = response.usage.prompt_tokens
                output_tokens = response.usage.completion_tokens
                total_tokens = response.usage.total_tokens
                
                span.set_attribute("gen_ai.usage.input_tokens", input_tokens)
                span.set_attribute("gen_ai.usage.output_tokens", output_tokens)
                span.set_attribute("gen_ai.usage.total_tokens", total_tokens)
                
                # ===== 成本和延迟 =====
                cost = self._calculate_cost(model, input_tokens, output_tokens)
                span.set_attribute("gen_ai.estimated_cost_usd", cost)
                span.set_attribute("gen_ai.latency_ms", latency_ms)
                
                # 检查截断
                if response.choices[0].finish_reason == "length":
                    span.set_attribute("gen_ai.warning", "response_truncated")
                    span.set_attribute("gen_ai.truncated", True)
                
                return {
                    "success": True,
                    "content": response.choices[0].message.content,
                    "model": response.model,
                    "response_id": response.id,
                    "finish_reason": response.choices[0].finish_reason,
                    "usage": {
                        "input_tokens": input_tokens,
                        "output_tokens": output_tokens,
                        "total_tokens": total_tokens
                    },
                    "cost_usd": cost,
                    "latency_ms": latency_ms
                }
                
            except Exception as e:
                latency_ms = (time.time() - start_time) * 1000
                span.set_attribute("gen_ai.latency_ms", latency_ms)
                span.set_attribute("error.type", type(e).__name__)
                span.set_attribute("error.message", str(e))
                span.set_status(Status(StatusCode.ERROR, str(e)))
                
                return {
                    "success": False,
                    "error": str(e),
                    "error_type": type(e).__name__,
                    "latency_ms": latency_ms
                }
    
    def create_embedding(
        self,
        text: str,
        model: str = "text-embedding-3-small",
        **kwargs
    ) -> Dict[str, Any]:
        """
        创建带仪器化的Embedding
        
        Args:
            text: 输入文本
            model: 嵌入模型
            **kwargs: 其他参数
        """
        
        with tracer.start_as_current_span("gen_ai.embeddings") as span:
            span.set_attribute("gen_ai.system", "openai")
            span.set_attribute("gen_ai.operation.name", "embeddings")
            span.set_attribute("gen_ai.request.model", model)
            span.set_attribute("gen_ai.input.length", len(text))
            
            start_time = time.time()
            
            try:
                response = self.client.embeddings.create(
                    model=model,
                    input=text,
                    **kwargs
                )
                
                latency_ms = (time.time() - start_time) * 1000
                
                # Token使用
                prompt_tokens = response.usage.prompt_tokens
                total_tokens = response.usage.total_tokens
                
                span.set_attribute("gen_ai.usage.prompt_tokens", prompt_tokens)
                span.set_attribute("gen_ai.usage.total_tokens", total_tokens)
                span.set_attribute("gen_ai.embedding.dimensions", 
                                 len(response.data[0].embedding))
                span.set_attribute("gen_ai.latency_ms", latency_ms)
                
                return {
                    "success": True,
                    "embedding": response.data[0].embedding,
                    "model": response.model,
                    "usage": {
                        "prompt_tokens": prompt_tokens,
                        "total_tokens": total_tokens
                    },
                    "latency_ms": latency_ms
                }
                
            except Exception as e:
                span.set_attribute("error.type", type(e).__name__)
                span.set_attribute("error.message", str(e))
                span.set_status(Status(StatusCode.ERROR, str(e)))
                
                return {
                    "success": False,
                    "error": str(e),
                    "error_type": type(e).__name__
                }
    
    def batch_embeddings(
        self,
        texts: List[str],
        model: str = "text-embedding-3-small",
        **kwargs
    ) -> Dict[str, Any]:
        """
        批量创建Embedding
        
        Args:
            texts: 文本列表
            model: 嵌入模型
        """
        
        with tracer.start_as_current_span("gen_ai.embeddings.batch") as span:
            span.set_attribute("gen_ai.system", "openai")
            span.set_attribute("gen_ai.operation.name", "embeddings")
            span.set_attribute("gen_ai.request.model", model)
            span.set_attribute("gen_ai.batch.size", len(texts))
            
            start_time = time.time()
            
            try:
                response = self.client.embeddings.create(
                    model=model,
                    input=texts,
                    **kwargs
                )
                
                latency_ms = (time.time() - start_time) * 1000
                
                span.set_attribute("gen_ai.usage.total_tokens", response.usage.total_tokens)
                span.set_attribute("gen_ai.latency_ms", latency_ms)
                
                return {
                    "success": True,
                    "embeddings": [item.embedding for item in response.data],
                    "model": response.model,
                    "usage": {
                        "total_tokens": response.usage.total_tokens
                    },
                    "latency_ms": latency_ms
                }
                
            except Exception as e:
                span.set_attribute("error.type", type(e).__name__)
                span.set_status(Status(StatusCode.ERROR, str(e)))
                
                return {
                    "success": False,
                    "error": str(e)
                }


def demo_chat_completion():
    """演示：带仪器化的Chat Completion"""
    print("=" * 60)
    print("演示：Chat Completion with OpenTelemetry")
    print("=" * 60)
    
    client = OpenAIInstrumentedClient()
    
    # 示例1：简单对话
    print("\n[示例1] 简单对话")
    result = client.chat_completion(
        messages=[
            {"role": "user", "content": "解释量子计算的基本原理，用一句话概括"}
        ],
        model="gpt-4o-mini",
        temperature=0.7,
        session_id="demo_session_001",
        user_id="demo_user_123"
    )
    
    if result["success"]:
        print(f"💬 回复: {result['content'][:100]}...")
        print(f"📊 Token: {result['usage']['total_tokens']} "
              f"(输入: {result['usage']['input_tokens']}, "
              f"输出: {result['usage']['output_tokens']})")
        print(f"💰 成本: ${result['cost_usd']:.6f}")
        print(f"⏱️  延迟: {result['latency_ms']:.0f}ms")
    else:
        print(f"❌ 错误: {result['error']}")
    
    # 示例2：多轮对话
    print("\n[示例2] 多轮对话")
    result = client.chat_completion(
        messages=[
            {"role": "system", "content": "你是一个有帮助的助手"},
            {"role": "user", "content": "你好"},
            {"role": "assistant", "content": "你好！有什么可以帮助你的？"},
            {"role": "user", "content": "解释一下Python的装饰器"}
        ],
        model="gpt-4o-mini",
        temperature=0.5,
        max_tokens=1000
    )
    
    if result["success"]:
        print(f"💬 回复: {result['content'][:100]}...")
        print(f"📊 Token: {result['usage']['total_tokens']}")
        print(f"💰 成本: ${result['cost_usd']:.6f}")
        print(f"⏱️  延迟: {result['latency_ms']:.0f}ms")
    
    # 示例3：使用不同模型对比
    print("\n[示例3] 模型对比")
    for model in ["gpt-4o-mini", "gpt-4o"]:
        result = client.chat_completion(
            messages=[{"role": "user", "content": "Hello"}],
            model=model,
            max_tokens=10
        )
        if result["success"]:
            print(f"{model:15} | Token: {result['usage']['total_tokens']:3} | "
                  f"成本: ${result['cost_usd']:.6f} | "
                  f"延迟: {result['latency_ms']:4.0f}ms")


def demo_embeddings():
    """演示：带仪器化的Embeddings"""
    print("\n" + "=" * 60)
    print("演示：Embeddings with OpenTelemetry")
    print("=" * 60)
    
    client = OpenAIInstrumentedClient()
    
    # 示例1：单个文本
    print("\n[示例1] 单个文本Embedding")
    result = client.create_embedding(
        text="OpenTelemetry是一个开源的可观测性框架",
        model="text-embedding-3-small"
    )
    
    if result["success"]:
        print(f"✅ Embedding维度: {len(result['embedding'])}")
        print(f"📊 Token使用: {result['usage']['total_tokens']}")
        print(f"⏱️  延迟: {result['latency_ms']:.0f}ms")
    
    # 示例2：批量处理
    print("\n[示例2] 批量Embedding")
    texts = [
        "OpenTelemetry是云原生计算基金会项目",
        "GenAI语义约定标准化了LLM观测数据",
        "可观测性对于AI应用至关重要"
    ]
    
    result = client.batch_embeddings(
        texts=texts,
        model="text-embedding-3-small"
    )
    
    if result["success"]:
        print(f"✅ 处理文本数: {len(result['embeddings'])}")
        print(f"📊 总Token: {result['usage']['total_tokens']}")
        print(f"⏱️  延迟: {result['latency_ms']:.0f}ms")


def demo_error_handling():
    """演示：错误处理"""
    print("\n" + "=" * 60)
    print("演示：Error Handling")
    print("=" * 60)
    
    client = OpenAIInstrumentedClient()
    
    # 示例：无效模型
    print("\n[示例] 无效模型名称")
    result = client.chat_completion(
        messages=[{"role": "user", "content": "Hello"}],
        model="invalid-model-name"
    )
    
    if not result["success"]:
        print(f"✅ 错误被捕获: {result['error_type']}")
        print(f"📝 错误信息: {result['error'][:100]}...")


def main():
    """主函数"""
    print("🚀 OpenAI GenAI Instrumentation Demo")
    print("=" * 60)
    
    # 运行演示
    demo_chat_completion()
    demo_embeddings()
    demo_error_handling()
    
    print("\n" + "=" * 60)
    print("✅ 演示完成！请检查您的OpenTelemetry后端查看追踪数据。")
    print("=" * 60)


if __name__ == "__main__":
    main()
