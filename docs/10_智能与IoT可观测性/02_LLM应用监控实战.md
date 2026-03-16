---
title: LLM应用监控实战
description: LLM应用监控实战 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 前沿技术
tags:
  - otlp
  - observability
  - performance
  - optimization
  - case-study
  - production
  - sampling
  - security
  - compliance
  - genai
  - llm
  - ai
status: published
---
# LLM应用监控实战

> **文档类型**: 实战指南
> **难度**: 中级
> **预计阅读时间**: 45分钟
> **创建日期**: 2026年3月15日

---

## 学习目标

完成本指南后，您将能够：

- ✅ 为LLM应用配置完整的OpenTelemetry仪器化
- ✅ 监控Token使用、成本和延迟
- ✅ 构建LLM应用的可观测性仪表板
- ✅ 实现生产级错误处理和降级策略

---

## 场景介绍

### 场景：智能客服系统

我们将构建一个智能客服系统，包含以下组件：

- **对话服务**: 处理用户消息，调用LLM生成回复
- **RAG检索**: 从知识库检索相关内容
- **意图识别**: 识别用户意图
- **成本监控**: 跟踪API调用成本

```text
┌─────────────────────────────────────────────────────────────────┐
│                      智能客服系统架构                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   用户消息 ──────► 意图识别 ──────► RAG检索 ──────► LLM生成       │
│       │               │              │              │           │
│       │               │              │              │           │
│       ▼               ▼              ▼              ▼           │
│   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐     │
│   │ 消息接收  │   │ 意图Span │   │ 检索Span │   │ ChatSpan │     │
│   │ Span     │   │          │   │          │   │          │     │
│   └──────────┘   └──────────┘   └──────────┘   └──────────┘     │
│       │               │              │              │           │
│       └───────────────┴──────────────┴──────────────┘           │
│                       │                                         │
│                       ▼                                         │
│           ┌─────────────────────┐                               │
│           │   OpenTelemetry     │                               │
│           │      Collector      │                               │
│           └─────────────────────┘                               │
│                       │                                         │
│                       ▼                                         │
│           ┌─────────────────────┐                               │
│           │   可观测性后端       │                               │
│           │ (OneUptime/Grafana) │                               │
│           └─────────────────────┘                               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 1. 环境准备

### 1.1 安装依赖

```bash
pip install opentelemetry-api opentelemetry-sdk opentelemetry-exporter-otlp-proto-grpc
pip install openai langchain langchain-openai
pip install pydantic python-dotenv
```

### 1.2 配置文件

```python
# config.py
import os
from pydantic import BaseSettings

class Settings(BaseSettings):
    # OpenAI配置
    openai_api_key: str = ""
    openai_model: str = "gpt-4o"

    # OpenTelemetry配置
    otel_service_name: str = "customer-service-ai"
    otel_endpoint: str = "http://localhost:4317"

    # GenAI配置
    genai_log_content: bool = False  # 生产环境设为False
    max_tokens_per_request: int = 4096
    temperature: float = 0.7

    # 成本告警阈值
    daily_cost_limit_usd: float = 100.0

    class Config:
        env_file = ".env"

settings = Settings()
```

### 1.3 OpenTelemetry初始化

```python
# telemetry.py
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource, SERVICE_NAME, SERVICE_VERSION
from opentelemetry.metrics import get_meter_provider, set_meter_provider
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from config import settings

def init_telemetry():
    """初始化OpenTelemetry"""

    # 资源配置
    resource = Resource(attributes={
        SERVICE_NAME: settings.otel_service_name,
        SERVICE_VERSION: "1.0.0",
        "deployment.environment": "production",
        "service.team": "ai-platform"
    })

    # 配置Tracer
    tracer_provider = TracerProvider(resource=resource)
    otlp_exporter = OTLPSpanExporter(endpoint=settings.otel_endpoint)
    span_processor = BatchSpanProcessor(otlp_exporter)
    tracer_provider.add_span_processor(span_processor)
    trace.set_tracer_provider(tracer_provider)

    # 配置Meter
    metric_reader = PeriodicExportingMetricReader(otlp_exporter)
    meter_provider = MeterProvider(resource=resource, metric_readers=[metric_reader])
    set_meter_provider(meter_provider)

    return trace.get_tracer("customer-service-ai"), get_meter_provider().get_meter("customer-service-ai")

tracer, meter = init_telemetry()

# 创建指标
token_counter = meter.create_counter(
    "gen_ai.tokens.used",
    description="Total tokens used",
    unit="1"
)

latency_histogram = meter.create_histogram(
    "gen_ai.latency",
    description="Request latency",
    unit="ms"
)

cost_counter = meter.create_counter(
    "gen_ai.cost.usd",
    description="Estimated cost in USD",
    unit="USD"
)
```

---

## 2. 核心服务实现

### 2.1 LLM客户端（带仪器化）

```python
# llm_client.py
import time
import json
from typing import List, Dict, Any
from openai import OpenAI
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode
from config import settings
from telemetry import tracer, token_counter, latency_histogram, cost_counter

# 模型定价 (per 1M tokens)
MODEL_PRICING = {
    "gpt-4o": {"input": 2.50, "output": 10.00},
    "gpt-4o-mini": {"input": 0.15, "output": 0.60},
}

class InstrumentedLLMClient:
    """带完整OpenTelemetry仪器化的LLM客户端"""

    def __init__(self):
        self.client = OpenAI(api_key=settings.openai_api_key)
        self.model = settings.openai_model

    def _calculate_cost(self, input_tokens: int, output_tokens: int) -> float:
        """计算API调用成本"""
        pricing = MODEL_PRICING.get(self.model, MODEL_PRICING["gpt-4o"])
        input_cost = (input_tokens / 1_000_000) * pricing["input"]
        output_cost = (output_tokens / 1_000_000) * pricing["output"]
        return input_cost + output_cost

    def chat_completion(
        self,
        messages: List[Dict[str, str]],
        session_id: str = None,
        user_id: str = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        执行带完整仪器化的Chat Completion

        Args:
            messages: 对话消息列表
            session_id: 会话ID（用于追踪）
            user_id: 用户ID
            **kwargs: 其他OpenAI参数
        """

        with tracer.start_as_current_span("gen_ai.chat") as span:
            # 设置必需属性
            span.set_attribute("gen_ai.system", "openai")
            span.set_attribute("gen_ai.operation.name", "chat")
            span.set_attribute("gen_ai.request.model", self.model)

            # 设置业务属性
            if session_id:
                span.set_attribute("session.id", session_id)
            if user_id:
                span.set_attribute("user.id", user_id)

            # 设置请求参数
            span.set_attribute("gen_ai.request.temperature",
                             kwargs.get("temperature", settings.temperature))
            span.set_attribute("gen_ai.request.max_tokens",
                             kwargs.get("max_tokens", settings.max_tokens_per_request))

            # 记录输入统计
            span.set_attribute("gen_ai.request.message_count", len(messages))

            start_time = time.time()

            try:
                # 调用API
                response = self.client.chat.completions.create(
                    model=self.model,
                    messages=messages,
                    **kwargs
                )

                # 计算延迟
                latency_ms = (time.time() - start_time) * 1000

                # 设置响应属性
                span.set_attribute("gen_ai.response.model", response.model)
                span.set_attribute("gen_ai.response.id", response.id)
                span.set_attribute("gen_ai.response.finish_reason",
                                 response.choices[0].finish_reason)

                # 设置Token使用
                input_tokens = response.usage.prompt_tokens
                output_tokens = response.usage.completion_tokens
                total_tokens = response.usage.total_tokens

                span.set_attribute("gen_ai.usage.input_tokens", input_tokens)
                span.set_attribute("gen_ai.usage.output_tokens", output_tokens)
                span.set_attribute("gen_ai.usage.total_tokens", total_tokens)

                # 计算并记录成本
                cost = self._calculate_cost(input_tokens, output_tokens)
                span.set_attribute("gen_ai.estimated_cost_usd", round(cost, 6))

                # 记录指标
                token_counter.add(total_tokens, {
                    "model": self.model,
                    "operation": "chat"
                })
                latency_histogram.record(latency_ms, {
                    "model": self.model
                })
                cost_counter.add(cost, {
                    "model": self.model
                })

                # 检查是否截断
                if response.choices[0].finish_reason == "length":
                    span.set_attribute("gen_ai.warning", "response_truncated")

                return {
                    "content": response.choices[0].message.content,
                    "model": response.model,
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
                raise
```

### 2.2 意图识别服务

```python
# intent_service.py
from typing import Dict
from telemetry import tracer

class IntentService:
    """用户意图识别服务"""

    def __init__(self, llm_client):
        self.llm_client = llm_client

    def recognize_intent(self, user_message: str, session_id: str = None) -> Dict:
        """识别用户意图"""

        with tracer.start_as_current_span("intent.recognition") as span:
            span.set_attribute("intent.input_length", len(user_message))

            messages = [
                {
                    "role": "system",
                    "content": """你是意图识别专家。分析用户消息，识别其意图。
可选意图：查询订单、退换货、产品咨询、投诉建议、其他。
以JSON格式返回：{"intent": "意图名称", "confidence": 0-1}"""
                },
                {"role": "user", "content": user_message}
            ]

            try:
                result = self.llm_client.chat_completion(
                    messages=messages,
                    session_id=session_id,
                    temperature=0.3,  # 低温度以获得更确定的结果
                    max_tokens=100
                )

                import json
                intent_data = json.loads(result["content"])

                span.set_attribute("intent.detected", intent_data.get("intent"))
                span.set_attribute("intent.confidence", intent_data.get("confidence"))

                return intent_data

            except Exception as e:
                span.set_attribute("intent.error", str(e))
                return {"intent": "unknown", "confidence": 0.0}
```

### 2.3 RAG检索服务

```python
# rag_service.py
from typing import List, Dict
from telemetry import tracer

class RAGService:
    """RAG检索服务（模拟实现）"""

    def __init__(self, llm_client):
        self.llm_client = llm_client
        self.knowledge_base = self._load_knowledge_base()

    def _load_knowledge_base(self):
        """加载知识库"""
        return [
            {"id": "kb_001", "content": "退货政策：7天无理由退货", "category": "退换货"},
            {"id": "kb_002", "content": "运费说明：满99元包邮", "category": "配送"},
            # ...
        ]

    def retrieve(self, query: str, top_k: int = 3) -> List[Dict]:
        """检索相关知识"""

        with tracer.start_as_current_span("rag.retrieval") as span:
            span.set_attribute("rag.query", query[:100])  # 截断长查询
            span.set_attribute("rag.top_k", top_k)

            # 模拟向量检索（实际应使用向量数据库）
            results = []
            for doc in self.knowledge_base:
                # 简单匹配评分
                score = self._calculate_relevance(query, doc["content"])
                if score > 0.5:
                    results.append({**doc, "score": score})

            # 按相关度排序
            results.sort(key=lambda x: x["score"], reverse=True)
            top_results = results[:top_k]

            span.set_attribute("rag.results_count", len(top_results))
            span.set_attribute("rag.result_ids", [r["id"] for r in top_results])

            return top_results

    def _calculate_relevance(self, query: str, content: str) -> float:
        """计算查询与内容的相关度（简化实现）"""
        query_words = set(query.lower().split())
        content_words = set(content.lower().split())
        overlap = query_words & content_words
        return len(overlap) / max(len(query_words), 1)
```

### 2.4 客服对话服务

```python
# customer_service.py
from typing import Dict
from telemetry import tracer

class CustomerService:
    """智能客服服务"""

    def __init__(self, llm_client, intent_service, rag_service):
        self.llm_client = llm_client
        self.intent_service = intent_service
        self.rag_service = rag_service

    def handle_message(
        self,
        user_message: str,
        session_id: str,
        user_id: str = None,
        conversation_history: list = None
    ) -> Dict:
        """处理用户消息"""

        with tracer.start_as_current_span("customer_service.handle_message") as parent_span:
            parent_span.set_attribute("session.id", session_id)
            parent_span.set_attribute("message.length", len(user_message))

            # 1. 意图识别
            intent_result = self.intent_service.recognize_intent(
                user_message, session_id
            )
            intent = intent_result.get("intent", "unknown")

            parent_span.set_attribute("detected_intent", intent)

            # 2. RAG检索（如果是产品咨询）
            context = ""
            if intent in ["产品咨询", "查询订单"]:
                retrieved_docs = self.rag_service.retrieve(user_message)
                if retrieved_docs:
                    context = "\n".join([
                        f"[{doc['id']}] {doc['content']}"
                        for doc in retrieved_docs
                    ])
                    parent_span.set_attribute("rag.context_used", True)
                    parent_span.set_attribute("rag.context_length", len(context))

            # 3. 构建系统提示词
            system_prompt = self._build_system_prompt(intent, context)

            # 4. 构建消息
            messages = [{"role": "system", "content": system_prompt}]

            if conversation_history:
                messages.extend(conversation_history[-5:])  # 最近5轮

            messages.append({"role": "user", "content": user_message})

            # 5. 调用LLM生成回复
            try:
                result = self.llm_client.chat_completion(
                    messages=messages,
                    session_id=session_id,
                    user_id=user_id
                )

                parent_span.set_attribute("response.success", True)
                parent_span.set_attribute("response.tokens", result["usage"]["total_tokens"])
                parent_span.set_attribute("response.cost_usd", result["cost_usd"])

                return {
                    "response": result["content"],
                    "intent": intent,
                    "usage": result["usage"],
                    "cost_usd": result["cost_usd"],
                    "latency_ms": result["latency_ms"]
                }

            except Exception as e:
                parent_span.set_attribute("response.success", False)
                parent_span.set_attribute("error.message", str(e))

                # 返回友好错误
                return {
                    "response": "抱歉，我暂时无法处理您的请求，请稍后再试。",
                    "intent": intent,
                    "error": str(e)
                }

    def _build_system_prompt(self, intent: str, context: str) -> str:
        """构建系统提示词"""
        base_prompt = f"""你是专业的智能客服助手。请基于以下信息回答用户问题：

用户意图：{intent}

"""
        if context:
            base_prompt += f"相关知识：\n{context}\n\n"

        base_prompt += """要求：
1. 回答要简洁专业
2. 如果不确定，建议转人工
3. 保持礼貌和耐心"""

        return base_prompt
```

---

## 3. 监控与告警

### 3.1 成本监控

```python
# cost_monitor.py
from opentelemetry import metrics
from telemetry import meter
import threading
import time

class CostMonitor:
    """成本监控器"""

    def __init__(self, daily_limit_usd: float):
        self.daily_limit = daily_limit_usd
        self.daily_cost = 0.0
        self.lock = threading.Lock()

        # 创建成本相关指标
        self.daily_cost_gauge = meter.create_observable_gauge(
            "gen_ai.daily_cost_usd",
            description="Daily accumulated cost",
            unit="USD",
            callbacks=[self._get_daily_cost]
        )

        self.budget_ratio_gauge = meter.create_observable_gauge(
            "gen_ai.budget_usage_ratio",
            description="Daily budget usage ratio",
            unit="1",
            callbacks=[self._get_budget_ratio]
        )

        # 启动重置定时器
        self._schedule_daily_reset()

    def _get_daily_cost(self, options):
        with self.lock:
            return [metrics.Observation(self.daily_cost, {})]

    def _get_budget_ratio(self, options):
        with self.lock:
            ratio = self.daily_cost / self.daily_limit if self.daily_limit > 0 else 0
            return [metrics.Observation(ratio, {})]

    def add_cost(self, cost_usd: float):
        """添加成本"""
        with self.lock:
            self.daily_cost += cost_usd

            # 检查是否接近预算限制
            if self.daily_cost > self.daily_limit * 0.8:
                print(f"⚠️ 警告：日成本达到预算的 {(self.daily_cost/self.daily_limit)*100:.1f}%")

            if self.daily_cost > self.daily_limit:
                print(f"🚨 告警：日成本超出预算！当前: ${self.daily_cost:.2f}, 限制: ${self.daily_limit:.2f}")

    def _schedule_daily_reset(self):
        """每天重置成本计数器"""
        def reset():
            while True:
                time.sleep(86400)  # 24小时
                with self.lock:
                    print(f"📊 日成本统计: ${self.daily_cost:.2f}")
                    self.daily_cost = 0.0

        thread = threading.Thread(target=reset, daemon=True)
        thread.start()

# 全局成本监控器
cost_monitor = CostMonitor(daily_limit_usd=100.0)
```

### 3.2 延迟监控

```python
# latency_monitor.py
from telemetry import latency_histogram
import functools
import time

def track_latency(operation_name: str):
    """延迟追踪装饰器"""
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            start = time.time()
            try:
                return func(*args, **kwargs)
            finally:
                latency_ms = (time.time() - start) * 1000
                latency_histogram.record(latency_ms, {
                    "operation": operation_name
                })
        return wrapper
    return decorator

# 使用示例
class MyService:
    @track_latency("my_operation")
    def do_something(self):
        # 业务逻辑
        pass
```

---

## 4. 完整示例运行

### 4.1 主程序

```python
# main.py
import json
from llm_client import InstrumentedLLMClient
from intent_service import IntentService
from rag_service import RAGService
from customer_service import CustomerService

def main():
    # 初始化服务
    llm_client = InstrumentedLLMClient()
    intent_service = IntentService(llm_client)
    rag_service = RAGService(llm_client)
    customer_service = CustomerService(llm_client, intent_service, rag_service)

    # 模拟对话
    session_id = "session_001"
    user_id = "user_12345"

    conversations = [
        "你好，我想了解一下退货政策",
        "订单怎么还没发货？",
        "这款产品有什么特色功能？"
    ]

    conversation_history = []

    for message in conversations:
        print(f"\n👤 用户: {message}")

        result = customer_service.handle_message(
            user_message=message,
            session_id=session_id,
            user_id=user_id,
            conversation_history=conversation_history
        )

        print(f"🤖 助手: {result['response'][:100]}...")
        print(f"📊 意图: {result['intent']}")

        if 'usage' in result:
            print(f"💰 成本: ${result['cost_usd']:.6f} | "
                  f"Token: {result['usage']['total_tokens']} | "
                  f"延迟: {result['latency_ms']:.0f}ms")

        # 更新对话历史
        conversation_history.append({"role": "user", "content": message})
        conversation_history.append({"role": "assistant", "content": result['response']})

if __name__ == "__main__":
    main()
```

### 4.2 运行输出示例

```
👤 用户: 你好，我想了解一下退货政策
🤖 助手: 您好！我们的退货政策是7天无理由退货。只要商品未使用、包装完整，您可以在收...
📊 意图: 退换货
💰 成本: $0.000125 | Token: 245 | 延迟: 850ms

👤 用户: 订单怎么还没发货？
🤖 助手: 我理解您的着急。让我帮您查询一下订单状态。请提供您的订单号，我可以...
📊 意图: 查询订单
💰 成本: $0.000089 | Token: 180 | 延迟: 620ms

👤 用户: 这款产品有什么特色功能？
🤖 助手: 根据产品资料，这款产品的主要特色包括：1. 超长续航 2. 智能降噪 3...
📊 意图: 产品咨询
💰 成本: $0.000156 | Token: 310 | 延迟: 920ms
```

---

## 5. 仪表板配置

### 5.1 Grafana仪表板JSON（示例）

```json
{
  "dashboard": {
    "title": "LLM Application Monitoring",
    "panels": [
      {
        "title": "Token Usage Rate",
        "targets": [{
          "expr": "rate(gen_ai_tokens_used_total[5m])",
          "legendFormat": "{{model}} - {{operation}}"
        }]
      },
      {
        "title": "Request Latency (p99)",
        "targets": [{
          "expr": "histogram_quantile(0.99, rate(gen_ai_latency_bucket[5m]))",
          "legendFormat": "p99 latency"
        }]
      },
      {
        "title": "Daily Cost",
        "targets": [{
          "expr": "gen_ai_daily_cost_usd",
          "legendFormat": "Daily Cost USD"
        }]
      },
      {
        "title": "Budget Usage %",
        "targets": [{
          "expr": "gen_ai_budget_usage_ratio * 100",
          "legendFormat": "Budget Used %"
        }],
        "alert": {
          "conditions": [{
            "evaluator": {"type": "gt", "params": [80]},
            "operator": {"type": "and"},
            "query": {"params": ["A", "5m", "now"]},
            "reducer": {"type": "avg"}
          }]
        }
      }
    ]
  }
}
```

---

## 6. 最佳实践总结

### 6.1 生产环境检查清单

- [ ] 禁用内容记录 (`GENAI_LOG_CONTENT=false`)
- [ ] 配置合理的采样率
- [ ] 设置成本告警阈值
- [ ] 实现错误降级策略
- [ ] 配置链路追踪传播
- [ ] 监控延迟百分位数
- [ ] 记录业务上下文（user_id, session_id）

### 6.2 性能优化建议

1. **批处理**: 批量处理embedding请求
2. **缓存**: 缓存常用查询结果
3. **采样**: 高流量场景降低采样率
4. **异步**: 异步发送telemetry数据

### 6.3 安全建议

1. **脱敏**: 不要记录完整的prompt/completion
2. **权限**: 限制API key访问范围
3. **审计**: 记录所有API调用
4. **限流**: 实现API调用限流

---

**完成本指南后，您已掌握**：

- ✅ 完整的LLM应用OpenTelemetry仪器化
- ✅ Token、成本、延迟监控
- ✅ 生产级错误处理
- ✅ 可观测性仪表板构建

---

**下一步**: [OpenAI集成指南](./03_OpenAI集成指南.md)
