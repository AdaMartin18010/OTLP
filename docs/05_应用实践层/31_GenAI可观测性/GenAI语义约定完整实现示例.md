---
title: GenAI语义约定完整实现示例
description: GenAI语义约定完整实现示例 详细指南和最佳实践
version: OTLP v1.9.0
date: 2026-03-17
author: OTLP项目团队
category: 前沿技术
tags:
  - otlp
  - observability
  - genai
  - llm
  - ai
  - deployment
  - kubernetes
  - docker
status: published
---
# GenAI语义约定完整实现示例

> **规范版本**: Semantic Conventions v1.40.0
> **稳定性**: Development (LLM), Draft (Agent)
> **文档状态**: ✅ 已对齐

---

## 完整Python实现

### 1. 基础设置

`python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource
import openai
import time
import json

# 初始化Tracer

resource = Resource.create({
    "service.name": "genai-service",
    "service.version": "1.0.0",
})

tracer_provider = TracerProvider(resource=resource)
otlp_exporter = OTLPSpanExporter(endpoint="localhost:4317", insecure=True)
tracer_provider.add_span_processor(BatchSpanProcessor(otlp_exporter))
trace.set_tracer_provider(tracer_provider)

tracer = trace.get_tracer("genai.instrumentation")
`

### 2. LLM调用完整示例

`python
def chat_completion_with_full_telemetry(
    messages: list,
    model: str = "gpt-4",
    temperature: float = 0.7,
    max_tokens: int = 2048
) -> dict:
    """
    带完整可观测性的Chat Completion调用
    符合Semantic Conventions v1.40.0
    """

    with tracer.start_as_current_span("gen_ai.chat") as span:
        # ===== 请求属性 =====
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "chat")
        span.set_attribute("gen_ai.request.model", model)
        span.set_attribute("gen_ai.request.temperature", temperature)
        span.set_attribute("gen_ai.request.max_tokens", max_tokens)
        span.set_attribute("gen_ai.request.top_p", 1.0)
        span.set_attribute("gen_ai.request.frequency_penalty", 0.0)
        span.set_attribute("gen_ai.request.presence_penalty", 0.0)
        span.set_attribute("gen_ai.request.stop_sequences", ["\n\n", "END"])

        # 记录消息数量（不包含完整内容，避免敏感数据）
        span.set_attribute("gen_ai.usage.input_messages", len(messages))

        # 记录消息角色分布
        role_counts = {}
        for msg in messages:
            role = msg.get("role", "unknown")
            role_counts[role] = role_counts.get(role, 0) + 1
        span.set_attribute("gen_ai.request.message.roles", json.dumps(role_counts))

        start_time = time.time()

        try:
            # ===== 执行调用 =====
            client = openai.OpenAI()
            response = client.chat.completions.create(
                model=model,
                messages=messages,
                temperature=temperature,
                max_tokens=max_tokens
            )

            # ===== 响应属性 =====
            span.set_attribute("gen_ai.response.model", response.model)
            span.set_attribute("gen_ai.response.id", response.id)
            span.set_attribute("gen_ai.response.finish_reason",
                             response.choices[0].finish_reason)

            # ===== Token使用 =====
            if response.usage:
                span.set_attribute("gen_ai.usage.input_tokens",
                                 response.usage.prompt_tokens)
                span.set_attribute("gen_ai.usage.output_tokens",
                                 response.usage.completion_tokens)
                span.set_attribute("gen_ai.usage.total_tokens",
                                 response.usage.total_tokens)

            # ===== 成本追踪 (v1.40新增) =====
            if "gpt-4" in model:
                input_cost = response.usage.prompt_tokens * 0.03 / 1000
                output_cost = response.usage.completion_tokens * 0.06 / 1000
                total_cost = input_cost + output_cost
                span.set_attribute("gen_ai.cost.currency", "USD")
                span.set_attribute("gen_ai.cost.amount", round(total_cost, 6))

            # ===== 延迟 =====
            latency_ms = (time.time() - start_time) * 1000
            span.set_attribute("gen_ai.latency_ms", latency_ms)

            return {
                "content": response.choices[0].message.content,
                "model": response.model,
                "usage": response.usage,
                "latency_ms": latency_ms
            }

        except Exception as e:
            span.set_attribute("error.type", type(e).__name__)
            span.set_attribute("error.message", str(e))
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
`

### 3. Streaming调用示例

`python
def chat_completion_streaming(
    messages: list,
    model: str = "gpt-4"
) -> str:
    """Streaming模式的可观测性实现"""

    with tracer.start_as_current_span("gen_ai.chat") as span:
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "chat")
        span.set_attribute("gen_ai.request.model", model)
        span.set_attribute("gen_ai.request.streaming", True)

        start_time = time.time()
        first_token_time = None
        full_content = []

        try:
            client = openai.OpenAI()
            stream = client.chat.completions.create(
                model=model,
                messages=messages,
                stream=True
            )

            for chunk in stream:
                if first_token_time is None:
                    first_token_time = time.time()
                    ttft_ms = (first_token_time - start_time) * 1000
                    span.set_attribute("gen_ai.response.time_to_first_token_ms", ttft_ms)

                if chunk.choices[0].delta.content:
                    full_content.append(chunk.choices[0].delta.content)
                    yield chunk.choices[0].delta.content

            # 记录完整响应统计
            final_content = "".join(full_content)
            span.set_attribute("gen_ai.usage.output_tokens",
                             len(final_content.split()))  # 近似值

            total_latency_ms = (time.time() - start_time) * 1000
            span.set_attribute("gen_ai.latency_ms", total_latency_ms)

        except Exception as e:
            span.set_attribute("error.type", type(e).__name__)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
`

### 4. Embedding调用示例

`python
def create_embedding_with_telemetry(
    texts: list[str],
    model: str = "text-embedding-3-small"
) -> list:
    """Embedding生成的可观测性实现"""

    with tracer.start_as_current_span("gen_ai.embeddings") as span:
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "embeddings")
        span.set_attribute("gen_ai.request.model", model)
        span.set_attribute("gen_ai.request.embedding.dimensions",
                         1536 if "small" in model else 3072)

        # 批处理信息
        span.set_attribute("gen_ai.request.batch_size", len(texts))

        start_time = time.time()

        try:
            client = openai.OpenAI()
            response = client.embeddings.create(
                model=model,
                input=texts
            )

            span.set_attribute("gen_ai.usage.input_tokens",
                             response.usage.prompt_tokens)
            span.set_attribute("gen_ai.usage.total_tokens",
                             response.usage.total_tokens)
            span.set_attribute("gen_ai.response.embedding.dimensions",
                             len(response.data[0].embedding))

            latency_ms = (time.time() - start_time) * 1000
            span.set_attribute("gen_ai.latency_ms", latency_ms)

            return [item.embedding for item in response.data]

        except Exception as e:
            span.set_attribute("error.type", type(e).__name__)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
`

---

## Agent语义约定实现 (v1.40 Draft)

### 1. Agent创建与调用

`python
import uuid

class TracedAIAgent:
    """带完整可观测性的AI Agent实现"""

    def __init__(self, agent_id: str, name: str, system: str = "custom"):
        self.agent_id = agent_id
        self.name = name
        self.system = system
        self.version = "1.0.0"
        self.tools = {}

        # 记录Agent创建
        with tracer.start_as_current_span("gen_ai.agent.create") as span:
            span.set_attribute("gen_ai.agent.id", agent_id)
            span.set_attribute("gen_ai.agent.name", name)
            span.set_attribute("gen_ai.agent.version", self.version)
            span.set_attribute("gen_ai.agent.system", system)

    def register_tool(self, name: str, func: callable):
        """注册工具"""
        self.tools[name] = func

    def invoke(self, user_input: str, invocation_type: str = "synchronous"):
        """
        Agent调用 - 完整追踪
        """
        invocation_id = str(uuid.uuid4())

        with tracer.start_as_current_span("gen_ai.agent.invoke") as parent_span:
            # Agent标识
            parent_span.set_attribute("gen_ai.agent.id", self.agent_id)
            parent_span.set_attribute("gen_ai.agent.invocation.id", invocation_id)
            parent_span.set_attribute("gen_ai.agent.invocation.type", invocation_type)

            # 记录用户输入摘要
            parent_span.set_attribute("gen_ai.agent.input_length", len(user_input))

            try:
                # 1. 规划步骤
                plan = self._create_plan(user_input, parent_span)

                # 2. 执行工具调用
                tool_results = []
                for step in plan:
                    if step.get("tool"):
                        result = self._execute_tool(
                            step["tool"],
                            step.get("input", {}),
                            parent_span
                        )
                        tool_results.append(result)

                # 3. 生成响应
                response = self._generate_response(
                    user_input,
                    tool_results,
                    parent_span
                )

                return response

            except Exception as e:
                parent_span.set_attribute("error.type", type(e).__name__)
                parent_span.set_attribute("error.message", str(e))
                parent_span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
                raise

    def _create_plan(self, user_input: str, parent_span):
        """创建执行计划"""
        with tracer.start_as_current_span("gen_ai.agent.plan", parent_span) as span:
            span.set_attribute("gen_ai.agent.id", self.agent_id)

            # 模拟规划
            plan = [
                {"step": 1, "action": "analyze", "tool": None},
                {"step": 2, "action": "search", "tool": "search_database",
                 "input": {"query": user_input}},
                {"step": 3, "action": "generate", "tool": None}
            ]

            span.set_attribute("gen_ai.agent.plan.steps", len(plan))
            return plan

    def _execute_tool(self, tool_name: str, tool_input: dict, parent_span):
        """执行工具调用"""
        with tracer.start_as_current_span("gen_ai.agent.tool", parent_span) as span:
            span.set_attribute("gen_ai.agent.id", self.agent_id)
            span.set_attribute("gen_ai.agent.tool.name", tool_name)
            span.set_attribute("gen_ai.agent.tool.input", json.dumps(tool_input))

            start_time = time.time()

            if tool_name in self.tools:
                result = self.tools[tool_name](**tool_input)
                span.set_attribute("gen_ai.agent.tool.output", json.dumps(result)[:1000])
            else:
                result = {"error": f"Tool {tool_name} not found"}
                span.set_attribute("error.type", "ToolNotFound")

            latency_ms = (time.time() - start_time) * 1000
            span.set_attribute("gen_ai.agent.tool.latency_ms", latency_ms)

            return result

    def _generate_response(self, user_input: str, context: list, parent_span):
        """生成Agent响应"""
        with tracer.start_as_current_span("gen_ai.agent.generate", parent_span) as span:
            span.set_attribute("gen_ai.agent.id", self.agent_id)
            span.set_attribute("gen_ai.system", self.system)
            span.set_attribute("gen_ai.operation.name", "generate")

            # 这里调用底层LLM
            # ... LLM调用代码 ...

            span.set_attribute("gen_ai.usage.output_tokens", 150)  # 示例
            return {"response": "Agent response", "context": context}
`

### 2. 多Agent协作示例

`python
class MultiAgentSystem:
    """多Agent系统可观测性实现"""

    def __init__(self):
        self.agents = {}

    def register_agent(self, agent: TracedAIAgent):
        self.agents[agent.agent_id] = agent

    def orchestrate(self, task: str, agent_ids: list):
        """
        多Agent协作编排
        """
        with tracer.start_as_current_span("gen_ai.agent.orchestrate") as span:
            span.set_attribute("gen_ai.agent.orchestration.task", task[:100])
            span.set_attribute("gen_ai.agent.orchestration.agents",
                             json.dumps(agent_ids))

            results = []
            for i, agent_id in enumerate(agent_ids):
                if agent_id in self.agents:
                    with tracer.start_as_current_span(
                        f"gen_ai.agent.orchestration.step.{i}"
                    ) as step_span:
                        step_span.set_attribute("gen_ai.agent.id", agent_id)
                        step_span.set_attribute("gen_ai.agent.orchestration.step", i)

                        result = self.agents[agent_id].invoke(task)
                        results.append(result)

            span.set_attribute("gen_ai.agent.orchestration.steps_completed",
                             len(results))
            return results
`

---

## 事件记录 (Events)

`python
def record_genai_events(span, messages, response):
    """记录GenAI事件"""

    # 记录提示词事件
    for i, msg in enumerate(messages):
        span.add_event(
            "gen_ai.content.prompt",
            {
                "gen_ai.system": "openai",
                "gen_ai.prompt.role": msg.get("role", "unknown"),
                "gen_ai.prompt.content": msg.get("content", "")[:1000]
            }
        )

    # 记录完成事件
    span.add_event(
        "gen_ai.content.completion",
        {
            "gen_ai.system": "openai",
            "gen_ai.completion.role": "assistant",
            "gen_ai.completion.content": response[:1000],
            "gen_ai.completion.finish_reason": "stop"
        }
    )
`

---

## 配置与部署

### Docker Compose示例

`yaml
version: '3'
services:
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.147.0
    volumes:
      - ./otel-config.yaml:/etc/otelcol-contrib/config.yaml
    ports:
      - "4317:4317"  # OTLP gRPC
      - "4318:4318"  # OTLP HTTP

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
`

### Collector配置

`yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
`

---

## 参考资源

- [GenAI Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)
- [OpenTelemetry Python SDK](https://opentelemetry.io/docs/languages/python/)
- [OpenAI API文档](https://platform.openai.com/docs/)

---

**文档版本**: v1.0
**更新日期**: 2026年3月16日
**规范版本**: Semantic Conventions v1.40.0
**维护者**: OTLP项目团队
