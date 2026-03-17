---
title: GenAI语义约定完整指南
description: GenAI语义约定完整指南 详细指南和最佳实践
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 前沿技术
tags:
  - otlp
  - observability
  - performance
  - optimization
  - sampling
  - genai
  - llm
  - ai
status: published
---
# GenAI语义约定完整指南

> **文档版本**: v1.0 (基于OpenTelemetry Semantic Conventions v1.41.0+)
> **稳定性**: Development (发展中)
> **适用范围**: LLM应用、AI Agent、RAG系统
> **创建日期**: 2026年3月15日

---

## 目录

- [GenAI语义约定完整指南](#genai语义约定完整指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是GenAI语义约定](#11-什么是genai语义约定)
    - [1.2 为什么需要GenAI语义约定](#12-为什么需要genai语义约定)
    - [1.3 支持的操作类型](#13-支持的操作类型)
  - [2. 核心概念](#2-核心概念)
    - [2.1 GenAI Span模型](#21-genai-span模型)
    - [2.2 命名空间结构](#22-命名空间结构)
  - [3. 语义约定详解](#3-语义约定详解)
    - [3.1 核心属性](#31-核心属性)
      - [gen\_ai.system](#gen_aisystem)
      - [gen\_ai.operation.name](#gen_aioperationname)
      - [gen\_ai.request.model](#gen_airequestmodel)
      - [gen\_ai.response.model](#gen_airesponsemodel)
      - [gen\_ai.usage.input\_tokens](#gen_aiusageinput_tokens)
      - [gen\_ai.usage.output\_tokens](#gen_aiusageoutput_tokens)
      - [gen\_ai.usage.total\_tokens](#gen_aiusagetotal_tokens)
      - [gen\_ai.response.finish\_reason](#gen_airesponsefinish_reason)
    - [3.2 请求参数属性](#32-请求参数属性)
      - [gen\_ai.request.temperature](#gen_airequesttemperature)
      - [gen\_ai.request.max\_tokens](#gen_airequestmax_tokens)
      - [gen\_ai.request.top\_p](#gen_airequesttop_p)
      - [gen\_ai.request.top\_k](#gen_airequesttop_k)
      - [gen\_ai.request.presence\_penalty](#gen_airequestpresence_penalty)
      - [gen\_ai.request.frequency\_penalty](#gen_airequestfrequency_penalty)
    - [3.3 消息内容属性](#33-消息内容属性)
      - [gen\_ai.system\_instructions](#gen_aisystem_instructions)
      - [gen\_ai.input.messages](#gen_aiinputmessages)
      - [gen\_ai.output.messages](#gen_aioutputmessages)
  - [4. 属性参考表](#4-属性参考表)
    - [4.1 完整属性列表](#41-完整属性列表)
    - [4.2 属性重要性分级](#42-属性重要性分级)
  - [5. 实现指南](#5-实现指南)
    - [5.1 Python实现](#51-python实现)
      - [基础配置](#基础配置)
      - [Chat Completions仪器化](#chat-completions仪器化)
      - [Embeddings仪器化](#embeddings仪器化)
      - [多模型统一接口](#多模型统一接口)
    - [5.2 环境变量配置](#52-环境变量配置)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 敏感数据处理](#61-敏感数据处理)
    - [6.2 成本监控](#62-成本监控)
    - [6.3 错误处理](#63-错误处理)
    - [6.4 批量请求处理](#64-批量请求处理)
  - [7. 常见问题](#7-常见问题)
    - [Q1: GenAI语义约定的稳定性如何？](#q1-genai语义约定的稳定性如何)
    - [Q2: 如何处理多模态输入（图像、音频）？](#q2-如何处理多模态输入图像音频)
    - [Q3: 是否支持流式响应？](#q3-是否支持流式响应)
    - [Q4: 如何处理函数调用/工具调用？](#q4-如何处理函数调用工具调用)
  - [8. 参考资源](#8-参考资源)
  - [6. Agent语义约定 (v1.40 Draft)](#6-agent语义约定-v140-draft)
    - [6.1 概述](#61-概述)
    - [6.2 Agent核心属性](#62-agent核心属性)
    - [6.3 Agent Span类型](#63-agent-span类型)
    - [6.4 Agent语义约定状态](#64-agent语义约定状态)
    - [6.5 参考资源](#65-参考资源)

---

## 1. 概述

### 1.1 什么是GenAI语义约定

GenAI语义约定是OpenTelemetry为生成式AI应用定义的标准化属性集合，用于统一LLM调用、嵌入生成、工具执行等操作的观测数据格式。

```
┌─────────────────────────────────────────────────────────────────┐
│                    GenAI可观测性全景图                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   用户请求 ──────► LLM应用 ──────► 模型API ──────► 观测数据     │
│       │              │              │              │            │
│       │              │              │              ▼            │
│       │              │              │     ┌─────────────────┐   │
│       │              │              │     │  gen_ai.system  │   │
│       │              │              │     │  gen_ai.request │   │
│       │              │              │     │  gen_ai.usage   │   │
│       │              │              │     └─────────────────┘   │
│       │              │              │              │            │
│       │              │              ▼              ▼            │
│       │              │     ┌─────────────────────────────┐      │
│       │              │     │     OpenTelemetry SDK      │      │
│       │              │     │  ┌───────────────────────┐  │      │
│       │              │     │  │  Traces (Spans)      │  │      │
│       │              │     │  │  - gen_ai.chat       │  │      │
│       │              │     │  │  - gen_ai.embeddings │  │      │
│       │              │     │  │  - execute_tool      │  │      │
│       │              │     │  └───────────────────────┘  │      │
│       │              │     └─────────────────────────────┘      │
│       │              │                       │                  │
│       │              ▼                       ▼                  │
│       │     ┌───────────────────────────────────────────┐       │
│       │     │         OpenTelemetry Collector            │       │
│       │     └───────────────────────────────────────────┘       │
│       │                       │                                  │
│       ▼                       ▼                                  │
│   ┌─────────────────────────────────────────────────────────┐   │
│   │              可观测性后端 (OneUptime/Grafana/etc)         │   │
│   │  • Token使用监控  • 成本分析  • 性能指标  • 错误追踪       │   │
│   └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 为什么需要GenAI语义约定

| 问题 | 解决方案 |
|:---|:---|
| **多模型统一监控** | 无论使用OpenAI、Anthropic还是自托管模型，观测数据格式一致 |
| **成本追踪** | 标准化token计数，支持跨模型成本对比 |
| **性能分析** | 统一的延迟、吞吐量指标 |
| **可移植性** | 更换模型提供商无需重新实现观测逻辑 |

### 1.3 支持的操作类型

```yaml
操作类型 (gen_ai.operation.name):
  chat:          # 对话补全 (OpenAI Chat Completions API)
  completions:   # 文本补全 (Legacy)
  embeddings:    # 嵌入向量生成
  execute_tool:  # 工具执行
  invoke_agent:  # Agent调用
  create_agent:  # Agent创建
  generate_content:  # 内容生成 (多模态)
```

---

## 2. 核心概念

### 2.1 GenAI Span模型

每个LLM调用都会产生一个span，包含以下信息：

```
Span: gen_ai.chat
├── 属性 (Attributes)
│   ├── gen_ai.system: openai
│   ├── gen_ai.request.model: gpt-4o
│   ├── gen_ai.usage.input_tokens: 150
│   ├── gen_ai.usage.output_tokens: 300
│   └── gen_ai.response.finish_reason: stop
├── 事件 (Events)
│   ├── gen_ai.content.prompt       # Prompt内容(可选)
│   └── gen_ai.content.completion   # Completion内容(可选)
└── 链接 (Links)
    └── 关联的trace context
```

### 2.2 命名空间结构

```
gen_ai.
├── system                    # AI系统标识
├── operation.
│   └── name                  # 操作类型
├── request.
│   ├── model                 # 请求的模型
│   ├── temperature           # 温度参数
│   ├── max_tokens           # 最大token数
│   ├── top_p                # Top P采样
│   ├── stop_sequences       # 停止序列
│   └── ...                  # 其他请求参数
├── response.
│   ├── model                # 实际使用的模型
│   ├── finish_reason        # 完成原因
│   ├── id                   # 响应ID
│   └── ...                  # 其他响应元数据
└── usage.
    ├── input_tokens         # 输入token数
    ├── output_tokens        # 输出token数
    └── total_tokens         # 总token数
```

---

## 3. 语义约定详解

### 3.1 核心属性

#### gen_ai.system

**描述**: 标识使用的AI系统/提供商

**取值范围**:

```yaml
gen_ai.system:
  - openai                    # OpenAI
  - anthropic                 # Anthropic
  - azure.ai.openai          # Azure OpenAI
  - aws.bedrock              # AWS Bedrock
  - google.vertex_ai         # Google Vertex AI
  - google.ai_studio         # Google AI Studio
  - cohere                   # Cohere
  - mistral_ai               # Mistral AI
  - meta.llama               # Meta Llama
  - x.ai                     # xAI (Grok)
  - deepseek                 # DeepSeek
```

**示例**:

```python
span.set_attribute("gen_ai.system", "openai")
span.set_attribute("gen_ai.system", "anthropic")
```

---

#### gen_ai.operation.name

**描述**: 操作类型标识

**取值**:

```yaml
chat:          # 聊天对话补全
completions:   # 文本补全 (legacy)
embeddings:    # 嵌入生成
text_completion:  # 文本补全
execute_tool:  # 执行工具
invoke_agent:  # 调用Agent
create_agent:  # 创建Agent
generate_content:  # 生成内容 (多模态)
```

**示例**:

```python
# OpenAI Chat Completions
span.set_attribute("gen_ai.operation.name", "chat")

# Embeddings
span.set_attribute("gen_ai.operation.name", "embeddings")

# Tool execution
span.set_attribute("gen_ai.operation.name", "execute_tool")
```

---

#### gen_ai.request.model

**描述**: 请求中指定的模型名称

**示例**:

```python
# OpenAI
span.set_attribute("gen_ai.request.model", "gpt-4o")
span.set_attribute("gen_ai.request.model", "gpt-4o-mini")
span.set_attribute("gen_ai.request.model", "o1-preview")

# Anthropic
span.set_attribute("gen_ai.request.model", "claude-3-5-sonnet-20241022")
span.set_attribute("gen_ai.request.model", "claude-3-opus-20240229")

# Azure OpenAI
span.set_attribute("gen_ai.request.model", "gpt-4o-2024-08-06")

# AWS Bedrock
span.set_attribute("gen_ai.request.model", "anthropic.claude-3-sonnet-20240229-v1:0")
```

---

#### gen_ai.response.model

**描述**: 实际响应中返回的模型名称（可能与请求不同）

**示例**:

```python
span.set_attribute("gen_ai.response.model", "gpt-4o-2024-08-06")
```

---

#### gen_ai.usage.input_tokens

**描述**: 输入（prompt）的token数量

**示例**:

```python
span.set_attribute("gen_ai.usage.input_tokens", 150)
```

**用途**:

- 成本计算
- 输入复杂度分析
- 配额监控

---

#### gen_ai.usage.output_tokens

**描述**: 输出（completion）的token数量

**示例**:

```python
span.set_attribute("gen_ai.usage.output_tokens", 300)
```

**用途**:

- 成本计算
- 响应长度分析
- 吞吐量指标

---

#### gen_ai.usage.total_tokens

**描述**: 总token数量（input + output）

**示例**:

```python
span.set_attribute("gen_ai.usage.total_tokens", 450)
```

---

#### gen_ai.response.finish_reason

**描述**: 模型停止生成的原因

**取值范围**:

```yaml
stop:          # 自然停止/遇到停止序列
length:        # 达到max_tokens限制
tool_calls:    # 需要调用工具
content_filter: # 内容被过滤
function_call: # (legacy) 需要调用函数
```

**示例**:

```python
span.set_attribute("gen_ai.response.finish_reason", "stop")
```

**重要性**: `length`表示响应可能被截断，需要特别关注。

---

### 3.2 请求参数属性

#### gen_ai.request.temperature

**描述**: 采样温度，控制随机性

**范围**: 0.0 - 2.0

**示例**:

```python
span.set_attribute("gen_ai.request.temperature", 0.7)
```

---

#### gen_ai.request.max_tokens

**描述**: 生成的最大token数

**示例**:

```python
span.set_attribute("gen_ai.request.max_tokens", 4096)
```

---

#### gen_ai.request.top_p

**描述**: 核采样参数

**范围**: 0.0 - 1.0

**示例**:

```python
span.set_attribute("gen_ai.request.top_p", 0.95)
```

---

#### gen_ai.request.top_k

**描述**: Top-K采样参数

**示例**:

```python
span.set_attribute("gen_ai.request.top_k", 40)
```

---

#### gen_ai.request.presence_penalty

**描述**: 存在惩罚，鼓励模型讨论新主题

**范围**: -2.0 - 2.0

**示例**:

```python
span.set_attribute("gen_ai.request.presence_penalty", 0.5)
```

---

#### gen_ai.request.frequency_penalty

**描述**: 频率惩罚，降低重复相同行的可能性

**范围**: -2.0 - 2.0

**示例**:

```python
span.set_attribute("gen_ai.request.frequency_penalty", 0.5)
```

---

### 3.3 消息内容属性

⚠️ **注意**: 消息内容属性可能包含敏感数据，应谨慎配置，生产环境中建议默认禁用。

#### gen_ai.system_instructions

**描述**: 系统指令/系统提示词

**示例**:

```python
# 仅记录系统指令的摘要或哈希
span.set_attribute("gen_ai.system_instructions_hash", "sha256:abc123...")
```

---

#### gen_ai.input.messages

**描述**: 输入消息数组（JSON格式）

**结构**:

```json
[
  {"role": "system", "content": "You are a helpful assistant."},
  {"role": "user", "content": "Hello!"},
  {"role": "assistant", "content": "Hi there!"},
  {"role": "user", "content": "What's the weather?"}
]
```

**示例**:

```python
import json
messages = [
    {"role": "user", "content": "Explain quantum computing"}
]
span.set_attribute("gen_ai.input.messages", json.dumps(messages))
```

---

#### gen_ai.output.messages

**描述**: 输出消息数组

**示例**:

```python
output_messages = [
    {"role": "assistant", "content": "Quantum computing is..."}
]
span.set_attribute("gen_ai.output.messages", json.dumps(output_messages))
```

---

## 4. 属性参考表

### 4.1 完整属性列表

| 属性 | 类型 | 是否必需 | 描述 | 示例 |
|:---|:---:|:---:|:---|:---|
| `gen_ai.system` | string | ✅ 是 | AI系统标识 | `openai`, `anthropic` |
| `gen_ai.operation.name` | string | ✅ 是 | 操作类型 | `chat`, `embeddings` |
| `gen_ai.request.model` | string | ✅ 是 | 请求模型 | `gpt-4o` |
| `gen_ai.response.model` | string | ⚠️ 推荐 | 响应模型 | `gpt-4o-2024-08-06` |
| `gen_ai.usage.input_tokens` | int | ✅ 是 | 输入token数 | `150` |
| `gen_ai.usage.output_tokens` | int | ✅ 是 | 输出token数 | `300` |
| `gen_ai.usage.total_tokens` | int | ⚠️ 推荐 | 总token数 | `450` |
| `gen_ai.response.finish_reason` | string | ⚠️ 推荐 | 完成原因 | `stop`, `length` |
| `gen_ai.request.temperature` | float | ❌ 否 | 温度参数 | `0.7` |
| `gen_ai.request.max_tokens` | int | ❌ 否 | 最大token数 | `4096` |
| `gen_ai.request.top_p` | float | ❌ 否 | Top P | `0.95` |
| `gen_ai.request.top_k` | int | ❌ 否 | Top K | `40` |
| `gen_ai.request.presence_penalty` | float | ❌ 否 | 存在惩罚 | `0.5` |
| `gen_ai.request.frequency_penalty` | float | ❌ 否 | 频率惩罚 | `0.5` |
| `gen_ai.request.stop_sequences` | string[] | ❌ 否 | 停止序列 | `["END"]` |
| `gen_ai.response.id` | string | ⚠️ 推荐 | 响应ID | `chatcmpl-abc123` |
| `gen_ai.response.headers` | map | ❌ 否 | 响应头 | 限流信息 |

### 4.2 属性重要性分级

```
必需 (Must have):
  ├── gen_ai.system
  ├── gen_ai.operation.name
  ├── gen_ai.request.model
  ├── gen_ai.usage.input_tokens
  └── gen_ai.usage.output_tokens

推荐 (Should have):
  ├── gen_ai.response.model
  ├── gen_ai.usage.total_tokens
  ├── gen_ai.response.finish_reason
  └── gen_ai.response.id

可选 (Nice to have):
  ├── 所有请求参数 (temperature, max_tokens等)
  └── 消息内容 (需考虑隐私)
```

---

## 5. 实现指南

### 5.1 Python实现

#### 基础配置

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource, SERVICE_NAME
import openai
import json

# 配置OpenTelemetry
resource = Resource(attributes={
    SERVICE_NAME: "llm-chat-service"
})
provider = TracerProvider(resource=resource)
processor = BatchSpanProcessor(OTLPSpanExporter())
provider.add_span_processor(processor)
trace.set_tracer_provider(provider)

tracer = trace.get_tracer("genai.instrumentation")
```

#### Chat Completions仪器化

```python
import time

def chat_with_telemetry(user_message: str, model: str = "gpt-4o") -> str:
    """带OpenTelemetry仪器化的Chat Completion"""

    with tracer.start_as_current_span("gen_ai.chat") as span:
        # 设置必需属性
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "chat")
        span.set_attribute("gen_ai.request.model", model)

        # 设置可选请求参数
        span.set_attribute("gen_ai.request.temperature", 0.7)
        span.set_attribute("gen_ai.request.max_tokens", 4096)

        start_time = time.time()

        try:
            # 调用OpenAI API
            client = openai.OpenAI()
            response = client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": user_message}],
                temperature=0.7,
                max_tokens=4096
            )

            # 记录响应属性
            span.set_attribute("gen_ai.response.model", response.model)
            span.set_attribute("gen_ai.response.id", response.id)
            span.set_attribute("gen_ai.response.finish_reason",
                             response.choices[0].finish_reason)

            # 记录Token使用
            span.set_attribute("gen_ai.usage.input_tokens",
                             response.usage.prompt_tokens)
            span.set_attribute("gen_ai.usage.output_tokens",
                             response.usage.completion_tokens)
            span.set_attribute("gen_ai.usage.total_tokens",
                             response.usage.total_tokens)

            # 计算延迟
            latency_ms = (time.time() - start_time) * 1000
            span.set_attribute("gen_ai.latency_ms", latency_ms)

            return response.choices[0].message.content

        except Exception as e:
            span.set_attribute("error.type", type(e).__name__)
            span.set_attribute("error.message", str(e))
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
```

#### Embeddings仪器化

```python
def create_embedding_with_telemetry(text: str, model: str = "text-embedding-3-small") -> list:
    """带仪器化的Embedding生成"""

    with tracer.start_as_current_span("gen_ai.embeddings") as span:
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "embeddings")
        span.set_attribute("gen_ai.request.model", model)

        try:
            client = openai.OpenAI()
            response = client.embeddings.create(
                model=model,
                input=text
            )

            span.set_attribute("gen_ai.usage.input_tokens",
                             response.usage.prompt_tokens)
            span.set_attribute("gen_ai.usage.total_tokens",
                             response.usage.total_tokens)
            span.set_attribute("gen_ai.embedding.dimensions",
                             len(response.data[0].embedding))

            return response.data[0].embedding

        except Exception as e:
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
```

#### 多模型统一接口

```python
from enum import Enum

class AISystem(Enum):
    OPENAI = "openai"
    ANTHROPIC = "anthropic"
    AZURE = "azure.ai.openai"

class UnifiedLLMClient:
    """支持多模型的统一LLM客户端，自动仪器化"""

    def __init__(self, system: AISystem, model: str):
        self.system = system.value
        self.model = model

    def chat(self, messages: list, **kwargs) -> str:
        with tracer.start_as_current_span("gen_ai.chat") as span:
            # 统一的仪器化
            span.set_attribute("gen_ai.system", self.system)
            span.set_attribute("gen_ai.operation.name", "chat")
            span.set_attribute("gen_ai.request.model", self.model)

            # 记录所有请求参数
            for key, value in kwargs.items():
                span.set_attribute(f"gen_ai.request.{key}", value)

            # 模型特定调用...
            if self.system == "openai":
                return self._call_openai(messages, **kwargs)
            elif self.system == "anthropic":
                return self._call_anthropic(messages, **kwargs)
            # ...
```

### 5.2 环境变量配置

```bash
# 服务标识
export OTEL_SERVICE_NAME="llm-chat-service"
export OTEL_RESOURCE_ATTRIBUTES="service.version=1.2.0,deployment.environment=production"

# 导出器配置
export OTEL_EXPORTER_OTLP_ENDPOINT="https://your-backend.com/otlp"
export OTEL_EXPORTER_OTLP_PROTOCOL="grpc"

# GenAI特定配置
export GENAI_LOG_CONTENT="false"  # 是否记录prompt/completion内容
export GENAI_MAX_CONTENT_LENGTH="1000"  # 内容最大长度

# 采样配置
export OTEL_TRACES_SAMPLER="parentbased_traceidratio"
export OTEL_TRACES_SAMPLER_ARG="0.1"  # 高流量场景下降低采样率
```

---

## 6. 最佳实践

### 6.1 敏感数据处理

```python
import hashlib

def sanitize_content(content: str, max_length: int = 1000) -> str:
    """清理敏感内容"""
    if not content:
        return content

    # 如果内容过长，截断并添加标记
    if len(content) > max_length:
        return content[:max_length] + "...[truncated]"

    return content

def hash_content(content: str) -> str:
    """计算内容哈希，用于追踪而不暴露内容"""
    return hashlib.sha256(content.encode()).hexdigest()[:16]

# 使用示例
with tracer.start_as_current_span("gen_ai.chat") as span:
    # 记录哈希而非内容
    span.set_attribute("gen_ai.prompt_hash", hash_content(user_prompt))

    # 仅在调试模式下记录完整内容
    if os.getenv("GENAI_LOG_CONTENT") == "true":
        span.set_attribute("gen_ai.input.messages",
                          sanitize_content(json.dumps(messages)))
```

### 6.2 成本监控

```python
def calculate_cost(input_tokens: int, output_tokens: int, model: str) -> float:
    """计算API调用成本 (USD)"""
    pricing = {
        "gpt-4o": {"input": 2.50 / 1_000_000, "output": 10.00 / 1_000_000},
        "gpt-4o-mini": {"input": 0.15 / 1_000_000, "output": 0.60 / 1_000_000},
        "claude-3-5-sonnet": {"input": 3.00 / 1_000_000, "output": 15.00 / 1_000_000},
    }

    if model not in pricing:
        return 0.0

    cost = (input_tokens * pricing[model]["input"] +
            output_tokens * pricing[model]["output"])
    return cost

# 在span中记录成本
span.set_attribute("gen_ai.estimated_cost_usd", calculate_cost(
    response.usage.prompt_tokens,
    response.usage.completion_tokens,
    model
))
```

### 6.3 错误处理

```python
try:
    response = client.chat.completions.create(...)
except openai.RateLimitError as e:
    span.set_attribute("error.type", "RateLimitError")
    span.set_attribute("gen_ai.error.code", "rate_limit_exceeded")
    span.set_attribute("gen_ai.retry_after", e.headers.get("retry-after", 0))
    span.set_status(trace.Status(trace.StatusCode.ERROR, "Rate limit exceeded"))
except openai.APIError as e:
    span.set_attribute("error.type", "APIError")
    span.set_attribute("gen_ai.error.code", e.code)
    span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
```

### 6.4 批量请求处理

```python
def batch_embeddings_with_telemetry(texts: list, model: str = "text-embedding-3-small"):
    """批量Embedding生成"""

    with tracer.start_as_current_span("gen_ai.embeddings.batch") as span:
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.operation.name", "embeddings")
        span.set_attribute("gen_ai.request.model", model)
        span.set_attribute("gen_ai.batch.size", len(texts))

        response = client.embeddings.create(model=model, input=texts)

        span.set_attribute("gen_ai.usage.total_tokens", response.usage.total_tokens)
        span.set_attribute("gen_ai.usage.tokens_per_item",
                         response.usage.total_tokens / len(texts))

        return [item.embedding for item in response.data]
```

---

## 7. 常见问题

### Q1: GenAI语义约定的稳定性如何？

**A**: 当前为**Development稳定性**，意味着仍在积极开发中，可能会有破坏性变更。建议：

- 关注[OpenTelemetry Semantic Conventions](https://github.com/open-telemetry/semantic-conventions)仓库
- 使用版本化的instrumentation库
- 预留更新周期

### Q2: 如何处理多模态输入（图像、音频）？

**A**: GenAI语义约定正在扩展以支持多模态。当前建议：

- 使用`generate_content`操作类型
- 记录内容类型和大小
- 使用外部存储引用大内容

### Q3: 是否支持流式响应？

**A**: 支持。对于流式响应：

- 创建父span表示整个流
- 为每个chunk创建子span（可选）
- 在父span中汇总总token数

### Q4: 如何处理函数调用/工具调用？

**A**: 使用`execute_tool`操作类型：

```python
span.set_attribute("gen_ai.operation.name", "execute_tool")
span.set_attribute("gen_ai.tool.name", "get_weather")
span.set_attribute("gen_ai.tool.arguments", json.dumps({"location": "NYC"}))
```

---

## 8. 参考资源

- [OpenTelemetry GenAI Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/gen-ai-spans/)
- [OpenLLMetry](https://github.com/traceloop/openllmetry) - 开源LLM仪器化
- [OpenAI API文档](https://platform.openai.com/docs/)
- [Anthropic API文档](https://docs.anthropic.com/)

---

**文档版本**: v1.0
**更新日期**: 2026年3月15日
**维护者**: OTLP项目团队

---

## 6. Agent语义约定 (v1.40 Draft)

> **状态**: Draft (草案阶段)
> **版本**: Semantic Conventions v1.41.0+
> **来源**: 基于Google AI Agent白皮书

### 6.1 概述

AI Agent是新兴的GenAI应用形态，具有自主决策、工具调用、多轮交互等特性。OTel v1.40新增了Agent语义约定草案。

### 6.2 Agent核心属性

| 属性名 | 类型 | 描述 | 示例 |
|:-------|:----:|:-----|:-----|
| gen_ai.agent.id | string | Agent唯一标识 | agent-001 |
| gen_ai.agent.name | string | Agent名称 | CustomerServiceAgent |
| gen_ai.agent.version | string | Agent版本 | 1.0.0 |
| gen_ai.agent.system | string | Agent框架 | langchain, llamaindex, autogen |
| gen_ai.agent.invocation.id | string | 调用ID | inv-12345 |
| gen_ai.agent.invocation.type | string | 调用类型 | synchronous, streaming |

### 6.3 Agent Span类型

**Agent创建Span**:
`python
with tracer.start_as_current_span("gen_ai.agent.create") as span:
    span.set_attribute("gen_ai.agent.id", "agent-001")
    span.set_attribute("gen_ai.agent.name", "ServiceAgent")
    span.set_attribute("gen_ai.agent.system", "langchain")
`

**Agent调用Span**:
`python
with tracer.start_as_current_span("gen_ai.agent.invoke") as span:
    span.set_attribute("gen_ai.agent.id", "agent-001")
    span.set_attribute("gen_ai.agent.invocation.type", "synchronous")
    # 调用Agent...
`

**Agent工具调用Span**:
`python
with tracer.start_as_current_span("gen_ai.agent.tool") as span:
    span.set_attribute("gen_ai.agent.tool.name", "search_database")
    # 执行工具...
`

### 6.4 Agent语义约定状态

| 约定领域 | 状态 | 说明 |
|:---------|:----:|:-----|
| LLM Spans | Development | 持续演进 |
| Agent Spans | **Draft** | v1.40新增草案 |
| Agent Tasks | Proposal | 提案阶段 |
| Agent Memory | Proposal | 提案阶段 |

### 6.5 参考资源

- [Google AI Agent Whitepaper](https://www.kaggle.com/whitepaper-agents)
- [OpenTelemetry GenAI Conventions](https://opentelemetry.io/docs/specs/semconv/gen-ai/)

---

**文档版本**: v1.1
**更新日期**: 2026年3月16日
**状态**: 已对齐OpenTelemetry Semantic Conventions v1.41.0
