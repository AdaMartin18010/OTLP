---
title: LLM应用可观测性实践
description: 基于OpenTelemetry的LLM应用可观测性方案，包括GenAI语义约定、Prompt追踪、Token消耗监控和成本优化
category: 应用实践
tags:
  - genai
  - llm
  - opentelemetry
  - cost-optimization
  - prompt-engineering
version: Semantic Conventions v1.40.0
date: 2026-03-17
status: published
---

# LLM应用可观测性实践

> **适用场景**: AI应用开发、LLM服务运维
> **技术深度**: ⭐⭐⭐ (中级)
> **最后更新**: 2026-03-17

---

## 1. GenAI可观测性概述

### 1.1 为什么LLM需要专门的可观测性

```
LLM应用的特殊挑战:
├── 非确定性输出
│   └── 相同输入可能产生不同结果
├── 高成本运算
│   └── Token消耗直接关联成本
├── Prompt工程复杂性
│   └── 需要追踪和优化Prompt
├── 响应延迟高
│   └── 流式响应需要特殊处理
└── 合规与安全
    └── 敏感信息过滤、审计追踪
```

### 1.2 GenAI语义约定 (v1.40.0)

```yaml
# GenAI核心属性
gen_ai.system: "openai"              # AI系统类型
gen_ai.request.model: "gpt-4"        # 请求模型
gen_ai.response.model: "gpt-4"       # 响应模型
gen_ai.usage.input_tokens: 150       # 输入Token数
gen_ai.usage.output_tokens: 80       # 输出Token数
gen_ai.usage.total_tokens: 230       # 总Token数

# OpenAI特定
gen_ai.openai.request.seed: 42       # 随机种子
gen_ai.openai.response.system_fingerprint: "fp_xxx"

# 向量数据库
gen_ai.vector_db.system: "pinecone"  # 向量数据库类型
```

---

## 2. SDK集成实践

### 2.1 Python (OpenAI)

```python
from openai import OpenAI
from opentelemetry import trace
from opentelemetry.instrumentation.openai import OpenAIInstrumentor

# 自动埋点
OpenAIInstrumentor().instrument()

client = OpenAI()
tracer = trace.get_tracer(__name__)

def chat_with_llm(prompt: str) -> str:
    with tracer.start_as_current_span("llm.chat") as span:
        span.set_attribute("gen_ai.system", "openai")
        span.set_attribute("gen_ai.request.model", "gpt-4")
        span.set_attribute("gen_ai.prompt", prompt[:100])  # 记录前100字符

        response = client.chat.completions.create(
            model="gpt-4",
            messages=[{"role": "user", "content": prompt}],
            temperature=0.7,
        )

        # 自动记录的属性:
        # - gen_ai.usage.input_tokens
        # - gen_ai.usage.output_tokens
        # - gen_ai.response.model

        result = response.choices[0].message.content
        span.set_attribute("gen_ai.response.length", len(result))

        return result
```

### 2.2 手动埋点 (无自动埋点SDK时)

```python
from opentelemetry import trace
from opentelemetry.semconv.attributes.gen_ai_attributes import *

tracer = trace.get_tracer(__name__)

class LLMTracer:
    def __init__(self):
        self.total_tokens = 0
        self.total_cost = 0.0

    def trace_completion(self, model: str, prompt: str, response: dict):
        with tracer.start_as_current_span("gen_ai.completion") as span:
            # 系统信息
            span.set_attribute(GEN_AI_SYSTEM, "openai")
            span.set_attribute(GEN_AI_REQUEST_MODEL, model)
            span.set_attribute(GEN_AI_RESPONSE_MODEL, response.get("model"))

            # Token使用
            usage = response.get("usage", {})
            input_tokens = usage.get("prompt_tokens", 0)
            output_tokens = usage.get("completion_tokens", 0)
            total_tokens = usage.get("total_tokens", 0)

            span.set_attribute(GEN_AI_USAGE_INPUT_TOKENS, input_tokens)
            span.set_attribute(GEN_AI_USAGE_OUTPUT_TOKENS, output_tokens)
            span.set_attribute(GEN_AI_USAGE_TOTAL_TOKENS, total_tokens)

            # 成本计算 (OpenAI定价)
            cost = self._calculate_cost(model, input_tokens, output_tokens)
            span.set_attribute("gen_ai.cost.usd", cost)

            # Prompt和Response哈希 (用于去重)
            span.set_attribute("gen_ai.prompt.hash", hashlib.sha256(prompt.encode()).hexdigest()[:16])

            return span

    def _calculate_cost(self, model: str, input_tokens: int, output_tokens: int) -> float:
        pricing = {
            "gpt-4": {"input": 0.03, "output": 0.06},
            "gpt-4-turbo": {"input": 0.01, "output": 0.03},
            "gpt-3.5-turbo": {"input": 0.0005, "output": 0.0015},
        }
        p = pricing.get(model, pricing["gpt-3.5-turbo"])
        return (input_tokens * p["input"] + output_tokens * p["output"]) / 1000
```

---

## 3. 关键指标监控

### 3.1 Token消耗监控

```promql
# Token消耗率
sum(rate(gen_ai_usage_total_tokens[5m])) by (model)

# 成本估算 (USD/小时)
sum(
  rate(gen_ai_usage_input_tokens[1h]) * 0.00001 +
  rate(gen_ai_usage_output_tokens[1h]) * 0.00003
) by (model)

# 异常检测 - Token激增
abs(
  sum(rate(gen_ai_usage_total_tokens[5m]))
  -
  sum(rate(gen_ai_usage_total_tokens[5m] offset 1h))
) > 1000
```

### 3.2 性能监控

```promql
# LLM调用延迟
histogram_quantile(0.95,
  sum(rate(gen_ai_completion_duration_bucket[5m])) by (le, model)
)

# 错误率
sum(rate(gen_ai_completion_errors[5m])) by (error_type)
/
sum(rate(gen_ai_completion_total[5m]))

# 流式响应首Token延迟
gen_ai_time_to_first_token
```

---

## 4. 成本优化

### 4.1 成本监控Dashboard

```yaml
# 成本追踪维度
成本分析:
  按模型:
    - gpt-4: $0.03/1K input tokens
    - gpt-3.5-turbo: $0.0005/1K input tokens

  按应用:
    - chatbot: 40%成本
    - code-assist: 35%成本
    - data-analysis: 25%成本

  按时间:
    - 高峰时段: 9-11am, 2-4pm
    - 低谷时段: 夜间
```

### 4.2 优化策略

```python
# 1. 缓存常用响应
class LLMCache:
    def __init__(self):
        self.cache = {}

    def get(self, prompt: str, model: str):
        key = hashlib.sha256(f"{model}:{prompt}".encode()).hexdigest()
        return self.cache.get(key)

    def set(self, prompt: str, model: str, response: str):
        key = hashlib.sha256(f"{model}:{prompt}".encode()).hexdigest()
        self.cache[key] = response

# 2. 模型降级策略
def smart_completion(prompt: str, complexity: float):
    if complexity < 0.3:
        model = "gpt-3.5-turbo"  # 低成本
    elif complexity < 0.7:
        model = "gpt-4-turbo"
    else:
        model = "gpt-4"  # 高性能

    return call_llm(prompt, model)

# 3. Token预算控制
class TokenBudget:
    def __init__(self, daily_limit: int):
        self.daily_limit = daily_limit
        self.used_today = 0

    def check_budget(self, estimated_tokens: int) -> bool:
        if self.used_today + estimated_tokens > self.daily_limit:
            raise BudgetExceededError("Daily token budget exceeded")
        return True
```

---

**最后更新**: 2026-03-17
**状态**: Published
