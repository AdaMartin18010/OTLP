---
title: GenAI Observability: 生成式AI可观测性
description: GenAI Observability: 生成式AI可观测性 详细指南和最佳实践
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
  - security
  - compliance
  - genai
  - llm
  - ai
status: published
---
# GenAI Observability: 生成式AI可观测性

> **规范版本**: v1.30.0 (Experimental)
> **最后更新**: 2025年10月8日

---

## 目录

- [GenAI Observability: 生成式AI可观测性](#genai-observability-生成式ai可观测性)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 为什么需要GenAI可观测性](#11-为什么需要genai可观测性)
    - [1.2 特殊挑战](#12-特殊挑战)
  - [2. GenAI语义约定](#2-genai语义约定)
    - [2.1 LLM调用属性](#21-llm调用属性)
    - [2.2 Token使用追踪](#22-token使用追踪)
  - [3. Prompt追踪](#3-prompt追踪)
  - [4. 成本追踪](#4-成本追踪)
  - [5. 性能监控](#5-性能监控)
  - [6. 质量监控](#6-质量监控)
  - [7. 实现示例](#7-实现示例)
    - [7.1 OpenAI集成](#71-openai集成)
    - [7.2 LangChain集成](#72-langchain集成)
  - [8. Dashboard与告警](#8-dashboard与告警)
  - [9. 安全与合规](#9-安全与合规)
  - [10. 最佳实践](#10-最佳实践)
  - [11. 参考资源](#11-参考资源)

---

## 1. 概述

### 1.1 为什么需要GenAI可观测性

```text
GenAI应用挑战:
1. 不确定性
   - 输出非确定性
   - 难以预测行为
   - 需要监控质量

2. 成本高
   - Token计费
   - API调用昂贵
   - 需要精确追踪成本

3. 延迟高
   - LLM响应慢 (1-10s)
   - 用户体验关键
   - 需要优化性能

4. 质量难评估
   - 主观性强
   - 需要多维度评估
   - 需要持续监控

5. 安全风险
   - Prompt注入
   - 数据泄露
   - 需要审计

可观测性解决:
✅ 追踪每次LLM调用
✅ 监控Token使用与成本
✅ 分析延迟与性能
✅ 评估输出质量
✅ 检测异常行为
✅ 审计敏感操作
```

### 1.2 特殊挑战

```text
与传统应用的区别:
┌────────────────┬──────────────┬──────────────┐
│ 维度           │ 传统应用      │ GenAI应用    │
├────────────────┼──────────────┼──────────────┤
│ 延迟           │ 10-100ms     │ 1-10s        │
│ 成本可预测性    │ 高           │ 低           │
│ 输出确定性      │ 高           │ 低           │
│ 监控复杂度      │ 中           │ 高           │
│ 成本追踪        │ 简单         │ 复杂         │
└────────────────┴──────────────┴──────────────┘

需要追踪:
- 每次API调用
- Token使用 (input + output)
- 模型版本
- 参数配置 (temperature, max_tokens)
- Prompt模板
- 输出质量指标
- 成本归因
```

---

## 2. GenAI语义约定

### 2.1 LLM调用属性

```text
核心属性:
┌──────────────────────────┬─────────┬────────────────────┐
│ 属性名                    │ 类型    │ 示例               │
├──────────────────────────┼─────────┼────────────────────┤
│ gen_ai.system            │ string  │ "openai"           │
│ gen_ai.request.model     │ string  │ "gpt-4"            │
│ gen_ai.request.max_tokens│ int     │ 1000               │
│ gen_ai.request.temperature│float   │ 0.7                │
│ gen_ai.request.top_p     │ float   │ 1.0                │
│ gen_ai.usage.input_tokens│ int     │ 150                │
│ gen_ai.usage.output_tokens│int     │ 50                 │
│ gen_ai.response.id       │ string  │ "chatcmpl-abc123"  │
│ gen_ai.response.model    │ string  │ "gpt-4-0613"       │
│ gen_ai.response.finish_reason│string│"stop"             │
└──────────────────────────┴─────────┴────────────────────┘

gen_ai.system标准值:
- "openai" (OpenAI)
- "anthropic" (Claude)
- "cohere"
- "huggingface"
- "vertex_ai" (Google)
- "azure_openai"

gen_ai.response.finish_reason:
- "stop" (正常结束)
- "length" (达到max_tokens)
- "content_filter" (内容过滤)
- "tool_calls" (函数调用)

完整示例:
{
  "gen_ai.system": "openai",
  "gen_ai.request.model": "gpt-4-turbo-preview",
  "gen_ai.request.max_tokens": 1000,
  "gen_ai.request.temperature": 0.7,
  "gen_ai.request.top_p": 1.0,
  "gen_ai.request.frequency_penalty": 0.0,
  "gen_ai.request.presence_penalty": 0.0,
  "gen_ai.usage.input_tokens": 150,
  "gen_ai.usage.output_tokens": 50,
  "gen_ai.usage.total_tokens": 200,
  "gen_ai.response.id": "chatcmpl-8abc123def",
  "gen_ai.response.model": "gpt-4-0613",
  "gen_ai.response.finish_reason": "stop"
}
```

### 2.2 Token使用追踪

```text
Token属性:
┌──────────────────────────┬─────────┬────────┐
│ 属性名                   │ 类型    │ 示例   │
├──────────────────────────┼─────────┼────────┤
│ gen_ai.usage.input_tokens│ int     │ 150    │
│ gen_ai.usage.output_tokens│int    │ 50     │
│ gen_ai.usage.total_tokens│ int     │ 200    │
└──────────────────────────┴─────────┴────────┘

计算公式:
total_tokens = input_tokens + output_tokens

Token成本:
不同模型不同价格

GPT-4 Turbo:
- Input: $0.01 / 1K tokens
- Output: $0.03 / 1K tokens

GPT-3.5 Turbo:
- Input: $0.0005 / 1K tokens
- Output: $0.0015 / 1K tokens

示例计算:
请求:
- Input: 150 tokens
- Output: 50 tokens
- 模型: GPT-4 Turbo

成本:
- Input cost: 150 * $0.01 / 1000 = $0.0015
- Output cost: 50 * $0.03 / 1000 = $0.0015
- Total: $0.003

Span属性:
span.SetAttributes(
    attribute.Int("gen_ai.usage.input_tokens", 150),
    attribute.Int("gen_ai.usage.output_tokens", 50),
    attribute.Float64("gen_ai.cost.usd", 0.003),
)
```

---

## 3. Prompt追踪

```text
Prompt属性:
┌──────────────────────────┬─────────┬────────────────────┐
│ 属性名                    │ 类型    │ 示例               │
├──────────────────────────┼─────────┼────────────────────┤
│ gen_ai.prompt.0.role     │ string  │ "system"           │
│ gen_ai.prompt.0.content  │ string  │ "You are..."       │
│ gen_ai.prompt.1.role     │ string  │ "user"             │
│ gen_ai.prompt.1.content  │ string  │ "Summarize..."     │
│ gen_ai.completion.0.role │ string  │ "assistant"        │
│ gen_ai.completion.0.content│string │ "Here is..."       │
└──────────────────────────┴─────────┴────────────────────┘

注意:
⚠️ Prompt和Completion可能包含敏感数据
⚠️ 生产环境可能需要脱敏或不记录

脱敏策略:
1. 完全不记录
   - 合规要求高

2. 记录元数据
   - 长度、Token数
   - 不记录内容

3. 哈希
   - 记录内容哈希
   - 用于去重

4. 部分记录
   - 只记录前100字符
   - 敏感部分删除

5. 采样记录
   - 只记录1%请求
   - 用于调试

示例 (记录元数据):
span.SetAttributes(
    attribute.Int("gen_ai.prompt.length", len(prompt)),
    attribute.Int("gen_ai.prompt.messages", 2),
    // 不记录实际内容
)

示例 (完整记录, 开发环境):
span.AddEvent("gen_ai.prompt", trace.WithAttributes(
    attribute.String("role", "user"),
    attribute.String("content", promptText),
))

span.AddEvent("gen_ai.completion", trace.WithAttributes(
    attribute.String("role", "assistant"),
    attribute.String("content", completionText),
))
```

---

## 4. 成本追踪

```go
// 成本计算器
type CostCalculator struct {
    // 价格表 (USD per 1K tokens)
    prices map[string]ModelPrice
}

type ModelPrice struct {
    InputPer1K  float64
    OutputPer1K float64
}

func NewCostCalculator() *CostCalculator {
    return &CostCalculator{
        prices: map[string]ModelPrice{
            "gpt-4-turbo-preview": {
                InputPer1K:  0.01,
                OutputPer1K: 0.03,
            },
            "gpt-4": {
                InputPer1K:  0.03,
                OutputPer1K: 0.06,
            },
            "gpt-3.5-turbo": {
                InputPer1K:  0.0005,
                OutputPer1K: 0.0015,
            },
        },
    }
}

func (c *CostCalculator) Calculate(model string, inputTokens, outputTokens int) float64 {
    price, ok := c.prices[model]
    if !ok {
        return 0
    }

    inputCost := float64(inputTokens) * price.InputPer1K / 1000
    outputCost := float64(outputTokens) * price.OutputPer1K / 1000

    return inputCost + outputCost
}

// 追踪成本
func trackLLMCall(ctx context.Context, model string, inputTokens, outputTokens int) {
    _, span := tracer.Start(ctx, "llm.call")
    defer span.End()

    calc := NewCostCalculator()
    cost := calc.Calculate(model, inputTokens, outputTokens)

    span.SetAttributes(
        attribute.String("gen_ai.system", "openai"),
        attribute.String("gen_ai.request.model", model),
        attribute.Int("gen_ai.usage.input_tokens", inputTokens),
        attribute.Int("gen_ai.usage.output_tokens", outputTokens),
        attribute.Int("gen_ai.usage.total_tokens", inputTokens+outputTokens),
        attribute.Float64("gen_ai.cost.usd", cost),
    )

    // 记录指标
    costCounter.Add(ctx, cost, metric.WithAttributes(
        attribute.String("model", model),
    ))

    tokenCounter.Add(ctx, int64(inputTokens+outputTokens), metric.WithAttributes(
        attribute.String("model", model),
        attribute.String("type", "total"),
    ))
}

// 成本归因
func attributeCost(ctx context.Context, userID, feature string, cost float64) {
    costCounter.Add(ctx, cost, metric.WithAttributes(
        attribute.String("user_id", userID),
        attribute.String("feature", feature),
    ))
}

// 成本报表查询 (Prometheus)
// 每个用户的成本
sum by (user_id) (rate(gen_ai_cost_usd_total[24h]))

// 每个功能的成本
sum by (feature) (rate(gen_ai_cost_usd_total[24h]))

// 每个模型的成本
sum by (model) (rate(gen_ai_cost_usd_total[24h]))

// 总成本
sum(rate(gen_ai_cost_usd_total[24h])) * 24 * 30  # 月成本预估
```

---

## 5. 性能监控

```go
// 延迟追踪
func monitorLLMLatency(ctx context.Context) {
    meter := otel.Meter("genai")

    // Histogram: LLM响应延迟
    latencyHistogram, _ := meter.Float64Histogram(
        "gen_ai.latency",
        metric.WithDescription("LLM response latency"),
        metric.WithUnit("ms"),
    )

    // Time to First Token (TTFT)
    ttftHistogram, _ := meter.Float64Histogram(
        "gen_ai.ttft",
        metric.WithDescription("Time to first token"),
        metric.WithUnit("ms"),
    )

    // Tokens per second
    tpsGauge, _ := meter.Float64Histogram(
        "gen_ai.tokens_per_second",
        metric.WithDescription("Token generation speed"),
        metric.WithUnit("tokens/s"),
    )
}

// 使用示例
func callLLM(ctx context.Context, prompt string) (string, error) {
    ctx, span := tracer.Start(ctx, "llm.call")
    defer span.End()

    start := time.Now()
    firstTokenTime := time.Time{}

    // 流式响应
    stream, err := client.CreateChatCompletionStream(ctx, request)
    if err != nil {
        span.RecordError(err)
        return "", err
    }
    defer stream.Close()

    var response strings.Builder
    tokenCount := 0

    for {
        chunk, err := stream.Recv()
        if err == io.EOF {
            break
        }
        if err != nil {
            span.RecordError(err)
            return "", err
        }

        // 记录第一个token时间
        if firstTokenTime.IsZero() {
            firstTokenTime = time.Now()
            ttft := firstTokenTime.Sub(start).Milliseconds()

            span.SetAttributes(attribute.Int64("gen_ai.ttft_ms", ttft))
            ttftHistogram.Record(ctx, float64(ttft))
        }

        response.WriteString(chunk.Choices[0].Delta.Content)
        tokenCount++
    }

    duration := time.Since(start)

    // 记录延迟
    latencyHistogram.Record(ctx, float64(duration.Milliseconds()),
        metric.WithAttributes(
            attribute.String("model", "gpt-4"),
        ),
    )

    // 记录Tokens/s
    if duration.Seconds() > 0 {
        tps := float64(tokenCount) / duration.Seconds()
        tpsGauge.Record(ctx, tps)
    }

    span.SetAttributes(
        attribute.Int64("gen_ai.latency_ms", duration.Milliseconds()),
        attribute.Int("gen_ai.output_tokens", tokenCount),
    )

    return response.String(), nil
}
```

---

## 6. 质量监控

```go
// 质量指标
type QualityMetrics struct {
    relevance   float64  // 相关性 (0-1)
    coherence   float64  // 连贯性 (0-1)
    groundedness float64 // 事实性 (0-1)
    safety      float64  // 安全性 (0-1)
}

// 评估输出质量
func evaluateQuality(ctx context.Context, prompt, completion string) QualityMetrics {
    // 使用另一个LLM评估质量
    evaluator := NewQualityEvaluator()

    metrics := evaluator.Evaluate(ctx, prompt, completion)

    // 记录指标
    meter := otel.Meter("genai.quality")

    relevanceGauge, _ := meter.Float64Histogram("gen_ai.quality.relevance")
    relevanceGauge.Record(ctx, metrics.relevance)

    coherenceGauge, _ := meter.Float64Histogram("gen_ai.quality.coherence")
    coherenceGauge.Record(ctx, metrics.coherence)

    // 检测低质量输出
    if metrics.relevance < 0.5 {
        logger.Warn("Low relevance score",
            "prompt", prompt[:100],
            "score", metrics.relevance)
    }

    return metrics
}

// 检测Hallucination (幻觉)
func detectHallucination(ctx context.Context, completion string, sources []string) bool {
    // 检查输出是否基于可靠来源
    checker := NewFactChecker()

    isGrounded := checker.Check(ctx, completion, sources)

    if !isGrounded {
        // 记录幻觉事件
        span := trace.SpanFromContext(ctx)
        span.AddEvent("hallucination_detected", trace.WithAttributes(
            attribute.String("completion", completion[:100]),
        ))

        hallucinationCounter.Add(ctx, 1)
    }

    return !isGrounded
}

// 安全检测
func detectUnsafeContent(ctx context.Context, text string) []string {
    detector := NewSafetyDetector()

    violations := detector.Detect(ctx, text)

    if len(violations) > 0 {
        span := trace.SpanFromContext(ctx)
        span.SetAttributes(
            attribute.Bool("gen_ai.unsafe_content", true),
            attribute.StringSlice("gen_ai.violations", violations),
        )

        safetyViolationCounter.Add(ctx, int64(len(violations)))
    }

    return violations
}
```

---

## 7. 实现示例

### 7.1 OpenAI集成

```go
package genai

import (
    "context"

    "github.com/sashabaranov/go-openai"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

type InstrumentedClient struct {
    client *openai.Client
    tracer trace.Tracer
    calculator *CostCalculator
}

func NewInstrumentedClient(apiKey string) *InstrumentedClient {
    return &InstrumentedClient{
        client: openai.NewClient(apiKey),
        tracer: otel.Tracer("genai.openai"),
        calculator: NewCostCalculator(),
    }
}

func (c *InstrumentedClient) CreateChatCompletion(
    ctx context.Context,
    req openai.ChatCompletionRequest,
) (openai.ChatCompletionResponse, error) {

    ctx, span := c.tracer.Start(ctx, "openai.chat.completion",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    // 记录请求属性
    span.SetAttributes(
        attribute.String("gen_ai.system", "openai"),
        attribute.String("gen_ai.request.model", req.Model),
        attribute.Int("gen_ai.request.max_tokens", req.MaxTokens),
        attribute.Float64("gen_ai.request.temperature", float64(req.Temperature)),
        attribute.Float64("gen_ai.request.top_p", float64(req.TopP)),
        attribute.Int("gen_ai.request.n", req.N),
    )

    // 记录prompt (可选，注意敏感数据)
    if shouldRecordPrompt() {
        for i, msg := range req.Messages {
            span.AddEvent("gen_ai.prompt", trace.WithAttributes(
                attribute.Int("index", i),
                attribute.String("role", msg.Role),
                attribute.Int("content_length", len(msg.Content)),
                // attribute.String("content", msg.Content), // 生产环境慎用
            ))
        }
    }

    // 调用API
    resp, err := c.client.CreateChatCompletion(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return resp, err
    }

    // 记录响应属性
    span.SetAttributes(
        attribute.String("gen_ai.response.id", resp.ID),
        attribute.String("gen_ai.response.model", resp.Model),
        attribute.Int("gen_ai.usage.input_tokens", resp.Usage.PromptTokens),
        attribute.Int("gen_ai.usage.output_tokens", resp.Usage.CompletionTokens),
        attribute.Int("gen_ai.usage.total_tokens", resp.Usage.TotalTokens),
    )

    if len(resp.Choices) > 0 {
        span.SetAttributes(
            attribute.String("gen_ai.response.finish_reason",
                string(resp.Choices[0].FinishReason)),
        )
    }

    // 计算成本
    cost := c.calculator.Calculate(
        req.Model,
        resp.Usage.PromptTokens,
        resp.Usage.CompletionTokens,
    )
    span.SetAttributes(attribute.Float64("gen_ai.cost.usd", cost))

    // 记录指标
    recordMetrics(ctx, req.Model, resp.Usage, cost)

    span.SetStatus(codes.Ok, "")
    return resp, nil
}

func recordMetrics(ctx context.Context, model string, usage openai.Usage, cost float64) {
    meter := otel.Meter("genai.openai")

    // Token计数
    tokenCounter, _ := meter.Int64Counter("gen_ai.tokens")
    tokenCounter.Add(ctx, int64(usage.TotalTokens),
        metric.WithAttributes(
            attribute.String("model", model),
        ),
    )

    // 成本
    costCounter, _ := meter.Float64Counter("gen_ai.cost")
    costCounter.Add(ctx, cost,
        metric.WithAttributes(
            attribute.String("model", model),
        ),
    )
}
```

### 7.2 LangChain集成

```python
from langchain.callbacks.base import BaseCallbackHandler
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode

class OpenTelemetryCallbackHandler(BaseCallbackHandler):
    def __init__(self):
        self.tracer = trace.get_tracer(__name__)
        self.span_stack = []

    def on_llm_start(self, serialized, prompts, **kwargs):
        """LLM调用开始"""
        span = self.tracer.start_span("llm.call")
        self.span_stack.append(span)

        # 记录请求属性
        span.set_attributes({
            "gen_ai.system": "openai",
            "gen_ai.request.model": kwargs.get("invocation_params", {}).get("model_name"),
            "gen_ai.request.temperature": kwargs.get("invocation_params", {}).get("temperature"),
        })

    def on_llm_end(self, response, **kwargs):
        """LLM调用结束"""
        if not self.span_stack:
            return

        span = self.span_stack.pop()

        # 记录Token使用
        if hasattr(response, "llm_output") and response.llm_output:
            token_usage = response.llm_output.get("token_usage", {})
            span.set_attributes({
                "gen_ai.usage.input_tokens": token_usage.get("prompt_tokens", 0),
                "gen_ai.usage.output_tokens": token_usage.get("completion_tokens", 0),
                "gen_ai.usage.total_tokens": token_usage.get("total_tokens", 0),
            })

        span.set_status(Status(StatusCode.OK))
        span.end()

    def on_llm_error(self, error, **kwargs):
        """LLM调用错误"""
        if not self.span_stack:
            return

        span = self.span_stack.pop()
        span.record_exception(error)
        span.set_status(Status(StatusCode.ERROR, str(error)))
        span.end()

# 使用
from langchain.llms import OpenAI

llm = OpenAI(
    temperature=0.7,
    callbacks=[OpenTelemetryCallbackHandler()]
)

response = llm("Summarize this text...")
```

---

## 8. Dashboard与告警

**Grafana Dashboard**:

```text
Panel 1: LLM调用量
Query: sum(rate(gen_ai_tokens_total[5m])) by (model)
Visualization: Time series

Panel 2: Token使用
Query: sum by (model, type) (rate(gen_ai_tokens_total[5m]))
Visualization: Stacked area chart

Panel 3: 成本
Query: sum(rate(gen_ai_cost_usd_total[1h])) * 24 * 30
Visualization: Stat (月成本预估)

Panel 4: 延迟分布
Query: histogram_quantile(0.99, rate(gen_ai_latency_bucket[5m]))
Visualization: Heatmap

Panel 5: 错误率
Query: rate(gen_ai_errors_total[5m]) / rate(gen_ai_requests_total[5m])
Visualization: Time series

Panel 6: 成本分解 (按功能)
Query: sum by (feature) (rate(gen_ai_cost_usd_total[1h]))
Visualization: Pie chart
```

**告警规则**:

```yaml
# Prometheus告警
groups:
  - name: genai_alerts
    rules:
      # 高成本告警
      - alert: HighGenAICost
        expr: sum(rate(gen_ai_cost_usd_total[1h])) * 24 * 30 > 1000
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "High GenAI monthly cost: {{ $value | humanize }}USD"

      # 高延迟告警
      - alert: HighGenAILatency
        expr: histogram_quantile(0.99, rate(gen_ai_latency_bucket[5m])) > 10000
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High GenAI p99 latency: {{ $value | humanize }}ms"

      # 高错误率告警
      - alert: HighGenAIErrorRate
        expr: rate(gen_ai_errors_total[5m]) / rate(gen_ai_requests_total[5m]) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High GenAI error rate: {{ $value | humanizePercentage }}"

      # 异常Token使用
      - alert: AnomalousTokenUsage
        expr: rate(gen_ai_tokens_total[5m]) > avg_over_time(rate(gen_ai_tokens_total[5m])[1h:5m]) * 3
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Anomalous token usage spike"
```

---

## 9. 安全与合规

```text
安全考虑:
1. Prompt注入检测
   - 检测恶意Prompt
   - 记录可疑请求
   - 自动拦截

2. 数据泄露防护
   - 不记录敏感Prompt/Completion
   - 使用脱敏
   - 限制访问

3. 审计日志
   - 记录所有LLM调用
   - 用户归因
   - 合规要求

4. 成本控制
   - 用户限额
   - 功能限额
   - 自动熔断

示例实现:
func secureTrace(ctx context.Context, prompt, completion string) {
    _, span := tracer.Start(ctx, "llm.call")
    defer span.End()

    // 1. 检测Prompt注入
    if detectInjection(prompt) {
        span.SetAttributes(attribute.Bool("security.injection_detected", true))
        injectionCounter.Add(ctx, 1)
        return // 拒绝请求
    }

    // 2. 脱敏
    sanitizedPrompt := sanitize(prompt)

    // 3. 只记录元数据
    span.SetAttributes(
        attribute.Int("prompt.length", len(prompt)),
        attribute.String("prompt.hash", hash(prompt)),
        // 不记录实际内容
    )

    // 4. 审计日志
    auditLog(ctx, "llm.call", userID, sanitizedPrompt)
}

合规实践:
✅ 数据最小化
   - 只记录必要信息
   - 定期删除旧数据

✅ 访问控制
   - RBAC
   - 审计追踪

✅ 数据保留
   - 明确保留期限
   - 自动清理

✅ 透明度
   - 用户知情
   - 可查询自己的数据
```

---

## 10. 最佳实践

```text
✅ DO (推荐)
1. 始终追踪Token使用
   - 每次调用记录
   - 成本归因到用户/功能

2. 监控关键指标
   - 延迟 (p50, p99)
   - 错误率
   - 成本
   - Token/s

3. 采样Prompt/Completion
   - 生产环境少记录 (< 1%)
   - 开发环境全记录
   - 使用脱敏

4. 设置告警
   - 成本超预算
   - 延迟过高
   - 错误率高
   - Token使用异常

5. 成本优化
   - 使用更便宜的模型
   - 缓存重复请求
   - 优化Prompt长度
   - 批处理

❌ DON'T (避免)
1. 不要记录敏感Prompt
2. 不要忽略成本追踪
3. 不要跳过错误处理
4. 不要阻塞应用 (同步追踪)
5. 不要忽略质量监控

示例最佳配置:
span.SetAttributes(
    // ✅ 必需
    attribute.String("gen_ai.system", "openai"),
    attribute.String("gen_ai.request.model", "gpt-4"),
    attribute.Int("gen_ai.usage.input_tokens", 150),
    attribute.Int("gen_ai.usage.output_tokens", 50),
    attribute.Float64("gen_ai.cost.usd", 0.003),

    // ✅ 推荐
    attribute.Int64("gen_ai.latency_ms", 1234),
    attribute.String("gen_ai.response.finish_reason", "stop"),

    // ⚠️ 可选 (小心敏感数据)
    attribute.Int("gen_ai.prompt.length", len(prompt)),

    // ❌ 避免 (生产环境)
    // attribute.String("gen_ai.prompt.content", prompt),
)
```

---

## 11. 参考资源

- **GenAI语义约定**: <https://opentelemetry.io/docs/specs/semconv/gen-ai/>
- **LangChain Observability**: <https://python.langchain.com/docs/integrations/callbacks/opentelemetry>
- **OpenLIT**: <https://github.com/openlit/openlit> (GenAI可观测性工具)

---

**文档状态**: ✅ 完成
**规范状态**: 🚧 实验性 (Experimental)
**生产就绪**: 部分功能已成熟
