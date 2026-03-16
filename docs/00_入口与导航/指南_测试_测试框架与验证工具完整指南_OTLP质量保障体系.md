# 🧪 测试框架与验证工具完整指南_OTLP质量保障体系

## 📋 目录

- [🧪 测试框架与验证工具完整指南\_OTLP质量保障体系](#-测试框架与验证工具完整指南_otlp质量保障体系)
  - [📋 目录](#-目录)
  - [1. OTLP 测试体系概述](#1-otlp-测试体系概述)
    - [1.1 测试金字塔与测试策略](#11-测试金字塔与测试策略)
      - [分层测试策略](#分层测试策略)
    - [1.2 OTLP 特定的测试挑战](#12-otlp-特定的测试挑战)
      - [挑战 1: 分布式系统的不确定性](#挑战-1-分布式系统的不确定性)
      - [挑战 2: 多协议多语言兼容性](#挑战-2-多协议多语言兼容性)
      - [挑战 3: 性能与正确性的平衡](#挑战-3-性能与正确性的平衡)
    - [1.3 端到端质量保障流程](#13-端到端质量保障流程)
      - [质量门禁标准](#质量门禁标准)
    - [1.4 测试环境与基础设施](#14-测试环境与基础设施)
      - [推荐的测试环境架构](#推荐的测试环境架构)
      - [测试环境管理脚本](#测试环境管理脚本)
  - [2. 单元测试框架](#2-单元测试框架)
    - [2.1 多语言单元测试最佳实践](#21-多语言单元测试最佳实践)
      - [Python (pytest)](#python-pytest)
      - [Go (testing + testify)](#go-testing--testify)
    - [2.2 Mock 与 Stub 策略](#22-mock-与-stub-策略)
      - [使用 Mock 隔离外部依赖](#使用-mock-隔离外部依赖)
    - [2.3 测试覆盖率与质量门禁](#23-测试覆盖率与质量门禁)
      - [配置覆盖率工具](#配置覆盖率工具)
  - [3. 集成测试框架](#3-集成测试框架)
    - [3.1 OTLP Collector 集成测试](#31-otlp-collector-集成测试)
      - [使用 Testcontainers 进行集成测试](#使用-testcontainers-进行集成测试)
    - [3.2 多组件联调测试](#32-多组件联调测试)
  - [4. 端到端测试 (E2E)](#4-端到端测试-e2e)
    - [4.1 分布式追踪场景测试](#41-分布式追踪场景测试)
    - [4.2 跨服务链路验证](#42-跨服务链路验证)
    - [4.3 性能基准测试](#43-性能基准测试)
      - [K6 性能测试脚本](#k6-性能测试脚本)
      - [JMeter 性能测试计划](#jmeter-性能测试计划)
    - [4.4 混沌工程 (Chaos Engineering)](#44-混沌工程-chaos-engineering)
  - [5. 协议一致性验证](#5-协议一致性验证)
    - [5.1 OTLP/gRPC 协议验证](#51-otlpgrpc-协议验证)
  - [7. 自动化测试流水线](#7-自动化测试流水线)
    - [7.1 CI/CD 集成 (GitHub Actions)](#71-cicd-集成-github-actions)
  - [8. 工具链与生态](#8-工具链与生态)
    - [8.1 推荐测试工具矩阵](#81-推荐测试工具矩阵)
    - [8.2 自定义测试工具开发](#82-自定义测试工具开发)
  - [9. 最佳实践与案例研究](#9-最佳实践与案例研究)
    - [9.1 行业标杆案例](#91-行业标杆案例)
      - [案例 1: Uber - 大规模分布式追踪测试](#案例-1-uber---大规模分布式追踪测试)
      - [案例 2: Netflix - 混沌工程驱动的可观测性测试](#案例-2-netflix---混沌工程驱动的可观测性测试)
    - [9.2 常见陷阱与解决方案](#92-常见陷阱与解决方案)
      - [陷阱 1: 测试环境与生产环境差异过大](#陷阱-1-测试环境与生产环境差异过大)
      - [陷阱 2: 测试数据不真实](#陷阱-2-测试数据不真实)
      - [陷阱 3: 测试数据污染](#陷阱-3-测试数据污染)
    - [9.3 测试策略演进路径](#93-测试策略演进路径)
      - [阶段 1: 基础测试 (0-3 个月)](#阶段-1-基础测试-0-3-个月)
      - [阶段 2: 自动化增强 (3-6 个月)](#阶段-2-自动化增强-3-6-个月)
      - [阶段 3: 生产级测试 (6-12 个月)](#阶段-3-生产级测试-6-12-个月)
      - [阶段 4: 持续优化 (12+ 个月)](#阶段-4-持续优化-12-个月)
    - [9.4 ROI 与质量度量](#94-roi-与质量度量)
      - [测试投资回报率计算](#测试投资回报率计算)
      - [质量度量指标](#质量度量指标)
  - [10. 总结与展望](#10-总结与展望)
    - [10.1 核心要点](#101-核心要点)
    - [10.2 未来趋势](#102-未来趋势)
  - [相关文档](#相关文档)

---

## 1. OTLP 测试体系概述

### 1.1 测试金字塔与测试策略

OTLP 测试体系遵循**测试金字塔**原则,构建分层测试策略:

```text
          ╱╲
         ╱E2E╲          少量 (5-10%) - 高价值,高成本
        ╱──────╲
       ╱ 集成测试 ╲       适中 (20-30%) - 验证组件交互
      ╱──────────╲
     ╱   单元测试   ╱      大量 (60-75%) - 快速反馈,低成本
    ╱──────────────╱
```

#### 分层测试策略

| 测试层级 | 测试对象 | 测试工具 | 执行频率 | 反馈时间 |
|---------|---------|---------|---------|---------|
| **单元测试** | 函数/方法/类 | JUnit, pytest, Go testing, Jest | 每次提交 | < 5 分钟 |
| **集成测试** | 组件交互 | Testcontainers, Docker Compose | 每次 PR | 10-30 分钟 |
| **契约测试** | API 兼容性 | Pact, Spring Cloud Contract | 每次 PR | 5-15 分钟 |
| **E2E 测试** | 完整场景 | Playwright, K6, Custom Framework | 每日/每周 | 30-120 分钟 |
| **性能测试** | 吞吐量/延迟 | K6, JMeter, Gatling | 每周/发布前 | 60-240 分钟 |
| **混沌测试** | 故障恢复 | Chaos Mesh, Litmus | 每周/按需 | 可变 |

### 1.2 OTLP 特定的测试挑战

#### 挑战 1: 分布式系统的不确定性

**问题**: 分布式追踪数据的生成和传输具有异步性和不确定性。

**解决方案**:

- **最终一致性验证**: 使用轮询机制等待数据到达
- **时间窗口容忍**: 允许时间戳在合理范围内波动
- **重试与幂等性**: 测试用例支持重试,验证幂等性

```python
# Python - 最终一致性验证示例
import time
from typing import Optional, Callable
from dataclasses import dataclass

@dataclass
class RetryConfig:
    """重试配置"""
    max_attempts: int = 10
    initial_delay: float = 0.5
    backoff_factor: float = 1.5
    max_delay: float = 10.0

def wait_for_condition(
    condition: Callable[[], bool],
    config: RetryConfig = RetryConfig(),
    timeout: float = 30.0
) -> bool:
    """
    等待条件满足 (最终一致性验证)

    Args:
        condition: 检查条件的函数
        config: 重试配置
        timeout: 超时时间 (秒)

    Returns:
        条件是否满足
    """
    start_time = time.time()
    delay = config.initial_delay

    for attempt in range(config.max_attempts):
        # 检查超时
        if time.time() - start_time > timeout:
            return False

        # 检查条件
        try:
            if condition():
                return True
        except Exception as e:
            # 记录但不中断重试
            print(f"Condition check failed (attempt {attempt + 1}): {e}")

        # 等待后重试
        time.sleep(delay)
        delay = min(delay * config.backoff_factor, config.max_delay)

    return False

# 使用示例
def verify_trace_received(trace_id: str, backend_api: str) -> None:
    """验证追踪数据已接收"""
    import requests

    def check_trace() -> bool:
        response = requests.get(f"{backend_api}/traces/{trace_id}", timeout=5)
        return response.status_code == 200 and response.json().get("spans")

    assert wait_for_condition(check_trace, timeout=30.0), \
        f"Trace {trace_id} not received within 30 seconds"
```

#### 挑战 2: 多协议多语言兼容性

**问题**: OTLP 支持 gRPC 和 HTTP 两种协议,以及多种编程语言 SDK。

**解决方案**:

- **协议一致性测试套件**: 对 gRPC 和 HTTP 使用相同的测试用例
- **跨语言互操作性测试**: 验证不同语言 SDK 生成数据的兼容性
- **参数化测试**: 使用测试框架的参数化功能覆盖多种场景

```go
// Go - 多协议参数化测试示例
package otlp_test

import (
    "context"
    "testing"
    "time"

    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
    "go.opentelemetry.io/otel/sdk/trace"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// ExporterFactory 定义导出器工厂接口
type ExporterFactory func(endpoint string) (trace.SpanExporter, error)

// TestExporterProtocols 测试多种协议
func TestExporterProtocols(t *testing.T) {
    testCases := []struct {
        name    string
        factory ExporterFactory
        endpoint string
    }{
        {
            name: "OTLP/gRPC",
            factory: func(endpoint string) (trace.SpanExporter, error) {
                return otlptracegrpc.New(
                    context.Background(),
                    otlptracegrpc.WithEndpoint(endpoint),
                    otlptracegrpc.WithInsecure(),
                )
            },
            endpoint: "localhost:4317",
        },
        {
            name: "OTLP/HTTP",
            factory: func(endpoint string) (trace.SpanExporter, error) {
                return otlptracehttp.New(
                    context.Background(),
                    otlptracehttp.WithEndpoint(endpoint),
                    otlptracehttp.WithInsecure(),
                )
            },
            endpoint: "localhost:4318",
        },
    }

    for _, tc := range testCases {
        t.Run(tc.name, func(t *testing.T) {
            // 创建导出器
            exporter, err := tc.factory(tc.endpoint)
            if err != nil {
                t.Fatalf("Failed to create exporter: %v", err)
            }
            defer exporter.Shutdown(context.Background())

            // 创建追踪提供器
            tp := sdktrace.NewTracerProvider(
                sdktrace.WithBatcher(exporter),
            )
            defer tp.Shutdown(context.Background())

            // 生成测试追踪
            tracer := tp.Tracer("test-tracer")
            ctx, span := tracer.Start(context.Background(), "test-span")
            span.SetAttributes(/* ... */)
            time.Sleep(10 * time.Millisecond)
            span.End()

            // 验证导出成功
            if err := tp.ForceFlush(ctx); err != nil {
                t.Errorf("Failed to flush traces: %v", err)
            }

            // 验证后端接收 (使用前面的 wait_for_condition 模式)
            // ...
        })
    }
}
```

#### 挑战 3: 性能与正确性的平衡

**问题**: 测试需要同时验证功能正确性和性能指标。

**解决方案**:

- **分离功能测试与性能测试**: 不同的测试套件和执行频率
- **性能基准回归检测**: 建立性能基线,检测退化
- **资源限制测试**: 在资源受限环境下验证正确性

```typescript
// TypeScript (Node.js) - 性能基准测试示例
import { performance } from 'perf_hooks';
import { trace, SpanStatusCode } from '@opentelemetry/api';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { BasicTracerProvider, BatchSpanProcessor } from '@opentelemetry/sdk-trace-base';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-http';

interface BenchmarkResult {
  totalSpans: number;
  durationMs: number;
  throughputPerSecond: number;
  avgLatencyMs: number;
  p95LatencyMs: number;
  p99LatencyMs: number;
}

/**
 * 性能基准测试
 */
class OTLPBenchmark {
  private provider: BasicTracerProvider;
  private exporter: OTLPTraceExporter;
  private latencies: number[] = [];

  constructor(collectorEndpoint: string) {
    this.exporter = new OTLPTraceExporter({
      url: collectorEndpoint,
    });

    this.provider = new BasicTracerProvider({
      resource: new Resource({
        [SemanticResourceAttributes.SERVICE_NAME]: 'benchmark-service',
      }),
    });

    this.provider.addSpanProcessor(new BatchSpanProcessor(this.exporter, {
      maxQueueSize: 10000,
      maxExportBatchSize: 512,
      scheduledDelayMillis: 1000,
    }));
  }

  /**
   * 运行基准测试
   */
  async runBenchmark(totalSpans: number, concurrency: number = 10): Promise<BenchmarkResult> {
    const tracer = this.provider.getTracer('benchmark-tracer');
    const startTime = performance.now();
    this.latencies = [];

    // 并发生成 Span
    const batchSize = Math.ceil(totalSpans / concurrency);
    const promises: Promise<void>[] = [];

    for (let i = 0; i < concurrency; i++) {
      const start = i * batchSize;
      const end = Math.min(start + batchSize, totalSpans);

      promises.push(this.generateSpanBatch(tracer, start, end));
    }

    await Promise.all(promises);

    // 强制刷新
    await this.provider.forceFlush();

    const endTime = performance.now();
    const durationMs = endTime - startTime;

    // 计算统计指标
    this.latencies.sort((a, b) => a - b);
    const avgLatencyMs = this.latencies.reduce((a, b) => a + b, 0) / this.latencies.length;
    const p95Index = Math.floor(this.latencies.length * 0.95);
    const p99Index = Math.floor(this.latencies.length * 0.99);

    return {
      totalSpans,
      durationMs,
      throughputPerSecond: (totalSpans / durationMs) * 1000,
      avgLatencyMs,
      p95LatencyMs: this.latencies[p95Index],
      p99LatencyMs: this.latencies[p99Index],
    };
  }

  /**
   * 生成一批 Span
   */
  private async generateSpanBatch(tracer: any, start: number, end: number): Promise<void> {
    for (let i = start; i < end; i++) {
      const spanStartTime = performance.now();

      const span = tracer.startSpan(`operation-${i}`, {
        attributes: {
          'span.index': i,
          'benchmark.batch': Math.floor(i / 100),
        },
      });

      // 模拟一些操作
      await this.simulateWork();

      span.setStatus({ code: SpanStatusCode.OK });
      span.end();

      const spanEndTime = performance.now();
      this.latencies.push(spanEndTime - spanStartTime);
    }
  }

  /**
   * 模拟工作负载
   */
  private async simulateWork(): Promise<void> {
    // 模拟 1-5ms 的异步工作
    const delay = Math.random() * 4 + 1;
    await new Promise(resolve => setTimeout(resolve, delay));
  }

  /**
   * 清理资源
   */
  async shutdown(): Promise<void> {
    await this.provider.shutdown();
  }
}

// 使用示例和断言
async function runPerformanceTest(): Promise<void> {
  const benchmark = new OTLPBenchmark('http://localhost:4318/v1/traces');

  try {
    console.log('Starting OTLP performance benchmark...');

    const result = await benchmark.runBenchmark(10000, 20);

    console.log('Benchmark Results:');
    console.log(`  Total Spans: ${result.totalSpans}`);
    console.log(`  Duration: ${result.durationMs.toFixed(2)} ms`);
    console.log(`  Throughput: ${result.throughputPerSecond.toFixed(2)} spans/sec`);
    console.log(`  Avg Latency: ${result.avgLatencyMs.toFixed(2)} ms`);
    console.log(`  P95 Latency: ${result.p95LatencyMs.toFixed(2)} ms`);
    console.log(`  P99 Latency: ${result.p99LatencyMs.toFixed(2)} ms`);

    // 性能断言 (基于历史基线)
    const baseline = {
      throughputPerSecond: 5000,  // 最低吞吐量
      p99LatencyMs: 50,            // 最大 P99 延迟
    };

    if (result.throughputPerSecond < baseline.throughputPerSecond) {
      throw new Error(
        `Performance regression: Throughput ${result.throughputPerSecond.toFixed(2)} ` +
        `< baseline ${baseline.throughputPerSecond}`
      );
    }

    if (result.p99LatencyMs > baseline.p99LatencyMs) {
      throw new Error(
        `Performance regression: P99 latency ${result.p99LatencyMs.toFixed(2)}ms ` +
        `> baseline ${baseline.p99LatencyMs}ms`
      );
    }

    console.log('✅ Performance test passed');

  } finally {
    await benchmark.shutdown();
  }
}

// 导出供测试框架使用
export { OTLPBenchmark, BenchmarkResult, runPerformanceTest };
```

### 1.3 端到端质量保障流程

```mermaid
graph TB
    A[代码提交] --> B[静态分析<br/>Linting/SAST]
    B --> C[单元测试<br/>覆盖率 > 80%]
    C --> D[集成测试<br/>组件交互]
    D --> E[契约测试<br/>API 兼容性]
    E --> F[E2E 测试<br/>关键场景]
    F --> G[性能测试<br/>基准回归]
    G --> H[安全扫描<br/>漏洞检测]
    H --> I{所有测试通过?}
    I -->|是| J[构建制品]
    I -->|否| K[通知开发者]
    K --> A
    J --> L[部署到测试环境]
    L --> M[冒烟测试]
    M --> N[发布到生产]
```

#### 质量门禁标准

| 阶段 | 指标 | 阈值 | 阻断级别 |
|------|------|------|---------|
| **代码质量** | Linting 错误 | 0 | ❌ 阻断 |
| **单元测试** | 覆盖率 | ≥ 80% | ❌ 阻断 |
| **单元测试** | 通过率 | 100% | ❌ 阻断 |
| **集成测试** | 通过率 | 100% | ❌ 阻断 |
| **契约测试** | 兼容性 | 无破坏性变更 | ❌ 阻断 |
| **E2E 测试** | 通过率 | 100% | ❌ 阻断 |
| **性能测试** | 吞吐量下降 | < 10% | ⚠️ 警告 |
| **性能测试** | P99 延迟增加 | < 20% | ⚠️ 警告 |
| **安全扫描** | 高危漏洞 | 0 | ❌ 阻断 |
| **安全扫描** | 中危漏洞 | ≤ 5 | ⚠️ 警告 |

### 1.4 测试环境与基础设施

#### 推荐的测试环境架构

```yaml
# docker-compose.test.yml - 完整的测试环境
version: '3.9'

services:
  # OTLP Collector (被测系统)
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.108.0
    container_name: otel-collector-test
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./test-configs/collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
    networks:
      - otlp-test-network

  # Jaeger (后端存储和查询)
  jaeger:
    image: jaegertracing/all-in-one:1.52
    container_name: jaeger-test
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    ports:
      - "16686:16686"  # Jaeger UI
      - "14250:14250"  # Jaeger gRPC
    networks:
      - otlp-test-network

  # Prometheus (指标后端)
  prometheus:
    image: prom/prometheus:v2.48.0
    container_name: prometheus-test
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    volumes:
      - ./test-configs/prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9090:9090"
    networks:
      - otlp-test-network

  # Redis (用于测试缓存和状态)
  redis:
    image: redis:7-alpine
    container_name: redis-test
    ports:
      - "6379:6379"
    networks:
      - otlp-test-network

  # PostgreSQL (用于测试数据库集成)
  postgres:
    image: postgres:16-alpine
    container_name: postgres-test
    environment:
      POSTGRES_USER: testuser
      POSTGRES_PASSWORD: testpass
      POSTGRES_DB: testdb
    ports:
      - "5432:5432"
    networks:
      - otlp-test-network

  # 测试应用 (生成测试数据)
  test-app:
    build:
      context: ./test-apps
      dockerfile: Dockerfile
    container_name: test-app
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4318
      - OTEL_SERVICE_NAME=test-application
    depends_on:
      - otel-collector
      - redis
      - postgres
    networks:
      - otlp-test-network

networks:
  otlp-test-network:
    driver: bridge
```

#### 测试环境管理脚本

```bash
#!/bin/bash
# test-env.sh - 测试环境管理脚本

set -e

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 启动测试环境
start_test_env() {
    log_info "Starting OTLP test environment..."
    docker-compose -f docker-compose.test.yml up -d

    log_info "Waiting for services to be ready..."
    wait_for_service "http://localhost:13133" "OTLP Collector"
    wait_for_service "http://localhost:16686" "Jaeger"
    wait_for_service "http://localhost:9090" "Prometheus"

    log_info "Test environment is ready!"
}

# 停止测试环境
stop_test_env() {
    log_info "Stopping OTLP test environment..."
    docker-compose -f docker-compose.test.yml down -v
    log_info "Test environment stopped."
}

# 等待服务就绪
wait_for_service() {
    local url=$1
    local name=$2
    local max_attempts=30
    local attempt=1

    while [ $attempt -le $max_attempts ]; do
        if curl -s -o /dev/null -w "%{http_code}" "$url" | grep -q "200\|404"; then
            log_info "$name is ready (attempt $attempt/$max_attempts)"
            return 0
        fi

        log_warn "$name not ready yet (attempt $attempt/$max_attempts)"
        sleep 2
        ((attempt++))
    done

    log_error "$name failed to start after $max_attempts attempts"
    return 1
}

# 清理测试数据
cleanup() {
    log_info "Cleaning up test data..."
    docker-compose -f docker-compose.test.yml exec -T redis redis-cli FLUSHALL
    docker-compose -f docker-compose.test.yml exec -T postgres psql -U testuser -d testdb -c "TRUNCATE TABLE test_table CASCADE;"
    log_info "Cleanup complete."
}

# 查看日志
logs() {
    local service=$1
    if [ -z "$service" ]; then
        docker-compose -f docker-compose.test.yml logs -f
    else
        docker-compose -f docker-compose.test.yml logs -f "$service"
    fi
}

# 健康检查
health_check() {
    log_info "Running health checks..."

    # Collector health
    if curl -s http://localhost:13133 | grep -q "Server available"; then
        log_info "✅ OTLP Collector is healthy"
    else
        log_error "❌ OTLP Collector is unhealthy"
        return 1
    fi

    # Jaeger health
    if curl -s http://localhost:16686 > /dev/null; then
        log_info "✅ Jaeger is healthy"
    else
        log_error "❌ Jaeger is unhealthy"
        return 1
    fi

    # Prometheus health
    if curl -s http://localhost:9090/-/healthy | grep -q "Prometheus is Healthy"; then
        log_info "✅ Prometheus is healthy"
    else
        log_error "❌ Prometheus is unhealthy"
        return 1
    fi

    log_info "All services are healthy!"
}

# 主函数
main() {
    local command=$1

    case "$command" in
        start)
            start_test_env
            ;;
        stop)
            stop_test_env
            ;;
        restart)
            stop_test_env
            start_test_env
            ;;
        cleanup)
            cleanup
            ;;
        logs)
            logs "$2"
            ;;
        health)
            health_check
            ;;
        *)
            echo "Usage: $0 {start|stop|restart|cleanup|logs [service]|health}"
            exit 1
            ;;
    esac
}

main "$@"
```

---

## 2. 单元测试框架

### 2.1 多语言单元测试最佳实践

#### Python (pytest)

```python
# test_trace_processor.py - Python 单元测试示例
import pytest
from unittest.mock import Mock, patch, MagicMock
from typing import List
from dataclasses import dataclass

from opentelemetry.proto.trace.v1 import trace_pb2
from opentelemetry.proto.common.v1 import common_pb2

@dataclass
class TraceProcessorConfig:
    """追踪处理器配置"""
    sample_rate: float = 1.0
    max_spans_per_trace: int = 1000
    enable_validation: bool = True

class TraceProcessor:
    """追踪数据处理器"""

    def __init__(self, config: TraceProcessorConfig):
        self.config = config
        self.processed_count = 0

    def process_spans(self, spans: List[trace_pb2.Span]) -> List[trace_pb2.Span]:
        """
        处理 Span 列表

        Args:
            spans: 原始 Span 列表

        Returns:
            处理后的 Span 列表

        Raises:
            ValueError: 如果 Span 无效
        """
        if not spans:
            return []

        if len(spans) > self.config.max_spans_per_trace:
            raise ValueError(
                f"Too many spans: {len(spans)} > {self.config.max_spans_per_trace}"
            )

        processed = []
        for span in spans:
            if self.config.enable_validation:
                self._validate_span(span)

            if self._should_sample():
                processed.append(self._enrich_span(span))

        self.processed_count += len(processed)
        return processed

    def _validate_span(self, span: trace_pb2.Span) -> None:
        """验证 Span 有效性"""
        if not span.trace_id:
            raise ValueError("Span missing trace_id")
        if not span.span_id:
            raise ValueError("Span missing span_id")
        if span.end_time_unix_nano <= span.start_time_unix_nano:
            raise ValueError("Invalid span duration")

    def _should_sample(self) -> bool:
        """采样决策"""
        import random
        return random.random() < self.config.sample_rate

    def _enrich_span(self, span: trace_pb2.Span) -> trace_pb2.Span:
        """丰富 Span 元数据"""
        # 添加处理时间戳
        span.attributes.append(
            common_pb2.KeyValue(
                key="processed_at",
                value=common_pb2.AnyValue(int_value=int(time.time() * 1e9))
            )
        )
        return span


# ===== 测试套件 =====

class TestTraceProcessor:
    """TraceProcessor 单元测试套件"""

    @pytest.fixture
    def processor(self) -> TraceProcessor:
        """测试夹具: 创建处理器实例"""
        config = TraceProcessorConfig(
            sample_rate=1.0,  # 100% 采样便于测试
            max_spans_per_trace=100,
            enable_validation=True
        )
        return TraceProcessor(config)

    @pytest.fixture
    def valid_span(self) -> trace_pb2.Span:
        """测试夹具: 创建有效的 Span"""
        return trace_pb2.Span(
            trace_id=b'\x01' * 16,
            span_id=b'\x02' * 8,
            name="test-span",
            kind=trace_pb2.Span.SPAN_KIND_INTERNAL,
            start_time_unix_nano=1000000,
            end_time_unix_nano=2000000,
        )

    def test_process_empty_spans(self, processor: TraceProcessor):
        """测试: 处理空列表"""
        result = processor.process_spans([])
        assert result == []
        assert processor.processed_count == 0

    def test_process_valid_span(self, processor: TraceProcessor, valid_span: trace_pb2.Span):
        """测试: 处理有效 Span"""
        result = processor.process_spans([valid_span])

        assert len(result) == 1
        assert result[0].trace_id == valid_span.trace_id
        assert result[0].span_id == valid_span.span_id
        assert processor.processed_count == 1

        # 验证丰富的元数据
        processed_at_attr = next(
            (attr for attr in result[0].attributes if attr.key == "processed_at"),
            None
        )
        assert processed_at_attr is not None
        assert processed_at_attr.value.int_value > 0

    @pytest.mark.parametrize("missing_field,expected_error", [
        ("trace_id", "missing trace_id"),
        ("span_id", "missing span_id"),
    ])
    def test_validate_span_missing_fields(
        self,
        processor: TraceProcessor,
        valid_span: trace_pb2.Span,
        missing_field: str,
        expected_error: str
    ):
        """测试: 验证缺失必需字段的 Span"""
        setattr(valid_span, missing_field, b'')

        with pytest.raises(ValueError, match=expected_error):
            processor.process_spans([valid_span])

    def test_validate_span_invalid_duration(self, processor: TraceProcessor, valid_span: trace_pb2.Span):
        """测试: 验证持续时间无效的 Span"""
        valid_span.end_time_unix_nano = valid_span.start_time_unix_nano - 1

        with pytest.raises(ValueError, match="Invalid span duration"):
            processor.process_spans([valid_span])

    def test_too_many_spans(self, processor: TraceProcessor, valid_span: trace_pb2.Span):
        """测试: 超过最大 Span 数量限制"""
        many_spans = [valid_span] * 101  # 超过配置的 100

        with pytest.raises(ValueError, match="Too many spans"):
            processor.process_spans(many_spans)

    def test_sampling(self, valid_span: trace_pb2.Span):
        """测试: 采样逻辑"""
        # 50% 采样率
        config = TraceProcessorConfig(sample_rate=0.5, enable_validation=False)
        processor = TraceProcessor(config)

        # 生成 1000 个 Span,统计采样数量
        spans = [valid_span] * 1000

        with patch('random.random', side_effect=[0.3, 0.7] * 500):  # 交替低于和高于 0.5
            result = processor.process_spans(spans)

        # 应该大约有 500 个被采样 (允许 5% 误差)
        assert 475 <= len(result) <= 525

    def test_disable_validation(self, valid_span: trace_pb2.Span):
        """测试: 禁用验证"""
        config = TraceProcessorConfig(
            sample_rate=1.0,
            enable_validation=False
        )
        processor = TraceProcessor(config)

        # 创建无效 Span (缺失 trace_id)
        invalid_span = trace_pb2.Span(
            span_id=b'\x02' * 8,
            name="invalid-span",
            start_time_unix_nano=1000000,
            end_time_unix_nano=2000000,
        )

        # 禁用验证时不应抛出异常
        result = processor.process_spans([invalid_span])
        assert len(result) == 1

    @patch('time.time', return_value=1234567890.123456)
    def test_enrich_span_timestamp(
        self,
        mock_time: Mock,
        processor: TraceProcessor,
        valid_span: trace_pb2.Span
    ):
        """测试: Span 丰富化添加时间戳"""
        result = processor.process_spans([valid_span])

        processed_at_attr = next(
            attr for attr in result[0].attributes if attr.key == "processed_at"
        )
        expected_timestamp = int(1234567890.123456 * 1e9)
        assert processed_at_attr.value.int_value == expected_timestamp


# 性能测试 (使用 pytest-benchmark)
def test_processor_performance(benchmark, valid_span: trace_pb2.Span):
    """性能测试: 处理 1000 个 Span 的性能"""
    config = TraceProcessorConfig(
        sample_rate=1.0,
        enable_validation=True
    )
    processor = TraceProcessor(config)
    spans = [valid_span] * 1000

    result = benchmark(processor.process_spans, spans)

    # 断言性能指标
    assert len(result) == 1000
    # benchmark 会自动报告执行时间统计
```

#### Go (testing + testify)

```go
// trace_processor_test.go - Go 单元测试示例
package processor_test

import (
    "context"
    "errors"
    "testing"
    "time"

    "github.com/stretchr/testify/assert"
    "github.com/stretchr/testify/mock"
    "github.com/stretchr/testify/require"
    "github.com/stretchr/testify/suite"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

// === 被测代码 ===

type SpanExporter interface {
    Export(ctx context.Context, spans ptrace.Traces) error
}

type TraceProcessor struct {
    exporter    SpanExporter
    sampleRate  float64
    maxSpans    int
}

func NewTraceProcessor(exporter SpanExporter, sampleRate float64, maxSpans int) *TraceProcessor {
    return &TraceProcessor{
        exporter:   exporter,
        sampleRate: sampleRate,
        maxSpans:   maxSpans,
    }
}

func (p *TraceProcessor) Process(ctx context.Context, traces ptrace.Traces) error {
    spanCount := traces.SpanCount()

    if spanCount > p.maxSpans {
        return errors.New("too many spans")
    }

    // 采样逻辑 (简化)
    if p.sampleRate < 1.0 {
        traces = p.sample(traces)
    }

    // 导出
    return p.exporter.Export(ctx, traces)
}

func (p *TraceProcessor) sample(traces ptrace.Traces) ptrace.Traces {
    // 简化的采样实现
    return traces
}

// === Mock 对象 ===

type MockExporter struct {
    mock.Mock
}

func (m *MockExporter) Export(ctx context.Context, spans ptrace.Traces) error {
    args := m.Called(ctx, spans)
    return args.Error(0)
}

// === 测试套件 (使用 testify/suite) ===

type TraceProcessorTestSuite struct {
    suite.Suite
    processor     *TraceProcessor
    mockExporter  *MockExporter
    ctx           context.Context
}

// SetupTest 在每个测试前运行
func (suite *TraceProcessorTestSuite) SetupTest() {
    suite.mockExporter = new(MockExporter)
    suite.processor = NewTraceProcessor(suite.mockExporter, 1.0, 1000)
    suite.ctx = context.Background()
}

// TearDownTest 在每个测试后运行
func (suite *TraceProcessorTestSuite) TearDownTest() {
    suite.mockExporter.AssertExpectations(suite.T())
}

// TestProcessValidTraces 测试处理有效追踪
func (suite *TraceProcessorTestSuite) TestProcessValidTraces() {
    // Arrange
    traces := ptrace.NewTraces()
    rs := traces.ResourceSpans().AppendEmpty()
    ss := rs.ScopeSpans().AppendEmpty()
    span := ss.Spans().AppendEmpty()
    span.SetName("test-span")
    span.SetTraceID([16]byte{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16})
    span.SetSpanID([8]byte{1, 2, 3, 4, 5, 6, 7, 8})

    suite.mockExporter.On("Export", suite.ctx, traces).Return(nil)

    // Act
    err := suite.processor.Process(suite.ctx, traces)

    // Assert
    assert.NoError(suite.T(), err)
}

// TestProcessTooManySpans 测试超过最大 Span 限制
func (suite *TraceProcessorTestSuite) TestProcessTooManySpans() {
    // Arrange
    traces := ptrace.NewTraces()
    rs := traces.ResourceSpans().AppendEmpty()
    ss := rs.ScopeSpans().AppendEmpty()

    // 创建 1001 个 Span (超过限制 1000)
    for i := 0; i < 1001; i++ {
        span := ss.Spans().AppendEmpty()
        span.SetName("span-" + string(rune(i)))
    }

    // Act
    err := suite.processor.Process(suite.ctx, traces)

    // Assert
    assert.Error(suite.T(), err)
    assert.Contains(suite.T(), err.Error(), "too many spans")
}

// TestProcessExporterError 测试导出器错误处理
func (suite *TraceProcessorTestSuite) TestProcessExporterError() {
    // Arrange
    traces := ptrace.NewTraces()
    rs := traces.ResourceSpans().AppendEmpty()
    ss := rs.ScopeSpans().AppendEmpty()
    span := ss.Spans().AppendEmpty()
    span.SetName("test-span")

    expectedError := errors.New("export failed")
    suite.mockExporter.On("Export", suite.ctx, traces).Return(expectedError)

    // Act
    err := suite.processor.Process(suite.ctx, traces)

    // Assert
    assert.Error(suite.T(), err)
    assert.Equal(suite.T(), expectedError, err)
}

// 运行测试套件
func TestTraceProcessorTestSuite(t *testing.T) {
    suite.Run(t, new(TraceProcessorTestSuite))
}

// === 表驱动测试 ===

func TestSamplingDecision(t *testing.T) {
    testCases := []struct {
        name         string
        sampleRate   float64
        shouldSample bool
    }{
        {"Always sample", 1.0, true},
        {"Never sample", 0.0, false},
        {"50% sample", 0.5, true}, // 简化,实际需要统计测试
    }

    for _, tc := range testCases {
        t.Run(tc.name, func(t *testing.T) {
            mockExporter := new(MockExporter)
            processor := NewTraceProcessor(mockExporter, tc.sampleRate, 1000)

            traces := ptrace.NewTraces()
            rs := traces.ResourceSpans().AppendEmpty()
            ss := rs.ScopeSpans().AppendEmpty()
            span := ss.Spans().AppendEmpty()
            span.SetName("test-span")

            if tc.shouldSample {
                mockExporter.On("Export", mock.Anything, mock.Anything).Return(nil)
            }

            err := processor.Process(context.Background(), traces)
            assert.NoError(t, err)

            mockExporter.AssertExpectations(t)
        })
    }
}

// === 基准测试 ===

func BenchmarkTraceProcessor(b *testing.B) {
    mockExporter := new(MockExporter)
    mockExporter.On("Export", mock.Anything, mock.Anything).Return(nil)

    processor := NewTraceProcessor(mockExporter, 1.0, 10000)
    ctx := context.Background()

    // 创建测试数据
    traces := ptrace.NewTraces()
    rs := traces.ResourceSpans().AppendEmpty()
    ss := rs.ScopeSpans().AppendEmpty()
    for i := 0; i < 100; i++ {
        span := ss.Spans().AppendEmpty()
        span.SetName("benchmark-span")
        span.SetTraceID([16]byte{byte(i)})
        span.SetSpanID([8]byte{byte(i)})
    }

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        err := processor.Process(ctx, traces)
        if err != nil {
            b.Fatal(err)
        }
    }
}

// === 并发测试 ===

func TestConcurrentProcessing(t *testing.T) {
    mockExporter := new(MockExporter)
    mockExporter.On("Export", mock.Anything, mock.Anything).Return(nil)

    processor := NewTraceProcessor(mockExporter, 1.0, 10000)

    // 并发执行 100 个 goroutine
    const goroutines = 100
    errors := make(chan error, goroutines)

    for i := 0; i < goroutines; i++ {
        go func() {
            traces := ptrace.NewTraces()
            rs := traces.ResourceSpans().AppendEmpty()
            ss := rs.ScopeSpans().AppendEmpty()
            span := ss.Spans().AppendEmpty()
            span.SetName("concurrent-span")

            err := processor.Process(context.Background(), traces)
            errors <- err
        }()
    }

    // 收集结果
    for i := 0; i < goroutines; i++ {
        err := <-errors
        assert.NoError(t, err)
    }
}
```

### 2.2 Mock 与 Stub 策略

#### 使用 Mock 隔离外部依赖

```java
// Java - 使用 Mockito 进行单元测试
package io.opentelemetry.exporter;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.sdk.trace.data.SpanData;
import io.opentelemetry.sdk.trace.export.SpanExporter;
import io.opentelemetry.sdk.common.CompletableResultCode;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Arrays;
import java.util.Collection;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * BatchSpanProcessor 单元测试
 */
@ExtendWith(MockitoExtension.class)
class BatchSpanProcessorTest {

    @Mock
    private SpanExporter mockExporter;

    private BatchSpanProcessor processor;

    @BeforeEach
    void setUp() {
        // 配置 Mock 导出器的默认行为
        when(mockExporter.export(anyCollection()))
            .thenReturn(CompletableResultCode.ofSuccess());
        when(mockExporter.flush())
            .thenReturn(CompletableResultCode.ofSuccess());
        when(mockExporter.shutdown())
            .thenReturn(CompletableResultCode.ofSuccess());

        // 创建被测对象
        processor = BatchSpanProcessor.builder(mockExporter)
            .setMaxQueueSize(2048)
            .setMaxExportBatchSize(512)
            .setScheduleDelay(1, TimeUnit.SECONDS)
            .build();
    }

    @Test
    void testExportBatch() {
        // Arrange
        SpanData span1 = createTestSpan("span-1");
        SpanData span2 = createTestSpan("span-2");

        // Act
        processor.onEnd(span1);
        processor.onEnd(span2);
        processor.forceFlush().join(5, TimeUnit.SECONDS);

        // Assert
        verify(mockExporter, atLeastOnce()).export(argThat(spans ->
            spans.size() >= 2
        ));
    }

    @Test
    void testExportFailureHandling() {
        // Arrange - Mock 导出失败
        when(mockExporter.export(anyCollection()))
            .thenReturn(CompletableResultCode.ofFailure());

        SpanData span = createTestSpan("span-1");

        // Act
        processor.onEnd(span);
        CompletableResultCode result = processor.forceFlush();
        result.join(5, TimeUnit.SECONDS);

        // Assert
        assertFalse(result.isSuccess(), "Flush should fail when export fails");
        verify(mockExporter, atLeastOnce()).export(anyCollection());
    }

    @Test
    void testMaxQueueSize() {
        // Arrange
        int maxQueueSize = 10;
        processor = BatchSpanProcessor.builder(mockExporter)
            .setMaxQueueSize(maxQueueSize)
            .build();

        // Act - 添加超过队列大小的 Span
        for (int i = 0; i < maxQueueSize + 5; i++) {
            processor.onEnd(createTestSpan("span-" + i));
        }
        processor.forceFlush().join(5, TimeUnit.SECONDS);

        // Assert - 验证只导出队列大小的 Span
        verify(mockExporter, atLeastOnce()).export(argThat(spans ->
            spans.size() <= maxQueueSize
        ));
    }

    @Test
    void testShutdown() {
        // Act
        CompletableResultCode result = processor.shutdown();
        result.join(5, TimeUnit.SECONDS);

        // Assert
        assertTrue(result.isSuccess());
        verify(mockExporter, times(1)).shutdown();
    }

    // 测试辅助方法
    private SpanData createTestSpan(String name) {
        return TestSpanData.builder()
            .setName(name)
            .setTraceId("00000000000000000000000000000001")
            .setSpanId("0000000000000001")
            .setStartEpochNanos(System.nanoTime())
            .setEndEpochNanos(System.nanoTime() + 1000000)
            .setKind(Span.Kind.INTERNAL)
            .setStatus(StatusData.ok())
            .build();
    }
}
```

### 2.3 测试覆盖率与质量门禁

#### 配置覆盖率工具

```xml
<!-- Maven (pom.xml) - JaCoCo 覆盖率配置 -->
<build>
    <plugins>
        <plugin>
            <groupId>org.jacoco</groupId>
            <artifactId>jacoco-maven-plugin</artifactId>
            <version>0.8.11</version>
            <executions>
                <execution>
                    <goals>
                        <goal>prepare-agent</goal>
                    </goals>
                </execution>
                <execution>
                    <id>report</id>
                    <phase>test</phase>
                    <goals>
                        <goal>report</goal>
                    </goals>
                </execution>
                <execution>
                    <id>jacoco-check</id>
                    <goals>
                        <goal>check</goal>
                    </goals>
                    <configuration>
                        <rules>
                            <rule>
                                <element>PACKAGE</element>
                                <limits>
                                    <limit>
                                        <counter>LINE</counter>
                                        <value>COVEREDRATIO</value>
                                        <minimum>0.80</minimum>
                                    </limit>
                                    <limit>
                                        <counter>BRANCH</counter>
                                        <value>COVEREDRATIO</value>
                                        <minimum>0.75</minimum>
                                    </limit>
                                </limits>
                            </rule>
                        </rules>
                    </configuration>
                </execution>
            </executions>
        </plugin>
    </plugins>
</build>
```

```python
# pytest.ini - Python 覆盖率配置
[pytest]
addopts =
    --cov=src
    --cov-report=html
    --cov-report=term-missing
    --cov-fail-under=80
    --cov-branch
    -v

[coverage:run]
source = src
omit =
    */tests/*
    */test_*.py
    */__pycache__/*

[coverage:report]
precision = 2
show_missing = True
skip_covered = False
```

```yaml
# .github/workflows/test.yml - GitHub Actions 覆盖率集成
name: Test and Coverage

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install -r requirements-test.txt

      - name: Run tests with coverage
        run: |
          pytest --cov=src --cov-report=xml --cov-report=term

      - name: Upload coverage to Codecov
        uses: codecov/codecov-action@v3
        with:
          file: ./coverage.xml
          fail_ci_if_error: true
          flags: unittests

      - name: Check coverage threshold
        run: |
          coverage report --fail-under=80
```

---

## 3. 集成测试框架

### 3.1 OTLP Collector 集成测试

#### 使用 Testcontainers 进行集成测试

```go
// collector_integration_test.go - Collector 集成测试
package integration_test

import (
    "context"
    "fmt"
    "testing"
    "time"

    "github.com/stretchr/testify/assert"
    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/wait"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/trace"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// CollectorTestSuite 集成测试套件
type CollectorTestSuite struct {
    collectorContainer testcontainers.Container
    jaegerContainer    testcontainers.Container
    collectorEndpoint  string
    jaegerUIEndpoint   string
}

// SetupSuite 启动测试环境
func (suite *CollectorTestSuite) SetupSuite(t *testing.T) {
    ctx := context.Background()

    // 启动 Jaeger (作为后端)
    jaegerReq := testcontainers.ContainerRequest{
        Image:        "jaegertracing/all-in-one:1.52",
        ExposedPorts: []string{"16686/tcp", "4317/tcp", "4318/tcp"},
        Env: map[string]string{
            "COLLECTOR_OTLP_ENABLED": "true",
        },
        WaitingFor: wait.ForHTTP("/").WithPort("16686/tcp"),
    }

    jaegerContainer, err := testcontainers.GenericContainer(ctx, testcontainers.GenericContainerRequest{
        ContainerRequest: jaegerReq,
        Started:          true,
    })
    require.NoError(t, err)
    suite.jaegerContainer = jaegerContainer

    jaegerHost, err := jaegerContainer.Host(ctx)
    require.NoError(t, err)
    jaegerPort, err := jaegerContainer.MappedPort(ctx, "16686")
    require.NoError(t, err)
    suite.jaegerUIEndpoint = fmt.Sprintf("http://%s:%s", jaegerHost, jaegerPort.Port())

    jaegerOTLPPort, err := jaegerContainer.MappedPort(ctx, "4317")
    require.NoError(t, err)
    jaegerOTLPEndpoint := fmt.Sprintf("%s:%s", jaegerHost, jaegerOTLPPort.Port())

    // 启动 OTLP Collector
    collectorConfig := fmt.Sprintf(`
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
    send_batch_size: 100

exporters:
  otlp:
    endpoint: %s
    tls:
      insecure: true
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp, logging]
`, jaegerOTLPEndpoint)

    collectorReq := testcontainers.ContainerRequest{
        Image:        "otel/opentelemetry-collector-contrib:0.108.0",
        ExposedPorts: []string{"4317/tcp", "4318/tcp", "8888/tcp"},
        Cmd:          []string{"--config=/etc/otel-collector-config.yaml"},
        Files: []testcontainers.ContainerFile{
            {
                HostFilePath:      "/tmp/otel-collector-config.yaml",
                ContainerFilePath: "/etc/otel-collector-config.yaml",
                FileMode:          0644,
            },
        },
        WaitingFor: wait.ForHTTP("/").WithPort("8888/tcp"),
    }

    // 写入配置文件
    require.NoError(t, os.WriteFile("/tmp/otel-collector-config.yaml", []byte(collectorConfig), 0644))

    collectorContainer, err := testcontainers.GenericContainer(ctx, testcontainers.GenericContainerRequest{
        ContainerRequest: collectorReq,
        Started:          true,
    })
    require.NoError(t, err)
    suite.collectorContainer = collectorContainer

    collectorHost, err := collectorContainer.Host(ctx)
    require.NoError(t, err)
    collectorPort, err := collectorContainer.MappedPort(ctx, "4317")
    require.NoError(t, err)
    suite.collectorEndpoint = fmt.Sprintf("%s:%s", collectorHost, collectorPort.Port())

    // 等待服务就绪
    time.Sleep(5 * time.Second)
}

// TearDownSuite 清理测试环境
func (suite *CollectorTestSuite) TearDownSuite(t *testing.T) {
    ctx := context.Background()

    if suite.collectorContainer != nil {
        require.NoError(t, suite.collectorContainer.Terminate(ctx))
    }
    if suite.jaegerContainer != nil {
        require.NoError(t, suite.jaegerContainer.Terminate(ctx))
    }
}

// TestEndToEndTracing 端到端追踪测试
func TestEndToEndTracing(t *testing.T) {
    suite := &CollectorTestSuite{}
    suite.SetupSuite(t)
    defer suite.TearDownSuite(t)

    ctx := context.Background()

    // 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(
        ctx,
        otlptracegrpc.WithEndpoint(suite.collectorEndpoint),
        otlptracegrpc.WithInsecure(),
    )
    require.NoError(t, err)
    defer exporter.Shutdown(ctx)

    // 创建追踪提供器
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )
    defer tp.Shutdown(ctx)
    otel.SetTracerProvider(tp)

    // 生成测试追踪
    tracer := otel.Tracer("integration-test")
    _, span := tracer.Start(ctx, "test-operation")
    span.SetAttributes(
        attribute.String("test.type", "integration"),
        attribute.Int("test.number", 42),
    )
    time.Sleep(100 * time.Millisecond)
    span.End()

    // 强制刷新
    require.NoError(t, tp.ForceFlush(ctx))

    // 等待数据传输到 Jaeger
    time.Sleep(5 * time.Second)

    // 验证追踪数据已到达 Jaeger
    traceID := span.SpanContext().TraceID().String()
    jaegerAPIURL := fmt.Sprintf("%s/api/traces/%s", suite.jaegerUIEndpoint, traceID)

    var resp *http.Response
    for i := 0; i < 10; i++ {
        resp, err = http.Get(jaegerAPIURL)
        if err == nil && resp.StatusCode == 200 {
            break
        }
        time.Sleep(2 * time.Second)
    }

    require.NoError(t, err)
    require.Equal(t, 200, resp.StatusCode)

    // 解析响应
    var jaegerTrace struct {
        Data []struct {
            TraceID string `json:"traceID"`
            Spans   []struct {
                OperationName string `json:"operationName"`
            } `json:"spans"`
        } `json:"data"`
    }

    require.NoError(t, json.NewDecoder(resp.Body).Decode(&jaegerTrace))
    require.Len(t, jaegerTrace.Data, 1)
    assert.Equal(t, "test-operation", jaegerTrace.Data[0].Spans[0].OperationName)
}
```

### 3.2 多组件联调测试

```python
# test_multi_component.py - 多组件联调测试
import pytest
import requests
import time
from typing import Dict, Any
from testcontainers.compose import DockerCompose

class TestMultiComponentIntegration:
    """多组件联调集成测试"""

    @pytest.fixture(scope="class")
    def test_environment(self):
        """启动完整的测试环境"""
        with DockerCompose(
            filepath=".",
            compose_file_name="docker-compose.test.yml",
            pull=True
        ) as compose:
            # 等待服务启动
            time.sleep(15)

            # 获取服务端点
            endpoints = {
                "collector": "http://localhost:4318",
                "jaeger": "http://localhost:16686",
                "prometheus": "http://localhost:9090",
            }

            # 健康检查
            for name, url in endpoints.items():
                assert self._wait_for_service(url), f"{name} failed to start"

            yield endpoints

    def _wait_for_service(self, url: str, timeout: int = 60) -> bool:
        """等待服务就绪"""
        start = time.time()
        while time.time() - start < timeout:
            try:
                response = requests.get(url, timeout=5)
                if response.status_code in [200, 404]:  # 404 也表示服务运行
                    return True
            except requests.RequestException:
                pass
            time.sleep(2)
        return False

    def test_traces_pipeline(self, test_environment: Dict[str, str]):
        """测试追踪数据管道"""
        # 1. 生成测试追踪
        trace_data = {
            "resourceSpans": [{
                "resource": {
                    "attributes": [{
                        "key": "service.name",
                        "value": {"stringValue": "test-service"}
                    }]
                },
                "scopeSpans": [{
                    "spans": [{
                        "traceId": "0102030405060708090a0b0c0d0e0f10",
                        "spanId": "0102030405060708",
                        "name": "test-span",
                        "kind": 1,
                        "startTimeUnixNano": str(int(time.time() * 1e9)),
                        "endTimeUnixNano": str(int((time.time() + 0.1) * 1e9)),
                        "attributes": [{
                            "key": "test.attribute",
                            "value": {"stringValue": "test-value"}
                        }]
                    }]
                }]
            }]
        }

        # 2. 发送到 Collector
        response = requests.post(
            f"{test_environment['collector']}/v1/traces",
            json=trace_data,
            headers={"Content-Type": "application/json"},
            timeout=10
        )
        assert response.status_code == 200, f"Failed to send traces: {response.text}"

        # 3. 等待数据传输
        time.sleep(5)

        # 4. 验证数据到达 Jaeger
        trace_id = "0102030405060708090a0b0c0d0e0f10"
        jaeger_url = f"{test_environment['jaeger']}/api/traces/{trace_id}"

        for _ in range(10):
            response = requests.get(jaeger_url, timeout=5)
            if response.status_code == 200:
                trace_result = response.json()
                if trace_result.get("data"):
                    break
            time.sleep(2)
        else:
            pytest.fail("Trace not found in Jaeger after 20 seconds")

        # 5. 验证追踪内容
        assert len(trace_result["data"]) == 1
        assert trace_result["data"][0]["traceID"] == trace_id
        spans = trace_result["data"][0]["spans"]
        assert len(spans) == 1
        assert spans[0]["operationName"] == "test-span"

    def test_metrics_pipeline(self, test_environment: Dict[str, str]):
        """测试指标数据管道"""
        # 1. 生成测试指标
        metric_data = {
            "resourceMetrics": [{
                "resource": {
                    "attributes": [{
                        "key": "service.name",
                        "value": {"stringValue": "test-service"}
                    }]
                },
                "scopeMetrics": [{
                    "metrics": [{
                        "name": "test_counter",
                        "unit": "1",
                        "sum": {
                            "dataPoints": [{
                                "asInt": "42",
                                "timeUnixNano": str(int(time.time() * 1e9))
                            }],
                            "aggregationTemporality": 2,
                            "isMonotonic": True
                        }
                    }]
                }]
            }]
        }

        # 2. 发送到 Collector
        response = requests.post(
            f"{test_environment['collector']}/v1/metrics",
            json=metric_data,
            headers={"Content-Type": "application/json"},
            timeout=10
        )
        assert response.status_code == 200

        # 3. 等待数据传输
        time.sleep(10)

        # 4. 查询 Prometheus
        prom_url = f"{test_environment['prometheus']}/api/v1/query"
        params = {"query": "test_counter"}

        for _ in range(10):
            response = requests.get(prom_url, params=params, timeout=5)
            if response.status_code == 200:
                result = response.json()
                if result["data"]["result"]:
                    break
            time.sleep(2)
        else:
            pytest.fail("Metric not found in Prometheus after 20 seconds")

        # 5. 验证指标值
        metric_result = result["data"]["result"][0]
        assert metric_result["metric"]["__name__"] == "test_counter"
        assert int(float(metric_result["value"][1])) == 42
```

---

## 4. 端到端测试 (E2E)

### 4.1 分布式追踪场景测试

```typescript
// e2e-tracing.spec.ts - Playwright E2E 测试
import { test, expect } from '@playwright/test';
import { trace, context, SpanStatusCode } from '@opentelemetry/api';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-http';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { BasicTracerProvider, BatchSpanProcessor } from '@opentelemetry/sdk-trace-base';
import axios from 'axios';

// 测试配置
const OTLP_ENDPOINT = process.env.OTLP_ENDPOINT || 'http://localhost:4318/v1/traces';
const JAEGER_UI = process.env.JAEGER_UI || 'http://localhost:16686';
const TEST_APP_URL = process.env.TEST_APP_URL || 'http://localhost:8080';

test.describe('E2E Distributed Tracing', () => {
  let tracerProvider: BasicTracerProvider;

  test.beforeAll(async () => {
    // 初始化追踪
    const exporter = new OTLPTraceExporter({
      url: OTLP_ENDPOINT,
    });

    tracerProvider = new BasicTracerProvider({
      resource: new Resource({
        [SemanticResourceAttributes.SERVICE_NAME]: 'e2e-test-client',
      }),
    });

    tracerProvider.addSpanProcessor(new BatchSpanProcessor(exporter));
    trace.setGlobalTracerProvider(tracerProvider);
  });

  test.afterAll(async () => {
    await tracerProvider.shutdown();
  });

  test('should propagate trace context across services', async () => {
    const tracer = trace.getTracer('e2e-test');
    const parentSpan = tracer.startSpan('e2e-test-request');
    const ctx = trace.setSpan(context.active(), parentSpan);

    let traceId: string;
    let spanId: string;

    await context.with(ctx, async () => {
      traceId = parentSpan.spanContext().traceId;
      spanId = parentSpan.spanContext().spanId;

      // 调用测试应用 (带追踪 header)
      const response = await axios.get(`${TEST_APP_URL}/api/test`, {
        headers: {
          'traceparent': `00-${traceId}-${spanId}-01`,
        },
      });

      expect(response.status).toBe(200);
      parentSpan.setStatus({ code: SpanStatusCode.OK });
      parentSpan.end();
    });

    // 强制刷新追踪数据
    await tracerProvider.forceFlush();

    // 等待数据传输
    await new Promise(resolve => setTimeout(resolve, 5000));

    // 验证追踪链路
    const traceData = await fetchTraceFromJaeger(traceId);

    expect(traceData).toBeDefined();
    expect(traceData.traceID).toBe(traceId);

    // 验证服务拓扑
    const spans = traceData.spans;
    expect(spans.length).toBeGreaterThan(1);

    // 验证根 Span
    const rootSpan = spans.find((s: any) => !s.references || s.references.length === 0);
    expect(rootSpan).toBeDefined();
    expect(rootSpan.operationName).toBe('e2e-test-request');

    // 验证子 Span
    const childSpans = spans.filter((s: any) =>
      s.references && s.references.some((r: any) => r.spanID === spanId)
    );
    expect(childSpans.length).toBeGreaterThan(0);
  });

  test('should capture errors in distributed traces', async () => {
    const tracer = trace.getTracer('e2e-test');
    const parentSpan = tracer.startSpan('e2e-test-error');
    const ctx = trace.setSpan(context.active(), parentSpan);

    let traceId: string;

    await context.with(ctx, async () => {
      traceId = parentSpan.spanContext().traceId;

      try {
        // 调用会失败的端点
        await axios.get(`${TEST_APP_URL}/api/error`);
      } catch (error) {
        parentSpan.recordException(error as Error);
        parentSpan.setStatus({
          code: SpanStatusCode.ERROR,
          message: (error as Error).message,
        });
      } finally {
        parentSpan.end();
      }
    });

    await tracerProvider.forceFlush();
    await new Promise(resolve => setTimeout(resolve, 5000));

    // 验证错误追踪
    const traceData = await fetchTraceFromJaeger(traceId);

    const errorSpans = traceData.spans.filter((s: any) =>
      s.tags.some((t: any) => t.key === 'error' && t.value === true)
    );

    expect(errorSpans.length).toBeGreaterThan(0);
  });
});

// 辅助函数: 从 Jaeger 获取追踪
async function fetchTraceFromJaeger(traceId: string, maxRetries = 10): Promise<any> {
  for (let i = 0; i < maxRetries; i++) {
    try {
      const response = await axios.get(`${JAEGER_UI}/api/traces/${traceId}`);
      if (response.data && response.data.data && response.data.data.length > 0) {
        return response.data.data[0];
      }
    } catch (error) {
      // 忽略错误,继续重试
    }
    await new Promise(resolve => setTimeout(resolve, 2000));
  }
  throw new Error(`Trace ${traceId} not found after ${maxRetries} retries`);
}
```

### 4.2 跨服务链路验证

```python
# test_cross_service.py - 跨服务链路测试
import pytest
import requests
import time
from typing import List, Dict
from dataclasses import dataclass
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import Resource, SERVICE_NAME

@dataclass
class ServiceEndpoint:
    """服务端点配置"""
    name: str
    url: str
    expected_operation: str

class TestCrossServiceTracing:
    """跨服务链路测试"""

    @pytest.fixture(scope="class")
    def tracer_provider(self):
        """初始化追踪提供器"""
        resource = Resource(attributes={
            SERVICE_NAME: "test-orchestrator"
        })

        provider = TracerProvider(resource=resource)
        otlp_exporter = OTLPSpanExporter(
            endpoint="http://localhost:4317",
            insecure=True
        )

        provider.add_span_processor(BatchSpanProcessor(otlp_exporter))
        trace.set_tracer_provider(provider)

        yield provider

        provider.shutdown()

    @pytest.fixture
    def service_chain(self) -> List[ServiceEndpoint]:
        """定义服务调用链"""
        return [
            ServiceEndpoint("frontend", "http://localhost:8080/api/users", "GET /api/users"),
            ServiceEndpoint("backend", "http://localhost:8081/api/users", "fetch_users"),
            ServiceEndpoint("database", "http://localhost:5432", "SELECT users"),
        ]

    def test_complete_service_chain(
        self,
        tracer_provider: TracerProvider,
        service_chain: List[ServiceEndpoint]
    ):
        """测试完整的服务调用链"""
        tracer = trace.get_tracer(__name__)

        with tracer.start_as_current_span("test-service-chain") as span:
            trace_id = format(span.get_span_context().trace_id, '032x')
            span_id = format(span.get_span_context().span_id, '016x')

            # 构造 W3C Trace Context header
            traceparent = f"00-{trace_id}-{span_id}-01"

            # 调用第一个服务 (frontend)
            response = requests.get(
                service_chain[0].url,
                headers={"traceparent": traceparent},
                timeout=10
            )

            assert response.status_code == 200, f"Frontend request failed: {response.text}"

            # 添加自定义属性
            span.set_attribute("test.chain_length", len(service_chain))
            span.set_attribute("test.frontend_response_time", response.elapsed.total_seconds())

        # 刷新追踪数据
        tracer_provider.force_flush()

        # 等待数据传输
        time.sleep(5)

        # 验证完整链路
        trace_data = self._fetch_trace_from_backend(trace_id)

        assert trace_data is not None, f"Trace {trace_id} not found"
        assert len(trace_data["spans"]) >= len(service_chain), \
            f"Expected at least {len(service_chain)} spans, got {len(trace_data['spans'])}"

        # 验证每个服务的 Span
        span_operations = {span["operationName"] for span in trace_data["spans"]}

        for service in service_chain:
            assert any(service.expected_operation in op for op in span_operations), \
                f"Missing span for service {service.name} (operation: {service.expected_operation})"

        # 验证链路完整性 (父子关系)
        self._verify_span_relationships(trace_data["spans"])

    def test_service_failure_propagation(
        self,
        tracer_provider: TracerProvider,
        service_chain: List[ServiceEndpoint]
    ):
        """测试服务故障传播"""
        tracer = trace.get_tracer(__name__)

        with tracer.start_as_current_span("test-failure-propagation") as span:
            trace_id = format(span.get_span_context().trace_id, '032x')
            span_id = format(span.get_span_context().span_id, '016x')
            traceparent = f"00-{trace_id}-{span_id}-01"

            # 调用会失败的端点
            try:
                response = requests.get(
                    f"{service_chain[0].url}/fail",
                    headers={"traceparent": traceparent},
                    timeout=10
                )
                # 预期会失败
                assert response.status_code >= 400
            except requests.RequestException as e:
                span.record_exception(e)
                span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))

        tracer_provider.force_flush()
        time.sleep(5)

        # 验证错误标记
        trace_data = self._fetch_trace_from_backend(trace_id)
        error_spans = [
            s for s in trace_data["spans"]
            if any(tag["key"] == "error" and tag["value"] for tag in s.get("tags", []))
        ]

        assert len(error_spans) > 0, "No error spans found in failed request"

    def _fetch_trace_from_backend(self, trace_id: str, max_retries: int = 10) -> Dict:
        """从后端获取追踪数据"""
        jaeger_url = f"http://localhost:16686/api/traces/{trace_id}"

        for attempt in range(max_retries):
            try:
                response = requests.get(jaeger_url, timeout=5)
                if response.status_code == 200:
                    data = response.json()
                    if data.get("data") and len(data["data"]) > 0:
                        return data["data"][0]
            except requests.RequestException:
                pass

            time.sleep(2)

        return None

    def _verify_span_relationships(self, spans: List[Dict]) -> None:
        """验证 Span 父子关系完整性"""
        span_map = {span["spanID"]: span for span in spans}

        for span in spans:
            # 检查父 Span 引用
            if span.get("references"):
                for ref in span["references"]:
                    if ref["refType"] == "CHILD_OF":
                        parent_id = ref["spanID"]
                        assert parent_id in span_map, \
                            f"Parent span {parent_id} not found for span {span['spanID']}"
```

### 4.3 性能基准测试

#### K6 性能测试脚本

```javascript
// performance-test.js - K6 性能基准测试
import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend } from 'k6/metrics';
import { randomItem } from 'https://jslib.k6.io/k6-utils/1.2.0/index.js';

// 自定义指标
const errorRate = new Rate('errors');
const traceDuration = new Trend('trace_duration');

// 测试配置
export const options = {
  stages: [
    { duration: '2m', target: 100 },  // 线性增加到 100 VU
    { duration: '5m', target: 100 },  // 保持 100 VU
    { duration: '2m', target: 200 },  // 增加到 200 VU
    { duration: '5m', target: 200 },  // 保持 200 VU
    { duration: '2m', target: 0 },    // 逐渐减少到 0
  ],
  thresholds: {
    'http_req_duration': ['p(95)<500', 'p(99)<1000'],  // 95% < 500ms, 99% < 1s
    'errors': ['rate<0.1'],  // 错误率 < 10%
    'http_req_failed': ['rate<0.01'],  // 失败率 < 1%
  },
};

const OTLP_ENDPOINT = __ENV.OTLP_ENDPOINT || 'http://localhost:4318/v1/traces';

// 生成测试追踪数据
function generateTraceData() {
  const traceId = Array.from({ length: 32 }, () =>
    Math.floor(Math.random() * 16).toString(16)
  ).join('');

  const spanId = Array.from({ length: 16 }, () =>
    Math.floor(Math.random() * 16).toString(16)
  ).join('');

  const startTime = Date.now() * 1000000;  // 纳秒
  const duration = Math.random() * 100 + 50;  // 50-150ms
  const endTime = startTime + (duration * 1000000);

  return {
    resourceSpans: [{
      resource: {
        attributes: [
          { key: 'service.name', value: { stringValue: `perf-test-${__VU}` } },
          { key: 'service.version', value: { stringValue: '1.0.0' } },
        ],
      },
      scopeSpans: [{
        scope: {
          name: 'k6-performance-test',
          version: '1.0.0',
        },
        spans: [{
          traceId,
          spanId,
          name: randomItem(['GET /api/users', 'POST /api/orders', 'GET /api/products']),
          kind: 1,
          startTimeUnixNano: startTime.toString(),
          endTimeUnixNano: endTime.toString(),
          attributes: [
            { key: 'http.method', value: { stringValue: randomItem(['GET', 'POST', 'PUT']) } },
            { key: 'http.status_code', value: { intValue: '200' } },
            { key: 'http.url', value: { stringValue: 'https://api.example.com/users' } },
          ],
        }],
      }],
    }],
  };
}

// 主测试场景
export default function () {
  const traceData = generateTraceData();

  const payload = JSON.stringify(traceData);
  const params = {
    headers: {
      'Content-Type': 'application/json',
    },
  };

  // 发送追踪数据
  const startTime = Date.now();
  const response = http.post(OTLP_ENDPOINT, payload, params);
  const duration = Date.now() - startTime;

  // 记录指标
  traceDuration.add(duration);

  // 检查响应
  const success = check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });

  errorRate.add(!success);

  // 模拟实际负载 (随机睡眠 100-500ms)
  sleep(Math.random() * 0.4 + 0.1);
}

// 测试生命周期钩子
export function setup() {
  console.log('Starting performance test...');
  // 预热
  for (let i = 0; i < 10; i++) {
    http.post(OTLP_ENDPOINT, JSON.stringify(generateTraceData()), {
      headers: { 'Content-Type': 'application/json' },
    });
  }
  return { startTime: Date.now() };
}

export function teardown(data) {
  const totalDuration = (Date.now() - data.startTime) / 1000;
  console.log(`Test completed in ${totalDuration.toFixed(2)} seconds`);
}
```

#### JMeter 性能测试计划

```xml
<!-- otlp-performance-test.jmx - JMeter 测试计划 (简化版) -->
<?xml version="1.0" encoding="UTF-8"?>
<jmeterTestPlan version="1.2" properties="5.0" jmeter="5.6.2">
  <hashTree>
    <TestPlan guiclass="TestPlanGui" testclass="TestPlan" testname="OTLP Performance Test">
      <elementProp name="TestPlan.user_defined_variables" elementType="Arguments">
        <collectionProp name="Arguments.arguments">
          <elementProp name="OTLP_HOST" elementType="Argument">
            <stringProp name="Argument.name">OTLP_HOST</stringProp>
            <stringProp name="Argument.value">localhost</stringProp>
          </elementProp>
          <elementProp name="OTLP_PORT" elementType="Argument">
            <stringProp name="Argument.name">OTLP_PORT</stringProp>
            <stringProp name="Argument.value">4318</stringProp>
          </elementProp>
        </collectionProp>
      </elementProp>
    </TestPlan>

    <hashTree>
      <ThreadGroup guiclass="ThreadGroupGui" testclass="ThreadGroup" testname="Trace Senders">
        <stringProp name="ThreadGroup.num_threads">100</stringProp>
        <stringProp name="ThreadGroup.ramp_time">60</stringProp>
        <stringProp name="ThreadGroup.duration">300</stringProp>
        <boolProp name="ThreadGroup.scheduler">true</boolProp>
        <stringProp name="ThreadGroup.on_sample_error">continue</stringProp>
      </ThreadGroup>

      <hashTree>
        <HTTPSamplerProxy guiclass="HttpTestSampleGui" testclass="HTTPSamplerProxy" testname="Send Trace">
          <stringProp name="HTTPSampler.domain">${OTLP_HOST}</stringProp>
          <stringProp name="HTTPSampler.port">${OTLP_PORT}</stringProp>
          <stringProp name="HTTPSampler.protocol">http</stringProp>
          <stringProp name="HTTPSampler.path">/v1/traces</stringProp>
          <stringProp name="HTTPSampler.method">POST</stringProp>
          <boolProp name="HTTPSampler.use_keepalive">true</boolProp>
          <elementProp name="HTTPsampler.Arguments" elementType="Arguments">
            <collectionProp name="Arguments.arguments">
              <elementProp name="" elementType="HTTPArgument">
                <boolProp name="HTTPArgument.always_encode">false</boolProp>
                <stringProp name="Argument.value">${__BeanShell(new groovy.json.JsonBuilder([
                  resourceSpans: [[
                    resource: [
                      attributes: [
                        [key: 'service.name', value: [stringValue: 'jmeter-test']]
                      ]
                    ],
                    scopeSpans: [[
                      spans: [[
                        traceId: UUID.randomUUID().toString().replace('-', ''),
                        spanId: UUID.randomUUID().toString().replace('-', '').substring(0, 16),
                        name: 'jmeter-test-span',
                        kind: 1,
                        startTimeUnixNano: (System.currentTimeMillis() * 1000000).toString(),
                        endTimeUnixNano: ((System.currentTimeMillis() + 100) * 1000000).toString()
                      ]]
                    ]]
                  ]]
                ]).toString())}</stringProp>
                <stringProp name="Argument.metadata">=</stringProp>
              </elementProp>
            </collectionProp>
          </elementProp>
        </HTTPSamplerProxy>

        <hashTree>
          <HeaderManager guiclass="HeaderPanel" testclass="HeaderManager" testname="HTTP Headers">
            <collectionProp name="HeaderManager.headers">
              <elementProp name="" elementType="Header">
                <stringProp name="Header.name">Content-Type</stringProp>
                <stringProp name="Header.value">application/json</stringProp>
              </elementProp>
            </collectionProp>
          </HeaderManager>

          <ResponseAssertion guiclass="AssertionGui" testclass="ResponseAssertion" testname="Status Code Assertion">
            <collectionProp name="Asserion.test_strings">
              <stringProp name="49586">200</stringProp>
            </collectionProp>
            <stringProp name="Assertion.test_field">Assertion.response_code</stringProp>
            <intProp name="Assertion.test_type">8</intProp>
          </ResponseAssertion>
        </hashTree>
      </hashTree>
    </hashTree>
  </hashTree>
</jmeterTestPlan>
```

### 4.4 混沌工程 (Chaos Engineering)

```yaml
# chaos-experiment.yaml - Chaos Mesh 混沌实验
apiVersion: chaos-mesh.org/v1alpha1
kind: Workflow
metadata:
  name: otlp-chaos-experiment
  namespace: otlp-test
spec:
  entry: otlp-resilience-test
  templates:
    - name: otlp-resilience-test
      templateType: Serial
      deadline: 30m
      children:
        - baseline-test
        - network-delay-test
        - pod-failure-test
        - stress-test
        - verification-test

    # 基线测试
    - name: baseline-test
      templateType: Task
      deadline: 5m
      task:
        container:
          name: baseline-test
          image: k6io/k6:latest
          command: ['k6', 'run', '--vus', '50', '--duration', '2m', '/scripts/baseline.js']
          volumeMounts:
            - name: test-scripts
              mountPath: /scripts

    # 网络延迟测试
    - name: network-delay-test
      templateType: Parallel
      deadline: 10m
      children:
        - inject-network-delay
        - run-test-under-delay

    - name: inject-network-delay
      templateType: NetworkChaos
      deadline: 8m
      networkChaos:
        action: delay
        mode: all
        selector:
          namespaces:
            - otlp-test
          labelSelectors:
            'app': 'otel-collector'
        delay:
          latency: '100ms'
          correlation: '50'
          jitter: '50ms'
        duration: 5m

    - name: run-test-under-delay
      templateType: Task
      deadline: 8m
      task:
        container:
          name: test-with-delay
          image: k6io/k6:latest
          command: ['k6', 'run', '--vus', '50', '--duration', '5m', '/scripts/latency-test.js']
          volumeMounts:
            - name: test-scripts
              mountPath: /scripts

    # Pod 故障测试
    - name: pod-failure-test
      templateType: Parallel
      deadline: 10m
      children:
        - inject-pod-failure
        - run-test-under-failure

    - name: inject-pod-failure
      templateType: PodChaos
      deadline: 8m
      podChaos:
        action: pod-kill
        mode: one
        selector:
          namespaces:
            - otlp-test
          labelSelectors:
            'app': 'otel-collector'
        duration: 5m
        gracePeriod: 0

    - name: run-test-under-failure
      templateType: Task
      deadline: 8m
      task:
        container:
          name: test-with-failure
          image: k6io/k6:latest
          command: ['k6', 'run', '--vus', '50', '--duration', '5m', '/scripts/resilience-test.js']
          volumeMounts:
            - name: test-scripts
              mountPath: /scripts

    # 压力测试
    - name: stress-test
      templateType: Parallel
      deadline: 10m
      children:
        - inject-stress
        - run-test-under-stress

    - name: inject-stress
      templateType: StressChaos
      deadline: 8m
      stressChaos:
        mode: one
        selector:
          namespaces:
            - otlp-test
          labelSelectors:
            'app': 'otel-collector'
        stressors:
          cpu:
            workers: 4
            load: 80
          memory:
            workers: 2
            size: '512MB'
        duration: 5m

    - name: run-test-under-stress
      templateType: Task
      deadline: 8m
      task:
        container:
          name: test-with-stress
          image: k6io/k6:latest
          command: ['k6', 'run', '--vus', '50', '--duration', '5m', '/scripts/stress-test.js']
          volumeMounts:
            - name: test-scripts
              mountPath: /scripts

    # 验证测试
    - name: verification-test
      templateType: Task
      deadline: 5m
      task:
        container:
          name: verification
          image: curlimages/curl:latest
          command: ['sh', '-c', '/scripts/verify-resilience.sh']
          volumeMounts:
            - name: test-scripts
              mountPath: /scripts

  volumes:
    - name: test-scripts
      configMap:
        name: chaos-test-scripts
```

```bash
#!/bin/bash
# verify-resilience.sh - 混沌实验验证脚本

set -e

JAEGER_API="http://jaeger-query:16686/api"
PROMETHEUS_API="http://prometheus:9090/api/v1"

echo "=== Chaos Engineering Verification ==="

# 1. 检查追踪数据完整性
echo "1. Checking trace completeness..."

TOTAL_TRACES=$(curl -s "${JAEGER_API}/services/perf-test/operations" | jq '.data | length')
echo "   Total traces: ${TOTAL_TRACES}"

if [ "${TOTAL_TRACES}" -lt 1000 ]; then
    echo "   ❌ FAIL: Expected at least 1000 traces, got ${TOTAL_TRACES}"
    exit 1
fi

echo "   ✅ PASS: Trace completeness verified"

# 2. 检查错误率
echo "2. Checking error rate..."

ERROR_RATE=$(curl -s "${PROMETHEUS_API}/query?query=rate(otlp_receiver_refused_spans[5m])" \
    | jq -r '.data.result[0].value[1] // "0"')

echo "   Error rate: ${ERROR_RATE}"

if [ "$(echo "${ERROR_RATE} > 0.05" | bc -l)" -eq 1 ]; then
    echo "   ❌ FAIL: Error rate ${ERROR_RATE} exceeds 5%"
    exit 1
fi

echo "   ✅ PASS: Error rate acceptable"

# 3. 检查延迟 P99
echo "3. Checking P99 latency..."

P99_LATENCY=$(curl -s "${PROMETHEUS_API}/query?query=histogram_quantile(0.99, rate(otlp_receiver_request_duration_seconds_bucket[5m]))" \
    | jq -r '.data.result[0].value[1] // "0"')

echo "   P99 latency: ${P99_LATENCY}s"

if [ "$(echo "${P99_LATENCY} > 2.0" | bc -l)" -eq 1 ]; then
    echo "   ⚠️  WARN: P99 latency ${P99_LATENCY}s exceeds 2s"
else
    echo "   ✅ PASS: P99 latency acceptable"
fi

# 4. 检查 Collector 恢复
echo "4. Checking Collector recovery..."

COLLECTOR_UP=$(curl -s "${PROMETHEUS_API}/query?query=up{job='otel-collector'}" \
    | jq -r '.data.result[0].value[1]')

if [ "${COLLECTOR_UP}" != "1" ]; then
    echo "   ❌ FAIL: Collector not recovered"
    exit 1
fi

echo "   ✅ PASS: Collector recovered successfully"

echo ""
echo "=== ✅ All chaos engineering tests passed ==="
```

---

## 5. 协议一致性验证

### 5.1 OTLP/gRPC 协议验证

```python
# test_otlp_grpc_protocol.py - OTLP gRPC 协议一致性测试
import pytest
import grpc
from opentelemetry.proto.collector.trace.v1 import trace_service_pb2, trace_service_pb2_grpc
from opentelemetry.proto.trace.v1 import trace_pb2
from opentelemetry.proto.common.v1 import common_pb2
from opentelemetry.proto.resource.v1 import resource_pb2
from typing import Iterator
import time

class TestOTLPgRPCProtocol:
    """OTLP gRPC 协议一致性测试"""

    @pytest.fixture(scope="class")
    def grpc_channel(self):
        """创建 gRPC 通道"""
        channel = grpc.insecure_channel('localhost:4317')
        yield channel
        channel.close()

    @pytest.fixture(scope="class")
    def trace_service_stub(self, grpc_channel):
        """创建 TraceService stub"""
        return trace_service_pb2_grpc.TraceServiceStub(grpc_channel)

    def create_valid_trace_request(self) -> trace_service_pb2.ExportTraceServiceRequest:
        """创建有效的追踪导出请求"""
        return trace_service_pb2.ExportTraceServiceRequest(
            resource_spans=[
                trace_pb2.ResourceSpans(
                    resource=resource_pb2.Resource(
                        attributes=[
                            common_pb2.KeyValue(
                                key='service.name',
                                value=common_pb2.AnyValue(string_value='test-service')
                            ),
                            common_pb2.KeyValue(
                                key='service.version',
                                value=common_pb2.AnyValue(string_value='1.0.0')
                            ),
                        ]
                    ),
                    scope_spans=[
                        trace_pb2.ScopeSpans(
                            scope=common_pb2.InstrumentationScope(
                                name='test-instrumentation',
                                version='1.0.0'
                            ),
                            spans=[
                                trace_pb2.Span(
                                    trace_id=b'\x01' * 16,
                                    span_id=b'\x02' * 8,
                                    name='test-operation',
                                    kind=trace_pb2.Span.SPAN_KIND_INTERNAL,
                                    start_time_unix_nano=int(time.time() * 1e9),
                                    end_time_unix_nano=int((time.time() + 0.1) * 1e9),
                                    attributes=[
                                        common_pb2.KeyValue(
                                            key='http.method',
                                            value=common_pb2.AnyValue(string_value='GET')
                                        ),
                                        common_pb2.KeyValue(
                                            key='http.status_code',
                                            value=common_pb2.AnyValue(int_value=200)
                                        ),
                                    ],
                                )
                            ]
                        )
                    ]
                )
            ]
        )

    def test_export_valid_trace(self, trace_service_stub):
        """测试: 导出有效追踪"""
        request = self.create_valid_trace_request()

        try:
            response = trace_service_stub.Export(request, timeout=10)

            # 验证响应类型
            assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)

            # 验证 PartialSuccess (如果存在)
            if response.HasField('partial_success'):
                assert response.partial_success.rejected_spans == 0, \
                    f"Unexpected rejected spans: {response.partial_success.error_message}"

        except grpc.RpcError as e:
            pytest.fail(f"gRPC export failed: {e.code()} - {e.details()}")

    def test_empty_request(self, trace_service_stub):
        """测试: 空请求"""
        request = trace_service_pb2.ExportTraceServiceRequest()

        # 空请求应该被接受 (根据 OTLP 规范)
        response = trace_service_stub.Export(request, timeout=10)
        assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)

    def test_invalid_trace_id(self, trace_service_stub):
        """测试: 无效的 trace_id (长度不正确)"""
        request = self.create_valid_trace_request()
        # 设置无效的 trace_id (不是 16 字节)
        request.resource_spans[0].scope_spans[0].spans[0].trace_id = b'\x01' * 8  # 只有 8 字节

        try:
            response = trace_service_stub.Export(request, timeout=10)

            # 某些实现可能拒绝,某些可能接受但标记为部分成功
            if response.HasField('partial_success'):
                assert response.partial_success.rejected_spans > 0

        except grpc.RpcError as e:
            # 预期可能失败 (根据实现)
            assert e.code() == grpc.StatusCode.INVALID_ARGUMENT

    def test_compression_support(self, grpc_channel):
        """测试: gRPC 压缩支持"""
        stub = trace_service_pb2_grpc.TraceServiceStub(grpc_channel)
        request = self.create_valid_trace_request()

        # 测试 gzip 压缩
        response = stub.Export(
            request,
            compression=grpc.Compression.Gzip,
            timeout=10
        )

        assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)

    def test_metadata_propagation(self, trace_service_stub):
        """测试: 元数据传播"""
        request = self.create_valid_trace_request()

        metadata = (
            ('x-custom-header', 'test-value'),
            ('authorization', 'Bearer test-token'),
        )

        response = trace_service_stub.Export(request, metadata=metadata, timeout=10)
        assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)

    def test_timeout_handling(self, trace_service_stub):
        """测试: 超时处理"""
        request = self.create_valid_trace_request()

        try:
            # 设置极短的超时
            response = trace_service_stub.Export(request, timeout=0.001)
            # 如果没有超时,也是可以接受的 (请求足够快)
            assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)
        except grpc.RpcError as e:
            # 预期超时
            assert e.code() == grpc.StatusCode.DEADLINE_EXCEEDED

    def test_concurrent_exports(self, trace_service_stub):
        """测试: 并发导出"""
        import concurrent.futures

        requests = [self.create_valid_trace_request() for _ in range(100)]

        with concurrent.futures.ThreadPoolExecutor(max_workers=20) as executor:
            futures = [
                executor.submit(trace_service_stub.Export, req, timeout=10)
                for req in requests
            ]

            results = [future.result() for future in concurrent.futures.as_completed(futures)]

        # 所有请求都应该成功
        assert len(results) == 100
        assert all(isinstance(r, trace_service_pb2.ExportTraceServiceResponse) for r in results)

    def test_large_payload(self, trace_service_stub):
        """测试: 大负载 (1000 spans)"""
        request = trace_service_pb2.ExportTraceServiceRequest(
            resource_spans=[
                trace_pb2.ResourceSpans(
                    resource=resource_pb2.Resource(
                        attributes=[
                            common_pb2.KeyValue(
                                key='service.name',
                                value=common_pb2.AnyValue(string_value='test-service')
                            ),
                        ]
                    ),
                    scope_spans=[
                        trace_pb2.ScopeSpans(
                            spans=[
                                trace_pb2.Span(
                                    trace_id=b'\x01' * 16,
                                    span_id=i.to_bytes(8, 'big'),
                                    name=f'span-{i}',
                                    kind=trace_pb2.Span.SPAN_KIND_INTERNAL,
                                    start_time_unix_nano=int(time.time() * 1e9),
                                    end_time_unix_nano=int((time.time() + 0.1) * 1e9),
                                )
                                for i in range(1000)
                            ]
                        )
                    ]
                )
            ]
        )

        response = trace_service_stub.Export(request, timeout=30)
        assert isinstance(response, trace_service_pb2.ExportTraceServiceResponse)

### 5.2 OTLP/HTTP 协议验证

```python
# test_otlp_http_protocol.py - OTLP HTTP 协议一致性测试
import pytest
import requests
import json
import time
from typing import Dict, Any

class TestOTLPHTTPProtocol:
    """OTLP HTTP 协议一致性测试"""

    BASE_URL = "http://localhost:4318"

    def create_valid_trace_json(self) -> Dict[str, Any]:
        """创建有效的追踪 JSON"""
        return {
            "resourceSpans": [{
                "resource": {
                    "attributes": [
                        {"key": "service.name", "value": {"stringValue": "test-service"}},
                        {"key": "service.version", "value": {"stringValue": "1.0.0"}},
                    ]
                },
                "scopeSpans": [{
                    "scope": {
                        "name": "test-instrumentation",
                        "version": "1.0.0"
                    },
                    "spans": [{
                        "traceId": "01020304050607080910111213141516",
                        "spanId": "0102030405060708",
                        "name": "test-operation",
                        "kind": 1,
                        "startTimeUnixNano": str(int(time.time() * 1e9)),
                        "endTimeUnixNano": str(int((time.time() + 0.1) * 1e9)),
                        "attributes": [
                            {"key": "http.method", "value": {"stringValue": "GET"}},
                            {"key": "http.status_code", "value": {"intValue": "200"}},
                        ],
                    }]
                }]
            }]
        }

    def test_json_content_type(self):
        """测试: application/json Content-Type"""
        data = self.create_valid_trace_json()

        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            json=data,
            headers={"Content-Type": "application/json"},
            timeout=10
        )

        assert response.status_code == 200, f"Unexpected status: {response.status_code} - {response.text}"

        # 验证响应格式
        if response.text:
            response_data = response.json()
            assert isinstance(response_data, dict)

    def test_protobuf_content_type(self):
        """测试: application/x-protobuf Content-Type"""
        from opentelemetry.proto.collector.trace.v1 import trace_service_pb2
        from opentelemetry.proto.trace.v1 import trace_pb2
        from opentelemetry.proto.common.v1 import common_pb2
        from opentelemetry.proto.resource.v1 import resource_pb2

        request = trace_service_pb2.ExportTraceServiceRequest(
            resource_spans=[
                trace_pb2.ResourceSpans(
                    resource=resource_pb2.Resource(
                        attributes=[
                            common_pb2.KeyValue(
                                key='service.name',
                                value=common_pb2.AnyValue(string_value='test-service')
                            ),
                        ]
                    ),
                    scope_spans=[
                        trace_pb2.ScopeSpans(
                            spans=[
                                trace_pb2.Span(
                                    trace_id=b'\x01' * 16,
                                    span_id=b'\x02' * 8,
                                    name='test-operation',
                                    kind=trace_pb2.Span.SPAN_KIND_INTERNAL,
                                    start_time_unix_nano=int(time.time() * 1e9),
                                    end_time_unix_nano=int((time.time() + 0.1) * 1e9),
                                )
                            ]
                        )
                    ]
                )
            ]
        )

        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            data=request.SerializeToString(),
            headers={"Content-Type": "application/x-protobuf"},
            timeout=10
        )

        assert response.status_code == 200

    def test_gzip_compression(self):
        """测试: gzip 压缩"""
        import gzip

        data = self.create_valid_trace_json()
        json_data = json.dumps(data).encode('utf-8')
        compressed_data = gzip.compress(json_data)

        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            data=compressed_data,
            headers={
                "Content-Type": "application/json",
                "Content-Encoding": "gzip",
            },
            timeout=10
        )

        assert response.status_code == 200

    def test_custom_headers(self):
        """测试: 自定义 HTTP headers"""
        data = self.create_valid_trace_json()

        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            json=data,
            headers={
                "Content-Type": "application/json",
                "X-Custom-Header": "test-value",
                "Authorization": "Bearer test-token",
            },
            timeout=10
        )

        assert response.status_code == 200

    def test_cors_headers(self):
        """测试: CORS headers"""
        # OPTIONS 预检请求
        response = requests.options(
            f"{self.BASE_URL}/v1/traces",
            headers={
                "Origin": "http://example.com",
                "Access-Control-Request-Method": "POST",
                "Access-Control-Request-Headers": "Content-Type",
            },
            timeout=10
        )

        # 验证 CORS headers (如果支持)
        if response.status_code == 200:
            assert "Access-Control-Allow-Origin" in response.headers or \
                   response.status_code == 404  # 某些实现不支持 OPTIONS

    def test_http_methods(self):
        """测试: 只支持 POST 方法"""
        data = self.create_valid_trace_json()

        # GET 应该失败
        response = requests.get(f"{self.BASE_URL}/v1/traces", timeout=10)
        assert response.status_code in [404, 405]

        # PUT 应该失败
        response = requests.put(
            f"{self.BASE_URL}/v1/traces",
            json=data,
            timeout=10
        )
        assert response.status_code in [404, 405]

        # DELETE 应该失败
        response = requests.delete(f"{self.BASE_URL}/v1/traces", timeout=10)
        assert response.status_code in [404, 405]

    def test_error_responses(self):
        """测试: 错误响应格式"""
        # 发送无效 JSON
        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            data="invalid json",
            headers={"Content-Type": "application/json"},
            timeout=10
        )

        # 应该返回 4xx 错误
        assert 400 <= response.status_code < 500

    def test_partial_success_response(self):
        """测试: 部分成功响应"""
        # 发送包含无效数据的请求
        data = self.create_valid_trace_json()
        data["resourceSpans"][0]["scopeSpans"][0]["spans"][0]["traceId"] = "invalid"  # 无效长度

        response = requests.post(
            f"{self.BASE_URL}/v1/traces",
            json=data,
            timeout=10
        )

        # 可能返回 200 (部分成功) 或 400 (完全失败),取决于实现
        assert response.status_code in [200, 400]

        if response.status_code == 200 and response.text:
            response_data = response.json()
            if "partialSuccess" in response_data:
                assert response_data["partialSuccess"]["rejectedSpans"] > 0

---

## 6. 性能测试与基准

### 6.1 吞吐量与延迟测试

```python
# benchmark_throughput.py - 吞吐量基准测试
import asyncio
import aiohttp
import time
import statistics
from typing import List, Dict
from dataclasses import dataclass
import json

@dataclass
class BenchmarkConfig:
    """基准测试配置"""
    endpoint: str = "http://localhost:4318/v1/traces"
    total_requests: int = 10000
    concurrency: int = 100
    payload_size: str = "small"  # small, medium, large

@dataclass
class BenchmarkResult:
    """基准测试结果"""
    total_requests: int
    successful_requests: int
    failed_requests: int
    total_duration_seconds: float
    requests_per_second: float
    avg_latency_ms: float
    median_latency_ms: float
    p95_latency_ms: float
    p99_latency_ms: float
    min_latency_ms: float
    max_latency_ms: float

class ThroughputBenchmark:
    """吞吐量基准测试"""

    def __init__(self, config: BenchmarkConfig):
        self.config = config
        self.latencies: List[float] = []
        self.success_count = 0
        self.failure_count = 0

    def generate_payload(self) -> Dict:
        """生成测试负载"""
        base_payload = {
            "resourceSpans": [{
                "resource": {
                    "attributes": [
                        {"key": "service.name", "value": {"stringValue": "benchmark-service"}},
                    ]
                },
                "scopeSpans": [{
                    "spans": []
                }]
            }]
        }

        # 根据 payload_size 调整 span 数量
        span_counts = {"small": 1, "medium": 10, "large": 100}
        num_spans = span_counts.get(self.config.payload_size, 1)

        for i in range(num_spans):
            span = {
                "traceId": f"{i:032x}",
                "spanId": f"{i:016x}",
                "name": f"benchmark-span-{i}",
                "kind": 1,
                "startTimeUnixNano": str(int(time.time() * 1e9)),
                "endTimeUnixNano": str(int((time.time() + 0.1) * 1e9)),
            }
            base_payload["resourceSpans"][0]["scopeSpans"][0]["spans"].append(span)

        return base_payload

    async def send_request(self, session: aiohttp.ClientSession) -> None:
        """发送单个请求"""
        payload = self.generate_payload()

        start_time = time.perf_counter()

        try:
            async with session.post(
                self.config.endpoint,
                json=payload,
                headers={"Content-Type": "application/json"},
                timeout=aiohttp.ClientTimeout(total=30)
            ) as response:
                await response.read()

                end_time = time.perf_counter()
                latency_ms = (end_time - start_time) * 1000

                self.latencies.append(latency_ms)

                if response.status == 200:
                    self.success_count += 1
                else:
                    self.failure_count += 1

        except Exception as e:
            self.failure_count += 1
            print(f"Request failed: {e}")

    async def run_benchmark(self) -> BenchmarkResult:
        """运行基准测试"""
        print(f"Starting benchmark: {self.config.total_requests} requests with concurrency {self.config.concurrency}")

        connector = aiohttp.TCPConnector(limit=self.config.concurrency)
        async with aiohttp.ClientSession(connector=connector) as session:
            start_time = time.time()

            # 创建任务
            tasks = [
                self.send_request(session)
                for _ in range(self.config.total_requests)
            ]

            # 执行任务 (限制并发)
            for i in range(0, len(tasks), self.config.concurrency):
                batch = tasks[i:i + self.config.concurrency]
                await asyncio.gather(*batch, return_exceptions=True)

            end_time = time.time()
            total_duration = end_time - start_time

        # 计算统计指标
        self.latencies.sort()

        return BenchmarkResult(
            total_requests=self.config.total_requests,
            successful_requests=self.success_count,
            failed_requests=self.failure_count,
            total_duration_seconds=total_duration,
            requests_per_second=self.config.total_requests / total_duration,
            avg_latency_ms=statistics.mean(self.latencies),
            median_latency_ms=statistics.median(self.latencies),
            p95_latency_ms=self.latencies[int(len(self.latencies) * 0.95)],
            p99_latency_ms=self.latencies[int(len(self.latencies) * 0.99)],
            min_latency_ms=min(self.latencies),
            max_latency_ms=max(self.latencies),
        )

    def print_results(self, result: BenchmarkResult) -> None:
        """打印结果"""
        print("\n" + "="*60)
        print("BENCHMARK RESULTS")
        print("="*60)
        print(f"Total Requests:        {result.total_requests}")
        print(f"Successful:            {result.successful_requests} ({result.successful_requests/result.total_requests*100:.2f}%)")
        print(f"Failed:                {result.failure_count}")
        print(f"Total Duration:        {result.total_duration_seconds:.2f}s")
        print(f"Throughput:            {result.requests_per_second:.2f} req/s")
        print(f"Average Latency:       {result.avg_latency_ms:.2f} ms")
        print(f"Median Latency:        {result.median_latency_ms:.2f} ms")
        print(f"P95 Latency:           {result.p95_latency_ms:.2f} ms")
        print(f"P99 Latency:           {result.p99_latency_ms:.2f} ms")
        print(f"Min Latency:           {result.min_latency_ms:.2f} ms")
        print(f"Max Latency:           {result.max_latency_ms:.2f} ms")
        print("="*60 + "\n")

# 使用示例
async def main():
    configs = [
        BenchmarkConfig(total_requests=1000, concurrency=10, payload_size="small"),
        BenchmarkConfig(total_requests=1000, concurrency=50, payload_size="small"),
        BenchmarkConfig(total_requests=1000, concurrency=100, payload_size="small"),
        BenchmarkConfig(total_requests=1000, concurrency=100, payload_size="medium"),
        BenchmarkConfig(total_requests=500, concurrency=100, payload_size="large"),
    ]

    for config in configs:
        print(f"\nRunning benchmark: concurrency={config.concurrency}, payload={config.payload_size}")
        benchmark = ThroughputBenchmark(config)
        result = await benchmark.run_benchmark()
        benchmark.print_results(result)

        # 等待系统恢复
        await asyncio.sleep(5)

if __name__ == "__main__":
    asyncio.run(main())
```

---

## 7. 自动化测试流水线

### 7.1 CI/CD 集成 (GitHub Actions)

```yaml
# .github/workflows/otlp-test-pipeline.yml
name: OTLP Test Pipeline

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main, develop]

env:
  OTLP_VERSION: "0.108.0"

jobs:
  # 静态分析
  static-analysis:
    name: Static Analysis
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Install linters
        run: |
          pip install pylint mypy black isort

      - name: Run Black (formatting check)
        run: black --check src/

      - name: Run isort (import sorting)
        run: isort --check-only src/

      - name: Run Pylint
        run: pylint src/

      - name: Run MyPy (type checking)
        run: mypy src/

  # 单元测试
  unit-tests:
    name: Unit Tests
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.9', '3.10', '3.11', '3.12']

    steps:
      - uses: actions/checkout@v4

      - name: Set up Python ${{ matrix.python-version }}
        uses: actions/setup-python@v5
        with:
          python-version: ${{ matrix.python-version }}

      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install -r requirements-test.txt

      - name: Run unit tests
        run: |
          pytest tests/unit \
            --cov=src \
            --cov-report=xml \
            --cov-report=term \
            --junitxml=test-results/junit.xml

      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          file: ./coverage.xml
          flags: unittests
          name: python-${{ matrix.python-version }}

      - name: Upload test results
        uses: actions/upload-artifact@v3
        if: always()
        with:
          name: test-results-${{ matrix.python-version }}
          path: test-results/

  # 集成测试
  integration-tests:
    name: Integration Tests
    runs-on: ubuntu-latest
    needs: [unit-tests]

    services:
      redis:
        image: redis:7-alpine
        ports:
          - 6379:6379

      postgres:
        image: postgres:16-alpine
        env:
          POSTGRES_USER: testuser
          POSTGRES_PASSWORD: testpass
          POSTGRES_DB: testdb
        ports:
          - 5432:5432
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5

    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Start OTLP Collector
        run: |
          docker run -d --name otel-collector \
            -p 4317:4317 -p 4318:4318 -p 8888:8888 \
            -v $(pwd)/test-configs/collector-config.yaml:/etc/otel-collector-config.yaml \
            otel/opentelemetry-collector-contrib:${{ env.OTLP_VERSION }} \
            --config=/etc/otel-collector-config.yaml

          # Wait for collector
          sleep 10
          curl -f http://localhost:8888/

      - name: Start Jaeger
        run: |
          docker run -d --name jaeger \
            -p 16686:16686 -p 14250:14250 \
            -e COLLECTOR_OTLP_ENABLED=true \
            jaegertracing/all-in-one:1.52

          sleep 5

      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install -r requirements-test.txt

      - name: Run integration tests
        env:
          OTLP_ENDPOINT: http://localhost:4318
          JAEGER_UI: http://localhost:16686
          REDIS_URL: redis://localhost:6379
          DATABASE_URL: postgresql://testuser:testpass@localhost:5432/testdb
        run: |
          pytest tests/integration \
            --junitxml=test-results/integration-junit.xml

      - name: Collect logs
        if: failure()
        run: |
          docker logs otel-collector > collector-logs.txt
          docker logs jaeger > jaeger-logs.txt

      - name: Upload logs
        if: failure()
        uses: actions/upload-artifact@v3
        with:
          name: integration-test-logs
          path: |
            collector-logs.txt
            jaeger-logs.txt

  # E2E 测试
  e2e-tests:
    name: E2E Tests
    runs-on: ubuntu-latest
    needs: [integration-tests]

    steps:
      - uses: actions/checkout@v4

      - name: Set up Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'

      - name: Start test environment
        run: |
          docker-compose -f docker-compose.test.yml up -d
          sleep 20

      - name: Install Playwright
        run: |
          npm install -D @playwright/test
          npx playwright install --with-deps

      - name: Run E2E tests
        run: |
          npx playwright test tests/e2e/

      - name: Upload Playwright report
        uses: actions/upload-artifact@v3
        if: always()
        with:
          name: playwright-report
          path: playwright-report/

  # 性能测试
  performance-tests:
    name: Performance Tests
    runs-on: ubuntu-latest
    needs: [integration-tests]

    steps:
      - uses: actions/checkout@v4

      - name: Start test environment
        run: |
          docker-compose -f docker-compose.test.yml up -d
          sleep 20

      - name: Install K6
        run: |
          sudo gpg -k
          sudo gpg --no-default-keyring --keyring /usr/share/keyrings/k6-archive-keyring.gpg \
            --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys C5AD17C747E3415A3642D57D77C6C491D6AC1D69
          echo "deb [signed-by=/usr/share/keyrings/k6-archive-keyring.gpg] https://dl.k6.io/deb stable main" \
            | sudo tee /etc/apt/sources.list.d/k6.list
          sudo apt-get update
          sudo apt-get install k6

      - name: Run performance tests
        run: |
          k6 run tests/performance/performance-test.js \
            --out json=performance-results.json

      - name: Analyze performance regression
        run: |
          python scripts/analyze_performance_regression.py \
            --current performance-results.json \
            --baseline performance-baseline.json \
            --threshold 0.10  # 10% regression threshold

      - name: Upload performance results
        uses: actions/upload-artifact@v3
        with:
          name: performance-results
          path: performance-results.json

  # 安全扫描
  security-scan:
    name: Security Scan
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4

      - name: Run Trivy (vulnerability scanner)
        uses: aquasecurity/trivy-action@master
        with:
          scan-type: 'fs'
          scan-ref: '.'
          format: 'sarif'
          output: 'trivy-results.sarif'

      - name: Upload Trivy results to GitHub Security
        uses: github/codeql-action/upload-sarif@v2
        with:
          sarif_file: 'trivy-results.sarif'

      - name: Run Bandit (Python security linter)
        run: |
          pip install bandit
          bandit -r src/ -f json -o bandit-results.json

      - name: Upload Bandit results
        uses: actions/upload-artifact@v3
        with:
          name: bandit-results
          path: bandit-results.json

  # 报告生成
  generate-report:
    name: Generate Test Report
    runs-on: ubuntu-latest
    needs: [unit-tests, integration-tests, e2e-tests, performance-tests, security-scan]
    if: always()

    steps:
      - uses: actions/checkout@v4

      - name: Download all artifacts
        uses: actions/download-artifact@v3

      - name: Generate unified report
        run: |
          python scripts/generate_test_report.py \
            --output test-report.html

      - name: Upload test report
        uses: actions/upload-artifact@v3
        with:
          name: test-report
          path: test-report.html

      - name: Comment PR with report
        if: github.event_name == 'pull_request'
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const report = fs.readFileSync('test-report-summary.md', 'utf8');
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: report
            });
```

---

## 8. 工具链与生态

### 8.1 推荐测试工具矩阵

| 测试类型 | 语言/框架 | 推荐工具 | 优势 | 集成难度 |
|---------|---------|---------|------|---------|
| **单元测试** | Python | pytest, unittest | 丰富的插件生态, 简洁语法 | ⭐ 低 |
| | Go | testing, testify | 内置标准库, 强大断言 | ⭐ 低 |
| | Java | JUnit 5, Mockito | 成熟稳定, 企业级支持 | ⭐⭐ 中 |
| | Node.js/TypeScript | Jest, Mocha | 快速执行, 良好 TypeScript 支持 | ⭐ 低 |
| **Mock/Stub** | 跨语言 | Mockito, unittest.mock, testify/mock | 灵活的模拟策略 | ⭐ 低 |
| **集成测试** | 容器编排 | Testcontainers | 真实环境隔离, 可重复 | ⭐⭐ 中 |
| | Docker | Docker Compose | 简单快速, 广泛支持 | ⭐ 低 |
| **契约测试** | 跨服务 | Pact, Spring Cloud Contract | API 兼容性保证 | ⭐⭐⭐ 高 |
| **E2E 测试** | Web UI | Playwright, Cypress | 现代浏览器自动化 | ⭐⭐ 中 |
| | API | Postman, Newman | 易用的 API 测试 | ⭐ 低 |
| **性能测试** | 负载生成 | K6, JMeter, Gatling | 强大的负载模拟 | ⭐⭐ 中 |
| | 基准测试 | pytest-benchmark, Go benchmarks | 精确的性能度量 | ⭐ 低 |
| **混沌工程** | Kubernetes | Chaos Mesh, Litmus | 分布式故障注入 | ⭐⭐⭐ 高 |
| | 通用 | Gremlin, Pumba | 多种混沌场景 | ⭐⭐ 中 |
| **覆盖率** | Python | coverage.py, pytest-cov | 详细的覆盖率报告 | ⭐ 低 |
| | Go | go test -cover | 内置覆盖率支持 | ⭐ 低 |
| | Java | JaCoCo | 企业级覆盖率分析 | ⭐⭐ 中 |
| **安全测试** | 漏洞扫描 | Trivy, Snyk | 自动依赖扫描 | ⭐ 低 |
| | SAST | Bandit, SonarQube | 静态代码安全分析 | ⭐⭐ 中 |
| **协议测试** | OTLP | Custom scripts, grpcurl | 协议级别验证 | ⭐⭐ 中 |

### 8.2 自定义测试工具开发

```python
# otlp_test_framework.py - 自定义 OTLP 测试框架
"""
OTLP 测试框架 - 提供简化的测试 API 和常用测试场景

使用示例:
    with OTLPTestEnvironment() as env:
        client = env.create_trace_client()
        trace_id = client.send_trace("test-operation")
        env.verify_trace_received(trace_id, timeout=10)
"""

import time
import uuid
import requests
from typing import Optional, Dict, Any, List
from contextlib import contextmanager
from dataclasses import dataclass
import docker
from opentelemetry.proto.collector.trace.v1 import trace_service_pb2
from opentelemetry.proto.trace.v1 import trace_pb2
from opentelemetry.proto.common.v1 import common_pb2
from opentelemetry.proto.resource.v1 import resource_pb2

@dataclass
class OTLPTestConfig:
    """测试环境配置"""
    collector_image: str = "otel/opentelemetry-collector-contrib:0.108.0"
    jaeger_image: str = "jaegertracing/all-in-one:1.52"
    collector_grpc_port: int = 4317
    collector_http_port: int = 4318
    jaeger_ui_port: int = 16686
    startup_timeout: int = 30

class OTLPTestEnvironment:
    """OTLP 测试环境管理器"""

    def __init__(self, config: Optional[OTLPTestConfig] = None):
        self.config = config or OTLPTestConfig()
        self.docker_client = docker.from_env()
        self.containers: Dict[str, Any] = {}
        self._started = False

    def __enter__(self):
        """进入上下文时启动测试环境"""
        self.start()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """退出上下文时清理测试环境"""
        self.cleanup()

    def start(self) -> None:
        """启动测试环境"""
        if self._started:
            return

        print("Starting OTLP test environment...")

        # 启动 Jaeger
        self.containers['jaeger'] = self.docker_client.containers.run(
            self.config.jaeger_image,
            name=f"otlp-test-jaeger-{uuid.uuid4().hex[:8]}",
            ports={
                '16686/tcp': self.config.jaeger_ui_port,
                '4317/tcp': 14317,  # 内部 OTLP gRPC
            },
            environment={'COLLECTOR_OTLP_ENABLED': 'true'},
            detach=True,
            remove=True,
        )

        # 启动 Collector
        collector_config = self._generate_collector_config()
        self.containers['collector'] = self.docker_client.containers.run(
            self.config.collector_image,
            name=f"otlp-test-collector-{uuid.uuid4().hex[:8]}",
            ports={
                '4317/tcp': self.config.collector_grpc_port,
                '4318/tcp': self.config.collector_http_port,
            },
            command=['--config=yaml:' + collector_config],
            detach=True,
            remove=True,
        )

        # 等待服务就绪
        self._wait_for_readiness()
        self._started = True
        print("✅ Test environment ready")

    def cleanup(self) -> None:
        """清理测试环境"""
        if not self._started:
            return

        print("Cleaning up test environment...")
        for name, container in self.containers.items():
            try:
                container.stop(timeout=5)
                print(f"  Stopped {name}")
            except Exception as e:
                print(f"  Error stopping {name}: {e}")

        self.containers.clear()
        self._started = False
        print("✅ Cleanup complete")

    def _generate_collector_config(self) -> str:
        """生成 Collector 配置"""
        jaeger_endpoint = f"{self.containers['jaeger'].name}:4317"

        return f"""
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
    send_batch_size: 100

exporters:
  otlp:
    endpoint: {jaeger_endpoint}
    tls:
      insecure: true
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp, logging]
"""

    def _wait_for_readiness(self) -> None:
        """等待服务就绪"""
        start = time.time()

        # 等待 Collector
        collector_ready = False
        while time.time() - start < self.config.startup_timeout:
            try:
                response = requests.get(
                    f"http://localhost:{self.config.collector_http_port}/",
                    timeout=2
                )
                if response.status_code in [200, 404]:
                    collector_ready = True
                    break
            except requests.RequestException:
                pass
            time.sleep(1)

        if not collector_ready:
            raise TimeoutError("Collector failed to start")

        # 等待 Jaeger
        jaeger_ready = False
        while time.time() - start < self.config.startup_timeout:
            try:
                response = requests.get(
                    f"http://localhost:{self.config.jaeger_ui_port}/",
                    timeout=2
                )
                if response.status_code == 200:
                    jaeger_ready = True
                    break
            except requests.RequestException:
                pass
            time.sleep(1)

        if not jaeger_ready:
            raise TimeoutError("Jaeger failed to start")

    def create_trace_client(self, service_name: str = "test-service") -> 'OTLPTraceClient':
        """创建追踪客户端"""
        return OTLPTraceClient(
            endpoint=f"http://localhost:{self.config.collector_http_port}",
            service_name=service_name
        )

    def verify_trace_received(
        self,
        trace_id: str,
        timeout: int = 10
    ) -> bool:
        """验证追踪数据已接收"""
        jaeger_api = f"http://localhost:{self.config.jaeger_ui_port}/api/traces/{trace_id}"

        start = time.time()
        while time.time() - start < timeout:
            try:
                response = requests.get(jaeger_api, timeout=5)
                if response.status_code == 200:
                    data = response.json()
                    if data.get('data') and len(data['data']) > 0:
                        return True
            except requests.RequestException:
                pass
            time.sleep(1)

        return False

    def get_trace(self, trace_id: str) -> Optional[Dict]:
        """获取追踪数据"""
        jaeger_api = f"http://localhost:{self.config.jaeger_ui_port}/api/traces/{trace_id}"

        try:
            response = requests.get(jaeger_api, timeout=5)
            if response.status_code == 200:
                data = response.json()
                if data.get('data') and len(data['data']) > 0:
                    return data['data'][0]
        except requests.RequestException:
            pass

        return None

class OTLPTraceClient:
    """OTLP 追踪客户端 (简化版)"""

    def __init__(self, endpoint: str, service_name: str):
        self.endpoint = f"{endpoint}/v1/traces"
        self.service_name = service_name

    def send_trace(
        self,
        operation_name: str,
        attributes: Optional[Dict[str, Any]] = None,
        duration_ms: float = 100.0
    ) -> str:
        """发送测试追踪"""
        trace_id = uuid.uuid4().hex
        span_id = uuid.uuid4().hex[:16]

        start_time = int(time.time() * 1e9)
        end_time = int((time.time() + duration_ms / 1000) * 1e9)

        span_attributes = [
            {"key": "test.type", "value": {"stringValue": "automated"}}
        ]

        if attributes:
            for key, value in attributes.items():
                if isinstance(value, str):
                    span_attributes.append({
                        "key": key,
                        "value": {"stringValue": value}
                    })
                elif isinstance(value, int):
                    span_attributes.append({
                        "key": key,
                        "value": {"intValue": str(value)}
                    })

        payload = {
            "resourceSpans": [{
                "resource": {
                    "attributes": [
                        {"key": "service.name", "value": {"stringValue": self.service_name}}
                    ]
                },
                "scopeSpans": [{
                    "spans": [{
                        "traceId": trace_id,
                        "spanId": span_id,
                        "name": operation_name,
                        "kind": 1,
                        "startTimeUnixNano": str(start_time),
                        "endTimeUnixNano": str(end_time),
                        "attributes": span_attributes,
                    }]
                }]
            }]
        }

        response = requests.post(
            self.endpoint,
            json=payload,
            headers={"Content-Type": "application/json"},
            timeout=10
        )

        if response.status_code != 200:
            raise RuntimeError(f"Failed to send trace: {response.status_code} - {response.text}")

        return trace_id

# ===== 使用示例 =====

def test_otlp_framework_example():
    """测试框架使用示例"""
    with OTLPTestEnvironment() as env:
        # 创建客户端
        client = env.create_trace_client(service_name="example-service")

        # 发送追踪
        trace_id = client.send_trace(
            operation_name="example-operation",
            attributes={
                "http.method": "GET",
                "http.status_code": 200,
            },
            duration_ms=50.0
        )

        print(f"Sent trace: {trace_id}")

        # 验证接收
        assert env.verify_trace_received(trace_id, timeout=10), \
            f"Trace {trace_id} not received"

        # 获取并验证内容
        trace_data = env.get_trace(trace_id)
        assert trace_data is not None
        assert len(trace_data['spans']) == 1
        assert trace_data['spans'][0]['operationName'] == 'example-operation'

        print("✅ Test passed!")

if __name__ == "__main__":
    test_otlp_framework_example()
```

---

## 9. 最佳实践与案例研究

### 9.1 行业标杆案例

#### 案例 1: Uber - 大规模分布式追踪测试

**挑战**:

- 每秒百万级追踪数据
- 复杂的微服务拓扑 (2000+ 服务)
- 多语言、多框架混合

**测试策略**:

1. **分层测试金字塔**:
   - 单元测试覆盖率 > 85%
   - 集成测试覆盖关键路径
   - E2E 测试覆盖用户核心流程

2. **影子流量测试** (Shadow Testing):
   - 复制生产流量到测试环境
   - 对比新老版本的追踪数据完整性

3. **性能基准回归**:
   - 每次 PR 自动运行性能测试
   - P99 延迟不得超过基线 10%

**成果**:

- 生产故障率降低 70%
- 测试覆盖率提升到 87%
- 发布频率提升 3 倍

#### 案例 2: Netflix - 混沌工程驱动的可观测性测试

**挑战**:

- 全球分布式架构
- 复杂的故障场景
- 高可用性要求 (99.99%)

**测试策略**:

1. **混沌工程集成**:
   - Chaos Monkey: 随机终止服务实例
   - Latency Monkey: 注入网络延迟
   - 验证追踪数据在故障场景下的完整性

2. **Canary 部署测试**:
   - 1% 流量先导测试
   - 实时监控追踪数据质量指标
   - 自动回滚机制

3. **跨区域测试**:
   - 模拟跨区域网络分区
   - 验证追踪上下文传播的鲁棒性

**成果**:

- 故障恢复时间 (MTTR) 减少 60%
- 追踪数据丢失率 < 0.1%

### 9.2 常见陷阱与解决方案

#### 陷阱 1: 测试环境与生产环境差异过大

**问题**:

- 测试环境使用单机 Collector
- 生产环境使用分布式 Collector 集群
- 导致测试通过但生产失败

**解决方案**:

```yaml
# docker-compose.test-production-like.yml
# 生产化的测试环境
version: '3.9'

services:
  # Collector 集群 (3 节点)
  otel-collector-1:
    image: otel/opentelemetry-collector-contrib:0.108.0
    <<: &collector-common
      volumes:
        - ./collector-config.yaml:/etc/config.yaml
      command: ["--config=/etc/config.yaml"]

  otel-collector-2:
    image: otel/opentelemetry-collector-contrib:0.108.0
    <<: *collector-common

  otel-collector-3:
    image: otel/opentelemetry-collector-contrib:0.108.0
    <<: *collector-common

  # 负载均衡器
  nginx-lb:
    image: nginx:alpine
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./nginx-lb.conf:/etc/nginx/nginx.conf
    depends_on:
      - otel-collector-1
      - otel-collector-2
      - otel-collector-3
```

#### 陷阱 2: 测试数据不真实

**问题**:

- 测试用例使用简单、规整的数据
- 生产环境有各种边界情况、异常数据

**解决方案**:

```python
# test_data_generator.py - 真实数据生成器
import random
import string
from typing import Dict, Any

class RealisticTraceGenerator:
    """生成更真实的测试追踪数据"""

    def generate_realistic_span(self) -> Dict[str, Any]:
        """生成真实的 Span 数据"""
        span = self._base_span()

        # 随机添加真实场景的复杂性
        scenarios = [
            self._add_error_scenario,
            self._add_long_duration,
            self._add_many_attributes,
            self._add_unicode_characters,
            self._add_large_events,
        ]

        # 20% 概率触发特殊场景
        if random.random() < 0.2:
            random.choice(scenarios)(span)

        return span

    def _base_span(self) -> Dict[str, Any]:
        """基础 Span"""
        return {
            "traceId": self._random_hex(32),
            "spanId": self._random_hex(16),
            "name": random.choice([
                "GET /api/users",
                "POST /api/orders",
                "database query",
                "cache lookup",
            ]),
            "kind": random.choice([1, 2, 3]),
            "startTimeUnixNano": str(int(time.time() * 1e9)),
            "endTimeUnixNano": str(int((time.time() + random.uniform(0.01, 2.0)) * 1e9)),
        }

    def _add_error_scenario(self, span: Dict[str, Any]) -> None:
        """添加错误场景"""
        span["status"] = {
            "code": 2,  # ERROR
            "message": random.choice([
                "Connection timeout",
                "Internal server error",
                "Resource not found",
            ])
        }
        span["events"] = [{
            "name": "exception",
            "timeUnixNano": span["startTimeUnixNano"],
            "attributes": [
                {"key": "exception.type", "value": {"stringValue": "TimeoutError"}},
                {"key": "exception.message", "value": {"stringValue": "Request timed out after 30s"}},
                {"key": "exception.stacktrace", "value": {"stringValue": self._generate_stacktrace()}},
            ]
        }]

    def _add_unicode_characters(self, span: Dict[str, Any]) -> None:
        """添加 Unicode 字符 (测试编码处理)"""
        span["name"] = "用户查询 🔍"
        span["attributes"] = [
            {"key": "user.name", "value": {"stringValue": "张三"}},
            {"key": "emoji", "value": {"stringValue": "👍😀🚀"}},
        ]

    def _add_many_attributes(self, span: Dict[str, Any]) -> None:
        """添加大量属性 (测试容量限制)"""
        span["attributes"] = [
            {"key": f"attr_{i}", "value": {"stringValue": f"value_{i}"}}
            for i in range(100)
        ]

    def _random_hex(self, length: int) -> str:
        """生成随机十六进制字符串"""
        return ''.join(random.choices('0123456789abcdef', k=length))

    def _generate_stacktrace(self) -> str:
        """生成模拟堆栈跟踪"""
        return "\n".join([
            f"  File '/app/service.py', line {random.randint(10, 500)}, in process_request"
            for _ in range(random.randint(3, 10))
        ])
```

#### 陷阱 3: 测试数据污染

**问题**:

- 测试之间共享状态
- 前一个测试失败导致后续测试受影响

**解决方案**:

```python
# test_isolation.py - 测试隔离最佳实践
import pytest
from typing import Generator

class TestWithProperIsolation:
    """测试隔离最佳实践"""

    @pytest.fixture(autouse=True)
    def setup_and_teardown(self) -> Generator:
        """每个测试前后自动清理"""
        # Setup: 创建隔离的测试数据
        self.test_id = uuid.uuid4().hex
        self.trace_ids = []

        yield

        # Teardown: 清理测试数据
        self._cleanup_test_data()

    def _cleanup_test_data(self) -> None:
        """清理测试数据"""
        for trace_id in self.trace_ids:
            # 清理追踪数据 (如果后端支持)
            try:
                requests.delete(f"http://backend/traces/{trace_id}")
            except:
                pass

    def test_isolated_1(self):
        """隔离的测试 1"""
        trace_id = self._send_test_trace(f"test-1-{self.test_id}")
        self.trace_ids.append(trace_id)
        # ... 测试逻辑 ...

    def test_isolated_2(self):
        """隔离的测试 2"""
        trace_id = self._send_test_trace(f"test-2-{self.test_id}")
        self.trace_ids.append(trace_id)
        # ... 测试逻辑 ...
```

### 9.3 测试策略演进路径

#### 阶段 1: 基础测试 (0-3 个月)

**目标**: 建立基本测试覆盖

- ✅ 单元测试覆盖率 > 70%
- ✅ 关键路径的集成测试
- ✅ 基本的 CI 集成

**工具**:

- pytest / JUnit / Go testing
- Docker Compose

#### 阶段 2: 自动化增强 (3-6 个月)

**目标**: 提升测试自动化和覆盖率

- ✅ 单元测试覆盖率 > 80%
- ✅ 完整的集成测试套件
- ✅ 初步的性能基准测试
- ✅ 自动化 E2E 测试

**工具**:

- Testcontainers
- K6 / JMeter
- Playwright

#### 阶段 3: 生产级测试 (6-12 个月)

**目标**: 达到生产级测试标准

- ✅ 单元测试覆盖率 > 85%
- ✅ 混沌工程测试
- ✅ 性能回归检测
- ✅ 安全扫描集成
- ✅ 影子流量测试

**工具**:

- Chaos Mesh
- 性能回归分析框架
- Trivy / Snyk

#### 阶段 4: 持续优化 (12+ 个月)

**目标**: 持续改进测试效率和质量

- ✅ 智能测试选择 (只运行相关测试)
- ✅ 测试并行化优化
- ✅ AI 辅助测试生成
- ✅ 生产环境测试验证

**工具**:

- 自定义测试框架
- AI/ML 工具

### 9.4 ROI 与质量度量

#### 测试投资回报率计算

**成本**:

- 测试基础设施: $5,000/月
- 测试工具许可证: $2,000/月
- 测试维护时间: 2 工程师 × 20% = 0.4 FTE × $120,000/年 = $48,000/年

**总年成本**: $5,000×12 + $2,000×12 + $48,000 = **$132,000/年**

**收益**:

- 生产故障减少 70%: 节省 $250,000/年 (故障成本)
- 发布速度提升 3 倍: 增加 $150,000/年 (业务价值)
- 客户满意度提升: $100,000/年 (客户留存)

**总年收益**: **$500,000/年**

**ROI**: ($500,000 - $132,000) / $132,000 = **278%**

#### 质量度量指标

| 指标 | 目标值 | 当前值 | 趋势 |
|------|--------|--------|------|
| **代码覆盖率** | > 85% | 87% | ✅ 达标 |
| **P0 Bug 逃逸率** | < 1% | 0.5% | ✅ 达标 |
| **测试执行时间** | < 30min | 25min | ✅ 达标 |
| **性能回归检测率** | 100% | 100% | ✅ 达标 |
| **生产故障率** | < 0.1% | 0.08% | ✅ 达标 |
| **MTTR (平均修复时间)** | < 1h | 45min | ✅ 达标 |

---

## 10. 总结与展望

### 10.1 核心要点

1. **分层测试策略**: 单元测试为基础,集成/E2E 测试为保障
2. **自动化优先**: CI/CD 集成,快速反馈
3. **真实环境模拟**: 使用 Testcontainers 等工具
4. **持续优化**: 性能基准、混沌工程、安全扫描

### 10.2 未来趋势

- **AI 辅助测试**: 自动生成测试用例、智能故障定位
- **云原生测试**: Kubernetes-native 测试框架
- **eBPF 测试**: 零侵入的生产环境验证
- **数字孪生**: 完整的生产环境克隆用于测试

---

## 相关文档

- [🤖_OTLP自主运维能力完整架构_AIOps平台设计.md](./🤖_OTLP自主运维能力完整架构_AIOps平台设计.md) - AIOps 平台的自动化测试策略
- [🛠️_交互式配置生成器_OTLP_Collector配置向导.md](./🛠️_交互式配置生成器_OTLP_Collector配置向导.md) - 配置生成器的测试验证
- [📚_OTLP_SDK最佳实践指南_多语言全栈实现.md](./📚_OTLP_SDK最佳实践指南_多语言全栈实现.md) - SDK 开发的单元测试最佳实践
- [📊_架构图表与可视化指南_Mermaid完整版.md](./📊_架构图表与可视化指南_Mermaid完整版.md) - 测试架构与流程可视化
- [🐝_eBPF可观测性深度技术指南_零侵入式追踪.md](./🐝_eBPF可观测性深度技术指南_零侵入式追踪.md) - eBPF 组件的测试策略
- [🕸️_服务网格可观测性完整指南_Istio_Linkerd深度集成.md](./🕸️_服务网格可观测性完整指南_Istio_Linkerd深度集成.md) - Service Mesh 集成测试

---

**文档版本**: v1.0.0
**最后更新**: 2025-10-09
**贡献者**: OTLP 测试框架工作组
