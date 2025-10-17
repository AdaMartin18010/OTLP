# Quick Start Guide

> **Language**: English  
> **Target Audience**: OpenTelemetry Beginners  
> **Estimated Time**: 30 minutes

[中文版](../../标准深度梳理_2025_10/00_总览/快速开始.md) | **English Version**

---

## 📋 Table of Contents

- [What is OpenTelemetry?](#what-is-opentelemetry)
- [What is OTLP?](#what-is-otlp)
- [Prerequisites](#prerequisites)
- [Running Your First Example](#running-your-first-example)
- [Understanding the Results](#understanding-the-results)
- [Next Steps](#next-steps)

---

## What is OpenTelemetry?

**OpenTelemetry** is an open-source observability framework for cloud-native software. It provides:

- 📊 **Traces**: Distributed tracing for understanding request flows
- 📈 **Metrics**: Performance measurements and system health indicators
- 📝 **Logs**: Structured logging with trace context

### Why OpenTelemetry?

✅ **Vendor-Neutral**: Not tied to any specific vendor  
✅ **Polyglot**: Supports multiple programming languages  
✅ **Unified**: Single standard for all telemetry data  
✅ **Built-in by Default**: Designed to be embedded in frameworks

---

## What is OTLP?

**OTLP (OpenTelemetry Protocol)** is the native protocol for transmitting telemetry data in OpenTelemetry.

### Key Features

- 🚀 **Efficient**: Protocol Buffers-based binary format
- 🔄 **Dual Transport**: Supports both gRPC and HTTP
- 📦 **Batching**: Optimized for high-throughput scenarios
- 🔒 **Secure**: TLS encryption support

### OTLP Architecture

```
┌─────────────┐      OTLP       ┌──────────────┐
│ Application │ ──────────────> │   Collector  │
│   (SDK)     │   (gRPC/HTTP)   │              │
└─────────────┘                  └──────────────┘
                                        │
                    ┌───────────────────┼───────────────────┐
                    ▼                   ▼                   ▼
              ┌──────────┐        ┌─────────┐        ┌─────────┐
              │  Jaeger  │        │ Zipkin  │        │Prometheus│
              └──────────┘        └─────────┘        └─────────┘
```

---

## Prerequisites

### Required Software

| Software | Minimum Version | Purpose |
|----------|----------------|---------|
| Docker | 20.10+ | Run infrastructure |
| Docker Compose | 2.0+ | Orchestrate services |
| Git | 2.30+ | Clone repository |

**Choose one programming language**:
- Go 1.21+ OR
- Python 3.11+ OR
- Java 17+ OR
- Node.js 18+

### Installation Check

```bash
# Check Docker
docker --version

# Check Docker Compose
docker-compose --version

# Check Git
git --version
```

---

## Running Your First Example

### Step 1: Clone the Repository

```bash
git clone https://github.com/YOUR_USERNAME/OTLP.git
cd OTLP
```

### Step 2: Start Infrastructure

```bash
# Start OTLP Collector and Jaeger
docker-compose up -d

# Wait for services to be ready (about 10 seconds)
sleep 10

# Verify services are running
docker-compose ps
```

**Expected Output**:
```
NAME                COMMAND             STATUS              PORTS
otel-collector      ...                 Up                  4317/tcp, 4318/tcp
jaeger              ...                 Up                  16686/tcp
```

### Step 3: Run an Example

Choose your preferred language:

#### Option A: Go Example

```bash
cd examples/go
go mod download
go run .
```

#### Option B: Python Example

```bash
cd examples/python
pip install -r requirements.txt
python app.py
```

#### Option C: Java Example

```bash
cd examples/java-spring-boot
mvn spring-boot:run
```

#### Option D: Node.js Example

```bash
cd examples/nodejs-express
npm install
npm start
```

### Step 4: Generate Telemetry Data

Open a new terminal and send requests:

```bash
# Basic request
curl http://localhost:3000/api/hello?name=OpenTelemetry

# Slow request (for testing performance tracing)
curl http://localhost:3000/api/slow

# Chained operations (nested spans)
curl http://localhost:3000/api/chain
```

---

## Understanding the Results

### View Traces in Jaeger UI

1. Open your browser: [http://localhost:16686](http://localhost:16686)
2. Select service from the dropdown (e.g., `otlp-nodejs-express-demo`)
3. Click "Find Traces"
4. Click on any trace to view details

#### Understanding Trace Structure

```
Example: Chained Operations Trace

chained-operations (300ms)                      ← Root span
  ├─ operation-1 (100ms)                        ← Child span
  │   └─ db.query [postgresql] (20ms)           ← Database span
  ├─ operation-2 (150ms)                        ← Child span
  │   └─ http.request [GET api.example.com] (100ms) ← HTTP span
  └─ operation-3 (50ms)                         ← Child span
      └─ cache.get [redis:user:123] (5ms)      ← Cache span
```

**Key Information**:
- **Duration**: How long each operation took
- **Attributes**: Metadata (HTTP method, database table, etc.)
- **Events**: Important moments (e.g., "greeting_processed")
- **Errors**: Exceptions and error messages

### Trace Context in Logs

If you check your application logs, you'll see trace IDs:

```
2025-10-17 10:30:15 [info] [8a3c60f7d188f8fa79d48a391a778fa6/79d48a391a778fa6] Processing hello request
```

**Format**: `[trace_id/span_id]`

This allows you to correlate logs with traces!

---

## Next Steps

### Learning Path

**Beginner Level** (You are here ✓):
- ✅ Ran your first example
- ✅ Viewed traces in Jaeger
- ✅ Understood basic concepts

**Intermediate Level**:
1. 📖 Read [OTLP Protocol Foundation](../../标准深度梳理_2025_10/01_协议基础/README.md)
2. 🔧 Customize SDK configuration
3. 📊 Add custom metrics
4. 🐛 Implement error tracking

**Advanced Level**:
1. 📚 Study [Theoretical Framework](../../标准深度梳理_2025_10/02_THEORETICAL_FRAMEWORK/)
2. ⚡ Learn [Sampling Strategies](../../标准深度梳理_2025_10/05_采样与性能/)
3. 🚀 Explore [OTLP Arrow](../../标准深度梳理_2025_10/12_前沿技术/04_OTLP_Arrow完整指南.md)
4. 🎓 Read [Cutting-Edge Research](../../标准深度梳理_2025_10/05_采样与性能/04_前沿采样技术_2025.md)

### Recommended Resources

**Official Documentation**:
- [OpenTelemetry Official Docs](https://opentelemetry.io/docs/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

**Project Documentation**:
- [Main README](../../README.md)
- [Contributing Guide](../../CONTRIBUTING.md)
- [Code Examples](../../examples/)

**Community**:
- [GitHub Discussions](../../discussions)
- [GitHub Issues](../../issues)
- [OpenTelemetry Slack](https://cloud-native.slack.com/archives/C01N3AT62SJ)

---

## 🆘 Troubleshooting

### Problem 1: Can't Connect to OTLP Collector

**Symptom**:
```
Error: 14 UNAVAILABLE: No connection established
```

**Solution**:
1. Check if collector is running:
   ```bash
   docker ps | grep otel-collector
   ```

2. Check collector health:
   ```bash
   curl http://localhost:13133/
   ```

3. Verify port mapping in `docker-compose.yml`

### Problem 2: No Traces in Jaeger

**Possible Causes**:
1. **Wrong service name**: Check OTLP_SERVICE_NAME
2. **Sampling disabled**: Verify sampler configuration
3. **Network issue**: Ensure correct endpoint

**Debug Steps**:
1. Enable debug logging in your application
2. Check application logs for export errors
3. Verify collector logs:
   ```bash
   docker-compose logs otel-collector
   ```

### Problem 3: Docker Compose Fails

**Symptom**:
```
ERROR: yaml: line X: mapping values are not allowed here
```

**Solution**:
1. Validate YAML syntax:
   ```bash
   docker-compose config
   ```

2. Check file indentation (must use spaces, not tabs)

3. Update Docker Compose to latest version

---

## 📞 Get Help

- 💬 Ask in [GitHub Discussions](../../discussions)
- 🐛 Report issues in [GitHub Issues](../../issues)
- 📖 Read [Troubleshooting Guide](../../标准深度梳理_2025_10/08_生产部署/故障排查.md)
- 🌐 Check [OpenTelemetry FAQ](https://opentelemetry.io/docs/what-is-opentelemetry/)

---

**Congratulations! 🎉**  
You've successfully run your first OpenTelemetry example and viewed distributed traces!

**Next**: [Learn about OTLP Protocol Basics](../../标准深度梳理_2025_10/01_协议基础/README.md)

---

**Last Updated**: October 17, 2025  
**Maintainer**: OTLP Project Team

