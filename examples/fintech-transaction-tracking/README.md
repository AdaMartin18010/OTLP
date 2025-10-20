# 💰 FinTech Transaction Tracking Example (Java + Spring Boot)

> **目的**: 展示如何使用OpenTelemetry追踪金融交易处理流程，包含合规、风控和欺诈检测  
> **语言**: Java 17 + Spring Boot 3.2  
> **协议**: OTLP (OpenTelemetry Protocol)  
> **配套文档**: [数据模型与语义转换完整指南](../../📊_数据模型与语义转换完整指南_2025_10_20.md)

---

## 📋 功能特性

### 1. 自定义金融业务属性（vendor前缀：fintech.*）

本示例展示如何为金融交易定义完整的自定义属性体系：

```java
// ✅ 交易基本信息
span.setAttribute("fintech.transaction.id", transactionId);
span.setAttribute("fintech.transaction.type", "PAYMENT");
span.setAttribute("fintech.transaction.amount", 50000.00);
span.setAttribute("fintech.transaction.currency", "USD");
span.setAttribute("fintech.transaction.is_high_value", true);
span.setAttribute("fintech.transaction.is_cross_border", true);

// ✅ 风险评估属性
span.setAttribute("fintech.risk.level", "HIGH");
span.setAttribute("fintech.risk.score", 0.75);
span.setAttribute("fintech.risk.factors", "{...}");

// ✅ 欺诈检测属性
span.setAttribute("fintech.fraud.detected", true);
span.setAttribute("fintech.fraud.probability", 0.85);
span.setAttribute("fintech.fraud.indicators", "{...}");
span.setAttribute("fintech.ml.model.name", "fraud-detection-v2");
span.setAttribute("fintech.ml.model.version", "2.1.0");

// ✅ 合规属性
span.setAttribute("fintech.compliance.kyc_verified", true);
span.setAttribute("fintech.compliance.aml_checked", true);
span.setAttribute("fintech.compliance.jurisdiction", "US-SEC");
span.setAttribute("fintech.compliance.level", "pci-dss-level-1");

// ✅ 发送方/接收方属性
span.setAttribute("fintech.sender.country", "US");
span.setAttribute("fintech.receiver.country", "CN");
span.setAttribute("fintech.payment.method", "wire_transfer");
```

### 2. 标准语义约定

同时使用OpenTelemetry标准语义约定：

```java
// HTTP属性
span.setAttribute(SemanticAttributes.HTTP_METHOD, "POST");
span.setAttribute(SemanticAttributes.HTTP_ROUTE, "/api/transactions");
span.setAttribute(SemanticAttributes.HTTP_STATUS_CODE, 201);
```

### 3. 完整的金融交易处理流程

```text
http.server.process_transaction (root span)
├─ transaction.process
│   ├─ compliance.check
│   │   ├─ compliance.kyc_check
│   │   ├─ compliance.aml_check
│   │   └─ compliance.jurisdiction_check
│   │
│   ├─ risk.assess
│   │
│   └─ fraud.detect
│       └─ fraud.ml_model.predict (ML inference)
```

### 4. 关键业务事件记录

```java
// 事件1: 交易接收
span.addEvent("transaction_received");

// 事件2: 风险评估完成
span.addEvent("risk_assessment_completed", Attributes.builder()
    .put("fintech.risk.score", 0.75)
    .put("fintech.risk.level", "HIGH")
    .build());

// 事件3: 欺诈检测（仅当检测到欺诈时）
span.addEvent("fraud_detected", Attributes.builder()
    .put("fintech.fraud.probability", 0.85)
    .put("fintech.transaction.id", transactionId)
    .build());

// 事件4: 交易完成
span.addEvent("transaction_completed", Attributes.builder()
    .put("fintech.transaction.status", "FLAGGED_FOR_REVIEW")
    .build());
```

---

## 🚀 快速开始

### 前置条件

1. **Java 17+**

   ```bash
   java -version
   ```

2. **Maven 3.6+**

   ```bash
   mvn -version
   ```

3. **OTLP Collector** (运行在localhost:4318)

   使用Docker快速启动:

   ```bash
   docker run -d --name jaeger \
     -e COLLECTOR_OTLP_ENABLED=true \
     -p 16686:16686 \
     -p 4317:4317 \
     -p 4318:4318 \
     jaegertracing/all-in-one:latest
   ```

### 运行步骤

1. **编译项目**

   ```bash
   cd examples/fintech-transaction-tracking
   mvn clean package
   ```

2. **运行应用**

   ```bash
   mvn spring-boot:run
   ```

   或使用JAR:

   ```bash
   java -jar target/fintech-transaction-tracking-1.0.0.jar
   ```

   输出示例:

   ```text
   💰 FinTech Transaction Tracking Application Started
   📊 Sending transaction traces to OTLP Collector at http://localhost:4318
   🔗 API Documentation: http://localhost:8080/swagger-ui.html
   🔍 Health Check: http://localhost:8080/actuator/health
   
   📖 Example API calls:
     POST http://localhost:8080/api/transactions
     GET  http://localhost:8080/api/transactions/{id}
   ```

3. **发送测试交易**

   **示例1: 低风险交易**

   ```bash
   curl -X POST http://localhost:8080/api/transactions \
     -H "Content-Type: application/json" \
     -d '{
       "transactionId": "TXN-2024-001",
       "type": "PAYMENT",
       "amount": 99.99,
       "currency": "USD",
       "senderId": "USER-001",
       "senderAccountNumber": "ACC-US-12345",
       "senderName": "John Doe",
       "senderCountry": "US",
       "receiverId": "USER-002",
       "receiverAccountNumber": "ACC-US-67890",
       "receiverName": "Jane Smith",
       "receiverCountry": "US",
       "paymentMethod": "credit_card",
       "kycVerified": true,
       "complianceLevel": "pci-dss-level-1"
     }'
   ```

   **示例2: 高风险跨境交易**

   ```bash
   curl -X POST http://localhost:8080/api/transactions \
     -H "Content-Type: application/json" \
     -d '{
       "transactionId": "TXN-2024-002",
       "type": "TRANSFER",
       "amount": 50000.00,
       "currency": "USD",
       "senderId": "USER-003",
       "senderAccountNumber": "ACC-US-11111",
       "senderName": "Alice Brown",
       "senderCountry": "US",
       "receiverId": "USER-004",
       "receiverAccountNumber": "ACC-CN-22222",
       "receiverName": "Bob Chen",
       "receiverCountry": "CN",
       "paymentMethod": "wire_transfer",
       "kycVerified": false,
       "complianceLevel": "standard"
     }'
   ```

   **示例3: 加密货币高风险交易**

   ```bash
   curl -X POST http://localhost:8080/api/transactions \
     -H "Content-Type: application/json" \
     -d '{
       "transactionId": "TXN-2024-003",
       "type": "PAYMENT",
       "amount": 150000.00,
       "currency": "USD",
       "senderId": "USER-005",
       "senderAccountNumber": "CRYPTO-WALLET-001",
       "senderName": "Crypto User",
       "senderCountry": "XX",
       "receiverId": "USER-006",
       "receiverAccountNumber": "CRYPTO-WALLET-002",
       "receiverName": "Anonymous",
       "receiverCountry": "YY",
       "paymentMethod": "crypto",
       "kycVerified": false,
       "complianceLevel": "standard"
     }'
   ```

4. **查看追踪**

   打开浏览器访问 [http://localhost:16686](http://localhost:16686)

   在Jaeger UI中:
   - Service: 选择 `fintech-transaction-service`
   - Operation: 选择 `http.server.process_transaction`
   - 点击 "Find Traces"

---

## 📊 追踪数据展示

### Jaeger UI中的Trace视图（高风险交易示例）

```text
http.server.process_transaction [450ms] ⚠️ HIGH RISK
  service.name: fintech-transaction-service
  service.version: 1.0.0
  deployment.environment: production
  fintech.service.tier: critical
  fintech.compliance.level: pci-dss-level-1
  
  http.method: POST
  http.route: /api/transactions
  http.status_code: 202
  
  fintech.transaction.id: TXN-2024-002
  fintech.transaction.type: TRANSFER
  fintech.transaction.amount: 50000.00
  fintech.transaction.currency: USD
  fintech.transaction.is_high_value: true
  fintech.transaction.is_cross_border: true
  fintech.transaction.status: FLAGGED_FOR_REVIEW
  
  fintech.sender.country: US
  fintech.receiver.country: CN
  fintech.payment.method: wire_transfer
  
  ├─ transaction.process [420ms]
  │    fintech.transaction.id: TXN-2024-002
  │    │
  │    ├─ compliance.check [120ms]
  │    │    fintech.compliance.kyc_verified: false
  │    │    fintech.compliance.aml_checked: true
  │    │    fintech.compliance.jurisdiction: US-SEC
  │    │    │
  │    │    ├─ compliance.kyc_check [40ms]
  │    │    │    fintech.sender.id: USER-003
  │    │    │    fintech.receiver.id: USER-004
  │    │    │    fintech.compliance.kyc_verified: false
  │    │    │
  │    │    ├─ compliance.aml_check [50ms]
  │    │    │    fintech.transaction.amount: 50000.00
  │    │    │    fintech.transaction.is_cross_border: true
  │    │    │    fintech.compliance.aml_checked: true
  │    │    │
  │    │    └─ compliance.jurisdiction_check [30ms]
  │    │         fintech.sender.country: US
  │    │         fintech.receiver.country: CN
  │    │         fintech.compliance.jurisdiction: US-SEC
  │    │
  │    ├─ risk.assess [150ms]
  │    │    fintech.transaction.amount: 50000.00
  │    │    fintech.transaction.is_cross_border: true
  │    │    fintech.risk.score: 0.75
  │    │    fintech.risk.level: HIGH
  │    │    fintech.risk.factors: {"amount_risk": 0.30, ...}
  │    │    Event: risk_assessment_completed
  │    │
  │    └─ fraud.detect [150ms]
  │         fintech.transaction.id: TXN-2024-002
  │         fintech.fraud.probability: 0.85
  │         fintech.fraud.detected: true ⚠️
  │         fintech.fraud.threshold: 0.7
  │         fintech.fraud.indicators: {"ml_probability": 0.85, ...}
  │         Event: fraud_detected ⚠️
  │         │
  │         └─ fraud.ml_model.predict [50ms]
  │              fintech.ml.model.name: fraud-detection-v2
  │              fintech.ml.model.version: 2.1.0
  │              fintech.ml.prediction.probability: 0.85
```

---

## 🎯 数据模型设计

### 自定义语义约定定义

参考[数据模型指南第2部分](../../📊_数据模型与语义转换完整指南_2025_10_20.md#第二部分自定义数据模型设计)

```yaml
namespace: fintech.transaction

attributes:
  # 交易基本信息
  fintech.transaction.id:
    type: string
    requirement: required
    description: 交易唯一标识
    example: "TXN-2024-001234"
    
  fintech.transaction.type:
    type: enum
    requirement: required
    values: ["PAYMENT", "TRANSFER", "WITHDRAWAL", "DEPOSIT", "REFUND"]
    description: 交易类型
    
  fintech.transaction.amount:
    type: double
    requirement: required
    description: 交易金额
    example: 50000.00
    
  fintech.transaction.currency:
    type: string
    requirement: required
    description: 货币代码 (ISO 4217)
    example: "USD"
    
  fintech.transaction.is_high_value:
    type: boolean
    requirement: recommended
    description: 是否高额交易 (>$10,000)
    
  fintech.transaction.is_cross_border:
    type: boolean
    requirement: recommended
    description: 是否跨境交易
    
  # 风险评估属性
  fintech.risk.level:
    type: enum
    requirement: required
    values: ["LOW", "MEDIUM", "HIGH", "CRITICAL"]
    description: 风险等级
    
  fintech.risk.score:
    type: double
    requirement: required
    description: 风险评分 (0.0-1.0)
    example: 0.75
    
  fintech.risk.factors:
    type: string
    requirement: optional
    description: 风险因素JSON
    example: '{"amount_risk": 0.30, "cross_border": true}'
    
  # 欺诈检测属性
  fintech.fraud.detected:
    type: boolean
    requirement: required
    description: 是否检测到欺诈
    
  fintech.fraud.probability:
    type: double
    requirement: conditional
    description: 欺诈概率 (0.0-1.0)
    example: 0.85
    
  fintech.fraud.indicators:
    type: string
    requirement: conditional
    description: 欺诈指标JSON
    
  # ML模型属性
  fintech.ml.model.name:
    type: string
    requirement: recommended
    description: ML模型名称
    example: "fraud-detection-v2"
    
  fintech.ml.model.version:
    type: string
    requirement: recommended
    description: ML模型版本
    example: "2.1.0"
    
  # 合规属性
  fintech.compliance.kyc_verified:
    type: boolean
    requirement: required
    description: KYC验证状态
    
  fintech.compliance.aml_checked:
    type: boolean
    requirement: required
    description: AML检查状态
    
  fintech.compliance.jurisdiction:
    type: enum
    requirement: required
    values: ["US-SEC", "EU-MiFID", "UK-FCA", "INTL-FATF"]
    description: 监管司法管辖区
    
  fintech.compliance.level:
    type: enum
    requirement: recommended
    values: ["pci-dss-level-1", "pci-dss-level-2", "standard"]
    description: 合规等级
```

---

## 🔍 关键代码说明

### 1. OpenTelemetry配置（OpenTelemetryConfig.java）

```java
@Bean
public OpenTelemetry openTelemetry() {
    // 创建Resource（服务级别属性）
    Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.builder()
                    // 标准属性
                    .put(ResourceAttributes.SERVICE_NAME, "fintech-transaction-service")
                    .put(ResourceAttributes.SERVICE_VERSION, "1.0.0")
                    .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production")
                    
                    // 自定义金融服务属性
                    .put("fintech.service.tier", "critical")
                    .put("fintech.service.category", "payment-processing")
                    .put("fintech.compliance.level", "pci-dss-level-1")
                    .build()));
    
    // 创建OTLP HTTP exporter
    OtlpHttpSpanExporter spanExporter = OtlpHttpSpanExporter.builder()
            .setEndpoint("http://localhost:4318/v1/traces")
            .build();
    
    // 配置TracerProvider
    SdkTracerProvider sdkTracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(BatchSpanProcessor.builder(spanExporter)
                    .setMaxQueueSize(2048)
                    .setMaxExportBatchSize(512)
                    .build())
            .setResource(resource)
            .build();
    
    return OpenTelemetrySdk.builder()
            .setTracerProvider(sdkTracerProvider)
            .buildAndRegisterGlobal();
}
```

### 2. 控制器中的Span创建（TransactionController.java）

```java
@PostMapping
public ResponseEntity<Map<String, Object>> processTransaction(@RequestBody Transaction transaction) {
    // 创建root span
    Span span = tracer.spanBuilder("http.server.process_transaction")
            .setSpanKind(SpanKind.SERVER)
            .startSpan();
    
    try (Scope scope = span.makeCurrent()) {
        // 标准HTTP属性
        span.setAttribute(SemanticAttributes.HTTP_METHOD, "POST");
        span.setAttribute(SemanticAttributes.HTTP_ROUTE, "/api/transactions");
        
        // 自定义fintech属性
        span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
        span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
        
        // 处理交易
        Transaction processedTransaction = transactionService.processTransaction(transaction);
        
        // 添加结果属性
        span.setAttribute("fintech.transaction.status", processedTransaction.getStatus().toString());
        span.setAttribute("fintech.fraud.detected", processedTransaction.isFraudDetected());
        
        // 记录事件
        span.addEvent("transaction_processed");
        
        span.setStatus(StatusCode.OK);
        return ResponseEntity.ok(response);
        
    } catch (Exception e) {
        span.recordException(e);
        span.setStatus(StatusCode.ERROR, "Transaction failed");
        throw e;
    } finally {
        span.end();
    }
}
```

### 3. 风险评估服务（RiskAssessmentService.java）

```java
public void assessRisk(Transaction transaction) {
    Span span = tracer.spanBuilder("risk.assess").startSpan();
    
    try (Scope scope = span.makeCurrent()) {
        // 计算风险评分
        double riskScore = calculateRiskScore(transaction);
        transaction.setRiskScore(riskScore);
        
        // 确定风险等级
        RiskLevel riskLevel = determineRiskLevel(riskScore);
        transaction.setRiskLevel(riskLevel);
        
        // 添加属性
        span.setAttribute("fintech.risk.score", riskScore);
        span.setAttribute("fintech.risk.level", riskLevel.toString());
        
        // 记录事件
        span.addEvent("risk_assessment_completed");
        
        span.setStatus(StatusCode.OK);
    } finally {
        span.end();
    }
}
```

---

## 📈 实际应用场景

### 场景1: 监控高风险交易

在Jaeger UI中查询:

```text
Service: fintech-transaction-service
Tags: fintech.risk.level=HIGH OR fintech.risk.level=CRITICAL
```

### 场景2: 追踪欺诈交易

查询所有被标记为欺诈的交易:

```text
Tags: fintech.fraud.detected=true
```

分析欺诈模式：

- 哪些国家组合高风险？
- 哪些支付方式容易欺诈？
- ML模型准确性如何？

### 场景3: 合规审计

查询未通过KYC验证的交易:

```text
Tags: fintech.compliance.kyc_verified=false
```

查询特定监管区域的交易:

```text
Tags: fintech.compliance.jurisdiction=US-SEC
```

### 场景4: 性能优化

分析交易处理延迟:

- 哪个步骤最慢？（compliance/risk/fraud）
- ML模型推理延迟多少？
- 不同金额的交易处理时间差异？

---

## 🏆 最佳实践

### ✅ DO (推荐做法)

1. **使用vendor前缀**

   ```java
   span.setAttribute("fintech.transaction.id", id); // ✅ 好
   ```

2. **合规属性必须记录**

   ```java
   span.setAttribute("fintech.compliance.kyc_verified", true);
   span.setAttribute("fintech.compliance.aml_checked", true);
   ```

3. **关键事件记录**

   ```java
   span.addEvent("fraud_detected", ...);
   span.addEvent("aml_flag_raised", ...);
   ```

4. **条件属性设置**

   ```java
   if (transaction.isFraudDetected()) {
       span.setAttribute("fintech.fraud.probability", probability);
       span.setAttribute("fintech.fraud.indicators", indicators);
   }
   ```

### ❌ DON'T (避免做法)

1. ❌ 记录敏感数据明文

   ```java
   span.setAttribute("credit_card.number", "1234-5678-9012-3456"); // ❌ 违反PCI-DSS
   span.setAttribute("user.ssn", "123-45-6789");                    // ❌ 隐私违规
   ```

2. ❌ 高基数属性

   ```java
   span.setAttribute("transaction.id", uniqueId); // ❌ 无限基数
   ```

   改为：

   ```java
   span.setAttribute("fintech.transaction.id", uniqueId); // ✅ vendor前缀 + 有限采样
   ```

3. ❌ 不记录合规属性

   ```java
   // ❌ 缺少合规追踪，审计无法追溯
   ```

---

## 🔗 相关资源

### 配套文档

| 文档 | 链接 |
|------|------|
| **数据模型指南** | [📊_数据模型与语义转换完整指南_2025_10_20.md](../../📊_数据模型与语义转换完整指南_2025_10_20.md) |
| **对标分析报告** | [📊_OTLP项目2025年10月20日全面对标分析报告.md](../../📊_OTLP项目2025年10月20日全面对标分析报告.md) |
| **可视化图表** | [📊_OTLP数据生命周期可视化图表_2025_10_20.md](../../📊_OTLP数据生命周期可视化图表_2025_10_20.md) |

### OpenTelemetry官方文档

- [Java SDK文档](https://opentelemetry.io/docs/instrumentation/java/)
- [Spring Boot集成](https://opentelemetry.io/docs/instrumentation/java/automatic/spring-boot/)
- [语义约定](https://opentelemetry.io/docs/specs/semconv/)

---

## 🛠️ 故障排查

### 问题1: 连接OTLP Collector失败

**错误信息**:

```text
Failed to export spans. The request could not be executed.
```

**解决方案**:

1. 检查Collector是否运行:

   ```bash
   docker ps | grep jaeger
   ```

2. 检查endpoint配置（application.yml）:

   ```yaml
   otel.exporter.otlp.endpoint: http://localhost:4318/v1/traces
   ```

3. 测试连接:

   ```bash
   curl http://localhost:4318/v1/traces
   ```

---

### 问题2: Jaeger UI中看不到traces

**解决方案**:

1. 检查Service名称: `fintech-transaction-service`
2. 等待15-30秒（数据有延迟）
3. 检查采样配置:

   ```yaml
   otel.traces.sampler.probability: 1.0  # 确保100%采样
   ```

---

## 📊 性能建议

### 1. 批处理

已配置批处理，性能优化：

```java
BatchSpanProcessor.builder(spanExporter)
    .setMaxQueueSize(2048)
    .setMaxExportBatchSize(512)
    .setExporterTimeout(Duration.ofSeconds(30))
    .build()
```

### 2. 采样

生产环境建议使用采样：

```yaml
# application-production.yml
otel:
  traces:
    sampler:
      probability: 0.1  # 10%采样
```

但务必保留：

- 所有fraud_detected=true的交易
- 所有risk.level=HIGH/CRITICAL的交易
- 所有错误交易

（需要Collector的tail_sampling配置）

### 3. 资源池配置

```yaml
# application.yml
server:
  tomcat:
    threads:
      max: 200
      min-spare: 10
```

---

## 🎓 学习要点

### 金融行业特定关注点

1. **合规追踪**: 所有交易必须可追溯，满足PCI-DSS、AML、KYC要求
2. **敏感数据保护**: 不得记录信用卡号、SSN等敏感信息
3. **审计日志**: 关键事件必须记录（fraud_detected, aml_flag_raised等）
4. **监管报告**: 支持按jurisdiction查询，便于监管报告
5. **实时欺诈检测**: ML模型推理必须低延迟（<100ms）

---

**创建时间**: 2025年10月20日  
**作者**: OTLP项目团队  
**版本**: v1.0.0  
**Java版本**: 17  
**Spring Boot版本**: 3.2.0  
**OpenTelemetry SDK**: 1.32.0

---

**💰 Financial Tracing Made Easy!** ✨
