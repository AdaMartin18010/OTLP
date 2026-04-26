# Security 规范补充

> **标准来源**: OpenTelemetry Specification v1.56.0 — Security Considerations + Best Practices
> **核心目标**: 补充 OpenTelemetry 官方安全规范的核心要点，与本项目现有安全文档形成完整覆盖

---

## 一、官方安全规范概览

### 1.1 规范来源

OpenTelemetry 官方安全内容分散在多个章节：

```text
安全相关内容分布:
├── Specification Overview: Security Principles
├── OTLP Protocol: TLS, Authentication, Compression
├── SDK Configuration: Environment Variable Security
├── Semantic Conventions: PII (Personally Identifiable Information) 处理
└── Library Guidelines: Safe Defaults, No Blocking

本项目已有安全文档:
├── docs/02_核心协议层/41_安全性/01_OTLP安全传输与认证实践.md
├── docs/02_核心协议层/41_安全性/02_mTLS双向认证完整配置.md
├── docs/04_部署运维层/41_安全合规/01_安全_安全加固完整清单.md
├── docs/04_部署运维层/41_安全合规/02_数据隐私合规.md
└── docs/04_部署运维层/41_安全合规/03_2025年最新安全威胁与防护_CVE_MFA.md
```

本文档聚焦于**规范层面的安全要求**，与现有实践文档互补。

---

## 二、核心安全原则

### 2.1 官方安全原则

OpenTelemetry 规范定义了以下安全原则，所有实现都必须遵守：

| 原则 | 说明 | 规范来源 |
|------|------|---------|
| **默认安全** | SDK 默认配置应是安全的，不应需要额外配置才能达到基本安全 | Library Guidelines |
| **不泄露敏感信息** | 遥测数据不得包含密码、Token、密钥等敏感信息 | Semantic Conventions |
| **最小权限** | Collector 组件应以最小权限运行，限制文件系统和网络访问 | Deployment Best Practices |
| **不阻塞** | 安全机制的实现不得阻塞业务线程 | Performance Spec |
| **可审计** | 安全相关配置和操作应可审计 | Security Guidelines |

### 2.2 敏感信息清单

以下信息**禁止**出现在遥测数据中：

```text
禁止项:
├── 密码和密钥
│   ├── 数据库密码
│   ├── API Key / Secret Key
│   ├── JWT Token（完整Token）
│   └── 私钥内容
│
├── 个人身份信息（PII）
│   ├── 身份证号
│   ├── 手机号（完整号码）
│   ├── 银行卡号
│   ├── 邮箱地址（视合规要求）
│   └── 生物识别数据
│
├── 业务敏感信息
│   ├── 内部 IP 地址和架构细节（视场景）
│   ├── 商业机密参数
│   └── 客户原始数据
│
└── 例外情况:
    ├── 经哈希/脱敏处理后的标识符可以使用
    └── 内部系统间的追踪通常不受 PII 限制，但需遵循组织政策
```

---

## 三、OTLP 协议安全要求

### 3.1 传输层安全

| 要求 | 规范 | 说明 |
|------|------|------|
| **TLS 加密** | 必须支持 | 生产环境必须启用 TLS |
| **证书验证** | 默认启用 | 默认验证服务端证书 |
| **mTLS** | 推荐 | 高安全场景启用双向认证 |
| **加密套件** | 现代标准 | 禁用 TLS 1.0/1.1，优先 TLS 1.3 |

### 3.2 认证机制

```text
OTLP 支持的认证方式:

1. 无认证（开发/测试环境）
   └── 规范允许，但生产环境不推荐

2. API Key / Token（HTTP Header）
   ├── Authorization: Bearer <token>
   └── 简单，但 Token 管理成本高

3. mTLS（双向 TLS）
   ├── 客户端证书认证
   ├── 最安全，适合零信任环境
   └── 证书管理复杂

4. OAuth 2.0 / OIDC（扩展）
   ├── 通过 Token 交换实现
   └── 部分后端支持

规范要求:
├── 服务端必须支持至少一种认证机制
├── 认证失败应返回明确的错误码
│   ├── gRPC: UNAUTHENTICATED (16)
│   └── HTTP: 401 Unauthorized
└── 认证信息不得通过 URL 参数传递
```

### 3.3 拒绝服务防护

```text
OTLP 实现必须考虑的 DoS 防护:

请求大小限制:
├── 最大请求体: 建议 4MB - 16MB
├── 最大消息数: 单请求建议不超过 10,000 条
└── 超限处理: 返回 INVALID_ARGUMENT (gRPC) 或 400 (HTTP)

速率限制:
├── 按客户端 IP / API Key 限流
├── 推荐使用 Token Bucket 算法
└── 超限返回 RESOURCE_EXHAUSTED (gRPC) 或 429 (HTTP)

连接限制:
├── 最大并发连接数
├── 连接超时配置
└── 空闲连接清理
```

---

## 四、SDK 安全规范

### 4.1 环境变量安全

```text
环境变量安全要求:

敏感配置:
├── OTEL_EXPORTER_OTLP_HEADERS: 可能包含 Token
│   └── 规范要求: 不得记录到日志中
├── OTEL_EXPORTER_OTLP_CERTIFICATE / CLIENT_KEY: 证书路径
│   └── 规范要求: 文件权限应为 600（仅所有者可读）
└── 其他环境变量: 一般视为非敏感

日志输出:
├── SDK 日志（诊断日志）不得输出环境变量的完整值
│   └── 特别是包含认证信息的变量
└── 错误信息不得泄露内部路径或配置细节
```

### 4.2 Baggage 安全

```text
Baggage 安全要求（规范层面）:

大小限制:
├── 总大小: 8192 字节（W3C 规范）
├── 单条目: 4096 字节
└── 实现应强制执行此限制，防止超大头攻击

内容限制:
├── 不得传播密码、Token、密钥
├── 下游服务不得盲信 Baggage 中的权限相关值
└── 对外部第三方服务的出站请求应考虑剥离 Baggage
```

---

## 五、Collector 安全规范

### 5.1 最小权限原则

```text
Collector 部署的安全要求:

进程权限:
├── 不以 root 运行
├── 限制文件系统访问（只读配置，只写日志/临时目录）
├── 限制网络访问（仅必要的出站端口）
└── 使用容器安全上下文:
    ├── runAsNonRoot: true
    ├── readOnlyRootFilesystem: true
    └── allowPrivilegeEscalation: false

配置安全:
├── 配置文件权限: 644 或更严格
├── 敏感值（Token、密码）应通过 Secret 管理
│   └── Kubernetes Secret、Vault、环境变量
└── 配置验证: 启动时验证配置语法和安全性
```

### 5.2 处理器安全

```text
Processor 安全注意事项:

属性处理器（Attributes Processor）:
├── 插入敏感属性时注意安全
├── 不得将环境变量中的敏感信息插入 Span
└── 建议: 使用 Resource 处理器替代，Resource 通常更安全

Transform Processor（OTTL）:
├── OTTL 表达式可能访问任意属性
├── 避免在 OTTL 中硬编码敏感值
└── 限制 OTTL 表达式的执行环境（沙箱）

自定义 Processor:
├── 遵循最小权限
├── 输入验证: 验证所有外部输入
└── 错误处理: 不得因 Processor 错误导致数据丢失
```

---

## 六、合规与隐私

### 6.1 GDPR / 个人信息保护合规

```text
遥测数据处理合规要点:

数据最小化:
├── 只收集必要的遥测数据
├── 默认不收集 PII
└── 如需收集，明确配置并记录

数据主体权利:
├── 删除权: 能够按用户 ID 删除其所有追踪数据
├── 可携带权: 导出特定用户的数据
└── 访问权: 查询特定用户的数据

数据处理协议（DPA）:
├── 如果使用第三方可观测性后端
├── 确保签订 DPA
└── 明确数据存储位置和保留期
```

### 6.2 数据保留与销毁

```text
规范建议:
├── 默认保留期: 7-30 天（高基数追踪数据）
├── 聚合指标: 可保留更长时间（1 年以上）
├── 自动清理: 配置 TTL 或生命周期策略
└── 加密存储: 静态数据加密（at-rest encryption）
```

---

## 七、安全检查清单

基于官方规范的安全合规检查：

### OTLP 传输

- [ ] 生产环境启用 TLS（最低 TLS 1.2，推荐 TLS 1.3）
- [ ] 验证服务端证书（默认开启，不跳过）
- [ ] 高安全场景启用 mTLS
- [ ] 认证 Token 不硬编码在配置文件中

### SDK

- [ ] 诊断日志不包含敏感环境变量值
- [ ] Baggage 不包含密码或 Token
- [ ] 默认采样策略不泄露业务逻辑

### Collector

- [ ] 不以 root 运行
- [ ] 配置文件权限正确（644 或更严格）
- [ ] 敏感值通过 Secret 管理
- [ ] 启用请求大小限制和速率限制
- [ ] 定期更新到最新版本（安全补丁）

### 数据

- [ ] 遥测数据不包含未脱敏的 PII
- [ ] 配置数据保留和自动清理策略
- [ ] 静态数据加密存储

---

## 八、与本项目现有安全文档的关系

| 本文档（规范层面） | 现有文档（实践层面） | 关系 |
|------------------|---------------------|------|
| 安全原则与规范要求 | `01_OTLP安全传输与认证实践.md` | 规范 → 实践 |
| TLS/mTLS 规范 | `02_mTLS双向认证完整配置.md` | 规范 → 配置示例 |
| 加固清单（规范项） | `01_安全_安全加固完整清单.md` | 补充规范依据 |
| PII 与合规 | `02_数据隐私合规.md` | 规范 → 合规指南 |
| CVE 与威胁 | `03_2025年最新安全威胁与防护_CVE_MFA.md` | 规范 + 最新威胁 |

---

## 九、参考资源

- OpenTelemetry Specification: Security Considerations
- OpenTelemetry Specification: OTLP Security
- W3C Trace Context: Privacy Considerations
- CNCF Security Best Practices for Observability

---

> **总结**: 本文档从 OpenTelemetry 官方规范层面补充了安全原则、OTLP 协议安全要求、SDK 环境变量安全、Collector 最小权限、数据隐私合规等内容。与项目现有安全实践文档形成"规范依据 + 实践指南"的互补体系，共同构成完整的安全知识覆盖。
