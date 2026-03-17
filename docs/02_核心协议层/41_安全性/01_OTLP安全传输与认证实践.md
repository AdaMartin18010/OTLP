---
title: OTLP安全传输与认证实践
description: OpenTelemetry Protocol安全传输配置，包括TLS/mTLS设置、认证机制和敏感数据处理
category: 核心协议
tags:
  - security
  - tls
  - mtls
  - authentication
  - encryption
version: OTLP v1.9.0
date: 2026-03-17
status: published
---

# OTLP安全传输与认证实践

> **安全等级**: 企业级  
> **适用场景**: 生产环境、多租户、合规要求  
> **最后更新**: 2026-03-17  

---

## 1. 安全传输概述

### 1.1 传输安全层级

```
┌─────────────────────────────────────────────────────────────┐
│                    OTLP传输安全层级                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Level 1: 无加密 (不推荐)                                    │
│  └── 仅用于开发和测试环境                                     │
│                                                             │
│  Level 2: TLS (传输层加密) ✓ 最低要求                        │
│  └── 证书验证 + 加密传输                                      │
│                                                             │
│  Level 3: mTLS (双向认证) ✓✓ 推荐                            │
│  └── 客户端+服务端双向证书认证                                │
│                                                             │
│  Level 4: mTLS + 认证令牌 ✓✓✓ 高安全                        │
│  └── 双向证书 + API Token认证                                │
│                                                             │
│  Level 5: 零信任架构 ✓✓✓✓ 最高安全                          │
│  └── mTLS + SPIFFE/SPIRE + 动态授权                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 2. TLS配置

### 2.1 基础TLS配置

```yaml
# Collector服务端TLS
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          # 可选: 客户端证书验证
          client_ca_file: /etc/otel/certs/ca.crt
          # 可选: 客户端证书要求
          client_auth_type: require_and_verify_client_cert

      http:
        endpoint: 0.0.0.0:4318
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key

# 客户端TLS配置
exporters:
  otlp:
    endpoint: collector:4317
    tls:
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      ca_file: /etc/otel/certs/ca.crt
      # 跳过证书验证 (仅测试)
      insecure_skip_verify: false
```

### 2.2 证书管理

```bash
#!/bin/bash
# 生成自签名证书 (仅用于测试)

# CA私钥
openssl genrsa -out ca.key 4096

# CA证书
openssl req -new -x509 -days 365 -key ca.key -out ca.crt \
  -subj "/CN=otel-ca/O=MyOrg"

# 服务端证书
openssl genrsa -out server.key 2048
openssl req -new -key server.key -out server.csr \
  -subj "/CN=otel-collector/O=MyOrg"
openssl x509 -req -days 365 -in server.csr -CA ca.crt -CAkey ca.key \
  -CAcreateserial -out server.crt

# 客户端证书
openssl genrsa -out client.key 2048
openssl req -new -key client.key -out client.csr \
  -subj "/CN=otel-client/O=MyOrg"
openssl x509 -req -days 365 -in client.csr -CA ca.crt -CAkey ca.key \
  -CAcreateserial -out client.crt
```

---

## 3. 认证机制

### 3.1 API Token认证

```yaml
# 使用extensions提供认证
extensions:
  bearertokenauth:
    token: ${env:OTEL_AUTH_TOKEN}
    # 或从文件读取
    # filename: /etc/otel/auth/token

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        auth:
          authenticator: bearertokenauth

service:
  extensions: [bearertokenauth]
```

### 3.2 OIDC认证

```yaml
extensions:
  oidc:
    issuer_url: https://auth.example.com
    audience: otel-collector
    # 可选: 自定义声明验证
    username_claim: sub
    groups_claim: groups

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: oidc
```

---

## 4. 敏感数据处理

### 4.1 数据脱敏

```yaml
processors:
  # 属性脱敏
  attributes/redaction:
    actions:
      # 删除敏感属性
      - key: password
        action: delete
      - key: token
        action: delete
      - key: api_key
        action: delete
      
      # 哈希处理
      - key: user.email
        action: hash
      
      # 掩码处理
      - key: credit_card
        action: mask
        pattern: ^(\d{4})-.*-(\d{4})$
        replace_with: $1-****-$2
      
      # 部分脱敏
      - key: phone
        action: mask
        pattern: ^(\d{3}).*(\d{4})$
        replace_with: $1****$2

  # 日志内容过滤
  filter/sensitive:
    logs:
      exclude:
        match_type: regexp
        bodies:
          - "password.*=.*"
          - "token.*=.*"
          - "api_key.*=.*"
```

---

**最后更新**: 2026-03-17  
**状态**: Published
