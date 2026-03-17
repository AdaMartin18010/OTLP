---
title: Collector安全加固指南
description: OpenTelemetry Collector生产环境安全加固完整方案
category: 运维实践
tags:
  - security
  - hardening
  - tls
version: Collector v0.147.0
date: 2026-03-17
status: published
---

# Collector安全加固指南

> **安全等级**: 企业级  
> **最后更新**: 2026-03-17  

---

## 1. TLS配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          min_version: "1.3"
```

## 2. mTLS配置

```yaml
tls:
  cert_file: /etc/otel/certs/server.crt
  key_file: /etc/otel/certs/server.key
  client_ca_file: /etc/otel/certs/ca.crt
  client_auth_type: require_and_verify_client_cert
```

---

**最后更新**: 2026-03-17  
**状态**: Published
