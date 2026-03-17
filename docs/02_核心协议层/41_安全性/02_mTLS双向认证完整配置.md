---
title: mTLS双向认证完整配置
description: OpenTelemetry Collector生产环境mTLS双向认证完整配置指南，包括证书管理、轮换策略和故障排查
category: 核心协议
tags:
  - mtls
  - tls
  - security
  - certificates
  - authentication
version: OTLP v1.10.0
date: 2026-03-17
status: published
---

# mTLS双向认证完整配置

> **安全等级**: 企业级
> **适用场景**: 生产环境、金融级应用
> **最后更新**: 2026-03-17

---

## 1. mTLS概述

### 1.1 什么是mTLS

```
mTLS (Mutual TLS) = 双向TLS认证

标准TLS:                mTLS:
┌─────────┐            ┌─────────┐
│ Client  │───TLS───►  │ Server  │
└─────────┘            └─────────┘
仅需客户端验证服务端证书

┌─────────┐            ┌─────────┐
│ Client  │◄──mTLS──►  │ Server  │
└─────────┘            └─────────┘
客户端验证服务端 + 服务端验证客户端

优势:
✓ 双向身份验证
✓ 防止中间人攻击
✓ 细粒度访问控制
✓ 符合合规要求
```

### 1.2 mTLS握手流程

```
1. Client Hello
   └── 支持的TLS版本、密码套件

2. Server Hello + Certificate
   └── 服务端证书 + 请求客户端证书

3. Client Certificate
   └── 客户端证书

4. 双向验证
   ├── 客户端验证服务端证书
   │   └── CA签名验证 + 域名匹配
   └── 服务端验证客户端证书
       └── CA签名验证 + 权限检查

5. 密钥交换 + 加密通信
```

---

## 2. 证书管理

### 2.1 生成CA和证书

```bash
#!/bin/bash
# generate-certs.sh - 生成mTLS所需证书

set -e

CERT_DIR="./certs"
mkdir -p $CERT_DIR

# 1. 生成CA私钥
echo "=== 生成CA私钥 ==="
openssl genrsa -out $CERT_DIR/ca.key 4096

# 2. 生成CA证书 (10年有效期)
echo "=== 生成CA证书 ==="
openssl req -new -x509 -days 3650 \
    -key $CERT_DIR/ca.key \
    -out $CERT_DIR/ca.crt \
    -subj "/CN=OTel-CA/O=MyOrg/C=US"

# 3. 生成服务端私钥
echo "=== 生成服务端私钥 ==="
openssl genrsa -out $CERT_DIR/server.key 2048

# 4. 生成服务端CSR
echo "=== 生成服务端CSR ==="
openssl req -new \
    -key $CERT_DIR/server.key \
    -out $CERT_DIR/server.csr \
    -subj "/CN=otel-collector/O=MyOrg/C=US" \
    -config <(cat <<EOF
[req]
distinguished_name = req_distinguished_name
req_extensions = v3_req
[req_distinguished_name]
[v3_req]
basicConstraints = CA:FALSE
keyUsage = nonRepudiation, digitalSignature, keyEncipherment
subjectAltName = @alt_names
[alt_names]
DNS.1 = localhost
DNS.2 = otel-collector
DNS.3 = otel-collector.monitoring
IP.1 = 127.0.0.1
IP.2 = 0.0.0.0
EOF
)

# 5. 使用CA签名服务端证书
openssl x509 -req -days 365 \
    -in $CERT_DIR/server.csr \
    -CA $CERT_DIR/ca.crt \
    -CAkey $CERT_DIR/ca.key \
    -CAcreateserial \
    -out $CERT_DIR/server.crt \
    -extensions v3_req \
    -extfile <(cat <<EOF
[v3_req]
basicConstraints = CA:FALSE
keyUsage = nonRepudiation, digitalSignature, keyEncipherment
subjectAltName = @alt_names
[alt_names]
DNS.1 = localhost
DNS.2 = otel-collector
DNS.3 = otel-collector.monitoring
IP.1 = 127.0.0.1
IP.2 = 0.0.0.0
EOF
)

# 6. 生成客户端私钥
echo "=== 生成客户端私钥 ==="
openssl genrsa -out $CERT_DIR/client.key 2048

# 7. 生成客户端CSR
echo "=== 生成客户端CSR ==="
openssl req -new \
    -key $CERT_DIR/client.key \
    -out $CERT_DIR/client.csr \
    -subj "/CN=otel-client/O=MyOrg/C=US"

# 8. 使用CA签名客户端证书
openssl x509 -req -days 365 \
    -in $CERT_DIR/client.csr \
    -CA $CERT_DIR/ca.crt \
    -CAkey $CERT_DIR/ca.key \
    -CAcreateserial \
    -out $CERT_DIR/client.crt

echo "=== 证书生成完成 ==="
echo "文件列表:"
ls -la $CERT_DIR/
```

### 2.2 Kubernetes Secret管理

```yaml
# 将证书存储为K8s Secret
apiVersion: v1
kind: Secret
metadata:
  name: otel-mtls-certs
  namespace: observability
type: Opaque
data:
  ca.crt: $(cat certs/ca.crt | base64 -w0)
  server.crt: $(cat certs/server.crt | base64 -w0)
  server.key: $(cat certs/server.key | base64 -w0)
---
apiVersion: v1
kind: Secret
metadata:
  name: otel-client-certs
  namespace: default
type: Opaque
data:
  ca.crt: $(cat certs/ca.crt | base64 -w0)
  client.crt: $(cat certs/client.crt | base64 -w0)
  client.key: $(cat certs/client.key | base64 -w0)
```

---

## 3. Collector mTLS配置

### 3.1 服务端配置

```yaml
# collector-mtls.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          # 服务端证书
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key

          # CA证书用于验证客户端
          client_ca_file: /etc/otel/certs/ca.crt

          # 要求客户端证书
          client_auth_type: require_and_verify_client_cert

          # 最小TLS版本
          min_version: "1.3"

          # 允许的密码套件
          cipher_suites:
            - TLS_AES_256_GCM_SHA384
            - TLS_CHACHA20_POLY1305_SHA256

          # 证书轮换热加载
          reload_interval: 1h

      http:
        endpoint: 0.0.0.0:4318
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          client_ca_file: /etc/otel/certs/ca.crt
          client_auth_type: require_and_verify_client_cert

exporters:
  # 导出到其他Collector也使用mTLS
  otlp/backend:
    endpoint: backend-collector:4317
    tls:
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      ca_file: /etc/otel/certs/ca.crt
      insecure_skip_verify: false
      server_name_override: backend-collector
```

### 3.2 Kubernetes部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: collector-mtls
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: collector-mtls
  template:
    metadata:
      labels:
        app: collector-mtls
    spec:
      containers:
        - name: collector
          image: otel/opentelemetry-collector-contrib:0.147.0
          args:
            - --config=/etc/otel/collector-mtls.yaml
          volumeMounts:
            - name: config
              mountPath: /etc/otel
            - name: certs
              mountPath: /etc/otel/certs
              readOnly: true
          resources:
            requests:
              cpu: "500m"
              memory: "1Gi"
      volumes:
        - name: config
          configMap:
            name: collector-mtls-config
        - name: certs
          secret:
            secretName: otel-mtls-certs
            items:
              - key: ca.crt
                path: ca.crt
              - key: server.crt
                path: server.crt
              - key: server.key
                path: server.key
```

---

## 4. 客户端配置

### 4.1 Go SDK mTLS配置

```go
package main

import (
    "crypto/tls"
    "crypto/x509"
    "fmt"
    "io/ioutil"

    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
)

func createMTLSConfig() (*tls.Config, error) {
    // 加载客户端证书
    cert, err := tls.LoadX509KeyPair("certs/client.crt", "certs/client.key")
    if err != nil {
        return nil, fmt.Errorf("failed to load client cert: %w", err)
    }

    // 加载CA证书
    caCert, err := ioutil.ReadFile("certs/ca.crt")
    if err != nil {
        return nil, fmt.Errorf("failed to load CA cert: %w", err)
    }

    certPool := x509.NewCertPool()
    certPool.AppendCertsFromPEM(caCert)

    return &tls.Config{
        Certificates: []tls.Certificate{cert},
        RootCAs:      certPool,
        MinVersion:   tls.VersionTLS13,
        CipherSuites: []uint16{
            tls.TLS_AES_256_GCM_SHA384,
            tls.TLS_CHACHA20_POLY1305_SHA256,
        },
    }, nil
}

func initTracer() error {
    tlsConfig, err := createMTLSConfig()
    if err != nil {
        return err
    }

    creds := credentials.NewTLS(tlsConfig)

    exporter, err := otlptracegrpc.New(
        context.Background(),
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithTLSCredentials(creds),
    )
    if err != nil {
        return err
    }

    // ... 配置Tracer Provider
    return nil
}
```

### 4.2 Java SDK mTLS配置

```java
// Java SDK mTLS配置
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.grpc.netty.GrpcSslContexts;
import io.netty.handler.ssl.SslContext;
import io.netty.handler.ssl.SslContextBuilder;

import javax.net.ssl.SSLException;
import java.io.File;

public class MTLSConfig {

    public static OtlpGrpcSpanExporter createMTLSExporter() throws SSLException {
        // 创建SSL上下文
        SslContext sslContext = GrpcSslContexts.forClient()
            .trustManager(new File("certs/ca.crt"))
            .keyManager(
                new File("certs/client.crt"),
                new File("certs/client.key")
            )
            .build();

        return OtlpGrpcSpanExporter.builder()
            .setEndpoint("https://otel-collector:4317")
            .setSslContext(sslContext)
            .build();
    }
}
```

---

## 5. 证书轮换

### 5.1 自动轮换方案

```yaml
# 使用cert-manager自动管理证书
apiVersion: cert-manager.io/v1
kind: Issuer
metadata:
  name: otel-ca-issuer
  namespace: observability
spec:
  ca:
    secretName: otel-ca-secret
---
apiVersion: cert-manager.io/v1
kind: Certificate
metadata:
  name: otel-server-cert
  namespace: observability
spec:
  secretName: otel-server-tls
  issuerRef:
    name: otel-ca-issuer
    kind: Issuer
  dnsNames:
    - otel-collector
    - otel-collector.monitoring
    - otel-collector.monitoring.svc.cluster.local
  ipAddresses:
    - 127.0.0.1
  # 自动轮换 (30天有效期，15天前开始轮换)
  duration: 720h  # 30天
  renewBefore: 360h  # 15天
  privateKey:
    rotationPolicy: Always
```

### 5.2 Collector热加载

```yaml
# Collector支持证书热加载
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otel/certs/server.crt
          key_file: /etc/otel/certs/server.key
          client_ca_file: /etc/otel/certs/ca.crt
          # 证书文件变化时自动重新加载
          reload_interval: 1h
```

---

## 6. 故障排查

### 6.1 常见问题

```
问题1: "bad certificate"
原因:
├── 客户端证书过期
├── 证书不在CA信任链
├── 域名不匹配
└── 证书格式错误

排查:
openssl verify -CAfile ca.crt client.crt
openssl x509 -in client.crt -text -noout

问题2: "certificate has expired"
原因: 证书已过期
解决: 重新生成证书或启用自动轮换

问题3: "unknown authority"
原因: CA证书不匹配
解决: 确保双方使用相同CA
```

### 6.2 调试命令

```bash
# 测试mTLS连接
openssl s_client -connect otel-collector:4317 \
    -cert client.crt \
    -key client.key \
    -CAfile ca.crt \
    -tls1_3

# 检查证书详细信息
openssl x509 -in server.crt -text -noout | grep -A2 "Subject Alternative Name"

# 验证证书链
openssl crl2pkcs7 -nocrl -certfile server.crt | openssl pkcs7 -print_certs -noout
```

---

**最后更新**: 2026-03-17
**维护者**: OTLP安全团队
**状态**: Published
