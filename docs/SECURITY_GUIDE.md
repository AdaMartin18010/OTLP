# OpenTelemetry 安全指南

> 📚 **文档导航**: [返回文档索引](INDEX.md) | [部署指南](DEPLOYMENT_GUIDE.md) | [性能优化](PERFORMANCE_GUIDE.md) | [故障排除](TROUBLESHOOTING.md)
> 最后更新: 2025-09-17

## 目录

- OpenTelemetry 安全指南

---

## 1. 安全威胁模型

### 1.1 数据泄露风险

- **敏感信息**: 密码、令牌、个人信息
- **业务数据**: 用户ID、订单信息、财务数据
- **系统信息**: 内部架构、配置信息

### 1.2 攻击向量

- **网络攻击**: 中间人攻击、数据包嗅探
- **认证绕过**: 未授权访问、权限提升
- **数据篡改**: 恶意修改遥测数据

## 2. 传输安全

### 2.1 TLS配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          cert_file: /etc/otel-collector/certs/server.crt
          key_file: /etc/otel-collector/certs/server.key
          client_ca_file: /etc/otel-collector/certs/ca.crt
```

### 2.2 mTLS配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otel-collector/certs/server.crt
          key_file: /etc/otel-collector/certs/server.key
          client_ca_file: /etc/otel-collector/certs/ca.crt
          require_client_cert: true
```

## 3. 认证和授权

### 3.1 OAuth2认证

```yaml
extensions:
  oauth2client:
    client_id: "${OAUTH2_CLIENT_ID}"
    client_secret: "${OAUTH2_CLIENT_SECRET}"
    token_url: "https://auth.example.com/oauth/token"
    scopes: ["otel-collector"]
    timeout: 5s

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: oauth2client
```

### 3.2 JWT认证

```yaml
extensions:
  jwt:
    issuer: "https://auth.example.com"
    audience: "otel-collector"
    public_key: "/etc/otel-collector/certs/jwt-public.key"
    algorithm: "RS256"

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: jwt
```

### 3.3 访问控制

```yaml
extensions:
  access_control:
    rules:
      - path: "/v1/traces"
        methods: ["POST"]
        roles: ["admin", "user"]
      - path: "/v1/metrics"
        methods: ["POST"]
        roles: ["admin", "user"]
      - path: "/health"
        methods: ["GET"]
        roles: ["admin", "user", "monitor"]
```

## 4. 数据保护

### 4.1 敏感数据过滤

```yaml
processors:
  attributes:
    actions:
      - key: "password"
        action: "delete"
      - key: "token"
        action: "delete"
      - key: "secret"
        action: "delete"
      - key: "key"
        action: "delete"
      - key: "auth"
        action: "delete"
      - key: "credit_card"
        action: "delete"
      - key: "ssn"
        action: "delete"
      - key: "email"
        action: "hash"
      - key: "phone"
        action: "hash"
      - key: "user_id"
        action: "hash"
```

### 4.2 数据脱敏

```yaml
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          - merge_maps(attributes, {"sensitive": false}, "upsert")
    metric_statements:
      - context: metric
        statements:
          - merge_maps(attributes, {"sensitive": false}, "upsert")
    log_statements:
      - context: log
        statements:
          - merge_maps(attributes, {"sensitive": false}, "upsert")
```

### 4.3 数据加密

```yaml
processors:
  encryption:
    algorithm: "AES-256-GCM"
    key: "${ENCRYPTION_KEY}"
```

## 5. 网络安全

### 5.1 防火墙配置

```bash
# 只允许特定IP访问
iptables -A INPUT -p tcp --dport 4317 -s 192.168.1.0/24 -j ACCEPT
iptables -A INPUT -p tcp --dport 4317 -j DROP

# 限制连接数
iptables -A INPUT -p tcp --dport 4317 -m connlimit --connlimit-above 100 -j DROP
```

### 5.2 网络分段

```yaml
# 使用专用网络
networks:
  otel-network:
    driver: bridge
    ipam:
      config:
        - subnet: 172.20.0.0/16
```

### 5.3 速率限制

```yaml
extensions:
  rate_limit:
    requests_per_second: 100
    burst_size: 200
    window_size: 60s
```

## 6. 存储安全

### 6.1 加密存储

```yaml
exporters:
  secure_storage:
    type: "encrypted_file"
    path: "/secure/otel-data"
    encryption_key: "${STORAGE_ENCRYPTION_KEY}"
    compression: "gzip"
```

### 访问控制

```bash
# 设置文件权限
chmod 600 /etc/otel-collector/certs/*.key
chmod 644 /etc/otel-collector/certs/*.crt
chown otel-collector:otel-collector /etc/otel-collector/certs/
```

## 7. 审计和监控

### 7.1 审计日志

```yaml
processors:
  audit:
    enabled: true
    log_file: "/var/log/otel-collector/audit.log"
    events:
      - "data_received"
      - "data_processed"
      - "data_exported"
      - "error_occurred"
      - "authentication_failed"
      - "authorization_denied"
```

### 7.2 安全监控

```yaml
# 监控安全事件
groups:
- name: security-alerts
  rules:
  - alert: AuthenticationFailure
    expr: rate(otelcol_authentication_failures[5m]) > 10
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "High authentication failure rate"
  
  - alert: UnauthorizedAccess
    expr: rate(otelcol_authorization_denials[5m]) > 5
    for: 1m
    labels:
      severity: warning
    annotations:
      summary: "Unauthorized access attempts"
```

## 8. 合规性

### 8.1 GDPR合规

```yaml
processors:
  gdpr_compliance:
    data_retention_days: 30
    anonymize_personal_data: true
    allow_data_export: true
    allow_data_deletion: true
```

### 8.2 PCI-DSS合规

```yaml
processors:
  pci_compliance:
    mask_card_numbers: true
    encrypt_sensitive_data: true
    audit_all_access: true
    restrict_data_access: true
```

### 8.3 HIPAA合规

```yaml
processors:
  hipaa_compliance:
    encrypt_phi: true
    audit_access: true
    restrict_phi_access: true
    data_minimization: true
```

## 9. 密钥管理

### 9.1 密钥轮换

```bash
# 自动密钥轮换脚本
#!/bin/bash
# 生成新密钥
openssl genrsa -out new-key.pem 2048
openssl req -new -key new-key.pem -out new-cert.csr
openssl x509 -req -in new-cert.csr -signkey new-key.pem -out new-cert.crt

# 更新配置
kubectl create secret tls otel-collector-tls --cert=new-cert.crt --key=new-key.pem --dry-run=client -o yaml | kubectl apply -f -

# 重启服务
kubectl rollout restart deployment/otel-collector
```

### 9.2 密钥存储

```yaml
# 使用外部密钥管理系统
extensions:
  vault:
    endpoint: "https://vault.example.com"
    token: "${VAULT_TOKEN}"
    path: "secret/otel-collector"
```

## 10. 安全最佳实践

### 10.1 配置安全

- 使用强密码和密钥
- 定期轮换密钥
- 限制配置文件权限

### 10.2 网络安全

- 使用TLS/mTLS加密
- 配置防火墙规则
- 实施网络分段

### 10.3 数据保护

- 过滤敏感数据
- 实施数据脱敏
- 加密存储数据

### 10.4 访问控制

- 实施最小权限原则
- 使用多因素认证
- 定期审查权限

### 10.5 监控和审计

- 记录所有安全事件
- 监控异常行为
- 定期安全审计

## 11. 高级安全配置

### 11.1 零信任架构

#### 11.1.1 服务网格安全

```yaml
# Istio安全配置
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: otel-collector-mtls
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  mtls:
    mode: STRICT

---
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: otel-collector-authz
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  rules:
  - from:
    - source:
        principals: ["cluster.local/ns/default/sa/my-app"]
    to:
    - operation:
        methods: ["POST"]
        paths: ["/v1/traces", "/v1/metrics"]
```

#### 11.1.2 网络策略

```yaml
# Kubernetes网络策略
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otel-collector-netpol
  namespace: observability
spec:
  podSelector:
    matchLabels:
      app: otel-collector
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: default
    - namespaceSelector:
        matchLabels:
          name: production
    ports:
    - protocol: TCP
      port: 4317
    - protocol: TCP
      port: 4318
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: observability
    ports:
    - protocol: TCP
      port: 14250
    - protocol: TCP
      port: 9090
```

### 11.2 数据加密

#### 11.2.1 端到端加密

```yaml
# 端到端加密配置
processors:
  encryption:
    algorithm: "AES-256-GCM"
    key: "${ENCRYPTION_KEY}"
    key_rotation_interval: "24h"
    compression: "gzip"

exporters:
  otlp:
    endpoint: "https://collector:4317"
    tls:
      cert_file: /etc/otel/certs/client.crt
      key_file: /etc/otel/certs/client.key
      ca_file: /etc/otel/certs/ca.crt
    headers:
      "X-Encryption": "AES-256-GCM"
      "X-Key-ID": "${ENCRYPTION_KEY_ID}"
```

#### 4.2 数据脱敏1

```yaml
# 高级数据脱敏
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # 脱敏敏感数据
          - replace_pattern(attributes["user.email"], "^(.*)@(.*)$", "***@$2")
          - replace_pattern(attributes["user.phone"], "^(\\d{3})\\d{4}(\\d{4})$", "$1****$2")
          - replace_pattern(attributes["credit_card"], "\\d{4}-\\d{4}-\\d{4}-(\\d{4})", "****-****-****-$1")
          # 删除敏感字段
          - delete_key(attributes, "password") where attributes["password"] != nil
          - delete_key(attributes, "token") where attributes["token"] != nil
          - delete_key(attributes, "secret") where attributes["secret"] != nil
```

### 11.3 访问控制

#### 11.3.1 基于角色的访问控制

```yaml
# RBAC配置
extensions:
  rbac:
    rules:
      - principal: "user:admin"
        permissions: ["read", "write", "delete"]
        resources: ["traces", "metrics", "logs"]
      - principal: "user:developer"
        permissions: ["read", "write"]
        resources: ["traces", "metrics"]
      - principal: "user:viewer"
        permissions: ["read"]
        resources: ["traces", "metrics", "logs"]
      - principal: "service:my-app"
        permissions: ["write"]
        resources: ["traces", "metrics"]
```

#### 11.3.2 属性基于访问控制

```yaml
# ABAC配置
extensions:
  abac:
    rules:
      - principal: "user:admin"
        conditions:
          - attribute: "tenant.id"
            operator: "equals"
            value: "admin-tenant"
        permissions: ["read", "write", "delete"]
      - principal: "user:developer"
        conditions:
          - attribute: "tenant.id"
            operator: "equals"
            value: "dev-tenant"
        permissions: ["read", "write"]
```

### 11.4 安全监控

#### 11.4.1 实时安全监控

```yaml
# 安全监控配置
processors:
  security_monitor:
    enabled: true
    rules:
      - name: "suspicious_activity"
        condition: "rate(authentication_failures[5m]) > 10"
        action: "alert"
        severity: "high"
      - name: "data_exfiltration"
        condition: "rate(large_data_transfers[5m]) > 100MB"
        action: "block"
        severity: "critical"
      - name: "privilege_escalation"
        condition: "rate(permission_denials[5m]) > 50"
        action: "alert"
        severity: "medium"
```

#### 11.4.2 安全事件响应

```yaml
# 安全事件响应配置
extensions:
  security_response:
    rules:
      - name: "block_suspicious_ip"
        trigger: "authentication_failure_rate > 20"
        action: "block_ip"
        duration: "1h"
      - name: "rate_limit_user"
        trigger: "user_request_rate > 1000"
        action: "rate_limit"
        duration: "30m"
      - name: "disable_user"
        trigger: "consecutive_failures > 5"
        action: "disable_user"
        duration: "24h"
```

### 11.5 合规性管理

#### 11.5.1 GDPR合规

```yaml
# GDPR合规配置
processors:
  gdpr_compliance:
    enabled: true
    data_retention_days: 30
    anonymize_personal_data: true
    allow_data_export: true
    allow_data_deletion: true
    consent_management: true
    data_processing_records: true
    privacy_impact_assessment: true
```

#### SOX合规

```yaml
# SOX合规配置
processors:
  sox_compliance:
    enabled: true
    audit_trail: true
    access_controls: true
    data_integrity: true
    change_management: true
    risk_assessment: true
    compliance_reporting: true
```

### 11.6 威胁检测

#### 11.6.1 异常检测

```yaml
# 异常检测配置
processors:
  anomaly_detection:
    enabled: true
    algorithms:
      - name: "statistical"
        threshold: 3.0
        window_size: "5m"
      - name: "machine_learning"
        model: "isolation_forest"
        threshold: 0.1
    features:
      - "request_rate"
      - "error_rate"
      - "response_time"
      - "data_volume"
```

#### 11.6.2 行为分析

```yaml
# 行为分析配置
processors:
  behavior_analysis:
    enabled: true
    baseline_period: "7d"
    analysis_interval: "1h"
    thresholds:
      - metric: "request_pattern"
        threshold: 0.8
      - metric: "data_access_pattern"
        threshold: 0.7
      - metric: "time_pattern"
        threshold: 0.6
```

## 12. 安全工具和脚本

### 12.1 安全扫描工具

#### 12.1.1 漏洞扫描脚本

```bash
#!/bin/bash
# security-scan.sh

echo "=== OpenTelemetry 安全扫描 ==="

# 检查TLS配置
echo "检查TLS配置..."
openssl s_client -connect localhost:4317 -servername localhost < /dev/null 2>/dev/null | openssl x509 -noout -text

# 检查端口安全
echo "检查端口安全..."
nmap -sS -O localhost

# 检查文件权限
echo "检查文件权限..."
find /etc/otel-collector -type f -exec ls -la {} \;

# 检查环境变量
echo "检查环境变量..."
env | grep -i secret
env | grep -i password
env | grep -i key

# 检查网络连接
echo "检查网络连接..."
netstat -tuln | grep -E "(4317|4318|13133)"

echo "=== 安全扫描完成 ==="
```

#### 12.1.2 配置安全验证

```bash
#!/bin/bash
# config-security-check.sh

CONFIG_FILE=${1:-"config.yaml"}

echo "=== 配置文件安全检查 ==="

# 检查敏感信息
echo "检查敏感信息..."
if grep -i "password\|secret\|key\|token" "$CONFIG_FILE"; then
    echo "⚠ 发现可能的敏感信息"
else
    echo "✓ 未发现敏感信息"
fi

# 检查TLS配置
echo "检查TLS配置..."
if grep -q "tls:" "$CONFIG_FILE"; then
    echo "✓ 发现TLS配置"
    if grep -q "insecure: true" "$CONFIG_FILE"; then
        echo "⚠ 发现不安全的TLS配置"
    else
        echo "✓ TLS配置安全"
    fi
else
    echo "⚠ 未发现TLS配置"
fi

# 检查认证配置
echo "检查认证配置..."
if grep -q "auth:" "$CONFIG_FILE"; then
    echo "✓ 发现认证配置"
else
    echo "⚠ 未发现认证配置"
fi

echo "=== 配置文件安全检查完成 ==="
```

### 12.2 安全监控脚本

#### 12.2.1 实时安全监控

```bash
#!/bin/bash
# security-monitor.sh

echo "=== OpenTelemetry 安全监控 ==="

while true; do
    # 检查认证失败
    auth_failures=$(curl -s http://localhost:13133/metrics | grep otelcol_authentication_failures | awk '{print $2}')
    if [ "$auth_failures" -gt 10 ]; then
        echo "⚠ 认证失败次数过高: $auth_failures"
    fi
    
    # 检查授权拒绝
    auth_denials=$(curl -s http://localhost:13133/metrics | grep otelcol_authorization_denials | awk '{print $2}')
    if [ "$auth_denials" -gt 5 ]; then
        echo "⚠ 授权拒绝次数过高: $auth_denials"
    fi
    
    # 检查异常请求
    suspicious_requests=$(curl -s http://localhost:13133/metrics | grep otelcol_suspicious_requests | awk '{print $2}')
    if [ "$suspicious_requests" -gt 0 ]; then
        echo "⚠ 发现可疑请求: $suspicious_requests"
    fi
    
    sleep 60
done
```

#### 安全事件响应

```bash
#!/bin/bash
# security-response.sh

echo "=== OpenTelemetry 安全事件响应 ==="

# 检查安全事件
SECURITY_EVENTS=$(curl -s http://localhost:13133/metrics | grep -E "(authentication_failures|authorization_denials|suspicious_requests)")

# 处理认证失败
AUTH_FAILURES=$(echo "$SECURITY_EVENTS" | grep authentication_failures | awk '{print $2}')
if [ "$AUTH_FAILURES" -gt 20 ]; then
    echo "🚨 检测到大量认证失败，启动响应措施"
    # 阻止可疑IP
    # 发送告警
    # 记录安全事件
fi

# 处理授权拒绝
AUTH_DENIALS=$(echo "$SECURITY_EVENTS" | grep authorization_denials | awk '{print $2}')
if [ "$AUTH_DENIALS" -gt 10 ]; then
    echo "🚨 检测到大量授权拒绝，启动响应措施"
    # 限制用户访问
    # 发送告警
    # 记录安全事件
fi

echo "=== 安全事件响应完成 ==="
```

### 12.3 安全测试工具

#### 12.3.1 渗透测试脚本

```bash
#!/bin/bash
# penetration-test.sh

echo "=== OpenTelemetry 渗透测试 ==="

# 测试认证绕过
echo "测试认证绕过..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[]}' \
  --max-time 5

# 测试SQL注入
echo "测试SQL注入..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[{"resource":{"attributes":[{"key":"db.statement","value":"SELECT * FROM users WHERE id = 1 OR 1=1"}]}}]}' \
  --max-time 5

# 测试XSS
echo "测试XSS..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[{"resource":{"attributes":[{"key":"user.agent","value":"<script>alert(\"XSS\")</script>"}]}}]}' \
  --max-time 5

# 测试CSRF
echo "测试CSRF..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -H "Origin: http://malicious-site.com" \
  -d '{"resourceSpans":[]}' \
  --max-time 5

echo "=== 渗透测试完成 ==="
```

#### 12.3.2 安全配置测试

```bash
#!/bin/bash
# security-config-test.sh

echo "=== OpenTelemetry 安全配置测试 ==="

# 测试TLS配置
echo "测试TLS配置..."
openssl s_client -connect localhost:4317 -servername localhost < /dev/null 2>/dev/null | grep -E "(Protocol|Cipher|Verify)"

# 测试认证配置
echo "测试认证配置..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[]}' \
  --max-time 5

# 测试授权配置
echo "测试授权配置..."
curl -X GET http://localhost:13133/ \
  --max-time 5

# 测试数据过滤
echo "测试数据过滤..."
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[{"resource":{"attributes":[{"key":"password","value":"secret123"}]}}]}' \
  --max-time 5

echo "=== 安全配置测试完成 ==="
```

## 13. 安全检查清单

### 13.1 部署前检查

- [ ] 启用TLS/mTLS
- [ ] 配置认证和授权
- [ ] 设置数据过滤规则
- [ ] 配置审计日志
- [ ] 设置安全监控
- [ ] 实施网络分段
- [ ] 配置防火墙规则
- [ ] 设置访问控制
- [ ] 启用威胁检测
- [ ] 配置安全响应

### 13.2 运行时检查

- [ ] 监控安全指标
- [ ] 检查访问日志
- [ ] 验证数据保护
- [ ] 测试故障恢复
- [ ] 更新安全补丁
- [ ] 检查异常行为
- [ ] 验证合规性
- [ ] 测试安全响应
- [ ] 检查密钥状态
- [ ] 验证备份安全

### 13.3 定期检查

- [ ] 安全配置审查
- [ ] 权限审计
- [ ] 密钥轮换
- [ ] 安全测试
- [ ] 合规性检查
- [ ] 漏洞扫描
- [ ] 渗透测试
- [ ] 安全培训
- [ ] 事件响应演练
- [ ] 安全策略更新
