# 🐳 OTLP Docker部署完整指南

> **目标**: 帮助用户使用Docker快速部署OTLP环境  
> **适用场景**: 开发、测试、小规模生产环境  
> **更新时间**: 2025年10月20日

---

## 📋 目录

- [🐳 OTLP Docker部署完整指南](#-otlp-docker部署完整指南)
  - [📋 目录](#-目录)
  - [🚀 环境准备](#-环境准备)
    - [1. 安装Docker](#1-安装docker)
      - [Linux](#linux)
      - [macOS](#macos)
      - [Windows](#windows)
    - [2. 安装Docker Compose](#2-安装docker-compose)
  - [🎯 快速开始](#-快速开始)
    - [1. 最小化部署](#1-最小化部署)
    - [2. 创建Collector配置](#2-创建collector配置)
    - [3. 启动服务](#3-启动服务)
    - [4. 验证部署](#4-验证部署)
  - [🏗️ 完整部署](#️-完整部署)
    - [1. 完整的docker-compose.yml](#1-完整的docker-composeyml)
    - [2. Prometheus配置](#2-prometheus配置)
    - [3. 高级Collector配置](#3-高级collector配置)
  - [⚙️ 配置管理](#️-配置管理)
    - [1. 环境变量配置](#1-环境变量配置)
    - [2. 多环境配置](#2-多环境配置)
  - [📊 监控和日志](#-监控和日志)
    - [1. 查看日志](#1-查看日志)
    - [2. 监控指标](#2-监控指标)
    - [3. 健康检查](#3-健康检查)
  - [🔧 故障排查](#-故障排查)
    - [1. 容器无法启动](#1-容器无法启动)
    - [2. 连接问题](#2-连接问题)
    - [3. 性能问题](#3-性能问题)
    - [4. 数据丢失](#4-数据丢失)
  - [📋 常用命令](#-常用命令)
    - [管理服务](#管理服务)
    - [调试和维护](#调试和维护)
    - [备份和恢复](#备份和恢复)
  - [🎯 最佳实践](#-最佳实践)
    - [1. 资源限制](#1-资源限制)
    - [2. 健康检查](#2-健康检查)
    - [3. 日志管理](#3-日志管理)
    - [4. 网络隔离](#4-网络隔离)
    - [5. 安全配置](#5-安全配置)
  - [🔗 相关资源](#-相关资源)

---

## 🚀 环境准备

### 1. 安装Docker

#### Linux

```bash
# Ubuntu/Debian
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh

# CentOS/RHEL
sudo yum install -y docker-ce docker-ce-cli containerd.io

# 启动Docker
sudo systemctl start docker
sudo systemctl enable docker

# 添加当前用户到docker组
sudo usermod -aG docker $USER
```

#### macOS

```bash
# 使用Homebrew
brew install --cask docker

# 或下载Docker Desktop
# https://www.docker.com/products/docker-desktop
```

#### Windows

```powershell
# 下载Docker Desktop for Windows
# https://www.docker.com/products/docker-desktop

# 或使用Chocolatey
choco install docker-desktop
```

### 2. 安装Docker Compose

```bash
# Linux
sudo curl -L "https://github.com/docker/compose/releases/download/v2.20.0/docker-compose-$(uname -s)-$(uname -m)" -o /usr/local/bin/docker-compose
sudo chmod +x /usr/local/bin/docker-compose

# 验证安装
docker --version
docker-compose --version
```

**预期输出**:

```text
Docker version 24.0.0, build xyz
Docker Compose version v2.20.0
```

---

## 🎯 快速开始

### 1. 最小化部署

创建 `docker-compose.yml`:

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    container_name: otel-collector
    command: ["--config=/etc/otel-config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "13133:13133" # Health check
      - "8888:8888"   # Metrics
    restart: unless-stopped

  # Jaeger - 追踪后端
  jaeger:
    image: jaegertracing/all-in-one:latest
    container_name: jaeger
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
    restart: unless-stopped

networks:
  default:
    name: otlp-network
```

### 2. 创建Collector配置

创建 `otel-config.yaml`:

```yaml
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
    send_batch_size: 512
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  logging:
    loglevel: info

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [jaeger, logging]
```

### 3. 启动服务

```bash
# 启动所有服务
docker-compose up -d

# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f otel-collector
```

### 4. 验证部署

```bash
# 健康检查
curl http://localhost:13133/

# 访问Jaeger UI
open http://localhost:16686

# 发送测试数据
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{
    "resourceSpans": [{
      "resource": {
        "attributes": [{"key": "service.name", "value": {"stringValue": "test-service"}}]
      },
      "scopeSpans": [{
        "spans": [{
          "traceId": "5B8EFFF798038103D269B633813FC60C",
          "spanId": "EEE19B7EC3C1B174",
          "name": "test-span",
          "kind": 1,
          "startTimeUnixNano": "1000000000000000000",
          "endTimeUnixNano": "1000000001000000000"
        }]
      }]
    }]
  }'
```

✅ **快速部署完成！**

---

## 🏗️ 完整部署

### 1. 完整的docker-compose.yml

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    container_name: otel-collector
    command: ["--config=/etc/otel-config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel-config.yaml
      - ./logs:/logs
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "13133:13133" # Health check
      - "8888:8888"   # Prometheus metrics
      - "55679:55679" # zpages
    environment:
      - OTEL_RESOURCE_ATTRIBUTES=service.name=otel-collector,service.version=1.0.0
    mem_limit: 2g
    mem_reservation: 1g
    restart: unless-stopped
    networks:
      - otlp-network
    depends_on:
      - jaeger
      - prometheus
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:13133/"]
      interval: 30s
      timeout: 10s
      retries: 3

  # Jaeger - 分布式追踪
  jaeger:
    image: jaegertracing/all-in-one:latest
    container_name: jaeger
    environment:
      - COLLECTOR_OTLP_ENABLED=true
      - SPAN_STORAGE_TYPE=badger
      - BADGER_EPHEMERAL=false
      - BADGER_DIRECTORY_VALUE=/badger/data
      - BADGER_DIRECTORY_KEY=/badger/key
    volumes:
      - jaeger-data:/badger
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
      - "6831:6831/udp" # Thrift compact
    restart: unless-stopped
    networks:
      - otlp-network

  # Prometheus - 指标存储
  prometheus:
    image: prom/prometheus:latest
    container_name: prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    restart: unless-stopped
    networks:
      - otlp-network

  # Grafana - 可视化
  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-provisioning:/etc/grafana/provisioning
    ports:
      - "3000:3000"
    restart: unless-stopped
    networks:
      - otlp-network
    depends_on:
      - prometheus

  # Elasticsearch - 日志存储（可选）
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.10.0
    container_name: elasticsearch
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
      - "ES_JAVA_OPTS=-Xms512m -Xmx512m"
    volumes:
      - es-data:/usr/share/elasticsearch/data
    ports:
      - "9200:9200"
    restart: unless-stopped
    networks:
      - otlp-network

volumes:
  jaeger-data:
  prometheus-data:
  grafana-data:
  es-data:

networks:
  otlp-network:
    driver: bridge
```

### 2. Prometheus配置

创建 `prometheus.yml`:

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  # Collector自身指标
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
        labels:
          service: 'otel-collector'
  
  # Prometheus自身指标
  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']
```

### 3. 高级Collector配置

创建 `otel-config.yaml`:

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 16
        max_concurrent_streams: 100
      http:
        endpoint: 0.0.0.0:4318
  
  # Prometheus指标接收
  prometheus:
    config:
      scrape_configs:
        - job_name: 'collector'
          scrape_interval: 10s
          static_configs:
            - targets: ['localhost:8888']

processors:
  # 内存限制
  memory_limiter:
    check_interval: 1s
    limit_mib: 1024
    spike_limit_mib: 256
  
  # 批处理
  batch:
    timeout: 1s
    send_batch_size: 512
    send_batch_max_size: 1024
  
  # Resource检测
  resourcedetection:
    detectors: [env, system, docker]
    timeout: 5s
  
  # 属性处理
  attributes:
    actions:
      - key: environment
        value: production
        action: insert
      - key: http.request.header.authorization
        action: delete
  
  # 智能采样
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    policies:
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      - name: slow
        type: latency
        latency:
          threshold_ms: 1000
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10

exporters:
  # Jaeger
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  # Prometheus
  prometheus:
    endpoint: 0.0.0.0:8889
  
  # Elasticsearch
  elasticsearch:
    endpoints: [http://elasticsearch:9200]
    traces_index: traces
    logs_index: logs
  
  # 日志输出
  logging:
    loglevel: info
    sampling_initial: 5
    sampling_thereafter: 200

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  
  pprof:
    endpoint: 0.0.0.0:1777
  
  zpages:
    endpoint: 0.0.0.0:55679

service:
  extensions: [health_check, pprof, zpages]
  
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection, attributes, tail_sampling, batch]
      exporters: [jaeger, elasticsearch, logging]
    
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, batch]
      exporters: [prometheus, logging]
    
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [elasticsearch, logging]
  
  telemetry:
    logs:
      level: info
    metrics:
      address: 0.0.0.0:8888
```

---

## ⚙️ 配置管理

### 1. 环境变量配置

创建 `.env` 文件:

```bash
# Collector配置
OTEL_COLLECTOR_IMAGE=otel/opentelemetry-collector-contrib:latest
OTEL_COLLECTOR_MEMORY_LIMIT=2g

# Jaeger配置
JAEGER_IMAGE=jaegertracing/all-in-one:latest
JAEGER_STORAGE_TYPE=badger

# Prometheus配置
PROMETHEUS_IMAGE=prom/prometheus:latest
PROMETHEUS_RETENTION=15d

# Grafana配置
GRAFANA_IMAGE=grafana/grafana:latest
GRAFANA_ADMIN_PASSWORD=admin123

# 网络配置
OTLP_GRPC_PORT=4317
OTLP_HTTP_PORT=4318
JAEGER_UI_PORT=16686
```

在 `docker-compose.yml` 中使用:

```yaml
services:
  otel-collector:
    image: ${OTEL_COLLECTOR_IMAGE}
    mem_limit: ${OTEL_COLLECTOR_MEMORY_LIMIT}
    ports:
      - "${OTLP_GRPC_PORT}:4317"
      - "${OTLP_HTTP_PORT}:4318"
```

### 2. 多环境配置

```bash
# 开发环境
docker-compose --env-file .env.dev up -d

# 测试环境
docker-compose --env-file .env.test up -d

# 生产环境
docker-compose --env-file .env.prod up -d
```

---

## 📊 监控和日志

### 1. 查看日志

```bash
# 查看所有服务日志
docker-compose logs -f

# 查看特定服务日志
docker-compose logs -f otel-collector

# 查看最近100行日志
docker-compose logs --tail=100 otel-collector

# 保存日志到文件
docker-compose logs otel-collector > collector.log
```

### 2. 监控指标

访问以下端点查看指标:

```bash
# Collector指标
curl http://localhost:8888/metrics

# Prometheus UI
open http://localhost:9090

# Grafana Dashboard
open http://localhost:3000
# 默认用户名/密码: admin/admin
```

### 3. 健康检查

```bash
# Collector健康检查
curl http://localhost:13133/

# Jaeger健康检查
curl http://localhost:16686/

# Prometheus健康检查
curl http://localhost:9090/-/healthy
```

---

## 🔧 故障排查

### 1. 容器无法启动

```bash
# 检查容器状态
docker-compose ps

# 查看容器日志
docker-compose logs otel-collector

# 检查端口占用
netstat -tuln | grep 4317
lsof -i :4317

# 检查配置文件
docker-compose config
```

### 2. 连接问题

```bash
# 测试容器网络
docker network inspect otlp-network

# 进入容器调试
docker exec -it otel-collector sh

# 从容器内测试连接
ping jaeger
nc -zv jaeger 14250
```

### 3. 性能问题

```bash
# 查看资源使用
docker stats

# 查看特定容器资源
docker stats otel-collector

# 增加资源限制
# 在docker-compose.yml中修改
services:
  otel-collector:
    mem_limit: 4g
    cpus: 2
```

### 4. 数据丢失

```bash
# 检查Collector处理指标
curl http://localhost:8888/metrics | grep dropped

# 检查批处理队列
curl http://localhost:8888/metrics | grep queue

# 增加队列大小
# 在otel-config.yaml中修改
exporters:
  jaeger:
    sending_queue:
      queue_size: 10000
```

---

## 📋 常用命令

### 管理服务

```bash
# 启动所有服务
docker-compose up -d

# 停止所有服务
docker-compose down

# 重启特定服务
docker-compose restart otel-collector

# 停止并删除所有容器、网络、卷
docker-compose down -v

# 更新镜像
docker-compose pull
docker-compose up -d
```

### 调试和维护

```bash
# 进入容器
docker exec -it otel-collector sh

# 查看容器配置
docker inspect otel-collector

# 复制文件到容器
docker cp local-file.yaml otel-collector:/etc/

# 从容器复制文件
docker cp otel-collector:/etc/otel-config.yaml ./backup.yaml

# 清理未使用的资源
docker system prune -a
```

### 备份和恢复

```bash
# 备份卷
docker run --rm -v jaeger-data:/data -v $(pwd):/backup alpine \
  tar czf /backup/jaeger-backup.tar.gz -C /data .

# 恢复卷
docker run --rm -v jaeger-data:/data -v $(pwd):/backup alpine \
  tar xzf /backup/jaeger-backup.tar.gz -C /data

# 导出容器配置
docker-compose config > docker-compose-backup.yml
```

---

## 🎯 最佳实践

### 1. 资源限制

```yaml
services:
  otel-collector:
    mem_limit: 2g
    mem_reservation: 1g
    cpus: 1.5
    
    deploy:
      resources:
        limits:
          memory: 2G
        reservations:
          memory: 1G
```

### 2. 健康检查

```yaml
services:
  otel-collector:
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:13133/"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
```

### 3. 日志管理

```yaml
services:
  otel-collector:
    logging:
      driver: "json-file"
      options:
        max-size: "100m"
        max-file: "3"
```

### 4. 网络隔离

```yaml
networks:
  frontend:
    driver: bridge
  backend:
    driver: bridge
    internal: true  # 不允许外部访问

services:
  otel-collector:
    networks:
      - frontend
      - backend
  
  jaeger:
    networks:
      - backend  # 仅内部访问
```

### 5. 安全配置

```yaml
services:
  otel-collector:
    # 不以root运行
    user: "1000:1000"
    
    # 只读根文件系统
    read_only: true
    
    # 安全选项
    security_opt:
      - no-new-privileges:true
    
    # 临时文件系统
    tmpfs:
      - /tmp
```

---

## 🔗 相关资源

- [🎯 5分钟快速入门](🎯_5分钟快速入门指南.md) - 快速开始
- [🔧 故障排查手册](🔧_故障排查完整手册.md) - 解决问题
- [⚡ 性能优化指南](⚡_性能优化完整指南.md) - 优化性能
- [Collector配置示例](examples/collector-configurations/README.md) - 配置参考

---

**更新时间**: 2025年10月20日  
**版本**: v1.0.0  
**维护者**: OTLP项目团队

---

**🐳 使用Docker快速部署OTLP环境！** 🚀
