# OTLP容错架构

**文档版本**: 1.0.0  
**创建日期**: 2025年10月7日  
**所属**: 第二部分 - 容错机制与策略  

---

## 目录

- [OTLP容错架构](#otlp容错架构)
  - [目录](#目录)
  - [概述](#概述)
  - [2.2.1 分层容错架构](#221-分层容错架构)
  - [2.2.2 SDK层容错](#222-sdk层容错)
    - [本地缓冲策略](#本地缓冲策略)
    - [降级策略](#降级策略)
  - [2.2.3 Collector层容错](#223-collector层容错)
    - [高可用架构](#高可用架构)
    - [数据持久化（WAL）](#数据持久化wal)
    - [过载保护](#过载保护)
  - [总结](#总结)

---

## 概述

本文档详细介绍OTLP的分层容错架构，包括SDK层、传输层、Collector层和存储层的容错机制。

---

## 2.2.1 分层容错架构

```text
┌─────────────────────────────────────────────────────────────┐
│                     应用层容错                               │
│  • SDK容错：本地缓冲、异步导出、降级策略                       │
│  • 应用容错：优雅降级、熔断、限流                              │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                     传输层容错                               │
│  • 重试机制：指数退避、抖动                                   │
│  • 负载均衡：轮询、最少连接、一致性哈希                        │
│  • 故障转移：主备切换、多活                                   │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                    Collector层容错                           │
│  • 高可用：主备、集群、分片                                   │
│  • 数据持久化：WAL、检查点                                    │
│  • 过载保护：限流、背压、丢弃策略                              │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                     存储层容错                               │
│  • 数据冗余：多副本、纠删码                                   │
│  • 故障检测：心跳、健康检查                                   │
│  • 自动恢复：副本重建、数据修复                               │
└─────────────────────────────────────────────────────────────┘
```

---

## 2.2.2 SDK层容错

### 本地缓冲策略

**环形缓冲区（无锁）**：

```go
// 环形缓冲区（无锁）
type RingBuffer struct {
    buffer []Span
    head   uint64
    tail   uint64
    mask   uint64
}

func NewRingBuffer(size int) *RingBuffer {
    // size必须是2的幂
    if size&(size-1) != 0 {
        panic("size must be power of 2")
    }
    return &RingBuffer{
        buffer: make([]Span, size),
        mask:   uint64(size - 1),
    }
}

func (rb *RingBuffer) Push(span Span) bool {
    head := atomic.LoadUint64(&rb.head)
    tail := atomic.LoadUint64(&rb.tail)
    
    // 检查是否满
    if head-tail >= uint64(len(rb.buffer)) {
        return false // 缓冲区满，丢弃
    }
    
    // 写入
    rb.buffer[head&rb.mask] = span
    atomic.StoreUint64(&rb.head, head+1)
    return true
}

func (rb *RingBuffer) Pop() (Span, bool) {
    head := atomic.LoadUint64(&rb.head)
    tail := atomic.LoadUint64(&rb.tail)
    
    // 检查是否空
    if head == tail {
        return Span{}, false
    }
    
    // 读取
    span := rb.buffer[tail&rb.mask]
    atomic.StoreUint64(&rb.tail, tail+1)
    return span, true
}
```

### 降级策略

**采样降级**：

```go
// 采样降级
type AdaptiveSampler struct {
    targetRate    float64
    currentRate   float64
    errorRate     float64
    mu            sync.RWMutex
}

func (s *AdaptiveSampler) ShouldSample(span Span) bool {
    s.mu.RLock()
    rate := s.currentRate
    s.mu.RUnlock()
    
    return rand.Float64() < rate
}

func (s *AdaptiveSampler) AdjustRate(metrics Metrics) {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 根据错误率调整采样率
    if metrics.ErrorRate > s.errorRate {
        // 错误率高，降低采样率减轻压力
        s.currentRate *= 0.9
    } else if metrics.CPUUsage < 0.7 {
        // 资源充足，提高采样率
        s.currentRate = min(s.currentRate*1.1, s.targetRate)
    }
}

// 功能降级
type FeatureFlag struct {
    enabled map[string]bool
    mu      sync.RWMutex
}

func (f *FeatureFlag) IsEnabled(feature string) bool {
    f.mu.RLock()
    defer f.mu.RUnlock()
    return f.enabled[feature]
}

func (f *FeatureFlag) Disable(feature string) {
    f.mu.Lock()
    defer f.mu.Unlock()
    f.enabled[feature] = false
}

// 使用示例
if featureFlag.IsEnabled("detailed_attributes") {
    span.SetAttribute("http.request.body", body)
} else {
    // 降级：不记录详细属性
    span.SetAttribute("http.request.size", len(body))
}
```

---

## 2.2.3 Collector层容错

### 高可用架构

```yaml
# 主备模式
collectors:
  - name: primary
    endpoint: collector-primary:4317
    role: primary
    priority: 100
    
  - name: secondary
    endpoint: collector-secondary:4317
    role: standby
    priority: 50

# 集群模式
collectors:
  - name: collector-1
    endpoint: collector-1:4317
    shard: 0
    
  - name: collector-2
    endpoint: collector-2:4317
    shard: 1
    
  - name: collector-3
    endpoint: collector-3:4317
    shard: 2

# 负载均衡
load_balancer:
  strategy: consistent_hash  # round_robin, least_conn, consistent_hash
  hash_key: trace_id
  health_check:
    interval: 10s
    timeout: 5s
    unhealthy_threshold: 3
    healthy_threshold: 2
```

### 数据持久化（WAL）

**Write-Ahead Log实现**：

```go
// Write-Ahead Log
type WAL struct {
    file      *os.File
    buffer    *bufio.Writer
    offset    int64
    mu        sync.Mutex
}

func (w *WAL) Append(data []byte) (int64, error) {
    w.mu.Lock()
    defer w.mu.Unlock()
    
    // 写入长度前缀
    length := uint32(len(data))
    if err := binary.Write(w.buffer, binary.LittleEndian, length); err != nil {
        return 0, err
    }
    
    // 写入数据
    if _, err := w.buffer.Write(data); err != nil {
        return 0, err
    }
    
    // 写入校验和
    checksum := crc32.ChecksumIEEE(data)
    if err := binary.Write(w.buffer, binary.LittleEndian, checksum); err != nil {
        return 0, err
    }
    
    // 刷新到磁盘
    if err := w.buffer.Flush(); err != nil {
        return 0, err
    }
    
    offset := w.offset
    w.offset += int64(4 + len(data) + 4)
    return offset, nil
}

func (w *WAL) Replay(handler func([]byte) error) error {
    // 从头读取WAL
    if _, err := w.file.Seek(0, io.SeekStart); err != nil {
        return err
    }
    
    reader := bufio.NewReader(w.file)
    for {
        // 读取长度
        var length uint32
        if err := binary.Read(reader, binary.LittleEndian, &length); err != nil {
            if err == io.EOF {
                break
            }
            return err
        }
        
        // 读取数据
        data := make([]byte, length)
        if _, err := io.ReadFull(reader, data); err != nil {
            return err
        }
        
        // 读取校验和
        var checksum uint32
        if err := binary.Read(reader, binary.LittleEndian, &checksum); err != nil {
            return err
        }
        
        // 验证校验和
        if crc32.ChecksumIEEE(data) != checksum {
            return errors.New("checksum mismatch")
        }
        
        // 处理数据
        if err := handler(data); err != nil {
            return err
        }
    }
    return nil
}
```

### 过载保护

**令牌桶限流**：

```go
// 令牌桶限流
type TokenBucket struct {
    capacity  int64
    tokens    int64
    rate      int64  // tokens per second
    lastTime  time.Time
    mu        sync.Mutex
}

func (tb *TokenBucket) Allow() bool {
    tb.mu.Lock()
    defer tb.mu.Unlock()
    
    now := time.Now()
    elapsed := now.Sub(tb.lastTime)
    tb.lastTime = now
    
    // 添加新令牌
    newTokens := int64(elapsed.Seconds() * float64(tb.rate))
    tb.tokens = min(tb.tokens+newTokens, tb.capacity)
    
    // 消费令牌
    if tb.tokens > 0 {
        tb.tokens--
        return true
    }
    return false
}

// 背压机制
type BackpressureController struct {
    queueSize    int
    maxQueueSize int
    mu           sync.RWMutex
}

func (bc *BackpressureController) ShouldApplyBackpressure() bool {
    bc.mu.RLock()
    defer bc.mu.RUnlock()
    
    utilization := float64(bc.queueSize) / float64(bc.maxQueueSize)
    return utilization > 0.8 // 80%阈值
}

func (bc *BackpressureController) GetBackpressureDelay() time.Duration {
    bc.mu.RLock()
    defer bc.mu.RUnlock()
    
    utilization := float64(bc.queueSize) / float64(bc.maxQueueSize)
    if utilization > 0.9 {
        return 100 * time.Millisecond
    } else if utilization > 0.8 {
        return 50 * time.Millisecond
    }
    return 0
}

// 丢弃策略
type DropPolicy interface {
    ShouldDrop(span Span) bool
}

// 基于优先级的丢弃
type PriorityDropPolicy struct {
    threshold float64
}

func (p *PriorityDropPolicy) ShouldDrop(span Span) bool {
    priority := span.GetPriority()
    return priority < p.threshold
}

// 基于采样的丢弃
type SamplingDropPolicy struct {
    dropRate float64
}

func (p *SamplingDropPolicy) ShouldDrop(span Span) bool {
    return rand.Float64() < p.dropRate
}
```

---

## 总结

OTLP容错架构采用分层设计：

**SDK层**：

- 本地缓冲（环形缓冲区）
- 采样降级
- 功能降级

**传输层**：

- 重试机制（指数退避）
- 负载均衡
- 故障转移

**Collector层**：

- 高可用（主备/集群）
- WAL持久化
- 过载保护（限流/背压/丢弃）

**存储层**：

- 多副本冗余
- 健康检查
- 自动恢复

---

**上一篇**: [05_容错理论基础.md](05_容错理论基础.md)  
**下一篇**: [07_容错性能分析.md](07_容错性能分析.md)

---

*最后更新: 2025年10月7日*:
