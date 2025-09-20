# 基准测试状态概览

## 目标

提供采样/批处理/队列参数的吞吐与延迟基准测试

## 完成度

### ✅ 已完成

1. **基准测试脚本**
   - `benchmarks/run-rust.ps1` - Rust 基准测试脚本
   - `benchmarks/run-go.ps1` - Go 基准测试脚本
   - `benchmarks/run-python.ps1` - Python 基准测试脚本

2. **测试报告模板**
   - `benchmarks/REPORT_TEMPLATE.md` - 标准化的测试报告模板

3. **测试配置**
   - 支持 gRPC 和 HTTP 协议
   - 可配置循环次数和端点
   - 自动生成测试报告

## 基准测试指标

### 性能指标

- **吞吐量**: 每秒处理的 spans/metrics/logs 数量
- **延迟**: 端到端处理延迟
- **内存使用**: 峰值内存使用量
- **CPU 使用**: 平均 CPU 使用率

### 测试场景

1. **基础性能测试**
   - 单连接性能
   - 多连接性能
   - 批处理性能

2. **协议对比测试**
   - gRPC vs HTTP/Protobuf
   - 压缩 vs 无压缩
   - 不同批处理大小

3. **压力测试**
   - 高并发场景
   - 大数据量场景
   - 长时间运行

## 使用方法

### 运行基准测试

```bash
# Rust 基准测试
./benchmarks/run-rust.ps1 -Loops 200

# Go 基准测试
gRPC: ./benchmarks/run-go.ps1 -Endpoint http://localhost:4317 -Protocol grpc -Loops 200
HTTP: ./benchmarks/run-go.ps1 -Endpoint http://localhost:4318 -Protocol http/protobuf -Loops 200

# Python 基准测试
gRPC: ./benchmarks/run-python.ps1 -Endpoint http://localhost:4317 -Protocol grpc -Loops 200
HTTP: ./benchmarks/run-python.ps1 -Endpoint http://localhost:4318 -Protocol http/protobuf -Loops 200
```

### 生成测试报告

1. 运行基准测试
2. 填写 `REPORT_TEMPLATE.md`
3. 提交测试结果

## 基准测试结果

### 预期性能指标

| 协议 | 吞吐量 | 延迟 | 内存使用 |
|------|--------|------|----------|
| gRPC | 200k spans/s | <10ms | <100MB |
| HTTP | 60k spans/s | <20ms | <150MB |

### 优化建议

1. **高吞吐场景**: 使用 gRPC 协议
2. **防火墙穿透**: 使用 HTTP 协议
3. **批处理优化**: 调整批处理大小和超时
4. **采样优化**: 根据业务需求调整采样率

## 下一步

1. 添加更多测试场景
2. 创建自动化基准测试流程
3. 建立性能回归检测

## 阻塞

无
