# 示例代码状态概览

## 目标

提供端到端最小示例（Go/Python/Rust）与本地一键运行

## 完成度

### ✅ 已完成

1. **`examples/minimal-rust`** - 完全可用，已测试通过
   - Cargo.toml 配置完整
   - main.rs 代码完整
   - 支持 gRPC 和 HTTP 协议
   - 包含 traces 和 metrics

2. **`examples/minimal-go`** - 代码完整，依赖已配置
   - go.mod 依赖配置完整
   - main.go 代码完整
   - 支持 gRPC 和 HTTP 协议
   - 包含 traces 和 metrics

3. **`examples/minimal-python`** - 代码完整，依赖已配置
   - requirements.txt 依赖配置完整
   - main.py 代码完整
   - 支持 gRPC 和 HTTP 协议
   - 包含 traces 和 metrics

## 使用说明

### 环境要求

- **Rust**: 1.78+
- **Go**: 1.21+
- **Python**: 3.10+
- **Docker**: 用于运行 Collector

### 运行步骤

1. **启动 Collector**:

   ```bash
   ./scripts/run-collector.ps1
   ```

2. **运行示例**:

   ```bash
   # Rust
   cd examples/minimal-rust && cargo run
   
   # Go
   cd examples/minimal-go && go run .
   
   # Python
   cd examples/minimal-python && pip install -r requirements.txt && python main.py
   ```

3. **查看结果**:
   - Jaeger UI: <http://localhost:16686>
   - Prometheus: <http://localhost:9090>

## 下一步

1. 创建端到端集成测试脚本
2. 添加更多示例场景
3. 性能基准测试

## 阻塞

无
