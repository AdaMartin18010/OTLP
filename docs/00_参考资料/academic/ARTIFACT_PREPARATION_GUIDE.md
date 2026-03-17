# 🎁 ICSE 2026 Artifact准备指南

> **目标**: 为ICSE 2026论文准备可重现的Artifact包  
> **状态**: 📝 框架就绪，等待论文完成后执行  
> **预计时间**: 1周（论文完成后）

---

## 🎯 Artifact目标

### ICSE 2026 Artifact评估标准

ICSE要求Artifact满足以下标准：

1. **Available** (可获得):
   - ✅ 公开可访问（如GitHub、Zenodo）
   - ✅ 永久归档
   - ✅ 明确的许可证

2. **Functional** (功能性):
   - ✅ 文档完整
   - ✅ 可以安装和运行
   - ✅ 能够重现论文中的关键结果

3. **Reusable** (可重用):
   - ✅ 代码结构清晰
   - ✅ 有良好的文档
   - ✅ 可以扩展到新的场景

4. **Reproduced** (可重现):
   - ✅ 能够重现论文中的所有实验结果
   - ✅ 结果一致性>90%

---

## 📦 Artifact内容清单

### 必须包含

1. **源代码** (5,000行Rust)
   - `src/` - 主要实现
   - `tests/` - 测试套件
   - `examples/` - 示例代码

2. **形式化证明** (2,140行)
   - `proofs/coq/` - Coq证明
   - `proofs/isabelle/` - Isabelle证明

3. **实验数据和脚本**
   - `data/` - 实验数据（或生成脚本）
   - `scripts/` - 实验运行脚本
   - `results/` - 预计算结果

4. **文档**
   - `README.md` - 完整的使用指南
   - `INSTALL.md` - 安装说明
   - `EXPERIMENTS.md` - 实验重现指南
   - `LICENSE` - 许可证文件

5. **Docker支持**
   - `Dockerfile` - Docker镜像
   - `docker-compose.yml` - 容器编排
   - `scripts/docker_build.sh` - 构建脚本

---

## 📂 目录结构

```text
otlp-verification-artifact/
├── README.md                    # 主要文档（第一个看的文件）
├── LICENSE                      # MIT或Apache 2.0
├── INSTALL.md                   # 详细安装指南
├── EXPERIMENTS.md               # 实验重现指南
├── Dockerfile                   # Docker支持
├── docker-compose.yml
├── .gitignore
├── Cargo.toml                   # Rust项目配置
│
├── src/                         # 源代码 (Rust)
│   ├── lib.rs
│   ├── types/                   # 类型系统
│   ├── algebra/                 # 代数结构
│   ├── flow/                    # 流分析
│   ├── temporal/                # 时态逻辑
│   └── semantic/                # 语义验证
│
├── tests/                       # 测试
│   ├── unit/                    # 单元测试
│   ├── integration/             # 集成测试
│   └── fixtures/                # 测试数据
│
├── proofs/                      # 形式化证明
│   ├── coq/                     # Coq证明 (5个定理)
│   │   ├── README.md
│   │   ├── TypeSystem.v
│   │   ├── Causality.v
│   │   ├── TemporalLogic.v
│   │   ├── Soundness.v
│   │   └── Completeness.v
│   │
│   └── isabelle/                # Isabelle证明 (3个定理)
│       ├── README.md
│       ├── SpanComposition.thy
│       ├── TraceAggregation.thy
│       └── Interoperability.thy
│
├── examples/                    # 示例
│   ├── simple_trace/            # 简单追踪示例
│   ├── complex_trace/           # 复杂追踪示例
│   └── case_studies/            # 案例研究
│
├── data/                        # 实验数据
│   ├── README.md
│   ├── raw/                     # 原始数据（或生成脚本）
│   ├── processed/               # 处理后的数据
│   └── synthetic/               # 合成数据
│
├── scripts/                     # 实验脚本
│   ├── setup.sh                 # 环境设置
│   ├── run_all_experiments.sh   # 运行所有实验
│   ├── experiment_1_violations.sh
│   ├── experiment_2_performance.sh
│   ├── experiment_3_effectiveness.sh
│   └── generate_figures.py      # 生成论文图表
│
├── results/                     # 预计算结果
│   ├── README.md
│   ├── violations.csv
│   ├── performance.csv
│   ├── effectiveness.csv
│   └── figures/                 # 论文图表
│
└── docs/                        # 额外文档
    ├── API.md                   # API文档
    ├── ARCHITECTURE.md          # 架构说明
    └── TROUBLESHOOTING.md       # 常见问题
```

---

## 📝 核心文档模板

### README.md

```markdown
      # OTLP Formal Verification Framework - Artifact

      [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)

      This artifact accompanies the paper:

      > **Title**: A Comprehensive Formal Verification Framework for OTLP: Ensuring Correctness and Consistency in Distributed Tracing
      > **Authors**: [Author Names]
      > **Conference**: ICSE 2026

      ## Quick Start

      ### Option 1: Docker (Recommended, 5 minutes)

      ```bash
      docker pull ghcr.io/username/otlp-verification:latest
      docker run -it ghcr.io/username/otlp-verification:latest
      ```

      ### Option 2: Local Installation (30 minutes)

      See [INSTALL.md](INSTALL.md) for detailed instructions.

      ```bash
      # Prerequisites
      # - Rust 1.70+
      # - Coq 8.17.0
      # - Isabelle2023

      # Build
      cargo build --release

      # Run tests
      cargo test

      # Run experiments
      ./scripts/run_all_experiments.sh
      ```

      ## Repository Structure

      - `src/` - Rust implementation (5,000 LOC)
      - `proofs/` - Formal proofs (2,140 LOC)
      - `examples/` - Usage examples
      - `scripts/` - Experiment scripts
      - `results/` - Pre-computed results

      ## Reproducing Paper Results

      See [EXPERIMENTS.md](EXPERIMENTS.md) for step-by-step instructions.

      **Estimated time**: 2-4 hours

      ## Claims and Validation

      This artifact supports the following claims from the paper:

      1. **Table 2-3**: Violation detection (Section 5.2)
         - Script: `./scripts/experiment_1_violations.sh`
         - Expected: 6,167 violations across 9.3M traces
         - Tolerance: ±5%

      2. **Table 5**: Performance overhead (Section 5.3)
         - Script: `./scripts/experiment_2_performance.sh`
         - Expected: <10% overhead
         - Tolerance: ±2%

      3. **Table 4**: Detection effectiveness (Section 5.4)
         - Script: `./scripts/experiment_3_effectiveness.sh`
         - Expected: 98%+ precision, 100% recall
         - Tolerance: ±1%

      4. **Formal Proofs**: Theorems T1-T8 (Section 3)
         - Coq proofs: `cd proofs/coq && make`
         - Isabelle proofs: `cd proofs/isabelle && isabelle build`
         - Expected: All proofs verify successfully

      ## License

      MIT License - see [LICENSE](LICENSE)

      ## Contact

      - Email: [email]
      - Issues: <https://github.com/username/otlp-verification/issues>

      ## Citation

      If you use this artifact, please cite our paper:

      ```bibtex
      @inproceedings{otlp-verification-icse2026,
      title={A Comprehensive Formal Verification Framework for OTLP},
      author={[Authors]},
      booktitle={Proceedings of ICSE 2026},
      year={2026}
      }
      ```

```

### INSTALL.md

```markdown
      # Installation Guide

      ## Prerequisites

      ### Required

      - **Rust**: 1.70 or later
      - **Cargo**: 1.70 or later
      - **Git**: Any recent version

      ### For Formal Proofs (Optional)

      - **Coq**: 8.17.0
      - **Isabelle**: 2023

      ### System Requirements

      - **OS**: Linux (Ubuntu 20.04+), macOS (12+), or Windows (WSL2)
      - **RAM**: 4GB minimum, 8GB recommended
      - **Disk**: 2GB free space

      ## Quick Installation (Docker)

      ### 1. Install Docker

      Follow the official guide: https://docs.docker.com/get-docker/

      ### 2. Pull and Run

      ```bash
      docker pull ghcr.io/username/otlp-verification:latest
      docker run -it ghcr.io/username/otlp-verification:latest
      ```

      All dependencies are pre-installed in the container.

      ## Local Installation

      ### Ubuntu/Debian

      ```bash
      # 1. Install Rust
      curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
      source $HOME/.cargo/env

      # 2. Clone repository
      git clone https://github.com/username/otlp-verification.git
      cd otlp-verification

      # 3. Build
      cargo build --release

      # 4. Run tests
      cargo test

      # 5. (Optional) Install Coq
      sudo apt-get install coq

      # 6. (Optional) Install Isabelle
      # Download from https://isabelle.in.tum.de/
      ```

      ### macOS

      ```bash
      # 1. Install Rust
      curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
      source $HOME/.cargo/env

      # 2. Clone repository
      git clone https://github.com/username/otlp-verification.git
      cd otlp-verification

      # 3. Build
      cargo build --release

      # 4. Run tests
      cargo test

      # 5. (Optional) Install Coq
      brew install coq

      # 6. (Optional) Install Isabelle
      # Download from https://isabelle.in.tum.de/
      ```

      ### Windows (WSL2)

      ```bash
      # Same as Ubuntu/Debian
      ```

      ## Verification

      After installation, verify everything works:

      ```bash
      # Run basic tests
      cargo test

      # Run a simple example
      cargo run --example simple_trace

      # Check formal proofs (if installed)
      cd proofs/coq && make
      cd ../isabelle && isabelle build
      ```

      Expected output: All tests pass, no errors.

      ## Troubleshooting

      See [docs/TROUBLESHOOTING.md](docs/TROUBLESHOOTING.md) for common issues.

      ## Next Steps

      See [EXPERIMENTS.md](EXPERIMENTS.md) to reproduce paper results.

```

### EXPERIMENTS.md

```markdown
      # Experiment Reproduction Guide

      This guide explains how to reproduce all experiments from our ICSE 2026 paper.

      **Estimated total time**: 2-4 hours

      ## Overview

      The paper presents five main experiments:

      1. **Experiment 1**: Violation Detection (30 min)
      2. **Experiment 2**: Performance Overhead (60 min)
      3. **Experiment 3**: Detection Effectiveness (30 min)
      4. **Experiment 4**: Formal Proof Verification (30 min)
      5. **Experiment 5**: Case Study Analysis (60 min)

      ## Prerequisites

      - Completed installation (see [INSTALL.md](INSTALL.md))
      - 4GB RAM, 2GB disk space
      - Internet connection (for downloading test data)

      ## Quick Start: Run All Experiments

      ```bash
      ./scripts/run_all_experiments.sh
      ```

      This will run all experiments and generate results in `results/`.

      **Estimated time**: 3-4 hours

      ## Detailed Instructions

      ### Experiment 1: Violation Detection

      **Claim**: Detect 6,167 violations across 9.3M traces (Table 3)

      **Steps**:

      ```bash
      # 1. Generate or download trace data
      ./scripts/setup_data.sh

      # 2. Run violation detection
      ./scripts/experiment_1_violations.sh

      # 3. Check results
      cat results/violations.csv
      ```

      **Expected output**:

      ```csv
      System,Traces,Violations,Rate
      CS1,1000000,1247,0.125%
      CS2,400000,89,0.022%
      ...
      Total,9330000,6167,0.066%
      ```

      **Tolerance**: ±5% (due to randomness in synthetic data)

      **Time**: 30 minutes

      ### Experiment 2: Performance Overhead

      **Claim**: <10% overhead (Table 5)

      **Steps**:

      ```bash
      ./scripts/experiment_2_performance.sh
      ```

      **Expected output**:

      ```csv
      Component,Baseline(ms),WithVerification(ms),Overhead(%)
      Type System,100,105,5.0%
      Algebraic,150,157,4.7%
      ...
      Overall,1000,1080,8.0%
      ```

      **Time**: 60 minutes

      ### Experiment 3: Detection Effectiveness

      **Claim**: 98%+ precision, 100% recall (Table 4)

      **Steps**:

      ```bash
      ./scripts/experiment_3_effectiveness.sh
      ```

      **Expected output**:

      ```csv
      Component,TP,FP,FN,Precision,Recall
      Type System,247,3,0,98.8%,100%
      ...
      ```

      **Time**: 30 minutes

      ### Experiment 4: Formal Proof Verification

      **Claim**: All 8 theorems proven (Section 3)

      **Steps**:

      ```bash
      # Coq proofs (T1, T2, T6, T7, T8)
      cd proofs/coq
      make

      # Isabelle proofs (T3, T4, T5)
      cd ../isabelle
      isabelle build -D .
      ```

      **Expected output**:

      ```text
      All proofs verified successfully.
      Total time: 15-30 minutes
      ```

      **Time**: 30 minutes

      ### Experiment 5: Case Study Analysis

      **Claim**: Successful deployment in 5 real-world systems

      **Steps**:

      ```bash
      ./scripts/experiment_5_case_studies.sh
      ```

      **Expected output**: Detailed analysis for each of the 5 case studies.

      **Time**: 60 minutes (mostly reading)

      ## Generating Paper Figures

      After running experiments, generate figures:

      ```bash
      python scripts/generate_figures.py
      ```

      Output: `results/figures/` (PNG and PDF)

      ## Comparing with Paper Results

      Compare your results with the paper:

      ```bash
      python scripts/compare_with_paper.py
      ```

      This will generate a report showing the difference between your results and the paper.

      ## Troubleshooting

      ### Issue 1: Data Download Fails

      **Solution**: Manually download from Zenodo and extract to `data/`

      ### Issue 2: Performance Results Differ Significantly

      **Reason**: Different hardware

      **Solution**: Compare relative overhead (%), not absolute times (ms)

      ### Issue 3: Proofs Don't Verify

      **Reason**: Version mismatch

      **Solution**: Ensure Coq 8.17.0 and Isabelle2023 are installed

      ## Contact

      Questions? Open an issue: <https://github.com/username/otlp-verification/issues>

```

---

## 🐳 Docker配置

### Dockerfile

```dockerfile
FROM rust:1.70 as builder

WORKDIR /app

# Copy source
COPY Cargo.toml Cargo.lock ./
COPY src ./src
COPY tests ./tests

# Build
RUN cargo build --release

# Runtime image
FROM ubuntu:22.04

# Install dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Copy binary
COPY --from=builder /app/target/release/otlp-verification /usr/local/bin/

# Copy artifact files
WORKDIR /artifact
COPY README.md INSTALL.md EXPERIMENTS.md LICENSE ./
COPY scripts ./scripts
COPY data ./data
COPY results ./results
COPY examples ./examples

# Set up environment
ENV PATH="/usr/local/bin:${PATH}"

# Run tests on container start
CMD ["/bin/bash"]
```

### docker-compose.yml

```yaml
version: '3.8'

services:
  otlp-verification:
    build: .
    container_name: otlp-verification-artifact
    volumes:
      - ./results:/artifact/results
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
```

---

## 📋 准备清单

### 阶段1: 代码整理（1天）

- [ ] 清理代码，移除调试代码
- [ ] 添加完整的代码注释
- [ ] 统一代码风格（`cargo fmt`）
- [ ] 运行linter（`cargo clippy`）
- [ ] 确保所有测试通过

### 阶段2: 文档编写（2天）

- [ ] 编写README.md
- [ ] 编写INSTALL.md
- [ ] 编写EXPERIMENTS.md
- [ ] 编写API.md
- [ ] 编写TROUBLESHOOTING.md

### 阶段3: Docker打包（1天）

- [ ] 创建Dockerfile
- [ ] 测试Docker镜像
- [ ] 优化镜像大小
- [ ] 创建docker-compose.yml

### 阶段4: 实验脚本（2天）

- [ ] 编写数据生成脚本
- [ ] 编写实验运行脚本
- [ ] 验证所有实验可重现
- [ ] 生成预计算结果

### 阶段5: 发布（1天）

- [ ] 创建GitHub仓库
- [ ] 上传到Zenodo获取DOI
- [ ] 构建Docker镜像并推送到GitHub Container Registry
- [ ] 最终测试（在干净的环境中）

---

## 🎯 质量检查清单

### 可用性

- [ ] 代码可以从GitHub克隆
- [ ] 有永久的DOI（Zenodo）
- [ ] 许可证清晰（MIT或Apache 2.0）

### 功能性

- [ ] README清晰，5分钟内理解
- [ ] 安装指南详细，30分钟内完成安装
- [ ] 所有示例都能运行
- [ ] Docker镜像正常工作

### 可重现性

- [ ] 所有实验都有详细步骤
- [ ] 结果与论文一致（±5%）
- [ ] 预计算结果已提供
- [ ] 所有形式化证明都能验证

### 可重用性

- [ ] 代码结构清晰
- [ ] API文档完整
- [ ] 有扩展示例
- [ ] 故障排除指南完备

---

## 📞 时间线

### Week 1 (论文完成后)

- **Day 1-2**: 代码整理和清理
- **Day 3-4**: 文档编写
- **Day 5**: Docker打包

### Week 2

- **Day 1-2**: 实验脚本和验证
- **Day 3**: 最终测试
- **Day 4**: 发布到GitHub和Zenodo
- **Day 5**: 提交Artifact（论文接收后）

---

## 💡 最佳实践

1. **Early Preparation**: 论文写作期间就开始整理代码
2. **Continuous Testing**: 定期在干净的环境中测试
3. **Clear Documentation**: 假设用户是第一次接触项目
4. **Reproducibility First**: 确保结果可以重现比追求完美重要
5. **Community Support**: 快速响应GitHub Issues

---

**状态**: 📝 框架就绪  
**下一步**: 等待论文完成后开始执行  
**预计开始时间**: 论文初稿完成后（约2周后）
