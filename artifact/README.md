# OTLP Formal Verification Framework - Artifact

> **ICSE 2026 Artifact Evaluation**  
> **Paper**: A Comprehensive Formal Verification Framework for OTLP  
> **Badges Target**: Available + Functional + Reusable + Reproduced

---

## 🎯 Artifact Overview

This artifact contains the complete implementation and evaluation materials for our OTLP formal verification framework presented at ICSE 2026.

### What's Included

1. ✅ **Source Code** (~15,000 lines of Rust)
2. ✅ **Formal Proofs** (2,500 lines Coq + 1,800 lines Isabelle)
3. ✅ **Experimental Scripts** (for reproducing all results)
4. ✅ **Evaluation Data** (9.33M traces from 5 systems)
5. ✅ **Docker Support** (for easy setup)
6. ✅ **Complete Documentation**

---

## 🚀 Quick Start (5 minutes)

### Option A: Using Docker (Recommended)

```bash
# 1. Clone the repository
git clone https://github.com/anonymous/otlp-verification-artifact
cd otlp-verification-artifact

# 2. Build and run with Docker
docker-compose up -d

# 3. Run a quick validation test
docker-compose exec verifier ./scripts/quick_validation.sh

# Expected output: "✓ All 5 systems validated successfully"
```

### Option B: Native Installation

```bash
# 1. Install dependencies
./scripts/install_deps.sh

# 2. Build the project
cargo build --release

# 3. Run quick validation
./scripts/quick_validation.sh
```

---

## 📋 Getting Started Checklist

Follow these steps to evaluate the artifact:

- [ ] **Step 1**: Read this README (5 min)
- [ ] **Step 2**: Read `INSTALL.md` and setup environment (15-30 min)
- [ ] **Step 3**: Read `EXPERIMENTS.md` and understand experiments (10 min)
- [ ] **Step 4**: Run quick validation (5 min)
- [ ] **Step 5**: Reproduce main results (1-2 hours)
- [ ] **Step 6**: Explore and extend (optional)

**Total Time**: ~2-3 hours for full evaluation

---

## 📊 Claims and Evidence

Our paper makes the following key claims, all reproducible with this artifact:

### Claim 1: Detection Accuracy (RQ1)

**Paper Claims**:

- Detected 6,167 protocol violations across 5 systems
- Precision: 97.5%
- Recall: 94.1%

**How to Verify**:

```bash
./scripts/reproduce_rq1.sh
```

**Expected Output**: Results matching Table 5 in paper (within ±2%)

---

### Claim 2: Performance Overhead (RQ2)

**Paper Claims**:

- 3.7ms per 100-span batch
- < 1% overhead for typical workloads
- Linear scalability

**How to Verify**:

```bash
./scripts/reproduce_rq2.sh
```

**Expected Output**: Results matching Figure 8 in paper (within ±5%)

---

### Claim 3: Production Scalability (RQ3)

**Paper Claims**:

- Handles millions of traces per day
- Average 0.8% overhead across systems
- 98.8% successful fix rate

**How to Verify**:

```bash
./scripts/reproduce_rq3.sh
```

**Expected Output**: Results matching Table 6 in paper (within ±3%)

---

### Claim 4: Formal Correctness

**Paper Claims**:

- 8 key theorems formally proven
- Type system soundness
- Algebraic correctness

**How to Verify**:

```bash
cd proofs/coq && make
cd ../isabelle && isabelle build -D .
```

**Expected Output**: All proofs compile without errors

---

## 🗂️ Artifact Structure

```text
artifact/
├── README.md                 # This file
├── INSTALL.md                # Detailed installation guide
├── EXPERIMENTS.md            # Experiment reproduction guide
├── LICENSE                   # Apache 2.0 License
├── STATUS.md                 # Badge requirements checklist
│
├── docker/                   # Docker support
│   ├── Dockerfile
│   ├── docker-compose.yml
│   └── entrypoint.sh
│
├── src/                      # Source code (~15K LOC Rust)
│   ├── lib.rs
│   ├── types/                # Type system implementation
│   ├── algebra/              # Algebraic structures
│   ├── flow/                 # Triple flow analysis
│   ├── temporal/             # Temporal logic
│   └── semantic/             # Semantic verification
│
├── proofs/                   # Formal proofs
│   ├── coq/                  # Coq proofs (2.5K lines)
│   │   ├── TypeSystem.v
│   │   ├── Causality.v
│   │   ├── TemporalLogic.v
│   │   └── ...
│   └── isabelle/             # Isabelle proofs (1.8K lines)
│       ├── TypeSafety.thy
│       ├── AlgebraicLaws.thy
│       └── ...
│
├── data/                     # Evaluation data
│   ├── ecommerce/            # E-commerce system traces
│   ├── finance/              # Finance system traces
│   ├── healthcare/           # Healthcare system traces
│   ├── media/                # Media streaming traces
│   ├── cloud/                # Cloud platform traces
│   └── README.md             # Data description
│
├── scripts/                  # Experiment scripts
│   ├── install_deps.sh       # Install dependencies
│   ├── quick_validation.sh   # Quick smoke test
│   ├── reproduce_rq1.sh      # Reproduce RQ1
│   ├── reproduce_rq2.sh      # Reproduce RQ2
│   ├── reproduce_rq3.sh      # Reproduce RQ3
│   ├── reproduce_all.sh      # Reproduce all experiments
│   └── analyze_results.py    # Result analysis
│
├── results/                  # Pre-computed results
│   ├── rq1/                  # RQ1 results
│   ├── rq2/                  # RQ2 results
│   ├── rq3/                  # RQ3 results
│   └── README.md             # Results description
│
├── tests/                    # Test suite
│   ├── unit/                 # Unit tests
│   ├── integration/          # Integration tests
│   └── fixtures/             # Test data
│
├── benchmarks/               # Performance benchmarks
│   ├── micro/                # Microbenchmarks
│   └── macro/                # System-level benchmarks
│
└── docs/                     # Additional documentation
    ├── API.md                # API documentation
    ├── ARCHITECTURE.md       # Architecture guide
    ├── EXTENDING.md          # Extension guide
    └── FAQ.md                # Frequently asked questions
```

---

## 💻 System Requirements

### Minimum Requirements

- **OS**: Linux (Ubuntu 20.04+), macOS (11.0+), Windows 10+ (WSL2)
- **CPU**: 4 cores
- **RAM**: 8 GB
- **Disk**: 20 GB free space
- **Network**: Internet connection (for initial setup)

### Recommended Requirements

- **OS**: Linux (Ubuntu 22.04)
- **CPU**: 8+ cores
- **RAM**: 16 GB
- **Disk**: 50 GB SSD
- **Network**: Stable connection

### Software Dependencies

- **Rust**: 1.70+ (stable)
- **Coq**: 8.17+
- **Isabelle**: 2023
- **Docker**: 20.10+ (optional but recommended)
- **Python**: 3.9+ (for analysis scripts)

---

## 🎓 Academic Use

### Citing This Work

If you use this artifact in your research, please cite:

```bibtex
@inproceedings{otlp-verification-icse2026,
  title = {A Comprehensive Formal Verification Framework for OTLP},
  author = {Anonymous Authors},
  booktitle = {ICSE 2026},
  year = {2026},
  doi = {10.1145/XXXXXXX.XXXXXXX}
}
```

### License

This artifact is released under the **Apache License 2.0**.

You are free to:

- ✅ Use commercially
- ✅ Modify
- ✅ Distribute
- ✅ Use privately

See `LICENSE` file for full details.

---

## 🐛 Troubleshooting

### Common Issues

**Issue 1**: Docker build fails

```bash
# Solution: Increase Docker memory limit to 4GB+
# Docker Desktop → Settings → Resources → Memory
```

**Issue 2**: Coq proofs don't compile

```bash
# Solution: Install correct Coq version
opam install coq.8.17.0
```

**Issue 3**: Out of memory during experiments

```bash
# Solution: Reduce batch size
export BATCH_SIZE=50  # Default is 100
./scripts/reproduce_rq2.sh
```

**Issue 4**: Network timeout downloading data

```bash
# Solution: Use alternative mirror
export DATA_MIRROR=https://zenodo.org/...
./scripts/download_data.sh
```

### Getting Help

If you encounter issues not covered here:

1. Check `docs/FAQ.md`
2. Check GitHub Issues (link available after publication)
3. Contact artifact authors (contact info in paper)

---

## 📧 Contact

For questions about this artifact:

- **Primary Contact**: [Withheld for anonymous review]
- **Backup Contact**: [Withheld for anonymous review]
- **GitHub Issues**: [Will be available after publication]

---

## 🏆 Artifact Evaluation Badges

We are applying for the following ACM badges:

- 🥇 **Artifacts Available**: Publicly accessible on GitHub + Zenodo
- 🥇 **Artifacts Evaluated - Functional**: Complete documentation, runnable
- 🥇 **Artifacts Evaluated - Reusable**: Well-structured, extensible
- 🥇 **Results Reproduced**: All key results reproducible

See `STATUS.md` for detailed badge requirements checklist.

---

## 📅 Version History

- **v1.0.0** (2025-10-18): Initial artifact submission for ICSE 2026
- **v1.1.0** (TBD): Updates based on artifact evaluation feedback

---

## 🎉 Acknowledgments

We thank:

- The ICSE 2026 Artifact Evaluation Committee
- The developers of Rust, Coq, and Isabelle
- The OpenTelemetry community
- The organizations that provided evaluation data (anonymized)

---

**Last Updated**: 2025-10-18  
**Artifact Version**: 1.0.0  
**Paper Submission ID**: [Withheld for review]  
**Estimated Evaluation Time**: 2-3 hours

---

## 🚦 Quick Status Check

Run this command to verify your setup:

```bash
./scripts/status_check.sh
```

Expected output:

```text
✅ Docker: Available
✅ Rust: 1.70.0
✅ Coq: 8.17.0
✅ Isabelle: 2023
✅ Data: Downloaded (42 GB)
✅ Build: Success
━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ Ready for evaluation!
```

---

**Ready to start?** Go to `INSTALL.md` for detailed setup instructions! 🚀
