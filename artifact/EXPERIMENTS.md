# Experiment Reproduction Guide

> **Total Time**: 1-2 hours for all experiments  
> **Quick Test**: 5 minutes  
> **Individual RQs**: 20-30 minutes each

---

## 🎯 Overview

This guide explains how to reproduce all experiments from our ICSE 2026 paper:

- **RQ1**: Detection accuracy (Precision, Recall, Violations)
- **RQ2**: Performance overhead (Latency, Throughput)
- **RQ3**: Production scalability (Large-scale analysis)

All experiments produce outputs that can be compared with paper results.

---

## 📊 Experiment Matrix

| RQ | Claim | Script | Time | Output |
|----|-------|--------|------|--------|
| **RQ1** | 6,167 violations detected | `reproduce_rq1.sh` | 30 min | Table 5 |
| **RQ2** | 3.7ms overhead per 100 spans | `reproduce_rq2.sh` | 20 min | Figure 8 |
| **RQ3** | 0.8% avg overhead at scale | `reproduce_rq3.sh` | 40 min | Table 6 |
| **ALL** | All above | `reproduce_all.sh` | 90 min | All results |

---

## 🚀 Quick Start

### Run All Experiments (90 minutes)

```bash
# Run all experiments in one command
./scripts/reproduce_all.sh

# Output will be saved to results/reproduced/
# Comparison with paper results will be shown at the end
```

### Run Individual Experiments

```bash
# RQ1 only (30 minutes)
./scripts/reproduce_rq1.sh

# RQ2 only (20 minutes)
./scripts/reproduce_rq2.sh

# RQ3 only (40 minutes)
./scripts/reproduce_rq3.sh
```

---

## 📋 RQ1: Detection Accuracy

### Research Question

> **RQ1**: Can our framework detect real protocol violations with high precision and recall?

### Claims in Paper

- **Total violations**: 6,167 across 5 systems
- **Precision**: 97.5%
- **Recall**: 94.1%
- **Fix rate**: 98.8%

### Reproduction Steps

```bash
# Step 1: Run RQ1 experiment
./scripts/reproduce_rq1.sh

# Step 2: Check results
cat results/reproduced/rq1_summary.txt

# Step 3: Compare with paper
./scripts/compare_results.py --rq rq1
```

### Expected Output

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
RQ1: Detection Accuracy Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

System         | Violations | Precision | Recall
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
E-commerce     | 1,847      | 98.2%     | 95.1%
Finance        | 1,253      | 97.8%     | 93.6%
Healthcare     | 982        | 96.5%     | 92.8%
Media          | 1,456      | 97.1%     | 94.9%
Cloud          | 629        | 98.1%     | 95.2%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Total          | 6,167      | 97.5%     | 94.1%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Fix Success Rate: 98.8%

Comparison with Paper (Table 5):
  Violations: Match (6,167 vs 6,167) ✅
  Precision:  Match (97.5% vs 97.5%) ✅
  Recall:     Match (94.1% vs 94.1%) ✅
```

### Detailed Breakdown

The script performs these steps:

1. Load traces from all 5 systems
2. Run violation detection algorithm
3. Classify violations by type:
   - Causality violations
   - Missing spans
   - Timestamp inconsistencies
   - Parent-child errors
4. Compute precision and recall using ground truth
5. Generate detailed report

### Artifacts Generated

```text
results/reproduced/rq1/
├── violations_summary.csv      # Violation counts per system
├── precision_recall.csv        # P/R metrics
├── violation_types.csv         # Breakdown by type
├── false_positives.csv         # FP analysis
├── false_negatives.csv         # FN analysis
└── rq1_plots/                  # Visualizations
    ├── violations_by_system.png
    ├── precision_recall.png
    └── violation_distribution.png
```

### Comparison Tolerance

Results should match paper within:
- **Violation counts**: ±2% (due to non-deterministic sampling)
- **Precision**: ±0.5%
- **Recall**: ±0.5%

---

## ⚡ RQ2: Performance Overhead

### Research Question

> **RQ2**: What is the performance overhead of our verification framework?

### Claims in Paper

- **100-span batch**: 3.7ms
- **Typical overhead**: < 1%
- **Scalability**: Linear with batch size

### Reproduction Steps

```bash
# Step 1: Run RQ2 benchmark
./scripts/reproduce_rq2.sh

# This will test various batch sizes: 10, 50, 100, 500, 1000 spans

# Step 2: View results
cat results/reproduced/rq2_performance.txt

# Step 3: Generate plots
python3 scripts/plot_rq2.py
```

### Expected Output

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
RQ2: Performance Overhead Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Batch Size | Time (ms) | Throughput (spans/s) | Overhead
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
10         | 0.4       | 25,000               | 0.3%
50         | 1.8       | 27,778               | 0.6%
100        | 3.7       | 27,027               | 0.9%
500        | 18.2      | 27,473               | 0.8%
1000       | 36.5      | 27,397               | 0.8%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Linear regression: R² = 0.998 (excellent linearity)

Comparison with Paper (Figure 8):
  100-span time: 3.7ms vs 3.7ms ✅
  Linearity: R²=0.998 vs 0.997 ✅
  Overhead: 0.9% vs <1% ✅
```

### Performance Breakdown

The benchmark measures:

1. **Type checking time**: ~28% of total
2. **Flow analysis time**: ~42% of total
3. **Temporal verification**: ~18% of total
4. **Other overhead**: ~12% of total

### Artifacts Generated

```text
results/reproduced/rq2/
├── performance_summary.csv      # Main results
├── breakdown_by_component.csv   # Time breakdown
├── memory_usage.csv             # Memory profiling
└── rq2_plots/
    ├── latency_vs_batch_size.png
    ├── throughput.png
    └── component_breakdown.png
```

### Comparison Tolerance

- **Latency**: ±10% (hardware variation)
- **Throughput**: ±15% (hardware variation)
- **Linearity (R²)**: ±0.01

---

## 📈 RQ3: Production Scalability

### Research Question

> **RQ3**: Does the framework scale to production workloads?

### Claims in Paper

- **Traces analyzed**: 9.33M across 5 systems
- **Average overhead**: 0.8%
- **Processing rate**: 1.9M traces/day on average

### Reproduction Steps

```bash
# Step 1: Run RQ3 scalability test
./scripts/reproduce_rq3.sh

# This processes full datasets (may take 40-60 minutes)

# Optional: Run with reduced dataset (5 minutes)
./scripts/reproduce_rq3.sh --quick

# Step 2: Analyze results
./scripts/analyze_rq3.py
```

### Expected Output

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
RQ3: Production Scalability Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

System      | Traces    | Time (s) | Rate (t/s) | Overhead
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
E-commerce  | 2,300,000 | 847      | 2,715      | 0.8%
Finance     | 1,800,000 | 673      | 2,675      | 0.9%
Healthcare  | 1,400,000 | 521      | 2,687      | 0.7%
Media       | 2,100,000 | 789      | 2,662      | 0.9%
Cloud       | 1,730,000 | 634      | 2,729      | 0.8%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Total       | 9,330,000 | 3,464    | 2,694      | 0.8%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Memory usage: Peak 2.3 GB, Average 1.8 GB

Comparison with Paper (Table 6):
  Total traces: 9.33M vs 9.33M ✅
  Avg overhead: 0.8% vs 0.8% ✅
  Processing rate: 2.69K t/s vs 2.7K t/s ✅
```

### Scalability Analysis

The experiment evaluates:

1. **Throughput**: Traces processed per second
2. **Memory efficiency**: Peak and average memory
3. **CPU utilization**: Average across cores
4. **Overhead percentage**: Compared to baseline

### Artifacts Generated

```text
results/reproduced/rq3/
├── scalability_summary.csv
├── system_resources.csv         # CPU, memory over time
├── throughput_analysis.csv
└── rq3_plots/
    ├── processing_rate.png
    ├── memory_usage_over_time.png
    ├── cpu_utilization.png
    └── overhead_comparison.png
```

### Comparison Tolerance

- **Trace counts**: Exact match
- **Processing time**: ±20% (hardware variation)
- **Overhead**: ±0.2%

---

## 🔬 Additional Experiments

### Formal Proofs Verification

```bash
# Verify all Coq proofs
cd proofs/coq
make

# Expected: All 8 theorems compile successfully

# Verify all Isabelle proofs
cd ../isabelle
isabelle build -D .

# Expected: All 8 theories verified
```

### Ablation Study

```bash
# Test framework without specific components
./scripts/ablation_study.sh

# This will show the contribution of each component:
# - Type system only
# - Flow analysis only
# - Temporal logic only
# - Full framework
```

### Stress Testing

```bash
# Test with extreme loads
./scripts/stress_test.sh

# Tests:
# - 10,000 spans per batch
# - 1M traces continuous processing
# - Concurrent verification (8 threads)
```

---

## 📊 Result Comparison

### Automated Comparison

```bash
# Compare all results with paper
./scripts/compare_all_results.py

# Output: Detailed comparison report
```

### Manual Comparison

Reference tables and figures in paper:

- **Table 5** (RQ1): `results/reproduced/rq1/violations_summary.csv`
- **Figure 8** (RQ2): `results/reproduced/rq2_plots/latency_vs_batch_size.png`
- **Table 6** (RQ3): `results/reproduced/rq3/scalability_summary.csv`

### Success Criteria

Experiment is considered **successfully reproduced** if:

1. ✅ Script completes without errors
2. ✅ Results match paper within tolerance
3. ✅ Visualizations are similar in shape/trend
4. ✅ Key metrics (precision, latency, throughput) match

---

## 🐛 Troubleshooting

### Experiment hangs

```bash
# Check system resources
htop

# If out of memory, reduce batch size
export BATCH_SIZE=50
./scripts/reproduce_rq2.sh
```

### Results differ significantly

```bash
# Possible causes and solutions:

# 1. Different hardware (expected variation ±10-20%)
#    → Document your hardware specs

# 2. Data corruption
./scripts/verify_data.sh
#    → Re-download if needed

# 3. Software version mismatch
./scripts/check_versions.sh
#    → Update to matching versions
```

### Script crashes

```bash
# Check logs
tail -n 100 logs/experiments.log

# Common issues:
# - Insufficient disk space
# - Permission errors
# - Network timeout (for data fetch)
```

---

## ⏱️ Time Budget

Recommended allocation for artifact evaluation:

| Task | Time | Priority |
|------|------|----------|
| Installation & Setup | 30 min | High |
| Quick validation | 5 min | High |
| RQ1 reproduction | 30 min | High |
| RQ2 reproduction | 20 min | High |
| RQ3 reproduction | 40 min | Medium |
| Proof verification | 15 min | Medium |
| Code exploration | 30 min | Low |
| Extension attempts | 60 min | Low |
| **Total** | **3.5 hours** | |

**Minimum for badge**: Installation + Quick validation + RQ1 (65 min)

---

## 📝 Reporting Results

When evaluating, please report:

1. **System specifications**:
   ```bash
   ./scripts/system_info.sh > my_system.txt
   ```

2. **Experiment results**:
   ```bash
   cp -r results/reproduced results/my_reproduction
   ```

3. **Any deviations**:
   - Document in `my_notes.md`
   - Include error logs if any

4. **Comparison summary**:
   ```bash
   ./scripts/generate_report.sh > comparison_report.txt
   ```

---

## 🎓 Understanding the Results

### RQ1: Violation Detection

- **High precision** means few false positives (framework doesn't cry wolf)
- **High recall** means few false negatives (framework catches most bugs)
- **Balanced** precision/recall indicates robust detection

### RQ2: Performance

- **Linear scaling** means overhead is predictable
- **< 1% overhead** means practical for production
- **Component breakdown** shows where time is spent

### RQ3: Scalability

- **Millions of traces** shows real-world applicability
- **Consistent overhead** shows no performance degradation
- **Low memory** shows efficiency

---

## 🚀 Quick Reference

```bash
# Full reproduction (90 minutes)
./scripts/reproduce_all.sh

# Individual RQs
./scripts/reproduce_rq1.sh  # 30 min
./scripts/reproduce_rq2.sh  # 20 min
./scripts/reproduce_rq3.sh  # 40 min

# Quick test (5 minutes)
./scripts/quick_validation.sh

# Compare results
./scripts/compare_all_results.py

# Generate report
./scripts/generate_report.sh
```

---

## 💡 Tips for Evaluators

1. **Start with quick_validation.sh** to ensure setup is correct
2. **Run RQ1 first** - it's the most important result
3. **Use --quick mode** for initial exploration
4. **Monitor resources** with `htop` during experiments
5. **Save your results** before re-running

---

**Ready to reproduce? Start with:**
```bash
./scripts/reproduce_all.sh
```

**Questions?** Check `docs/FAQ.md` or contact us.

