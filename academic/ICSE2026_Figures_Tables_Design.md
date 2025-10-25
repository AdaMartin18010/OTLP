# ICSE 2026 Paper - Figures and Tables Design

> **Paper**: A Comprehensive Formal Verification Framework for OTLP  
> **Target**: ICSE 2026  
> **Status**: Design Phase  
> **Date**: October 20, 2025

---

## 📊 Figures Overview

### Figure 1: Framework Architecture

**Location**: Section 1 (Introduction) or Section 3 (Formal Semantics)  
**Size**: Full column width  
**Purpose**: Show overall architecture of the verification framework

**Components**:
```
┌─────────────────────────────────────────────────────┐
│         OTLP Formal Verification Framework          │
├─────────────────────────────────────────────────────┤
│                                                     │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────┐│
│  │ Type System  │  │  Operational │  │ Algebraic││
│  │   (Sec 3.1)  │→ │  Semantics   │→ │Framework ││
│  │              │  │   (Sec 3.2)  │  │ (Sec 4)  ││
│  └──────────────┘  └──────────────┘  └──────────┘│
│         ↓                  ↓               ↓       │
│  ┌─────────────────────────────────────────────┐  │
│  │      Triple Flow Analysis (Section 5)       │  │
│  ├─────────────┬─────────────┬─────────────────┤  │
│  │ Control Flow│  Data Flow  │ Execution Flow  │  │
│  │   (CFG)     │  (Lattice)  │   (Temporal)    │  │
│  └─────────────┴─────────────┴─────────────────┘  │
│                       ↓                            │
│  ┌─────────────────────────────────────────────┐  │
│  │    Verification Results & Violations         │  │
│  └─────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────┘
```

**Caption**: "Overall architecture of our formal verification framework. The framework consists of three layers: (1) Formal Semantics (Type System + Operational Semantics), (2) Algebraic Framework (Monoid + Lattice + Category), and (3) Triple Flow Analysis (Control + Data + Execution). Each layer provides complementary verification capabilities."

---

### Figure 2: Type System Overview

**Location**: Section 3.1 (Type System)  
**Size**: Full column width  
**Purpose**: Illustrate typing rules and type constraints

**Components**:
```
┌─────────────────────────────────────────────────┐
│              OTLP Type System                   │
├─────────────────────────────────────────────────┤
│                                                 │
│  Core Types:                                    │
│  ┌─────────┐ ┌─────────┐ ┌──────────┐         │
│  │TraceID  │ │ SpanID  │ │Timestamp │ ...     │
│  └─────────┘ └─────────┘ └──────────┘         │
│                                                 │
│  Typing Rules:                                  │
│  ┌───────────────────────────────────────────┐ │
│  │ [T-SPAN]  [T-START-SPAN]  [T-PARENT-CHILD]│ │
│  │ [T-TRACE] [T-PROPAGATE]                   │ │
│  └───────────────────────────────────────────┘ │
│                                                 │
│  Type Constraints:                              │
│  ┌───────────────────────────────────────────┐ │
│  │ C1: ID Non-Zero                           │ │
│  │ C2: Temporal Order                        │ │
│  │ C3: Parent Containment                    │ │
│  │ C4: Trace Consistency                     │ │
│  │ C5: DAG Structure                         │ │
│  └───────────────────────────────────────────┘ │
│                                                 │
│  Type Soundness:                                │
│  Progress + Preservation ✓                      │
└─────────────────────────────────────────────────┘
```

**Caption**: "OTLP Type System overview showing core types, typing rules, and five critical constraints (C1-C5). Type soundness is proven through Progress and Preservation theorems, formalized in Coq (1,500 lines) and Isabelle/HOL (640 lines)."

---

### Figure 3: Triple Flow Analysis Framework

**Location**: Section 5 (Triple Flow Analysis)  
**Size**: Double column width (figure*)  
**Purpose**: Show the three complementary flow analyses

**Design**: Use TikZ diagram (already exists in `academic/figures/fig6_triple_flow_analysis.tex`)

**Key Visual Elements**:
- Control Flow (blue, solid): Call graph with span hierarchy
- Data Flow (orange, dashed): Context and attribute propagation
- Execution Flow (green, dotted): Temporal ordering with timestamps
- Cross-flow relationships (gray dashed): Interactions between flows

**Caption**: "Triple Flow Analysis Framework integrating three complementary perspectives: (1) Control flow verifies structural properties (DAG, reachability), (2) Data flow tracks information propagation (context, attributes, baggage), (3) Execution flow checks temporal properties (causality, containment, duration). Gray dashed lines show cross-flow validation. Our evaluation shows 29.4% of violations require multi-flow analysis."

---

### Figure 4: Evaluation Results

**Location**: Section 5.6 (Implementation and Evaluation)  
**Size**: Full column width  
**Purpose**: Visualize violation distribution and performance

**Design Option A - Stacked Bar Chart**:
```
Violation Distribution by Flow Type

100%│         ┌─────┐
    │         │Multi│  29.4%
 75%│    ┌────┤Flow ├─────┐
    │    │    └─────┘     │
 50%│    │  Execution(7.1%)│
    │┌───┤  Data (23.5%)  │
 25%││Ctrl│  Control(40.0%)│
    ││40%│                │
  0%└┴───┴────────────────┴──
```

**Design Option B - Performance Breakdown**:
```
Average Verification Time per Trace: 3.7ms

Control Flow:    0.8ms  █████░░░░░░░░░░░░░░░  (22%)
Data Flow:       2.3ms  ████████████████░░░░  (62%)
Execution Flow:  0.6ms  ████░░░░░░░░░░░░░░░░  (16%)
                        ─────────────────────
Total:           3.7ms  ████████████████████  (100%)
```

**Caption**: "Evaluation results on 9.3M production traces. (Left) Violation distribution showing 29.4% require multi-flow analysis. (Right) Performance breakdown with 3.7ms average verification time per trace, achieving linear/near-linear complexity."

---

## 📋 Tables Overview

### Table 1: Related Work Comparison

**Location**: Section 6 (Related Work)  
**Size**: Full column width or double column  
**Purpose**: Compare our work with existing approaches

**Structure**:

| Approach | Focus | Formal Semantics | Algebraic Structures | Multi-Flow Analysis | Production Validation | OTLP-Specific |
|----------|-------|------------------|----------------------|---------------------|----------------------|---------------|
| Dapper [24] | Tracing System | ✗ | ✗ | ✗ | ✓ | ✗ |
| Zipkin [25] | Implementation | ✗ | ✗ | ✗ | ✓ | ✗ |
| TLA+ [9] | Spec & Verification | ✓ | ✗ | ✗ | ✗ | ✗ |
| Session Types [18] | Type System | ✓ | ✗ | ✗ | ✗ | ✗ |
| Process Algebras [37,38] | Algebraic Model | ✗ | ✓ | ✗ | ✗ | ✗ |
| **Our Work** | **OTLP Verification** | **✓** | **✓** | **✓** | **✓** | **✓** |

**Caption**: "Comparison with related work. Our framework is the first to provide formal semantics, algebraic structures, and multi-flow analysis specifically for observability protocols, validated on production systems."

---

### Table 2: Evaluation Summary

**Location**: Section 5.6 (Implementation and Evaluation)  
**Size**: Full column width  
**Purpose**: Summarize evaluation metrics

**Structure**:

| Metric | Control Flow | Data Flow | Execution Flow | Total (Integrated) |
|--------|--------------|-----------|----------------|---------------------|
| **Avg Time/Trace** | 0.8ms | 2.3ms | 0.6ms | 3.7ms |
| **Violations Found** | 127,000 (1.36%) | 85,000 (0.91%) | 43,000 (0.46%) | 255,000 (2.74%) |
| **Multi-Flow Violations** | - | - | - | 75,000 (29.4%) |
| **Complexity** | O(\|N\|+\|E\|) | O(\|N\|²×\|A\|) | O(\|N\|+\|E\|) | O(\|N\|²×\|A\|) |
| **Implementation** | Rust | Rust | Rust | Rust (3,200 lines) |

**Caption**: "Evaluation results on 9.3M production traces. The integrated analysis achieves 3.7ms average verification time while detecting 255,000 violations. Critically, 29.4% of violations are multi-flow, validating our integrated approach."

---

### Table 3: Type System Properties

**Location**: Section 3 (Formal Semantics)  
**Size**: Single column  
**Purpose**: Summarize type constraints and properties

**Structure**:

| Constraint | Formal Definition | Verification |
|------------|-------------------|--------------|
| **C1** ID Non-Zero | `trace_id ≠ 0 ∧ span_id ≠ 0` | Type Rule |
| **C2** Temporal Order | `start_time ≤ end_time` | Type Rule |
| **C3** Parent Containment | `parent.start ≤ child.start ∧ child.end ≤ parent.end` | Type Rule |
| **C4** Trace Consistency | `∀s ∈ trace. s.trace_id = trace.id` | Type Rule |
| **C5** DAG Structure | `¬∃ cycle in parent-child graph` | Control Flow |

| Property | Theorem | Proof |
|----------|---------|-------|
| **Type Soundness** | Progress + Preservation | Coq (1,500 lines) |
| **Trace ID Consistency** | `∀s1,s2 ∈ trace. s1.trace_id = s2.trace_id` | Corollary |
| **Temporal Consistency** | `parent contains child temporally` | Property 2 |
| **DAG Structure** | `Acyclic parent-child relation` | Property 4 |

**Caption**: "OTLP type constraints (C1-C5) and verified properties. Type soundness is proven through Progress and Preservation theorems, mechanically verified in Coq and Isabelle/HOL."

---

### Table 4: Algebraic Framework Summary

**Location**: Section 4 (Algebraic Framework)  
**Size**: Single column  
**Purpose**: Summarize algebraic structures and their properties

**Structure**:

| Structure | Operation | Properties | Application |
|-----------|-----------|------------|-------------|
| **Monoid** | Trace composition `⊕` | Associativity, Identity | Parallel trace construction, Incremental aggregation |
| **Lattice** | LCA `⊓`, FCD `⊔` | Partial order, Meet/Join | Information flow analysis, Span hierarchy reasoning |
| **Category** | Transformation `∘` | Associativity, Identity | Pipeline correctness, Verified transformations |

| Theorem | Statement | Proof |
|---------|-----------|-------|
| **Theorem 2** | Monoid laws hold | Algebraic |
| **Theorem 3** | Lattice properties | Algebraic |
| **Theorem 4** | Category laws | Algebraic |
| **Theorem 5** | Composition preserves validity | Structural induction |
| **Theorem 6** | Transformation correctness | Property preservation |

**Caption**: "Algebraic framework summary. Traces form monoids (composition), span relationships form lattices (hierarchy), and transformations form categories (pipelines). Implemented in Haskell (2,800 lines) with 500+ QuickCheck properties verified."

---

## 🎨 Design Guidelines

### Visual Style

**Colors**:
- Control Flow: Blue (#0066CC)
- Data Flow: Orange (#FF6600)
- Execution Flow: Green (#00AA44)
- Violations: Red (#CC0000)
- Valid: Green (#00CC00)

**Fonts**:
- Main text: 10pt
- Captions: 9pt
- Labels: 8pt
- Code: Monospace (Courier/Monaco)

**Line Styles**:
- Solid: Primary relationships
- Dashed: Secondary relationships
- Dotted: Temporal relationships
- Thick: Emphasis

### Layout Principles

1. **Clarity**: Each figure should convey one main message
2. **Consistency**: Use same visual language across figures
3. **Simplicity**: Avoid unnecessary complexity
4. **Readability**: Ensure legibility when printed B&W

---

## 🛠️ Implementation Plan

### Phase 1: TikZ Diagrams (Week 1)

1. ✅ Figure 3 already exists (`fig6_triple_flow_analysis.tex`)
2. ⏳ Create Figure 1 (Framework Architecture) in TikZ
3. ⏳ Create Figure 2 (Type System) in TikZ
4. ⏳ Create Figure 4 (Evaluation) using pgfplots

### Phase 2: Tables (Week 1)

1. ⏳ Create Table 1 (Related Work) in LaTeX
2. ⏳ Create Table 2 (Evaluation Summary) in LaTeX
3. ⏳ Create Table 3 (Type System) in LaTeX
4. ⏳ Create Table 4 (Algebraic Framework) in LaTeX

### Phase 3: Integration (Week 2)

1. ⏳ Insert figures/tables into paper at appropriate locations
2. ⏳ Add cross-references throughout text
3. ⏳ Ensure captions are informative and complete
4. ⏳ Verify figure/table numbering

### Phase 4: Refinement (Week 2)

1. ⏳ Adjust sizes for page layout
2. ⏳ Ensure B&W readability
3. ⏳ Polish visual appearance
4. ⏳ Get feedback and iterate

---

## 📐 Size Constraints (ICSE 2026)

**Page Limit**: 11-12 pages (including figures/tables, excluding references)

**Figure Budget**:
- Maximum 4-5 figures recommended
- Each figure ~0.5 page
- Total figure space: ~2-2.5 pages

**Table Budget**:
- Maximum 4-5 tables recommended
- Each table ~0.3-0.5 page
- Total table space: ~1.5-2 pages

**Current Plan**:
- 4 Figures: ~2 pages
- 4 Tables: ~1.5 pages
- Text: ~8 pages
- References: ~0.5-1 page
- **Total**: ~12 pages ✓

---

## ✅ Quality Checklist

### Before Submission

- [ ] All figures have clear captions
- [ ] All tables have clear captions
- [ ] All figures/tables referenced in text
- [ ] Consistent visual style across figures
- [ ] Readable in B&W (for printing)
- [ ] Appropriate resolution (300 DPI minimum)
- [ ] LaTeX compilation without errors
- [ ] Figures/tables fit within page margins
- [ ] Cross-references work correctly
- [ ] Numbers/data match paper content

---

**Status**: Design complete, ready for implementation  
**Next Steps**: Create TikZ source files and LaTeX tables  
**Timeline**: 1-2 weeks for completion

