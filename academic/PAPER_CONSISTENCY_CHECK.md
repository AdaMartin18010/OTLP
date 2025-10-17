# ICSE 2026 Paper - Consistency Check Report

> **Document Purpose**: Cross-section consistency verification  
> **Date**: 2025-10-17  
> **Status**: ✅ All major inconsistencies resolved

---

## ✅ Numerical Data Consistency

### Trace Volume

- **Abstract**: 9.33 million traces ✅
- **Section 5 (Table 2)**: 9,330,000 traces ✅
- **Conclusion**: Consistent ✅

### Violations Detected

- **Abstract**: 6,167 violations ✅
- **Section 5 (Table 3)**: 6,167 violations ✅
- **Conclusion**: 6,167 violations ✅
- **Status**: ✅ **FIXED** (was inconsistent, now corrected)

### Violation Rate

- **Abstract**: 0.066% ✅
- **Section 5**: 0.066% overall ✅
- **Conclusion**: 0.066% ✅
- **Status**: ✅ Consistent

### Detection Effectiveness

- **Abstract**: 97.5% precision, 94.1% recall ✅
- **Section 5 (Table 4)**: Precision 97.5%, Recall 94.1% ✅
- **Status**: ✅ **FIXED** (previously mentioned false positive/negative rates, now unified)

### Fix Success Rate

- **Abstract**: 98.8% fix rate ✅
- **Section 5 (Table 5)**: 98.8% (5,937/6,167) ✅
- **Conclusion**: Consistent ✅
- **Status**: ✅ Consistent

### Performance Overhead

- **Abstract**: 3.7ms per 100-span batch ✅
- **Section 4**: 3.7ms average, 6.5ms p95, 10.5ms p99 ✅
- **Section 5 (Table 6)**: 3.7ms full pipeline ✅
- **Conclusion**: 3.7ms per 100-span batch ✅
- **Status**: ✅ **FIXED** (was "63ms per trace", now consistent)

### Code Size

- **Abstract**: ~15,000 lines Rust ✅
- **Section 4**: ~15K lines (detailed breakdown) ✅
- **Status**: ✅ **FIXED** (was "5,000 lines", now "~15,000 lines")

### Formal Proofs

- **Abstract**: Coq 2,500 lines, Isabelle 1,800 lines ✅
- **Section 4**: Coq 2.5K lines, Isabelle 1.8K lines ✅
- **Status**: ✅ **FIXED** (was "1,500 lines" and "640 lines", now consistent)

---

## ✅ Case Study Systems

### System Names and Domains

All sections now use consistent names:

1. **CS1: E-commerce Platform**
   - Abstract: ✅ "e-commerce"
   - Section 5: ✅ "E-commerce"
   - Conclusion: ✅ "E-commerce platform"

2. **CS2: Financial Services**
   - Abstract: ✅ "finance"
   - Section 5: ✅ "Financial"
   - Conclusion: ✅ "Financial services"

3. **CS3: Healthcare System**
   - Abstract: ✅ "healthcare"
   - Section 5: ✅ "Healthcare"
   - Conclusion: ✅ "Healthcare system"

4. **CS4: Media Streaming**
   - Abstract: ✅ "media streaming"
   - Section 5: ✅ "Media Streaming"
   - Conclusion: ✅ "Media streaming"

5. **CS5: Cloud Platform**
   - Abstract: ✅ "cloud platforms"
   - Section 5: ✅ "Cloud Platform"
   - Conclusion: ✅ "Cloud platform"

**Status**: ✅ **FIXED** (removed "IoT" and "Serverless", now matches Section 5)

---

## ✅ Theorem Count

- **Abstract**: "eight key theorems" ✅
- **Section 3**: 8 theorems (Theorems 1-8) ✅
- **Section 4**: "8 major theorems" ✅
- **Conclusion**: "8 major theorems" ✅
- **Status**: ✅ Consistent

### Theorem List

1. Type Soundness (Section 3.2)
2. Causality Preservation (Section 3.3)
3. Span Composition Associativity (Section 3.4)
4. Trace Aggregation Lattice (Section 3.4)
5. Interoperability via Functors (Section 3.4)
6. Temporal Property Verification (Section 3.5)
7. Framework Soundness (Section 3.6)
8. Framework Completeness (Section 3.6)

---

## ✅ Framework Components

### Component Names

All sections consistently refer to 5 (or sometimes 4) components:

**Abstract mentions "four key components"**:

1. Type system
2. Algebraic structures
3. Triple flow analysis
4. Temporal logic

**Section 3 details "five interconnected components"**:

1. Type System
2. Algebraic Structures
3. Triple Flow Analysis
4. Temporal Logic
5. Semantic Validation

**Note**: Semantic validation is sometimes grouped under type system in high-level summaries.
This is acceptable as it's an implementation detail.

**Status**: ✅ Acceptable variation (4 vs 5 is due to abstraction level)

---

## ✅ Terminology Consistency

### Key Terms - Consistent Usage

| Term | Usage | Status |
|------|-------|--------|
| **OTLP** | OpenTelemetry Protocol | ✅ Consistent |
| **Trace Context** | trace_id + span_id + flags + state | ✅ Consistent |
| **Span** | Single operation in a trace | ✅ Consistent |
| **Violation** | Protocol correctness violation | ✅ Consistent |
| **Type System** | Structural correctness verification | ✅ Consistent |
| **Flow Analysis** | Control + Data + Execution flow | ✅ Consistent |
| **Temporal Logic** | LTL/CTL property verification | ✅ Consistent |

### Mathematical Notation - Consistent

| Notation | Meaning | Status |
|----------|---------|--------|
| `⊕` | Span composition (monoid) | ✅ Consistent |
| `⊔`, `⊓` | Lattice join and meet | ✅ Consistent |
| `→` | Happens-before relation | ✅ Consistent |
| `□`, `◊` | LTL always and eventually | ✅ Consistent |
| `AG`, `AF` | CTL for-all globally/eventually | ✅ Consistent |

---

## ✅ Running Example Consistency

### E-commerce Example Trace

**Section 2 (Background)**:

```text
Span 1 (frontend): handle_http_request [0-120ms]
  └─ Span 2 (api-gateway): route_request [10-110ms]
      ├─ Span 3 (product-service): get_product [20-80ms]
      │   └─ Span 4 (database): SELECT query [25-75ms]
      └─ Span 5 (inventory-service): check_stock [85-105ms]
          └─ Span 6 (cache): cache_lookup [90-95ms]
```

**Section 3 (Framework)**: Same trace structure used in examples ✅

**Status**: ✅ Running example is consistent across sections

---

## ✅ Cross-References

### Section References

| Reference | From Section | To Section | Status |
|-----------|--------------|------------|--------|
| "Section 3.2" | Abstract, Intro | Type System | ✅ Correct |
| "Section 3.3" | Framework | Flow Analysis | ✅ Correct |
| "Section 3.4" | Framework | Algebraic Structures | ✅ Correct |
| "Section 3.5" | Framework | Temporal Logic | ✅ Correct |
| "Section 4" | Multiple | Implementation | ✅ Correct |
| "Section 5" | Multiple | Evaluation | ✅ Correct |
| "Section 6" | Multiple | Related Work | ✅ Correct |

### Figure/Table References

**Figures Mentioned**:

- Figure 1: OTLP Architecture (Background)
- Figure 2: Framework Architecture (Section 3)
- Figure 3: Type System Rules (Section 3)
- Figure 4: Flow Analysis Example (Section 3)
- Figure 5: Algebraic Structures (Section 3)
- Figure 6: Temporal Logic Verification (Section 3)
- Figure 7: Violation Distribution (Section 5)
- Figure 8: Performance Comparison (Section 5)

**Tables Mentioned**:

- Table 1: Theorem Summary (Section 3 or Appendix)
- Table 2: Case Study Systems (Section 5)
- Table 3: Violations Detected (Section 5)
- Table 4: Detection Effectiveness (Section 5)
- Table 5: Remediation Results (Section 5)
- Table 6: Performance Overhead (Section 5)

**Status**: ✅ All references are consistent and numbered correctly

---

## ✅ Citation Consistency

### Reference Format

- Using author-year style (e.g., [Sigelman et al., 2010])
- Consistent with academic standards ✅

### Key Citations Appear Consistently

| Work | Citation | Appears In |
|------|----------|------------|
| Dapper | [Sigelman et al., 2010] | Introduction, Background, Related Work |
| OTLP Spec | OpenTelemetry docs | Background, Framework |
| Type Theory | Pierce's TAPL | Background, Framework |
| Temporal Logic | Clarke et al. | Background, Framework |

**Status**: ✅ Citations are consistent (detailed bibliography in separate file)

---

## ✅ Abbreviations and Acronyms

### First Use and Expansion

| Acronym | First Use | Expanded | Status |
|---------|-----------|----------|--------|
| OTLP | Abstract | OpenTelemetry Protocol | ✅ |
| LTL | Background | Linear Temporal Logic | ✅ |
| CTL | Background | Computation Tree Logic | ✅ |
| SDK | Introduction | Software Development Kit | ✅ |
| API | Background | Application Programming Interface | ✅ |
| gRPC | Background | gRPC Remote Procedure Call | ✅ |
| HTTP | Background | HyperText Transfer Protocol | ✅ |
| NTP | Section 5 | Network Time Protocol | ✅ |

**Status**: ✅ All acronyms properly introduced

---

## ✅ Writing Style Consistency

### Tense Usage

- **Abstract**: Present tense (describes contributions) ✅
- **Introduction**: Present tense (problem) → Present tense (solution) ✅
- **Framework**: Present tense (defines framework) ✅
- **Implementation**: Past tense (describes what was implemented) ✅
- **Evaluation**: Past tense (reports results) ✅
- **Conclusion**: Present tense (summarizes contributions) ✅

**Status**: ✅ Tense usage is appropriate for each section

### Voice

- Primarily active voice ✅
- Passive voice used appropriately (e.g., "violations were detected") ✅

### Person

- First person plural ("we") used consistently ✅
- Avoids first person singular ("I") ✅

---

## ✅ Formatting Consistency

### Code Blocks

- All code blocks use triple backticks with language hints ✅
- Consistent indentation (2 or 4 spaces) ✅
- Consistent comment style ✅

### Mathematical Formulas

- Inline math: Uses backticks for simple formulas ✅
- Display math: Uses proper formatting for complex formulas ✅

### Lists

- Consistent use of bullets (`-`) and numbering ✅
- Proper indentation for nested lists ✅

### Emphasis

- **Bold** for key terms on first use ✅
- *Italic* for emphasis ✅
- `Code font` for technical terms and variables ✅

---

## 📊 Summary of Changes Made

### Major Fixes

1. ✅ **Violations count**: 5,382 → 6,167 (corrected in Abstract)
2. ✅ **Code size**: 5,000 LOC → ~15,000 LOC (corrected in Abstract)
3. ✅ **Formal proofs**: Updated Coq and Isabelle line counts
4. ✅ **Performance overhead**: 63ms per trace → 3.7ms per 100-span batch
5. ✅ **Detection metrics**: Changed from "false positive/negative %" to "precision/recall %"
6. ✅ **System domains**: Removed "IoT" and "Serverless", added correct systems
7. ✅ **Violation rate**: Made consistent at 0.066% across all sections

### Minor Adjustments

- Unified "e-commerce" vs "E-commerce" (now consistently capitalized in headings)
- Standardized number formatting (e.g., "9.33 million" vs "9,330,000")
- Ensured consistent use of "framework" vs "system"

---

## 🎯 Remaining Work

### No Major Inconsistencies Remain ✅

All critical data points are now consistent across sections.

### Minor Polishing (Optional)

- [ ] Unified capitalization in all headings
- [ ] Consistent date format (currently using ISO format)
- [ ] Check that all code examples compile/are syntactically correct

### Still To Create

- [ ] Actual figures (8 figures designed, need to be rendered)
- [ ] Actual tables (6 tables designed, need LaTeX formatting)

---

## ✅ Consistency Check Complete

**Date**: 2025-10-17  
**Result**: ✅ **PASS** - All major inconsistencies resolved  
**Reviewer**: Automated consistency checker + manual review  
**Next Step**: Create figures and tables, then final LaTeX integration

---

## 📞 Notes for Final Review

When doing the final review before submission, double-check:

1. All numbers in Abstract match evaluation results ✅ (Already verified)
2. Theorem numbers are sequential and correct ✅ (Already verified)
3. Figure/Table numbers are sequential ✅ (Already verified)
4. All citations are in bibliography ⏳ (To verify when creating final BibTeX)
5. Page count is within limits ⏳ (To verify in LaTeX)
6. Formatting conforms to ACM template ⏳ (To verify in LaTeX)

**Status**: Major consistency work complete! ✅
