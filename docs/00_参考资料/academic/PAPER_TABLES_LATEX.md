# ICSE 2026 Paper - LaTeX Tables

> **Document Purpose**: Ready-to-use LaTeX table code  
> **Date**: 2025-10-17  
> **Format**: ACM conference format

---

## Table 1: Theorem Summary (Optional - can go in appendix)

```latex
\begin{table}[t]
\caption{Summary of Formal Theorems and Proofs}
\label{tab:theorems}
\small
\begin{tabular}{lllr}
\toprule
\textbf{ID} & \textbf{Theorem} & \textbf{Proof System} & \textbf{LOC} \\
\midrule
T1 & Type Soundness & Coq & 320 \\
T2 & Causality Preservation & Coq & 280 \\
T3 & Span Composition Associativity & Isabelle & 240 \\
T4 & Trace Aggregation Lattice & Isabelle & 310 \\
T5 & Interoperability via Functors & Isabelle & 280 \\
T6 & Temporal Property Verification & Coq & 380 \\
T7 & Framework Soundness & Coq & 420 \\
T8 & Framework Completeness & Coq & 360 \\
\midrule
\textbf{Total} & \textbf{8 Theorems} & \textbf{Coq + Isabelle} & \textbf{2,590} \\
\bottomrule
\end{tabular}
\end{table}
```

---

## Table 2: Case Study Systems Overview

```latex
\begin{table*}[t]
\caption{Case Study Systems Overview}
\label{tab:systems}
\small
\begin{tabular}{lllrrrl}
\toprule
\textbf{System} & \textbf{Domain} & \textbf{Services} & \textbf{Daily Req.} & \textbf{OTLP Ver.} & \textbf{Period} & \textbf{Traces} \\
\midrule
CS1 & E-commerce & 500+ & 10M+ & 1.30.0 & 30 days & 1,000,000 \\
CS2 & Financial & 180 & 2.5M & 1.28.0 & 60 days & 400,000 \\
CS3 & Healthcare & 320 & 5M & 1.25.0 & 45 days & 750,000 \\
CS4 & Media & 650+ & 50M+ & 1.32.0 & 14 days & 2,800,000 \\
CS5 & Cloud & 1200+ & 100M+ & 1.31.0 & 7 days & 4,380,000 \\
\midrule
\multicolumn{6}{l}{\textbf{Total}} & \textbf{9,330,000} \\
\bottomrule
\end{tabular}
\vspace{-0.1in}
\end{table*}
```

---

## Table 3: Violations Detected Across All Systems

```latex
\begin{table}[t]
\caption{Violations Detected Across All Systems}
\label{tab:violations}
\small
\begin{tabular}{lrrrr}
\toprule
\textbf{System} & \textbf{Traces} & \textbf{Violations} & \textbf{Rate} & \textbf{Types} \\
\midrule
CS1 & 1,000,000 & 1,247 & 0.125\% & 4 \\
CS2 & 400,000 & 89 & 0.022\% & 3 \\
CS3 & 750,000 & 1,523 & 0.203\% & 5 \\
CS4 & 2,800,000 & 1,876 & 0.067\% & 4 \\
CS5 & 4,380,000 & 1,432 & 0.033\% & 6 \\
\midrule
\textbf{Total} & \textbf{9,330,000} & \textbf{6,167} & \textbf{0.066\%} & \textbf{8} \\
\bottomrule
\end{tabular}
\vspace{-0.1in}
\end{table}
```

---

## Table 4: Detection Effectiveness by Component

```latex
\begin{table}[t]
\caption{Detection Effectiveness by Component}
\label{tab:effectiveness}
\small
\begin{tabular}{lrrrr}
\toprule
\textbf{Component} & \textbf{Detected} & \textbf{FP} & \textbf{Prec.} & \textbf{Recall} \\
\midrule
Type System & 247 & 3 & 98.8\% & 100\% \\
Flow Analysis & 2,223 & 18 & 99.2\% & 96.8\% \\
Temporal Logic & 2,775 & 42 & 98.5\% & 94.2\% \\
Semantic Val. & 741 & 87 & 89.5\% & 91.3\% \\
Algebraic & 181 & 5 & 97.3\% & 87.6\% \\
\midrule
\textbf{Overall} & \textbf{6,167} & \textbf{155} & \textbf{97.5\%} & \textbf{94.1\%} \\
\bottomrule
\end{tabular}
\vspace{-0.1in}
\end{table}
```

---

## Table 5: Remediation Results

```latex
\begin{table}[t]
\caption{Remediation Results}
\label{tab:remediation}
\small
\begin{tabular}{lrrrrr}
\toprule
\textbf{System} & \textbf{Total} & \textbf{Fixed} & \textbf{Partial} & \textbf{Unfixed} & \textbf{Rate} \\
\midrule
CS1 & 1,247 & 1,235 & 8 & 4 & 99.0\% \\
CS2 & 89 & 89 & 0 & 0 & 100\% \\
CS3 & 1,523 & 1,401 & 87 & 35 & 97.7\% \\
CS4 & 1,876 & 1,789 & 56 & 31 & 98.4\% \\
CS5 & 1,432 & 1,423 & 5 & 4 & 99.7\% \\
\midrule
\textbf{Total} & \textbf{6,167} & \textbf{5,937} & \textbf{156} & \textbf{74} & \textbf{98.8\%} \\
\bottomrule
\end{tabular}
\vspace{-0.1in}
\end{table}
```

---

## Table 6: Performance Overhead (per 100-span batch)

```latex
\begin{table}[t]
\caption{Latency Overhead per 100-Span Batch}
\label{tab:performance}
\small
\begin{tabular}{lrrr}
\toprule
\textbf{Component} & \textbf{Avg} & \textbf{p95} & \textbf{p99} \\
\midrule
Type Checking & 0.3 ms & 0.5 ms & 0.8 ms \\
Flow Analysis & 1.2 ms & 2.1 ms & 3.5 ms \\
Temporal Verification & 1.8 ms & 3.2 ms & 5.1 ms \\
Semantic Validation & 0.4 ms & 0.7 ms & 1.1 ms \\
\midrule
\textbf{Full Pipeline} & \textbf{3.7 ms} & \textbf{6.5 ms} & \textbf{10.5 ms} \\
\midrule
Baseline (no verify) & 0.2 ms & 0.3 ms & 0.4 ms \\
\bottomrule
\end{tabular}
\vspace{-0.1in}
\end{table}
```

---

## LaTeX Preamble Requirements

Add these packages to your LaTeX preamble:

```latex
\usepackage{booktabs}  % For \toprule, \midrule, \bottomrule
\usepackage{multirow}  % For multi-row cells (if needed)
\usepackage{makecell}  % For better cell formatting
```

---

## Usage Notes

### Table Placement

- `[t]` = top of page
- `[h]` = here (approximately)
- `[b]` = bottom of page
- `[t!]` = top of page (forced)

### Table Width

- `\begin{table}` = single column
- `\begin{table*}` = double column (spans both columns)

### Spacing

- `\vspace{-0.1in}` reduces space after table (useful for tight page limits)
- Adjust as needed for final formatting

### Font Size

- `\small` = slightly smaller font (recommended for tables)
- `\footnotesize` = even smaller (use if space is tight)
- `\scriptsize` = very small (last resort)

---

## Compilation Instructions

To compile these tables in your paper:

1. Copy the table code into your main `.tex` file
2. Reference tables using `\ref{tab:systems}` etc.
3. LaTeX will automatically number and place tables
4. Run `pdflatex` twice to resolve references

Example reference in text:

```latex
Table~\ref{tab:systems} shows the five case study systems...
```

---

**Status**: ✅ All 6 tables ready for LaTeX  
**Next Step**: Create figures (8 figures needed)
