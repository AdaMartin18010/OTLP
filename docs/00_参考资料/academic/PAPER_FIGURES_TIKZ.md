# ICSE 2026 Paper - TikZ Figure Code

> **Document Purpose**: Ready-to-use TikZ figure code  
> **Date**: 2025-10-17  
> **Format**: LaTeX/TikZ for ACM conference

---

## Figure 1: OTLP Architecture Overview

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  node distance=1cm,
  box/.style={rectangle, draw, minimum width=2.5cm, minimum height=0.8cm, align=center},
  arrow/.style={->, >=stealth, thick}
]

% Instrumented Applications
\node[box, fill=blue!20] (app1) {Application 1\\(Java)};
\node[box, fill=blue!20, right=of app1] (app2) {Application 2\\(Python)};
\node[box, fill=blue!20, right=of app2] (app3) {Application 3\\(Go)};

% OTLP Exporter layer
\node[box, fill=green!20, below=0.5cm of app2] (otlp) {OTLP Exporter\\(gRPC/HTTP)};

% Collector
\node[box, fill=yellow!20, below=0.5cm of otlp, minimum width=7cm] (collector) {OpenTelemetry Collector\\(Processors, Exporters)};

% Backends
\node[box, fill=red!20, below left=0.5cm and 0.5cm of collector] (backend1) {Jaeger};
\node[box, fill=red!20, below=0.5cm of collector] (backend2) {Prometheus};
\node[box, fill=red!20, below right=0.5cm and 0.5cm of collector] (backend3) {Custom Backend};

% Arrows
\draw[arrow] (app1) -- (otlp);
\draw[arrow] (app2) -- (otlp);
\draw[arrow] (app3) -- (otlp);
\draw[arrow] (otlp) -- (collector);
\draw[arrow] (collector) -- (backend1);
\draw[arrow] (collector) -- (backend2);
\draw[arrow] (collector) -- (backend3);

\end{tikzpicture}
\caption{OTLP Architecture: Applications export telemetry via OTLP to collectors, which process and forward to backends.}
\label{fig:otlp-arch}
\end{figure}
```

---

## Figure 2: Framework Architecture (5 Layers)

```latex
\begin{figure*}[t]
\centering
\begin{tikzpicture}[
  layer/.style={rectangle, draw, minimum width=12cm, minimum height=1.2cm, align=center, font=\small},
  component/.style={rectangle, draw, minimum width=2.2cm, minimum height=0.8cm, align=center, font=\footnotesize},
  arrow/.style={->, >=stealth, thick}
]

% Input layer
\node[layer, fill=gray!10] (input) at (0, 0) {\textbf{OTLP Data Stream}\\(Traces, Metrics, Logs from SDKs → Collector → Backend)};

% Verification layers
\node[layer, fill=blue!10, below=0.3cm of input] (verify) {\textbf{Formal Verification Framework}};

\node[component, fill=blue!20, below left=0.5cm and 4.5cm of verify] (type) {1. Type\\System};
\node[component, fill=blue!20, right=0.2cm of type] (algebra) {2. Algebraic\\Structures};
\node[component, fill=blue!20, right=0.2cm of algebra] (flow) {3. Triple Flow\\Analysis};
\node[component, fill=blue!20, right=0.2cm of flow] (temporal) {4. Temporal\\Logic};
\node[component, fill=blue!20, right=0.2cm of temporal] (semantic) {5. Semantic\\Validation};

% Properties
\node[font=\scriptsize, below=0.1cm of type] {Structural};
\node[font=\scriptsize, below=0.1cm of algebra] {Compositional};
\node[font=\scriptsize, below=0.1cm of flow] {Causality};
\node[font=\scriptsize, below=0.1cm of temporal] {System-wide};
\node[font=\scriptsize, below=0.1cm of semantic] {Convention};

% Output layer
\node[layer, fill=green!10, below=1.5cm of flow] (output) {\textbf{Verification Results}\\Violations Detected • Correctness Proofs • Diagnostic Reports};

% Arrows
\draw[arrow] (input) -- (verify);
\draw[arrow] (verify) -- (type);
\draw[arrow] (verify) -- (algebra);
\draw[arrow] (verify) -- (flow);
\draw[arrow] (verify) -- (temporal);
\draw[arrow] (verify) -- (semantic);
\draw[arrow] (type) -- (output);
\draw[arrow] (algebra) -- (output);
\draw[arrow] (flow) -- (output);
\draw[arrow] (temporal) -- (output);
\draw[arrow] (semantic) -- (output);

\end{tikzpicture}
\caption{Framework Architecture: Five verification components operate on OTLP data streams to ensure correctness at different abstraction levels.}
\label{fig:framework}
\end{figure*}
```

---

## Figure 3: Type System Example (Simplified)

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  node distance=0.3cm,
  box/.style={rectangle, draw, minimum width=6cm, minimum height=0.6cm, align=left, font=\footnotesize}
]

\node[box, fill=yellow!10] (span) {
  \texttt{Span} = \{\\
  \quad context: SpanContext,\\
  \quad parent\_id: Option[SpanID],\\
  \quad start\_time: \{t: Int64 | t ≥ 0\},\\
  \quad end\_time: \{t: Int64 | t ≥ start\_time\}\\
  \}
};

\node[below=0.5cm of span, font=\small] (constraint) {
  Type constraint ensures: \texttt{end\_time ≥ start\_time}
};

\node[box, fill=red!10, below=0.3cm of constraint] (violation) {
  Violation Example:\\
  start\_time = 1000, end\_time = 500 \quad ❌ Rejected
};

\node[box, fill=green!10, below=0.3cm of violation] (valid) {
  Valid Example:\\
  start\_time = 1000, end\_time = 1500 \quad ✅ Accepted
};

\end{tikzpicture}
\caption{Type System ensures structural correctness: dependent types enforce that end time cannot precede start time.}
\label{fig:type-system}
\end{figure}
```

---

## Figure 4: Flow Analysis Example (Trace DAG)

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  node distance=1.5cm,
  span/.style={circle, draw, minimum size=1cm, font=\small},
  arrow/.style={->, >=stealth}
]

% Spans
\node[span, fill=blue!20] (s1) {S1};
\node[span, fill=blue!20, below left=of s1] (s2) {S2};
\node[span, fill=blue!20, below right=of s1] (s3) {S3};
\node[span, fill=blue!20, below=of s2] (s4) {S4};
\node[span, fill=blue!20, below=of s3] (s5) {S5};

% Call graph edges
\draw[arrow] (s1) -- (s2);
\draw[arrow] (s1) -- (s3);
\draw[arrow] (s2) -- (s4);
\draw[arrow] (s3) -- (s5);

% Labels
\node[right=0.1cm of s1, font=\scriptsize] {frontend};
\node[right=0.1cm of s2, font=\scriptsize] {api-gateway};
\node[right=0.1cm of s3, font=\scriptsize] {product-svc};
\node[right=0.1cm of s4, font=\scriptsize] {database};
\node[right=0.1cm of s5, font=\scriptsize] {cache};

% Properties checked
\node[below=2cm of s1, font=\footnotesize, align=left] {
  \textbf{Verified Properties:}\\
  ✓ Acyclic (no cycles)\\
  ✓ Connected (all reachable from S1)\\
  ✓ Context preserved (same TraceID)
};

\end{tikzpicture}
\caption{Flow Analysis constructs call graph from parent-child relationships and verifies acyclicity, connectedness, and context propagation.}
\label{fig:flow-analysis}
\end{figure}
```

---

## Figure 5: Algebraic Structures (Monoid + Lattice)

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  box/.style={rectangle, draw, minimum width=5cm, minimum height=2cm, align=center},
  node distance=0.5cm
]

% Monoid
\node[box, fill=blue!10] (monoid) {
  \textbf{Monoid (Span Composition)}\\[0.2cm]
  $(Span, ⊕, ε)$\\[0.1cm]
  \texttt{s1 ⊕ s2 ⊕ s3} (any order)\\[0.1cm]
  Associative • Identity
};

% Lattice
\node[box, fill=green!10, below=of monoid] (lattice) {
  \textbf{Lattice (Trace Aggregation)}\\[0.2cm]
  $(TraceViews, ⊔, ⊓)$\\[0.1cm]
  \texttt{v1 ⊔ v2 ⊔ v3} (merge views)\\[0.1cm]
  Idempotent • Commutative
};

% Benefits
\node[right=1.5cm of monoid, font=\footnotesize, align=left] (benefit1) {
  → Out-of-order\\
  \quad span processing
};

\node[right=1.5cm of lattice, font=\footnotesize, align=left] (benefit2) {
  → Partial trace\\
  \quad aggregation
};

\draw[->, >=stealth] (monoid) -- (benefit1);
\draw[->, >=stealth] (lattice) -- (benefit2);

\end{tikzpicture}
\caption{Algebraic Structures: Monoids enable out-of-order span composition; Lattices enable consistent trace aggregation from partial views.}
\label{fig:algebra}
\end{figure}
```

---

## Figure 6: Temporal Logic Verification Flow

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  node distance=1cm,
  box/.style={rectangle, draw, minimum width=4cm, minimum height=0.8cm, align=center, font=\small},
  arrow/.style={->, >=stealth, thick}
]

\node[box, fill=yellow!10] (trace) {Trace Stream};
\node[box, fill=blue!10, below=of trace] (ltl) {LTL/CTL Properties};
\node[box, fill=green!10, below=of ltl] (checker) {Model Checker};
\node[box, fill=red!10, below left=of checker] (viol) {Violations};
\node[box, fill=green!10, below right=of checker] (pass) {Verified ✓};

\draw[arrow] (trace) -- (checker);
\draw[arrow] (ltl) -- (checker);
\draw[arrow] (checker) -- (viol);
\draw[arrow] (checker) -- (pass);

% Property examples
\node[right=0.5cm of ltl, font=\footnotesize, align=left] {
  Examples:\\
  □(started → ◊ended)\\
  AG(valid\_trace\_id)
};

\end{tikzpicture}
\caption{Temporal Logic Verification: LTL/CTL properties are checked against trace streams using model checking.}
\label{fig:temporal}
\end{figure}
```

---

## Figure 7: Violation Type Distribution (Bar Chart)

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[
  ybar,
  width=7cm,
  height=5cm,
  bar width=0.4cm,
  ylabel={Count},
  xlabel={Violation Type},
  xticklabels={Timestamp, Context, Resource, Invalid Rel., Type, Causality, Semantic, Other},
  x tick label style={rotate=45, anchor=east, font=\scriptsize},
  ymin=0,
  ymax=3000,
  legend style={at={(0.5,-0.3)}, anchor=north, legend columns=1, font=\scriptsize},
  nodes near coords,
  every node near coord/.append style={font=\tiny}
]
\addplot coordinates {
  (1, 2775)  % Timestamp
  (2, 1729)  % Context
  (3, 741)   % Resource
  (4, 494)   % Invalid Rel.
  (5, 247)   % Type
  (6, 123)   % Causality
  (7, 62)    % Semantic
  (8, 10)    % Other
};
\end{axis}
\end{tikzpicture}
\caption{Violation Type Distribution: Timestamp violations (45\%) and context propagation errors (28\%) are the most common.}
\label{fig:violations}
\end{figure}
```

**Note**: Requires `\usepackage{pgfplots}` and `\pgfplotsset{compat=1.18}`

---

## Figure 8: Performance Comparison (Grouped Bar Chart)

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[
  ybar,
  width=7cm,
  height=5cm,
  bar width=0.2cm,
  ylabel={Latency (ms)},
  xlabel={Trace Size (spans)},
  xticklabels={10, 50, 100, 200, 500},
  ymin=0,
  ymax=20,
  legend style={at={(0.5,-0.25)}, anchor=north, legend columns=2, font=\scriptsize},
  nodes near coords,
  every node near coord/.append style={font=\tiny}
]
\addplot coordinates {(1,0.4) (2,2.1) (3,3.7) (4,7.8) (5,18.5)};
\addplot coordinates {(1,0.02) (2,0.08) (3,0.2) (4,0.35) (5,0.9)};
\legend{Our Framework, Baseline}
\end{axis}
\end{tikzpicture}
\caption{Performance Comparison: Our framework adds minimal overhead (3.7ms for 100-span trace) compared to baseline.}
\label{fig:performance}
\end{figure}
```

---

## LaTeX Preamble Requirements

Add these packages to your LaTeX preamble:

```latex
\usepackage{tikz}
\usetikzlibrary{positioning, arrows.meta, shapes, calc}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
```

---

## Compilation Notes

### TikZ Benefits

- **Vector graphics**: Scales perfectly at any zoom level
- **Consistent fonts**: Matches paper typography
- **Easy to modify**: Edit coordinates and styles in LaTeX
- **Small file size**: No embedded images

### Alternative Tools

If TikZ is too complex, you can also create figures with:

1. **draw.io** → Export as PDF → Include with `\includegraphics`
2. **Python matplotlib** → Export as PDF
3. **Inkscape** → Export as PDF

### Including External PDFs

```latex
\begin{figure}[t]
\centering
\includegraphics[width=0.9\columnwidth]{figures/framework.pdf}
\caption{Framework Architecture}
\label{fig:framework}
\end{figure}
```

---

**Status**: ✅ All 8 figures designed (TikZ code provided)  
**Alternative**: Can also use external tools and export to PDF  
**Next Step**: Integrate tables and figures into main paper LaTeX file
