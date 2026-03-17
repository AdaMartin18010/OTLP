# LaTeX Integration Guide for ICSE 2026 Paper

> **Purpose**: Step-by-step guide to compile the paper  
> **Date**: 2025-10-17  
> **Target**: Complete LaTeX compilation

---

## 📁 File Structure

```text
academic/
├── paper_main.tex              # Main LaTeX document
├── references.bib              # BibTeX bibliography
├── sections/                   # Individual sections
│   ├── 01_introduction.tex
│   ├── 02_background.tex
│   ├── 03_framework.tex
│   ├── 04_implementation.tex
│   ├── 05_evaluation.tex
│   ├── 06_related_work.tex
│   └── 07_conclusion.tex
├── figures/                    # Generated figures (PDF)
└── tables/                     # Table code (included in sections)
```

---

## 🚀 Quick Start

### Step 1: Convert Markdown to LaTeX

Each section needs to be converted from Markdown to LaTeX format. I'll provide conversion templates for each section.

**Conversion priorities**:

1. ✅ Main structure created (`paper_main.tex`)
2. 📝 Need to convert: 7 section files
3. 📝 Need to create: `references.bib`

### Step 2: Required Software

**Essential**:

- LaTeX distribution (TeXLive 2023+ or MiKTeX)
- ACM template (included in `acmart` package)

**Optional but recommended**:

- Overleaf (online LaTeX editor, no installation needed)
- VS Code with LaTeX Workshop extension

### Step 3: Compilation

```bash
# Standard compilation
pdflatex paper_main.tex
bibtex paper_main
pdflatex paper_main.tex
pdflatex paper_main.tex

# Or use latexmk for automatic compilation
latexmk -pdf paper_main.tex
```

---

## 📝 Section Conversion Status

### Already Created

- ✅ `paper_main.tex` - Main document with abstract

### Need to Create (7 sections)

1. **Section 1: Introduction** (1.5 pages)
   - Source: `PAPER_DRAFT_Abstract_Introduction.md`
   - Target: `sections/01_introduction.tex`
   - Key elements: Motivation, Problem, Contributions

2. **Section 2: Background** (1.5 pages)
   - Source: `PAPER_DRAFT_Section2_Background.md`
   - Target: `sections/02_background.tex`
   - Key elements: OTLP overview, Running example

3. **Section 3: Framework** (3.0 pages) ⭐ CORE
   - Source: `PAPER_DRAFT_Section3_Framework.md`
   - Target: `sections/03_framework.tex`
   - Key elements: 5 components, 8 theorems, algorithms

4. **Section 4: Implementation** (1.5 pages)
   - Source: `PAPER_DRAFT_Section4_Implementation.md`
   - Target: `sections/04_implementation.tex`
   - Key elements: Rust code, Coq/Isabelle proofs

5. **Section 5: Evaluation** (2.0 pages) ⭐ CORE
   - Source: `PAPER_DRAFT_Section5_Evaluation.md`
   - Target: `sections/05_evaluation.tex`
   - Key elements: 5 case studies, tables, results

6. **Section 6: Related Work** (1.0 page)
   - Source: `PAPER_DRAFT_Section6_RelatedWork.md`
   - Target: `sections/06_related_work.tex`
   - Key elements: Comparison with prior work

7. **Section 7: Conclusion** (0.5 page)
   - Source: `PAPER_DRAFT_Section7_Conclusion.md`
   - Target: `sections/07_conclusion.tex`
   - Key elements: Summary, future work

---

## 📚 BibTeX References

Create `references.bib` with all 44 references from `OTLP_References_Bibliography.md`.

**Key references to include**:

- Dapper (Google's distributed tracing)
- OpenTelemetry specification
- Formal verification papers (TLA+, Coq, Isabelle)
- Type theory references
- Temporal logic papers

---

## 🎨 Figures Integration

### Option 1: TikZ (Recommended)

- Use the TikZ code from `PAPER_FIGURES_TIKZ.md`
- Directly embed in LaTeX sections
- Pros: Vector graphics, consistent fonts
- Cons: Compilation slower

### Option 2: External PDFs

- Create figures using draw.io or Python
- Export as PDF
- Include with `\includegraphics`
- Pros: Faster compilation
- Cons: Need separate files

**Figures to create**:

1. Figure 1: OTLP Architecture (in Section 2)
2. Figure 2: Framework Architecture (in Section 3)
3. Figure 3: Type System Rules (in Section 3)
4. Figure 4: Flow Analysis (in Section 3)
5. Figure 5: Algebraic Structures (in Section 3)
6. Figure 6: Temporal Logic (in Section 3)
7. Figure 7: Violation Distribution (in Section 5)
8. Figure 8: Performance (in Section 5)

---

## 📊 Tables Integration

Tables are already in LaTeX format in `PAPER_TABLES_LATEX.md`.

**Copy directly into sections**:

- Table 2 → Section 5 (Case Studies)
- Table 3 → Section 5 (Violations)
- Table 4 → Section 5 (Effectiveness)
- Table 5 → Section 5 (Remediation)
- Table 6 → Section 5 (Performance)

---

## 🔧 Conversion Templates

### Markdown to LaTeX Basics

**Headers**:

```markdown
### 3.1 Title    →    \subsection{Title}
#### 3.1.1 Sub   →    \subsubsection{Sub}
```

**Text formatting**:

```markdown
**bold**         →    \textbf{bold}
*italic*         →    \textit{italic}
`code`           →    \texttt{code}
```

**Lists**:

```markdown
- Item 1         →    \begin{itemize}
- Item 2         →      \item Item 1
                 →      \item Item 2
                 →    \end{itemize}
```

**Code blocks**:

```markdown
```rust          →    \begin{lstlisting}[language=Rust]
code             →    code
```              →    \end{lstlisting}
```

**Math**:

```markdown
`s ⊕ t`          →    $s \oplus t$
```

**References**:

```markdown
(Section 3.2)    →    (Section~\ref{sec:type-system})
[Smith 2020]     →    \cite{smith2020}
```

---

## 📋 Conversion Checklist

### For Each Section

- [ ] Create `sections/XX_name.tex` file
- [ ] Convert headers to `\section`, `\subsection`, `\subsubsection`
- [ ] Convert text formatting (bold, italic, code)
- [ ] Convert lists (itemize, enumerate)
- [ ] Convert code blocks to `lstlisting` or `verbatim`
- [ ] Convert math notation
- [ ] Add figure references
- [ ] Add table references
- [ ] Add citations
- [ ] Add labels for cross-references

### For Figures

- [ ] Either embed TikZ code or create external PDFs
- [ ] Place in appropriate sections
- [ ] Add captions
- [ ] Add labels (`\label{fig:name}`)
- [ ] Reference in text (`Figure~\ref{fig:name}`)

### For Tables

- [ ] Copy LaTeX code from `PAPER_TABLES_LATEX.md`
- [ ] Verify column alignment
- [ ] Add captions
- [ ] Add labels (`\label{tab:name}`)
- [ ] Reference in text (`Table~\ref{tab:name}`)

### For References

- [ ] Create `references.bib`
- [ ] Add all 44 references
- [ ] Use consistent citation keys
- [ ] Verify BibTeX format

---

## 🎯 Priority Order

### Phase 1: Core Structure (Priority: High)

1. ✅ Create `paper_main.tex`
2. Create `references.bib` (basic version with 10-15 key refs)
3. Convert Section 1 (Introduction)
4. Convert Section 3 (Framework) - CORE SECTION

### Phase 2: Complete Sections (Priority: High)

1. Convert Section 5 (Evaluation) - CORE SECTION
2. Convert Section 2 (Background)
3. Convert Section 4 (Implementation)

### Phase 3: Supporting Sections (Priority: Medium)

1. Convert Section 6 (Related Work)
2. Convert Section 7 (Conclusion)
3. Complete `references.bib` (all 44 refs)

### Phase 4: Figures and Tables (Priority: Medium)

1. Add all 6 tables (already in LaTeX)
2. Create or embed 8 figures

### Phase 5: Polish (Priority: Low)

1. Fine-tune formatting
2. Check page count
3. Proofread

---

## 🚦 Current Status

- ✅ Main structure created
- 📝 Need: Convert 7 sections from Markdown to LaTeX
- 📝 Need: Create BibTeX file
- 📝 Need: Integrate figures
- 📝 Need: Final compilation test

**Estimated time**: 4-6 hours of focused work

---

## 💡 Tips

### Using Overleaf

1. Create new project
2. Upload `paper_main.tex`
3. Upload ACM template files
4. Create section files directly in Overleaf
5. Compile online (no local setup needed)

### Local LaTeX

1. Install TeXLive or MiKTeX
2. Use VS Code with LaTeX Workshop
3. Enable auto-compile on save
4. Use SyncTeX for PDF preview

### Common Issues

**Issue**: Missing ACM template

- **Fix**: `\usepackage{acmart}` should auto-download, or manually download from CTAN

**Issue**: TikZ compilation slow

- **Fix**: Use externalization or switch to PDF figures

**Issue**: Reference not found

- **Fix**: Run `bibtex` then `pdflatex` twice

---

## 📞 Next Steps

1. **Now**: Start converting Section 1 (Introduction) to LaTeX
2. **Next**: Convert Section 3 (Framework) and Section 5 (Evaluation)
3. **Then**: Create complete `references.bib`
4. **Finally**: First compilation test

---

**Status**: Main structure ready, conversion in progress  
**Next milestone**: First successful PDF compilation  
**Target date**: 2025-10-24
