# ICSE 2026 论文编译指南

> **创建时间**: 2025年10月20日  
> **状态**: LaTeX源文件100%就绪，等待编译

---

## 📋 编译前准备

### 1. 安装LaTeX发行版

#### Windows系统

**推荐**: TeX Live（完整安装）

```powershell
# 下载TeX Live安装器
# 访问: https://tug.org/texlive/acquire-netinstall.html
# 下载: install-tl-windows.exe

# 运行安装（完整安装约7GB，需要1-2小时）
.\install-tl-windows.exe

# 或使用MiKTeX（较小，按需下载包）
# 访问: https://miktex.org/download
# 下载并安装MiKTeX
```

**验证安装**:

```powershell
pdflatex --version
bibtex --version
```

#### Linux系统

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install texlive-full

# Fedora/CentOS
sudo yum install texlive-scheme-full
```

#### macOS系统

```bash
# 使用Homebrew安装MacTeX
brew install --cask mactex

# 或下载完整安装包
# 访问: https://tug.org/mactex/
```

---

## 🚀 编译步骤

### 标准编译流程

```bash
cd academic

# 第一次pdflatex编译（生成.aux文件）
pdflatex ICSE2026_Paper_Main.tex

# 处理bibliography（生成.bbl文件）
bibtex ICSE2026_Paper_Main

# 第二次pdflatex编译（处理citations）
pdflatex ICSE2026_Paper_Main.tex

# 第三次pdflatex编译（解析cross-references）
pdflatex ICSE2026_Paper_Main.tex
```

### 使用编译脚本

**Windows PowerShell** (`compile.ps1`):

```powershell
# 编译论文
.\compile.ps1

# 清理临时文件
.\compile.ps1 -clean
```

**Linux/macOS** (`compile.sh`):

```bash
# 编译论文
./compile.sh

# 清理临时文件
./compile.sh clean
```

---

## 📊 文件结构

### 源文件组织

```text
academic/
├── ICSE2026_Paper_Main.tex          # 主文件
├── references.bib                   # Bibliography
├── sections/                        # 章节文件
│   ├── 01_introduction.tex          # Section 1
│   ├── 02_background.tex            # Section 2
│   ├── 03_formal_semantics.tex      # Section 3
│   ├── 04_algebraic_framework.tex   # Section 4
│   ├── 05_triple_flow_analysis.tex  # Section 5
│   ├── 06_related_work.tex          # Section 6
│   └── 07_conclusion.tex            # Section 7
├── figures/                         # 图表文件
│   ├── fig1_framework_architecture.tex
│   ├── fig2_type_system.tex
│   ├── fig4_evaluation_results.tex
│   └── fig6_triple_flow_analysis.tex
└── tables/                          # 表格文件
    ├── table1_related_work.tex
    ├── table2_evaluation_summary.tex
    ├── table3_type_system_properties.tex
    └── table4_algebraic_framework.tex
```

### 生成文件

编译成功后会生成：

```text
academic/
├── ICSE2026_Paper_Main.pdf          # 最终PDF ⭐
├── ICSE2026_Paper_Main.aux          # 辅助文件
├── ICSE2026_Paper_Main.bbl          # Bibliography处理结果
├── ICSE2026_Paper_Main.blg          # Bibliography日志
├── ICSE2026_Paper_Main.log          # 编译日志
├── ICSE2026_Paper_Main.out          # 超链接信息
└── ICSE2026_Paper_Main.synctex.gz   # 同步信息
```

---

## 🔧 常见问题排查

### 问题1: 缺少LaTeX包

**症状**:

```text
! LaTeX Error: File `xxx.sty' not found.
```

**解决方案**:

```bash
# TeX Live - 安装缺失的包
tlmgr install <package-name>

# MiKTeX - 自动安装（首次编译时）
# 或使用MiKTeX Console手动安装
```

### 问题2: Bibliography未显示

**症状**: References部分为空或显示"?"

**解决方案**:

1. 确保运行了完整的编译流程（pdflatex → bibtex → pdflatex → pdflatex）
2. 检查`references.bib`文件是否存在
3. 检查是否有BibTeX错误（查看`.blg`文件）

### 问题3: Cross-references未解析

**症状**: 显示"??"而非正确的编号

**解决方案**:

运行额外的pdflatex编译（通常第三次就足够）：

```bash
pdflatex ICSE2026_Paper_Main.tex
```

### 问题4: 数学公式错误

**症状**:

```text
! Missing $ inserted.
```

**解决方案**:

检查LaTeX日志文件定位错误位置：

```bash
# 查看错误详情
cat ICSE2026_Paper_Main.log | grep "Error"
```

### 问题5: 图表不显示

**症状**: 编译成功但图表缺失

**解决方案**:

1. 检查TikZ库是否加载：`\usetikzlibrary{...}`
2. 检查pgfplots版本：`\pgfplotsset{compat=1.18}`
3. 确保figures/tables目录中的文件存在

---

## 📈 编译性能优化

### 快速编译（草稿模式）

```bash
# 使用draft模式（跳过图片生成）
pdflatex -draftmode ICSE2026_Paper_Main.tex
```

### 只编译特定部分

```latex
% 在Main文件中添加：
\includeonly{sections/01_introduction}

% 然后正常编译
```

### 使用latexmk自动编译

```bash
# 安装latexmk（通常随TeX Live安装）
latexmk -pdf ICSE2026_Paper_Main.tex

# 持续监视并自动重新编译
latexmk -pdf -pvc ICSE2026_Paper_Main.tex
```

---

## ✅ 编译成功标准

编译完成后，验证以下内容：

### 基本检查

- [ ] PDF文件成功生成
- [ ] 页数在预期范围（目标：11-12页正文 + 2-3页references）
- [ ] 无major LaTeX errors（允许minor warnings）
- [ ] 所有sections显示正确
- [ ] 所有figures显示清晰
- [ ] 所有tables格式正确

### Citations检查

- [ ] 所有`\cite{}`命令正确显示
- [ ] References部分完整显示
- [ ] 无"[?]"或"??"显示
- [ ] Bibliography格式符合ACM标准

### Cross-references检查

- [ ] 所有`\ref{}`命令正确解析
- [ ] Section/Figure/Table编号正确
- [ ] Theorem/Definition编号正确
- [ ] 页码正确生成

### 格式检查

- [ ] 标题和作者信息正确
- [ ] Abstract显示完整
- [ ] CCS concepts和keywords正确
- [ ] 页眉页脚格式正确
- [ ] 双栏layout正确

### 内容检查

- [ ] 所有数学公式正确渲染
- [ ] 所有代码块正确显示
- [ ] 所有inference rules清晰
- [ ] 所有theorem environments正确
- [ ] TikZ图表正确生成

---

## 📊 预期输出

### 页数分布

| Section | 预期页数 |
|---------|---------|
| Abstract | 0.2页 |
| Section 1: Introduction | 1.5页 |
| Section 2: Background | 1.5页 |
| Section 3: Formal Semantics | 2.0页 |
| Section 4: Algebraic Framework | 1.5页 |
| Section 5: Triple Flow Analysis | 2.5页 |
| Section 6: Related Work | 1.0页 |
| Section 7: Conclusion | 0.8页 |
| **正文总计** | **~11页** |
| References | 2-3页 |
| **总计** | **13-14页** |

### 文件大小

- PDF大小：预期 2-5 MB（含TikZ图表）
- 编译时间：首次编译 30-60秒，后续编译 10-20秒

---

## 🐛 调试技巧

### 1. 查看详细错误

```bash
# 查看完整编译日志
less ICSE2026_Paper_Main.log

# 搜索错误
grep -i "error" ICSE2026_Paper_Main.log

# 搜索警告
grep -i "warning" ICSE2026_Paper_Main.log
```

### 2. 二分查找错误

如果编译失败但错误位置不明确：

```latex
% 注释掉一半sections
% \input{sections/03_formal_semantics}
% \input{sections/04_algebraic_framework}
% \input{sections/05_triple_flow_analysis}

% 重新编译，缩小范围
```

### 3. 使用交互模式

```bash
# 不使用nonstopmode，允许交互
pdflatex ICSE2026_Paper_Main.tex

# 按'h'查看帮助
# 按'x'退出
# 按'r'运行到下一个错误
```

---

## 🎯 下一步（编译成功后）

1. **格式调整**（预计2-3小时）
   - 调整figure/table尺寸
   - 优化page breaks
   - 修复overfull/underfull boxes
   - Balance columns

2. **内容审阅**（预计1-2天）
   - 检查语法和拼写
   - 验证技术准确性
   - 优化表达清晰度
   - 确保citations完整

3. **最终检查**（预计1天）
   - 运行ICSE格式检查
   - 验证页数限制
   - 确认匿名性（review版本）
   - 生成submission package

---

## 📚 有用资源

### LaTeX帮助

- [Overleaf Documentation](https://www.overleaf.com/learn)
- [LaTeX Wikibook](https://en.wikibooks.org/wiki/LaTeX)
- [TeX Stack Exchange](https://tex.stackexchange.com/)

### ACM模板

- [ACM Article Template](https://www.acm.org/publications/proceedings-template)
- [acmart Documentation](http://mirrors.ctan.org/macros/latex/contrib/acmart/acmart.pdf)

### TikZ/PGFPlots

- [TikZ Manual](https://ctan.org/pkg/pgf)
- [PGFPlots Manual](https://ctan.org/pkg/pgfplots)
- [TikZ Examples](http://www.texample.net/tikz/)

---

## 🎊 当前状态

✅ **LaTeX源文件100%就绪**

- 7个sections完整转换
- 4个figures (TikZ)
- 4个tables (LaTeX)
- Main file配置完成
- References.bib完整

⏳ **等待编译**

- 需要安装LaTeX发行版
- 首次编译预计30-60秒
- 完整流程预计2-3分钟

🎯 **编译后立即开始格式调整**

---

**文档版本**: 1.0  
**最后更新**: 2025年10月20日  
**维护者**: OTLP项目团队

**🚀 准备就绪，开始编译！**
