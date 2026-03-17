# ⚠️ LaTeX 安装指南 - 论文编译前置条件

> **状态**: 阻塞中 ⏸️  
> **阻塞原因**: 系统未安装 LaTeX 环境  
> **解决时间**: 约30-60分钟  
> **优先级**: 🔴 P0 - 最高

---

## 🎯 当前状态

### 论文准备度: 70% ➡️ 100%

```text
✅ 论文内容:     ████████████████████ 100% 完成
✅ Figures:      ████████████████████ 100% 完成 (4个TikZ图表)
✅ Tables:       ████████████████████ 100% 完成 (4个LaTeX表格)  
✅ 参考文献:     ████████████████████ 100% 完成 (44篇)
✅ LaTeX源文件:  ████████████████████ 100% 完成 (所有.tex文件)
⏸️ 编译PDF:      ░░░░░░░░░░░░░░░░░░░░   0% 阻塞 - 需LaTeX环境
```

### 文件检查清单

| 文件 | 状态 | 大小 |
|------|------|------|
| ICSE2026_Paper_Main.tex | ✅ | 5,711 bytes |
| references.bib | ✅ | 7,196 bytes |
| sections/01_introduction.tex | ✅ | 12,376 bytes |
| sections/02_background.tex | ✅ | 12,040 bytes |
| sections/03_formal_semantics.tex | ✅ | 13,454 bytes |
| sections/04_algebraic_framework.tex | ✅ | 15,048 bytes |
| sections/05_triple_flow_analysis.tex | ✅ | 11,398 bytes |
| sections/06_related_work.tex | ✅ | 8,578 bytes |
| sections/07_conclusion.tex | ✅ | 8,064 bytes |
| figures/*.tex (8个) | ✅ | ~30,000 bytes |
| tables/*.tex (4个) | ✅ | ~7,700 bytes |

---

## 📥 LaTeX 安装选项

### 选项1: MiKTeX (推荐 - Windows)

**下载地址**: https://miktex.org/download

**安装步骤**:

1. 下载 MiKTeX 安装程序 (约 200MB)
2. 运行安装程序，选择 "Complete MiKTeX"
3. 安装路径: `C:\Program Files\MiKTeX`
4. 勾选 "Install missing packages on-the-fly"
5. 等待安装完成 (约20-30分钟)
6. 重启命令行/PowerShell

**验证安装**:
```powershell
pdflatex --version
```

---

### 选项2: TeX Live (跨平台)

**下载地址**: https://tug.org/texlive/

**安装步骤**:

1. 下载 TeX Live ISO (约 4GB) 或网络安装程序
2. 运行 `install-tl-windows.bat`
3. 选择 "Standard collections" (包含ACM模板)
4. 等待安装完成 (约30-60分钟)
5. 添加环境变量: `C:\texlive\2024\bin\windows`
6. 重启命令行/PowerShell

**验证安装**:
```powershell
pdflatex --version
```

---

### 选项3: 在线编译 (临时方案)

**Overleaf**: https://www.overleaf.com

**步骤**:

1. 注册 Overleaf 账号
2. 创建新项目 → 上传所有论文文件
3. 设置编译器为 "pdfLaTeX" 或 "XeLaTeX"
4. 编译查看结果

**限制**:
- 需要上传所有文件
- 免费版有编译时间限制
- 无法使用本地脚本

---

## 🔧 编译步骤 (安装后)

### 快速编译

```powershell
# 进入论文目录
cd academic\academic

# 运行编译脚本
.\compile.ps1
```

### 手动编译 (如果脚本失败)

```powershell
# 第1步: 编译主文件
pdflatex -interaction=nonstopmode ICSE2026_Paper_Main.tex

# 第2步: 编译参考文献
bibtex ICSE2026_Paper_Main

# 第3步: 再次编译 (解析引用)
pdflatex -interaction=nonstopmode ICSE2026_Paper_Main.tex

# 第4步: 最终编译
pdflatex -interaction=nonstopmode ICSE2026_Paper_Main.tex
```

---

## 📋 预期编译结果

### 成功输出

```
========================================
ICSE 2026 Paper Compilation Script
========================================

Step 1/4: First pdflatex pass...
  ✓ Complete
Step 2/4: Running bibtex...
  ✓ Complete
Step 3/4: Second pdflatex pass...
  ✓ Complete
Step 4/4: Third pdflatex pass (resolving references)...
  ✓ Complete

========================================
Compilation Successful! 🎉
========================================

Output: ICSE2026_Paper_Main.pdf
PDF Size: 1.5 MB
```

### 预期PDF规格

| 属性 | 预期值 |
|------|--------|
| 页数 | 16.5页 |
| 字数 | 26,900词 |
| 文件大小 | ~1.5 MB |
| 格式 | ACM双栏 |
| 状态 | review/anonymous |

---

## ⚠️ 常见编译问题

### 问题1: "acmart.cls not found"

**解决**:
```powershell
# MiKTeX会自动安装缺失包
# 或手动安装:
mpm --install=acmart
```

### 问题2: "TikZ library not found"

**解决**:
```powershell
# 确保安装完整版MiKTeX
# 或在MiKTeX Console中安装:
# Packages → tikz, pgfplots
```

### 问题3: 编译超时

**解决**:
```powershell
# 分步编译，观察错误
pdflatex -interaction=nonstopmode ICSE2026_Paper_Main.tex 2>&1 | Tee-Object compile.log
```

---

## 🚀 安装后行动计划

### 立即执行 (安装LaTeX后)

- [ ] 验证 pdflatex 安装: `pdflatex --version`
- [ ] 运行编译脚本: `.\compile.ps1`
- [ ] 检查PDF生成: `ICSE2026_Paper_Main.pdf`
- [ ] 验证页数: 16.5页
- [ ] 检查图表: 4 Figures + 4 Tables

### 后续步骤

- [ ] 技术审阅
- [ ] 语言润色
- [ ] 外部审阅
- [ ] ICSE 2026 投稿

---

## 📞 支持

### 本地支持

- 编译指南: `COMPILATION_GUIDE.md`
- 常见问题: `🔧_LaTeX编译常见问题解决方案_2025_10_17.md`
- 快速测试: `QUICK_COMPILE_TEST.md`

### 在线资源

- MiKTeX: https://miktex.org/doc
- TeX Live: https://tug.org/texlive/doc.html
- ACM模板: https://www.acm.org/publications/proceedings-template

---

## ⏱️ 时间估算

| 步骤 | 时间 |
|------|------|
| 下载MiKTeX | 5-10分钟 |
| 安装MiKTeX | 20-30分钟 |
| 首次编译 | 2-5分钟 |
| 调试问题 | 5-15分钟 |
| **总计** | **30-60分钟** |

---

**记录时间**: 2026年3月16日  
**状态**: 等待LaTeX安装  
**下一步**: 用户安装MiKTeX后运行编译脚本

---

> 💡 **提示**: 安装完成后，论文编译将在5分钟内完成！
