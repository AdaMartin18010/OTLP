# 🔧 LaTeX环境配置完整指南

> **状态**: LaTeX环境未安装  
> **发现日期**: 2025年10月17日  
> **紧急程度**: 🔴 高（编译论文必需）

---

## 🚨 当前状态

### 检测结果

```bash
> pdflatex --version
错误: 'pdflatex' 不是内部或外部命令
```

**结论**: 系统中未安装LaTeX发行版

---

## 💡 解决方案（三选一）

### ⭐ 方案A：Overleaf在线编译（推荐，最快）

**优点**:

- ✅ 无需本地安装
- ✅ 立即可用（5分钟内）
- ✅ 协作友好
- ✅ 自动保存
- ✅ 内置PDF预览
- ✅ Git集成

**步骤**:

1. **注册账号** (2分钟)
   - 访问: <https://www.overleaf.com>
   - 注册免费账号

2. **创建新项目** (1分钟)
   - 点击 "New Project" → "Blank Project"
   - 命名: "OTLP_ICSE2026"

3. **上传文件** (2分钟)
   - 点击左上角 "Upload" 图标
   - 上传所有文件:

     ```text
     paper_main.tex
     references.bib
     sections/01_introduction.tex
     sections/02_background.tex
     sections/03_framework.tex
     sections/04_implementation.tex
     sections/05_evaluation.tex
     sections/06_related_work.tex
     sections/07_conclusion.tex
     ```

4. **编译论文** (立即)
   - 点击 "Recompile" 按钮
   - 右侧自动显示PDF

5. **下载PDF** (1分钟)
   - 点击 "Download PDF" 按钮

**总时间**: ⏱️ 5-10分钟

**推荐理由**: 无需安装任何软件，立即可以编译查看结果！

---

### 方案B：MiKTeX安装（Windows推荐）

**优点**:

- ✅ Windows原生支持
- ✅ 自动下载缺失包
- ✅ 轻量级
- ✅ IDE集成良好

**缺点**:

- ❌ 下载安装需要时间（~30分钟）
- ❌ 首次编译较慢（下载包）

**步骤**:

1. **下载MiKTeX** (5分钟)
   - 访问: <https://miktex.org/download>
   - 下载Windows安装包（~300MB）

2. **安装MiKTeX** (10分钟)
   - 运行安装程序
   - 选择 "Install MiKTeX for all users"（推荐）
   - 安装路径: 默认即可
   - 勾选 "Automatic package installation: Yes"

3. **验证安装** (1分钟)

   ```bash
   pdflatex --version
   bibtex --version
   ```

4. **首次编译** (10-15分钟，会自动下载所需包)

   ```bash
   cd E:\_src\OTLP\academic
   pdflatex paper_main.tex
   bibtex paper_main
   pdflatex paper_main.tex
   pdflatex paper_main.tex
   ```

**总时间**: ⏱️ 30-45分钟

---

### 方案C：TeX Live安装（完整版）

**优点**:

- ✅ 最完整的LaTeX发行版
- ✅ 包含所有常用包
- ✅ 跨平台
- ✅ 学术界标准

**缺点**:

- ❌ 文件巨大（~5GB）
- ❌ 下载安装耗时（1-2小时）

**步骤**:

1. **下载TeX Live** (30-60分钟)
   - 访问: <https://www.tug.org/texlive/>
   - 下载安装器或ISO镜像

2. **安装TeX Live** (30-60分钟)
   - 运行安装程序
   - 选择完整安装（Full Scheme）

3. **验证安装** (1分钟)

   ```bash
   pdflatex --version
   bibtex --version
   ```

**总时间**: ⏱️ 1-2小时

**适用场景**: 长期学术写作需求

---

## 🎯 推荐选择策略

### 立即查看论文PDF？

→ **选择方案A: Overleaf** ⭐⭐⭐⭐⭐

**理由**:

- ✅ 5分钟内看到编译结果
- ✅ 立即评估页数和布局
- ✅ 快速定位需要调整的地方
- ✅ 无需等待软件安装

### 长期本地开发？

→ **选择方案B: MiKTeX** ⭐⭐⭐⭐

**理由**:

- ✅ 30分钟安装，永久使用
- ✅ 离线编译
- ✅ 更快的编译速度（首次后）
- ✅ 更好的IDE集成

### 学术写作专业用户？

→ **选择方案C: TeX Live** ⭐⭐⭐⭐⭐

**理由**:

- ✅ 最完整的功能
- ✅ 所有包都齐全
- ✅ 学术界标准

---

## 📋 方案A详细操作流程（Overleaf推荐）

### Step 1: 准备文件（1分钟）

确认以下文件已存在:

```bash
E:\_src\OTLP\academic\
├── paper_main.tex
├── references.bib
└── sections\
    ├── 01_introduction.tex
    ├── 02_background.tex
    ├── 03_framework.tex
    ├── 04_implementation.tex
    ├── 05_evaluation.tex
    ├── 06_related_work.tex
    └── 07_conclusion.tex
```

### Step 2: 注册Overleaf（2分钟）

1. 打开浏览器，访问: <https://www.overleaf.com>
2. 点击右上角 "Register"
3. 填写邮箱和密码
4. 验证邮箱（检查收件箱）

### Step 3: 创建项目（1分钟）

1. 登录后，点击 "New Project"
2. 选择 "Blank Project"
3. 项目名称: `OTLP_ICSE2026_Paper`
4. 点击 "Create"

### Step 4: 上传文件（3分钟）

**方法1: 拖拽上传**-

1. 在左侧文件树面板
2. 拖拽 `paper_main.tex` → 上传
3. 拖拽 `references.bib` → 上传
4. 点击文件树的 "New Folder" → 创建 `sections` 文件夹
5. 进入 `sections` 文件夹
6. 拖拽所有 `.tex` 文件 → 上传

**方法2: 手动上传**-

1. 点击左上角 "Upload" 图标
2. 选择文件 → 上传

### Step 5: 设置主文档（1分钟）

1. 点击左上角 "Menu"
2. 找到 "Main document"
3. 设置为 `paper_main.tex`
4. 点击 "Save"

### Step 6: 首次编译（1分钟）

1. 点击顶部绿色 "Recompile" 按钮
2. 等待编译完成（10-30秒）
3. 右侧自动显示PDF预览

**可能的问题**:

- **问题1**: "LaTeX Error: File `acmart.cls' not found"
  - **解决**: 在 `paper_main.tex` 开头添加:

    ```latex
    % Use Overleaf's ACM template
    \documentclass[sigconf,anonymous,review]{acmart}
    ```

- **问题2**: "Undefined control sequence"
  - **解决**: 检查LaTeX包是否正确导入

### Step 7: 检查结果（5分钟）

**页数统计**:

- 目标: 11页
- 实际: ___页（在PDF右下角查看）

**章节检查**:

- [ ] Abstract
- [ ] Introduction
- [ ] Background
- [ ] Formal Verification Framework
- [ ] Implementation
- [ ] Evaluation
- [ ] Related Work
- [ ] Conclusion
- [ ] References

**格式检查**:

- [ ] 所有引用正确（无 `[?]`）
- [ ] 所有表格正确（无 `??`）
- [ ] 所有图表正确
- [ ] 数学公式正确渲染
- [ ] 代码块格式正确

### Step 8: 下载PDF（1分钟）

1. 点击右上角 "Download PDF" 图标
2. 保存到本地: `E:\_src\OTLP\academic\paper_main_v1.pdf`

**总时间**: ⏱️ 约15分钟

---

## 🔄 后续工作流程

### 在Overleaf中编辑

**优点**:

- ✅ 实时预览
- ✅ 自动保存
- ✅ 错误提示
- ✅ 协作编辑

**步骤**:

1. 在左侧文件树点击文件
2. 在中间编辑器中修改
3. 点击 "Recompile" 查看结果
4. 重复上述步骤直到满意

### Git同步（可选）

**如果需要版本控制**:

1. 在Overleaf项目中，点击 "Menu"
2. 找到 "Git" 部分
3. 复制 Git URL
4. 在本地执行:

   ```bash
   git clone <Overleaf-Git-URL>
   ```

---

## 📊 编译检查清单

### 首次编译后必查项目

- [ ] **页数符合要求** (目标: 11页，范围: 10-12页)
- [ ] **Abstract完整** (≤200字)
- [ ] **章节编号正确** (1-7)
- [ ] **表格编号正确** (Table 1-6)
- [ ] **图表编号正确** (Figure 1-8)
- [ ] **引用编号正确** ([1]-[44]，无`[?]`)
- [ ] **数学公式正确** (无编译错误)
- [ ] **代码块正常** (无溢出)
- [ ] **参考文献格式** (ACM标准)

### 质量检查项目

- [ ] **无编译警告** (Warnings = 0)
- [ ] **无编译错误** (Errors = 0)
- [ ] **无Overfull/Underfull hbox**
- [ ] **所有交叉引用正确**
- [ ] **所有标签唯一**

---

## 🎯 下一步行动计划

### 方案A用户（Overleaf）

1. **立即**: 注册Overleaf + 上传文件（10分钟）
2. **今晚**: 首次编译 + 检查页数（15分钟）
3. **明天**: 嵌入表格和图表（2小时）
4. **本周**: 内部审阅 + 润色（2天）

### 方案B用户（MiKTeX）

1. **今晚**: 下载+安装MiKTeX（30分钟）
2. **今晚晚些时候**: 首次编译（15分钟）
3. **明天**: 嵌入表格和图表（2小时）
4. **本周**: 内部审阅 + 润色（2天）

### 方案C用户（TeX Live）

1. **今晚**: 开始下载TeX Live（后台运行）
2. **明天**: 安装+首次编译（1小时）
3. **明天下午**: 嵌入表格和图表（2小时）
4. **本周**: 内部审阅 + 润色（2天）

---

## 💬 建议

### 🌟 最佳实践：混合使用

1. **立即**: 使用Overleaf快速验证编译结果（今晚15分钟）
2. **并行**: 安装MiKTeX用于长期开发（明天完成）
3. **未来**: 所有修改在本地完成，定期同步到Overleaf

**好处**:

- ✅ 立即看到结果（Overleaf）
- ✅ 长期高效开发（本地）
- ✅ 协作和展示（Overleaf）
- ✅ 版本控制（Git）

---

## 📞 总结

### 推荐方案：方案A（Overleaf） ⭐⭐⭐⭐⭐

**理由**:

1. 立即可用（5-15分钟）
2. 零配置
3. 可以快速评估论文状态
4. 不影响后续安装本地LaTeX

### 行动步骤

1. **现在（5分钟）**: 注册Overleaf账号
2. **今晚（10分钟）**: 上传文件 + 首次编译
3. **今晚（5分钟）**: 检查页数和基本格式
4. **明天**: 根据结果决定后续步骤

---

**🎯 目标**: 今晚看到论文首个PDF版本！

**📊 准备状态**: LaTeX文件100%就绪，仅差编译环境

**🚀 下一里程碑**: 首个PDF生成（预计今晚完成）
