# 📸 Camera-Ready准备指南

> **使用时机**: 论文被ICSE 2026录取后  
> **目标**: 准备最终出版版本  
> **预计时间**: 3-5天

---

## 🎉 恭喜录取

**您的论文已被ICSE 2026录取！** 🎊

现在需要准备Camera-Ready版本（最终出版版本）。本指南将帮助您完成这一关键步骤。

---

## 📋 Camera-Ready概览

### 什么是Camera-Ready？

**Camera-Ready（CR）**是论文的最终出版版本，将直接用于会议论文集和ACM Digital Library。

**与投稿版本的区别**:

| 项目 | 投稿版本 | Camera-Ready版本 |
|------|---------|------------------|
| **作者信息** | ❌ 隐藏（匿名） | ✅ 显示（完整） |
| **致谢** | ❌ 无 | ✅ 有 |
| **版权信息** | ❌ 无 | ✅ 必须 |
| **页数** | 11页 | 11页（通常不变） |
| **内容** | 投稿时 | 根据审稿意见修改后 |
| **格式** | ACM sigconf | ACM sigconf（更严格） |
| **截止日期** | 投稿截止 | 录取后2-4周 |

---

## 🎯 Camera-Ready准备流程

### 阶段1: 响应审稿意见（1-2天）

#### 1.1 整理审稿意见

**收到的材料**:

- 录取通知邮件
- 审稿意见（3-4位审稿人）
- Meta-Review（PC意见）
- 修改要求清单

**操作**:

1. **创建修改清单**:

   ```text
   reviewer_comments.md
   
   # Reviewer A
   ## Major Comments
   1. [Issue] Clarify Theorem 3 proof
      [Action] Add intuitive explanation (Section 3.2)
      [Status] ✅ Done
   
   2. [Issue] Add comparison with Zipkin
      [Action] Expand Related Work (Section 6.1)
      [Status] ⏳ In Progress
   
   ## Minor Comments
   1. [Issue] Typo in Figure 2 caption
      [Action] Fix typo
      [Status] ✅ Done
   
   # Reviewer B
   ...
   ```

2. **优先级排序**:
   - 🔴 **Must-Fix**: PC要求的修改
   - 🟠 **Should-Fix**: 审稿人明确指出的问题
   - 🟡 **Nice-to-Fix**: 建议性修改

#### 1.2 修改论文内容

**原则**:

- ✅ 认真对待所有意见
- ✅ 即使不完全同意，也要回应
- ❌ 不要大幅改变论文结构
- ❌ 不要删除审稿人认可的内容

**常见修改**:

1. **澄清技术细节**:
   - 添加更多解释
   - 补充例子
   - 改进公式表述

2. **扩展实验**:
   - 添加对比实验
   - 补充统计分析
   - 更新图表

3. **改进写作**:
   - 修正语法错误
   - 优化句子结构
   - 统一术语使用

4. **更新相关工作**:
   - 引用审稿人提到的工作
   - 更详细的对比
   - 公正的评价

---

### 阶段2: 恢复作者信息（30分钟）

#### 2.1 添加作者信息

**之前（投稿版本）**:

```latex
% 投稿时注释掉了作者信息
% \author{John Doe}
% \affiliation{University of Example}
```

**现在（Camera-Ready）**:

```latex
\author{John Doe}
\affiliation{%
  \institution{University of Example}
  \city{City}
  \country{Country}
}
\email{john.doe@example.edu}

\author{Jane Smith}
\affiliation{%
  \institution{Another University}
  \city{Another City}
  \country{Another Country}
}
\email{jane.smith@another.edu}
```

**注意**:

- 作者顺序通常与投稿时一致（除非有特殊情况）
- 所有作者的affiliation和email必须准确
- 通讯作者（Corresponding Author）需标注

#### 2.2 添加致谢（Acknowledgments）

```latex
\section{Acknowledgments}

We thank the anonymous reviewers for their insightful comments 
that helped improve this paper. This work was supported in part 
by [Funding Agency] under Grant No. [Grant Number]. We are 
grateful to [Colleagues/Collaborators] for valuable discussions.
```

**应该致谢**:

- ✅ 审稿人（匿名）
- ✅ 资助机构（Funding agencies）
- ✅ 合作者（如果未列为作者）
- ✅ 提供数据/工具的人员
- ✅ 导师/顾问（如适用）

**不应致谢**:

- ❌ 过度感谢（夸张的言辞）
- ❌ 与研究无关的人员
- ❌ 商业产品（除非确实使用）

---

### 阶段3: 添加版权信息（15分钟）

#### 3.1 ACM版权声明

ICSE会提供具体的版权代码，通常是以下之一：

**情况1: ACM拥有版权**（最常见）:

```latex
\copyrightyear{2026}
\acmYear{2026}
\setcopyright{acmcopyright}
\acmConference[ICSE '26]{48th International Conference on Software Engineering}{May 2026}{Montreal, Canada}
\acmBooktitle{Proceedings of the 48th International Conference on Software Engineering (ICSE '26), May 2026, Montreal, Canada}
\acmPrice{15.00}
\acmDOI{10.1145/XXXXXXX.YYYYYYY}
\acmISBN{978-X-XXXX-XXXX-X/YY/MM}
```

**情况2: 作者保留版权**:

```latex
\setcopyright{rightsretained}
```

**情况3: 政府工作**:

```latex
\setcopyright{usgov}
```

**注意**:

- DOI和ISBN由会议组织者提供
- 不要自己编造这些信息
- 准确复制提供的代码

#### 3.2 CCS概念（Computing Classification System）

添加ACM CCS分类：

```latex
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
<concept_desc>Software and its engineering~Software verification and validation</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011066</concept_id>
<concept_desc>Software and its engineering~Formal methods</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Software verification and validation}
\ccsdesc[500]{Software and its engineering~Formal methods}
```

**如何选择CCS概念**:

1. 访问 <https://dl.acm.org/ccs>
2. 搜索相关主题
3. 选择3-5个最相关的概念
4. 复制XML代码

---

### 阶段4: 格式检查与优化（1-2天）

#### 4.1 页数检查

**目标**: 确保符合页数限制（通常仍是11页）

**如果超过限制**:

1. **微调空白**:

   ```latex
   % 减少Section间距
   \vspace{-0.1in}
   
   % 减少图表间距
   \vspace{-0.05in}
   ```

2. **优化表格**:

   ```latex
   % 使用更小的字体
   \begin{table}
   \footnotesize
   ...
   \end{table}
   
   % 调整列宽
   \begin{tabular}{p{2cm}p{2.5cm}p{3cm}}
   ```

3. **精简文本**:
   - 删除冗余句子
   - 合并相似段落
   - 使用更简洁的表达

**如果少于限制**:

- 通常不需要填充
- 如果明显太短，可以扩展discussion

#### 4.2 图表质量检查

**检查清单**:

- [ ] 所有图表清晰可读（300 DPI以上）
- [ ] 字体大小≥8pt
- [ ] 颜色打印效果（不依赖颜色区分）
- [ ] 所有轴有标签
- [ ] 所有图例清晰
- [ ] Caption描述完整

**优化建议**:

```latex
% TikZ图表优化
\begin{tikzpicture}[
  scale=1.2,  % 适当缩放
  font=\small,  % 统一字体
  every node/.style={font=\small}
]
...
\end{tikzpicture}

% 图片优化
\includegraphics[width=0.9\textwidth,height=0.4\textheight,keepaspectratio]{figure.pdf}
```

#### 4.3 参考文献格式

**检查**:

- [ ] 所有条目格式一致
- [ ] 所有URL可访问
- [ ] 所有DOI正确
- [ ] 作者名字完整
- [ ] 年份、页码准确

**更新references.bib**:

```bibtex
@inproceedings{smith2020,
  author = {Smith, John and Doe, Jane},
  title = {A Great Paper},
  booktitle = {Proceedings of ICSE},
  year = {2020},
  pages = {123--135},
  doi = {10.1145/1234567.7654321},
  url = {https://doi.org/10.1145/1234567.7654321}
}
```

#### 4.4 超链接检查

```latex
% 确保hyperref配置正确
\usepackage[
  colorlinks=true,
  linkcolor=black,
  citecolor=black,
  urlcolor=blue
]{hyperref}
```

**检查**:

- [ ] 所有内部链接工作（\ref, \cite）
- [ ] 所有URL链接可点击
- [ ] 书签（PDF目录）正确

---

### 阶段5: 创建修改说明（1天）

#### 5.1 Response Letter

会议通常要求提供修改说明文档，详细说明如何响应审稿意见。

**模板**:

```text
Response to Reviewers
ICSE 2026 - Paper #123
Title: Formal Verification Framework for OTLP

We thank all reviewers for their insightful comments. We have 
carefully addressed all concerns in the camera-ready version. 
Below, we detail our responses and the corresponding changes.

==========================================================
Reviewer A
==========================================================

Comment A.1: "The proof of Theorem 3 lacks intuition."

Response: We agree and have added an intuitive explanation 
before the formal proof (Section 3.2, page 5, lines 15-25). 
We now provide a concrete example to illustrate the key idea.

Changes: 
- Added paragraph "Intuitively, Theorem 3 states that..." 
  (Section 3.2, page 5)
- Added Example 2 with a concrete trace (Section 3.2, page 5)

---

Comment A.2: "The comparison with Zipkin is too brief."

Response: We have expanded the comparison in the Related Work 
section (Section 6.1, page 9, lines 30-45), adding a dedicated 
paragraph discussing Zipkin's approach to trace verification 
and how our method differs.

Changes:
- Expanded Section 6.1 with detailed Zipkin comparison (page 9)
- Added reference [18] for Zipkin's latest paper (2024)
- Updated Table 6 to include Zipkin's features (page 10)

---

==========================================================
Reviewer B
==========================================================

Comment B.1: "Figure 2 has a typo in the caption."

Response: Thank you for catching this. We have corrected 
"architecutre" to "architecture" in Figure 2's caption.

Changes:
- Fixed typo in Figure 2 caption (page 6)

---

... (continue for all comments)

==========================================================
Summary of Major Changes
==========================================================

1. Enhanced Section 3.2 with intuitive explanations and examples
2. Expanded Related Work (Section 6.1) with detailed comparisons
3. Updated Table 6 to include additional baseline systems
4. Fixed all typos and grammatical errors identified by reviewers
5. Added 3 new references suggested by reviewers

Total pages: 11 (unchanged from submission)
New content: ~0.5 pages
Removed content: ~0.5 pages (redundant text)
```

#### 5.2 Track Changes（可选）

某些会议要求提供"track changes"版本：

```latex
% 使用changes包
\usepackage[final]{changes}

% 标记修改
\added{This is new text added in response to reviewers.}
\deleted{This old text was removed.}
\replaced{new text}{old text}
```

**生成两个版本**:

1. `paper_main_changes.pdf` - 带修改标记
2. `paper_main_final.pdf` - 最终版本（无标记）

---

### 阶段6: 最终检查与提交（1天）

#### 6.1 最终检查清单

**内容检查**:

- [ ] 所有审稿意见已响应
- [ ] 作者信息完整准确
- [ ] 致谢部分完整
- [ ] 版权信息正确
- [ ] 页数符合要求
- [ ] 无拼写/语法错误

**格式检查**:

- [ ] 符合ACM格式要求
- [ ] 所有图表清晰
- [ ] 所有引用正确
- [ ] 超链接工作正常
- [ ] PDF/A格式（如要求）

**文件检查**:

- [ ] `paper_main_final.pdf` - 最终PDF
- [ ] `paper_main_source.zip` - LaTeX源码
- [ ] `response_to_reviewers.pdf` - 修改说明
- [ ] `paper_main_changes.pdf` - Track changes版本（如需要）

#### 6.2 生成PDF/A格式（如要求）

某些出版商要求PDF/A格式（长期存档格式）：

```latex
% 添加到preamble
\usepackage[a-1b]{pdfx}

% 创建pdfx.xmpdata文件
\begin{filecontents*}{\jobname.xmpdata}
\Title{Your Paper Title}
\Author{John Doe\sep Jane Smith}
\Language{en-US}
\Subject{Software Engineering}
\Keywords{OTLP\sep Formal Verification\sep Distributed Tracing}
\end{filecontents*}
```

**验证PDF/A**:

- 使用Adobe Acrobat Pro
- 或在线工具：<https://www.pdf-online.com/osa/validate.aspx>

#### 6.3 上传到会议系统

**步骤**:

1. **登录投稿系统**:
   - 使用投稿时的账号
   - 找到您的录取论文

2. **上传文件**:
   - Main PDF: `paper_main_final.pdf`
   - Source Files: `paper_main_source.zip`
   - Response Letter: `response_to_reviewers.pdf`

3. **填写额外信息**:
   - Copyright form（版权表）
   - Author information（作者信息）
   - Presentation preferences（演讲偏好）

4. **确认提交**:
   - 检查所有文件
   - 确认无误后提交
   - 保存确认邮件

---

## 📄 版权转让

### ACM版权表

ICSE通常使用ACM出版，需要签署版权表：

**流程**:

1. **收到版权表链接**（邮件）
2. **在线填写**:
   - 论文ID
   - 作者信息
   - 版权选项
3. **电子签名**
4. **下载确认书**

**版权选项**:

| 选项 | 说明 | 推荐 |
|------|------|------|
| **Copyright Transfer** | ACM拥有全部版权 | ✅ 默认 |
| **Exclusive License** | 作者保留某些权利 | 🟢 可选 |
| **Author-Pays** | 开放获取（需付费） | 💰 可选 |

**重要**:

- 所有作者必须同意版权选项
- 签署前仔细阅读条款
- 保存确认书副本

---

## 🎤 准备演讲（可选，会前准备）

虽然不是Camera-Ready的一部分，但录取后应开始准备会议演讲。

**详细演讲准备**请参考: [会议演讲准备指南](./🎤_会议演讲准备指南_2025_10_17.md)

**简要提示**:

- ✅ 20分钟演讲（通常）
- ✅ 15-20张幻灯片
- ✅ 重点突出：问题、方法、结果
- ✅ 练习多次（至少5次）
- ✅ 准备Q&A

---

## ⏰ 时间线

### 典型Camera-Ready时间线

| 时间点 | 任务 | 预计时间 |
|--------|------|----------|
| **Day 0** | 收到录取通知 | - |
| **Day 1-2** | 响应审稿意见，修改内容 | 1-2天 |
| **Day 3** | 恢复作者信息，添加致谢 | 30分钟 |
| **Day 3** | 添加版权信息 | 15分钟 |
| **Day 4-5** | 格式检查与优化 | 1-2天 |
| **Day 6** | 创建修改说明 | 1天 |
| **Day 7** | 最终检查与提交 | 1天 |
| **Deadline** | 提交截止（通常Day 14-28） | - |

**建议**:

- ✅ 提前1周完成
- ✅ 留出缓冲时间
- ❌ 不要拖到最后一天

---

## 🚨 常见错误与避免

### 错误1: 忘记更新CCS概念

**后果**: 论文分类不准确，影响检索

**避免**: 按照本指南添加CCS XML

### 错误2: 版权信息错误

**后果**: 论文可能被拒绝出版

**避免**: 准确复制会议提供的版权代码

### 错误3: 超过页数限制

**后果**: 被要求重新提交

**避免**: 提前检查页数，提前优化

### 错误4: 遗漏审稿意见

**后果**: PC可能拒绝Camera-Ready

**避免**: 创建清单，逐一响应所有意见

### 错误5: 提交错误版本

**后果**: 出版版本有错误

**避免**: 最终检查，确认文件正确

---

## 📞 需要帮助？

### 联系途径

1. **Program Chairs**:
   - 任何Camera-Ready相关问题
   - 技术问题
   - 延期请求

2. **Publication Chair**:
   - 格式问题
   - 版权问题
   - 提交问题

3. **ACM Support**:
   - 版权表问题
   - PDF格式问题

### 紧急情况

**如果无法按时提交**:

1. 立即联系Program Chairs
2. 说明原因
3. 请求延期（通常可获得3-7天）
4. 提供预计完成时间

---

## 🎊 总结

Camera-Ready准备是论文出版的关键步骤：

1. ✅ **响应审稿意见**（1-2天）
2. ✅ **恢复作者信息**（30分钟）
3. ✅ **添加版权信息**（15分钟）
4. ✅ **格式检查优化**（1-2天）
5. ✅ **创建修改说明**（1天）
6. ✅ **最终检查提交**（1天）

**总时间**: 3-5天  
**建议提前**: 1周

**完成Camera-Ready后**:

- ✅ 论文将正式出版
- ✅ 收到ACM DOI
- ✅ 出现在ACM Digital Library
- ✅ 可以公开讨论和分享
- ✅ 开始准备会议演讲

**下一步**: [会议演讲准备指南](./🎤_会议演讲准备指南_2025_10_17.md) 🎤

---

**创建时间**: 2025年10月17日  
**使用时机**: ICSE 2026录取后  
**预计完成时间**: 3-5天

---

**📸 准备完美的Camera-Ready版本！Publication-ready! 📚**-
