# ICSE 2026 演讲资料

> **状态**: 准备就绪（等待论文录用）  
> **格式**: Beamer PDF (LaTeX)  
> **时长**: 20分钟演讲 + 5-10分钟Q&A

---

## 📊 文件说明

### 主文件

- `presentation_main.tex` - 主演讲文件（包含所有幻灯片）
- `compile_presentation.bat` - Windows编译脚本
- `compile_presentation.sh` - Linux/Mac编译脚本

### 幻灯片结构

```text
总计: 24张幻灯片（含3张备用）

1. Title Slide                      [30秒]
2. Roadmap                          [30秒]

Section 1: Motivation               [3分钟]
3. Why Verify OTLP?
4. Real-World Impact

Section 2: Problem & Contributions  [2分钟]
5. Problem Statement
6. Our Contributions

Section 3: Technical Approach       [8分钟]
7. Framework Architecture
8. Component 1: Type System
9. Component 2: Algebraic Structures
10. Component 3: Triple Flow Analysis
11. Component 4: Temporal Logic

Section 4: Implementation           [2分钟]
12. Implementation Stack

Section 5: Evaluation               [6分钟]
13. Evaluation Setup
14. RQ1: Violation Detection
15. RQ2: Performance Overhead
16. RQ3: Scalability

Section 6: Discussion               [2分钟]
17. Key Insights
18. Limitations

Section 7: Conclusion               [1分钟]
19. Summary
20. Thank You!

Backup Slides (for Q&A):
21. Type System Details
22. Proof Complexity
23. Case Study - E-commerce
```

---

## 🚀 快速开始

### 编译演讲PDF

**Windows**:

```bash
compile_presentation.bat
```

**Linux/Mac**:

```bash
chmod +x compile_presentation.sh
./compile_presentation.sh
```

**手动编译**:

```bash
pdflatex presentation_main.tex
pdflatex presentation_main.tex
pdflatex presentation_main.tex
```

---

## 🎨 定制指南

### 修改主题

默认主题: Madrid + Seahorse

更改主题（在`presentation_main.tex`中）:

```latex
\usetheme{Madrid}        % 其他: Berlin, Copenhagen, Warsaw
\usecolortheme{seahorse} % 其他: dolphin, beaver, crane
```

### 调整宽高比

默认: 16:9 (现代投影仪)

更改为4:3:

```latex
\documentclass[aspectratio=43,xcolor=dvipsnames]{beamer}
```

### 添加Logo

在`presentation_main.tex`的preamble部分添加:

```latex
\logo{\includegraphics[height=1cm]{your_logo.png}}
```

---

## 📝 演讲准备清单

### 论文录用后

- [ ] 更新作者信息（移除anonymous）
- [ ] 添加作者照片（可选）
- [ ] 更新机构信息
- [ ] 确认会议日期和地点
- [ ] 添加机构Logo

### 演讲练习

- [ ] 全程演练（目标20分钟）
- [ ] 录制视频自我审阅
- [ ] 准备Q&A回答（至少10个问题）
- [ ] 熟悉备用幻灯片内容
- [ ] 准备演示Demo（如果需要）

### 技术检查

- [ ] 测试PDF在不同设备上的显示
- [ ] 准备备份（USB + 云端）
- [ ] 测试会场投影仪
- [ ] 准备演讲者笔记
- [ ] 检查字体是否嵌入PDF

---

## 🎤 演讲技巧

### 时间分配

| Section | 时间 | 重点 |
|---------|------|------|
| Motivation | 3分钟 | 吸引兴趣 |
| Problem & Contributions | 2分钟 | 明确贡献 |
| Technical Approach | 8分钟 | 核心内容（最重要） |
| Implementation | 2分钟 | 证明可行性 |
| Evaluation | 6分钟 | 展示结果 |
| Discussion | 2分钟 | 洞察与局限 |
| Conclusion | 1分钟 | 强化记忆点 |

### 演讲要点

1. **开场（前30秒）**:
   - 自我介绍简短
   - 立即切入主题
   - 抛出引人注意的数据

2. **技术部分（中间8分钟）**:
   - 使用图表而非大段文字
   - 强调关键定理和证明思路
   - 适当使用动画（不要过度）

3. **结果部分（6分钟）**:
   - 清晰的数据可视化
   - 强调实际影响
   - 与baseline对比

4. **结尾（最后1分钟）**:
   - 重申核心贡献
   - 留下深刻印象
   - 邀请提问

### 常见问题准备

准备以下类型问题的回答:

1. **技术深度**:
   - "为什么选择Rust而不是其他语言？"
   - "Type系统的soundness如何证明？"
   - "如何处理分布式环境的时钟偏移？"

2. **比较**:
   - "与现有的X工具有什么区别？"
   - "为什么不使用Y方法？"

3. **实用性**:
   - "学习成本有多高？"
   - "如何集成到现有系统？"
   - "是否开源？"

4. **局限性**:
   - "哪些场景不适用？"
   - "未来计划？"

---

## 📸 演讲录制（可选）

如果会议要求预录制视频:

### 录制工具

- **OBS Studio** (免费, 推荐)
- **Zoom** (简单易用)
- **PowerPoint自带录制**

### 录制设置

- 分辨率: 1920x1080 (Full HD)
- 帧率: 30fps
- 格式: MP4 (H.264)
- 音频: 清晰，无回声
- 时长: 严格控制在20分钟内

### 后期处理

- 剪辑掉口误和停顿
- 添加字幕（强烈推荐）
- 标准化音量
- 添加会议Logo（如要求）

---

## 🔧 常见问题

### Q: 编译后某些符号不显示？

**A**: 检查字体包是否安装:

```bash
# TeX Live
tlmgr install amsfonts
tlmgr install cm-super

# MiKTeX
mpm --install=amsfonts
```

### Q: 图表太小/太大？

**A**: 调整TikZ图形大小:

```latex
\begin{tikzpicture}[scale=0.9]  % 调整scale值
```

### Q: 如何添加动画效果？

**A**: 使用Beamer的overlay:

```latex
\begin{itemize}
  \item<1-> 第一点（第1帧出现）
  \item<2-> 第二点（第2帧出现）
  \item<3-> 第三点（第3帧出现）
\end{itemize}
```

### Q: 如何导出为PowerPoint？

**A**: 两种方法:

1. 使用pdf2pptx工具转换
2. 在PowerPoint中插入PDF页面

**推荐**: 保持PDF格式，更专业且无兼容性问题

---

## 📦 打包清单（会议前）

准备以下文件:

```text
presentation/
├─ presentation_main.pdf        (最终演讲PDF)
├─ presenter_notes.pdf          (演讲者笔记)
├─ backup_presentation.pdf      (备份)
└─ demo/                        (如有演示)
   ├─ demo_video.mp4
   └─ demo_screenshots/
```

---

## 🌟 最佳实践

1. **视觉设计**:
   - 每页不超过7行文字
   - 使用高对比度颜色
   - 避免花哨的字体
   - 图表优于表格，表格优于文字

2. **内容组织**:
   - 每张幻灯片一个核心观点
   - 使用编号列表引导
   - 适当留白
   - 统一的视觉风格

3. **技术细节**:
   - 不要在幻灯片上放完整代码
   - 使用伪代码或关键片段
   - 数学公式简洁清晰
   - 图表加标题和标签

4. **互动**:
   - 眼神交流（不要一直看屏幕）
   - 使用激光笔指示
   - 适当停顿等待理解
   - 鼓励中途提问（如果时间允许）

---

## 📚 参考资源

### 演讲技巧

- "How to Give a Great Research Talk" (Simon Peyton Jones)
- "The Craft of Scientific Presentations" (Michael Alley)

### Beamer教程

- Beamer User Guide: <https://ctan.org/pkg/beamer>
- Overleaf Beamer Gallery: <https://www.overleaf.com/gallery/tagged/presentation>

### 案例研究

- 观看往届ICSE的演讲录像
- 学习顶级研究者的演讲风格

---

**创建时间**: 2025-10-18  
**状态**: 待论文录用后使用  
**维护者**: 论文作者团队

**下一步**: 等待ICSE 2026录用通知 → 定制演讲 → 练习 → 出发！
