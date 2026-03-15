#!/bin/bash
# ====================================================================
# OTLP ICSE2026 论文自动编译脚本 (Linux/Mac)
# 使用方法: chmod +x compile_paper.sh && ./compile_paper.sh
# 前提条件: 已安装TeX Live
# ====================================================================

echo "===================================================================="
echo "OTLP ICSE2026 论文编译脚本"
echo "===================================================================="
echo ""

# 检查pdflatex是否安装
if ! command -v pdflatex &> /dev/null; then
    echo "[错误] 未检测到pdflatex命令"
    echo ""
    echo "请先安装LaTeX环境:"
    echo "  Ubuntu/Debian: sudo apt-get install texlive-full"
    echo "  macOS: brew install --cask mactex"
    echo "  或使用Overleaf在线编译: https://www.overleaf.com"
    echo ""
    echo "详细说明请查看: LATEX_ENVIRONMENT_SETUP_GUIDE.md"
    echo ""
    exit 1
fi

echo "[1/5] 检查LaTeX环境..."
pdflatex --version | head -n 1
if [ $? -ne 0 ]; then
    echo "[错误] pdflatex版本检查失败"
    exit 1
fi
echo "[✓] LaTeX环境正常"
echo ""

# 检查主文件是否存在
if [ ! -f "paper_main.tex" ]; then
    echo "[错误] 找不到paper_main.tex文件"
    echo "请确保在academic目录下运行此脚本"
    exit 1
fi

echo "[2/5] 第一次编译 - 生成.aux文件..."
pdflatex -interaction=nonstopmode paper_main.tex
if [ $? -ne 0 ]; then
    echo "[警告] 首次编译有错误，继续尝试..."
fi
echo ""

echo "[3/5] 运行BibTeX - 处理参考文献..."
bibtex paper_main
if [ $? -ne 0 ]; then
    echo "[警告] BibTeX处理有问题，继续尝试..."
fi
echo ""

echo "[4/5] 第二次编译 - 整合参考文献..."
pdflatex -interaction=nonstopmode paper_main.tex
if [ $? -ne 0 ]; then
    echo "[警告] 第二次编译有错误，继续尝试..."
fi
echo ""

echo "[5/5] 第三次编译 - 最终生成PDF..."
pdflatex -interaction=nonstopmode paper_main.tex
if [ $? -ne 0 ]; then
    echo "[错误] 最终编译失败"
    echo "请检查paper_main.log文件查看详细错误"
    exit 1
fi
echo ""

# 检查PDF是否生成
if [ -f "paper_main.pdf" ]; then
    echo "===================================================================="
    echo "[✓] 编译成功！"
    echo "===================================================================="
    echo ""
    echo "PDF文件已生成: paper_main.pdf"
    echo ""
    
    # 统计页数（如果安装了pdfinfo）
    if command -v pdfinfo &> /dev/null; then
        echo "统计信息:"
        pdfinfo paper_main.pdf | grep "Pages"
    fi
    
    echo ""
    echo "下一步建议:"
    echo "  1. 打开paper_main.pdf查看编译结果"
    echo "  2. 检查页数是否符合要求 (目标: 11页)"
    echo "  3. 检查是否有编译警告 (查看paper_main.log)"
    echo "  4. 嵌入表格和图表"
    echo ""
    
    # 尝试自动打开PDF (macOS)
    if [[ "$OSTYPE" == "darwin"* ]]; then
        echo "正在尝试打开PDF..."
        open paper_main.pdf
    fi
    
    # 尝试自动打开PDF (Linux)
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        if command -v xdg-open &> /dev/null; then
            echo "正在尝试打开PDF..."
            xdg-open paper_main.pdf
        fi
    fi
    
else
    echo "[错误] PDF文件未生成"
    echo "请检查paper_main.log文件查看详细错误"
    exit 1
fi

echo ""
echo "===================================================================="
echo "编译过程结束"
echo "===================================================================="

