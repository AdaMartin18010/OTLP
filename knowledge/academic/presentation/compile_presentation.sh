#!/bin/bash
# ====================================================================
# ICSE 2026 Presentation自动编译脚本 (Linux/Mac)
# 用途: 编译Beamer演讲PPT
# ====================================================================

echo "===================================================================="
echo "ICSE 2026 Presentation编译脚本"
echo "===================================================================="
echo ""

# 检查pdflatex
if ! command -v pdflatex &> /dev/null; then
    echo "[错误] 未检测到pdflatex"
    echo "请先安装LaTeX环境"
    exit 1
fi

echo "[1/3] 第一次编译..."
pdflatex -interaction=nonstopmode presentation_main.tex
echo ""

echo "[2/3] 第二次编译 (解决引用)..."
pdflatex -interaction=nonstopmode presentation_main.tex
echo ""

echo "[3/3] 第三次编译 (最终版本)..."
pdflatex -interaction=nonstopmode presentation_main.tex
echo ""

if [ -f "presentation_main.pdf" ]; then
    echo "===================================================================="
    echo "[✓] 编译成功！"
    echo "===================================================================="
    echo ""
    echo "PDF文件: presentation_main.pdf"
    echo ""
    
    # macOS
    if [[ "$OSTYPE" == "darwin"* ]]; then
        echo "正在打开PDF..."
        open presentation_main.pdf
    fi
    
    # Linux
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        if command -v xdg-open &> /dev/null; then
            echo "正在打开PDF..."
            xdg-open presentation_main.pdf
        fi
    fi
else
    echo "[错误] PDF未生成"
    echo "请查看日志: presentation_main.log"
    exit 1
fi

