@echo off
REM ====================================================================
REM OTLP ICSE2026 论文自动编译脚本
REM 使用方法: 双击运行此脚本，或在CMD中执行 compile_paper.bat
REM 前提条件: 已安装MiKTeX或TeX Live
REM ====================================================================

echo ====================================================================
echo OTLP ICSE2026 论文编译脚本
echo ====================================================================
echo.

REM 检查pdflatex是否安装
where pdflatex >nul 2>nul
if %ERRORLEVEL% NEQ 0 (
    echo [错误] 未检测到pdflatex命令
    echo.
    echo 请先安装LaTeX环境:
    echo   方案A: Overleaf在线编译 ^(推荐^)
    echo          访问: https://www.overleaf.com
    echo   方案B: MiKTeX本地安装
    echo          访问: https://miktex.org/download
    echo.
    echo 详细说明请查看: LATEX_ENVIRONMENT_SETUP_GUIDE.md
    echo.
    pause
    exit /b 1
)

echo [1/5] 检查LaTeX环境...
pdflatex --version | findstr "pdfTeX"
if %ERRORLEVEL% NEQ 0 (
    echo [错误] pdflatex版本检查失败
    pause
    exit /b 1
)
echo [✓] LaTeX环境正常
echo.

REM 检查主文件是否存在
if not exist "paper_main.tex" (
    echo [错误] 找不到paper_main.tex文件
    echo 请确保在academic目录下运行此脚本
    pause
    exit /b 1
)

echo [2/5] 第一次编译 - 生成.aux文件...
pdflatex -interaction=nonstopmode paper_main.tex
if %ERRORLEVEL% NEQ 0 (
    echo [警告] 首次编译有错误，继续尝试...
)
echo.

echo [3/5] 运行BibTeX - 处理参考文献...
bibtex paper_main
if %ERRORLEVEL% NEQ 0 (
    echo [警告] BibTeX处理有问题，继续尝试...
)
echo.

echo [4/5] 第二次编译 - 整合参考文献...
pdflatex -interaction=nonstopmode paper_main.tex
if %ERRORLEVEL% NEQ 0 (
    echo [警告] 第二次编译有错误，继续尝试...
)
echo.

echo [5/5] 第三次编译 - 最终生成PDF...
pdflatex -interaction=nonstopmode paper_main.tex
if %ERRORLEVEL% NEQ 0 (
    echo [错误] 最终编译失败
    echo 请检查paper_main.log文件查看详细错误
    pause
    exit /b 1
)
echo.

REM 检查PDF是否生成
if exist "paper_main.pdf" (
    echo ====================================================================
    echo [✓] 编译成功！
    echo ====================================================================
    echo.
    echo PDF文件已生成: paper_main.pdf
    echo.
    
    REM 统计页数（如果安装了pdfinfo）
    where pdfinfo >nul 2>nul
    if %ERRORLEVEL% EQU 0 (
        echo 统计信息:
        pdfinfo paper_main.pdf | findstr "Pages"
    )
    
    echo.
    echo 下一步建议:
    echo   1. 打开paper_main.pdf查看编译结果
    echo   2. 检查页数是否符合要求 ^(目标: 11页^)
    echo   3. 检查是否有编译警告 ^(查看paper_main.log^)
    echo   4. 嵌入表格和图表
    echo.
    
    REM 尝试自动打开PDF
    echo 正在尝试打开PDF...
    start paper_main.pdf
    
) else (
    echo [错误] PDF文件未生成
    echo 请检查paper_main.log文件查看详细错误
)

echo.
echo ====================================================================
echo 编译过程结束
echo ====================================================================
pause

