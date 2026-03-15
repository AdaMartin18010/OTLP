@echo off
REM ====================================================================
REM ICSE 2026 Presentation自动编译脚本
REM 用途: 编译Beamer演讲PPT
REM ====================================================================

echo ====================================================================
echo ICSE 2026 Presentation编译脚本
echo ====================================================================
echo.

REM 检查pdflatex
where pdflatex >nul 2>nul
if %ERRORLEVEL% NEQ 0 (
    echo [错误] 未检测到pdflatex
    echo 请先安装LaTeX环境
    pause
    exit /b 1
)

echo [1/3] 第一次编译...
pdflatex -interaction=nonstopmode presentation_main.tex
echo.

echo [2/3] 第二次编译 (解决引用)...
pdflatex -interaction=nonstopmode presentation_main.tex
echo.

echo [3/3] 第三次编译 (最终版本)...
pdflatex -interaction=nonstopmode presentation_main.tex
echo.

if exist "presentation_main.pdf" (
    echo ====================================================================
    echo [✓] 编译成功！
    echo ====================================================================
    echo.
    echo PDF文件: presentation_main.pdf
    echo.
    echo 正在打开PDF...
    start presentation_main.pdf
) else (
    echo [错误] PDF未生成
    echo 请查看日志: presentation_main.log
)

pause

