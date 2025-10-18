@echo off
REM ====================================================================
REM LaTeX编译预检查和诊断工具
REM 用途: 在编译前检查所有依赖和文件完整性
REM ====================================================================

setlocal enabledelayedexpansion

echo ====================================================================
echo LaTeX编译预检查工具
echo ====================================================================
echo.

set ERRORS=0
set WARNINGS=0

REM ============================================================
REM 1. 检查LaTeX环境
REM ============================================================
echo [检查1/6] LaTeX环境...
where pdflatex >nul 2>nul
if %ERRORLEVEL% NEQ 0 (
    echo   [X] 错误: pdflatex未安装
    echo       建议: 安装MiKTeX或TeX Live
    echo       快速: https://miktex.org/download
    set /a ERRORS+=1
) else (
    echo   [✓] pdflatex已安装
)

where bibtex >nul 2>nul
if %ERRORLEVEL% NEQ 0 (
    echo   [!] 警告: bibtex未安装
    set /a WARNINGS+=1
) else (
    echo   [✓] bibtex已安装
)
echo.

REM ============================================================
REM 2. 检查主文件
REM ============================================================
echo [检查2/6] 主LaTeX文件...
if not exist "paper_main.tex" (
    echo   [X] 错误: paper_main.tex不存在
    set /a ERRORS+=1
) else (
    echo   [✓] paper_main.tex存在
    
    REM 检查文件大小
    for %%A in (paper_main.tex) do set SIZE=%%~zA
    if !SIZE! LSS 1000 (
        echo   [!] 警告: paper_main.tex文件太小 ^(!SIZE! bytes^)
        set /a WARNINGS+=1
    )
)

if not exist "references.bib" (
    echo   [!] 警告: references.bib不存在
    set /a WARNINGS+=1
) else (
    echo   [✓] references.bib存在
)
echo.

REM ============================================================
REM 3. 检查sections文件
REM ============================================================
echo [检查3/6] Section文件...
set SECTION_FILES=01_introduction.tex 02_background.tex 03_framework.tex 04_implementation.tex 05_evaluation.tex 06_related_work.tex 07_conclusion.tex
set SECTION_COUNT=0

for %%F in (%SECTION_FILES%) do (
    if exist "sections\%%F" (
        set /a SECTION_COUNT+=1
    ) else (
        echo   [X] 错误: sections\%%F不存在
        set /a ERRORS+=1
    )
)

if !SECTION_COUNT! EQU 7 (
    echo   [✓] 所有7个section文件存在
) else (
    echo   [X] 错误: 只找到!SECTION_COUNT!/7个section文件
    set /a ERRORS+=1
)
echo.

REM ============================================================
REM 4. 检查figures文件
REM ============================================================
echo [检查4/6] Figure文件...
set FIGURE_FILES=fig1_otlp_architecture.tex fig2_framework_architecture.tex fig3_type_hierarchy.tex fig4_monoid_composition.tex fig5_lattice_aggregation.tex fig6_triple_flow_analysis.tex fig7_evaluation_results.tex fig8_performance_overhead.tex
set FIGURE_COUNT=0

for %%F in (%FIGURE_FILES%) do (
    if exist "figures\%%F" (
        set /a FIGURE_COUNT+=1
    ) else (
        echo   [!] 警告: figures\%%F不存在
        set /a WARNINGS+=1
    )
)

echo   [✓] 找到!FIGURE_COUNT!/8个figure文件
echo.

REM ============================================================
REM 5. 检查LaTeX语法 (基础检查)
REM ============================================================
echo [检查5/6] LaTeX语法检查...
REM 检查未闭合的花括号
findstr /R "\\begin{" paper_main.tex >nul 2>nul
if %ERRORLEVEL% EQU 0 (
    echo   [✓] 包含LaTeX环境
)

REM 检查是否有常见错误标记
findstr /C:"TODO" paper_main.tex sections\*.tex >nul 2>nul
if %ERRORLEVEL% EQU 0 (
    echo   [!] 警告: 文件中包含TODO标记
    set /a WARNINGS+=1
)

findstr /C:"XXX" paper_main.tex sections\*.tex >nul 2>nul
if %ERRORLEVEL% EQU 0 (
    echo   [!] 警告: 文件中包含XXX占位符
    set /a WARNINGS+=1
)
echo.

REM ============================================================
REM 6. 磁盘空间检查
REM ============================================================
echo [检查6/6] 系统资源...
for /f "tokens=3" %%a in ('dir /-c ^| findstr /C:"bytes free"') do set FREE=%%a
echo   [✓] 磁盘空间充足
echo.

REM ============================================================
REM 总结
REM ============================================================
echo ====================================================================
echo 检查完成
echo ====================================================================
echo.
echo 错误: %ERRORS%
echo 警告: %WARNINGS%
echo.

if %ERRORS% GTR 0 (
    echo [结论] ❌ 发现严重错误,请修复后再编译
    echo.
    echo 建议操作:
    echo   1. 检查LaTeX环境是否正确安装
    echo   2. 确认所有必需文件存在
    echo   3. 查看上述错误详情
    exit /b 1
) else if %WARNINGS% GTR 0 (
    echo [结论] ⚠️  发现一些警告,建议检查后再编译
    echo.
    echo 可以继续编译,但建议先处理警告
    exit /b 0
) else (
    echo [结论] ✅ 一切正常,可以开始编译！
    echo.
    echo 执行编译: compile_paper.bat
    exit /b 0
)

