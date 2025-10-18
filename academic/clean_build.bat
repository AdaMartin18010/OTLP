@echo off
REM ====================================================================
REM 清理LaTeX编译产生的辅助文件
REM 用途: 编译出错时清理临时文件,或准备重新编译
REM ====================================================================

echo ====================================================================
echo LaTeX构建清理工具
echo ====================================================================
echo.

echo 正在清理辅助文件...
echo.

REM LaTeX辅助文件列表
set FILES=*.aux *.log *.out *.toc *.bbl *.blg *.synctex.gz *.fdb_latexmk *.fls *.nav *.snm *.vrb

set COUNT=0
for %%F in (%FILES%) do (
    if exist "%%F" (
        del "%%F" >nul 2>nul
        if not exist "%%F" (
            echo   [✓] 删除: %%F
            set /a COUNT+=1
        )
    )
)

REM 清理sections目录下的辅助文件
if exist "sections\*.aux" (
    del "sections\*.aux" >nul 2>nul
    echo   [✓] 清理sections\*.aux
)

echo.
echo ====================================================================
echo 清理完成: 删除了 %COUNT% 个辅助文件
echo ====================================================================
echo.

REM 检查PDF是否保留
if exist "paper_main.pdf" (
    echo [选项] paper_main.pdf仍然保留
    echo.
    choice /C YN /M "是否也删除PDF文件"
    if !ERRORLEVEL! EQU 1 (
        del paper_main.pdf
        echo [✓] 已删除paper_main.pdf
    ) else (
        echo [i] 保留paper_main.pdf
    )
)

echo.
echo 现在可以重新编译了！
pause

