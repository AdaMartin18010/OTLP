@echo off
chcp 65001 >nul
echo 🚀 OpenTelemetry 2025 自动化系统
echo ================================================
echo.

REM 检查虚拟环境是否存在
if exist ".venv\Scripts\python.exe" (
    echo ✅ 找到虚拟环境
    set PYTHON_CMD=.venv\Scripts\python.exe
) else (
    echo ⚠️ 未找到虚拟环境，使用系统Python
    set PYTHON_CMD=python
)

REM 检查Python是否可用
%PYTHON_CMD% --version >nul 2>&1
if errorlevel 1 (
    echo ❌ Python不可用，请检查安装
    pause
    exit /b 1
)

echo 🔍 检查依赖...
%PYTHON_CMD% -c "import yaml" >nul 2>&1
if errorlevel 1 (
    echo ❌ 缺少PyYAML依赖，正在安装...
    %PYTHON_CMD% -m pip install PyYAML
    if errorlevel 1 (
        echo ❌ 依赖安装失败
        pause
        exit /b 1
    )
)

echo ✅ 依赖检查通过
echo.

REM 运行自动化脚本
echo 🚀 开始运行自动化任务...
echo.
%PYTHON_CMD% scripts/run_all_automation.py

echo.
echo 🎉 自动化任务完成！
echo.
echo 💡 提示:
echo - 查看 doc/00_项目概览与导航/ 目录获取最新文档
echo - 查看 scripts/backups/ 目录获取备份文件
echo.
pause
