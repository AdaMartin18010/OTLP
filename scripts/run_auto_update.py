#!/usr/bin/env python3
"""
OpenTelemetry 2025 项目自动更新主脚本
一键运行所有自动化更新任务
"""

import os
import sys
import subprocess
from pathlib import Path
from datetime import datetime

def run_script(script_name: str, description: str) -> bool:
    """运行脚本"""
    print(f"\n🔄 {description}...")
    print("-" * 50)
    
    try:
        result = subprocess.run([
            sys.executable, script_name
        ], capture_output=True, text=True, cwd=Path(__file__).parent)
        
        if result.returncode == 0:
            print(f"✅ {description} 完成")
            if result.stdout:
                print(result.stdout)
            return True
        else:
            print(f"❌ {description} 失败")
            if result.stderr:
                print(f"错误: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ {description} 异常: {e}")
        return False

def main():
    """主函数"""
    print("🚀 OpenTelemetry 2025 项目自动更新系统")
    print("=" * 60)
    print(f"开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    scripts_dir = Path(__file__).parent
    os.chdir(scripts_dir)
    
    # 定义要运行的脚本
    scripts = [
        ("auto_generate_toc.py", "自动生成目录结构"),
        ("auto_update_navigation.py", "自动更新导航文件"),
    ]
    
    success_count = 0
    total_count = len(scripts)
    
    for script_name, description in scripts:
        if run_script(script_name, description):
            success_count += 1
    
    print("\n" + "=" * 60)
    print("📊 执行结果汇总")
    print(f"✅ 成功: {success_count}/{total_count}")
    print(f"❌ 失败: {total_count - success_count}/{total_count}")
    
    if success_count == total_count:
        print("\n🎉 所有自动化任务执行成功!")
        print("📁 目录结构已自动更新")
        print("🗺️ 导航文件已自动更新")
        print("📊 统计报告已生成")
    else:
        print(f"\n⚠️ 有 {total_count - success_count} 个任务执行失败")
        print("请检查错误信息并手动修复")
    
    print(f"\n结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

if __name__ == "__main__":
    main()
