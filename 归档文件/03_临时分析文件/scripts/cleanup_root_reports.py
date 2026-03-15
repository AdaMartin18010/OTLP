#!/usr/bin/env python3
"""
根目录报告文件清理工具
自动将28个历史报告文件移动到归档目录
"""

import os
import shutil
from pathlib import Path
from datetime import datetime

# 需要移动的文件列表
FILES_TO_ARCHIVE = [
    "⚡_快速开始_LaTeX编译_2025_10_17.md",
    "✅_准备工作全部完成_等待启动_2025_10_17.md",
    "🌟_第9次持续推进完成_2025_10_17.md",
    "🌟_选项A学术完善_最终报告_2025_10_17.md",
    "🎉_P0任务全部完成_2025_10_17.md",
    "🎉_最终完成报告_2025_10_17.md",
    "🎉_持续推进完成报告_READY_TO_COMPILE_2025_10_17.md",
    "🎉_论文初稿完成报告_2025_10_17.md",
    "🎉_论文编译准备全部完成_2025_10_17.md",
    "🎉_项目完美收官_2025_10_17_FINAL.md",
    "🎊_持续推进完成报告_2025_10_17.md",
    "🎊_第10次持续推进完成_2025_10_17_FINAL.md",
    "🎊_编译准备全部完成_2025_10_17_LATEST.md",
    "🎓_论文写作进度更新_Week1_2025_10_17.md",
    "🎓_论文写作进度更新_Week2_2025_10_17.md",
    "🎓_论文撰写启动报告_2025_10_17.md",
    "🎯_LaTeX环境配置任务启动_2025_10_17_FINAL.md",
    "🎯_LaTeX集成启动报告_2025_10_17.md",
    "🎯_现在就开始编译_2025_10_17.md",
    "🏆_全部任务完成_2025_10_17.md",
    "📊_论文编译环境配置进度_2025_10_17.md",
    "📝_第9次持续推进总结_2025_10_17.md",
    "🔴_LaTeX环境未安装_立即行动_2025_10_17.md",
    "🚀_LaTeX编译全面推进完成_2025_10_17_FINAL.md",
    "🚀_最终推进总结_2025_10_17.md",
    "🚀_持续推进完成报告_2025_10_17_FINAL.md",
    "🚀_持续推进完成报告_2025_10_17_更新.md",
    "🚀_项目持续推进_论文阶段启动_2025_10_17.md",
]

def cleanup_root_reports(dry_run=True):
    """
    清理根目录的报告文件
    
    Args:
        dry_run: 如果为True，只显示将要执行的操作，不实际移动文件
    """
    print("="*70)
    print("根目录报告文件清理工具")
    print("="*70)
    print(f"模式: {'🔍 预览模式（不会实际移动文件）' if dry_run else '⚠️  执行模式（将实际移动文件）'}")
    print(f"日期: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    
    # 创建归档目录
    archive_dir = Path("doc_legacy_archive/2025_10_reports")
    
    if not dry_run:
        archive_dir.mkdir(parents=True, exist_ok=True)
        print(f"✅ 创建归档目录: {archive_dir}\n")
    else:
        print(f"📁 将创建归档目录: {archive_dir}\n")
    
    # 统计
    found_files = []
    missing_files = []
    
    print("扫描文件...\n")
    
    for filename in FILES_TO_ARCHIVE:
        filepath = Path(filename)
        if filepath.exists():
            found_files.append(filename)
            size = filepath.stat().st_size
            print(f"✅ 找到: {filename} ({size:,} bytes)")
        else:
            missing_files.append(filename)
            print(f"⚠️  缺失: {filename}")
    
    print(f"\n" + "="*70)
    print(f"扫描结果:")
    print(f"  找到: {len(found_files)} 个文件")
    print(f"  缺失: {len(missing_files)} 个文件")
    print("="*70 + "\n")
    
    if not found_files:
        print("❌ 没有找到需要移动的文件")
        return
    
    # 移动文件
    if dry_run:
        print("以下文件将被移动:\n")
        for filename in found_files:
            target = archive_dir / filename
            print(f"  {filename}")
            print(f"    → {target}\n")
    else:
        print("开始移动文件...\n")
        moved_count = 0
        for filename in found_files:
            source = Path(filename)
            target = archive_dir / filename
            try:
                shutil.move(str(source), str(target))
                print(f"✅ 移动: {filename}")
                moved_count += 1
            except Exception as e:
                print(f"❌ 失败: {filename} - {e}")
        
        print(f"\n{'='*70}")
        print(f"移动完成: {moved_count}/{len(found_files)} 个文件")
        print("="*70)
        
        # 创建README
        readme_path = archive_dir / "README.md"
        with open(readme_path, 'w', encoding='utf-8') as f:
            f.write("# 历史报告归档（2025年10月）\n\n")
            f.write(f"**归档日期**: {datetime.now().strftime('%Y-%m-%d')}\n")
            f.write(f"**归档原因**: 项目结构优化，清理根目录\n")
            f.write(f"**文件数量**: {moved_count} 个\n\n")
            f.write("## 文件列表\n\n")
            for filename in sorted(found_files):
                f.write(f"- {filename}\n")
            f.write("\n## 说明\n\n")
            f.write("这些文件是项目在2025年10月17日的各个推进阶段产生的状态报告。\n")
            f.write("为了保持根目录整洁，已统一移动到此归档目录。\n\n")
            f.write("**当前项目状态请参考**: `../../PROJECT_STATUS_2025_10_18.md`\n")
        
        print(f"\n✅ 创建归档说明: {readme_path}")
    
    print("\n" + "="*70)
    print("清理完成！")
    print("="*70)

if __name__ == "__main__":
    import sys
    
    print("\n")
    
    # 首先以预览模式运行
    cleanup_root_reports(dry_run=True)
    
    print("\n" + "="*70)
    print("⚠️  注意：上面是预览模式的结果")
    print("="*70)
    
    # 询问是否继续
    if len(sys.argv) > 1 and sys.argv[1] == "--execute":
        print("\n检测到 --execute 参数，将执行实际移动操作\n")
        cleanup_root_reports(dry_run=False)
    else:
        print("\n要执行实际移动操作，请运行:")
        print("  python scripts/cleanup_root_reports.py --execute\n")

