#!/usr/bin/env python3
"""
文档目录格式批量修复工具

功能:
1. 批量修复目录格式: ## 目录 → ## 📋 目录
2. 批量修复目录链接: [目录](#目录) → [📋 目录](#-目录)
"""

import os
import re
from pathlib import Path
from typing import List, Tuple

def find_markdown_files(root_dir: str) -> List[Path]:
    """查找所有Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        # 跳过某些目录
        dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules', '__pycache__']]
        for file in files:
            if file.endswith('.md'):
                md_files.append(Path(root) / file)
    return md_files

def fix_toc_format(content: str) -> Tuple[str, int]:
    """修复目录格式"""
    fixes = 0
    
    # 修复目录标题: ## 目录 → ## 📋 目录
    pattern1 = re.compile(r'^## 目录\s*$', re.MULTILINE)
    if pattern1.search(content):
        content = pattern1.sub('## 📋 目录', content)
        fixes += 1
    
    # 修复目录链接: [目录](#目录) → [📋 目录](#-目录)
    pattern2 = re.compile(r'  - \[目录\]\(#目录\)')
    matches = pattern2.findall(content)
    if matches:
        content = pattern2.sub('  - [📋 目录](#-目录)', content)
        fixes += len(matches)
    
    return content, fixes

def process_file(file_path: Path) -> Tuple[bool, int]:
    """处理单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        content, fixes = fix_toc_format(content)
        
        if fixes > 0:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return True, fixes
        return False, 0
    except Exception as e:
        print(f"处理文件 {file_path} 时出错: {e}")
        return False, 0

def main():
    """主函数"""
    root_dir = Path(__file__).parent.parent / 'docs'
    
    if not root_dir.exists():
        print(f"目录不存在: {root_dir}")
        return
    
    print(f"开始扫描目录: {root_dir}")
    md_files = find_markdown_files(str(root_dir))
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    fixed_files = []
    total_fixes = 0
    
    for md_file in md_files:
        fixed, fixes = process_file(md_file)
        if fixed:
            fixed_files.append((md_file, fixes))
            total_fixes += fixes
    
    print(f"\n修复完成!")
    print(f"修复文件数: {len(fixed_files)}")
    print(f"总修复数: {total_fixes}")
    
    if fixed_files:
        print("\n修复的文件:")
        for file_path, fixes in fixed_files:
            print(f"  - {file_path.relative_to(root_dir.parent)} ({fixes} 处修复)")

if __name__ == '__main__':
    main()
