#!/usr/bin/env python3
"""
文档重复度分析工具
用于分析doc_legacy_archive/和docs/的重复内容
"""

import os
import hashlib
from collections import defaultdict
import json
from pathlib import Path

def calculate_file_hash(filepath):
    """计算文件的MD5哈希值"""
    try:
        with open(filepath, 'rb') as f:
            return hashlib.md5(f.read()).hexdigest()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return None

def scan_directory(directory, extension='.md'):
    """扫描目录中的所有指定扩展名文件"""
    files = []
    for root, dirs, filenames in os.walk(directory):
        for filename in filenames:
            if filename.endswith(extension):
                filepath = os.path.join(root, filename)
                files.append(filepath)
    return files

def analyze_duplicates(dir1, dir2, output_file):
    """分析两个目录的重复文件"""
    print(f"开始分析重复度...")
    print(f"目录1: {dir1}")
    print(f"目录2: {dir2}")
    
    hash_map = defaultdict(list)
    
    # 扫描第一个目录
    print(f"\n扫描 {dir1}...")
    dir1_files = scan_directory(dir1)
    print(f"找到 {len(dir1_files)} 个.md文件")
    
    for filepath in dir1_files:
        file_hash = calculate_file_hash(filepath)
        if file_hash:
            hash_map[file_hash].append(filepath)
    
    # 扫描第二个目录
    print(f"\n扫描 {dir2}...")
    dir2_files = scan_directory(dir2)
    print(f"找到 {len(dir2_files)} 个.md文件")
    
    for filepath in dir2_files:
        file_hash = calculate_file_hash(filepath)
        if file_hash:
            hash_map[file_hash].append(filepath)
    
    # 识别重复文件
    duplicates = {k: v for k, v in hash_map.items() if len(v) > 1}
    
    # 计算统计信息
    total_files = len(dir1_files) + len(dir2_files)
    duplicate_files = sum(len(v) for v in duplicates.values())
    unique_files = total_files - duplicate_files + len(duplicates)
    duplicate_rate = (duplicate_files / total_files * 100) if total_files > 0 else 0
    
    stats = {
        "total_files": total_files,
        "dir1_files": len(dir1_files),
        "dir2_files": len(dir2_files),
        "duplicate_groups": len(duplicates),
        "duplicate_files": duplicate_files,
        "unique_files": unique_files,
        "duplicate_rate": f"{duplicate_rate:.1f}%"
    }
    
    # 生成Markdown报告
    print(f"\n生成报告: {output_file}")
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write("# 文档重复度分析报告\n\n")
        f.write(f"**分析日期**: 2025-10-18\n")
        f.write(f"**分析工具**: analyze_duplicates.py\n\n")
        
        f.write("## 📊 统计概览\n\n")
        f.write(f"- **总文件数**: {stats['total_files']}\n")
        f.write(f"  - {dir1}: {stats['dir1_files']} 个文件\n")
        f.write(f"  - {dir2}: {stats['dir2_files']} 个文件\n")
        f.write(f"- **重复文件组数**: {stats['duplicate_groups']}\n")
        f.write(f"- **重复文件总数**: {stats['duplicate_files']}\n")
        f.write(f"- **唯一文件数**: {stats['unique_files']}\n")
        f.write(f"- **重复率**: {stats['duplicate_rate']}\n\n")
        
        f.write("## 🔍 重复文件详情\n\n")
        
        if duplicates:
            for i, (hash_val, files) in enumerate(duplicates.items(), 1):
                f.write(f"### 重复组 #{i}\n\n")
                f.write(f"**Hash**: `{hash_val[:16]}...`\n\n")
                f.write(f"**文件数**: {len(files)}\n\n")
                for filepath in files:
                    f.write(f"- `{filepath}`\n")
                f.write("\n")
        else:
            f.write("未发现重复文件。\n\n")
        
        f.write("## 💡 建议\n\n")
        if duplicate_rate > 30:
            f.write("🔴 **高重复率警告**: 重复率超过30%，建议立即清理。\n\n")
            f.write("**推荐操作**:\n")
            f.write("1. 评估哪些文件是最新版本\n")
            f.write("2. 将旧版本移动到归档目录\n")
            f.write("3. 更新所有引用链接\n")
        elif duplicate_rate > 10:
            f.write("🟡 **中等重复率**: 重复率在10-30%之间，建议适度清理。\n")
        else:
            f.write("🟢 **低重复率**: 重复率低于10%，文档结构良好。\n")
    
    # 保存JSON格式数据
    json_file = output_file.replace('.md', '.json')
    with open(json_file, 'w', encoding='utf-8') as f:
        json.dump({
            "stats": stats,
            "duplicate_groups": len(duplicates),
            "duplicates_sample": {k: v for k, v in list(duplicates.items())[:10]}
        }, f, indent=2, ensure_ascii=False)
    
    print(f"\n✅ 分析完成！")
    print(f"📄 Markdown报告: {output_file}")
    print(f"📊 JSON数据: {json_file}")
    print(f"\n发现 {len(duplicates)} 组重复文件（共 {duplicate_files} 个文件）")
    print(f"重复率: {stats['duplicate_rate']}")
    
    return duplicates, stats

if __name__ == "__main__":
    # 确保输出目录存在
    Path(".progress").mkdir(exist_ok=True)
    
    # 运行分析
    try:
        duplicates, stats = analyze_duplicates(
            "doc_legacy_archive",
            "docs",
            ".progress/duplicate_analysis_report.md"
        )
        
        print("\n" + "="*60)
        print("分析摘要")
        print("="*60)
        for key, value in stats.items():
            print(f"{key}: {value}")
        
    except Exception as e:
        print(f"\n❌ 分析失败: {e}")
        import traceback
        traceback.print_exc()

