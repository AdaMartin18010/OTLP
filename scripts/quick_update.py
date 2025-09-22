#!/usr/bin/env python3
"""
OpenTelemetry 2025 快速更新脚本
简化版本，快速更新文档目录和导航
"""

import os
import sys
from pathlib import Path

# 添加脚本目录到路径
script_dir = Path(__file__).parent
sys.path.insert(0, str(script_dir))

def quick_update():
    """快速更新"""
    print("🚀 OpenTelemetry 2025 快速更新")
    print("=" * 40)
    
    try:
        # 导入智能文档管理器
        from smart_document_manager import SmartDocumentManager
        
        # 创建管理器实例
        manager = SmartDocumentManager()
        
        # 扫描文档
        print("🔍 扫描文档...")
        documents, changed_files = manager.scan_documents()
        
        if not documents:
            print("❌ 未找到任何文档")
            return
        
        print(f"📁 扫描了 {len(documents)} 个模块")
        print(f"🔄 发现 {len(changed_files)} 个文件有变化")
        
        # 生成目录
        print("📝 生成目录...")
        toc_content = manager.generate_comprehensive_toc(documents)
        
        toc_file = manager.doc_root / "00_项目概览与导航" / "快速更新目录.md"
        toc_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(toc_file, 'w', encoding='utf-8') as f:
            f.write(toc_content)
        print(f"✅ 已生成目录: {toc_file}")
        
        # 更新导航
        print("🗺️ 更新导航...")
        manager.update_navigation_file(documents)
        
        # 生成简单统计
        total_files = sum(module['stats']['total_files'] for module in documents.values())
        total_size = sum(module['stats']['total_size'] for module in documents.values())
        
        print("\n📊 更新完成!")
        print(f"📁 模块数: {len(documents)}")
        print(f"📄 文档数: {total_files}")
        print(f"💾 总大小: {total_size / 1024 / 1024:.1f} MB")
        print(f"🔄 变化文件: {len(changed_files)}")
        
    except ImportError as e:
        print(f"❌ 导入错误: {e}")
        print("请确保所有依赖已安装")
    except Exception as e:
        print(f"❌ 执行错误: {e}")

if __name__ == "__main__":
    quick_update()
