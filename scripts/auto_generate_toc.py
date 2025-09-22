#!/usr/bin/env python3
"""
OpenTelemetry 2025 项目自动目录生成脚本
自动扫描文档结构并生成目录索引
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import yaml
from datetime import datetime

class DocumentTOCGenerator:
    def __init__(self, doc_root: str = "doc"):
        # 获取脚本所在目录的父目录作为项目根目录
        script_dir = Path(__file__).parent
        project_root = script_dir.parent
        self.doc_root = project_root / doc_root
        self.toc_structure = {}
        self.navigation_links = {}
        
    def scan_document_structure(self) -> Dict:
        """扫描文档结构"""
        structure = {}
        
        for item in sorted(self.doc_root.iterdir()):
            if item.is_dir() and not item.name.startswith('.'):
                structure[item.name] = self._scan_directory(item)
                
        return structure
    
    def _scan_directory(self, directory: Path) -> Dict:
        """递归扫描目录"""
        content = {
            'files': [],
            'subdirs': {}
        }
        
        for item in sorted(directory.iterdir()):
            if item.is_file() and item.suffix == '.md':
                content['files'].append({
                    'name': item.name,
                    'path': str(item.relative_to(self.doc_root)),
                    'title': self._extract_title(item)
                })
            elif item.is_dir() and not item.name.startswith('.'):
                content['subdirs'][item.name] = self._scan_directory(item)
                
        return content
    
    def _extract_title(self, file_path: Path) -> str:
        """从Markdown文件中提取标题"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                first_line = f.readline().strip()
                if first_line.startswith('#'):
                    return first_line[1:].strip()
                return file_path.stem
        except:
            return file_path.stem
    
    def generate_toc_markdown(self, structure: Dict) -> str:
        """生成Markdown格式的目录"""
        toc_lines = [
            "# OpenTelemetry 2025 项目文档目录",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            f"**文档版本**: 2.0.0",
            f"**维护者**: OpenTelemetry 2025 自动化系统",
            f"**状态**: 知识理论模型分析梳理项目",
            f"**目录范围**: 完整文档体系目录",
            "",
            "## 🎯 目录概览",
            "",
            "### 主要模块",
            ""
        ]
        
        # 生成模块概览
        module_count = 0
        for module_name, module_content in structure.items():
            module_count += 1
            file_count = self._count_files(module_content)
            toc_lines.append(f"{module_count}. **{module_name}** - {file_count} 个文档")
        
        toc_lines.extend([
            "",
            f"**总模块数**: {len(structure)}",
            f"**总文档数**: {self._count_total_files(structure)}",
            "",
            "## 📚 详细目录结构",
            ""
        ])
        
        # 生成详细目录
        for module_name, module_content in structure.items():
            toc_lines.extend(self._generate_module_toc(module_name, module_content, 0))
        
        return "\n".join(toc_lines)
    
    def _count_files(self, content: Dict) -> int:
        """计算文件数量"""
        count = len(content.get('files', []))
        for subdir_content in content.get('subdirs', {}).values():
            count += self._count_files(subdir_content)
        return count
    
    def _count_total_files(self, structure: Dict) -> int:
        """计算总文件数"""
        total = 0
        for module_content in structure.values():
            total += self._count_files(module_content)
        return total
    
    def _generate_module_toc(self, name: str, content: Dict, level: int) -> List[str]:
        """生成模块目录"""
        lines = []
        indent = "  " * level
        
        # 模块标题
        if level == 0:
            lines.append(f"### {name}")
        else:
            lines.append(f"{indent}- **{name}**")
        
        lines.append("")
        
        # 文件列表
        for file_info in content.get('files', []):
            file_path = file_info['path']
            title = file_info['title']
            lines.append(f"{indent}  - [{title}]({file_path})")
        
        lines.append("")
        
        # 子目录
        for subdir_name, subdir_content in content.get('subdirs', {}).items():
            lines.extend(self._generate_module_toc(subdir_name, subdir_content, level + 1))
        
        return lines
    
    def generate_navigation_links(self, structure: Dict) -> str:
        """生成导航链接"""
        nav_lines = [
            "# OpenTelemetry 2025 项目导航链接",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            "",
            "## 🗺️ 快速导航",
            ""
        ]
        
        # 生成快速导航
        for module_name, module_content in structure.items():
            nav_lines.append(f"### {module_name}")
            nav_lines.append("")
            
            # 主要文档
            main_files = [f for f in module_content.get('files', []) 
                         if not any(keyword in f['name'].lower() 
                                  for keyword in ['readme', 'index', 'toc'])]
            
            for file_info in main_files[:5]:  # 限制显示数量
                nav_lines.append(f"- [{file_info['title']}]({file_info['path']})")
            
            if len(main_files) > 5:
                nav_lines.append(f"- ... 还有 {len(main_files) - 5} 个文档")
            
            nav_lines.append("")
        
        return "\n".join(nav_lines)
    
    def update_navigation_file(self, structure: Dict):
        """更新主导航文件"""
        nav_file = self.doc_root / "00_项目概览与导航" / "文档导航与索引.md"
        
        if not nav_file.exists():
            print(f"警告: 导航文件不存在: {nav_file}")
            return
        
        # 读取现有文件
        with open(nav_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 找到需要更新的部分
        start_marker = "## 🗺️ 完整文档导航"
        end_marker = "## 📊 文档统计"
        
        start_idx = content.find(start_marker)
        end_idx = content.find(end_marker)
        
        if start_idx == -1 or end_idx == -1:
            print("警告: 无法找到更新标记")
            return
        
        # 生成新的导航内容
        new_nav_content = self._generate_detailed_navigation(structure)
        
        # 更新内容
        new_content = (
            content[:start_idx] + 
            start_marker + "\n\n" + 
            new_nav_content + "\n\n" + 
            content[end_idx:]
        )
        
        # 写回文件
        with open(nav_file, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        print(f"✅ 已更新导航文件: {nav_file}")
    
    def _generate_detailed_navigation(self, structure: Dict) -> str:
        """生成详细导航内容"""
        lines = []
        
        for module_name, module_content in structure.items():
            lines.append(f"### {module_name}")
            lines.append("")
            
            # 生成模块内导航
            lines.extend(self._generate_module_navigation(module_name, module_content, 0))
            lines.append("")
        
        return "\n".join(lines)
    
    def _generate_module_navigation(self, name: str, content: Dict, level: int) -> List[str]:
        """生成模块导航"""
        lines = []
        indent = "  " * level
        
        # 文件链接
        for file_info in content.get('files', []):
            file_path = file_info['path']
            title = file_info['title']
            lines.append(f"{indent}- [{title}]({file_path})")
        
        # 子目录
        for subdir_name, subdir_content in content.get('subdirs', {}).items():
            lines.append(f"{indent}- **{subdir_name}**")
            lines.extend(self._generate_module_navigation(subdir_name, subdir_content, level + 1))
        
        return lines
    
    def generate_all(self):
        """生成所有目录和导航文件"""
        print("🔍 扫描文档结构...")
        structure = self.scan_document_structure()
        
        print("📝 生成目录文件...")
        toc_content = self.generate_toc_markdown(structure)
        
        # 保存目录文件
        toc_file = self.doc_root / "00_项目概览与导航" / "自动生成目录.md"
        with open(toc_file, 'w', encoding='utf-8') as f:
            f.write(toc_content)
        print(f"✅ 已生成目录文件: {toc_file}")
        
        print("🗺️ 更新导航文件...")
        self.update_navigation_file(structure)
        
        print("📊 生成统计信息...")
        stats = self._generate_stats(structure)
        print(stats)
        
        return structure
    
    def _generate_stats(self, structure: Dict) -> str:
        """生成统计信息"""
        total_modules = len(structure)
        total_files = self._count_total_files(structure)
        
        stats_lines = [
            "## 📊 文档统计",
            "",
            f"**总模块数**: {total_modules}",
            f"**总文档数**: {total_files}",
            "",
            "### 模块统计",
            ""
        ]
        
        for module_name, module_content in structure.items():
            file_count = self._count_files(module_content)
            stats_lines.append(f"- **{module_name}**: {file_count} 个文档")
        
        return "\n".join(stats_lines)

def main():
    """主函数"""
    print("🚀 OpenTelemetry 2025 项目自动目录生成器")
    print("=" * 50)
    
    generator = DocumentTOCGenerator()
    structure = generator.generate_all()
    
    print("\n✅ 目录生成完成!")
    print(f"📁 扫描了 {len(structure)} 个模块")
    print(f"📄 总共 {generator._count_total_files(structure)} 个文档")

if __name__ == "__main__":
    main()
