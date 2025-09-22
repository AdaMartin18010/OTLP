#!/usr/bin/env python3
"""
OpenTelemetry 2025 项目自动导航更新脚本
自动更新项目导航和索引文件
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import yaml
from datetime import datetime

class NavigationUpdater:
    def __init__(self, doc_root: str = "doc"):
        # 获取脚本所在目录的父目录作为项目根目录
        script_dir = Path(__file__).parent
        project_root = script_dir.parent
        self.doc_root = project_root / doc_root
        self.nav_files = [
            "00_项目概览与导航/文档导航与索引.md",
            "00_项目概览/项目完整索引与导航系统.md"
        ]
        
    def scan_all_documents(self) -> Dict:
        """扫描所有文档"""
        documents = {}
        
        for item in sorted(self.doc_root.iterdir()):
            if item.is_dir() and not item.name.startswith('.'):
                documents[item.name] = self._scan_module(item)
                
        return documents
    
    def _scan_module(self, module_path: Path) -> Dict:
        """扫描模块"""
        module_info = {
            'name': module_path.name,
            'files': [],
            'submodules': {},
            'readme': None
        }
        
        for item in sorted(module_path.iterdir()):
            if item.is_file() and item.suffix == '.md':
                file_info = self._analyze_file(item)
                if item.name.lower() in ['readme.md', 'index.md']:
                    module_info['readme'] = file_info
                else:
                    module_info['files'].append(file_info)
            elif item.is_dir() and not item.name.startswith('.'):
                module_info['submodules'][item.name] = self._scan_module(item)
        
        return module_info
    
    def _analyze_file(self, file_path: Path) -> Dict:
        """分析文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 提取标题
            title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
            title = title_match.group(1) if title_match else file_path.stem
            
            # 提取创建时间
            time_match = re.search(r'\*\*创建时间\*\*:\s*(.+)', content)
            created_time = time_match.group(1) if time_match else "未知"
            
            # 提取版本
            version_match = re.search(r'\*\*文档版本\*\*:\s*(.+)', content)
            version = version_match.group(1) if version_match else "1.0.0"
            
            # 提取状态
            status_match = re.search(r'\*\*状态\*\*:\s*(.+)', content)
            status = status_match.group(1) if status_match else "活跃"
            
            return {
                'name': file_path.name,
                'path': str(file_path.relative_to(self.doc_root)),
                'title': title,
                'created_time': created_time,
                'version': version,
                'status': status,
                'size': file_path.stat().st_size,
                'modified': datetime.fromtimestamp(file_path.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S')
            }
        except Exception as e:
            print(f"警告: 无法分析文件 {file_path}: {e}")
            return {
                'name': file_path.name,
                'path': str(file_path.relative_to(self.doc_root)),
                'title': file_path.stem,
                'created_time': "未知",
                'version': "1.0.0",
                'status': "未知",
                'size': 0,
                'modified': "未知"
            }
    
    def generate_navigation_content(self, documents: Dict) -> str:
        """生成导航内容"""
        lines = [
            "# OpenTelemetry 2025 知识理论模型分析梳理项目文档导航",
            "",
            "## 📊 导航概览",
            "",
            f"**创建时间**: {datetime.now().strftime('%Y年%m月%d日')}",
            f"**文档版本**: 2.0.0",
            f"**维护者**: OpenTelemetry 2025 学术研究团队",
            f"**状态**: 知识理论模型分析梳理项目",
            f"**导航范围**: 完整文档体系导航",
            "",
            "## 🎯 导航目标",
            "",
            "### 主要目标",
            "",
            "1. **完整导航**: 提供完整的文档体系导航",
            "2. **快速定位**: 支持快速定位所需内容",
            "3. **逻辑清晰**: 提供清晰的逻辑结构",
            "4. **易于维护**: 支持易于维护的导航结构",
            "5. **用户友好**: 提供用户友好的导航体验",
            "",
            "### 成功标准",
            "",
            "- **导航完整性**: 100%文档覆盖",
            "- **定位准确性**: 快速准确的内容定位",
            "- **结构清晰性**: 清晰的逻辑结构",
            "- **维护便利性**: 易于维护和更新",
            "- **用户体验**: 良好的用户体验",
            "",
            "## 🗺️ 完整文档导航",
            ""
        ]
        
        # 生成模块导航
        for module_name, module_info in documents.items():
            lines.extend(self._generate_module_navigation(module_name, module_info))
        
        # 添加统计信息
        lines.extend(self._generate_statistics(documents))
        
        return "\n".join(lines)
    
    def _generate_module_navigation(self, module_name: str, module_info: Dict) -> List[str]:
        """生成模块导航"""
        lines = []
        
        # 模块标题
        lines.append(f"### {module_name}")
        lines.append("")
        
        # 模块描述
        if module_info.get('readme'):
            readme = module_info['readme']
            lines.append(f"**模块入口**: [{readme['title']}]({readme['path']})")
            lines.append("")
        
        # 主要文档
        main_files = [f for f in module_info.get('files', []) 
                     if not any(keyword in f['name'].lower() 
                              for keyword in ['readme', 'index', 'toc', 'summary'])]
        
        if main_files:
            lines.append("#### 核心文档")
            lines.append("")
            for file_info in main_files[:10]:  # 限制显示数量
                lines.append(f"- [{file_info['title']}]({file_info['path']})")
            
            if len(main_files) > 10:
                lines.append(f"- ... 还有 {len(main_files) - 10} 个文档")
            lines.append("")
        
        # 子模块
        if module_info.get('submodules'):
            lines.append("#### 子模块")
            lines.append("")
            for submodule_name, submodule_info in module_info['submodules'].items():
                lines.append(f"##### {submodule_name}")
                lines.append("")
                
                sub_files = submodule_info.get('files', [])
                for file_info in sub_files[:5]:  # 限制显示数量
                    lines.append(f"- [{file_info['title']}]({file_info['path']})")
                
                if len(sub_files) > 5:
                    lines.append(f"- ... 还有 {len(sub_files) - 5} 个文档")
                lines.append("")
        
        lines.append("")
        return lines
    
    def _generate_statistics(self, documents: Dict) -> List[str]:
        """生成统计信息"""
        lines = [
            "## 📊 文档统计",
            "",
            "### 总体统计",
            ""
        ]
        
        total_modules = len(documents)
        total_files = sum(self._count_files(module_info) for module_info in documents.values())
        
        lines.extend([
            f"- **总模块数**: {total_modules}",
            f"- **总文档数**: {total_files}",
            f"- **最后更新**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            "",
            "### 模块统计",
            ""
        ])
        
        for module_name, module_info in documents.items():
            file_count = self._count_files(module_info)
            lines.append(f"- **{module_name}**: {file_count} 个文档")
        
        lines.extend([
            "",
            "## 🔗 快速链接",
            "",
            "### 按主题导航",
            ""
        ])
        
        # 按主题分类
        theme_links = self._generate_theme_links(documents)
        lines.extend(theme_links)
        
        lines.extend([
            "",
            "### 按用户类型导航",
            "",
            "#### 研究人员",
            "- [理论基础与形式化证明](01_理论基础与形式化证明/)",
            "- [学术研究与理论创新](06_学术研究与理论创新/)",
            "- [批判性分析与评价](05_批判性分析与评价/)",
            "",
            "#### 工程师",
            "- [OTLP标准深度分析](02_OTLP标准深度分析/)",
            "- [实施指南与操作手册](07_实施指南与操作手册/)",
            "- [行业标准与最佳实践](03_行业标准与最佳实践/)",
            "",
            "#### 管理者",
            "- [项目概览与导航](00_项目概览与导航/)",
            "- [可持续发展计划](08_可持续发展计划/)",
            "- [附录与参考资料](09_附录与参考资料/)",
            "",
            "---",
            "",
            f"**文档创建完成时间**: {datetime.now().strftime('%Y年%m月%d日')}",
            f"**文档版本**: 2.0.0",
            f"**维护者**: OpenTelemetry 2025 学术研究团队",
            f"**下次审查**: {(datetime.now().replace(month=datetime.now().month+1) if datetime.now().month < 12 else datetime.now().replace(year=datetime.now().year+1, month=1)).strftime('%Y年%m月%d日')}"
        ])
        
        return lines
    
    def _count_files(self, module_info: Dict) -> int:
        """计算文件数量"""
        count = len(module_info.get('files', []))
        for submodule_info in module_info.get('submodules', {}).values():
            count += self._count_files(submodule_info)
        return count
    
    def _generate_theme_links(self, documents: Dict) -> List[str]:
        """生成主题链接"""
        theme_mapping = {
            "理论基础": ["01_理论基础与形式化证明"],
            "标准分析": ["02_OTLP标准深度分析", "03_行业标准与最佳实践"],
            "学术研究": ["06_学术研究与理论创新"],
            "批判分析": ["05_批判性分析与评价"],
            "实施指南": ["07_实施指南与操作手册"],
            "可持续发展": ["08_可持续发展计划"],
            "参考资料": ["09_附录与参考资料"]
        }
        
        lines = []
        for theme, modules in theme_mapping.items():
            lines.append(f"#### {theme}")
            for module in modules:
                if module in documents:
                    lines.append(f"- [{module}]({module}/)")
            lines.append("")
        
        return lines
    
    def update_navigation_files(self):
        """更新所有导航文件"""
        print("🔍 扫描文档结构...")
        documents = self.scan_all_documents()
        
        print("📝 生成导航内容...")
        nav_content = self.generate_navigation_content(documents)
        
        # 更新所有导航文件
        for nav_file_path in self.nav_files:
            nav_file = self.doc_root / nav_file_path
            if nav_file.exists():
                with open(nav_file, 'w', encoding='utf-8') as f:
                    f.write(nav_content)
                print(f"✅ 已更新导航文件: {nav_file}")
            else:
                print(f"⚠️ 导航文件不存在: {nav_file}")
        
        # 生成统计报告
        stats = self._generate_detailed_stats(documents)
        stats_file = self.doc_root / "00_项目概览与导航" / "文档统计报告.md"
        with open(stats_file, 'w', encoding='utf-8') as f:
            f.write(stats)
        print(f"✅ 已生成统计报告: {stats_file}")
        
        return documents
    
    def _generate_detailed_stats(self, documents: Dict) -> str:
        """生成详细统计报告"""
        lines = [
            "# OpenTelemetry 2025 项目文档统计报告",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            f"**报告版本**: 2.0.0",
            "",
            "## 📊 总体统计",
            ""
        ]
        
        total_modules = len(documents)
        total_files = sum(self._count_files(module_info) for module_info in documents.values())
        
        lines.extend([
            f"- **总模块数**: {total_modules}",
            f"- **总文档数**: {total_files}",
            f"- **平均每模块文档数**: {total_files / total_modules:.1f}",
            "",
            "## 📁 模块详细统计",
            ""
        ])
        
        for module_name, module_info in documents.items():
            file_count = self._count_files(module_info)
            submodule_count = len(module_info.get('submodules', {}))
            
            lines.extend([
                f"### {module_name}",
                f"- **文档数量**: {file_count}",
                f"- **子模块数量**: {submodule_count}",
                ""
            ])
            
            # 列出主要文档
            main_files = module_info.get('files', [])[:5]
            if main_files:
                lines.append("**主要文档**:")
                for file_info in main_files:
                    lines.append(f"- [{file_info['title']}]({file_info['path']})")
                lines.append("")
        
        return "\n".join(lines)

def main():
    """主函数"""
    print("🚀 OpenTelemetry 2025 项目自动导航更新器")
    print("=" * 50)
    
    updater = NavigationUpdater()
    documents = updater.update_navigation_files()
    
    print("\n✅ 导航更新完成!")
    print(f"📁 扫描了 {len(documents)} 个模块")
    print(f"📄 总共 {sum(updater._count_files(module_info) for module_info in documents.values())} 个文档")

if __name__ == "__main__":
    main()
