#!/usr/bin/env python3
"""
OpenTelemetry 2025 智能文档管理系统
自动维护文档结构、生成目录、更新导航
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import yaml
from datetime import datetime
import hashlib

class SmartDocumentManager:
    def __init__(self, doc_root: str = "doc"):
        # 获取脚本所在目录的父目录作为项目根目录
        script_dir = Path(__file__).parent
        project_root = script_dir.parent
        self.doc_root = project_root / doc_root
        self.cache_file = script_dir / ".document_cache.json"
        self.config_file = script_dir / "document_config.yaml"
        self.load_config()
        self.load_cache()
        
    def load_config(self):
        """加载配置"""
        default_config = {
            "auto_update": True,
            "generate_toc": True,
            "update_navigation": True,
            "backup_changes": True,
            "exclude_patterns": [
                "*.tmp",
                "*.bak",
                ".git/*",
                "node_modules/*"
            ],
            "module_mapping": {
                "00_项目概览与导航": "项目概览",
                "01_理论基础与形式化证明": "理论基础",
                "02_OTLP标准深度分析": "标准分析",
                "03_行业标准与最佳实践": "最佳实践",
                "04_形式论证与证明体系": "形式论证",
                "05_批判性分析与评价": "批判分析",
                "06_学术研究与理论创新": "学术研究",
                "07_实施指南与操作手册": "实施指南",
                "08_可持续发展计划": "可持续发展",
                "09_附录与参考资料": "参考资料"
            }
        }
        
        if self.config_file.exists():
            try:
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    self.config = yaml.safe_load(f)
            except:
                self.config = default_config
        else:
            self.config = default_config
            self.save_config()
    
    def save_config(self):
        """保存配置"""
        with open(self.config_file, 'w', encoding='utf-8') as f:
            yaml.dump(self.config, f, default_flow_style=False, allow_unicode=True)
    
    def load_cache(self):
        """加载缓存"""
        if self.cache_file.exists():
            try:
                with open(self.cache_file, 'r', encoding='utf-8') as f:
                    self.cache = json.load(f)
            except:
                self.cache = {"files": {}, "last_scan": None}
        else:
            self.cache = {"files": {}, "last_scan": None}
    
    def save_cache(self):
        """保存缓存"""
        with open(self.cache_file, 'w', encoding='utf-8') as f:
            json.dump(self.cache, f, ensure_ascii=False, indent=2)
    
    def get_file_hash(self, file_path: Path) -> str:
        """获取文件哈希值"""
        try:
            with open(file_path, 'rb') as f:
                return hashlib.md5(f.read()).hexdigest()
        except:
            return ""
    
    def scan_documents(self) -> Dict:
        """扫描文档结构"""
        print("🔍 扫描文档结构...")
        documents = {}
        changed_files = []
        
        for item in sorted(self.doc_root.iterdir()):
            if item.is_dir() and not item.name.startswith('.'):
                module_info = self._scan_module(item)
                documents[item.name] = module_info
                
                # 检查文件变化
                for file_info in module_info.get('files', []):
                    file_path = Path(file_info['path'])
                    current_hash = self.get_file_hash(file_path)
                    cached_hash = self.cache.get('files', {}).get(str(file_path), '')
                    
                    if current_hash != cached_hash:
                        changed_files.append(str(file_path))
                        self.cache['files'][str(file_path)] = current_hash
        
        self.cache['last_scan'] = datetime.now().isoformat()
        self.save_cache()
        
        print(f"📁 扫描了 {len(documents)} 个模块")
        print(f"🔄 发现 {len(changed_files)} 个文件有变化")
        
        return documents, changed_files
    
    def _scan_module(self, module_path: Path) -> Dict:
        """扫描模块"""
        module_info = {
            'name': module_path.name,
            'display_name': self.config['module_mapping'].get(module_path.name, module_path.name),
            'files': [],
            'submodules': {},
            'readme': None,
            'stats': {
                'total_files': 0,
                'total_size': 0,
                'last_modified': None
            }
        }
        
        for item in sorted(module_path.iterdir()):
            if item.is_file() and item.suffix == '.md':
                file_info = self._analyze_file(item)
                module_info['files'].append(file_info)
                module_info['stats']['total_files'] += 1
                module_info['stats']['total_size'] += file_info['size']
                
                if item.name.lower() in ['readme.md', 'index.md']:
                    module_info['readme'] = file_info
                    
            elif item.is_dir() and not item.name.startswith('.'):
                submodule_info = self._scan_module(item)
                module_info['submodules'][item.name] = submodule_info
                module_info['stats']['total_files'] += submodule_info['stats']['total_files']
                module_info['stats']['total_size'] += submodule_info['stats']['total_size']
        
        return module_info
    
    def _analyze_file(self, file_path: Path) -> Dict:
        """分析文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 提取元数据
            title = self._extract_title(content, file_path)
            created_time = self._extract_metadata(content, '创建时间')
            version = self._extract_metadata(content, '文档版本')
            status = self._extract_metadata(content, '状态')
            maintainer = self._extract_metadata(content, '维护者')
            
            # 分析内容
            word_count = len(content.split())
            line_count = len(content.splitlines())
            
            return {
                'name': file_path.name,
                'path': str(file_path.relative_to(self.doc_root)),
                'title': title,
                'created_time': created_time or "未知",
                'version': version or "1.0.0",
                'status': status or "活跃",
                'maintainer': maintainer or "未知",
                'size': file_path.stat().st_size,
                'word_count': word_count,
                'line_count': line_count,
                'modified': datetime.fromtimestamp(file_path.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S'),
                'hash': self.get_file_hash(file_path)
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
                'maintainer': "未知",
                'size': 0,
                'word_count': 0,
                'line_count': 0,
                'modified': "未知",
                'hash': ""
            }
    
    def _extract_title(self, content: str, file_path: Path) -> str:
        """提取标题"""
        # 尝试提取第一个一级标题
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if title_match:
            return title_match.group(1).strip()
        
        # 尝试提取第一个二级标题
        title_match = re.search(r'^##\s+(.+)$', content, re.MULTILINE)
        if title_match:
            return title_match.group(1).strip()
        
        return file_path.stem
    
    def _extract_metadata(self, content: str, key: str) -> Optional[str]:
        """提取元数据"""
        pattern = rf'\*\*{re.escape(key)}\*\*:\s*(.+)'
        match = re.search(pattern, content)
        return match.group(1).strip() if match else None
    
    def generate_comprehensive_toc(self, documents: Dict) -> str:
        """生成综合目录"""
        lines = [
            "# OpenTelemetry 2025 知识理论模型分析梳理项目完整目录",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            f"**文档版本**: 2.0.0",
            f"**维护者**: OpenTelemetry 2025 智能文档管理系统",
            f"**状态**: 知识理论模型分析梳理项目",
            f"**目录范围**: 完整文档体系目录",
            "",
            "## 🎯 目录概览",
            "",
            "### 项目统计",
            ""
        ]
        
        # 统计信息
        total_modules = len(documents)
        total_files = sum(module['stats']['total_files'] for module in documents.values())
        total_size = sum(module['stats']['total_size'] for module in documents.values())
        
        lines.extend([
            f"- **总模块数**: {total_modules}",
            f"- **总文档数**: {total_files}",
            f"- **总大小**: {total_size / 1024 / 1024:.1f} MB",
            f"- **平均每模块文档数**: {total_files / total_modules:.1f}",
            "",
            "### 模块概览",
            ""
        ])
        
        # 模块概览
        for module_name, module_info in documents.items():
            display_name = module_info['display_name']
            file_count = module_info['stats']['total_files']
            size_mb = module_info['stats']['total_size'] / 1024 / 1024
            lines.append(f"- **{display_name}** ({module_name}) - {file_count} 个文档 ({size_mb:.1f} MB)")
        
        lines.extend([
            "",
            "## 📚 详细目录结构",
            ""
        ])
        
        # 详细目录
        for module_name, module_info in documents.items():
            lines.extend(self._generate_module_toc(module_name, module_info, 0))
        
        # 添加快速导航
        lines.extend(self._generate_quick_navigation(documents))
        
        return "\n".join(lines)
    
    def _generate_module_toc(self, name: str, module_info: Dict, level: int) -> List[str]:
        """生成模块目录"""
        lines = []
        indent = "  " * level
        
        # 模块标题
        if level == 0:
            display_name = module_info['display_name']
            lines.append(f"### {display_name} ({name})")
            lines.append("")
            
            # 模块统计
            stats = module_info['stats']
            lines.append(f"**模块统计**: {stats['total_files']} 个文档, {stats['total_size'] / 1024 / 1024:.1f} MB")
            lines.append("")
        else:
            lines.append(f"{indent}- **{name}**")
            lines.append("")
        
        # README文件
        if module_info.get('readme'):
            readme = module_info['readme']
            lines.append(f"{indent}  - 📖 [{readme['title']}]({readme['path']}) - 模块入口")
            lines.append("")
        
        # 主要文档
        main_files = [f for f in module_info.get('files', []) 
                     if f != module_info.get('readme') and 
                     not any(keyword in f['name'].lower() 
                            for keyword in ['readme', 'index', 'toc', 'summary'])]
        
        if main_files:
            lines.append(f"{indent}  **核心文档**:")
            for file_info in main_files:
                lines.append(f"{indent}  - [{file_info['title']}]({file_info['path']})")
            lines.append("")
        
        # 子模块
        for submodule_name, submodule_info in module_info.get('submodules', {}).items():
            lines.extend(self._generate_module_toc(submodule_name, submodule_info, level + 1))
        
        return lines
    
    def _generate_quick_navigation(self, documents: Dict) -> List[str]:
        """生成快速导航"""
        lines = [
            "## 🗺️ 快速导航",
            "",
            "### 按主题导航",
            ""
        ]
        
        # 按主题分类
        theme_mapping = {
            "📋 项目概览": ["00_项目概览与导航"],
            "🧮 理论基础": ["01_理论基础与形式化证明", "04_形式论证与证明体系"],
            "📊 标准分析": ["02_OTLP标准深度分析", "03_行业标准与最佳实践"],
            "🔬 学术研究": ["06_学术研究与理论创新"],
            "🔍 批判分析": ["05_批判性分析与评价"],
            "🛠️ 实施指南": ["07_实施指南与操作手册"],
            "🌱 可持续发展": ["08_可持续发展计划"],
            "📚 参考资料": ["09_附录与参考资料"]
        }
        
        for theme, modules in theme_mapping.items():
            lines.append(f"#### {theme}")
            for module in modules:
                if module in documents:
                    module_info = documents[module]
                    display_name = module_info['display_name']
                    file_count = module_info['stats']['total_files']
                    lines.append(f"- [{display_name}]({module}/) - {file_count} 个文档")
            lines.append("")
        
        lines.extend([
            "### 按用户类型导航",
            "",
            "#### 👨‍🔬 研究人员",
            "- [理论基础与形式化证明](01_理论基础与形式化证明/)",
            "- [学术研究与理论创新](06_学术研究与理论创新/)",
            "- [批判性分析与评价](05_批判性分析与评价/)",
            "",
            "#### 👨‍💻 工程师",
            "- [OTLP标准深度分析](02_OTLP标准深度分析/)",
            "- [实施指南与操作手册](07_实施指南与操作手册/)",
            "- [行业标准与最佳实践](03_行业标准与最佳实践/)",
            "",
            "#### 👨‍💼 管理者",
            "- [项目概览与导航](00_项目概览与导航/)",
            "- [可持续发展计划](08_可持续发展计划/)",
            "- [附录与参考资料](09_附录与参考资料/)",
            "",
            "---",
            "",
            f"**目录生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            f"**目录版本**: 2.0.0",
            f"**维护者**: OpenTelemetry 2025 智能文档管理系统",
            f"**下次自动更新**: {(datetime.now().replace(day=datetime.now().day+1)).strftime('%Y年%m月%d日')}"
        ])
        
        return lines
    
    def update_navigation_file(self, documents: Dict):
        """更新主导航文件"""
        nav_file = self.doc_root / "00_项目概览与导航" / "文档导航与索引.md"
        
        if not nav_file.exists():
            print(f"⚠️ 导航文件不存在: {nav_file}")
            return
        
        # 生成新的导航内容
        nav_content = self.generate_navigation_content(documents)
        
        # 备份原文件
        if self.config.get('backup_changes', True):
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            backup_file = nav_file.with_suffix(f'.md.backup_{timestamp}')
            if backup_file.exists():
                backup_file.unlink()
            nav_file.rename(backup_file)
            print(f"📦 已备份原文件: {backup_file}")
        
        # 写入新内容
        with open(nav_file, 'w', encoding='utf-8') as f:
            f.write(nav_content)
        
        print(f"✅ 已更新导航文件: {nav_file}")
    
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
        lines.extend(self._generate_navigation_statistics(documents))
        
        return "\n".join(lines)
    
    def _generate_module_navigation(self, module_name: str, module_info: Dict) -> List[str]:
        """生成模块导航"""
        lines = []
        display_name = module_info['display_name']
        
        # 模块标题
        lines.append(f"### {display_name}")
        lines.append("")
        
        # 模块描述
        if module_info.get('readme'):
            readme = module_info['readme']
            lines.append(f"**模块入口**: [{readme['title']}]({readme['path']})")
            lines.append("")
        
        # 主要文档
        main_files = [f for f in module_info.get('files', []) 
                     if f != module_info.get('readme') and 
                     not any(keyword in f['name'].lower() 
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
    
    def _generate_navigation_statistics(self, documents: Dict) -> List[str]:
        """生成导航统计信息"""
        lines = [
            "## 📊 文档统计",
            "",
            "### 总体统计",
            ""
        ]
        
        total_modules = len(documents)
        total_files = sum(module['stats']['total_files'] for module in documents.values())
        total_size = sum(module['stats']['total_size'] for module in documents.values())
        
        lines.extend([
            f"- **总模块数**: {total_modules}",
            f"- **总文档数**: {total_files}",
            f"- **总大小**: {total_size / 1024 / 1024:.1f} MB",
            f"- **最后更新**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}",
            "",
            "### 模块统计",
            ""
        ])
        
        for module_name, module_info in documents.items():
            display_name = module_info['display_name']
            file_count = module_info['stats']['total_files']
            size_mb = module_info['stats']['total_size'] / 1024 / 1024
            lines.append(f"- **{display_name}**: {file_count} 个文档 ({size_mb:.1f} MB)")
        
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
    
    def _generate_theme_links(self, documents: Dict) -> List[str]:
        """生成主题链接"""
        theme_mapping = {
            "理论基础": ["01_理论基础与形式化证明", "04_形式论证与证明体系"],
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
                    module_info = documents[module]
                    display_name = module_info['display_name']
                    lines.append(f"- [{display_name}]({module}/)")
            lines.append("")
        
        return lines
    
    def generate_statistics_report(self, documents: Dict) -> str:
        """生成统计报告"""
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
        total_files = sum(module['stats']['total_files'] for module in documents.values())
        total_size = sum(module['stats']['total_size'] for module in documents.values())
        
        lines.extend([
            f"- **总模块数**: {total_modules}",
            f"- **总文档数**: {total_files}",
            f"- **总大小**: {total_size / 1024 / 1024:.1f} MB",
            f"- **平均每模块文档数**: {total_files / total_modules:.1f}",
            f"- **平均文档大小**: {total_size / total_files / 1024:.1f} KB",
            "",
            "## 📁 模块详细统计",
            ""
        ])
        
        for module_name, module_info in documents.items():
            display_name = module_info['display_name']
            stats = module_info['stats']
            submodule_count = len(module_info.get('submodules', {}))
            
            lines.extend([
                f"### {display_name} ({module_name})",
                f"- **文档数量**: {stats['total_files']}",
                f"- **子模块数量**: {submodule_count}",
                f"- **总大小**: {stats['total_size'] / 1024 / 1024:.1f} MB",
                ""
            ])
            
            # 列出主要文档
            main_files = module_info.get('files', [])[:5]
            if main_files:
                lines.append("**主要文档**:")
                for file_info in main_files:
                    size_kb = file_info['size'] / 1024
                    lines.append(f"- [{file_info['title']}]({file_info['path']}) ({size_kb:.1f} KB)")
                lines.append("")
        
        return "\n".join(lines)
    
    def run_full_update(self):
        """运行完整更新"""
        print("🚀 OpenTelemetry 2025 智能文档管理系统")
        print("=" * 60)
        print(f"开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        # 扫描文档
        documents, changed_files = self.scan_documents()
        
        if not documents:
            print("❌ 未找到任何文档")
            return
        
        # 生成目录
        if self.config.get('generate_toc', True):
            print("\n📝 生成完整目录...")
            toc_content = self.generate_comprehensive_toc(documents)
            
            toc_file = self.doc_root / "00_项目概览与导航" / "自动生成完整目录.md"
            with open(toc_file, 'w', encoding='utf-8') as f:
                f.write(toc_content)
            print(f"✅ 已生成完整目录: {toc_file}")
        
        # 更新导航
        if self.config.get('update_navigation', True):
            print("\n🗺️ 更新导航文件...")
            self.update_navigation_file(documents)
        
        # 生成统计报告
        print("\n📊 生成统计报告...")
        stats_content = self.generate_statistics_report(documents)
        
        stats_file = self.doc_root / "00_项目概览与导航" / "文档统计报告.md"
        with open(stats_file, 'w', encoding='utf-8') as f:
            f.write(stats_content)
        print(f"✅ 已生成统计报告: {stats_file}")
        
        print("\n" + "=" * 60)
        print("📊 执行结果汇总")
        print(f"✅ 扫描模块: {len(documents)}")
        print(f"📄 总文档数: {sum(module['stats']['total_files'] for module in documents.values())}")
        print(f"🔄 变化文件: {len(changed_files)}")
        print(f"📁 总大小: {sum(module['stats']['total_size'] for module in documents.values()) / 1024 / 1024:.1f} MB")
        
        print("\n🎉 智能文档管理完成!")
        print(f"结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

def main():
    """主函数"""
    manager = SmartDocumentManager()
    manager.run_full_update()

if __name__ == "__main__":
    main()
