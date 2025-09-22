#!/usr/bin/env python3
"""
OpenTelemetry 2025 自动文档更新器
检测文档变化并自动更新相关内容
"""

import os
import re
import json
import shutil
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import yaml
from datetime import datetime
import hashlib
import difflib

class AutoDocumentUpdater:
    def __init__(self, doc_root: str = "doc"):
        # 获取脚本所在目录的父目录作为项目根目录
        script_dir = Path(__file__).parent
        project_root = script_dir.parent
        self.doc_root = project_root / doc_root
        self.cache_file = script_dir / ".document_cache.json"
        self.backup_dir = script_dir / "backups"
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        # 文档模板
        self.templates = {
            "standard_doc": {
                "header": """# {title}

## 📊 {title}概览

**创建时间**: {created_time}  
**文档版本**: {version}  
**维护者**: {maintainer}  
**状态**: {status}  
**{title}范围**: {scope}

## 🎯 {title}目标

### 主要目标

1. **目标1**: {goal1}
2. **目标2**: {goal2}
3. **目标3**: {goal3}
4. **目标4**: {goal4}
5. **目标5**: {goal5}

### 成功标准

- **标准1**: {standard1}
- **标准2**: {standard2}
- **标准3**: {standard3}
- **标准4**: {standard4}
- **标准5**: {standard5}
""",
                "footer": """
## 📚 总结

{title}为OpenTelemetry 2025知识理论模型分析梳理项目提供了重要的{value}，通过系统性的{approach}，确保了{quality}。

### 主要贡献

1. **贡献1**: {contribution1}
2. **贡献2**: {contribution2}
3. **贡献3**: {contribution3}
4. **贡献4**: {contribution4}
5. **贡献5**: {contribution5}

### 技术价值

1. **价值1**: {value1}
2. **价值2**: {value2}
3. **价值3**: {value3}
4. **价值4**: {value4}

### 应用指导

1. **指导1**: {guidance1}
2. **指导2**: {guidance2}
3. **指导3**: {guidance3}
4. **指导4**: {guidance4}

{title}为OTLP标准的{impact}提供了重要的技术支撑。

---

**文档创建完成时间**: {created_time}  
**文档版本**: {version}  
**维护者**: {maintainer}  
**下次审查**: {next_review}
"""
            }
        }
        
        self.load_cache()
    
    def load_cache(self):
        """加载缓存"""
        if self.cache_file.exists():
            try:
                with open(self.cache_file, 'r', encoding='utf-8') as f:
                    self.cache = json.load(f)
            except:
                self.cache = {"files": {}, "last_scan": None, "backups": []}
        else:
            self.cache = {"files": {}, "last_scan": None, "backups": []}
    
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
    
    def backup_file(self, file_path: Path) -> Path:
        """备份文件"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup_name = f"{file_path.stem}_{timestamp}{file_path.suffix}"
        backup_path = self.backup_dir / backup_name
        
        shutil.copy2(file_path, backup_path)
        
        # 记录备份
        self.cache["backups"].append({
            "original": str(file_path),
            "backup": str(backup_path),
            "timestamp": timestamp,
            "size": file_path.stat().st_size
        })
        
        # 保持最近10个备份
        if len(self.cache["backups"]) > 10:
            old_backup = self.cache["backups"].pop(0)
            old_backup_path = Path(old_backup["backup"])
            if old_backup_path.exists():
                old_backup_path.unlink()
        
        return backup_path
    
    def detect_changes(self) -> List[Tuple[Path, str, str]]:
        """检测文件变化"""
        changes = []
        
        for md_file in self.doc_root.rglob("*.md"):
            current_hash = self.get_file_hash(md_file)
            cached_hash = self.cache.get("files", {}).get(str(md_file), "")
            
            if current_hash != cached_hash:
                changes.append((md_file, cached_hash, current_hash))
                self.cache["files"][str(md_file)] = current_hash
        
        self.cache["last_scan"] = datetime.now().isoformat()
        self.save_cache()
        
        return changes
    
    def analyze_document_structure(self, file_path: Path) -> Dict:
        """分析文档结构"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 提取标题
            title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
            title = title_match.group(1).strip() if title_match else file_path.stem
            
            # 提取元数据
            metadata = {
                'title': title,
                'created_time': self._extract_metadata(content, '创建时间'),
                'version': self._extract_metadata(content, '文档版本'),
                'maintainer': self._extract_metadata(content, '维护者'),
                'status': self._extract_metadata(content, '状态'),
                'scope': self._extract_metadata(content, '范围') or self._extract_metadata(content, '分析范围'),
            }
            
            # 分析结构完整性
            structure_analysis = {
                'has_header': bool(re.search(r'^#\s+', content, re.MULTILINE)),
                'has_overview': bool(re.search(r'##\s+.*概览', content)),
                'has_goals': bool(re.search(r'##\s+.*目标', content)),
                'has_summary': bool(re.search(r'##\s+.*总结', content)),
                'has_footer': bool(re.search(r'---\s*$', content, re.MULTILINE)),
                'section_count': len(re.findall(r'^##\s+', content, re.MULTILINE)),
                'subsection_count': len(re.findall(r'^###\s+', content, re.MULTILINE)),
            }
            
            return {
                'metadata': metadata,
                'structure': structure_analysis,
                'content_length': len(content),
                'line_count': len(content.splitlines())
            }
            
        except Exception as e:
            print(f"警告: 无法分析文档 {file_path}: {e}")
            return {}
    
    def _extract_metadata(self, content: str, key: str) -> Optional[str]:
        """提取元数据"""
        pattern = rf'\*\*{re.escape(key)}\*\*:\s*(.+)'
        match = re.search(pattern, content)
        return match.group(1).strip() if match else None
    
    def fix_document_structure(self, file_path: Path, analysis: Dict) -> bool:
        """修复文档结构"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 备份原文件
            self.backup_file(file_path)
            
            # 修复标题
            if not analysis['structure']['has_header']:
                title = analysis['metadata']['title']
                content = f"# {title}\n\n{content}"
            
            # 修复概览部分
            if not analysis['structure']['has_overview']:
                overview = self._generate_overview_section(analysis['metadata'])
                content = self._insert_section(content, overview, after_title=True)
            
            # 修复目标部分
            if not analysis['structure']['has_goals']:
                goals = self._generate_goals_section(analysis['metadata'])
                content = self._insert_section(content, goals, after_overview=True)
            
            # 修复总结部分
            if not analysis['structure']['has_summary']:
                summary = self._generate_summary_section(analysis['metadata'])
                content = self._insert_section(content, summary, before_footer=True)
            
            # 修复页脚
            if not analysis['structure']['has_footer']:
                footer = self._generate_footer_section(analysis['metadata'])
                content += f"\n{footer}"
            
            # 写回文件
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            return True
            
        except Exception as e:
            print(f"错误: 修复文档 {file_path} 失败: {e}")
            return False
    
    def _generate_overview_section(self, metadata: Dict) -> str:
        """生成概览部分"""
        title = metadata['title']
        created_time = metadata['created_time'] or datetime.now().strftime('%Y年%m月%d日')
        version = metadata['version'] or "2.0.0"
        maintainer = metadata['maintainer'] or "OpenTelemetry 2025 团队"
        status = metadata['status'] or "知识理论模型分析梳理项目"
        scope = metadata['scope'] or f"{title}分析"
        
        return f"""## 📊 {title}概览

**创建时间**: {created_time}  
**文档版本**: {version}  
**维护者**: {maintainer}  
**状态**: {status}  
**{title}范围**: {scope}

"""
    
    def _generate_goals_section(self, metadata: Dict) -> str:
        """生成目标部分"""
        title = metadata['title']
        
        return f"""## 🎯 {title}目标

### 主要目标

1. **目标1**: 实现{title}的核心功能
2. **目标2**: 确保{title}的质量和可靠性
3. **目标3**: 提供{title}的完整解决方案
4. **目标4**: 建立{title}的最佳实践
5. **目标5**: 推动{title}的持续改进

### 成功标准

- **标准1**: 100%功能实现
- **标准2**: 高质量标准达成
- **标准3**: 完整解决方案提供
- **标准4**: 最佳实践建立
- **标准5**: 持续改进机制

"""
    
    def _generate_summary_section(self, metadata: Dict) -> str:
        """生成总结部分"""
        title = metadata['title']
        
        return f"""## 📚 总结

{title}为OpenTelemetry 2025知识理论模型分析梳理项目提供了重要的技术支撑，通过系统性的分析和研究，确保了项目的质量和可靠性。

### 主要贡献

1. **贡献1**: 提供了完整的{title}解决方案
2. **贡献2**: 建立了{title}的最佳实践
3. **贡献3**: 推动了{title}的技术创新
4. **贡献4**: 确保了{title}的质量标准
5. **贡献5**: 建立了{title}的持续改进机制

### 技术价值

1. **理论价值**: 为{title}提供理论基础
2. **实践价值**: 为实际应用提供指导
3. **创新价值**: 推动{title}技术创新
4. **质量价值**: 为{title}质量提供保证

### 应用指导

1. **实施指导**: 为{title}实施提供详细指导
2. **优化指导**: 为{title}优化提供策略方法
3. **维护指导**: 为{title}维护提供最佳实践
4. **扩展指导**: 为{title}扩展提供方向建议

{title}为OTLP标准的成功应用提供了重要的技术支撑。

"""
    
    def _generate_footer_section(self, metadata: Dict) -> str:
        """生成页脚部分"""
        created_time = metadata['created_time'] or datetime.now().strftime('%Y年%m月%d日')
        version = metadata['version'] or "2.0.0"
        maintainer = metadata['maintainer'] or "OpenTelemetry 2025 团队"
        next_review = (datetime.now().replace(month=datetime.now().month+1) if datetime.now().month < 12 
                      else datetime.now().replace(year=datetime.now().year+1, month=1)).strftime('%Y年%m月%d日')
        
        return f"""---

**文档创建完成时间**: {created_time}  
**文档版本**: {version}  
**维护者**: {maintainer}  
**下次审查**: {next_review}
"""
    
    def _insert_section(self, content: str, section: str, after_title: bool = False, 
                       after_overview: bool = False, before_footer: bool = False) -> str:
        """插入章节"""
        lines = content.splitlines()
        
        if after_title:
            # 在第一个标题后插入
            for i, line in enumerate(lines):
                if line.startswith('# '):
                    lines.insert(i + 1, "")
                    lines.insert(i + 2, section.strip())
                    break
        elif after_overview:
            # 在概览章节后插入
            for i, line in enumerate(lines):
                if '概览' in line and line.startswith('##'):
                    # 找到概览章节的结束位置
                    j = i + 1
                    while j < len(lines) and not (lines[j].startswith('##') and not lines[j].startswith('###')):
                        j += 1
                    lines.insert(j, "")
                    lines.insert(j + 1, section.strip())
                    break
        elif before_footer:
            # 在页脚前插入
            for i, line in enumerate(lines):
                if line.strip() == '---':
                    lines.insert(i, "")
                    lines.insert(i + 1, section.strip())
                    break
        
        return '\n'.join(lines)
    
    def update_cross_references(self, changed_files: List[Path]):
        """更新交叉引用"""
        print("🔗 更新交叉引用...")
        
        # 扫描所有文档，建立引用关系
        all_documents = {}
        for md_file in self.doc_root.rglob("*.md"):
            analysis = self.analyze_document_structure(md_file)
            if analysis:
                all_documents[str(md_file)] = analysis
        
        # 为每个变化的文件更新引用
        for changed_file in changed_files:
            self._update_file_references(changed_file, all_documents)
    
    def _update_file_references(self, file_path: Path, all_documents: Dict):
        """更新文件引用"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 查找可能的引用
            references = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
            
            updated = False
            for ref_text, ref_path in references:
                if ref_path.endswith('.md'):
                    # 检查引用路径是否存在
                    ref_file = self.doc_root / ref_path
                    if not ref_file.exists():
                        # 尝试找到正确的路径
                        correct_path = self._find_correct_path(ref_path, all_documents)
                        if correct_path:
                            # 更新引用
                            old_ref = f"[{ref_text}]({ref_path})"
                            new_ref = f"[{ref_text}]({correct_path})"
                            content = content.replace(old_ref, new_ref)
                            updated = True
            
            if updated:
                # 备份并保存
                self.backup_file(file_path)
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                print(f"✅ 已更新引用: {file_path}")
                
        except Exception as e:
            print(f"警告: 更新引用失败 {file_path}: {e}")
    
    def _find_correct_path(self, ref_path: str, all_documents: Dict) -> Optional[str]:
        """查找正确的引用路径"""
        ref_name = Path(ref_path).name
        
        for doc_path, doc_info in all_documents.items():
            if Path(doc_path).name == ref_name:
                # 计算相对路径
                return str(Path(doc_path).relative_to(self.doc_root))
        
        return None
    
    def run_auto_update(self):
        """运行自动更新"""
        print("🚀 OpenTelemetry 2025 自动文档更新器")
        print("=" * 60)
        print(f"开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        # 检测变化
        print("\n🔍 检测文档变化...")
        changes = self.detect_changes()
        
        if not changes:
            print("✅ 没有检测到文档变化")
            return
        
        print(f"🔄 发现 {len(changes)} 个文件有变化")
        
        # 处理每个变化的文件
        fixed_count = 0
        for file_path, old_hash, new_hash in changes:
            print(f"\n📝 处理文件: {file_path}")
            
            # 分析文档结构
            analysis = self.analyze_document_structure(file_path)
            if not analysis:
                continue
            
            # 检查结构完整性
            structure = analysis['structure']
            needs_fix = not all([
                structure['has_header'],
                structure['has_overview'],
                structure['has_goals'],
                structure['has_summary'],
                structure['has_footer']
            ])
            
            if needs_fix:
                print(f"🔧 修复文档结构: {file_path}")
                if self.fix_document_structure(file_path, analysis):
                    fixed_count += 1
                    print(f"✅ 已修复: {file_path}")
                else:
                    print(f"❌ 修复失败: {file_path}")
            else:
                print(f"✅ 结构完整: {file_path}")
        
        # 更新交叉引用
        changed_files = [file_path for file_path, _, _ in changes]
        self.update_cross_references(changed_files)
        
        print("\n" + "=" * 60)
        print("📊 执行结果汇总")
        print(f"🔄 变化文件: {len(changes)}")
        print(f"🔧 修复文件: {fixed_count}")
        print(f"📦 备份文件: {len(self.cache['backups'])}")
        
        print("\n🎉 自动文档更新完成!")
        print(f"结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

def main():
    """主函数"""
    updater = AutoDocumentUpdater()
    updater.run_auto_update()

if __name__ == "__main__":
    main()
