#!/usr/bin/env python3
"""
OpenTelemetry 2025 文档管理工具
用于自动化文档管理、质量检查和链接验证
"""

import os
import re
import hashlib
import yaml
import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Dict, List, Set, Tuple, Optional

class DocumentManager:
    """文档管理器"""
    
    def __init__(self, doc_root: str = "doc"):
        self.doc_root = Path(doc_root)
        self.config = self.load_config()
        self.duplicates = defaultdict(list)
        self.content_hash = {}
        self.link_issues = []
        self.quality_issues = []
    
    def load_config(self) -> Dict:
        """加载配置文件"""
        config_file = self.doc_root / "config" / "document_config.yaml"
        if config_file.exists():
            with open(config_file, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        else:
            return self.get_default_config()
    
    def get_default_config(self) -> Dict:
        """获取默认配置"""
        return {
            "document_structure": {
                "00_项目概览": ["README.md", "项目章程.md", "快速开始.md", "文档导航.md"],
                "01_理论基础": ["README.md", "数学基础.md", "形式化验证.md", "理论证明.md"],
                "02_标准规范": ["README.md", "国际标准对齐.md", "行业标准.md", "合规框架.md"],
                "03_技术架构": ["README.md", "系统架构.md", "协议实现.md", "工具链.md"],
                "04_应用实践": ["README.md", "行业解决方案.md", "部署指南.md", "最佳实践.md"],
                "05_质量保证": ["README.md", "测试框架.md", "性能基准.md", "质量监控.md"],
                "06_社区生态": ["README.md", "治理框架.md", "贡献指南.md", "学术合作.md"],
                "07_商业化": ["README.md", "商业模式.md", "市场分析.md", "发展路线.md"],
                "08_附录": ["术语表.md", "参考文献.md", "配置示例.md", "故障排除.md"]
            },
            "quality_standards": {
                "min_length": 100,
                "required_sections": ["标题", "概述", "内容", "结论"],
                "required_metadata": ["最后更新", "文档版本", "维护者"],
                "link_check": True,
                "duplicate_check": True
            },
            "exclude_patterns": [
                "*.tmp",
                "*.bak",
                "*.old",
                ".git/*",
                "node_modules/*"
            ]
        }
    
    def detect_duplicates(self) -> Dict[str, List[Path]]:
        """检测重复文档"""
        print("🔍 检测重复文档...")
        
        for md_file in self.doc_root.rglob("*.md"):
            if self.should_exclude(md_file):
                continue
                
            try:
                content = md_file.read_text(encoding='utf-8')
                content_hash = hashlib.md5(content.encode()).hexdigest()
                
                if content_hash in self.content_hash:
                    self.duplicates[content_hash].append(md_file)
                else:
                    self.content_hash[content_hash] = md_file
            except Exception as e:
                print(f"⚠️ 读取文件失败: {md_file} - {e}")
        
        return dict(self.duplicates)
    
    def should_exclude(self, file_path: Path) -> bool:
        """检查是否应该排除文件"""
        for pattern in self.config["exclude_patterns"]:
            if file_path.match(pattern):
                return True
        return False
    
    def consolidate_duplicates(self) -> Dict[str, str]:
        """整合重复文档"""
        print("🔄 整合重复文档...")
        
        consolidation_results = {}
        
        for content_hash, files in self.duplicates.items():
            if len(files) > 1:
                main_file = self.select_main_document(files)
                merged_content = self.merge_content(files)
                
                # 写入主文档
                main_file.write_text(merged_content, encoding='utf-8')
                consolidation_results[str(main_file)] = "已整合"
                
                # 删除其他重复文档
                for file in files:
                    if file != main_file:
                        file.unlink()
                        consolidation_results[str(file)] = "已删除"
                        print(f"🗑️ 删除重复文档: {file}")
        
        return consolidation_results
    
    def select_main_document(self, files: List[Path]) -> Path:
        """选择主文档"""
        # 优先级：README > 项目概览 > 其他
        for file in files:
            if file.name == "README.md":
                return file
            if "项目概览" in str(file):
                return file
        
        # 选择最完整的文档
        max_length = 0
        main_file = files[0]
        
        for file in files:
            try:
                content = file.read_text(encoding='utf-8')
                if len(content) > max_length:
                    max_length = len(content)
                    main_file = file
            except:
                continue
        
        return main_file
    
    def merge_content(self, files: List[Path]) -> str:
        """合并文档内容"""
        merged_sections = defaultdict(list)
        
        for file in files:
            try:
                content = file.read_text(encoding='utf-8')
                sections = self.parse_sections(content)
                
                for section, content in sections.items():
                    merged_sections[section].append(content)
            except:
                continue
        
        # 合并内容
        merged_content = ""
        for section, contents in merged_sections.items():
            merged_content += f"## {section}\n\n"
            for content in contents:
                merged_content += content + "\n\n"
        
        return merged_content
    
    def parse_sections(self, content: str) -> Dict[str, str]:
        """解析文档章节"""
        sections = {}
        current_section = "概述"
        current_content = []
        
        for line in content.split('\n'):
            if line.startswith('#'):
                if current_content:
                    sections[current_section] = '\n'.join(current_content)
                current_section = line.strip('#').strip()
                current_content = []
            else:
                current_content.append(line)
        
        if current_content:
            sections[current_section] = '\n'.join(current_content)
        
        return sections
    
    def check_document_quality(self) -> List[Dict]:
        """检查文档质量"""
        print("📊 检查文档质量...")
        
        quality_issues = []
        
        for md_file in self.doc_root.rglob("*.md"):
            if self.should_exclude(md_file):
                continue
            
            try:
                content = md_file.read_text(encoding='utf-8')
                issues = self.analyze_document_quality(md_file, content)
                quality_issues.extend(issues)
            except Exception as e:
                quality_issues.append({
                    "file": str(md_file),
                    "type": "读取错误",
                    "message": str(e),
                    "severity": "高"
                })
        
        return quality_issues
    
    def analyze_document_quality(self, file_path: Path, content: str) -> List[Dict]:
        """分析单个文档质量"""
        issues = []
        
        # 检查文档长度
        if len(content) < self.config["quality_standards"]["min_length"]:
            issues.append({
                "file": str(file_path),
                "type": "长度不足",
                "message": f"文档长度 {len(content)} 字符，少于最小要求 {self.config['quality_standards']['min_length']} 字符",
                "severity": "中"
            })
        
        # 检查必需章节
        required_sections = self.config["quality_standards"]["required_sections"]
        for section in required_sections:
            if section not in content:
                issues.append({
                    "file": str(file_path),
                    "type": "缺少章节",
                    "message": f"缺少必需章节: {section}",
                    "severity": "中"
                })
        
        # 检查元数据
        required_metadata = self.config["quality_standards"]["required_metadata"]
        for metadata in required_metadata:
            if metadata not in content:
                issues.append({
                    "file": str(file_path),
                    "type": "缺少元数据",
                    "message": f"缺少必需元数据: {metadata}",
                    "severity": "低"
                })
        
        # 检查链接
        if self.config["quality_standards"]["link_check"]:
            link_issues = self.check_links(file_path, content)
            issues.extend(link_issues)
        
        return issues
    
    def check_links(self, file_path: Path, content: str) -> List[Dict]:
        """检查文档链接"""
        link_issues = []
        
        # 查找所有链接
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        
        for link_text, link_url in links:
            if link_url.startswith('http'):
                # 外部链接，暂时跳过
                continue
            
            # 内部链接
            if link_url.startswith('../'):
                target_path = file_path.parent / link_url
            elif link_url.startswith('./'):
                target_path = file_path.parent / link_url
            else:
                target_path = file_path.parent / link_url
            
            if not target_path.exists():
                link_issues.append({
                    "file": str(file_path),
                    "type": "链接错误",
                    "message": f"链接 '{link_text}' 指向不存在的文件: {link_url}",
                    "severity": "高"
                })
        
        return link_issues
    
    def restructure_documents(self) -> Dict[str, str]:
        """重组文档结构"""
        print("🏗️ 重组文档结构...")
        
        restructure_results = {}
        
        # 创建新目录结构
        for new_dir in self.config["document_structure"].keys():
            target_dir = self.doc_root / new_dir
            target_dir.mkdir(exist_ok=True)
            restructure_results[new_dir] = "目录已创建"
        
        # 移动文档到对应目录
        for dir_name, expected_files in self.config["document_structure"].items():
            target_dir = self.doc_root / dir_name
            
            for expected_file in expected_files:
                target_path = target_dir / expected_file
                
                # 查找现有文件
                existing_file = self.find_existing_file(expected_file)
                
                if existing_file:
                    # 移动现有文件
                    shutil.move(str(existing_file), str(target_path))
                    restructure_results[str(target_path)] = "文件已移动"
                else:
                    # 创建新文件
                    target_path.touch()
                    restructure_results[str(target_path)] = "文件已创建"
        
        return restructure_results
    
    def find_existing_file(self, filename: str) -> Optional[Path]:
        """查找现有文件"""
        for md_file in self.doc_root.rglob(filename):
            if not self.should_exclude(md_file):
                return md_file
        return None
    
    def generate_navigation(self) -> str:
        """生成文档导航"""
        print("🧭 生成文档导航...")
        
        navigation = "# OpenTelemetry 2025 文档导航\n\n"
        navigation += f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日')}\n\n"
        
        for dir_name, files in self.config["document_structure"].items():
            navigation += f"## {dir_name}\n\n"
            
            for file in files:
                file_path = self.doc_root / dir_name / file
                if file_path.exists():
                    navigation += f"- [{file}]({dir_name}/{file})\n"
                else:
                    navigation += f"- [{file}]({dir_name}/{file}) ⚠️ 待创建\n"
            
            navigation += "\n"
        
        return navigation
    
    def generate_quality_report(self) -> str:
        """生成质量报告"""
        print("📋 生成质量报告...")
        
        report = "# OpenTelemetry 2025 文档质量报告\n\n"
        report += f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}\n\n"
        
        # 统计信息
        total_files = len(list(self.doc_root.rglob("*.md")))
        duplicate_count = sum(len(files) for files in self.duplicates.values() if len(files) > 1)
        
        report += "## 📊 统计信息\n\n"
        report += f"- **总文档数量**: {total_files}\n"
        report += f"- **重复文档数量**: {duplicate_count}\n"
        report += f"- **质量问题数量**: {len(self.quality_issues)}\n\n"
        
        # 重复文档
        if self.duplicates:
            report += "## 🔄 重复文档\n\n"
            for content_hash, files in self.duplicates.items():
                if len(files) > 1:
                    report += f"### 重复组 {content_hash[:8]}...\n\n"
                    for file in files:
                        report += f"- {file}\n"
                    report += "\n"
        
        # 质量问题
        if self.quality_issues:
            report += "## ⚠️ 质量问题\n\n"
            
            # 按严重程度分组
            severity_groups = defaultdict(list)
            for issue in self.quality_issues:
                severity_groups[issue["severity"]].append(issue)
            
            for severity in ["高", "中", "低"]:
                if severity in severity_groups:
                    report += f"### {severity}优先级问题\n\n"
                    for issue in severity_groups[severity]:
                        report += f"- **{issue['file']}**: {issue['message']}\n"
                    report += "\n"
        
        return report
    
    def run_full_analysis(self) -> Dict:
        """运行完整分析"""
        print("🚀 开始完整文档分析...")
        
        results = {
            "timestamp": datetime.now().isoformat(),
            "duplicates": self.detect_duplicates(),
            "quality_issues": self.check_document_quality(),
            "consolidation_results": {},
            "restructure_results": {},
            "navigation": "",
            "quality_report": ""
        }
        
        # 整合重复文档
        if results["duplicates"]:
            results["consolidation_results"] = self.consolidate_duplicates()
        
        # 重组文档结构
        results["restructure_results"] = self.restructure_documents()
        
        # 生成导航
        results["navigation"] = self.generate_navigation()
        
        # 生成质量报告
        results["quality_report"] = self.generate_quality_report()
        
        return results
    
    def save_results(self, results: Dict):
        """保存分析结果"""
        # 保存导航文档
        nav_file = self.doc_root / "00_项目概览" / "文档导航.md"
        nav_file.write_text(results["navigation"], encoding='utf-8')
        
        # 保存质量报告
        report_file = self.doc_root / "质量报告.md"
        report_file.write_text(results["quality_report"], encoding='utf-8')
        
        # 保存JSON结果
        json_file = self.doc_root / "分析结果.json"
        with open(json_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, ensure_ascii=False, indent=2)
        
        print(f"📁 结果已保存到:")
        print(f"  - 导航文档: {nav_file}")
        print(f"  - 质量报告: {report_file}")
        print(f"  - JSON结果: {json_file}")

def main():
    """主函数"""
    print("🎯 OpenTelemetry 2025 文档管理工具")
    print("=" * 50)
    
    # 创建文档管理器
    manager = DocumentManager()
    
    # 运行完整分析
    results = manager.run_full_analysis()
    
    # 保存结果
    manager.save_results(results)
    
    # 输出摘要
    print("\n📊 分析摘要:")
    print(f"  - 重复文档组: {len(results['duplicates'])}")
    print(f"  - 质量问题: {len(results['quality_issues'])}")
    print(f"  - 整合文档: {len(results['consolidation_results'])}")
    print(f"  - 重组目录: {len(results['restructure_results'])}")
    
    print("\n✅ 文档管理完成!")

if __name__ == "__main__":
    main()
