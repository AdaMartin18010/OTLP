#!/usr/bin/env python3
"""
OpenTelemetry 2025 文档质量检查工具

功能：
- 检查文档格式一致性
- 验证链接有效性
- 检查元数据完整性
- 生成质量报告
"""

import os
import re
import json
import yaml
import hashlib
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from datetime import datetime
import argparse
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class DocumentIssue:
    """文档问题"""
    file_path: str
    line_number: int
    issue_type: str
    severity: str
    message: str
    suggestion: Optional[str] = None

@dataclass
class DocumentStats:
    """文档统计信息"""
    total_files: int
    total_lines: int
    total_size: int
    issues_count: int
    issues_by_type: Dict[str, int]
    issues_by_severity: Dict[str, int]

@dataclass
class QualityReport:
    """质量报告"""
    timestamp: str
    total_files: int
    total_issues: int
    issues: List[DocumentIssue]
    stats: DocumentStats
    quality_score: float

class DocumentQualityChecker:
    """文档质量检查器"""
    
    def __init__(self, doc_root: str = "doc"):
        self.doc_root = Path(doc_root)
        self.issues: List[DocumentIssue] = []
        self.required_metadata = [
            "创建时间", "文档版本", "维护者", "状态"
        ]
        self.required_sections = [
            "概述", "目标", "内容", "总结"
        ]
        self.emoji_patterns = {
            "📊": "概述、统计、数据",
            "🎯": "目标、目的、愿景",
            "📋": "内容、列表、清单",
            "🏗️": "架构、结构、设计",
            "🔧": "工具、技术、实现",
            "📈": "进展、趋势、分析",
            "🌟": "特色、亮点、优势",
            "🚀": "发展、未来、创新",
            "📚": "参考、资源、文档",
            "📞": "联系、支持、帮助"
        }
    
    def check_all_documents(self) -> QualityReport:
        """检查所有文档"""
        logger.info("开始检查所有文档...")
        
        md_files = list(self.doc_root.rglob("*.md"))
        logger.info(f"找到 {len(md_files)} 个Markdown文件")
        
        for md_file in md_files:
            self._check_single_document(md_file)
        
        return self._generate_report(md_files)
    
    def _check_single_document(self, file_path: Path):
        """检查单个文档"""
        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            # 检查基本格式
            self._check_basic_format(file_path, content, lines)
            
            # 检查元数据
            self._check_metadata(file_path, content)
            
            # 检查结构
            self._check_structure(file_path, content)
            
            # 检查链接
            self._check_links(file_path, content)
            
            # 检查格式一致性
            self._check_format_consistency(file_path, content, lines)
            
        except Exception as e:
            self.issues.append(DocumentIssue(
                file_path=str(file_path),
                line_number=0,
                issue_type="文件读取错误",
                severity="error",
                message=f"无法读取文件: {e}"
            ))
    
    def _check_basic_format(self, file_path: Path, content: str, lines: List[str]):
        """检查基本格式"""
        # 检查文件是否以一级标题开始
        if not content.strip().startswith('#'):
            self.issues.append(DocumentIssue(
                file_path=str(file_path),
                line_number=1,
                issue_type="格式错误",
                severity="warning",
                message="文档应该以一级标题开始",
                suggestion="在文档开头添加一级标题"
            ))
        
        # 检查文件是否以单个换行符结束
        if not content.endswith('\n'):
            self.issues.append(DocumentIssue(
                file_path=str(file_path),
                line_number=len(lines),
                issue_type="格式错误",
                severity="warning",
                message="文件应该以单个换行符结束",
                suggestion="在文件末尾添加换行符"
            ))
        
        # 检查标题格式
        for i, line in enumerate(lines, 1):
            if line.strip().startswith('#'):
                # 检查标题前后是否有空行
                if i > 1 and lines[i-2].strip() != '':
                    self.issues.append(DocumentIssue(
                        file_path=str(file_path),
                        line_number=i,
                        issue_type="格式错误",
                        severity="warning",
                        message="标题前应该有空行",
                        suggestion="在标题前添加空行"
                    ))
                
                if i < len(lines) and lines[i].strip() != '':
                    self.issues.append(DocumentIssue(
                        file_path=str(file_path),
                        line_number=i,
                        issue_type="格式错误",
                        severity="warning",
                        message="标题后应该有空行",
                        suggestion="在标题后添加空行"
                    ))
    
    def _check_metadata(self, file_path: Path, content: str):
        """检查元数据"""
        for metadata in self.required_metadata:
            if metadata not in content:
                self.issues.append(DocumentIssue(
                    file_path=str(file_path),
                    line_number=0,
                    issue_type="元数据缺失",
                    severity="warning",
                    message=f"缺少必需元数据: {metadata}",
                    suggestion=f"在文档中添加 {metadata} 信息"
                ))
    
    def _check_structure(self, file_path: Path, content: str):
        """检查文档结构"""
        for section in self.required_sections:
            if section not in content:
                self.issues.append(DocumentIssue(
                    file_path=str(file_path),
                    line_number=0,
                    issue_type="结构缺失",
                    severity="info",
                    message=f"建议添加章节: {section}",
                    suggestion=f"添加 ## {section} 章节"
                ))
    
    def _check_links(self, file_path: Path, content: str):
        """检查链接"""
        # 查找所有链接
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        
        for link_text, link_url in links:
            if link_url.startswith('http'):
                # 外部链接，暂时跳过检查
                continue
            else:
                # 内部链接检查
                if link_url.startswith('/'):
                    target_path = self.doc_root / link_url[1:]
                else:
                    target_path = file_path.parent / link_url
                
                if not target_path.exists():
                    self.issues.append(DocumentIssue(
                        file_path=str(file_path),
                        line_number=0,
                        issue_type="链接错误",
                        severity="error",
                        message=f"链接目标不存在: {link_text} -> {link_url}",
                        suggestion="检查链接路径是否正确"
                    ))
    
    def _check_format_consistency(self, file_path: Path, content: str, lines: List[str]):
        """检查格式一致性"""
        # 检查列表格式
        for i, line in enumerate(lines, 1):
            if line.strip().startswith('-') and not line.startswith('- '):
                self.issues.append(DocumentIssue(
                    file_path=str(file_path),
                    line_number=i,
                    issue_type="格式错误",
                    severity="warning",
                    message="列表项格式不正确",
                    suggestion="使用 '- ' 格式"
                ))
        
        # 检查代码块格式
        in_code_block = False
        for i, line in enumerate(lines, 1):
            if line.strip().startswith('```'):
                in_code_block = not in_code_block
            elif in_code_block and line.strip() == '':
                # 代码块中的空行
                continue
            elif not in_code_block and line.strip() == '':
                # 检查连续空行
                if i < len(lines) and lines[i].strip() == '':
                    self.issues.append(DocumentIssue(
                        file_path=str(file_path),
                        line_number=i,
                        issue_type="格式错误",
                        severity="info",
                        message="存在连续空行",
                        suggestion="删除多余的空行"
                    ))
    
    def _generate_report(self, md_files: List[Path]) -> QualityReport:
        """生成质量报告"""
        total_files = len(md_files)
        total_lines = sum(len(f.read_text(encoding='utf-8').split('\n')) for f in md_files)
        total_size = sum(f.stat().st_size for f in md_files)
        
        issues_by_type = {}
        issues_by_severity = {}
        
        for issue in self.issues:
            issues_by_type[issue.issue_type] = issues_by_type.get(issue.issue_type, 0) + 1
            issues_by_severity[issue.severity] = issues_by_severity.get(issue.severity, 0) + 1
        
        stats = DocumentStats(
            total_files=total_files,
            total_lines=total_lines,
            total_size=total_size,
            issues_count=len(self.issues),
            issues_by_type=issues_by_type,
            issues_by_severity=issues_by_severity
        )
        
        # 计算质量分数
        quality_score = self._calculate_quality_score(stats)
        
        return QualityReport(
            timestamp=datetime.now().isoformat(),
            total_files=total_files,
            total_issues=len(self.issues),
            issues=self.issues,
            stats=stats,
            quality_score=quality_score
        )
    
    def _calculate_quality_score(self, stats: DocumentStats) -> float:
        """计算质量分数"""
        if stats.total_files == 0:
            return 0.0
        
        # 基础分数
        base_score = 100.0
        
        # 根据问题数量和严重程度扣分
        error_penalty = stats.issues_by_severity.get('error', 0) * 10
        warning_penalty = stats.issues_by_severity.get('warning', 0) * 5
        info_penalty = stats.issues_by_severity.get('info', 0) * 1
        
        total_penalty = error_penalty + warning_penalty + info_penalty
        quality_score = max(0.0, base_score - total_penalty)
        
        return round(quality_score, 2)
    
    def generate_html_report(self, report: QualityReport, output_file: str = "doc-quality-report.html"):
        """生成HTML报告"""
        html_template = """
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OpenTelemetry 2025 文档质量报告</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background: #f5f5f5; padding: 20px; border-radius: 5px; }
        .stats { display: flex; gap: 20px; margin: 20px 0; }
        .stat-card { background: #e8f4f8; padding: 15px; border-radius: 5px; flex: 1; }
        .issues { margin: 20px 0; }
        .issue { border: 1px solid #ddd; margin: 10px 0; padding: 15px; border-radius: 5px; }
        .issue.error { border-left: 5px solid #dc3545; }
        .issue.warning { border-left: 5px solid #ffc107; }
        .issue.info { border-left: 5px solid #17a2b8; }
        .quality-score { font-size: 2em; font-weight: bold; color: #28a745; }
    </style>
</head>
<body>
    <div class="header">
        <h1>OpenTelemetry 2025 文档质量报告</h1>
        <p>生成时间: {timestamp}</p>
        <div class="quality-score">质量分数: {quality_score}/100</div>
    </div>
    
    <div class="stats">
        <div class="stat-card">
            <h3>文档统计</h3>
            <p>总文件数: {total_files}</p>
            <p>总行数: {total_lines}</p>
            <p>总大小: {total_size} 字节</p>
        </div>
        <div class="stat-card">
            <h3>问题统计</h3>
            <p>总问题数: {total_issues}</p>
            <p>错误: {error_count}</p>
            <p>警告: {warning_count}</p>
            <p>信息: {info_count}</p>
        </div>
    </div>
    
    <div class="issues">
        <h2>问题详情</h2>
        {issues_html}
    </div>
</body>
</html>
        """
        
        # 生成问题HTML
        issues_html = ""
        for issue in report.issues:
            issues_html += f"""
            <div class="issue {issue.severity}">
                <h4>{issue.file_path}</h4>
                <p><strong>类型:</strong> {issue.issue_type}</p>
                <p><strong>严重程度:</strong> {issue.severity}</p>
                <p><strong>消息:</strong> {issue.message}</p>
                {f'<p><strong>建议:</strong> {issue.suggestion}</p>' if issue.suggestion else ''}
            </div>
            """
        
        html_content = html_template.format(
            timestamp=report.timestamp,
            quality_score=report.quality_score,
            total_files=report.stats.total_files,
            total_lines=report.stats.total_lines,
            total_size=report.stats.total_size,
            total_issues=report.total_issues,
            error_count=report.stats.issues_by_severity.get('error', 0),
            warning_count=report.stats.issues_by_severity.get('warning', 0),
            info_count=report.stats.issues_by_severity.get('info', 0),
            issues_html=issues_html
        )
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        logger.info(f"HTML报告已生成: {output_file}")
    
    def generate_json_report(self, report: QualityReport, output_file: str = "doc-quality-report.json"):
        """生成JSON报告"""
        report_dict = asdict(report)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
        
        logger.info(f"JSON报告已生成: {output_file}")

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="OpenTelemetry 2025 文档质量检查工具")
    parser.add_argument("--doc-root", default="doc", help="文档根目录")
    parser.add_argument("--output-html", default="doc-quality-report.html", help="HTML报告输出文件")
    parser.add_argument("--output-json", default="doc-quality-report.json", help="JSON报告输出文件")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建检查器
    checker = DocumentQualityChecker(args.doc_root)
    
    # 执行检查
    report = checker.check_all_documents()
    
    # 生成报告
    checker.generate_html_report(report, args.output_html)
    checker.generate_json_report(report, args.output_json)
    
    # 输出摘要
    print(f"\n=== 文档质量检查完成 ===")
    print(f"检查文件数: {report.total_files}")
    print(f"发现问题数: {report.total_issues}")
    print(f"质量分数: {report.quality_score}/100")
    print(f"HTML报告: {args.output_html}")
    print(f"JSON报告: {args.output_json}")
    
    # 按严重程度显示问题统计
    print(f"\n=== 问题统计 ===")
    for severity, count in report.stats.issues_by_severity.items():
        print(f"{severity}: {count}")

if __name__ == "__main__":
    main()
