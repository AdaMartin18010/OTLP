#!/usr/bin/env python3
"""
OpenTelemetry 2025 文档链接验证工具

功能：
- 验证内部链接有效性
- 检查外部链接可访问性
- 生成链接报告
- 自动修复常见链接问题
"""

import os
import re
import json
import requests
import time
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass, asdict
from datetime import datetime
from urllib.parse import urlparse, urljoin
import argparse
import logging
from concurrent.futures import ThreadPoolExecutor, as_completed

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class LinkInfo:
    """链接信息"""
    file_path: str
    line_number: int
    link_text: str
    link_url: str
    link_type: str  # 'internal' or 'external'
    status: str  # 'valid', 'invalid', 'broken', 'timeout'
    error_message: Optional[str] = None
    suggestion: Optional[str] = None

@dataclass
class LinkReport:
    """链接报告"""
    timestamp: str
    total_links: int
    internal_links: int
    external_links: int
    valid_links: int
    invalid_links: int
    broken_links: int
    timeout_links: int
    links: List[LinkInfo]
    broken_files: List[str]

class LinkValidator:
    """链接验证器"""
    
    def __init__(self, doc_root: str = "doc", timeout: int = 10, max_workers: int = 10):
        self.doc_root = Path(doc_root)
        self.timeout = timeout
        self.max_workers = max_workers
        self.links: List[LinkInfo] = []
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'OpenTelemetry-Doc-Link-Checker/1.0'
        })
        
        # 链接模式
        self.link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        self.anchor_pattern = r'#([^#\s]+)'
        
        # 已知的锚点
        self.known_anchors: Dict[str, Set[str]] = {}
    
    def validate_all_links(self) -> LinkReport:
        """验证所有链接"""
        logger.info("开始验证所有链接...")
        
        # 收集所有链接
        self._collect_all_links()
        
        # 验证内部链接
        self._validate_internal_links()
        
        # 验证外部链接
        self._validate_external_links()
        
        return self._generate_report()
    
    def _collect_all_links(self):
        """收集所有链接"""
        md_files = list(self.doc_root.rglob("*.md"))
        logger.info(f"扫描 {len(md_files)} 个Markdown文件...")
        
        for md_file in md_files:
            self._collect_links_from_file(md_file)
        
        logger.info(f"收集到 {len(self.links)} 个链接")
    
    def _collect_links_from_file(self, file_path: Path):
        """从文件中收集链接"""
        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            for line_num, line in enumerate(lines, 1):
                matches = re.finditer(self.link_pattern, line)
                for match in matches:
                    link_text = match.group(1)
                    link_url = match.group(2)
                    
                    # 判断链接类型
                    if link_url.startswith('http'):
                        link_type = 'external'
                    else:
                        link_type = 'internal'
                    
                    link_info = LinkInfo(
                        file_path=str(file_path.relative_to(self.doc_root)),
                        line_number=line_num,
                        link_text=link_text,
                        link_url=link_url,
                        link_type=link_type,
                        status='pending'
                    )
                    
                    self.links.append(link_info)
        
        except Exception as e:
            logger.error(f"读取文件失败 {file_path}: {e}")
    
    def _validate_internal_links(self):
        """验证内部链接"""
        logger.info("验证内部链接...")
        
        for link in self.links:
            if link.link_type == 'internal':
                self._validate_single_internal_link(link)
    
    def _validate_single_internal_link(self, link: LinkInfo):
        """验证单个内部链接"""
        try:
            # 解析链接URL
            if link.link_url.startswith('/'):
                # 绝对路径
                target_path = self.doc_root / link.link_url[1:]
            else:
                # 相对路径
                source_file = self.doc_root / link.file_path
                target_path = source_file.parent / link.link_url
            
            # 检查锚点
            if '#' in link.link_url:
                file_part, anchor_part = link.link_url.split('#', 1)
                if file_part:
                    target_path = self.doc_root / file_part
                else:
                    # 同一文件内的锚点
                    target_path = self.doc_root / link.file_path
                
                # 检查文件是否存在
                if not target_path.exists():
                    link.status = 'invalid'
                    link.error_message = f"目标文件不存在: {target_path}"
                    link.suggestion = "检查文件路径是否正确"
                    return
                
                # 检查锚点是否存在
                if not self._check_anchor_exists(target_path, anchor_part):
                    link.status = 'invalid'
                    link.error_message = f"锚点不存在: #{anchor_part}"
                    link.suggestion = "检查锚点名称是否正确"
                    return
            else:
                # 检查文件是否存在
                if not target_path.exists():
                    link.status = 'invalid'
                    link.error_message = f"目标文件不存在: {target_path}"
                    link.suggestion = "检查文件路径是否正确"
                    return
            
            link.status = 'valid'
        
        except Exception as e:
            link.status = 'invalid'
            link.error_message = f"验证失败: {e}"
    
    def _check_anchor_exists(self, file_path: Path, anchor: str) -> bool:
        """检查锚点是否存在"""
        try:
            content = file_path.read_text(encoding='utf-8')
            
            # 查找标题锚点
            title_pattern = r'^#+\s+(.+)$'
            for line in content.split('\n'):
                match = re.match(title_pattern, line)
                if match:
                    title = match.group(1).strip()
                    # 生成锚点ID
                    anchor_id = self._generate_anchor_id(title)
                    if anchor_id == anchor:
                        return True
            
            return False
        
        except Exception as e:
            logger.error(f"检查锚点失败 {file_path}: {e}")
            return False
    
    def _generate_anchor_id(self, title: str) -> str:
        """生成锚点ID"""
        # 移除emoji和特殊字符
        clean_title = re.sub(r'[^\w\s-]', '', title)
        # 转换为小写
        clean_title = clean_title.lower()
        # 替换空格为连字符
        anchor_id = re.sub(r'\s+', '-', clean_title)
        # 移除多余的连字符
        anchor_id = re.sub(r'-+', '-', anchor_id)
        # 移除首尾连字符
        anchor_id = anchor_id.strip('-')
        
        return anchor_id
    
    def _validate_external_links(self):
        """验证外部链接"""
        logger.info("验证外部链接...")
        
        external_links = [link for link in self.links if link.link_type == 'external']
        
        if not external_links:
            return
        
        # 使用线程池并发验证
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_link = {
                executor.submit(self._validate_single_external_link, link): link
                for link in external_links
            }
            
            for future in as_completed(future_to_link):
                link = future_to_link[future]
                try:
                    future.result()
                except Exception as e:
                    logger.error(f"验证外部链接失败 {link.link_url}: {e}")
                    link.status = 'broken'
                    link.error_message = f"验证异常: {e}"
    
    def _validate_single_external_link(self, link: LinkInfo):
        """验证单个外部链接"""
        try:
            response = self.session.head(
                link.link_url,
                timeout=self.timeout,
                allow_redirects=True
            )
            
            if response.status_code == 200:
                link.status = 'valid'
            elif response.status_code in [301, 302, 303, 307, 308]:
                link.status = 'valid'
                link.suggestion = f"链接重定向到: {response.headers.get('Location', '未知')}"
            else:
                link.status = 'broken'
                link.error_message = f"HTTP {response.status_code}"
                link.suggestion = "检查链接是否正确"
        
        except requests.exceptions.Timeout:
            link.status = 'timeout'
            link.error_message = f"请求超时 ({self.timeout}秒)"
            link.suggestion = "检查网络连接或增加超时时间"
        
        except requests.exceptions.ConnectionError:
            link.status = 'broken'
            link.error_message = "连接错误"
            link.suggestion = "检查网络连接或链接是否正确"
        
        except requests.exceptions.RequestException as e:
            link.status = 'broken'
            link.error_message = f"请求错误: {e}"
            link.suggestion = "检查链接是否正确"
        
        except Exception as e:
            link.status = 'broken'
            link.error_message = f"未知错误: {e}"
    
    def _generate_report(self) -> LinkReport:
        """生成链接报告"""
        total_links = len(self.links)
        internal_links = len([l for l in self.links if l.link_type == 'internal'])
        external_links = len([l for l in self.links if l.link_type == 'external'])
        
        valid_links = len([l for l in self.links if l.status == 'valid'])
        invalid_links = len([l for l in self.links if l.status == 'invalid'])
        broken_links = len([l for l in self.links if l.status == 'broken'])
        timeout_links = len([l for l in self.links if l.status == 'timeout'])
        
        # 收集有问题的文件
        broken_files = set()
        for link in self.links:
            if link.status in ['invalid', 'broken', 'timeout']:
                broken_files.add(link.file_path)
        
        return LinkReport(
            timestamp=datetime.now().isoformat(),
            total_links=total_links,
            internal_links=internal_links,
            external_links=external_links,
            valid_links=valid_links,
            invalid_links=invalid_links,
            broken_links=broken_links,
            timeout_links=timeout_links,
            links=self.links,
            broken_files=list(broken_files)
        )
    
    def generate_html_report(self, report: LinkReport, output_file: str = "link-validation-report.html"):
        """生成HTML报告"""
        html_template = """
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OpenTelemetry 2025 链接验证报告</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background: #f5f5f5; padding: 20px; border-radius: 5px; }
        .stats { display: flex; gap: 20px; margin: 20px 0; }
        .stat-card { background: #e8f4f8; padding: 15px; border-radius: 5px; flex: 1; }
        .links { margin: 20px 0; }
        .link { border: 1px solid #ddd; margin: 10px 0; padding: 15px; border-radius: 5px; }
        .link.valid { border-left: 5px solid #28a745; }
        .link.invalid { border-left: 5px solid #dc3545; }
        .link.broken { border-left: 5px solid #dc3545; }
        .link.timeout { border-left: 5px solid #ffc107; }
        .summary { background: #d4edda; padding: 15px; border-radius: 5px; margin: 20px 0; }
    </style>
</head>
<body>
    <div class="header">
        <h1>OpenTelemetry 2025 链接验证报告</h1>
        <p>生成时间: {timestamp}</p>
    </div>
    
    <div class="summary">
        <h2>验证摘要</h2>
        <p>总链接数: {total_links} | 有效链接: {valid_links} | 无效链接: {invalid_links} | 损坏链接: {broken_links} | 超时链接: {timeout_links}</p>
        <p>内部链接: {internal_links} | 外部链接: {external_links}</p>
        <p>有问题的文件数: {broken_files_count}</p>
    </div>
    
    <div class="stats">
        <div class="stat-card">
            <h3>链接类型统计</h3>
            <p>内部链接: {internal_links}</p>
            <p>外部链接: {external_links}</p>
        </div>
        <div class="stat-card">
            <h3>链接状态统计</h3>
            <p>有效: {valid_links}</p>
            <p>无效: {invalid_links}</p>
            <p>损坏: {broken_links}</p>
            <p>超时: {timeout_links}</p>
        </div>
    </div>
    
    <div class="links">
        <h2>链接详情</h2>
        {links_html}
    </div>
</body>
</html>
        """
        
        # 生成链接HTML
        links_html = ""
        for link in report.links:
            status_class = link.status
            links_html += f"""
            <div class="link {status_class}">
                <h4>{link.file_path}:{link.line_number}</h4>
                <p><strong>链接文本:</strong> {link.link_text}</p>
                <p><strong>链接URL:</strong> <a href="{link.link_url}" target="_blank">{link.link_url}</a></p>
                <p><strong>类型:</strong> {link.link_type}</p>
                <p><strong>状态:</strong> {link.status}</p>
                {f'<p><strong>错误信息:</strong> {link.error_message}</p>' if link.error_message else ''}
                {f'<p><strong>建议:</strong> {link.suggestion}</p>' if link.suggestion else ''}
            </div>
            """
        
        html_content = html_template.format(
            timestamp=report.timestamp,
            total_links=report.total_links,
            valid_links=report.valid_links,
            invalid_links=report.invalid_links,
            broken_links=report.broken_links,
            timeout_links=report.timeout_links,
            internal_links=report.internal_links,
            external_links=report.external_links,
            broken_files_count=len(report.broken_files),
            links_html=links_html
        )
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        logger.info(f"HTML报告已生成: {output_file}")
    
    def generate_json_report(self, report: LinkReport, output_file: str = "link-validation-report.json"):
        """生成JSON报告"""
        report_dict = asdict(report)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
        
        logger.info(f"JSON报告已生成: {output_file}")
    
    def fix_common_issues(self, report: LinkReport) -> List[str]:
        """修复常见问题"""
        fixed_files = []
        
        # 按文件分组
        files_with_issues = {}
        for link in report.links:
            if link.status in ['invalid', 'broken']:
                if link.file_path not in files_with_issues:
                    files_with_issues[link.file_path] = []
                files_with_issues[link.file_path].append(link)
        
        # 修复每个文件
        for file_path, issues in files_with_issues.items():
            if self._fix_file_issues(file_path, issues):
                fixed_files.append(file_path)
        
        return fixed_files
    
    def _fix_file_issues(self, file_path: str, issues: List[LinkInfo]) -> bool:
        """修复文件中的问题"""
        try:
            full_path = self.doc_root / file_path
            content = full_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            modified = False
            
            for issue in issues:
                if issue.suggestion and "检查文件路径" in issue.suggestion:
                    # 尝试修复文件路径
                    fixed_url = self._suggest_file_path(issue.link_url)
                    if fixed_url:
                        # 替换链接
                        old_link = f"[{issue.link_text}]({issue.link_url})"
                        new_link = f"[{issue.link_text}]({fixed_url})"
                        
                        if old_link in lines[issue.line_number - 1]:
                            lines[issue.line_number - 1] = lines[issue.line_number - 1].replace(old_link, new_link)
                            modified = True
                            logger.info(f"修复链接: {file_path}:{issue.line_number} {issue.link_url} -> {fixed_url}")
            
            if modified:
                full_path.write_text('\n'.join(lines), encoding='utf-8')
                return True
            
            return False
        
        except Exception as e:
            logger.error(f"修复文件失败 {file_path}: {e}")
            return False
    
    def _suggest_file_path(self, broken_url: str) -> Optional[str]:
        """建议正确的文件路径"""
        # 简单的路径修复逻辑
        if broken_url.startswith('/'):
            # 绝对路径
            potential_path = self.doc_root / broken_url[1:]
        else:
            # 相对路径，需要更多上下文
            return None
        
        # 检查是否存在
        if potential_path.exists():
            return broken_url
        
        # 尝试常见的修复
        common_fixes = [
            broken_url.replace('.md', ''),
            broken_url.replace('.md', '.md'),
            broken_url + '.md',
            broken_url.replace('_', '-'),
            broken_url.replace('-', '_')
        ]
        
        for fix in common_fixes:
            if fix.startswith('/'):
                test_path = self.doc_root / fix[1:]
            else:
                test_path = self.doc_root / fix
            
            if test_path.exists():
                return fix
        
        return None

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="OpenTelemetry 2025 链接验证工具")
    parser.add_argument("--doc-root", default="doc", help="文档根目录")
    parser.add_argument("--timeout", type=int, default=10, help="请求超时时间（秒）")
    parser.add_argument("--max-workers", type=int, default=10, help="最大并发数")
    parser.add_argument("--output-html", default="link-validation-report.html", help="HTML报告输出文件")
    parser.add_argument("--output-json", default="link-validation-report.json", help="JSON报告输出文件")
    parser.add_argument("--fix", action="store_true", help="自动修复常见问题")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建验证器
    validator = LinkValidator(args.doc_root, args.timeout, args.max_workers)
    
    # 执行验证
    report = validator.validate_all_links()
    
    # 生成报告
    validator.generate_html_report(report, args.output_html)
    validator.generate_json_report(report, args.output_json)
    
    # 自动修复
    if args.fix:
        fixed_files = validator.fix_common_issues(report)
        if fixed_files:
            print(f"已修复 {len(fixed_files)} 个文件:")
            for file_path in fixed_files:
                print(f"  - {file_path}")
        else:
            print("没有找到可以自动修复的问题")
    
    # 输出摘要
    print(f"\n=== 链接验证完成 ===")
    print(f"总链接数: {report.total_links}")
    print(f"有效链接: {report.valid_links}")
    print(f"无效链接: {report.invalid_links}")
    print(f"损坏链接: {report.broken_links}")
    print(f"超时链接: {report.timeout_links}")
    print(f"有问题的文件: {len(report.broken_files)}")
    print(f"HTML报告: {args.output_html}")
    print(f"JSON报告: {args.output_json}")

if __name__ == "__main__":
    main()
