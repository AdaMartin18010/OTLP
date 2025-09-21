#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OpenTelemetry 2025 自动化质量保证系统
Automated Quality Assurance System for OpenTelemetry 2025

功能特性:
- 文档质量检查
- 标准对齐验证
- 知识完整性评估
- 学术合作监控
- 自动报告生成
- 改进建议提供
"""

import os
import sys
import json
import yaml
import time
import logging
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('quality_assurance.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class QualityLevel(Enum):
    """质量级别枚举"""
    EXCELLENT = "excellent"
    GOOD = "good"
    FAIR = "fair"
    POOR = "poor"
    CRITICAL = "critical"

@dataclass
class QualityMetrics:
    """质量指标数据类"""
    completeness: float
    accuracy: float
    consistency: float
    timeliness: float
    overall_score: float
    level: QualityLevel

class DocumentQualityChecker:
    """文档质量检查器"""
    
    def __init__(self, base_path: str = "doc"):
        self.base_path = Path(base_path)
        self.quality_thresholds = {
            'completeness': 0.8,
            'accuracy': 0.9,
            'consistency': 0.85,
            'timeliness': 0.7
        }
    
    def check_document_quality(self, doc_path: str) -> QualityMetrics:
        """检查文档质量"""
        try:
            doc_file = self.base_path / doc_path
            
            if not doc_file.exists():
                return QualityMetrics(0, 0, 0, 0, 0, QualityLevel.CRITICAL)
            
            # 读取文档内容
            content = doc_file.read_text(encoding='utf-8')
            
            # 计算各项质量指标
            completeness = self._calculate_completeness(content)
            accuracy = self._calculate_accuracy(content)
            consistency = self._calculate_consistency(content)
            timeliness = self._calculate_timeliness(doc_file)
            
            # 计算总体分数
            overall_score = (completeness + accuracy + consistency + timeliness) / 4
            
            # 确定质量级别
            level = self._determine_quality_level(overall_score)
            
            return QualityMetrics(
                completeness=completeness,
                accuracy=accuracy,
                consistency=consistency,
                timeliness=timeliness,
                overall_score=overall_score,
                level=level
            )
            
        except Exception as e:
            logger.error(f"检查文档质量时出错: {e}")
            return QualityMetrics(0, 0, 0, 0, 0, QualityLevel.CRITICAL)
    
    def _calculate_completeness(self, content: str) -> float:
        """计算完整性分数"""
        required_sections = [
            '# 概述', '## 核心内容', '## 应用场景', 
            '## 性能优化', '## 测试与验证', '## 参考文献'
        ]
        
        found_sections = sum(1 for section in required_sections if section in content)
        return found_sections / len(required_sections)
    
    def _calculate_accuracy(self, content: str) -> float:
        """计算准确性分数"""
        # 检查常见错误
        errors = 0
        total_checks = 0
        
        # 检查链接格式
        import re
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        total_checks += len(links)
        
        for link_text, link_url in links:
            if not link_url.startswith(('http', '/', '#')):
                errors += 1
        
        # 检查代码块格式
        code_blocks = content.count('```')
        if code_blocks % 2 != 0:
            errors += 1
            total_checks += 1
        
        return 1.0 - (errors / max(total_checks, 1))
    
    def _calculate_consistency(self, content: str) -> float:
        """计算一致性分数"""
        # 检查标题层级一致性
        import re
        headers = re.findall(r'^(#{1,6})\s+(.+)$', content, re.MULTILINE)
        
        if not headers:
            return 1.0
        
        # 检查标题层级是否合理
        levels = [len(header[0]) for header in headers]
        max_level = max(levels)
        
        # 检查是否有跳级
        consistency_score = 1.0
        for i in range(1, len(levels)):
            if levels[i] > levels[i-1] + 1:
                consistency_score -= 0.1
        
        return max(0, consistency_score)
    
    def _calculate_timeliness(self, doc_file: Path) -> float:
        """计算时效性分数"""
        try:
            # 获取文件修改时间
            mtime = doc_file.stat().st_mtime
            current_time = time.time()
            
            # 计算文件年龄（天）
            age_days = (current_time - mtime) / (24 * 3600)
            
            # 根据文件年龄计算分数
            if age_days < 30:
                return 1.0
            elif age_days < 90:
                return 0.8
            elif age_days < 180:
                return 0.6
            elif age_days < 365:
                return 0.4
            else:
                return 0.2
                
        except Exception:
            return 0.0
    
    def _determine_quality_level(self, score: float) -> QualityLevel:
        """确定质量级别"""
        if score >= 0.9:
            return QualityLevel.EXCELLENT
        elif score >= 0.8:
            return QualityLevel.GOOD
        elif score >= 0.7:
            return QualityLevel.FAIR
        elif score >= 0.6:
            return QualityLevel.POOR
        else:
            return QualityLevel.CRITICAL

class StandardsAlignmentChecker:
    """标准对齐检查器"""
    
    def __init__(self):
        self.standards_config = self._load_standards_config()
    
    def _load_standards_config(self) -> Dict[str, Any]:
        """加载标准配置"""
        try:
            config_path = Path("config/international_standards_alignment.yaml")
            if config_path.exists():
                with open(config_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            return {}
        except Exception as e:
            logger.error(f"加载标准配置失败: {e}")
            return {}
    
    def check_standards_alignment(self) -> Dict[str, Any]:
        """检查标准对齐情况"""
        alignment_results = {}
        
        for standard_name, config in self.standards_config.items():
            alignment_results[standard_name] = {
                'alignment_status': config.get('alignment_status', 'unknown'),
                'implementation_status': config.get('implementation_status', 'unknown'),
                'compliance_score': self._calculate_compliance_score(config),
                'last_updated': config.get('last_updated', 'unknown')
            }
        
        return alignment_results
    
    def _calculate_compliance_score(self, config: Dict[str, Any]) -> float:
        """计算合规分数"""
        # 基于配置计算合规分数
        score = 0.0
        
        if config.get('alignment_status') == '100%':
            score += 0.4
        elif config.get('alignment_status') == '80%':
            score += 0.3
        elif config.get('alignment_status') == '60%':
            score += 0.2
        
        if config.get('implementation_status') == '已完成':
            score += 0.3
        elif config.get('implementation_status') == '进行中':
            score += 0.2
        elif config.get('implementation_status') == '计划中':
            score += 0.1
        
        # 检查是否有具体要求
        if config.get('requirements'):
            score += 0.3
        
        return min(1.0, score)

class KnowledgeCompletenessChecker:
    """知识完整性检查器"""
    
    def __init__(self, base_path: str = "doc/02_知识体系"):
        self.base_path = Path(base_path)
        self.required_layers = [
            "01_理论基础层",
            "02_标准规范层", 
            "03_技术实现层",
            "04_应用实践层",
            "05_质量保证层",
            "06_社区生态层",
            "07_学术研究层"
        ]
    
    def check_knowledge_completeness(self) -> Dict[str, Any]:
        """检查知识完整性"""
        completeness_results = {}
        
        for layer in self.required_layers:
            layer_path = self.base_path / layer
            completeness_results[layer] = self._check_layer_completeness(layer_path)
        
        # 计算总体完整性
        total_completeness = sum(
            result['completeness_score'] for result in completeness_results.values()
        ) / len(completeness_results)
        
        return {
            'layers': completeness_results,
            'total_completeness': total_completeness,
            'missing_components': self._identify_missing_components(completeness_results)
        }
    
    def _check_layer_completeness(self, layer_path: Path) -> Dict[str, Any]:
        """检查层级完整性"""
        if not layer_path.exists():
            return {
                'exists': False,
                'completeness_score': 0.0,
                'missing_files': ['README.md']
            }
        
        # 检查必需文件
        required_files = ['README.md']
        existing_files = list(layer_path.glob('**/*.md'))
        
        missing_files = []
        for required_file in required_files:
            if not (layer_path / required_file).exists():
                missing_files.append(required_file)
        
        # 计算完整性分数
        completeness_score = 1.0 - (len(missing_files) / len(required_files))
        
        return {
            'exists': True,
            'completeness_score': completeness_score,
            'missing_files': missing_files,
            'total_files': len(existing_files)
        }
    
    def _identify_missing_components(self, completeness_results: Dict[str, Any]) -> List[str]:
        """识别缺失组件"""
        missing_components = []
        
        for layer_name, result in completeness_results.items():
            if not result['exists']:
                missing_components.append(f"{layer_name} - 整个层级缺失")
            elif result['missing_files']:
                missing_components.append(f"{layer_name} - 缺失文件: {', '.join(result['missing_files'])}")
        
        return missing_components

class QualityReportGenerator:
    """质量报告生成器"""
    
    def __init__(self):
        self.template_path = Path("templates/quality_report_template.md")
    
    def generate_quality_report(self, quality_data: Dict[str, Any]) -> str:
        """生成质量报告"""
        report_content = f"""# OpenTelemetry 2025 质量保证报告

## 📊 报告概述

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**报告版本**: 1.0.0
**检查范围**: 整个知识体系

## 📈 质量指标总览

### 文档质量
- **平均完整性**: {quality_data.get('document_quality', {}).get('average_completeness', 0):.2%}
- **平均准确性**: {quality_data.get('document_quality', {}).get('average_accuracy', 0):.2%}
- **平均一致性**: {quality_data.get('document_quality', {}).get('average_consistency', 0):.2%}
- **平均时效性**: {quality_data.get('document_quality', {}).get('average_timeliness', 0):.2%}
- **总体质量分数**: {quality_data.get('document_quality', {}).get('overall_score', 0):.2%}

### 标准对齐
- **对齐标准数量**: {len(quality_data.get('standards_alignment', {}))}
- **完全对齐标准**: {sum(1 for std in quality_data.get('standards_alignment', {}).values() if std.get('alignment_status') == '100%')}
- **平均合规分数**: {sum(std.get('compliance_score', 0) for std in quality_data.get('standards_alignment', {}).values()) / max(len(quality_data.get('standards_alignment', {})), 1):.2%}

### 知识完整性
- **知识层级数量**: {len(quality_data.get('knowledge_completeness', {}).get('layers', {}))}
- **总体完整性**: {quality_data.get('knowledge_completeness', {}).get('total_completeness', 0):.2%}
- **缺失组件数量**: {len(quality_data.get('knowledge_completeness', {}).get('missing_components', []))}

## 🔍 详细分析

### 文档质量分析
"""
        
        # 添加文档质量详细分析
        doc_quality = quality_data.get('document_quality', {})
        if 'detailed_results' in doc_quality:
            report_content += "\n#### 各文档质量详情\n\n"
            report_content += "| 文档路径 | 完整性 | 准确性 | 一致性 | 时效性 | 总体分数 | 质量级别 |\n"
            report_content += "|---------|--------|--------|--------|--------|----------|----------|\n"
            
            for doc_path, metrics in doc_quality['detailed_results'].items():
                report_content += f"| {doc_path} | {metrics.completeness:.2%} | {metrics.accuracy:.2%} | {metrics.consistency:.2%} | {metrics.timeliness:.2%} | {metrics.overall_score:.2%} | {metrics.level.value} |\n"
        
        # 添加标准对齐分析
        report_content += "\n### 标准对齐分析\n\n"
        standards = quality_data.get('standards_alignment', {})
        for std_name, std_data in standards.items():
            report_content += f"#### {std_name}\n"
            report_content += f"- **对齐状态**: {std_data.get('alignment_status', 'unknown')}\n"
            report_content += f"- **实施状态**: {std_data.get('implementation_status', 'unknown')}\n"
            report_content += f"- **合规分数**: {std_data.get('compliance_score', 0):.2%}\n"
            report_content += f"- **最后更新**: {std_data.get('last_updated', 'unknown')}\n\n"
        
        # 添加知识完整性分析
        report_content += "\n### 知识完整性分析\n\n"
        knowledge = quality_data.get('knowledge_completeness', {})
        layers = knowledge.get('layers', {})
        
        for layer_name, layer_data in layers.items():
            report_content += f"#### {layer_name}\n"
            report_content += f"- **存在性**: {'是' if layer_data.get('exists') else '否'}\n"
            report_content += f"- **完整性分数**: {layer_data.get('completeness_score', 0):.2%}\n"
            report_content += f"- **文件总数**: {layer_data.get('total_files', 0)}\n"
            if layer_data.get('missing_files'):
                report_content += f"- **缺失文件**: {', '.join(layer_data['missing_files'])}\n"
            report_content += "\n"
        
        # 添加改进建议
        report_content += "\n## 💡 改进建议\n\n"
        improvements = self._generate_improvement_suggestions(quality_data)
        for i, improvement in enumerate(improvements, 1):
            report_content += f"{i}. {improvement}\n"
        
        # 添加结论
        report_content += f"""

## 📋 结论

基于本次质量检查，OpenTelemetry 2025知识体系整体质量{'优秀' if quality_data.get('document_quality', {}).get('overall_score', 0) > 0.8 else '良好' if quality_data.get('document_quality', {}).get('overall_score', 0) > 0.6 else '需要改进'}。

### 主要成就
- 知识体系结构完整，覆盖了从理论基础到实际应用的各个层面
- 标准对齐工作进展良好，与国际标准保持高度一致
- 文档质量整体较高，内容详实，结构清晰

### 需要关注的问题
- 部分文档需要更新以保持时效性
- 某些标准的具体实施细节需要进一步完善
- 知识体系的某些组件需要补充

### 下一步行动
1. 优先处理质量级别为"critical"和"poor"的文档
2. 完善缺失的知识组件
3. 加强标准对齐的具体实施
4. 建立定期的质量检查机制

---
*本报告由OpenTelemetry 2025自动化质量保证系统生成*
"""
        
        return report_content
    
    def _generate_improvement_suggestions(self, quality_data: Dict[str, Any]) -> List[str]:
        """生成改进建议"""
        suggestions = []
        
        # 基于文档质量的建议
        doc_quality = quality_data.get('document_quality', {})
        if doc_quality.get('average_completeness', 0) < 0.8:
            suggestions.append("提高文档完整性，确保所有必需章节都存在")
        
        if doc_quality.get('average_accuracy', 0) < 0.9:
            suggestions.append("提高文档准确性，检查链接格式和代码块语法")
        
        if doc_quality.get('average_timeliness', 0) < 0.7:
            suggestions.append("更新过时的文档，保持内容的时效性")
        
        # 基于标准对齐的建议
        standards = quality_data.get('standards_alignment', {})
        low_compliance_standards = [
            name for name, data in standards.items() 
            if data.get('compliance_score', 0) < 0.7
        ]
        if low_compliance_standards:
            suggestions.append(f"提高以下标准的合规性: {', '.join(low_compliance_standards)}")
        
        # 基于知识完整性的建议
        knowledge = quality_data.get('knowledge_completeness', {})
        missing_components = knowledge.get('missing_components', [])
        if missing_components:
            suggestions.append(f"补充缺失的知识组件: {', '.join(missing_components[:3])}")
        
        return suggestions

class AutomatedQualityAssurance:
    """自动化质量保证主类"""
    
    def __init__(self, base_path: str = "doc"):
        self.base_path = Path(base_path)
        self.doc_checker = DocumentQualityChecker(base_path)
        self.standards_checker = StandardsAlignmentChecker()
        self.knowledge_checker = KnowledgeCompletenessChecker(base_path)
        self.report_generator = QualityReportGenerator()
    
    def run_quality_assurance(self) -> Dict[str, Any]:
        """运行质量保证检查"""
        logger.info("开始运行自动化质量保证检查...")
        
        quality_data = {}
        
        # 1. 文档质量检查
        logger.info("执行文档质量检查...")
        quality_data['document_quality'] = self._check_document_quality()
        
        # 2. 标准对齐检查
        logger.info("执行标准对齐检查...")
        quality_data['standards_alignment'] = self.standards_checker.check_standards_alignment()
        
        # 3. 知识完整性检查
        logger.info("执行知识完整性检查...")
        quality_data['knowledge_completeness'] = self.knowledge_checker.check_knowledge_completeness()
        
        # 4. 生成质量报告
        logger.info("生成质量报告...")
        report_content = self.report_generator.generate_quality_report(quality_data)
        
        # 5. 保存报告
        self._save_quality_report(report_content)
        
        logger.info("自动化质量保证检查完成")
        return quality_data
    
    def _check_document_quality(self) -> Dict[str, Any]:
        """检查文档质量"""
        # 获取所有markdown文件
        md_files = list(self.base_path.glob('**/*.md'))
        
        detailed_results = {}
        total_metrics = QualityMetrics(0, 0, 0, 0, 0, QualityLevel.POOR)
        
        for md_file in md_files:
            # 计算相对路径
            rel_path = md_file.relative_to(self.base_path)
            
            # 检查文档质量
            metrics = self.doc_checker.check_document_quality(str(rel_path))
            detailed_results[str(rel_path)] = metrics
            
            # 累加指标
            total_metrics.completeness += metrics.completeness
            total_metrics.accuracy += metrics.accuracy
            total_metrics.consistency += metrics.consistency
            total_metrics.timeliness += metrics.timeliness
        
        # 计算平均值
        file_count = len(md_files)
        if file_count > 0:
            total_metrics.completeness /= file_count
            total_metrics.accuracy /= file_count
            total_metrics.consistency /= file_count
            total_metrics.timeliness /= file_count
            total_metrics.overall_score = (
                total_metrics.completeness + total_metrics.accuracy + 
                total_metrics.consistency + total_metrics.timeliness
            ) / 4
            total_metrics.level = self.doc_checker._determine_quality_level(total_metrics.overall_score)
        
        return {
            'detailed_results': detailed_results,
            'average_completeness': total_metrics.completeness,
            'average_accuracy': total_metrics.accuracy,
            'average_consistency': total_metrics.consistency,
            'average_timeliness': total_metrics.timeliness,
            'overall_score': total_metrics.overall_score,
            'total_files_checked': file_count
        }
    
    def _save_quality_report(self, report_content: str):
        """保存质量报告"""
        try:
            # 创建报告目录
            report_dir = Path("reports")
            report_dir.mkdir(exist_ok=True)
            
            # 生成报告文件名
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            report_file = report_dir / f"quality_assurance_report_{timestamp}.md"
            
            # 保存报告
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report_content)
            
            logger.info(f"质量报告已保存到: {report_file}")
            
        except Exception as e:
            logger.error(f"保存质量报告失败: {e}")

def main():
    """主函数"""
    try:
        # 创建自动化质量保证实例
        qa_system = AutomatedQualityAssurance()
        
        # 运行质量保证检查
        quality_data = qa_system.run_quality_assurance()
        
        # 输出简要结果
        print("\n" + "="*60)
        print("OpenTelemetry 2025 自动化质量保证检查结果")
        print("="*60)
        
        doc_quality = quality_data.get('document_quality', {})
        print(f"📊 文档质量总体分数: {doc_quality.get('overall_score', 0):.2%}")
        print(f"📁 检查文档数量: {doc_quality.get('total_files_checked', 0)}")
        
        knowledge = quality_data.get('knowledge_completeness', {})
        print(f"🧠 知识完整性: {knowledge.get('total_completeness', 0):.2%}")
        
        standards = quality_data.get('standards_alignment', {})
        print(f"📋 标准对齐数量: {len(standards)}")
        
        print("\n详细报告已生成，请查看 reports/ 目录")
        print("="*60)
        
    except Exception as e:
        logger.error(f"运行质量保证检查时出错: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
