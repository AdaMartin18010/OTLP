#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OpenTelemetry 2025 标准合规监控系统
Standards Compliance Monitoring System for OpenTelemetry 2025

功能特性:
- 标准合规性检查
- 合规状态监控
- 合规报告生成
- 合规趋势分析
- 自动合规提醒
- 合规改进建议
"""

import os
import sys
import json
import yaml
import time
import logging
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import re

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('standards_compliance.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class ComplianceLevel(Enum):
    """合规级别枚举"""
    FULLY_COMPLIANT = "fully_compliant"
    MOSTLY_COMPLIANT = "mostly_compliant"
    PARTIALLY_COMPLIANT = "partially_compliant"
    NON_COMPLIANT = "non_compliant"
    NOT_ASSESSED = "not_assessed"

class StandardType(Enum):
    """标准类型枚举"""
    INTERNATIONAL = "international"
    INDUSTRY = "industry"
    TECHNICAL = "technical"
    SECURITY = "security"
    QUALITY = "quality"

@dataclass
class ComplianceRequirement:
    """合规要求数据类"""
    id: str
    title: str
    description: str
    category: str
    priority: str
    mandatory: bool
    implementation_notes: str
    verification_method: str

@dataclass
class ComplianceStatus:
    """合规状态数据类"""
    standard_id: str
    standard_name: str
    standard_type: StandardType
    compliance_level: ComplianceLevel
    compliance_score: float
    requirements_total: int
    requirements_met: int
    requirements_partial: int
    requirements_not_met: int
    last_assessment: str
    next_assessment: str
    issues: List[str]
    recommendations: List[str]

class StandardsComplianceChecker:
    """标准合规检查器"""
    
    def __init__(self, config_path: str = "config/international_standards_alignment.yaml"):
        self.config_path = Path(config_path)
        self.standards_config = self._load_standards_config()
        self.compliance_requirements = self._load_compliance_requirements()
    
    def _load_standards_config(self) -> Dict[str, Any]:
        """加载标准配置"""
        try:
            if self.config_path.exists():
                with open(self.config_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            return {}
        except Exception as e:
            logger.error(f"加载标准配置失败: {e}")
            return {}
    
    def _load_compliance_requirements(self) -> Dict[str, List[ComplianceRequirement]]:
        """加载合规要求"""
        requirements = {}
        
        # 定义各类标准的合规要求
        requirements['ISO_27001'] = [
            ComplianceRequirement(
                id="ISO27001-001",
                title="信息安全管理体系",
                description="建立和维护信息安全管理体系",
                category="管理体系",
                priority="高",
                mandatory=True,
                implementation_notes="需要建立ISMS框架，包括政策、程序和控制措施",
                verification_method="文档审查、现场检查"
            ),
            ComplianceRequirement(
                id="ISO27001-002",
                title="风险评估",
                description="定期进行信息安全风险评估",
                category="风险管理",
                priority="高",
                mandatory=True,
                implementation_notes="建立风险评估流程，识别和评估信息安全风险",
                verification_method="风险评估报告审查"
            )
        ]
        
        requirements['ISO_20000'] = [
            ComplianceRequirement(
                id="ISO20000-001",
                title="IT服务管理体系",
                description="建立和维护IT服务管理体系",
                category="服务管理",
                priority="高",
                mandatory=True,
                implementation_notes="需要建立ITSM框架，包括服务设计、交付和支持",
                verification_method="服务管理文档审查"
            )
        ]
        
        requirements['IEEE_1888'] = [
            ComplianceRequirement(
                id="IEEE1888-001",
                title="物联网协议标准",
                description="遵循IEEE 1888物联网协议标准",
                category="协议标准",
                priority="中",
                mandatory=False,
                implementation_notes="在物联网应用中采用IEEE 1888协议",
                verification_method="协议实现检查"
            )
        ]
        
        return requirements
    
    def check_standard_compliance(self, standard_id: str) -> ComplianceStatus:
        """检查单个标准的合规性"""
        try:
            # 获取标准配置
            standard_config = self.standards_config.get(standard_id, {})
            
            # 获取合规要求
            requirements = self.compliance_requirements.get(standard_id, [])
            
            if not requirements:
                return ComplianceStatus(
                    standard_id=standard_id,
                    standard_name=standard_config.get('name', standard_id),
                    standard_type=StandardType.INTERNATIONAL,
                    compliance_level=ComplianceLevel.NOT_ASSESSED,
                    compliance_score=0.0,
                    requirements_total=0,
                    requirements_met=0,
                    requirements_partial=0,
                    requirements_not_met=0,
                    last_assessment=datetime.now().isoformat(),
                    next_assessment=(datetime.now() + timedelta(days=90)).isoformat(),
                    issues=["未找到合规要求定义"],
                    recommendations=["请定义该标准的合规要求"]
                )
            
            # 评估合规状态
            compliance_results = self._assess_compliance_requirements(requirements, standard_config)
            
            # 计算合规分数
            compliance_score = self._calculate_compliance_score(compliance_results)
            
            # 确定合规级别
            compliance_level = self._determine_compliance_level(compliance_score)
            
            # 生成问题和建议
            issues, recommendations = self._generate_issues_and_recommendations(
                requirements, compliance_results, standard_config
            )
            
            return ComplianceStatus(
                standard_id=standard_id,
                standard_name=standard_config.get('name', standard_id),
                standard_type=StandardType.INTERNATIONAL,
                compliance_level=compliance_level,
                compliance_score=compliance_score,
                requirements_total=len(requirements),
                requirements_met=compliance_results['met'],
                requirements_partial=compliance_results['partial'],
                requirements_not_met=compliance_results['not_met'],
                last_assessment=datetime.now().isoformat(),
                next_assessment=(datetime.now() + timedelta(days=90)).isoformat(),
                issues=issues,
                recommendations=recommendations
            )
            
        except Exception as e:
            logger.error(f"检查标准合规性时出错: {e}")
            return ComplianceStatus(
                standard_id=standard_id,
                standard_name=standard_id,
                standard_type=StandardType.INTERNATIONAL,
                compliance_level=ComplianceLevel.NOT_ASSESSED,
                compliance_score=0.0,
                requirements_total=0,
                requirements_met=0,
                requirements_partial=0,
                requirements_not_met=0,
                last_assessment=datetime.now().isoformat(),
                next_assessment=(datetime.now() + timedelta(days=90)).isoformat(),
                issues=[f"检查过程中出错: {str(e)}"],
                recommendations=["请检查标准配置和实现状态"]
            )
    
    def _assess_compliance_requirements(self, requirements: List[ComplianceRequirement], 
                                      standard_config: Dict[str, Any]) -> Dict[str, int]:
        """评估合规要求"""
        results = {'met': 0, 'partial': 0, 'not_met': 0}
        
        for requirement in requirements:
            # 基于标准配置评估合规状态
            alignment_status = standard_config.get('alignment_status', '0%')
            implementation_status = standard_config.get('implementation_status', '未开始')
            
            # 简化的评估逻辑
            if alignment_status == '100%' and implementation_status == '已完成':
                results['met'] += 1
            elif alignment_status in ['80%', '60%'] or implementation_status == '进行中':
                results['partial'] += 1
            else:
                results['not_met'] += 1
        
        return results
    
    def _calculate_compliance_score(self, compliance_results: Dict[str, int]) -> float:
        """计算合规分数"""
        total = sum(compliance_results.values())
        if total == 0:
            return 0.0
        
        # 完全合规得1分，部分合规得0.5分，不合规得0分
        score = (compliance_results['met'] * 1.0 + 
                compliance_results['partial'] * 0.5 + 
                compliance_results['not_met'] * 0.0) / total
        
        return score
    
    def _determine_compliance_level(self, score: float) -> ComplianceLevel:
        """确定合规级别"""
        if score >= 0.9:
            return ComplianceLevel.FULLY_COMPLIANT
        elif score >= 0.7:
            return ComplianceLevel.MOSTLY_COMPLIANT
        elif score >= 0.5:
            return ComplianceLevel.PARTIALLY_COMPLIANT
        elif score > 0:
            return ComplianceLevel.NON_COMPLIANT
        else:
            return ComplianceLevel.NOT_ASSESSED
    
    def _generate_issues_and_recommendations(self, requirements: List[ComplianceRequirement],
                                           compliance_results: Dict[str, int],
                                           standard_config: Dict[str, Any]) -> Tuple[List[str], List[str]]:
        """生成问题和建议"""
        issues = []
        recommendations = []
        
        # 基于合规结果生成问题
        if compliance_results['not_met'] > 0:
            issues.append(f"有 {compliance_results['not_met']} 个要求未满足")
        
        if compliance_results['partial'] > 0:
            issues.append(f"有 {compliance_results['partial']} 个要求部分满足")
        
        # 基于标准配置生成问题
        alignment_status = standard_config.get('alignment_status', '0%')
        if alignment_status in ['0%', '20%', '40%']:
            issues.append(f"标准对齐度较低: {alignment_status}")
        
        implementation_status = standard_config.get('implementation_status', '未开始')
        if implementation_status in ['未开始', '计划中']:
            issues.append(f"实施状态需要改进: {implementation_status}")
        
        # 生成建议
        if compliance_results['not_met'] > 0:
            recommendations.append("优先处理未满足的合规要求")
        
        if compliance_results['partial'] > 0:
            recommendations.append("完善部分满足的合规要求")
        
        if alignment_status in ['0%', '20%', '40%']:
            recommendations.append("提高标准对齐度，制定详细的对齐计划")
        
        if implementation_status in ['未开始', '计划中']:
            recommendations.append("加快标准实施进度，制定实施时间表")
        
        return issues, recommendations

class ComplianceTrendAnalyzer:
    """合规趋势分析器"""
    
    def __init__(self, history_file: str = "data/compliance_history.json"):
        self.history_file = Path(history_file)
        self.compliance_history = self._load_compliance_history()
    
    def _load_compliance_history(self) -> List[Dict[str, Any]]:
        """加载合规历史数据"""
        try:
            if self.history_file.exists():
                with open(self.history_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            return []
        except Exception as e:
            logger.error(f"加载合规历史数据失败: {e}")
            return []
    
    def save_compliance_snapshot(self, compliance_statuses: List[ComplianceStatus]):
        """保存合规快照"""
        try:
            # 创建数据目录
            self.history_file.parent.mkdir(parents=True, exist_ok=True)
            
            # 创建快照
            snapshot = {
                'timestamp': datetime.now().isoformat(),
                'standards': [asdict(status) for status in compliance_statuses]
            }
            
            # 添加到历史数据
            self.compliance_history.append(snapshot)
            
            # 保存历史数据
            with open(self.history_file, 'w', encoding='utf-8') as f:
                json.dump(self.compliance_history, f, ensure_ascii=False, indent=2)
            
            logger.info(f"合规快照已保存: {snapshot['timestamp']}")
            
        except Exception as e:
            logger.error(f"保存合规快照失败: {e}")
    
    def analyze_compliance_trends(self) -> Dict[str, Any]:
        """分析合规趋势"""
        if len(self.compliance_history) < 2:
            return {'trend': 'insufficient_data', 'message': '历史数据不足，无法分析趋势'}
        
        # 分析总体合规趋势
        recent_snapshots = self.compliance_history[-5:]  # 最近5个快照
        
        trend_analysis = {
            'overall_trend': self._analyze_overall_trend(recent_snapshots),
            'standard_trends': self._analyze_standard_trends(recent_snapshots),
            'compliance_level_distribution': self._analyze_compliance_level_distribution(recent_snapshots[-1]),
            'improvement_areas': self._identify_improvement_areas(recent_snapshots)
        }
        
        return trend_analysis
    
    def _analyze_overall_trend(self, snapshots: List[Dict[str, Any]]) -> Dict[str, Any]:
        """分析总体趋势"""
        if len(snapshots) < 2:
            return {'trend': 'stable', 'change': 0.0}
        
        # 计算平均合规分数
        scores = []
        for snapshot in snapshots:
            total_score = 0
            count = 0
            for standard in snapshot['standards']:
                total_score += standard['compliance_score']
                count += 1
            if count > 0:
                scores.append(total_score / count)
        
        if len(scores) < 2:
            return {'trend': 'stable', 'change': 0.0}
        
        # 计算趋势
        latest_score = scores[-1]
        previous_score = scores[-2]
        change = latest_score - previous_score
        
        if change > 0.05:
            trend = 'improving'
        elif change < -0.05:
            trend = 'declining'
        else:
            trend = 'stable'
        
        return {
            'trend': trend,
            'change': change,
            'latest_score': latest_score,
            'previous_score': previous_score
        }
    
    def _analyze_standard_trends(self, snapshots: List[Dict[str, Any]]) -> Dict[str, Any]:
        """分析各标准趋势"""
        standard_trends = {}
        
        # 获取所有标准ID
        all_standards = set()
        for snapshot in snapshots:
            for standard in snapshot['standards']:
                all_standards.add(standard['standard_id'])
        
        # 分析每个标准的趋势
        for standard_id in all_standards:
            scores = []
            for snapshot in snapshots:
                for standard in snapshot['standards']:
                    if standard['standard_id'] == standard_id:
                        scores.append(standard['compliance_score'])
                        break
            
            if len(scores) >= 2:
                change = scores[-1] - scores[-2]
                if change > 0.05:
                    trend = 'improving'
                elif change < -0.05:
                    trend = 'declining'
                else:
                    trend = 'stable'
                
                standard_trends[standard_id] = {
                    'trend': trend,
                    'change': change,
                    'latest_score': scores[-1]
                }
        
        return standard_trends
    
    def _analyze_compliance_level_distribution(self, latest_snapshot: Dict[str, Any]) -> Dict[str, int]:
        """分析合规级别分布"""
        distribution = {
            'fully_compliant': 0,
            'mostly_compliant': 0,
            'partially_compliant': 0,
            'non_compliant': 0,
            'not_assessed': 0
        }
        
        for standard in latest_snapshot['standards']:
            level = standard['compliance_level']
            distribution[level] += 1
        
        return distribution
    
    def _identify_improvement_areas(self, snapshots: List[Dict[str, Any]]) -> List[str]:
        """识别改进领域"""
        improvement_areas = []
        
        if len(snapshots) < 2:
            return improvement_areas
        
        # 比较最新和之前的快照
        latest = snapshots[-1]
        previous = snapshots[-2]
        
        # 找出合规分数下降的标准
        for latest_standard in latest['standards']:
            standard_id = latest_standard['standard_id']
            latest_score = latest_standard['compliance_score']
            
            for previous_standard in previous['standards']:
                if previous_standard['standard_id'] == standard_id:
                    previous_score = previous_standard['compliance_score']
                    if latest_score < previous_score - 0.05:
                        improvement_areas.append(f"{standard_id}: 合规分数从 {previous_score:.2%} 下降到 {latest_score:.2%}")
                    break
        
        return improvement_areas

class ComplianceReportGenerator:
    """合规报告生成器"""
    
    def __init__(self):
        self.template_path = Path("templates/compliance_report_template.md")
    
    def generate_compliance_report(self, compliance_statuses: List[ComplianceStatus], 
                                 trend_analysis: Dict[str, Any]) -> str:
        """生成合规报告"""
        report_content = f"""# OpenTelemetry 2025 标准合规监控报告

## 📊 报告概述

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**报告版本**: 1.0.0
**监控标准数量**: {len(compliance_statuses)}

## 📈 合规状态总览

### 总体合规情况
- **完全合规标准**: {sum(1 for status in compliance_statuses if status.compliance_level == ComplianceLevel.FULLY_COMPLIANT)}
- **基本合规标准**: {sum(1 for status in compliance_statuses if status.compliance_level == ComplianceLevel.MOSTLY_COMPLIANT)}
- **部分合规标准**: {sum(1 for status in compliance_statuses if status.compliance_level == ComplianceLevel.PARTIALLY_COMPLIANT)}
- **不合规标准**: {sum(1 for status in compliance_statuses if status.compliance_level == ComplianceLevel.NON_COMPLIANT)}
- **未评估标准**: {sum(1 for status in compliance_statuses if status.compliance_level == ComplianceLevel.NOT_ASSESSED)}

### 平均合规分数
- **总体平均分数**: {sum(status.compliance_score for status in compliance_statuses) / max(len(compliance_statuses), 1):.2%}

## 🔍 详细合规分析

### 各标准合规详情
"""
        
        # 添加各标准详细分析
        for status in compliance_statuses:
            report_content += f"""
#### {status.standard_name} ({status.standard_id})

- **合规级别**: {status.compliance_level.value}
- **合规分数**: {status.compliance_score:.2%}
- **要求总数**: {status.requirements_total}
- **已满足**: {status.requirements_met}
- **部分满足**: {status.requirements_partial}
- **未满足**: {status.requirements_not_met}
- **最后评估**: {status.last_assessment}
- **下次评估**: {status.next_assessment}

**问题**:
"""
            for issue in status.issues:
                report_content += f"- {issue}\n"
            
            report_content += "\n**建议**:\n"
            for recommendation in status.recommendations:
                report_content += f"- {recommendation}\n"
        
        # 添加趋势分析
        report_content += "\n## 📈 合规趋势分析\n\n"
        
        overall_trend = trend_analysis.get('overall_trend', {})
        if overall_trend.get('trend') != 'insufficient_data':
            report_content += f"### 总体趋势\n"
            report_content += f"- **趋势方向**: {overall_trend.get('trend', 'unknown')}\n"
            report_content += f"- **变化幅度**: {overall_trend.get('change', 0):.2%}\n"
            report_content += f"- **最新分数**: {overall_trend.get('latest_score', 0):.2%}\n"
            report_content += f"- **之前分数**: {overall_trend.get('previous_score', 0):.2%}\n\n"
        
        # 添加标准趋势
        standard_trends = trend_analysis.get('standard_trends', {})
        if standard_trends:
            report_content += "### 各标准趋势\n\n"
            for standard_id, trend_data in standard_trends.items():
                report_content += f"- **{standard_id}**: {trend_data.get('trend', 'unknown')} ({trend_data.get('change', 0):.2%})\n"
        
        # 添加改进建议
        report_content += "\n## 💡 改进建议\n\n"
        improvement_areas = trend_analysis.get('improvement_areas', [])
        if improvement_areas:
            for area in improvement_areas:
                report_content += f"- {area}\n"
        else:
            report_content += "- 所有标准合规状态良好，继续保持\n"
        
        # 添加结论
        report_content += f"""

## 📋 结论

基于本次合规监控，OpenTelemetry 2025项目在标准合规方面表现{'优秀' if sum(status.compliance_score for status in compliance_statuses) / max(len(compliance_statuses), 1) > 0.8 else '良好' if sum(status.compliance_score for status in compliance_statuses) / max(len(compliance_statuses), 1) > 0.6 else '需要改进'}。

### 主要成就
- 大部分标准达到基本合规或完全合规水平
- 标准对齐工作进展良好
- 合规管理体系逐步完善

### 需要关注的问题
- 部分标准需要进一步提高合规水平
- 某些合规要求需要更详细的实施计划
- 需要建立更完善的合规监控机制

### 下一步行动
1. 优先处理不合规和部分合规的标准
2. 完善合规要求的实施细节
3. 建立定期的合规评估机制
4. 加强合规培训和意识提升

---
*本报告由OpenTelemetry 2025标准合规监控系统生成*
"""
        
        return report_content

class StandardsComplianceMonitor:
    """标准合规监控主类"""
    
    def __init__(self, config_path: str = "config/international_standards_alignment.yaml"):
        self.compliance_checker = StandardsComplianceChecker(config_path)
        self.trend_analyzer = ComplianceTrendAnalyzer()
        self.report_generator = ComplianceReportGenerator()
    
    def run_compliance_monitoring(self) -> Dict[str, Any]:
        """运行合规监控"""
        logger.info("开始运行标准合规监控...")
        
        # 1. 检查所有标准的合规性
        compliance_statuses = []
        for standard_id in self.compliance_checker.standards_config.keys():
            status = self.compliance_checker.check_standard_compliance(standard_id)
            compliance_statuses.append(status)
        
        # 2. 保存合规快照
        self.trend_analyzer.save_compliance_snapshot(compliance_statuses)
        
        # 3. 分析合规趋势
        trend_analysis = self.trend_analyzer.analyze_compliance_trends()
        
        # 4. 生成合规报告
        report_content = self.report_generator.generate_compliance_report(
            compliance_statuses, trend_analysis
        )
        
        # 5. 保存报告
        self._save_compliance_report(report_content)
        
        logger.info("标准合规监控完成")
        
        return {
            'compliance_statuses': compliance_statuses,
            'trend_analysis': trend_analysis,
            'report_content': report_content
        }
    
    def _save_compliance_report(self, report_content: str):
        """保存合规报告"""
        try:
            # 创建报告目录
            report_dir = Path("reports")
            report_dir.mkdir(exist_ok=True)
            
            # 生成报告文件名
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            report_file = report_dir / f"standards_compliance_report_{timestamp}.md"
            
            # 保存报告
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report_content)
            
            logger.info(f"合规报告已保存到: {report_file}")
            
        except Exception as e:
            logger.error(f"保存合规报告失败: {e}")

def main():
    """主函数"""
    try:
        # 创建标准合规监控实例
        monitor = StandardsComplianceMonitor()
        
        # 运行合规监控
        results = monitor.run_compliance_monitoring()
        
        # 输出简要结果
        print("\n" + "="*60)
        print("OpenTelemetry 2025 标准合规监控结果")
        print("="*60)
        
        compliance_statuses = results['compliance_statuses']
        print(f"📋 监控标准数量: {len(compliance_statuses)}")
        
        # 统计合规级别
        level_counts = {}
        for status in compliance_statuses:
            level = status.compliance_level.value
            level_counts[level] = level_counts.get(level, 0) + 1
        
        print("📊 合规级别分布:")
        for level, count in level_counts.items():
            print(f"  - {level}: {count}")
        
        # 计算平均合规分数
        avg_score = sum(status.compliance_score for status in compliance_statuses) / max(len(compliance_statuses), 1)
        print(f"📈 平均合规分数: {avg_score:.2%}")
        
        # 显示趋势分析
        trend_analysis = results['trend_analysis']
        if trend_analysis.get('overall_trend', {}).get('trend') != 'insufficient_data':
            overall_trend = trend_analysis['overall_trend']
            print(f"📈 总体趋势: {overall_trend.get('trend', 'unknown')} ({overall_trend.get('change', 0):.2%})")
        
        print("\n详细报告已生成，请查看 reports/ 目录")
        print("="*60)
        
    except Exception as e:
        logger.error(f"运行标准合规监控时出错: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
