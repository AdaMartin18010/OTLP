#!/usr/bin/env python3
"""
OpenTelemetry 2025年项目质量监控系统
基于国际标准对齐和知识体系的质量保证系统
"""

import os
import yaml
import json
import time
import hashlib
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional

class QualityMonitor:
    def __init__(self, config_path: str = "config/quality_monitor.yaml"):
        self.config = self.load_config(config_path)
        self.base_path = Path("doc")
        self.metrics = {}
        self.report_history = []
    
    def load_config(self, config_path: str) -> Dict[str, Any]:
        """加载质量监控配置"""
        if os.path.exists(config_path):
            with open(config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "quality_standards": {
                "documentation": {
                    "min_length": 100,
                    "max_age_days": 30,
                    "required_sections": ["概述", "核心内容", "参考文献"]
                },
                "standards_alignment": {
                    "coverage_threshold": 100,
                    "update_frequency_days": 30
                },
                "knowledge_completeness": {
                    "layers_required": 6,
                    "categories_per_layer": 3
                }
            },
            "monitoring": {
                "check_interval_hours": 24,
                "report_frequency": "daily",
                "alert_thresholds": {
                    "quality_score": 80,
                    "completion_rate": 90
                }
            }
        }
    
    def check_documentation_quality(self) -> Dict[str, Any]:
        """检查文档质量"""
        doc_path = Path("doc")
        quality_metrics = {
            "total_documents": 0,
            "valid_documents": 0,
            "outdated_documents": 0,
            "missing_documents": 0,
            "quality_score": 0,
            "details": []
        }
        
        for doc_file in doc_path.rglob("*.md"):
            quality_metrics["total_documents"] += 1
            
            doc_quality = self.analyze_document_quality(doc_file)
            quality_metrics["details"].append(doc_quality)
            
            if doc_quality["is_valid"]:
                quality_metrics["valid_documents"] += 1
            else:
                quality_metrics["missing_documents"] += 1
            
            if doc_quality["is_outdated"]:
                quality_metrics["outdated_documents"] += 1
        
        # 计算质量分数
        if quality_metrics["total_documents"] > 0:
            quality_metrics["quality_score"] = (
                quality_metrics["valid_documents"] / quality_metrics["total_documents"]
            ) * 100
        
        return quality_metrics
    
    def analyze_document_quality(self, doc_file: Path) -> Dict[str, Any]:
        """分析单个文档质量"""
        try:
            with open(doc_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 基本检查
            is_valid = len(content.strip()) > 0
            is_outdated = self.is_document_outdated(doc_file)
            
            # 内容分析
            word_count = len(content.split())
            has_required_sections = self.check_required_sections(content)
            has_references = "参考文献" in content or "References" in content
            
            # 计算文档质量分数
            quality_score = 0
            if is_valid:
                quality_score += 40
            if word_count >= 100:
                quality_score += 20
            if has_required_sections:
                quality_score += 20
            if has_references:
                quality_score += 20
            
            return {
                "file_path": str(doc_file),
                "is_valid": is_valid,
                "is_outdated": is_outdated,
                "word_count": word_count,
                "has_required_sections": has_required_sections,
                "has_references": has_references,
                "quality_score": quality_score,
                "last_modified": datetime.fromtimestamp(doc_file.stat().st_mtime).isoformat()
            }
        except Exception as e:
            return {
                "file_path": str(doc_file),
                "is_valid": False,
                "is_outdated": True,
                "error": str(e),
                "quality_score": 0
            }
    
    def is_document_outdated(self, doc_file: Path) -> bool:
        """检查文档是否过期"""
        try:
            stat = doc_file.stat()
            modified_time = datetime.fromtimestamp(stat.st_mtime)
            max_age = timedelta(days=self.config["quality_standards"]["documentation"]["max_age_days"])
            return datetime.now() - modified_time > max_age
        except:
            return True
    
    def check_required_sections(self, content: str) -> bool:
        """检查是否包含必需章节"""
        required_sections = self.config["quality_standards"]["documentation"]["required_sections"]
        return all(section in content for section in required_sections)
    
    def check_standards_alignment(self) -> Dict[str, Any]:
        """检查标准对齐情况"""
        alignment_metrics = {
            "total_standards": 0,
            "aligned_standards": 0,
            "partially_aligned": 0,
            "not_aligned": 0,
            "alignment_rate": 0,
            "details": []
        }
        
        # 加载标准对齐配置
        standards_config_path = "config/international_standards_alignment.yaml"
        if os.path.exists(standards_config_path):
            with open(standards_config_path, 'r', encoding='utf-8') as f:
                standards_config = yaml.safe_load(f)
            
            # 检查各类标准
            for category, standards in standards_config.items():
                if isinstance(standards, dict):
                    for standard_name, standard_info in standards.items():
                        if isinstance(standard_info, dict) and "alignment_status" in standard_info:
                            alignment_metrics["total_standards"] += 1
                            
                            alignment_status = standard_info.get("alignment_status", "not_aligned")
                            alignment_metrics["details"].append({
                                "category": category,
                                "standard": standard_name,
                                "status": alignment_status,
                                "name": standard_info.get("name", standard_name)
                            })
                            
                            if alignment_status == "100%":
                                alignment_metrics["aligned_standards"] += 1
                            elif "部分" in alignment_status or "partial" in alignment_status.lower():
                                alignment_metrics["partially_aligned"] += 1
                            else:
                                alignment_metrics["not_aligned"] += 1
        
        # 计算对齐率
        if alignment_metrics["total_standards"] > 0:
            alignment_metrics["alignment_rate"] = (
                alignment_metrics["aligned_standards"] / alignment_metrics["total_standards"]
            ) * 100
        
        return alignment_metrics
    
    def check_knowledge_completeness(self) -> Dict[str, Any]:
        """检查知识完整性"""
        knowledge_metrics = {
            "total_layers": 6,
            "completed_layers": 0,
            "total_categories": 0,
            "completed_categories": 0,
            "completion_rate": 0,
            "details": []
        }
        
        knowledge_path = Path("doc/02_知识体系")
        if knowledge_path.exists():
            for layer_path in knowledge_path.iterdir():
                if layer_path.is_dir() and layer_path.name.startswith(("01_", "02_", "03_", "04_", "05_", "06_")):
                    layer_complete = self.is_layer_complete(layer_path)
                    layer_info = {
                        "layer_name": layer_path.name,
                        "is_complete": layer_complete,
                        "categories": []
                    }
                    
                    if layer_complete:
                        knowledge_metrics["completed_layers"] += 1
                    
                    # 检查分类完整性
                    categories = [d for d in layer_path.iterdir() if d.is_dir()]
                    knowledge_metrics["total_categories"] += len(categories)
                    
                    for category in categories:
                        category_complete = self.is_category_complete(category)
                        layer_info["categories"].append({
                            "name": category.name,
                            "is_complete": category_complete
                        })
                        
                        if category_complete:
                            knowledge_metrics["completed_categories"] += 1
                    
                    knowledge_metrics["details"].append(layer_info)
        
        # 计算完成率
        if knowledge_metrics["total_layers"] > 0:
            knowledge_metrics["completion_rate"] = (
                knowledge_metrics["completed_layers"] / knowledge_metrics["total_layers"]
            ) * 100
        
        return knowledge_metrics
    
    def is_layer_complete(self, layer_path: Path) -> bool:
        """检查层级是否完整"""
        required_files = ["README.md"]
        for file_name in required_files:
            if not (layer_path / file_name).exists():
                return False
        return True
    
    def is_category_complete(self, category_path: Path) -> bool:
        """检查分类是否完整"""
        required_files = ["README.md"]
        for file_name in required_files:
            if not (category_path / file_name).exists():
                return False
        return True
    
    def check_academic_collaboration(self) -> Dict[str, Any]:
        """检查学术合作情况"""
        collaboration_metrics = {
            "total_universities": 0,
            "active_collaborations": 0,
            "total_projects": 0,
            "active_projects": 0,
            "collaboration_rate": 0,
            "details": []
        }
        
        # 加载学术合作配置
        collaboration_config_path = "config/academic_collaboration.yaml"
        if os.path.exists(collaboration_config_path):
            with open(collaboration_config_path, 'r', encoding='utf-8') as f:
                collaboration_config = yaml.safe_load(f)
            
            universities = collaboration_config.get("universities", {})
            collaboration_metrics["total_universities"] = len(universities)
            
            for uni_name, uni_info in universities.items():
                if isinstance(uni_info, dict):
                    projects = uni_info.get("projects", [])
                    collaboration_metrics["total_projects"] += len(projects)
                    
                    active_projects = [p for p in projects if p.get("status") in ["active", "planning"]]
                    collaboration_metrics["active_projects"] += len(active_projects)
                    
                    if len(active_projects) > 0:
                        collaboration_metrics["active_collaborations"] += 1
                    
                    collaboration_metrics["details"].append({
                        "university": uni_name,
                        "name": uni_info.get("name", uni_name),
                        "total_projects": len(projects),
                        "active_projects": len(active_projects),
                        "status": "active" if len(active_projects) > 0 else "inactive"
                    })
        
        # 计算合作率
        if collaboration_metrics["total_universities"] > 0:
            collaboration_metrics["collaboration_rate"] = (
                collaboration_metrics["active_collaborations"] / collaboration_metrics["total_universities"]
            ) * 100
        
        return collaboration_metrics
    
    def generate_quality_report(self) -> Dict[str, Any]:
        """生成质量报告"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "report_id": self.generate_report_id(),
            "documentation_quality": self.check_documentation_quality(),
            "standards_alignment": self.check_standards_alignment(),
            "knowledge_completeness": self.check_knowledge_completeness(),
            "academic_collaboration": self.check_academic_collaboration()
        }
        
        # 计算总体质量分数
        doc_quality = report["documentation_quality"]["quality_score"]
        std_quality = report["standards_alignment"]["alignment_rate"]
        know_quality = report["knowledge_completeness"]["completion_rate"]
        collab_quality = report["academic_collaboration"]["collaboration_rate"]
        
        overall_score = (doc_quality + std_quality + know_quality + collab_quality) / 4
        report["overall_quality_score"] = overall_score
        
        # 质量等级评估
        if overall_score >= 90:
            report["quality_grade"] = "A+"
        elif overall_score >= 80:
            report["quality_grade"] = "A"
        elif overall_score >= 70:
            report["quality_grade"] = "B"
        elif overall_score >= 60:
            report["quality_grade"] = "C"
        else:
            report["quality_grade"] = "D"
        
        # 改进建议
        report["improvement_recommendations"] = self.generate_improvement_recommendations(report)
        
        return report
    
    def generate_report_id(self) -> str:
        """生成报告ID"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        return f"QR_{timestamp}"
    
    def generate_improvement_recommendations(self, report: Dict[str, Any]) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        # 文档质量改进建议
        doc_quality = report["documentation_quality"]["quality_score"]
        if doc_quality < 80:
            recommendations.append("提高文档质量：增加文档内容，确保包含必需章节和参考文献")
        
        if report["documentation_quality"]["outdated_documents"] > 0:
            recommendations.append(f"更新过期文档：{report['documentation_quality']['outdated_documents']}个文档需要更新")
        
        # 标准对齐改进建议
        std_quality = report["standards_alignment"]["alignment_rate"]
        if std_quality < 100:
            recommendations.append("完善标准对齐：确保所有标准100%对齐")
        
        # 知识完整性改进建议
        know_quality = report["knowledge_completeness"]["completion_rate"]
        if know_quality < 100:
            recommendations.append("完善知识体系：完成所有层级和分类的内容")
        
        # 学术合作改进建议
        collab_quality = report["academic_collaboration"]["collaboration_rate"]
        if collab_quality < 50:
            recommendations.append("加强学术合作：增加与大学的合作项目")
        
        return recommendations
    
    def save_quality_report(self, report: Dict[str, Any]) -> str:
        """保存质量报告"""
        report_path = Path("reports/quality_reports")
        report_path.mkdir(parents=True, exist_ok=True)
        
        # 保存详细报告
        report_file = report_path / f"quality_report_{report['report_id']}.json"
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        # 更新最新报告
        latest_report = report_path / "latest_quality_report.json"
        with open(latest_report, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        # 保存报告历史
        self.report_history.append(report)
        history_file = report_path / "quality_report_history.json"
        with open(history_file, 'w', encoding='utf-8') as f:
            json.dump(self.report_history, f, indent=2, ensure_ascii=False)
        
        return str(report_file)
    
    def print_quality_summary(self, report: Dict[str, Any]):
        """打印质量摘要"""
        print("=" * 60)
        print("OpenTelemetry 2025年项目质量监控报告")
        print("=" * 60)
        print(f"报告时间: {report['timestamp']}")
        print(f"报告ID: {report['report_id']}")
        print(f"总体质量分数: {report['overall_quality_score']:.2f}")
        print(f"质量等级: {report['quality_grade']}")
        print()
        
        print("📊 详细指标:")
        print(f"  文档质量: {report['documentation_quality']['quality_score']:.2f}")
        print(f"  标准对齐: {report['standards_alignment']['alignment_rate']:.2f}")
        print(f"  知识完整性: {report['knowledge_completeness']['completion_rate']:.2f}")
        print(f"  学术合作: {report['academic_collaboration']['collaboration_rate']:.2f}")
        print()
        
        print("📈 统计信息:")
        print(f"  总文档数: {report['documentation_quality']['total_documents']}")
        print(f"  有效文档: {report['documentation_quality']['valid_documents']}")
        print(f"  过期文档: {report['documentation_quality']['outdated_documents']}")
        print(f"  总标准数: {report['standards_alignment']['total_standards']}")
        print(f"  已对齐标准: {report['standards_alignment']['aligned_standards']}")
        print(f"  完成层级: {report['knowledge_completeness']['completed_layers']}/{report['knowledge_completeness']['total_layers']}")
        print(f"  合作大学: {report['academic_collaboration']['active_collaborations']}/{report['academic_collaboration']['total_universities']}")
        print()
        
        if report["improvement_recommendations"]:
            print("💡 改进建议:")
            for i, recommendation in enumerate(report["improvement_recommendations"], 1):
                print(f"  {i}. {recommendation}")
        print()
        print("=" * 60)

def main():
    """主函数"""
    monitor = QualityMonitor()
    
    print("开始质量监控检查...")
    report = monitor.generate_quality_report()
    
    print("保存质量报告...")
    report_file = monitor.save_quality_report(report)
    
    print("生成质量摘要...")
    monitor.print_quality_summary(report)
    
    print(f"详细报告已保存至: {report_file}")
    
    # 检查是否需要告警
    if report["overall_quality_score"] < monitor.config["monitoring"]["alert_thresholds"]["quality_score"]:
        print("⚠️  警告: 质量分数低于阈值，需要关注!")
    
    if report["knowledge_completeness"]["completion_rate"] < monitor.config["monitoring"]["alert_thresholds"]["completion_rate"]:
        print("⚠️  警告: 完成率低于阈值，需要关注!")

if __name__ == "__main__":
    main()
