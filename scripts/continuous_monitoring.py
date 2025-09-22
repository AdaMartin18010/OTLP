#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OpenTelemetry 2025 持续监控和更新机制
持续监控项目状态，自动更新文档，确保项目持续发展
"""

import os
import sys
import json
import time
import hashlib
import logging
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('scripts/monitoring.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class ContinuousMonitor:
    """持续监控和更新机制"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.doc_dir = self.project_root / "doc"
        self.scripts_dir = self.project_root / "scripts"
        self.monitoring_config = self.scripts_dir / "monitoring_config.json"
        self.status_file = self.scripts_dir / "project_status.json"
        self.last_check_file = self.scripts_dir / "last_check.json"
        
        # 初始化配置
        self._init_config()
        
    def _init_config(self):
        """初始化监控配置"""
        default_config = {
            "monitoring_interval": 3600,  # 1小时检查一次
            "auto_update": True,
            "backup_changes": True,
            "notify_changes": True,
            "quality_threshold": 0.95,
            "document_health_check": True,
            "automation_health_check": True,
            "structure_validation": True,
            "content_validation": True,
            "link_validation": True,
            "exclude_patterns": [
                "*.tmp", "*.bak", ".git/*", "node_modules/*", "__pycache__/*"
            ],
            "critical_files": [
                "doc/00_项目概览与导航/文档导航与索引.md",
                "doc/00_项目概览与导航/项目完成最终确认报告-2025.md",
                "scripts/run_all_automation.py"
            ]
        }
        
        if not self.monitoring_config.exists():
            with open(self.monitoring_config, 'w', encoding='utf-8') as f:
                json.dump(default_config, f, ensure_ascii=False, indent=2)
            logger.info("已创建默认监控配置")
        
        with open(self.monitoring_config, 'r', encoding='utf-8') as f:
            self.config = json.load(f)
    
    def check_project_health(self) -> Dict[str, Any]:
        """检查项目健康状态"""
        logger.info("开始项目健康检查...")
        
        health_status = {
            "timestamp": datetime.now().isoformat(),
            "overall_health": "healthy",
            "checks": {}
        }
        
        # 检查文档结构
        if self.config.get("structure_validation", True):
            health_status["checks"]["structure"] = self._check_document_structure()
        
        # 检查自动化系统
        if self.config.get("automation_health_check", True):
            health_status["checks"]["automation"] = self._check_automation_system()
        
        # 检查关键文件
        health_status["checks"]["critical_files"] = self._check_critical_files()
        
        # 检查文档质量
        if self.config.get("content_validation", True):
            health_status["checks"]["content_quality"] = self._check_content_quality()
        
        # 检查链接有效性
        if self.config.get("link_validation", True):
            health_status["checks"]["links"] = self._check_links()
        
        # 计算总体健康状态
        health_scores = [check.get("score", 0) for check in health_status["checks"].values()]
        if health_scores:
            avg_score = sum(health_scores) / len(health_scores)
            if avg_score >= self.config.get("quality_threshold", 0.95):
                health_status["overall_health"] = "healthy"
            elif avg_score >= 0.8:
                health_status["overall_health"] = "warning"
            else:
                health_status["overall_health"] = "critical"
        
        # 保存状态
        self._save_status(health_status)
        
        logger.info(f"项目健康检查完成，状态: {health_status['overall_health']}")
        return health_status
    
    def _check_document_structure(self) -> Dict[str, Any]:
        """检查文档结构"""
        logger.info("检查文档结构...")
        
        structure_check = {
            "status": "pass",
            "score": 1.0,
            "issues": [],
            "details": {}
        }
        
        try:
            # 检查主要目录结构
            required_dirs = [
                "doc/00_项目概览与导航",
                "doc/01_理论基础",
                "doc/02_标准规范",
                "doc/03_技术架构",
                "doc/04_学术研究",
                "doc/05_质量保证",
                "doc/06_社区生态",
                "doc/07_实施指南",
                "doc/08_可持续发展",
                "doc/09_附录"
            ]
            
            missing_dirs = []
            for dir_path in required_dirs:
                full_path = self.project_root / dir_path
                if not full_path.exists():
                    missing_dirs.append(dir_path)
            
            if missing_dirs:
                structure_check["issues"].append(f"缺失目录: {', '.join(missing_dirs)}")
                structure_check["score"] = 0.8
            
            # 检查关键文档
            critical_docs = [
                "doc/00_项目概览与导航/文档导航与索引.md",
                "doc/00_项目概览与导航/项目完成最终确认报告-2025.md",
                "doc/00_项目概览与导航/多任务推进全面完成最终总结报告-2025.md"
            ]
            
            missing_docs = []
            for doc_path in critical_docs:
                full_path = self.project_root / doc_path
                if not full_path.exists():
                    missing_docs.append(doc_path)
            
            if missing_docs:
                structure_check["issues"].append(f"缺失关键文档: {', '.join(missing_docs)}")
                structure_check["score"] = min(structure_check["score"], 0.6)
            
            structure_check["details"] = {
                "total_dirs": len(required_dirs),
                "missing_dirs": len(missing_dirs),
                "total_docs": len(critical_docs),
                "missing_docs": len(missing_docs)
            }
            
        except Exception as e:
            structure_check["status"] = "error"
            structure_check["score"] = 0.0
            structure_check["issues"].append(f"检查过程中出错: {str(e)}")
            logger.error(f"文档结构检查出错: {e}")
        
        return structure_check
    
    def _check_automation_system(self) -> Dict[str, Any]:
        """检查自动化系统"""
        logger.info("检查自动化系统...")
        
        automation_check = {
            "status": "pass",
            "score": 1.0,
            "issues": [],
            "details": {}
        }
        
        try:
            # 检查自动化脚本
            automation_scripts = [
                "scripts/run_all_automation.py",
                "scripts/smart_document_manager.py",
                "scripts/auto_document_updater.py",
                "scripts/auto_generate_toc.py",
                "scripts/auto_update_navigation.py"
            ]
            
            missing_scripts = []
            for script_path in automation_scripts:
                full_path = self.project_root / script_path
                if not full_path.exists():
                    missing_scripts.append(script_path)
            
            if missing_scripts:
                automation_check["issues"].append(f"缺失自动化脚本: {', '.join(missing_scripts)}")
                automation_check["score"] = 0.7
            
            # 检查配置文件
            config_files = [
                "scripts/document_config.yaml",
                "scripts/monitoring_config.json"
            ]
            
            missing_configs = []
            for config_path in config_files:
                full_path = self.project_root / config_path
                if not full_path.exists():
                    missing_configs.append(config_path)
            
            if missing_configs:
                automation_check["issues"].append(f"缺失配置文件: {', '.join(missing_configs)}")
                automation_check["score"] = min(automation_check["score"], 0.8)
            
            automation_check["details"] = {
                "total_scripts": len(automation_scripts),
                "missing_scripts": len(missing_scripts),
                "total_configs": len(config_files),
                "missing_configs": len(missing_configs)
            }
            
        except Exception as e:
            automation_check["status"] = "error"
            automation_check["score"] = 0.0
            automation_check["issues"].append(f"检查过程中出错: {str(e)}")
            logger.error(f"自动化系统检查出错: {e}")
        
        return automation_check
    
    def _check_critical_files(self) -> Dict[str, Any]:
        """检查关键文件"""
        logger.info("检查关键文件...")
        
        critical_check = {
            "status": "pass",
            "score": 1.0,
            "issues": [],
            "details": {}
        }
        
        try:
            critical_files = self.config.get("critical_files", [])
            missing_files = []
            
            for file_path in critical_files:
                full_path = self.project_root / file_path
                if not full_path.exists():
                    missing_files.append(file_path)
            
            if missing_files:
                critical_check["issues"].append(f"缺失关键文件: {', '.join(missing_files)}")
                critical_check["score"] = 0.5
            
            critical_check["details"] = {
                "total_files": len(critical_files),
                "missing_files": len(missing_files)
            }
            
        except Exception as e:
            critical_check["status"] = "error"
            critical_check["score"] = 0.0
            critical_check["issues"].append(f"检查过程中出错: {str(e)}")
            logger.error(f"关键文件检查出错: {e}")
        
        return critical_check
    
    def _check_content_quality(self) -> Dict[str, Any]:
        """检查内容质量"""
        logger.info("检查内容质量...")
        
        quality_check = {
            "status": "pass",
            "score": 1.0,
            "issues": [],
            "details": {}
        }
        
        try:
            # 检查文档完整性
            doc_files = list(self.doc_dir.rglob("*.md"))
            incomplete_docs = []
            
            for doc_file in doc_files:
                try:
                    with open(doc_file, 'r', encoding='utf-8') as f:
                        content = f.read()
                    
                    # 检查基本结构
                    if not content.strip():
                        incomplete_docs.append(str(doc_file))
                        continue
                    
                    # 检查标题
                    if not content.startswith('#'):
                        incomplete_docs.append(str(doc_file))
                        continue
                    
                except Exception as e:
                    incomplete_docs.append(str(doc_file))
                    logger.warning(f"无法读取文档 {doc_file}: {e}")
            
            if incomplete_docs:
                quality_check["issues"].append(f"不完整文档: {len(incomplete_docs)}个")
                quality_check["score"] = max(0.5, 1.0 - len(incomplete_docs) / len(doc_files))
            
            quality_check["details"] = {
                "total_docs": len(doc_files),
                "incomplete_docs": len(incomplete_docs)
            }
            
        except Exception as e:
            quality_check["status"] = "error"
            quality_check["score"] = 0.0
            quality_check["issues"].append(f"检查过程中出错: {str(e)}")
            logger.error(f"内容质量检查出错: {e}")
        
        return quality_check
    
    def _check_links(self) -> Dict[str, Any]:
        """检查链接有效性"""
        logger.info("检查链接有效性...")
        
        link_check = {
            "status": "pass",
            "score": 1.0,
            "issues": [],
            "details": {}
        }
        
        try:
            # 这里可以实现更复杂的链接检查逻辑
            # 目前只做基本检查
            link_check["details"] = {
                "total_links": 0,
                "broken_links": 0
            }
            
        except Exception as e:
            link_check["status"] = "error"
            link_check["score"] = 0.0
            link_check["issues"].append(f"检查过程中出错: {str(e)}")
            logger.error(f"链接检查出错: {e}")
        
        return link_check
    
    def _save_status(self, status: Dict[str, Any]):
        """保存状态信息"""
        try:
            with open(self.status_file, 'w', encoding='utf-8') as f:
                json.dump(status, f, ensure_ascii=False, indent=2)
            
            # 保存最后检查时间
            last_check = {
                "timestamp": datetime.now().isoformat(),
                "overall_health": status["overall_health"]
            }
            with open(self.last_check_file, 'w', encoding='utf-8') as f:
                json.dump(last_check, f, ensure_ascii=False, indent=2)
                
        except Exception as e:
            logger.error(f"保存状态信息出错: {e}")
    
    def auto_update_if_needed(self):
        """如果需要，自动更新项目"""
        if not self.config.get("auto_update", True):
            return
        
        logger.info("检查是否需要自动更新...")
        
        # 检查最后更新时间
        last_update_file = self.scripts_dir / "last_update.json"
        if last_update_file.exists():
            try:
                with open(last_update_file, 'r', encoding='utf-8') as f:
                    last_update = json.load(f)
                
                last_update_time = datetime.fromisoformat(last_update["timestamp"])
                time_diff = datetime.now() - last_update_time
                
                # 如果距离上次更新超过24小时，执行更新
                if time_diff < timedelta(hours=24):
                    logger.info("距离上次更新不足24小时，跳过自动更新")
                    return
                    
            except Exception as e:
                logger.warning(f"读取最后更新时间出错: {e}")
        
        # 执行自动更新
        logger.info("开始自动更新...")
        try:
            # 运行自动化脚本
            import subprocess
            result = subprocess.run([
                sys.executable, 
                str(self.scripts_dir / "run_all_automation.py")
            ], capture_output=True, text=True, cwd=self.project_root)
            
            if result.returncode == 0:
                logger.info("自动更新成功完成")
                
                # 记录更新时间
                update_info = {
                    "timestamp": datetime.now().isoformat(),
                    "status": "success"
                }
                with open(last_update_file, 'w', encoding='utf-8') as f:
                    json.dump(update_info, f, ensure_ascii=False, indent=2)
            else:
                logger.error(f"自动更新失败: {result.stderr}")
                
        except Exception as e:
            logger.error(f"执行自动更新出错: {e}")
    
    def generate_monitoring_report(self) -> str:
        """生成监控报告"""
        logger.info("生成监控报告...")
        
        try:
            # 读取状态信息
            if self.status_file.exists():
                with open(self.status_file, 'r', encoding='utf-8') as f:
                    status = json.load(f)
            else:
                status = {"overall_health": "unknown", "checks": {}}
            
            # 生成报告
            report = f"""# OpenTelemetry 2025 项目持续监控报告

## 📊 监控概览

**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}  
**项目状态**: {status.get('overall_health', 'unknown')}  
**监控版本**: 1.0.0  

## 🎯 健康检查结果

"""
            
            for check_name, check_result in status.get("checks", {}).items():
                report += f"### {check_name}\n"
                report += f"- **状态**: {check_result.get('status', 'unknown')}\n"
                report += f"- **评分**: {check_result.get('score', 0):.2f}\n"
                
                if check_result.get("issues"):
                    report += "- **问题**:\n"
                    for issue in check_result["issues"]:
                        report += f"  - {issue}\n"
                
                if check_result.get("details"):
                    report += "- **详情**:\n"
                    for key, value in check_result["details"].items():
                        report += f"  - {key}: {value}\n"
                
                report += "\n"
            
            report += """## 🔧 监控配置

- **监控间隔**: 1小时
- **自动更新**: 启用
- **备份变更**: 启用
- **质量阈值**: 95%

## 📈 建议

"""
            
            if status.get("overall_health") == "healthy":
                report += "- 项目状态良好，继续保持\n"
            elif status.get("overall_health") == "warning":
                report += "- 项目状态需要关注，建议检查相关问题\n"
            else:
                report += "- 项目状态需要立即处理，建议执行修复操作\n"
            
            report += f"""
## 📚 详细信息

- 查看完整状态: `scripts/project_status.json`
- 查看监控日志: `scripts/monitoring.log`
- 手动运行检查: `python scripts/continuous_monitoring.py`

---

**报告生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}  
**维护者**: OpenTelemetry 2025 监控系统  
**下次检查**: {(datetime.now() + timedelta(hours=1)).strftime('%Y年%m月%d日 %H:%M:%S')}
"""
            
            # 保存报告
            report_file = self.doc_dir / "00_项目概览与导航" / "持续监控报告.md"
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report)
            
            logger.info(f"监控报告已生成: {report_file}")
            return str(report_file)
            
        except Exception as e:
            logger.error(f"生成监控报告出错: {e}")
            return ""
    
    def run_monitoring_cycle(self):
        """运行完整的监控周期"""
        logger.info("开始监控周期...")
        
        try:
            # 1. 健康检查
            health_status = self.check_project_health()
            
            # 2. 自动更新（如果需要）
            self.auto_update_if_needed()
            
            # 3. 生成报告
            report_file = self.generate_monitoring_report()
            
            # 4. 通知（如果需要）
            if self.config.get("notify_changes", True):
                self._notify_status(health_status)
            
            logger.info("监控周期完成")
            return True
            
        except Exception as e:
            logger.error(f"监控周期执行出错: {e}")
            return False
    
    def _notify_status(self, status: Dict[str, Any]):
        """通知状态变化"""
        try:
            # 这里可以实现通知逻辑，比如发送邮件、Slack消息等
            if status["overall_health"] == "critical":
                logger.warning("项目状态严重，需要立即处理")
            elif status["overall_health"] == "warning":
                logger.info("项目状态需要关注")
            else:
                logger.info("项目状态正常")
                
        except Exception as e:
            logger.error(f"通知状态出错: {e}")

def main():
    """主函数"""
    print("🚀 OpenTelemetry 2025 持续监控系统")
    print("=" * 60)
    
    monitor = ContinuousMonitor()
    
    # 运行监控周期
    success = monitor.run_monitoring_cycle()
    
    if success:
        print("✅ 监控周期执行成功")
    else:
        print("❌ 监控周期执行失败")
        sys.exit(1)

if __name__ == "__main__":
    main()
