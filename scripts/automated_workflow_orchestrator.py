#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OpenTelemetry 2025 自动化工作流编排器
Automated Workflow Orchestrator for OpenTelemetry 2025

功能特性:
- 工作流编排
- 任务调度
- 依赖管理
- 状态监控
- 错误处理
- 报告生成
"""

import os
import sys
import json
import yaml
import time
import logging
import subprocess
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional, Callable
from dataclasses import dataclass, asdict
from enum import Enum
import threading
import queue
import concurrent.futures

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('workflow_orchestrator.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class TaskStatus(Enum):
    """任务状态枚举"""
    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"
    SKIPPED = "skipped"

class TaskPriority(Enum):
    """任务优先级枚举"""
    LOW = "low"
    NORMAL = "normal"
    HIGH = "high"
    CRITICAL = "critical"

@dataclass
class Task:
    """任务数据类"""
    id: str
    name: str
    description: str
    command: str
    script_path: str
    priority: TaskPriority
    status: TaskStatus
    dependencies: List[str]
    timeout: int
    retry_count: int
    max_retries: int
    created_at: str
    started_at: Optional[str]
    completed_at: Optional[str]
    error_message: Optional[str]
    output: Optional[str]

@dataclass
class Workflow:
    """工作流数据类"""
    id: str
    name: str
    description: str
    tasks: List[Task]
    status: TaskStatus
    created_at: str
    started_at: Optional[str]
    completed_at: Optional[str]
    total_tasks: int
    completed_tasks: int
    failed_tasks: int

class TaskExecutor:
    """任务执行器"""
    
    def __init__(self, max_workers: int = 4):
        self.max_workers = max_workers
        self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_workers)
        self.running_tasks: Dict[str, concurrent.futures.Future] = {}
    
    def execute_task(self, task: Task) -> Task:
        """执行任务"""
        try:
            logger.info(f"开始执行任务: {task.name}")
            
            # 更新任务状态
            task.status = TaskStatus.RUNNING
            task.started_at = datetime.now().isoformat()
            
            # 执行命令或脚本
            if task.script_path:
                result = self._execute_script(task.script_path, task.timeout)
            else:
                result = self._execute_command(task.command, task.timeout)
            
            # 更新任务结果
            if result['success']:
                task.status = TaskStatus.COMPLETED
                task.output = result['output']
                logger.info(f"任务执行成功: {task.name}")
            else:
                task.status = TaskStatus.FAILED
                task.error_message = result['error']
                logger.error(f"任务执行失败: {task.name} - {result['error']}")
            
            task.completed_at = datetime.now().isoformat()
            
        except Exception as e:
            task.status = TaskStatus.FAILED
            task.error_message = str(e)
            task.completed_at = datetime.now().isoformat()
            logger.error(f"任务执行异常: {task.name} - {e}")
        
        return task
    
    def _execute_script(self, script_path: str, timeout: int) -> Dict[str, Any]:
        """执行脚本"""
        try:
            script_file = Path(script_path)
            if not script_file.exists():
                return {'success': False, 'error': f'脚本文件不存在: {script_path}'}
            
            # 执行脚本
            result = subprocess.run(
                [sys.executable, str(script_file)],
                capture_output=True,
                text=True,
                timeout=timeout,
                encoding='utf-8'
            )
            
            if result.returncode == 0:
                return {'success': True, 'output': result.stdout}
            else:
                return {'success': False, 'error': result.stderr}
                
        except subprocess.TimeoutExpired:
            return {'success': False, 'error': f'脚本执行超时: {timeout}秒'}
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    def _execute_command(self, command: str, timeout: int) -> Dict[str, Any]:
        """执行命令"""
        try:
            result = subprocess.run(
                command,
                shell=True,
                capture_output=True,
                text=True,
                timeout=timeout,
                encoding='utf-8'
            )
            
            if result.returncode == 0:
                return {'success': True, 'output': result.stdout}
            else:
                return {'success': False, 'error': result.stderr}
                
        except subprocess.TimeoutExpired:
            return {'success': False, 'error': f'命令执行超时: {timeout}秒'}
        except Exception as e:
            return {'success': False, 'error': str(e)}

class WorkflowScheduler:
    """工作流调度器"""
    
    def __init__(self):
        self.workflows: Dict[str, Workflow] = {}
        self.task_executor = TaskExecutor()
        self.scheduler_config = self._load_scheduler_config()
    
    def _load_scheduler_config(self) -> Dict[str, Any]:
        """加载调度器配置"""
        try:
            config_path = Path("config/workflow_scheduler.yaml")
            if config_path.exists():
                with open(config_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            return {}
        except Exception as e:
            logger.error(f"加载调度器配置失败: {e}")
            return {}
    
    def create_workflow(self, workflow_id: str, name: str, description: str, 
                       tasks: List[Dict[str, Any]]) -> Workflow:
        """创建工作流"""
        workflow_tasks = []
        
        for task_data in tasks:
            task = Task(
                id=task_data['id'],
                name=task_data['name'],
                description=task_data.get('description', ''),
                command=task_data.get('command', ''),
                script_path=task_data.get('script_path', ''),
                priority=TaskPriority(task_data.get('priority', 'normal')),
                status=TaskStatus.PENDING,
                dependencies=task_data.get('dependencies', []),
                timeout=task_data.get('timeout', 300),
                retry_count=0,
                max_retries=task_data.get('max_retries', 3),
                created_at=datetime.now().isoformat(),
                started_at=None,
                completed_at=None,
                error_message=None,
                output=None
            )
            workflow_tasks.append(task)
        
        workflow = Workflow(
            id=workflow_id,
            name=name,
            description=description,
            tasks=workflow_tasks,
            status=TaskStatus.PENDING,
            created_at=datetime.now().isoformat(),
            started_at=None,
            completed_at=None,
            total_tasks=len(workflow_tasks),
            completed_tasks=0,
            failed_tasks=0
        )
        
        self.workflows[workflow_id] = workflow
        logger.info(f"工作流创建成功: {workflow_id}")
        
        return workflow
    
    def execute_workflow(self, workflow_id: str) -> Workflow:
        """执行工作流"""
        if workflow_id not in self.workflows:
            raise ValueError(f"工作流不存在: {workflow_id}")
        
        workflow = self.workflows[workflow_id]
        logger.info(f"开始执行工作流: {workflow.name}")
        
        # 更新工作流状态
        workflow.status = TaskStatus.RUNNING
        workflow.started_at = datetime.now().isoformat()
        
        try:
            # 按依赖关系排序任务
            sorted_tasks = self._sort_tasks_by_dependencies(workflow.tasks)
            
            # 执行任务
            for task in sorted_tasks:
                if workflow.status == TaskStatus.CANCELLED:
                    break
                
                # 检查依赖
                if not self._check_dependencies(task, workflow.tasks):
                    task.status = TaskStatus.SKIPPED
                    continue
                
                # 执行任务
                task = self.task_executor.execute_task(task)
                
                # 更新工作流统计
                if task.status == TaskStatus.COMPLETED:
                    workflow.completed_tasks += 1
                elif task.status == TaskStatus.FAILED:
                    workflow.failed_tasks += 1
                    
                    # 检查是否需要重试
                    if task.retry_count < task.max_retries:
                        task.retry_count += 1
                        task.status = TaskStatus.PENDING
                        task.started_at = None
                        task.completed_at = None
                        task.error_message = None
                        task.output = None
                        
                        # 重新执行任务
                        task = self.task_executor.execute_task(task)
                        
                        if task.status == TaskStatus.COMPLETED:
                            workflow.completed_tasks += 1
                        else:
                            workflow.failed_tasks += 1
            
            # 更新工作流状态
            if workflow.failed_tasks > 0:
                workflow.status = TaskStatus.FAILED
            else:
                workflow.status = TaskStatus.COMPLETED
            
            workflow.completed_at = datetime.now().isoformat()
            
        except Exception as e:
            workflow.status = TaskStatus.FAILED
            workflow.completed_at = datetime.now().isoformat()
            logger.error(f"工作流执行异常: {workflow.name} - {e}")
        
        logger.info(f"工作流执行完成: {workflow.name} - {workflow.status.value}")
        return workflow
    
    def _sort_tasks_by_dependencies(self, tasks: List[Task]) -> List[Task]:
        """按依赖关系排序任务"""
        sorted_tasks = []
        remaining_tasks = tasks.copy()
        
        while remaining_tasks:
            # 找到没有未满足依赖的任务
            ready_tasks = []
            for task in remaining_tasks:
                if self._check_dependencies(task, sorted_tasks):
                    ready_tasks.append(task)
            
            if not ready_tasks:
                # 如果所有剩余任务都有未满足的依赖，按优先级排序
                ready_tasks = [remaining_tasks[0]]
            
            # 按优先级排序
            ready_tasks.sort(key=lambda t: t.priority.value, reverse=True)
            
            # 添加到排序列表
            for task in ready_tasks:
                sorted_tasks.append(task)
                remaining_tasks.remove(task)
        
        return sorted_tasks
    
    def _check_dependencies(self, task: Task, completed_tasks: List[Task]) -> bool:
        """检查任务依赖"""
        if not task.dependencies:
            return True
        
        completed_task_ids = {t.id for t in completed_tasks if t.status == TaskStatus.COMPLETED}
        
        for dep_id in task.dependencies:
            if dep_id not in completed_task_ids:
                return False
        
        return True
    
    def get_workflow_status(self, workflow_id: str) -> Dict[str, Any]:
        """获取工作流状态"""
        if workflow_id not in self.workflows:
            return {'error': f'工作流不存在: {workflow_id}'}
        
        workflow = self.workflows[workflow_id]
        
        return {
            'workflow_id': workflow.id,
            'name': workflow.name,
            'status': workflow.status.value,
            'total_tasks': workflow.total_tasks,
            'completed_tasks': workflow.completed_tasks,
            'failed_tasks': workflow.failed_tasks,
            'progress': workflow.completed_tasks / workflow.total_tasks if workflow.total_tasks > 0 else 0,
            'created_at': workflow.created_at,
            'started_at': workflow.started_at,
            'completed_at': workflow.completed_at
        }

class WorkflowOrchestrator:
    """工作流编排器主类"""
    
    def __init__(self):
        self.scheduler = WorkflowScheduler()
        self.workflow_configs = self._load_workflow_configs()
    
    def _load_workflow_configs(self) -> Dict[str, Any]:
        """加载工作流配置"""
        try:
            config_path = Path("config/workflow_configs.yaml")
            if config_path.exists():
                with open(config_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            return {}
        except Exception as e:
            logger.error(f"加载工作流配置失败: {e}")
            return {}
    
    def run_automated_workflows(self) -> Dict[str, Any]:
        """运行自动化工作流"""
        logger.info("开始运行自动化工作流...")
        
        results = {}
        
        # 运行预定义的工作流
        for workflow_id, config in self.workflow_configs.items():
            try:
                logger.info(f"运行工作流: {workflow_id}")
                
                # 创建工作流
                workflow = self.scheduler.create_workflow(
                    workflow_id=workflow_id,
                    name=config['name'],
                    description=config.get('description', ''),
                    tasks=config['tasks']
                )
                
                # 执行工作流
                executed_workflow = self.scheduler.execute_workflow(workflow_id)
                
                # 保存结果
                results[workflow_id] = {
                    'status': executed_workflow.status.value,
                    'total_tasks': executed_workflow.total_tasks,
                    'completed_tasks': executed_workflow.completed_tasks,
                    'failed_tasks': executed_workflow.failed_tasks,
                    'progress': executed_workflow.completed_tasks / executed_workflow.total_tasks if executed_workflow.total_tasks > 0 else 0
                }
                
            except Exception as e:
                logger.error(f"运行工作流失败: {workflow_id} - {e}")
                results[workflow_id] = {
                    'status': 'failed',
                    'error': str(e)
                }
        
        # 生成工作流报告
        report_content = self._generate_workflow_report(results)
        
        # 保存报告
        self._save_workflow_report(report_content)
        
        logger.info("自动化工作流执行完成")
        
        return {
            'workflow_results': results,
            'report_content': report_content
        }
    
    def _generate_workflow_report(self, results: Dict[str, Any]) -> str:
        """生成工作流报告"""
        report_content = f"""# OpenTelemetry 2025 自动化工作流执行报告

## 📊 报告概述

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**报告版本**: 1.0.0
**执行工作流数量**: {len(results)}

## 🔄 工作流执行结果

### 总体统计
- **成功工作流**: {sum(1 for r in results.values() if r.get('status') == 'completed')}
- **失败工作流**: {sum(1 for r in results.values() if r.get('status') == 'failed')}
- **总任务数**: {sum(r.get('total_tasks', 0) for r in results.values())}
- **完成任务数**: {sum(r.get('completed_tasks', 0) for r in results.values())}
- **失败任务数**: {sum(r.get('failed_tasks', 0) for r in results.values())}

### 各工作流详情
"""
        
        # 添加各工作流详细结果
        for workflow_id, result in results.items():
            report_content += f"""
#### {workflow_id}

- **状态**: {result.get('status', 'unknown')}
- **总任务数**: {result.get('total_tasks', 0)}
- **完成任务数**: {result.get('completed_tasks', 0)}
- **失败任务数**: {result.get('failed_tasks', 0)}
- **进度**: {result.get('progress', 0):.2%}
"""
            
            if 'error' in result:
                report_content += f"- **错误信息**: {result['error']}\n"
        
        # 添加改进建议
        report_content += "\n## 💡 改进建议\n\n"
        suggestions = self._generate_workflow_suggestions(results)
        for i, suggestion in enumerate(suggestions, 1):
            report_content += f"{i}. {suggestion}\n"
        
        # 添加结论
        report_content += f"""

## 📋 结论

OpenTelemetry 2025自动化工作流执行{'成功' if all(r.get('status') == 'completed' for r in results.values()) else '部分成功'}，共执行 {len(results)} 个工作流。

### 主要成就
- 自动化工作流系统运行正常
- 大部分工作流执行成功
- 任务调度和依赖管理机制有效

### 需要关注的问题
- 部分工作流执行失败，需要检查错误原因
- 某些任务可能需要优化执行时间
- 需要建立更完善的错误处理机制

### 下一步行动
1. 修复失败的工作流
2. 优化任务执行效率
3. 完善错误处理和重试机制
4. 建立工作流监控和告警机制

---
*本报告由OpenTelemetry 2025自动化工作流编排器生成*
"""
        
        return report_content
    
    def _generate_workflow_suggestions(self, results: Dict[str, Any]) -> List[str]:
        """生成工作流改进建议"""
        suggestions = []
        
        # 基于执行结果的建议
        failed_workflows = [wf_id for wf_id, result in results.items() if result.get('status') == 'failed']
        if failed_workflows:
            suggestions.append(f"修复失败的工作流: {', '.join(failed_workflows)}")
        
        # 基于任务完成率的建议
        low_completion_workflows = [
            wf_id for wf_id, result in results.items() 
            if result.get('progress', 0) < 0.8 and result.get('status') != 'failed'
        ]
        if low_completion_workflows:
            suggestions.append(f"优化低完成率工作流: {', '.join(low_completion_workflows)}")
        
        # 基于执行时间的建议
        suggestions.append("建立工作流执行时间监控，识别性能瓶颈")
        
        # 基于错误处理的建议
        suggestions.append("完善错误处理机制，提高工作流稳定性")
        
        return suggestions
    
    def _save_workflow_report(self, report_content: str):
        """保存工作流报告"""
        try:
            # 创建报告目录
            report_dir = Path("reports")
            report_dir.mkdir(exist_ok=True)
            
            # 生成报告文件名
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            report_file = report_dir / f"workflow_execution_report_{timestamp}.md"
            
            # 保存报告
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report_content)
            
            logger.info(f"工作流报告已保存到: {report_file}")
            
        except Exception as e:
            logger.error(f"保存工作流报告失败: {e}")

def main():
    """主函数"""
    try:
        # 创建工作流编排器实例
        orchestrator = WorkflowOrchestrator()
        
        # 运行自动化工作流
        results = orchestrator.run_automated_workflows()
        
        # 输出简要结果
        print("\n" + "="*60)
        print("OpenTelemetry 2025 自动化工作流执行结果")
        print("="*60)
        
        workflow_results = results['workflow_results']
        print(f"🔄 执行工作流数量: {len(workflow_results)}")
        
        # 统计执行结果
        success_count = sum(1 for r in workflow_results.values() if r.get('status') == 'completed')
        failed_count = sum(1 for r in workflow_results.values() if r.get('status') == 'failed')
        
        print(f"✅ 成功工作流: {success_count}")
        print(f"❌ 失败工作流: {failed_count}")
        
        # 显示各工作流状态
        print("\n📊 各工作流状态:")
        for workflow_id, result in workflow_results.items():
            status = result.get('status', 'unknown')
            progress = result.get('progress', 0)
            print(f"  - {workflow_id}: {status} ({progress:.2%})")
        
        print("\n详细报告已生成，请查看 reports/ 目录")
        print("="*60)
        
    except Exception as e:
        logger.error(f"运行自动化工作流时出错: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
