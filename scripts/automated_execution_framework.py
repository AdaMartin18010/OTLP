#!/usr/bin/env python3
"""
OpenTelemetry 自动化执行框架
统一管理所有自动化任务和流程
"""

import os
import sys
import json
import yaml
import logging
import subprocess
from datetime import datetime
from typing import Dict, List, Any, Optional
from pathlib import Path
import concurrent.futures
import threading

class AutomatedExecutionFramework:
    """自动化执行框架"""
    
    def __init__(self, config_file: str = "config/execution_config.yaml"):
        self.config_file = config_file
        self.config = self.load_config()
        self.logger = self.setup_logging()
        self.execution_status = {}
        self.lock = threading.Lock()
    
    def load_config(self) -> Dict[str, Any]:
        """加载配置文件"""
        try:
            with open(self.config_file, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            self.logger.warning(f"配置文件 {self.config_file} 不存在，使用默认配置")
            return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            'execution': {
                'parallel_tasks': 4,
                'timeout': 3600,
                'retry_count': 3,
                'log_level': 'INFO'
            },
            'tasks': {
                'document_restructure': {
                    'enabled': True,
                    'priority': 1,
                    'script': 'scripts/document_restructure.py',
                    'dependencies': []
                },
                'formal_verification': {
                    'enabled': True,
                    'priority': 2,
                    'script': 'scripts/formal_verification.py',
                    'dependencies': ['document_restructure']
                },
                'case_studies': {
                    'enabled': True,
                    'priority': 3,
                    'script': 'scripts/case_studies_collection.py',
                    'dependencies': []
                },
                'community_building': {
                    'enabled': True,
                    'priority': 4,
                    'script': 'scripts/community_building.py',
                    'dependencies': ['case_studies']
                },
                'quality_assurance': {
                    'enabled': True,
                    'priority': 5,
                    'script': 'scripts/quality_assurance.py',
                    'dependencies': ['document_restructure', 'formal_verification']
                }
            }
        }
    
    def setup_logging(self) -> logging.Logger:
        """设置日志"""
        logger = logging.getLogger('AutomatedExecution')
        logger.setLevel(getattr(logging, self.config.get('execution', {}).get('log_level', 'INFO')))
        
        # 创建日志目录
        log_dir = Path('logs')
        log_dir.mkdir(exist_ok=True)
        
        # 文件处理器
        file_handler = logging.FileHandler(
            log_dir / f'execution_{datetime.now().strftime("%Y%m%d_%H%M%S")}.log',
            encoding='utf-8'
        )
        file_handler.setLevel(logging.DEBUG)
        
        # 控制台处理器
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        
        # 格式化器
        formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        file_handler.setFormatter(formatter)
        console_handler.setFormatter(formatter)
        
        logger.addHandler(file_handler)
        logger.addHandler(console_handler)
        
        return logger
    
    def execute_task(self, task_name: str, task_config: Dict[str, Any]) -> Dict[str, Any]:
        """执行单个任务"""
        start_time = datetime.now()
        self.logger.info(f"开始执行任务: {task_name}")
        
        try:
            # 检查依赖
            if not self.check_dependencies(task_name, task_config.get('dependencies', [])):
                raise Exception(f"任务 {task_name} 的依赖未满足")
            
            # 执行脚本
            script_path = task_config.get('script')
            if not script_path or not os.path.exists(script_path):
                raise Exception(f"脚本 {script_path} 不存在")
            
            # 运行脚本
            result = subprocess.run(
                [sys.executable, script_path],
                capture_output=True,
                text=True,
                timeout=self.config.get('execution', {}).get('timeout', 3600)
            )
            
            end_time = datetime.now()
            duration = (end_time - start_time).total_seconds()
            
            if result.returncode == 0:
                self.logger.info(f"任务 {task_name} 执行成功，耗时 {duration:.2f} 秒")
                status = {
                    'status': 'success',
                    'start_time': start_time.isoformat(),
                    'end_time': end_time.isoformat(),
                    'duration': duration,
                    'output': result.stdout,
                    'error': result.stderr
                }
            else:
                self.logger.error(f"任务 {task_name} 执行失败，返回码: {result.returncode}")
                status = {
                    'status': 'failed',
                    'start_time': start_time.isoformat(),
                    'end_time': end_time.isoformat(),
                    'duration': duration,
                    'output': result.stdout,
                    'error': result.stderr,
                    'return_code': result.returncode
                }
            
        except subprocess.TimeoutExpired:
            self.logger.error(f"任务 {task_name} 执行超时")
            status = {
                'status': 'timeout',
                'start_time': start_time.isoformat(),
                'end_time': datetime.now().isoformat(),
                'duration': self.config.get('execution', {}).get('timeout', 3600),
                'error': 'Task execution timeout'
            }
        except Exception as e:
            self.logger.error(f"任务 {task_name} 执行异常: {str(e)}")
            status = {
                'status': 'error',
                'start_time': start_time.isoformat(),
                'end_time': datetime.now().isoformat(),
                'duration': (datetime.now() - start_time).total_seconds(),
                'error': str(e)
            }
        
        # 更新执行状态
        with self.lock:
            self.execution_status[task_name] = status
        
        return status
    
    def check_dependencies(self, task_name: str, dependencies: List[str]) -> bool:
        """检查任务依赖"""
        if not dependencies:
            return True
        
        with self.lock:
            for dep in dependencies:
                if dep not in self.execution_status:
                    self.logger.warning(f"任务 {task_name} 的依赖 {dep} 未执行")
                    return False
                
                if self.execution_status[dep]['status'] != 'success':
                    self.logger.warning(f"任务 {task_name} 的依赖 {dep} 执行失败")
                    return False
        
        return True
    
    def execute_parallel_tasks(self, tasks: List[str]) -> Dict[str, Any]:
        """并行执行任务"""
        self.logger.info(f"开始并行执行 {len(tasks)} 个任务")
        
        max_workers = self.config.get('execution', {}).get('parallel_tasks', 4)
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            # 提交任务
            future_to_task = {}
            for task_name in tasks:
                if task_name in self.config.get('tasks', {}):
                    task_config = self.config['tasks'][task_name]
                    if task_config.get('enabled', True):
                        future = executor.submit(self.execute_task, task_name, task_config)
                        future_to_task[future] = task_name
                    else:
                        self.logger.info(f"任务 {task_name} 已禁用，跳过")
                else:
                    self.logger.warning(f"任务 {task_name} 配置不存在")
            
            # 等待完成
            results = {}
            for future in concurrent.futures.as_completed(future_to_task):
                task_name = future_to_task[future]
                try:
                    result = future.result()
                    results[task_name] = result
                except Exception as e:
                    self.logger.error(f"任务 {task_name} 执行异常: {str(e)}")
                    results[task_name] = {
                        'status': 'error',
                        'error': str(e)
                    }
        
        return results
    
    def execute_sequential_tasks(self, tasks: List[str]) -> Dict[str, Any]:
        """顺序执行任务"""
        self.logger.info(f"开始顺序执行 {len(tasks)} 个任务")
        
        results = {}
        for task_name in tasks:
            if task_name in self.config.get('tasks', {}):
                task_config = self.config['tasks'][task_name]
                if task_config.get('enabled', True):
                    result = self.execute_task(task_name, task_config)
                    results[task_name] = result
                    
                    # 如果任务失败，停止后续任务
                    if result['status'] != 'success':
                        self.logger.error(f"任务 {task_name} 失败，停止后续任务")
                        break
                else:
                    self.logger.info(f"任务 {task_name} 已禁用，跳过")
            else:
                self.logger.warning(f"任务 {task_name} 配置不存在")
        
        return results
    
    def execute_all_tasks(self) -> Dict[str, Any]:
        """执行所有任务"""
        self.logger.info("开始执行所有任务")
        
        # 按优先级排序任务
        tasks = sorted(
            self.config.get('tasks', {}).keys(),
            key=lambda x: self.config['tasks'][x].get('priority', 999)
        )
        
        # 分析依赖关系，确定执行顺序
        execution_order = self.analyze_dependencies(tasks)
        
        # 执行任务
        all_results = {}
        for batch in execution_order:
            if len(batch) == 1:
                # 单个任务，顺序执行
                result = self.execute_sequential_tasks(batch)
                all_results.update(result)
            else:
                # 多个任务，并行执行
                result = self.execute_parallel_tasks(batch)
                all_results.update(result)
        
        return all_results
    
    def analyze_dependencies(self, tasks: List[str]) -> List[List[str]]:
        """分析依赖关系，确定执行顺序"""
        # 构建依赖图
        dependency_graph = {}
        for task in tasks:
            task_config = self.config['tasks'][task]
            dependencies = task_config.get('dependencies', [])
            dependency_graph[task] = dependencies
        
        # 拓扑排序
        execution_order = []
        visited = set()
        temp_visited = set()
        
        def visit(task):
            if task in temp_visited:
                raise Exception(f"循环依赖检测到: {task}")
            if task in visited:
                return
            
            temp_visited.add(task)
            for dep in dependency_graph.get(task, []):
                if dep in dependency_graph:
                    visit(dep)
            temp_visited.remove(task)
            visited.add(task)
            execution_order.append(task)
        
        for task in tasks:
            if task not in visited:
                visit(task)
        
        # 按依赖关系分组
        batches = []
        current_batch = []
        current_deps = set()
        
        for task in execution_order:
            task_deps = set(dependency_graph.get(task, []))
            
            # 检查是否可以加入当前批次
            if not task_deps.intersection(current_batch):
                current_batch.append(task)
                current_deps.update(task_deps)
            else:
                # 开始新批次
                if current_batch:
                    batches.append(current_batch)
                current_batch = [task]
                current_deps = task_deps
        
        if current_batch:
            batches.append(current_batch)
        
        return batches
    
    def generate_execution_report(self, results: Dict[str, Any]) -> str:
        """生成执行报告"""
        report = f"""
# OpenTelemetry 自动化执行报告

生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 执行摘要

总任务数: {len(results)}
成功任务数: {sum(1 for r in results.values() if r.get('status') == 'success')}
失败任务数: {sum(1 for r in results.values() if r.get('status') == 'failed')}
错误任务数: {sum(1 for r in results.values() if r.get('status') == 'error')}
超时任务数: {sum(1 for r in results.values() if r.get('status') == 'timeout')}

## 详细结果

"""
        
        for task_name, result in results.items():
            status = result.get('status', 'unknown')
            duration = result.get('duration', 0)
            
            report += f"### {task_name}\n"
            report += f"- **状态**: {status}\n"
            report += f"- **耗时**: {duration:.2f} 秒\n"
            
            if result.get('start_time'):
                report += f"- **开始时间**: {result['start_time']}\n"
            if result.get('end_time'):
                report += f"- **结束时间**: {result['end_time']}\n"
            
            if result.get('error'):
                report += f"- **错误信息**: {result['error']}\n"
            
            if result.get('output'):
                report += f"- **输出**: {result['output'][:200]}...\n"
            
            report += "\n"
        
        return report
    
    def save_execution_report(self, results: Dict[str, Any], filename: str = None):
        """保存执行报告"""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"reports/execution_report_{timestamp}.md"
        
        # 创建报告目录
        report_dir = Path('reports')
        report_dir.mkdir(exist_ok=True)
        
        # 生成并保存报告
        report = self.generate_execution_report(results)
        with open(report_dir / filename, 'w', encoding='utf-8') as f:
            f.write(report)
        
        self.logger.info(f"执行报告已保存到: {report_dir / filename}")
    
    def run(self, tasks: Optional[List[str]] = None):
        """运行自动化执行框架"""
        self.logger.info("启动自动化执行框架")
        
        try:
            if tasks:
                # 执行指定任务
                results = self.execute_sequential_tasks(tasks)
            else:
                # 执行所有任务
                results = self.execute_all_tasks()
            
            # 生成报告
            self.save_execution_report(results)
            
            # 输出摘要
            success_count = sum(1 for r in results.values() if r.get('status') == 'success')
            total_count = len(results)
            
            self.logger.info(f"执行完成: {success_count}/{total_count} 个任务成功")
            
            return results
            
        except Exception as e:
            self.logger.error(f"执行框架运行异常: {str(e)}")
            raise

def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='OpenTelemetry 自动化执行框架')
    parser.add_argument('--config', default='config/execution_config.yaml',
                       help='配置文件路径')
    parser.add_argument('--tasks', nargs='+',
                       help='要执行的任务列表')
    parser.add_argument('--all', action='store_true',
                       help='执行所有任务')
    
    args = parser.parse_args()
    
    # 创建执行框架
    framework = AutomatedExecutionFramework(args.config)
    
    # 执行任务
    if args.all:
        results = framework.run()
    elif args.tasks:
        results = framework.run(args.tasks)
    else:
        print("请指定要执行的任务或使用 --all 执行所有任务")
        return
    
    # 输出结果摘要
    success_count = sum(1 for r in results.values() if r.get('status') == 'success')
    total_count = len(results)
    print(f"\n执行完成: {success_count}/{total_count} 个任务成功")

if __name__ == "__main__":
    main()
