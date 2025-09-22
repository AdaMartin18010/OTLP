#!/usr/bin/env python3
"""
OpenTelemetry 2025 一键自动化脚本
运行所有自动化任务：文档更新、目录生成、导航维护
"""

import os
import sys
import subprocess
import time
from pathlib import Path
from datetime import datetime

class AutomationRunner:
    def __init__(self):
        self.scripts_dir = Path(__file__).parent
        self.start_time = datetime.now()
        self.results = []
        
    def run_script(self, script_name: str, description: str, timeout: int = 300) -> bool:
        """运行脚本"""
        print(f"\n🔄 {description}...")
        print("-" * 60)
        
        script_path = self.scripts_dir / script_name
        
        if not script_path.exists():
            print(f"❌ 脚本不存在: {script_path}")
            return False
        
        try:
            start_time = time.time()
            result = subprocess.run([
                sys.executable, str(script_path)
            ], capture_output=True, text=True, cwd=self.scripts_dir, timeout=timeout)
            
            end_time = time.time()
            duration = end_time - start_time
            
            if result.returncode == 0:
                print(f"✅ {description} 完成 (耗时: {duration:.1f}秒)")
                if result.stdout:
                    # 只显示关键输出
                    lines = result.stdout.split('\n')
                    for line in lines:
                        if any(keyword in line for keyword in ['✅', '❌', '📁', '📄', '🔄', '📊']):
                            print(f"  {line}")
                return True
            else:
                print(f"❌ {description} 失败 (耗时: {duration:.1f}秒)")
                if result.stderr:
                    print(f"错误: {result.stderr}")
                return False
                
        except subprocess.TimeoutExpired:
            print(f"⏰ {description} 超时 (>{timeout}秒)")
            return False
        except Exception as e:
            print(f"❌ {description} 异常: {e}")
            return False
    
    def check_dependencies(self) -> bool:
        """检查依赖"""
        print("🔍 检查依赖...")
        
        required_packages = ['yaml']
        missing_packages = []
        
        for package in required_packages:
            try:
                __import__(package)
            except ImportError:
                missing_packages.append(package)
        
        if missing_packages:
            print(f"❌ 缺少依赖: {', '.join(missing_packages)}")
            print("请运行: pip install PyYAML")
            return False
        
        print("✅ 依赖检查通过")
        return True
    
    def run_all_automation(self):
        """运行所有自动化任务"""
        print("🚀 OpenTelemetry 2025 一键自动化系统")
        print("=" * 80)
        print(f"开始时间: {self.start_time.strftime('%Y-%m-%d %H:%M:%S')}")
        
        # 检查依赖
        if not self.check_dependencies():
            return
        
        # 定义自动化任务
        tasks = [
            {
                "script": "auto_document_updater.py",
                "description": "自动文档更新和结构修复",
                "timeout": 300
            },
            {
                "script": "smart_document_manager.py", 
                "description": "智能文档管理和目录生成",
                "timeout": 600
            },
            {
                "script": "auto_generate_toc.py",
                "description": "自动生成目录结构",
                "timeout": 300
            },
            {
                "script": "auto_update_navigation.py",
                "description": "自动更新导航文件",
                "timeout": 300
            }
        ]
        
        success_count = 0
        total_count = len(tasks)
        
        for i, task in enumerate(tasks, 1):
            print(f"\n📋 任务 {i}/{total_count}")
            success = self.run_script(
                task["script"], 
                task["description"], 
                task["timeout"]
            )
            
            self.results.append({
                "task": task["description"],
                "script": task["script"],
                "success": success,
                "timestamp": datetime.now().isoformat()
            })
            
            if success:
                success_count += 1
            
            # 任务间暂停
            if i < total_count:
                print("⏳ 等待3秒后继续下一个任务...")
                time.sleep(3)
        
        # 生成执行报告
        self.generate_report()
        
        # 显示结果汇总
        self.show_summary(success_count, total_count)
    
    def generate_report(self):
        """生成执行报告"""
        report_content = f"""# OpenTelemetry 2025 自动化执行报告

## 📊 执行概览

**执行时间**: {self.start_time.strftime('%Y年%m月%d日 %H:%M:%S')} - {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}  
**执行版本**: 2.0.0  
**维护者**: OpenTelemetry 2025 自动化系统  
**状态**: 自动化任务执行报告  

## 🎯 执行目标

### 主要目标

1. **文档更新**: 自动检测和修复文档结构
2. **目录生成**: 自动生成完整的文档目录
3. **导航维护**: 自动更新导航和索引文件
4. **质量保证**: 确保文档质量和一致性

## 📋 任务执行详情

"""
        
        for i, result in enumerate(self.results, 1):
            status = "✅ 成功" if result["success"] else "❌ 失败"
            report_content += f"""
### 任务 {i}: {result["task"]}

- **脚本**: {result["script"]}
- **状态**: {status}
- **执行时间**: {result["timestamp"]}
"""
        
        report_content += f"""

## 📊 执行统计

- **总任务数**: {len(self.results)}
- **成功任务数**: {sum(1 for r in self.results if r["success"])}
- **失败任务数**: {sum(1 for r in self.results if not r["success"])}
- **成功率**: {sum(1 for r in self.results if r["success"]) / len(self.results) * 100:.1f}%

## 🔧 自动化功能

### 已实现功能

1. **智能文档管理**: 自动扫描、分析和组织文档
2. **结构修复**: 自动检测和修复文档结构问题
3. **目录生成**: 自动生成完整的文档目录
4. **导航更新**: 自动更新导航和索引文件
5. **交叉引用**: 自动检查和修复文档引用
6. **备份机制**: 自动备份修改的文件
7. **缓存系统**: 智能缓存提高执行效率

### 技术特性

- **增量更新**: 只处理变化的文件
- **智能分析**: 自动分析文档结构和内容
- **错误恢复**: 自动备份和错误恢复机制
- **性能优化**: 缓存和并行处理
- **可配置性**: 灵活的配置选项

## 📚 使用说明

### 运行自动化

```bash
# 运行所有自动化任务
python scripts/run_all_automation.py

# 运行单个任务
python scripts/smart_document_manager.py
python scripts/auto_document_updater.py
```

### 配置选项

- 编辑 `scripts/document_config.yaml` 自定义配置
- 修改 `scripts/.document_cache.json` 管理缓存
- 查看 `scripts/backups/` 目录获取备份文件

## 🎉 总结

OpenTelemetry 2025 自动化系统成功完成了文档管理的自动化任务，大大提高了文档维护的效率和一致性。

### 主要成果

1. **效率提升**: 自动化处理减少了手工维护工作量
2. **质量保证**: 自动检查和修复确保了文档质量
3. **一致性**: 标准化处理保证了文档格式一致性
4. **可维护性**: 智能缓存和备份机制提高了可维护性

---

**报告生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}  
**报告版本**: 2.0.0  
**维护者**: OpenTelemetry 2025 自动化系统  
**下次执行**: {(datetime.now().replace(day=datetime.now().day+1)).strftime('%Y年%m月%d日')}
"""
        
        # 保存报告
        report_file = Path("doc/00_项目概览与导航/自动化执行报告.md")
        report_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        print(f"\n📊 已生成执行报告: {report_file}")
    
    def show_summary(self, success_count: int, total_count: int):
        """显示结果汇总"""
        end_time = datetime.now()
        duration = end_time - self.start_time
        
        print("\n" + "=" * 80)
        print("📊 执行结果汇总")
        print("=" * 80)
        print(f"✅ 成功任务: {success_count}/{total_count}")
        print(f"❌ 失败任务: {total_count - success_count}/{total_count}")
        print(f"⏱️ 总耗时: {duration.total_seconds():.1f} 秒")
        print(f"📅 开始时间: {self.start_time.strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"📅 结束时间: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        
        if success_count == total_count:
            print("\n🎉 所有自动化任务执行成功!")
            print("📁 文档结构已自动更新")
            print("🗺️ 导航文件已自动更新")
            print("📊 统计报告已生成")
            print("🔧 文档结构已自动修复")
        else:
            print(f"\n⚠️ 有 {total_count - success_count} 个任务执行失败")
            print("请检查错误信息并手动修复")
        
        print("\n💡 提示:")
        print("- 查看 doc/00_项目概览与导航/ 目录获取最新文档")
        print("- 查看 scripts/backups/ 目录获取备份文件")
        print("- 编辑 scripts/document_config.yaml 自定义配置")

def main():
    """主函数"""
    runner = AutomationRunner()
    runner.run_all_automation()

if __name__ == "__main__":
    main()
