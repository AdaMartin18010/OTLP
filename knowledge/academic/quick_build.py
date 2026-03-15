#!/usr/bin/env python3
"""
LaTeX智能编译工具
功能:
- 自动检测LaTeX环境
- 智能编译（只在必要时运行BibTeX）
- 实时显示编译进度
- 错误诊断和建议
- 支持增量编译
"""

import os
import sys
import subprocess
import time
from pathlib import Path
from typing import Tuple, List

class Colors:
    """终端颜色"""
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

def print_header(text: str):
    """打印标题"""
    print(f"\n{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{text:^70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}\n")

def print_step(step: int, total: int, text: str):
    """打印步骤"""
    print(f"{Colors.OKBLUE}[{step}/{total}]{Colors.ENDC} {text}...")

def print_success(text: str):
    """打印成功信息"""
    print(f"{Colors.OKGREEN}✓{Colors.ENDC} {text}")

def print_warning(text: str):
    """打印警告"""
    print(f"{Colors.WARNING}⚠{Colors.ENDC} {text}")

def print_error(text: str):
    """打印错误"""
    print(f"{Colors.FAIL}✗{Colors.ENDC} {text}")

def check_command(cmd: str) -> bool:
    """检查命令是否存在"""
    try:
        subprocess.run([cmd, '--version'], 
                      stdout=subprocess.DEVNULL, 
                      stderr=subprocess.DEVNULL,
                      check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False

def check_environment() -> bool:
    """检查LaTeX环境"""
    print_step(1, 6, "检查LaTeX环境")
    
    has_errors = False
    
    # 检查pdflatex
    if check_command('pdflatex'):
        print_success("pdflatex已安装")
    else:
        print_error("pdflatex未安装")
        print_warning("请安装MiKTeX或TeX Live")
        has_errors = True
    
    # 检查bibtex
    if check_command('bibtex'):
        print_success("bibtex已安装")
    else:
        print_warning("bibtex未安装（可选）")
    
    print()
    return not has_errors

def check_files() -> Tuple[bool, List[str]]:
    """检查必需文件"""
    print_step(2, 6, "检查项目文件")
    
    missing_files = []
    
    # 检查主文件
    if Path('paper_main.tex').exists():
        print_success("paper_main.tex")
    else:
        print_error("paper_main.tex不存在")
        missing_files.append("paper_main.tex")
    
    # 检查references
    if Path('references.bib').exists():
        print_success("references.bib")
    else:
        print_warning("references.bib不存在")
    
    # 检查sections
    section_files = [
        "01_introduction.tex", "02_background.tex", "03_framework.tex",
        "04_implementation.tex", "05_evaluation.tex", "06_related_work.tex",
        "07_conclusion.tex"
    ]
    
    sections_dir = Path('sections')
    if sections_dir.exists():
        missing_sections = []
        for sec in section_files:
            if not (sections_dir / sec).exists():
                missing_sections.append(sec)
        
        if not missing_sections:
            print_success(f"所有{len(section_files)}个section文件")
        else:
            print_warning(f"缺失{len(missing_sections)}个section文件")
            missing_files.extend(missing_sections)
    else:
        print_error("sections/目录不存在")
        missing_files.append("sections/")
    
    # 检查figures
    figures_dir = Path('figures')
    if figures_dir.exists():
        fig_count = len(list(figures_dir.glob('*.tex')))
        print_success(f"找到{fig_count}个figure文件")
    else:
        print_warning("figures/目录不存在")
    
    print()
    return len(missing_files) == 0, missing_files

def run_pdflatex(interaction_mode: str = 'nonstopmode') -> Tuple[bool, str]:
    """运行pdflatex"""
    try:
        result = subprocess.run(
            ['pdflatex', f'-interaction={interaction_mode}', 'paper_main.tex'],
            capture_output=True,
            text=True,
            timeout=300  # 5分钟超时
        )
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, "编译超时（超过5分钟）"
    except Exception as e:
        return False, str(e)

def run_bibtex() -> Tuple[bool, str]:
    """运行bibtex"""
    try:
        result = subprocess.run(
            ['bibtex', 'paper_main'],
            capture_output=True,
            text=True,
            timeout=60
        )
        return result.returncode == 0, result.stdout + result.stderr
    except Exception as e:
        return False, str(e)

def needs_bibtex() -> bool:
    """检查是否需要运行bibtex"""
    aux_file = Path('paper_main.aux')
    bbl_file = Path('paper_main.bbl')
    
    if not aux_file.exists():
        return False
    
    if not bbl_file.exists():
        return True
    
    # 检查.aux文件是否比.bbl文件新
    return aux_file.stat().st_mtime > bbl_file.stat().st_mtime

def compile_paper():
    """编译论文"""
    print_header("OTLP ICSE2026 论文智能编译")
    
    # 1. 检查环境
    if not check_environment():
        print_error("环境检查失败，无法继续")
        return False
    
    # 2. 检查文件
    files_ok, missing = check_files()
    if not files_ok:
        print_error(f"缺失{len(missing)}个必需文件:")
        for f in missing:
            print(f"  - {f}")
        return False
    
    # 3. 第一次编译
    print_step(3, 6, "首次编译（生成.aux文件）")
    success, output = run_pdflatex()
    if success:
        print_success("首次编译成功")
    else:
        print_warning("首次编译有警告（这是正常的）")
    print()
    
    # 4. BibTeX（如果需要）
    if needs_bibtex():
        print_step(4, 6, "运行BibTeX（处理参考文献）")
        success, output = run_bibtex()
        if success:
            print_success("BibTeX处理成功")
        else:
            print_warning("BibTeX有警告（可能正常）")
        print()
    else:
        print_step(4, 6, "跳过BibTeX（无需更新）")
        print_success("参考文献已是最新")
        print()
    
    # 5. 第二次编译
    print_step(5, 6, "第二次编译（整合引用）")
    success, output = run_pdflatex()
    if success:
        print_success("第二次编译成功")
    else:
        print_warning("第二次编译有警告")
    print()
    
    # 6. 第三次编译（最终）
    print_step(6, 6, "第三次编译（最终PDF）")
    success, output = run_pdflatex()
    if success:
        print_success("最终编译成功！")
    else:
        print_error("最终编译失败")
        print("\n查看详细错误:")
        print("  cat paper_main.log | grep -A 5 'Error'")
        return False
    print()
    
    # 7. 检查结果
    pdf_file = Path('paper_main.pdf')
    if pdf_file.exists():
        size_kb = pdf_file.stat().st_size / 1024
        print_header("编译成功！")
        print_success(f"PDF已生成: paper_main.pdf ({size_kb:.1f} KB)")
        print()
        print("下一步建议:")
        print("  1. 打开并检查PDF: open paper_main.pdf")
        print("  2. 检查页数和格式")
        print("  3. 查看编译日志: tail paper_main.log")
        return True
    else:
        print_error("PDF文件未生成")
        print("请查看日志文件: paper_main.log")
        return False

def main():
    """主函数"""
    # 确保在正确的目录
    if not Path('paper_main.tex').exists():
        print_error("请在academic目录下运行此脚本")
        sys.exit(1)
    
    start_time = time.time()
    
    try:
        success = compile_paper()
        
        elapsed = time.time() - start_time
        print(f"\n总耗时: {elapsed:.1f}秒")
        
        sys.exit(0 if success else 1)
    
    except KeyboardInterrupt:
        print("\n\n编译被用户中断")
        sys.exit(1)
    except Exception as e:
        print_error(f"发生错误: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()

