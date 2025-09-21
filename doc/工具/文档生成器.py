#!/usr/bin/env python3
"""
OpenTelemetry 2025 文档生成器

功能：
- 自动生成文档模板
- 批量创建文档结构
- 生成文档索引
- 自动更新文档链接
"""

import os
import re
import json
import yaml
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, asdict
from datetime import datetime
import argparse
import logging
from jinja2 import Template

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class DocumentTemplate:
    """文档模板"""
    name: str
    title: str
    description: str
    template_content: str
    required_sections: List[str]
    metadata: Dict[str, Any]

@dataclass
class DocumentStructure:
    """文档结构"""
    name: str
    path: str
    type: str  # 'file' or 'directory'
    children: List['DocumentStructure']
    template: Optional[str] = None

class DocumentGenerator:
    """文档生成器"""
    
    def __init__(self, doc_root: str = "doc"):
        self.doc_root = Path(doc_root)
        self.templates = self._load_templates()
        self.structure = self._load_structure()
    
    def _load_templates(self) -> Dict[str, DocumentTemplate]:
        """加载文档模板"""
        templates = {}
        
        # 基础文档模板
        templates['basic'] = DocumentTemplate(
            name='basic',
            title='基础文档模板',
            description='标准的基础文档模板',
            template_content=self._get_basic_template(),
            required_sections=['概述', '目标', '内容', '总结'],
            metadata={
                'version': '1.0.0',
                'author': 'OpenTelemetry 2025 团队',
                'created': datetime.now().strftime('%Y年%m月%d日')
            }
        )
        
        # README模板
        templates['readme'] = DocumentTemplate(
            name='readme',
            title='README文档模板',
            description='目录总览文档模板',
            template_content=self._get_readme_template(),
            required_sections=['概览', '目标', '结构', '快速开始'],
            metadata={
                'version': '1.0.0',
                'author': 'OpenTelemetry 2025 团队',
                'created': datetime.now().strftime('%Y年%m月%d日')
            }
        )
        
        # 技术文档模板
        templates['technical'] = DocumentTemplate(
            name='technical',
            title='技术文档模板',
            description='技术实现文档模板',
            template_content=self._get_technical_template(),
            required_sections=['概述', '架构', '实现', '配置', '部署'],
            metadata={
                'version': '1.0.0',
                'author': 'OpenTelemetry 2025 技术团队',
                'created': datetime.now().strftime('%Y年%m月%d日')
            }
        )
        
        return templates
    
    def _get_basic_template(self) -> str:
        """获取基础文档模板"""
        return """# {{ title }}

## 📊 概述

**创建时间**: {{ created_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**状态**: {{ status }}  

## 🎯 目标

### 主要目标

1. 目标1
2. 目标2
3. 目标3

### 成功标准

- 标准1
- 标准2
- 标准3

## 📋 内容

### 章节1
内容...

### 章节2
内容...

## 📊 统计

### 定量指标
- 指标1: 数值
- 指标2: 数值

### 定性指标
- 指标1: 描述
- 指标2: 描述

## 🚀 总结

### 主要成果
1. 成果1
2. 成果2

### 后续发展
1. 发展方向1
2. 发展方向2

## 📚 参考资源

### 相关文档
- [文档1](链接1)
- [文档2](链接2)

### 外部资源
- [资源1](链接1)
- [资源2](链接2)

---

**最后更新**: {{ update_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**下次审查**: {{ review_date }}"""
    
    def _get_readme_template(self) -> str:
        """获取README文档模板"""
        return """# {{ title }}

## 📊 概览

**创建时间**: {{ created_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**状态**: {{ status }}  

## 🎯 目标

### 主要目标

1. **目标1**: 描述
2. **目标2**: 描述
3. **目标3**: 描述

### 成功标准

- **标准1**: 描述
- **标准2**: 描述
- **标准3**: 描述

## 🏗️ 结构

### 文档结构

```text
{{ structure_tree }}
```

### 核心文档

- [文档1](链接1) - 描述
- [文档2](链接2) - 描述
- [文档3](链接3) - 描述

## 🚀 快速开始

### 新用户

1. 阅读[项目章程](../00_项目概览/项目章程.md)了解项目背景
2. 查看[快速开始指南](../00_项目概览/快速开始.md)开始学习
3. 使用[文档导航](../00_项目概览/文档导航.md)查找所需信息

### 开发者

1. 学习[技术架构](../03_技术架构/README.md)了解技术实现
2. 查看[协议实现](../03_技术架构/协议实现.md)了解协议细节
3. 使用[开发工具链](../03_技术架构/工具链.md)进行开发

### 研究人员

1. 研究[理论基础](../01_理论基础/README.md)了解理论框架
2. 学习[形式化验证](../01_理论基础/形式化验证框架.md)掌握验证方法
3. 参与[学术合作](../06_社区生态/学术合作.md)进行学术研究

## 📊 统计

### 文档统计

- **总文档数量**: {{ total_docs }} 个
- **技术文档**: {{ tech_docs }} 个
- **标准文档**: {{ standard_docs }} 个
- **实践文档**: {{ practice_docs }} 个

### 知识体系统计

- **知识层级**: {{ knowledge_levels }} 层
- **知识节点**: {{ knowledge_nodes }} 个
- **知识关系**: {{ knowledge_relations }} 个
- **标准对齐**: {{ standards_aligned }} 个

## 🔮 未来展望

### 短期目标（3-6个月）

1. 目标1
2. 目标2
3. 目标3

### 中期目标（6-12个月）

1. 目标1
2. 目标2
3. 目标3

### 长期目标（1-2年）

1. 目标1
2. 目标2
3. 目标3

## 📚 参考资源

### 相关文档

- [文档1](链接1)
- [文档2](链接2)
- [文档3](链接3)

### 外部资源

- [资源1](链接1)
- [资源2](链接2)
- [资源3](链接3)

---

**概览建立时间**: {{ created_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**下次审查**: {{ review_date }}"""
    
    def _get_technical_template(self) -> str:
        """获取技术文档模板"""
        return """# {{ title }}

## 📊 技术概述

**创建时间**: {{ created_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**状态**: {{ status }}  

## 🎯 技术目标

### 主要目标

1. **技术目标1**: 描述
2. **技术目标2**: 描述
3. **技术目标3**: 描述

### 技术指标

- **性能指标**: 描述
- **可靠性指标**: 描述
- **安全性指标**: 描述

## 🏗️ 技术架构

### 整体架构

```text
{{ architecture_diagram }}
```

### 核心组件

- **组件1**: 描述
- **组件2**: 描述
- **组件3**: 描述

### 技术栈

- **前端技术**: 描述
- **后端技术**: 描述
- **数据库技术**: 描述
- **基础设施**: 描述

## 🔧 技术实现

### 实现方案

#### 方案1
```yaml
# 配置示例
config:
  key1: value1
  key2: value2
```

#### 方案2
```python
# 代码示例
def example_function():
    return "Hello, World!"
```

### 关键技术

- **技术1**: 详细说明
- **技术2**: 详细说明
- **技术3**: 详细说明

## ⚙️ 配置管理

### 配置文件

```yaml
# 主配置文件
main_config:
  setting1: value1
  setting2: value2
```

### 环境配置

- **开发环境**: 配置说明
- **测试环境**: 配置说明
- **生产环境**: 配置说明

## 🚀 部署指南

### 部署要求

- **系统要求**: 描述
- **依赖软件**: 描述
- **网络要求**: 描述

### 部署步骤

1. **步骤1**: 详细说明
2. **步骤2**: 详细说明
3. **步骤3**: 详细说明

### 部署验证

- **验证方法1**: 说明
- **验证方法2**: 说明
- **验证方法3**: 说明

## 📊 性能优化

### 性能指标

- **响应时间**: < 100ms
- **吞吐量**: > 1000 req/s
- **并发数**: > 10000

### 优化策略

- **策略1**: 详细说明
- **策略2**: 详细说明
- **策略3**: 详细说明

## 🔍 监控告警

### 监控指标

- **业务指标**: 描述
- **技术指标**: 描述
- **系统指标**: 描述

### 告警规则

```yaml
# 告警配置
alerts:
  - name: "HighErrorRate"
    condition: "error_rate > 0.1"
    severity: "warning"
```

## 🚀 未来展望

### 技术发展

1. **发展方向1**: 描述
2. **发展方向2**: 描述
3. **发展方向3**: 描述

### 技术升级

- **升级计划1**: 描述
- **升级计划2**: 描述
- **升级计划3**: 描述

## 📚 参考资源

### 技术文档

- [文档1](链接1)
- [文档2](链接2)
- [文档3](链接3)

### 技术资源

- [资源1](链接1)
- [资源2](链接2)
- [资源3](链接3)

---

**技术文档建立时间**: {{ created_date }}  
**文档版本**: {{ version }}  
**维护者**: {{ maintainer }}  
**下次审查**: {{ review_date }}"""
    
    def _load_structure(self) -> DocumentStructure:
        """加载文档结构"""
        return DocumentStructure(
            name="doc",
            path="doc",
            type="directory",
            children=[
                DocumentStructure(
                    name="00_项目概览",
                    path="00_项目概览",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="项目章程.md", path="项目章程.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="快速开始.md", path="快速开始.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="文档导航.md", path="文档导航.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="项目执行报告.md", path="项目执行报告.md", type="file", children=[], template="basic")
                    ]
                ),
                DocumentStructure(
                    name="01_理论基础",
                    path="01_理论基础",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="数学基础理论.md", path="数学基础理论.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="形式化验证框架.md", path="形式化验证框架.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="理论证明系统.md", path="理论证明系统.md", type="file", children=[], template="technical")
                    ]
                ),
                DocumentStructure(
                    name="02_标准规范",
                    path="02_标准规范",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="国际标准对齐.md", path="国际标准对齐.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="OTLP规范详解.md", path="OTLP规范详解.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="语义约定标准.md", path="语义约定标准.md", type="file", children=[], template="technical")
                    ]
                ),
                DocumentStructure(
                    name="03_技术架构",
                    path="03_技术架构",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="系统架构设计.md", path="系统架构设计.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="协议实现.md", path="协议实现.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="工具链.md", path="工具链.md", type="file", children=[], template="technical")
                    ]
                ),
                DocumentStructure(
                    name="04_应用实践",
                    path="04_应用实践",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="行业解决方案.md", path="行业解决方案.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="部署指南.md", path="部署指南.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="最佳实践.md", path="最佳实践.md", type="file", children=[], template="basic")
                    ]
                ),
                DocumentStructure(
                    name="05_质量保证",
                    path="05_质量保证",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="测试框架.md", path="测试框架.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="性能基准.md", path="性能基准.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="质量监控.md", path="质量监控.md", type="file", children=[], template="technical")
                    ]
                ),
                DocumentStructure(
                    name="06_社区生态",
                    path="06_社区生态",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="治理框架.md", path="治理框架.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="贡献指南.md", path="贡献指南.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="学术合作.md", path="学术合作.md", type="file", children=[], template="basic")
                    ]
                ),
                DocumentStructure(
                    name="07_商业化",
                    path="07_商业化",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="商业模式.md", path="商业模式.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="市场分析.md", path="市场分析.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="发展路线.md", path="发展路线.md", type="file", children=[], template="basic")
                    ]
                ),
                DocumentStructure(
                    name="08_附录",
                    path="08_附录",
                    type="directory",
                    children=[
                        DocumentStructure(name="README.md", path="README.md", type="file", children=[], template="readme"),
                        DocumentStructure(name="术语表.md", path="术语表.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="参考文献.md", path="参考文献.md", type="file", children=[], template="basic"),
                        DocumentStructure(name="配置示例.md", path="配置示例.md", type="file", children=[], template="technical"),
                        DocumentStructure(name="故障排除.md", path="故障排除.md", type="file", children=[], template="basic")
                    ]
                )
            ]
        )
    
    def generate_document(self, template_name: str, output_path: str, **kwargs) -> bool:
        """生成单个文档"""
        try:
            if template_name not in self.templates:
                logger.error(f"模板不存在: {template_name}")
                return False
            
            template = self.templates[template_name]
            
            # 准备模板变量
            template_vars = {
                'title': kwargs.get('title', '文档标题'),
                'created_date': kwargs.get('created_date', datetime.now().strftime('%Y年%m月%d日')),
                'version': kwargs.get('version', '1.0.0'),
                'maintainer': kwargs.get('maintainer', 'OpenTelemetry 2025 团队'),
                'status': kwargs.get('status', '活跃开发中'),
                'update_date': datetime.now().strftime('%Y年%m月%d日'),
                'review_date': (datetime.now().replace(month=datetime.now().month + 1)).strftime('%Y年%m月%d日'),
                **kwargs
            }
            
            # 渲染模板
            jinja_template = Template(template.template_content)
            content = jinja_template.render(**template_vars)
            
            # 写入文件
            output_file = self.doc_root / output_path
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_text(content, encoding='utf-8')
            
            logger.info(f"文档已生成: {output_path}")
            return True
        
        except Exception as e:
            logger.error(f"生成文档失败 {output_path}: {e}")
            return False
    
    def generate_structure(self, structure: DocumentStructure, base_path: str = "") -> int:
        """生成文档结构"""
        generated_count = 0
        
        try:
            current_path = Path(base_path) / structure.path if base_path else Path(structure.path)
            
            if structure.type == "directory":
                # 创建目录
                full_path = self.doc_root / current_path
                full_path.mkdir(parents=True, exist_ok=True)
                logger.info(f"目录已创建: {current_path}")
                
                # 递归处理子结构
                for child in structure.children:
                    generated_count += self.generate_structure(child, str(current_path))
            
            elif structure.type == "file":
                # 生成文件
                if structure.template:
                    # 准备文件特定的变量
                    file_vars = {
                        'title': structure.name.replace('.md', ''),
                        'path': str(current_path)
                    }
                    
                    if self.generate_document(structure.template, str(current_path), **file_vars):
                        generated_count += 1
                else:
                    # 创建空文件
                    full_path = self.doc_root / current_path
                    full_path.parent.mkdir(parents=True, exist_ok=True)
                    full_path.touch()
                    logger.info(f"文件已创建: {current_path}")
                    generated_count += 1
        
        except Exception as e:
            logger.error(f"生成结构失败 {structure.path}: {e}")
        
        return generated_count
    
    def generate_all_documents(self) -> int:
        """生成所有文档"""
        logger.info("开始生成所有文档...")
        
        total_generated = 0
        
        # 生成主README
        if self.generate_document('readme', 'README.md', 
                                title='OpenTelemetry 2025 知识经验梳理和形式化证明学术研究项目',
                                structure_tree=self._generate_structure_tree()):
            total_generated += 1
        
        # 生成文档结构
        total_generated += self.generate_structure(self.structure)
        
        logger.info(f"文档生成完成，共生成 {total_generated} 个文档")
        return total_generated
    
    def _generate_structure_tree(self) -> str:
        """生成结构树"""
        def build_tree(structure: DocumentStructure, prefix: str = "") -> str:
            result = []
            
            if structure.type == "directory":
                result.append(f"{prefix}├── {structure.name}/")
                for i, child in enumerate(structure.children):
                    is_last = i == len(structure.children) - 1
                    child_prefix = prefix + ("    " if is_last else "│   ")
                    result.append(build_tree(child, child_prefix))
            else:
                result.append(f"{prefix}├── {structure.name}")
            
            return "\n".join(result)
        
        return build_tree(self.structure)
    
    def update_document_links(self) -> int:
        """更新文档链接"""
        logger.info("开始更新文档链接...")
        
        updated_count = 0
        md_files = list(self.doc_root.rglob("*.md"))
        
        for md_file in md_files:
            try:
                content = md_file.read_text(encoding='utf-8')
                original_content = content
                
                # 更新相对链接
                content = self._update_relative_links(content, md_file)
                
                # 更新交叉引用
                content = self._update_cross_references(content, md_file)
                
                if content != original_content:
                    md_file.write_text(content, encoding='utf-8')
                    updated_count += 1
                    logger.info(f"链接已更新: {md_file.relative_to(self.doc_root)}")
            
            except Exception as e:
                logger.error(f"更新链接失败 {md_file}: {e}")
        
        logger.info(f"链接更新完成，共更新 {updated_count} 个文件")
        return updated_count
    
    def _update_relative_links(self, content: str, file_path: Path) -> str:
        """更新相对链接"""
        # 这里可以添加更复杂的链接更新逻辑
        return content
    
    def _update_cross_references(self, content: str, file_path: Path) -> str:
        """更新交叉引用"""
        # 这里可以添加交叉引用更新逻辑
        return content
    
    def generate_index(self, output_file: str = "doc-index.json") -> bool:
        """生成文档索引"""
        try:
            index = {
                'generated_at': datetime.now().isoformat(),
                'total_documents': 0,
                'documents': [],
                'structure': asdict(self.structure)
            }
            
            md_files = list(self.doc_root.rglob("*.md"))
            index['total_documents'] = len(md_files)
            
            for md_file in md_files:
                try:
                    content = md_file.read_text(encoding='utf-8')
                    
                    # 提取文档信息
                    doc_info = {
                        'path': str(md_file.relative_to(self.doc_root)),
                        'size': md_file.stat().st_size,
                        'modified': datetime.fromtimestamp(md_file.stat().st_mtime).isoformat(),
                        'title': self._extract_title(content),
                        'sections': self._extract_sections(content),
                        'links': self._extract_links(content)
                    }
                    
                    index['documents'].append(doc_info)
                
                except Exception as e:
                    logger.error(f"处理文档失败 {md_file}: {e}")
            
            # 写入索引文件
            index_file = self.doc_root / output_file
            with open(index_file, 'w', encoding='utf-8') as f:
                json.dump(index, f, ensure_ascii=False, indent=2)
            
            logger.info(f"文档索引已生成: {output_file}")
            return True
        
        except Exception as e:
            logger.error(f"生成索引失败: {e}")
            return False
    
    def _extract_title(self, content: str) -> str:
        """提取文档标题"""
        lines = content.split('\n')
        for line in lines:
            if line.strip().startswith('# '):
                return line.strip()[2:]
        return "无标题"
    
    def _extract_sections(self, content: str) -> List[str]:
        """提取文档章节"""
        sections = []
        lines = content.split('\n')
        
        for line in lines:
            if line.strip().startswith('## '):
                sections.append(line.strip()[3:])
        
        return sections
    
    def _extract_links(self, content: str) -> List[str]:
        """提取文档链接"""
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        return [f"{text} -> {url}" for text, url in links]

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="OpenTelemetry 2025 文档生成器")
    parser.add_argument("--doc-root", default="doc", help="文档根目录")
    parser.add_argument("--template", help="指定模板名称")
    parser.add_argument("--output", help="输出文件路径")
    parser.add_argument("--generate-all", action="store_true", help="生成所有文档")
    parser.add_argument("--update-links", action="store_true", help="更新文档链接")
    parser.add_argument("--generate-index", action="store_true", help="生成文档索引")
    parser.add_argument("--title", help="文档标题")
    parser.add_argument("--maintainer", help="维护者")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建生成器
    generator = DocumentGenerator(args.doc_root)
    
    if args.generate_all:
        # 生成所有文档
        count = generator.generate_all_documents()
        print(f"已生成 {count} 个文档")
    
    elif args.template and args.output:
        # 生成单个文档
        template_vars = {}
        if args.title:
            template_vars['title'] = args.title
        if args.maintainer:
            template_vars['maintainer'] = args.maintainer
        
        if generator.generate_document(args.template, args.output, **template_vars):
            print(f"文档已生成: {args.output}")
        else:
            print("文档生成失败")
    
    if args.update_links:
        # 更新文档链接
        count = generator.update_document_links()
        print(f"已更新 {count} 个文件的链接")
    
    if args.generate_index:
        # 生成文档索引
        if generator.generate_index():
            print("文档索引已生成")
        else:
            print("文档索引生成失败")
    
    if not any([args.generate_all, args.template, args.update_links, args.generate_index]):
        print("请指定操作：--generate-all, --template, --update-links, 或 --generate-index")

if __name__ == "__main__":
    main()
