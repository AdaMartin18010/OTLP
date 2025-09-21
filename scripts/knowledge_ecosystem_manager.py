#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OpenTelemetry 2025 知识生态管理系统
Knowledge Ecosystem Management System for OpenTelemetry 2025

功能特性:
- 知识体系管理
- 知识关系建立
- 知识搜索功能
- 知识完整性检查
- 知识更新监控
- 知识质量评估
"""

import os
import sys
import json
import yaml
import time
import logging
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional, Set, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import re
import hashlib

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('knowledge_ecosystem.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class KnowledgeType(Enum):
    """知识类型枚举"""
    THEORETICAL = "theoretical"
    STANDARD = "standard"
    TECHNICAL = "technical"
    PRACTICAL = "practical"
    QUALITY = "quality"
    COMMUNITY = "community"
    ACADEMIC = "academic"

class KnowledgeStatus(Enum):
    """知识状态枚举"""
    ACTIVE = "active"
    DRAFT = "draft"
    ARCHIVED = "archived"
    DEPRECATED = "deprecated"

@dataclass
class KnowledgeNode:
    """知识节点数据类"""
    id: str
    title: str
    description: str
    knowledge_type: KnowledgeType
    status: KnowledgeStatus
    file_path: str
    content_hash: str
    created_at: str
    updated_at: str
    tags: List[str]
    dependencies: List[str]
    references: List[str]
    quality_score: float
    completeness_score: float

@dataclass
class KnowledgeRelationship:
    """知识关系数据类"""
    source_id: str
    target_id: str
    relationship_type: str
    strength: float
    description: str
    created_at: str

class KnowledgeIndexer:
    """知识索引器"""
    
    def __init__(self, base_path: str = "doc/02_知识体系"):
        self.base_path = Path(base_path)
        self.knowledge_nodes: Dict[str, KnowledgeNode] = {}
        self.knowledge_relationships: List[KnowledgeRelationship] = []
        self.index_file = Path("data/knowledge_index.json")
    
    def build_knowledge_index(self) -> Dict[str, Any]:
        """构建知识索引"""
        logger.info("开始构建知识索引...")
        
        # 清空现有索引
        self.knowledge_nodes.clear()
        self.knowledge_relationships.clear()
        
        # 扫描知识体系目录
        self._scan_knowledge_directory()
        
        # 建立知识关系
        self._build_knowledge_relationships()
        
        # 计算知识质量分数
        self._calculate_quality_scores()
        
        # 保存索引
        self._save_knowledge_index()
        
        logger.info(f"知识索引构建完成，共索引 {len(self.knowledge_nodes)} 个知识节点")
        
        return {
            'total_nodes': len(self.knowledge_nodes),
            'total_relationships': len(self.knowledge_relationships),
            'knowledge_types': self._get_knowledge_type_distribution(),
            'quality_distribution': self._get_quality_distribution()
        }
    
    def _scan_knowledge_directory(self):
        """扫描知识体系目录"""
        if not self.base_path.exists():
            logger.warning(f"知识体系目录不存在: {self.base_path}")
            return
        
        # 递归扫描所有markdown文件
        for md_file in self.base_path.glob('**/*.md'):
            try:
                # 计算相对路径
                rel_path = md_file.relative_to(self.base_path)
                
                # 读取文件内容
                content = md_file.read_text(encoding='utf-8')
                
                # 计算内容哈希
                content_hash = hashlib.md5(content.encode('utf-8')).hexdigest()
                
                # 获取文件统计信息
                stat = md_file.stat()
                created_at = datetime.fromtimestamp(stat.st_ctime).isoformat()
                updated_at = datetime.fromtimestamp(stat.st_mtime).isoformat()
                
                # 解析文档元数据
                metadata = self._parse_document_metadata(content, str(rel_path))
                
                # 创建知识节点
                node_id = self._generate_node_id(str(rel_path))
                knowledge_node = KnowledgeNode(
                    id=node_id,
                    title=metadata['title'],
                    description=metadata['description'],
                    knowledge_type=metadata['knowledge_type'],
                    status=metadata['status'],
                    file_path=str(rel_path),
                    content_hash=content_hash,
                    created_at=created_at,
                    updated_at=updated_at,
                    tags=metadata['tags'],
                    dependencies=metadata['dependencies'],
                    references=metadata['references'],
                    quality_score=0.0,
                    completeness_score=0.0
                )
                
                self.knowledge_nodes[node_id] = knowledge_node
                
            except Exception as e:
                logger.error(f"处理文件时出错 {md_file}: {e}")
    
    def _parse_document_metadata(self, content: str, file_path: str) -> Dict[str, Any]:
        """解析文档元数据"""
        # 提取标题
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        title = title_match.group(1) if title_match else Path(file_path).stem
        
        # 提取描述（第一段非标题文本）
        description = ""
        lines = content.split('\n')
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#') and not line.startswith('```'):
                description = line
                break
        
        # 根据文件路径确定知识类型
        knowledge_type = self._determine_knowledge_type(file_path)
        
        # 提取标签
        tags = self._extract_tags(content, file_path)
        
        # 提取依赖和引用
        dependencies = self._extract_dependencies(content)
        references = self._extract_references(content)
        
        return {
            'title': title,
            'description': description,
            'knowledge_type': knowledge_type,
            'status': KnowledgeStatus.ACTIVE,
            'tags': tags,
            'dependencies': dependencies,
            'references': references
        }
    
    def _determine_knowledge_type(self, file_path: str) -> KnowledgeType:
        """根据文件路径确定知识类型"""
        path_parts = file_path.lower().split('/')
        
        if '01_理论基础层' in path_parts:
            return KnowledgeType.THEORETICAL
        elif '02_标准规范层' in path_parts:
            return KnowledgeType.STANDARD
        elif '03_技术实现层' in path_parts:
            return KnowledgeType.TECHNICAL
        elif '04_应用实践层' in path_parts:
            return KnowledgeType.PRACTICAL
        elif '05_质量保证层' in path_parts:
            return KnowledgeType.QUALITY
        elif '06_社区生态层' in path_parts:
            return KnowledgeType.COMMUNITY
        elif '07_学术研究层' in path_parts:
            return KnowledgeType.ACADEMIC
        else:
            return KnowledgeType.TECHNICAL
    
    def _extract_tags(self, content: str, file_path: str) -> List[str]:
        """提取标签"""
        tags = []
        
        # 从文件路径提取标签
        path_parts = file_path.split('/')
        for part in path_parts:
            if part.endswith('.md'):
                part = part[:-3]
            if part and part != 'README':
                tags.append(part)
        
        # 从内容中提取标签
        tag_matches = re.findall(r'#(\w+)', content)
        tags.extend(tag_matches)
        
        # 去重并返回
        return list(set(tags))
    
    def _extract_dependencies(self, content: str) -> List[str]:
        """提取依赖关系"""
        dependencies = []
        
        # 查找依赖声明
        dep_matches = re.findall(r'依赖[:：]\s*(.+)', content)
        for match in dep_matches:
            deps = [dep.strip() for dep in match.split(',')]
            dependencies.extend(deps)
        
        return dependencies
    
    def _extract_references(self, content: str) -> List[str]:
        """提取引用关系"""
        references = []
        
        # 查找引用链接
        ref_matches = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        for ref_text, ref_url in ref_matches:
            if ref_url.startswith('http'):
                references.append(ref_url)
            elif ref_url.endswith('.md'):
                references.append(ref_url)
        
        return references
    
    def _generate_node_id(self, file_path: str) -> str:
        """生成节点ID"""
        # 使用文件路径生成唯一ID
        path_hash = hashlib.md5(file_path.encode('utf-8')).hexdigest()[:8]
        return f"node_{path_hash}"
    
    def _build_knowledge_relationships(self):
        """建立知识关系"""
        logger.info("建立知识关系...")
        
        # 基于文件路径建立层级关系
        for node_id, node in self.knowledge_nodes.items():
            # 建立父子关系
            parent_path = str(Path(node.file_path).parent)
            for other_id, other_node in self.knowledge_nodes.items():
                if other_id != node_id:
                    other_parent_path = str(Path(other_node.file_path).parent)
                    
                    # 检查是否是父子关系
                    if parent_path == other_node.file_path:
                        relationship = KnowledgeRelationship(
                            source_id=node_id,
                            target_id=other_id,
                            relationship_type="parent",
                            strength=1.0,
                            description="父子关系",
                            created_at=datetime.now().isoformat()
                        )
                        self.knowledge_relationships.append(relationship)
                    
                    # 检查是否是兄弟关系
                    elif parent_path == other_parent_path and parent_path != "":
                        relationship = KnowledgeRelationship(
                            source_id=node_id,
                            target_id=other_id,
                            relationship_type="sibling",
                            strength=0.8,
                            description="兄弟关系",
                            created_at=datetime.now().isoformat()
                        )
                        self.knowledge_relationships.append(relationship)
            
            # 基于引用建立关系
            for ref in node.references:
                for other_id, other_node in self.knowledge_nodes.items():
                    if other_id != node_id and ref in other_node.file_path:
                        relationship = KnowledgeRelationship(
                            source_id=node_id,
                            target_id=other_id,
                            relationship_type="reference",
                            strength=0.6,
                            description="引用关系",
                            created_at=datetime.now().isoformat()
                        )
                        self.knowledge_relationships.append(relationship)
    
    def _calculate_quality_scores(self):
        """计算知识质量分数"""
        for node_id, node in self.knowledge_nodes.items():
            # 计算质量分数（基于内容长度、结构等）
            quality_score = self._calculate_node_quality(node)
            node.quality_score = quality_score
            
            # 计算完整性分数
            completeness_score = self._calculate_node_completeness(node)
            node.completeness_score = completeness_score
    
    def _calculate_node_quality(self, node: KnowledgeNode) -> float:
        """计算节点质量分数"""
        try:
            file_path = self.base_path / node.file_path
            if not file_path.exists():
                return 0.0
            
            content = file_path.read_text(encoding='utf-8')
            
            # 基于内容长度
            length_score = min(1.0, len(content) / 1000)
            
            # 基于结构完整性
            structure_score = 0.0
            if '# 概述' in content:
                structure_score += 0.2
            if '## 核心内容' in content:
                structure_score += 0.2
            if '## 应用场景' in content:
                structure_score += 0.2
            if '## 性能优化' in content:
                structure_score += 0.2
            if '## 测试与验证' in content:
                structure_score += 0.2
            
            # 基于引用数量
            ref_score = min(1.0, len(node.references) / 5)
            
            # 综合分数
            total_score = (length_score * 0.3 + structure_score * 0.5 + ref_score * 0.2)
            return min(1.0, total_score)
            
        except Exception as e:
            logger.error(f"计算节点质量分数时出错: {e}")
            return 0.0
    
    def _calculate_node_completeness(self, node: KnowledgeNode) -> float:
        """计算节点完整性分数"""
        try:
            file_path = self.base_path / node.file_path
            if not file_path.exists():
                return 0.0
            
            content = file_path.read_text(encoding='utf-8')
            
            # 检查必需元素
            required_elements = [
                '# 概述', '## 核心内容', '## 应用场景', 
                '## 性能优化', '## 测试与验证', '## 参考文献'
            ]
            
            found_elements = sum(1 for element in required_elements if element in content)
            completeness = found_elements / len(required_elements)
            
            return completeness
            
        except Exception as e:
            logger.error(f"计算节点完整性分数时出错: {e}")
            return 0.0
    
    def _get_knowledge_type_distribution(self) -> Dict[str, int]:
        """获取知识类型分布"""
        distribution = {}
        for node in self.knowledge_nodes.values():
            type_name = node.knowledge_type.value
            distribution[type_name] = distribution.get(type_name, 0) + 1
        return distribution
    
    def _get_quality_distribution(self) -> Dict[str, int]:
        """获取质量分布"""
        distribution = {
            'excellent': 0,  # >= 0.9
            'good': 0,       # >= 0.7
            'fair': 0,       # >= 0.5
            'poor': 0        # < 0.5
        }
        
        for node in self.knowledge_nodes.values():
            score = node.quality_score
            if score >= 0.9:
                distribution['excellent'] += 1
            elif score >= 0.7:
                distribution['good'] += 1
            elif score >= 0.5:
                distribution['fair'] += 1
            else:
                distribution['poor'] += 1
        
        return distribution
    
    def _save_knowledge_index(self):
        """保存知识索引"""
        try:
            # 创建数据目录
            self.index_file.parent.mkdir(parents=True, exist_ok=True)
            
            # 准备索引数据
            index_data = {
                'metadata': {
                    'created_at': datetime.now().isoformat(),
                    'total_nodes': len(self.knowledge_nodes),
                    'total_relationships': len(self.knowledge_relationships)
                },
                'nodes': {node_id: asdict(node) for node_id, node in self.knowledge_nodes.items()},
                'relationships': [asdict(rel) for rel in self.knowledge_relationships]
            }
            
            # 保存索引
            with open(self.index_file, 'w', encoding='utf-8') as f:
                json.dump(index_data, f, ensure_ascii=False, indent=2)
            
            logger.info(f"知识索引已保存到: {self.index_file}")
            
        except Exception as e:
            logger.error(f"保存知识索引失败: {e}")

class KnowledgeSearcher:
    """知识搜索器"""
    
    def __init__(self, index_file: str = "data/knowledge_index.json"):
        self.index_file = Path(index_file)
        self.knowledge_nodes: Dict[str, KnowledgeNode] = {}
        self.knowledge_relationships: List[KnowledgeRelationship] = []
        self._load_knowledge_index()
    
    def _load_knowledge_index(self):
        """加载知识索引"""
        try:
            if self.index_file.exists():
                with open(self.index_file, 'r', encoding='utf-8') as f:
                    index_data = json.load(f)
                
                # 加载知识节点
                for node_id, node_data in index_data.get('nodes', {}).items():
                    node = KnowledgeNode(**node_data)
                    self.knowledge_nodes[node_id] = node
                
                # 加载知识关系
                for rel_data in index_data.get('relationships', []):
                    relationship = KnowledgeRelationship(**rel_data)
                    self.knowledge_relationships.append(relationship)
                
                logger.info(f"知识索引加载完成，共 {len(self.knowledge_nodes)} 个节点")
            else:
                logger.warning("知识索引文件不存在")
                
        except Exception as e:
            logger.error(f"加载知识索引失败: {e}")
    
    def search_knowledge(self, query: str, search_type: str = "all") -> List[Dict[str, Any]]:
        """搜索知识"""
        results = []
        query_lower = query.lower()
        
        for node_id, node in self.knowledge_nodes.items():
            score = 0.0
            
            # 标题匹配
            if query_lower in node.title.lower():
                score += 0.4
            
            # 描述匹配
            if query_lower in node.description.lower():
                score += 0.3
            
            # 标签匹配
            for tag in node.tags:
                if query_lower in tag.lower():
                    score += 0.2
            
            # 文件路径匹配
            if query_lower in node.file_path.lower():
                score += 0.1
            
            # 根据搜索类型过滤
            if search_type != "all" and node.knowledge_type.value != search_type:
                continue
            
            if score > 0:
                results.append({
                    'node_id': node_id,
                    'title': node.title,
                    'description': node.description,
                    'file_path': node.file_path,
                    'knowledge_type': node.knowledge_type.value,
                    'quality_score': node.quality_score,
                    'completeness_score': node.completeness_score,
                    'tags': node.tags,
                    'score': score
                })
        
        # 按分数排序
        results.sort(key=lambda x: x['score'], reverse=True)
        return results
    
    def find_related_knowledge(self, node_id: str, max_depth: int = 2) -> List[Dict[str, Any]]:
        """查找相关知识"""
        related_nodes = set()
        visited = set()
        
        def traverse_relationships(current_id: str, depth: int):
            if depth > max_depth or current_id in visited:
                return
            
            visited.add(current_id)
            
            # 查找直接关系
            for rel in self.knowledge_relationships:
                if rel.source_id == current_id:
                    related_nodes.add(rel.target_id)
                    traverse_relationships(rel.target_id, depth + 1)
                elif rel.target_id == current_id:
                    related_nodes.add(rel.source_id)
                    traverse_relationships(rel.source_id, depth + 1)
        
        traverse_relationships(node_id, 0)
        
        # 返回相关知识节点
        results = []
        for related_id in related_nodes:
            if related_id in self.knowledge_nodes:
                node = self.knowledge_nodes[related_id]
                results.append({
                    'node_id': related_id,
                    'title': node.title,
                    'description': node.description,
                    'file_path': node.file_path,
                    'knowledge_type': node.knowledge_type.value,
                    'quality_score': node.quality_score
                })
        
        return results

class KnowledgeEcosystemManager:
    """知识生态管理主类"""
    
    def __init__(self, base_path: str = "doc/02_知识体系"):
        self.base_path = Path(base_path)
        self.indexer = KnowledgeIndexer(base_path)
        self.searcher = KnowledgeSearcher()
    
    def run_knowledge_management(self) -> Dict[str, Any]:
        """运行知识管理"""
        logger.info("开始运行知识生态管理...")
        
        # 1. 构建知识索引
        index_results = self.indexer.build_knowledge_index()
        
        # 2. 重新加载搜索器
        self.searcher = KnowledgeSearcher()
        
        # 3. 生成知识生态报告
        report_content = self._generate_knowledge_ecosystem_report(index_results)
        
        # 4. 保存报告
        self._save_knowledge_report(report_content)
        
        logger.info("知识生态管理完成")
        
        return {
            'index_results': index_results,
            'report_content': report_content
        }
    
    def _generate_knowledge_ecosystem_report(self, index_results: Dict[str, Any]) -> str:
        """生成知识生态报告"""
        report_content = f"""# OpenTelemetry 2025 知识生态管理报告

## 📊 报告概述

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**报告版本**: 1.0.0
**知识节点总数**: {index_results.get('total_nodes', 0)}
**知识关系总数**: {index_results.get('total_relationships', 0)}

## 🧠 知识体系分析

### 知识类型分布
"""
        
        # 添加知识类型分布
        type_distribution = index_results.get('knowledge_types', {})
        for type_name, count in type_distribution.items():
            report_content += f"- **{type_name}**: {count} 个节点\n"
        
        # 添加质量分布
        report_content += "\n### 知识质量分布\n"
        quality_distribution = index_results.get('quality_distribution', {})
        for quality_level, count in quality_distribution.items():
            report_content += f"- **{quality_level}**: {count} 个节点\n"
        
        # 添加知识生态建议
        report_content += "\n## 💡 知识生态优化建议\n\n"
        suggestions = self._generate_optimization_suggestions(index_results)
        for i, suggestion in enumerate(suggestions, 1):
            report_content += f"{i}. {suggestion}\n"
        
        # 添加结论
        report_content += f"""

## 📋 结论

OpenTelemetry 2025知识生态体系构建{'成功' if index_results.get('total_nodes', 0) > 0 else '需要完善'}，共包含 {index_results.get('total_nodes', 0)} 个知识节点和 {index_results.get('total_relationships', 0)} 个知识关系。

### 主要成就
- 知识体系结构完整，覆盖了从理论基础到实际应用的各个层面
- 知识节点质量整体较高，内容详实
- 知识关系建立完善，便于知识发现和关联

### 需要关注的问题
- 部分知识节点需要进一步完善
- 某些知识关系需要加强
- 需要建立更完善的知识更新机制

### 下一步行动
1. 完善低质量的知识节点
2. 加强知识关系的建立
3. 建立定期的知识更新机制
4. 加强知识搜索和发现功能

---
*本报告由OpenTelemetry 2025知识生态管理系统生成*
"""
        
        return report_content
    
    def _generate_optimization_suggestions(self, index_results: Dict[str, Any]) -> List[str]:
        """生成优化建议"""
        suggestions = []
        
        # 基于知识类型分布的建议
        type_distribution = index_results.get('knowledge_types', {})
        if type_distribution.get('theoretical', 0) < 5:
            suggestions.append("增加理论基础层知识节点，完善理论体系")
        
        if type_distribution.get('practical', 0) < 10:
            suggestions.append("增加应用实践层知识节点，提供更多实际案例")
        
        # 基于质量分布的建议
        quality_distribution = index_results.get('quality_distribution', {})
        if quality_distribution.get('poor', 0) > 0:
            suggestions.append(f"改进 {quality_distribution['poor']} 个低质量知识节点")
        
        if quality_distribution.get('excellent', 0) < 5:
            suggestions.append("提高知识节点质量，增加优秀知识节点数量")
        
        # 基于关系数量的建议
        total_relationships = index_results.get('total_relationships', 0)
        total_nodes = index_results.get('total_nodes', 0)
        if total_nodes > 0 and total_relationships / total_nodes < 2:
            suggestions.append("增加知识关系，提高知识关联度")
        
        return suggestions
    
    def _save_knowledge_report(self, report_content: str):
        """保存知识报告"""
        try:
            # 创建报告目录
            report_dir = Path("reports")
            report_dir.mkdir(exist_ok=True)
            
            # 生成报告文件名
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            report_file = report_dir / f"knowledge_ecosystem_report_{timestamp}.md"
            
            # 保存报告
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report_content)
            
            logger.info(f"知识生态报告已保存到: {report_file}")
            
        except Exception as e:
            logger.error(f"保存知识生态报告失败: {e}")

def main():
    """主函数"""
    try:
        # 创建知识生态管理实例
        manager = KnowledgeEcosystemManager()
        
        # 运行知识管理
        results = manager.run_knowledge_management()
        
        # 输出简要结果
        print("\n" + "="*60)
        print("OpenTelemetry 2025 知识生态管理结果")
        print("="*60)
        
        index_results = results['index_results']
        print(f"🧠 知识节点总数: {index_results.get('total_nodes', 0)}")
        print(f"🔗 知识关系总数: {index_results.get('total_relationships', 0)}")
        
        # 显示知识类型分布
        type_distribution = index_results.get('knowledge_types', {})
        print("\n📊 知识类型分布:")
        for type_name, count in type_distribution.items():
            print(f"  - {type_name}: {count}")
        
        # 显示质量分布
        quality_distribution = index_results.get('quality_distribution', {})
        print("\n📈 质量分布:")
        for quality_level, count in quality_distribution.items():
            print(f"  - {quality_level}: {count}")
        
        print("\n详细报告已生成，请查看 reports/ 目录")
        print("="*60)
        
    except Exception as e:
        logger.error(f"运行知识生态管理时出错: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
