#!/usr/bin/env python3
"""
OpenTelemetry 2025年知识管理系统
基于六层知识体系的知识获取、组织、应用和维护系统
"""

import os
import yaml
import json
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional

class KnowledgeManager:
    def __init__(self, base_path: str = "doc/02_知识体系"):
        self.base_path = Path(base_path)
        self.knowledge_config = self.load_config()
        self.knowledge_index = {}
        self.relationships = {}
    
    def load_config(self) -> Dict[str, Any]:
        """加载知识管理配置"""
        config_path = "config/knowledge_management.yaml"
        if os.path.exists(config_path):
            with open(config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "knowledge_layers": {
                "01_理论基础层": {
                    "categories": ["数学基础", "形式化验证", "理论证明"],
                    "description": "理论基础与形式化证明"
                },
                "02_标准规范层": {
                    "categories": ["国际标准", "行业标准", "技术标准"],
                    "description": "标准规范与最佳实践"
                },
                "03_技术实现层": {
                    "categories": ["协议实现", "SDK开发", "工具链"],
                    "description": "技术实现与开发工具"
                },
                "04_应用实践层": {
                    "categories": ["行业应用", "部署实践", "运维实践"],
                    "description": "应用实践与运维经验"
                },
                "05_质量保证层": {
                    "categories": ["测试框架", "验证方法", "性能基准"],
                    "description": "质量保证与验证体系"
                },
                "06_社区生态层": {
                    "categories": ["学术社区", "开源社区", "商业生态"],
                    "description": "社区生态与治理体系"
                }
            },
            "quality_standards": {
                "min_content_length": 500,
                "required_sections": ["概述", "核心内容", "应用场景", "参考文献"],
                "update_frequency": "weekly"
            }
        }
    
    def create_knowledge_item(self, layer: str, category: str, title: str, content: str, 
                            metadata: Optional[Dict[str, Any]] = None) -> str:
        """创建知识条目"""
        # 验证层级和分类
        if not self.validate_layer_category(layer, category):
            raise ValueError(f"无效的层级或分类: {layer}/{category}")
        
        # 创建文件路径
        item_path = self.base_path / layer / category / f"{title}.md"
        item_path.parent.mkdir(parents=True, exist_ok=True)
        
        # 生成内容
        full_content = self.generate_knowledge_content(title, content, metadata)
        
        # 写入文件
        with open(item_path, 'w', encoding='utf-8') as f:
            f.write(full_content)
        
        # 更新索引
        self.update_knowledge_index(layer, category, title, str(item_path), metadata)
        
        # 建立关系
        self.establish_relationships(layer, category, title, metadata)
        
        return str(item_path)
    
    def validate_layer_category(self, layer: str, category: str) -> bool:
        """验证层级和分类"""
        layers = self.knowledge_config.get("knowledge_layers", {})
        if layer not in layers:
            return False
        
        categories = layers[layer].get("categories", [])
        return category in categories
    
    def generate_knowledge_content(self, title: str, content: str, 
                                 metadata: Optional[Dict[str, Any]] = None) -> str:
        """生成知识内容"""
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # 生成文档头部
        header = f"""# {title}

**创建时间**: {timestamp}  
**最后更新**: {timestamp}  
**知识ID**: {self.generate_knowledge_id(title)}  

"""
        
        # 添加元数据
        if metadata:
            header += "## 元数据\n\n"
            for key, value in metadata.items():
                header += f"- **{key}**: {value}\n"
            header += "\n"
        
        # 添加标准章节
        sections = self.knowledge_config["quality_standards"]["required_sections"]
        for section in sections:
            if section not in content:
                header += f"## {section}\n\n*待完善*\n\n"
        
        # 添加主要内容
        header += content
        
        # 添加文档尾部
        footer = f"""

---

## 相关资源

- [知识体系导航](../README.md)
- [相关文档](#)
- [外部链接](#)

## 贡献指南

如需更新此文档，请：
1. 确保内容准确性和完整性
2. 遵循文档格式规范
3. 添加必要的参考文献
4. 更新最后修改时间

---

*本文档是OpenTelemetry 2025年知识体系的一部分*  
*最后更新: {timestamp}*
"""
        
        return header + footer
    
    def generate_knowledge_id(self, title: str) -> str:
        """生成知识ID"""
        timestamp = datetime.now().strftime("%Y%m%d")
        hash_obj = hashlib.md5(title.encode('utf-8'))
        short_hash = hash_obj.hexdigest()[:8]
        return f"KNOW_{timestamp}_{short_hash}"
    
    def update_knowledge_index(self, layer: str, category: str, title: str, 
                             path: str, metadata: Optional[Dict[str, Any]] = None):
        """更新知识索引"""
        index_path = self.base_path / layer / "index.yaml"
        
        if index_path.exists():
            with open(index_path, 'r', encoding='utf-8') as f:
                index = yaml.safe_load(f) or {}
        else:
            index = {}
        
        if category not in index:
            index[category] = []
        
        # 检查是否已存在
        existing_item = None
        for item in index[category]:
            if item.get("title") == title:
                existing_item = item
                break
        
        if existing_item:
            # 更新现有条目
            existing_item.update({
                "path": path,
                "updated": datetime.now().isoformat(),
                "metadata": metadata or {}
            })
        else:
            # 添加新条目
            index[category].append({
                "title": title,
                "path": path,
                "created": datetime.now().isoformat(),
                "updated": datetime.now().isoformat(),
                "metadata": metadata or {}
            })
        
        with open(index_path, 'w', encoding='utf-8') as f:
            yaml.dump(index, f, default_flow_style=False, allow_unicode=True)
    
    def establish_relationships(self, layer: str, category: str, title: str, 
                              metadata: Optional[Dict[str, Any]] = None):
        """建立知识关系"""
        if not metadata:
            return
        
        relationships = metadata.get("relationships", {})
        knowledge_id = self.generate_knowledge_id(title)
        
        if knowledge_id not in self.relationships:
            self.relationships[knowledge_id] = {
                "title": title,
                "layer": layer,
                "category": category,
                "relationships": {}
            }
        
        for rel_type, rel_items in relationships.items():
            self.relationships[knowledge_id]["relationships"][rel_type] = rel_items
    
    def search_knowledge(self, query: str, layer: Optional[str] = None, 
                        category: Optional[str] = None) -> List[Dict[str, Any]]:
        """搜索知识"""
        results = []
        
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir() and (layer is None or layer_path.name == layer):
                index_path = layer_path / "index.yaml"
                if index_path.exists():
                    with open(index_path, 'r', encoding='utf-8') as f:
                        index = yaml.safe_load(f) or {}
                    
                    for cat_name, items in index.items():
                        if category is None or cat_name == category:
                            for item in items:
                                if self.matches_query(item, query):
                                    results.append({
                                        "layer": layer_path.name,
                                        "category": cat_name,
                                        "item": item,
                                        "relevance_score": self.calculate_relevance(item, query)
                                    })
        
        # 按相关性排序
        results.sort(key=lambda x: x["relevance_score"], reverse=True)
        return results
    
    def matches_query(self, item: Dict[str, Any], query: str) -> bool:
        """检查项目是否匹配查询"""
        query_lower = query.lower()
        
        # 检查标题
        if query_lower in item.get("title", "").lower():
            return True
        
        # 检查元数据
        metadata = item.get("metadata", {})
        for value in metadata.values():
            if isinstance(value, str) and query_lower in value.lower():
                return True
        
        return False
    
    def calculate_relevance(self, item: Dict[str, Any], query: str) -> float:
        """计算相关性分数"""
        query_lower = query.lower()
        score = 0.0
        
        # 标题匹配权重最高
        title = item.get("title", "").lower()
        if query_lower in title:
            score += 10.0
        
        # 元数据匹配
        metadata = item.get("metadata", {})
        for value in metadata.values():
            if isinstance(value, str) and query_lower in value.lower():
                score += 5.0
        
        return score
    
    def get_knowledge_statistics(self) -> Dict[str, Any]:
        """获取知识统计信息"""
        stats = {
            "total_layers": 0,
            "total_categories": 0,
            "total_items": 0,
            "layer_details": {},
            "category_details": {},
            "recent_updates": []
        }
        
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir() and layer_path.name.startswith(("01_", "02_", "03_", "04_", "05_", "06_")):
                stats["total_layers"] += 1
                layer_name = layer_path.name
                layer_stats = {
                    "categories": 0,
                    "items": 0,
                    "last_updated": None
                }
                
                index_path = layer_path / "index.yaml"
                if index_path.exists():
                    with open(index_path, 'r', encoding='utf-8') as f:
                        index = yaml.safe_load(f) or {}
                    
                    for category, items in index.items():
                        stats["total_categories"] += 1
                        layer_stats["categories"] += 1
                        layer_stats["items"] += len(items)
                        stats["total_items"] += len(items)
                        
                        # 统计分类详情
                        if category not in stats["category_details"]:
                            stats["category_details"][category] = 0
                        stats["category_details"][category] += len(items)
                        
                        # 收集最近更新
                        for item in items:
                            updated = item.get("updated", item.get("created", ""))
                            if updated:
                                stats["recent_updates"].append({
                                    "title": item["title"],
                                    "layer": layer_name,
                                    "category": category,
                                    "updated": updated
                                })
                
                stats["layer_details"][layer_name] = layer_stats
        
        # 按更新时间排序最近更新
        stats["recent_updates"].sort(key=lambda x: x["updated"], reverse=True)
        stats["recent_updates"] = stats["recent_updates"][:10]  # 只保留最近10个
        
        return stats
    
    def generate_knowledge_report(self) -> Dict[str, Any]:
        """生成知识报告"""
        stats = self.get_knowledge_statistics()
        
        report = {
            "timestamp": datetime.now().isoformat(),
            "statistics": stats,
            "quality_metrics": self.calculate_quality_metrics(),
            "recommendations": self.generate_recommendations(stats)
        }
        
        return report
    
    def calculate_quality_metrics(self) -> Dict[str, Any]:
        """计算质量指标"""
        metrics = {
            "completeness": 0.0,
            "consistency": 0.0,
            "currency": 0.0,
            "overall_quality": 0.0
        }
        
        # 计算完整性
        expected_layers = len(self.knowledge_config["knowledge_layers"])
        actual_layers = 0
        
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir() and layer_path.name.startswith(("01_", "02_", "03_", "04_", "05_", "06_")):
                actual_layers += 1
        
        metrics["completeness"] = (actual_layers / expected_layers) * 100
        
        # 计算一致性（基于索引完整性）
        total_items = 0
        indexed_items = 0
        
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir():
                index_path = layer_path / "index.yaml"
                if index_path.exists():
                    with open(index_path, 'r', encoding='utf-8') as f:
                        index = yaml.safe_load(f) or {}
                    
                    for category, items in index.items():
                        indexed_items += len(items)
        
        # 统计实际文件数量
        for md_file in self.base_path.rglob("*.md"):
            if md_file.name != "README.md" and md_file.name != "index.yaml":
                total_items += 1
        
        if total_items > 0:
            metrics["consistency"] = (indexed_items / total_items) * 100
        
        # 计算时效性（基于最近更新时间）
        recent_count = 0
        total_count = 0
        
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir():
                index_path = layer_path / "index.yaml"
                if index_path.exists():
                    with open(index_path, 'r', encoding='utf-8') as f:
                        index = yaml.safe_load(f) or {}
                    
                    for category, items in index.items():
                        for item in items:
                            total_count += 1
                            updated = item.get("updated", item.get("created", ""))
                            if updated:
                                try:
                                    update_time = datetime.fromisoformat(updated.replace('Z', '+00:00'))
                                    if (datetime.now() - update_time).days <= 30:
                                        recent_count += 1
                                except:
                                    pass
        
        if total_count > 0:
            metrics["currency"] = (recent_count / total_count) * 100
        
        # 计算总体质量
        metrics["overall_quality"] = (metrics["completeness"] + metrics["consistency"] + metrics["currency"]) / 3
        
        return metrics
    
    def generate_recommendations(self, stats: Dict[str, Any]) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        # 完整性建议
        if stats["total_layers"] < 6:
            recommendations.append("完善知识体系：确保所有6个层级都有内容")
        
        # 一致性建议
        for category, count in stats["category_details"].items():
            if count == 0:
                recommendations.append(f"补充分类内容：{category}分类缺少内容")
        
        # 时效性建议
        if len(stats["recent_updates"]) < 5:
            recommendations.append("更新知识内容：最近更新的内容较少，建议定期更新")
        
        # 质量建议
        quality_metrics = self.calculate_quality_metrics()
        if quality_metrics["overall_quality"] < 80:
            recommendations.append("提升知识质量：整体质量分数较低，需要改进")
        
        return recommendations
    
    def export_knowledge_base(self, output_path: str = "exports/knowledge_base.json"):
        """导出知识库"""
        export_data = {
            "export_timestamp": datetime.now().isoformat(),
            "knowledge_config": self.knowledge_config,
            "statistics": self.get_knowledge_statistics(),
            "relationships": self.relationships,
            "layers": {}
        }
        
        # 导出各层级内容
        for layer_path in self.base_path.iterdir():
            if layer_path.is_dir() and layer_path.name.startswith(("01_", "02_", "03_", "04_", "05_", "06_")):
                layer_name = layer_path.name
                export_data["layers"][layer_name] = {}
                
                index_path = layer_path / "index.yaml"
                if index_path.exists():
                    with open(index_path, 'r', encoding='utf-8') as f:
                        index = yaml.safe_load(f) or {}
                    
                    for category, items in index.items():
                        export_data["layers"][layer_name][category] = items
        
        # 创建输出目录
        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        # 写入导出文件
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(export_data, f, indent=2, ensure_ascii=False)
        
        return str(output_file)

def main():
    """主函数"""
    km = KnowledgeManager()
    
    print("OpenTelemetry 2025年知识管理系统")
    print("=" * 50)
    
    # 显示统计信息
    stats = km.get_knowledge_statistics()
    print(f"知识体系统计:")
    print(f"  总层级数: {stats['total_layers']}")
    print(f"  总分类数: {stats['total_categories']}")
    print(f"  总条目数: {stats['total_items']}")
    print()
    
    # 显示质量指标
    quality_metrics = km.calculate_quality_metrics()
    print(f"质量指标:")
    print(f"  完整性: {quality_metrics['completeness']:.2f}%")
    print(f"  一致性: {quality_metrics['consistency']:.2f}%")
    print(f"  时效性: {quality_metrics['currency']:.2f}%")
    print(f"  总体质量: {quality_metrics['overall_quality']:.2f}%")
    print()
    
    # 生成报告
    report = km.generate_knowledge_report()
    print("改进建议:")
    for i, recommendation in enumerate(report["recommendations"], 1):
        print(f"  {i}. {recommendation}")
    
    # 导出知识库
    export_file = km.export_knowledge_base()
    print(f"\n知识库已导出至: {export_file}")

if __name__ == "__main__":
    main()
