#!/usr/bin/env python3
"""
OpenTelemetry 语义约定验证工具

用于验证遥测数据中的属性是否符合OpenTelemetry语义约定规范。
"""

import json
import re
import sys
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

class ValidationLevel(Enum):
    ERROR = "error"
    WARNING = "warning"
    INFO = "info"

@dataclass
class ValidationResult:
    level: ValidationLevel
    message: str
    attribute: str
    suggestion: Optional[str] = None

class SemanticValidator:
    """语义约定验证器"""
    
    def __init__(self):
        self.valid_namespaces = {
            'http', 'db', 'rpc', 'messaging', 'cloud', 'k8s', 'faas',
            'service', 'host', 'container', 'os', 'process', 'runtime'
        }
        
        self.required_attributes = {
            'http': ['http.method', 'http.url', 'http.status_code'],
            'db': ['db.system'],
            'rpc': ['rpc.system'],
            'messaging': ['messaging.system'],
            'cloud': ['cloud.provider'],
        }
        
        self.valid_values = {
            'http.method': ['GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'HEAD', 'OPTIONS'],
            'db.system': ['mysql', 'postgresql', 'redis', 'mongodb', 'sqlite', 'oracle', 'mssql'],
            'rpc.system': ['grpc', 'dubbo', 'thrift', 'jsonrpc'],
            'messaging.system': ['kafka', 'rabbitmq', 'nats', 'activemq', 'pulsar'],
            'cloud.provider': ['aws', 'azure', 'gcp', 'alibaba_cloud', 'tencent_cloud'],
        }
        
        self.deprecated_attributes = {
            'http.status': 'http.status_code',
            'db.name': 'db.sql.table',
        }

    def validate_attributes(self, attributes: Dict[str, any]) -> List[ValidationResult]:
        """验证属性字典"""
        results = []
        
        for attr_name, attr_value in attributes.items():
            results.extend(self.validate_attribute(attr_name, attr_value))
        
        # 检查必需属性
        results.extend(self.check_required_attributes(attributes))
        
        return results

    def validate_attribute(self, name: str, value: any) -> List[ValidationResult]:
        """验证单个属性"""
        results = []
        
        # 检查命名规范
        if not self.is_valid_attribute_name(name):
            results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"属性名 '{name}' 不符合命名规范",
                attribute=name,
                suggestion="使用小写字母和点号，如 'http.method'"
            ))
        
        # 检查命名空间
        namespace = name.split('.')[0]
        if namespace not in self.valid_namespaces:
            results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message=f"未知的命名空间 '{namespace}'",
                attribute=name,
                suggestion=f"考虑使用标准命名空间: {', '.join(self.valid_namespaces)}"
            ))
        
        # 检查废弃属性
        if name in self.deprecated_attributes:
            results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message=f"属性 '{name}' 已废弃",
                attribute=name,
                suggestion=f"使用 '{self.deprecated_attributes[name]}' 替代"
            ))
        
        # 检查有效值
        if name in self.valid_values:
            if str(value) not in self.valid_values[name]:
                results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message=f"属性 '{name}' 的值 '{value}' 不在有效值列表中",
                    attribute=name,
                    suggestion=f"有效值: {', '.join(self.valid_values[name])}"
                ))
        
        # 检查数据类型
        results.extend(self.validate_data_type(name, value))
        
        return results

    def is_valid_attribute_name(self, name: str) -> bool:
        """检查属性名是否符合规范"""
        # 使用小写字母和点号
        pattern = r'^[a-z][a-z0-9_]*(\.[a-z][a-z0-9_]*)*$'
        return bool(re.match(pattern, name))

    def validate_data_type(self, name: str, value: any) -> List[ValidationResult]:
        """验证数据类型"""
        results = []
        
        # HTTP状态码应该是整数
        if name == 'http.status_code':
            if not isinstance(value, int):
                results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message=f"'{name}' 应该是整数类型",
                    attribute=name,
                    suggestion=f"当前类型: {type(value).__name__}"
                ))
        
        # 内容长度应该是非负整数
        if name in ['http.request_content_length', 'http.response_content_length']:
            if not isinstance(value, int) or value < 0:
                results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message=f"'{name}' 应该是非负整数",
                    attribute=name,
                    suggestion=f"当前值: {value}"
                ))
        
        return results

    def check_required_attributes(self, attributes: Dict[str, any]) -> List[ValidationResult]:
        """检查必需属性"""
        results = []
        
        # 检查是否有HTTP相关属性但缺少必需属性
        has_http_attrs = any(attr.startswith('http.') for attr in attributes.keys())
        if has_http_attrs:
            for required_attr in self.required_attributes['http']:
                if required_attr not in attributes:
                    results.append(ValidationResult(
                        level=ValidationLevel.WARNING,
                        message=f"缺少必需的HTTP属性 '{required_attr}'",
                        attribute=required_attr,
                        suggestion="添加此属性以符合HTTP语义约定"
                    ))
        
        return results

    def validate_span(self, span_data: Dict) -> List[ValidationResult]:
        """验证Span数据"""
        results = []
        
        # 检查必需字段
        required_fields = ['name', 'span_id', 'trace_id']
        for field in required_fields:
            if field not in span_data:
                results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message=f"Span缺少必需字段 '{field}'",
                    attribute=field
                ))
        
        # 验证属性
        if 'attributes' in span_data:
            results.extend(self.validate_attributes(span_data['attributes']))
        
        return results

    def validate_resource(self, resource_data: Dict) -> List[ValidationResult]:
        """验证Resource数据"""
        results = []
        
        # 检查必需字段
        if 'attributes' not in resource_data:
            results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Resource缺少attributes字段",
                attribute="attributes"
            ))
            return results
        
        # 验证属性
        results.extend(self.validate_attributes(resource_data['attributes']))
        
        # 检查service.name
        if 'service.name' not in resource_data['attributes']:
            results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Resource缺少必需的service.name属性",
                attribute="service.name"
            ))
        
        return results

def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("用法: python semantic-validator.py <json-file>")
        sys.exit(1)
    
    validator = SemanticValidator()
    
    try:
        with open(sys.argv[1], 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        results = []
        
        # 验证Span
        if 'spans' in data:
            for span in data['spans']:
                results.extend(validator.validate_span(span))
        
        # 验证Resource
        if 'resource' in data:
            results.extend(validator.validate_resource(data['resource']))
        
        # 验证属性
        if 'attributes' in data:
            results.extend(validator.validate_attributes(data['attributes']))
        
        # 输出结果
        if not results:
            print("✅ 所有属性都符合语义约定规范")
        else:
            for result in results:
                level_icon = {
                    ValidationLevel.ERROR: "❌",
                    ValidationLevel.WARNING: "⚠️",
                    ValidationLevel.INFO: "ℹ️"
                }
                print(f"{level_icon[result.level]} {result.message}")
                if result.suggestion:
                    print(f"   建议: {result.suggestion}")
                print()
    
    except FileNotFoundError:
        print(f"错误: 文件 '{sys.argv[1]}' 不存在")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"错误: JSON解析失败 - {e}")
        sys.exit(1)
    except Exception as e:
        print(f"错误: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
