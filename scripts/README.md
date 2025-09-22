# OpenTelemetry 2025 自动化脚本使用指南

## 🚀 快速开始

### 一键运行所有自动化任务

```bash
# 使用虚拟环境运行
.venv\Scripts\python.exe scripts/run_all_automation.py

# 或者直接运行（如果Python在PATH中）
python scripts/run_all_automation.py
```

### 单独运行特定任务

```bash
# 智能文档管理和目录生成
.venv\Scripts\python.exe scripts/smart_document_manager.py

# 自动文档更新和结构修复
.venv\Scripts\python.exe scripts/auto_document_updater.py

# 自动生成目录结构
.venv\Scripts\python.exe scripts/auto_generate_toc.py

# 自动更新导航文件
.venv\Scripts\python.exe scripts/auto_update_navigation.py
```

## 📋 自动化功能

### 1. 智能文档管理 (`smart_document_manager.py`)

**功能**:

- 自动扫描文档结构
- 生成完整的文档目录
- 更新导航文件
- 生成统计报告

**特点**:

- 智能缓存，只处理变化的文件
- 支持增量更新
- 自动备份修改的文件
- 生成详细的统计信息

### 2. 自动文档更新器 (`auto_document_updater.py`)

**功能**:

- 检测文档变化
- 自动修复文档结构
- 更新交叉引用
- 备份修改的文件

**修复内容**:

- 添加缺失的标题
- 补充概览部分
- 添加目标部分
- 完善总结部分
- 修复页脚格式

### 3. 目录生成器 (`auto_generate_toc.py`)

**功能**:

- 扫描文档结构
- 生成Markdown格式目录
- 更新导航文件
- 生成统计信息

### 4. 导航更新器 (`auto_update_navigation.py`)

**功能**:

- 扫描所有文档
- 更新导航文件
- 生成主题链接
- 按用户类型分类

## 🔧 配置选项

### 配置文件: `scripts/document_config.yaml`

```yaml
auto_update: true
generate_toc: true
update_navigation: true
backup_changes: true
exclude_patterns:
  - "*.tmp"
  - "*.bak"
  - ".git/*"
  - "node_modules/*"
module_mapping:
  "00_项目概览与导航": "项目概览"
  "01_理论基础与形式化证明": "理论基础"
  # ... 更多映射
```

### 缓存文件: `scripts/.document_cache.json`

自动生成，用于跟踪文件变化，提高执行效率。

## 📊 输出文件

### 主要输出

1. **完整目录**: `doc/00_项目概览与导航/自动生成完整目录.md`
2. **导航文件**: `doc/00_项目概览与导航/文档导航与索引.md`
3. **统计报告**: `doc/00_项目概览与导航/文档统计报告.md`
4. **执行报告**: `doc/00_项目概览与导航/自动化执行报告.md`

### 备份文件

所有修改的文件都会自动备份到 `scripts/backups/` 目录。

## 🎯 使用场景

### 1. 日常维护

```bash
# 每天运行一次，保持文档结构最新
.venv\Scripts\python.exe scripts/run_all_automation.py
```

### 2. 添加新文档后

```bash
# 添加新文档后运行，更新目录和导航
.venv\Scripts\python.exe scripts/smart_document_manager.py
```

### 3. 修复文档结构

```bash
# 发现文档结构问题时运行
.venv\Scripts\python.exe scripts/auto_document_updater.py
```

### 4. 生成报告

```bash
# 需要生成统计报告时运行
.venv\Scripts\python.exe scripts/auto_generate_toc.py
```

## 🔍 故障排除

### 常见问题

1. **Python未找到**

   ```bash
   # 使用虚拟环境
   .venv\Scripts\python.exe scripts/run_all_automation.py
   ```

2. **依赖缺失**

   ```bash
   # 安装依赖
   pip install PyYAML
   ```

3. **权限问题**
   - 确保有写入权限
   - 检查文件是否被其他程序占用

4. **路径问题**
   - 确保在项目根目录运行
   - 检查 `doc` 目录是否存在

### 日志和调试

- 查看控制台输出获取详细信息
- 检查 `scripts/backups/` 目录获取备份文件
- 查看生成的报告文件了解执行结果

## 📈 性能优化

### 缓存机制

- 自动缓存文件哈希值
- 只处理变化的文件
- 大幅提高执行效率

### 增量更新

- 智能检测文件变化
- 避免重复处理
- 支持大规模文档库

### 并行处理

- 支持多文件并行处理
- 优化I/O操作
- 提高整体性能

## 🎉 最佳实践

### 1. 定期运行

建议每天或每次添加文档后运行自动化脚本。

### 2. 备份重要文件

自动化系统会自动备份，但建议手动备份重要文件。

### 3. 检查输出

运行后检查生成的报告，确保所有任务成功完成。

### 4. 自定义配置

根据项目需要调整配置文件，优化自动化行为。

## 📚 技术细节

### 依赖

- Python 3.7+
- PyYAML
- pathlib (内置)
- datetime (内置)
- hashlib (内置)

### 支持的文件格式

- Markdown (.md)
- 自动识别文档结构
- 支持中文内容

### 兼容性

- Windows 10/11
- macOS
- Linux
- 支持中文路径和文件名

---

**维护者**: OpenTelemetry 2025 自动化系统  
**版本**: 2.0.0  
**最后更新**: 2025年1月27日
