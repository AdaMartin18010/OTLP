#!/usr/bin/env python3
"""
OpenTelemetry 2025 文档同步工具

功能：
- 同步文档到多个目标
- 自动备份文档
- 版本控制集成
- 文档发布管理
"""

import os
import shutil
import subprocess
import json
import hashlib
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, asdict
from datetime import datetime
import argparse
import logging
import tempfile
import zipfile

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class SyncTarget:
    """同步目标"""
    name: str
    type: str  # 'local', 'remote', 'git', 's3'
    path: str
    config: Dict[str, Any]

@dataclass
class SyncResult:
    """同步结果"""
    target: str
    success: bool
    files_synced: int
    files_skipped: int
    files_failed: int
    error_message: Optional[str] = None
    duration: float = 0.0

@dataclass
class DocumentInfo:
    """文档信息"""
    path: str
    size: int
    modified: datetime
    hash: str
    status: str  # 'new', 'modified', 'unchanged', 'deleted'

class DocumentSynchronizer:
    """文档同步器"""
    
    def __init__(self, doc_root: str = "doc"):
        self.doc_root = Path(doc_root)
        self.targets = self._load_sync_targets()
        self.sync_history = self._load_sync_history()
    
    def _load_sync_targets(self) -> List[SyncTarget]:
        """加载同步目标配置"""
        targets = []
        
        # 本地备份目标
        targets.append(SyncTarget(
            name="local_backup",
            type="local",
            path="./backup",
            config={
                "create_timestamp": True,
                "compress": True,
                "exclude_patterns": [".git", "__pycache__", "*.pyc"]
            }
        ))
        
        # Git仓库目标
        targets.append(SyncTarget(
            name="git_repo",
            type="git",
            path=".",
            config={
                "remote": "origin",
                "branch": "main",
                "commit_message": "Auto-sync documents",
                "push": True
            }
        ))
        
        return targets
    
    def _load_sync_history(self) -> Dict[str, Any]:
        """加载同步历史"""
        history_file = self.doc_root / ".sync_history.json"
        
        if history_file.exists():
            try:
                with open(history_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception as e:
                logger.error(f"加载同步历史失败: {e}")
        
        return {
            "last_sync": None,
            "sync_count": 0,
            "targets": {}
        }
    
    def _save_sync_history(self):
        """保存同步历史"""
        history_file = self.doc_root / ".sync_history.json"
        
        try:
            with open(history_file, 'w', encoding='utf-8') as f:
                json.dump(self.sync_history, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logger.error(f"保存同步历史失败: {e}")
    
    def _calculate_file_hash(self, file_path: Path) -> str:
        """计算文件哈希值"""
        try:
            with open(file_path, 'rb') as f:
                content = f.read()
                return hashlib.md5(content).hexdigest()
        except Exception as e:
            logger.error(f"计算文件哈希失败 {file_path}: {e}")
            return ""
    
    def _get_document_info(self, file_path: Path) -> DocumentInfo:
        """获取文档信息"""
        stat = file_path.stat()
        
        return DocumentInfo(
            path=str(file_path.relative_to(self.doc_root)),
            size=stat.st_size,
            modified=datetime.fromtimestamp(stat.st_mtime),
            hash=self._calculate_file_hash(file_path),
            status="unknown"
        )
    
    def _scan_documents(self) -> List[DocumentInfo]:
        """扫描文档"""
        documents = []
        md_files = list(self.doc_root.rglob("*.md"))
        
        for md_file in md_files:
            # 跳过隐藏文件和临时文件
            if any(part.startswith('.') for part in md_file.parts):
                continue
            
            doc_info = self._get_document_info(md_file)
            documents.append(doc_info)
        
        return documents
    
    def _sync_to_local(self, target: SyncTarget, documents: List[DocumentInfo]) -> SyncResult:
        """同步到本地目录"""
        start_time = datetime.now()
        result = SyncResult(
            target=target.name,
            success=True,
            files_synced=0,
            files_skipped=0,
            files_failed=0
        )
        
        try:
            target_path = Path(target.path)
            
            # 创建时间戳目录
            if target.config.get("create_timestamp", False):
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                target_path = target_path / timestamp
            
            target_path.mkdir(parents=True, exist_ok=True)
            
            # 同步文件
            for doc in documents:
                try:
                    source_file = self.doc_root / doc.path
                    dest_file = target_path / doc.path
                    
                    # 创建目标目录
                    dest_file.parent.mkdir(parents=True, exist_ok=True)
                    
                    # 复制文件
                    shutil.copy2(source_file, dest_file)
                    result.files_synced += 1
                    
                except Exception as e:
                    logger.error(f"同步文件失败 {doc.path}: {e}")
                    result.files_failed += 1
            
            # 压缩备份
            if target.config.get("compress", False):
                self._compress_backup(target_path)
            
        except Exception as e:
            result.success = False
            result.error_message = str(e)
            logger.error(f"本地同步失败: {e}")
        
        result.duration = (datetime.now() - start_time).total_seconds()
        return result
    
    def _sync_to_git(self, target: SyncTarget, documents: List[DocumentInfo]) -> SyncResult:
        """同步到Git仓库"""
        start_time = datetime.now()
        result = SyncResult(
            target=target.name,
            success=True,
            files_synced=0,
            files_skipped=0,
            files_failed=0
        )
        
        try:
            # 检查Git状态
            git_status = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=self.doc_root,
                capture_output=True,
                text=True
            )
            
            if git_status.returncode != 0:
                raise Exception(f"Git状态检查失败: {git_status.stderr}")
            
            # 检查是否有变更
            if not git_status.stdout.strip():
                result.files_skipped = len(documents)
                logger.info("没有文件变更，跳过Git同步")
                return result
            
            # 添加所有变更
            add_result = subprocess.run(
                ["git", "add", "."],
                cwd=self.doc_root,
                capture_output=True,
                text=True
            )
            
            if add_result.returncode != 0:
                raise Exception(f"Git添加失败: {add_result.stderr}")
            
            # 提交变更
            commit_message = target.config.get("commit_message", "Auto-sync documents")
            commit_result = subprocess.run(
                ["git", "commit", "-m", commit_message],
                cwd=self.doc_root,
                capture_output=True,
                text=True
            )
            
            if commit_result.returncode != 0:
                if "nothing to commit" in commit_result.stdout:
                    result.files_skipped = len(documents)
                    logger.info("没有变更需要提交")
                else:
                    raise Exception(f"Git提交失败: {commit_result.stderr}")
            else:
                result.files_synced = len(documents)
                logger.info(f"Git提交成功: {commit_result.stdout}")
            
            # 推送到远程仓库
            if target.config.get("push", False):
                push_result = subprocess.run(
                    ["git", "push", target.config.get("remote", "origin"), target.config.get("branch", "main")],
                    cwd=self.doc_root,
                    capture_output=True,
                    text=True
                )
                
                if push_result.returncode != 0:
                    raise Exception(f"Git推送失败: {push_result.stderr}")
                
                logger.info("Git推送成功")
        
        except Exception as e:
            result.success = False
            result.error_message = str(e)
            logger.error(f"Git同步失败: {e}")
        
        result.duration = (datetime.now() - start_time).total_seconds()
        return result
    
    def _compress_backup(self, backup_path: Path):
        """压缩备份"""
        try:
            zip_path = backup_path.with_suffix('.zip')
            
            with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
                for file_path in backup_path.rglob('*'):
                    if file_path.is_file():
                        arcname = file_path.relative_to(backup_path)
                        zipf.write(file_path, arcname)
            
            # 删除原始目录
            shutil.rmtree(backup_path)
            
            logger.info(f"备份已压缩: {zip_path}")
        
        except Exception as e:
            logger.error(f"压缩备份失败: {e}")
    
    def sync_all_targets(self) -> List[SyncResult]:
        """同步到所有目标"""
        logger.info("开始同步到所有目标...")
        
        # 扫描文档
        documents = self._scan_documents()
        logger.info(f"扫描到 {len(documents)} 个文档")
        
        results = []
        
        for target in self.targets:
            logger.info(f"同步到目标: {target.name}")
            
            if target.type == "local":
                result = self._sync_to_local(target, documents)
            elif target.type == "git":
                result = self._sync_to_git(target, documents)
            else:
                logger.warning(f"不支持的目标类型: {target.type}")
                continue
            
            results.append(result)
            
            # 更新同步历史
            self.sync_history["targets"][target.name] = {
                "last_sync": datetime.now().isoformat(),
                "success": result.success,
                "files_synced": result.files_synced
            }
        
        # 更新总体同步历史
        self.sync_history["last_sync"] = datetime.now().isoformat()
        self.sync_history["sync_count"] += 1
        
        # 保存同步历史
        self._save_sync_history()
        
        return results
    
    def sync_to_target(self, target_name: str) -> Optional[SyncResult]:
        """同步到指定目标"""
        target = next((t for t in self.targets if t.name == target_name), None)
        
        if not target:
            logger.error(f"目标不存在: {target_name}")
            return None
        
        documents = self._scan_documents()
        
        if target.type == "local":
            return self._sync_to_local(target, documents)
        elif target.type == "git":
            return self._sync_to_git(target, documents)
        else:
            logger.error(f"不支持的目标类型: {target.type}")
            return None
    
    def create_backup(self, backup_name: Optional[str] = None) -> str:
        """创建备份"""
        if not backup_name:
            backup_name = f"backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        backup_path = Path("./backups") / backup_name
        backup_path.mkdir(parents=True, exist_ok=True)
        
        # 复制所有文档
        documents = self._scan_documents()
        for doc in documents:
            source_file = self.doc_root / doc.path
            dest_file = backup_path / doc.path
            dest_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_file, dest_file)
        
        # 压缩备份
        zip_path = backup_path.with_suffix('.zip')
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for file_path in backup_path.rglob('*'):
                if file_path.is_file():
                    arcname = file_path.relative_to(backup_path)
                    zipf.write(file_path, arcname)
        
        # 删除原始目录
        shutil.rmtree(backup_path)
        
        logger.info(f"备份已创建: {zip_path}")
        return str(zip_path)
    
    def restore_backup(self, backup_path: str) -> bool:
        """恢复备份"""
        try:
            backup_file = Path(backup_path)
            
            if not backup_file.exists():
                logger.error(f"备份文件不存在: {backup_path}")
                return False
            
            # 创建临时目录
            with tempfile.TemporaryDirectory() as temp_dir:
                temp_path = Path(temp_dir)
                
                # 解压备份
                with zipfile.ZipFile(backup_file, 'r') as zipf:
                    zipf.extractall(temp_path)
                
                # 复制文件到文档目录
                for file_path in temp_path.rglob('*'):
                    if file_path.is_file():
                        relative_path = file_path.relative_to(temp_path)
                        dest_file = self.doc_root / relative_path
                        dest_file.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(file_path, dest_file)
            
            logger.info(f"备份已恢复: {backup_path}")
            return True
        
        except Exception as e:
            logger.error(f"恢复备份失败: {e}")
            return False
    
    def generate_sync_report(self, results: List[SyncResult]) -> str:
        """生成同步报告"""
        report = []
        report.append("# 文档同步报告")
        report.append(f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}")
        report.append("")
        
        # 总体统计
        total_synced = sum(r.files_synced for r in results)
        total_skipped = sum(r.files_skipped for r in results)
        total_failed = sum(r.files_failed for r in results)
        success_count = sum(1 for r in results if r.success)
        
        report.append("## 📊 同步统计")
        report.append(f"- **成功目标**: {success_count}/{len(results)}")
        report.append(f"- **同步文件**: {total_synced}")
        report.append(f"- **跳过文件**: {total_skipped}")
        report.append(f"- **失败文件**: {total_failed}")
        report.append("")
        
        # 详细结果
        report.append("## 📋 详细结果")
        for result in results:
            status = "✅ 成功" if result.success else "❌ 失败"
            report.append(f"### {result.target} - {status}")
            report.append(f"- **同步文件**: {result.files_synced}")
            report.append(f"- **跳过文件**: {result.files_skipped}")
            report.append(f"- **失败文件**: {result.files_failed}")
            report.append(f"- **耗时**: {result.duration:.2f}秒")
            
            if result.error_message:
                report.append(f"- **错误信息**: {result.error_message}")
            
            report.append("")
        
        return "\n".join(report)
    
    def list_backups(self) -> List[str]:
        """列出所有备份"""
        backup_dir = Path("./backups")
        
        if not backup_dir.exists():
            return []
        
        backups = []
        for backup_file in backup_dir.glob("*.zip"):
            stat = backup_file.stat()
            backup_info = {
                "name": backup_file.name,
                "path": str(backup_file),
                "size": stat.st_size,
                "created": datetime.fromtimestamp(stat.st_ctime).isoformat()
            }
            backups.append(backup_info)
        
        return sorted(backups, key=lambda x: x["created"], reverse=True)

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="OpenTelemetry 2025 文档同步工具")
    parser.add_argument("--doc-root", default="doc", help="文档根目录")
    parser.add_argument("--sync-all", action="store_true", help="同步到所有目标")
    parser.add_argument("--sync-target", help="同步到指定目标")
    parser.add_argument("--create-backup", help="创建备份")
    parser.add_argument("--restore-backup", help="恢复备份")
    parser.add_argument("--list-backups", action="store_true", help="列出所有备份")
    parser.add_argument("--report", help="生成同步报告文件")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建同步器
    synchronizer = DocumentSynchronizer(args.doc_root)
    
    if args.sync_all:
        # 同步到所有目标
        results = synchronizer.sync_all_targets()
        
        # 生成报告
        if args.report:
            report_content = synchronizer.generate_sync_report(results)
            with open(args.report, 'w', encoding='utf-8') as f:
                f.write(report_content)
            print(f"同步报告已生成: {args.report}")
        
        # 输出摘要
        success_count = sum(1 for r in results if r.success)
        total_synced = sum(r.files_synced for r in results)
        print(f"同步完成: {success_count}/{len(results)} 个目标成功，共同步 {total_synced} 个文件")
    
    elif args.sync_target:
        # 同步到指定目标
        result = synchronizer.sync_to_target(args.sync_target)
        if result:
            status = "成功" if result.success else "失败"
            print(f"同步到 {args.sync_target}: {status}")
            print(f"同步文件: {result.files_synced}, 跳过: {result.files_skipped}, 失败: {result.files_failed}")
        else:
            print(f"同步到 {args.sync_target} 失败")
    
    elif args.create_backup:
        # 创建备份
        backup_path = synchronizer.create_backup(args.create_backup)
        print(f"备份已创建: {backup_path}")
    
    elif args.restore_backup:
        # 恢复备份
        if synchronizer.restore_backup(args.restore_backup):
            print(f"备份已恢复: {args.restore_backup}")
        else:
            print(f"恢复备份失败: {args.restore_backup}")
    
    elif args.list_backups:
        # 列出备份
        backups = synchronizer.list_backups()
        if backups:
            print("可用备份:")
            for backup in backups:
                size_mb = backup["size"] / (1024 * 1024)
                print(f"  - {backup['name']} ({size_mb:.2f}MB) - {backup['created']}")
        else:
            print("没有找到备份文件")
    
    else:
        print("请指定操作：--sync-all, --sync-target, --create-backup, --restore-backup, 或 --list-backups")

if __name__ == "__main__":
    main()
