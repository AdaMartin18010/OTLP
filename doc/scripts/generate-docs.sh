#!/usr/bin/env bash
set -euo pipefail
OUT_DIR=${1:-docs}

mkdir -p "$OUT_DIR"

# STATS.md
stats_file="$OUT_DIR/STATS.md"
mapfile -t files < <(find "$OUT_DIR" -type f -name "*.md" | sort)

count=${#files[@]}
lines=0; words=0; chars=0
for f in "${files[@]}"; do
  l=$(wc -l < "$f" | tr -d ' ')
  w=$(wc -w < "$f" | tr -d ' ')
  c=$(wc -m < "$f" | tr -d ' ')
  lines=$((lines+l)); words=$((words+w)); chars=$((chars+c))
done

{
  echo "# 文档统计信息"
  echo
  echo "> 📚 **文档导航**: [返回文档索引](INDEX.md) | [文档状态](STATUS.md) | [格式标准](FORMAT_STANDARDS.md)"
  echo "> 最后更新: $(date +%F)"
  echo
  echo "## 总体统计"
  echo
  echo "- **文档数量**: $count 个"
  echo "- **总行数**: $lines 行"
  echo "- **总字数**: $words 字"
  echo "- **总字符数**: $chars 字符"
  echo
  echo "## 文档详情"
  echo
  echo "| 文件名 | 行数 | 字数 | 字符数 | 最后修改 |"
  echo "|--------|------|------|--------|----------|"
  for f in "${files[@]}"; do
    bn=$(basename "$f")
    l=$(wc -l < "$f" | tr -d ' ')
    w=$(wc -w < "$f" | tr -d ' ')
    c=$(wc -m < "$f" | tr -d ' ')
    m=$(date -r "$f" +"%Y-%m-%d %H:%M")
    echo "| [$bn]($bn) | $l | $w | $c | $m |"
  done
  echo "## 生成时间"
  echo
  echo "*统计生成时间: $(date +"%Y-%m-%d %H:%M:%S")*"
  echo
  echo "### 示例"
  echo
  echo '```bash'
  echo '# 重新生成统计与目录'
  echo './scripts/generate-docs.sh'
  echo '```'
  echo
  echo '---'
  echo
  echo '*此文件由文档生成工具自动创建，请勿手动编辑*'
} > "$stats_file"

# TOC.md
{
  echo "# 文档目录"
  echo
  echo "> 📚 **文档导航**: [返回文档索引](INDEX.md) | [文档状态](STATUS.md)"
  echo "> 最后更新: $(date +%F)"
  echo
  echo "## 核心文档"
  echo
  for n in QUICK_START.md TUTORIALS.md API_REFERENCE.md ARCHITECTURE.md TERMS.md SEMANTIC_CONVENTIONS.md; do
    [[ -f "$OUT_DIR/$n" ]] && echo "- [$n]($n)"
  done
  echo "## 实践指南"
  echo
  for n in DEPLOYMENT_GUIDE.md INTEGRATION_GUIDE.md PERFORMANCE_GUIDE.md SECURITY_GUIDE.md TROUBLESHOOTING.md; do
    [[ -f "$OUT_DIR/$n" ]] && echo "- [$n]($n)"
  done
  echo "## 教育与研究"
  echo
  for n in COURSE_ALIGNMENT.md FORMAL_PROOFS.md; do
    [[ -f "$OUT_DIR/$n" ]] && echo "- [$n]($n)"
  done
  echo "## 项目状态"
  echo
  for n in STATUS.md FORMAT_STANDARDS.md STATS.md; do
    [[ -f "$OUT_DIR/$n" ]] && echo "- [$n]($n)"
  done
  echo "### 示例"
  echo
  echo '```bash'
  echo 'ls docs | grep ".md"'
  echo '```'
  echo
  echo '---'
  echo
  echo "*此目录由文档生成工具自动创建，最后更新时间: $(date +"%Y-%m-%d %H:%M:%S")*"
} > "$OUT_DIR/TOC.md"

printf "生成完成：\n- %s\n- %s\n" "$stats_file" "$OUT_DIR/TOC.md"
