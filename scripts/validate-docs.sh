#!/usr/bin/env bash
set -euo pipefail

print_help() {
  cat <<'EOF'
用法: ./scripts/validate-docs.sh [--path <dir>] [--strict] [--no-nav] [--help]

选项:
  --path <dir>   指定文档目录（默认 docs）
  --strict       将所有警告视为错误（非零退出）
  --no-nav       不要求“文档导航”提示块
  -h, --help     显示帮助
EOF
}

DOC_PATH="docs"
STRICT=0
CHECK_NAV=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    --path)
      DOC_PATH=${2:-}
      if [[ -z "$DOC_PATH" ]]; then echo "--path 需要一个目录" >&2; exit 2; fi
      shift 2 ;;
    --strict)
      STRICT=1; shift ;;
    --no-nav)
      CHECK_NAV=0; shift ;;
    -h|--help)
      print_help; exit 0 ;;
    *)
      echo "未知参数: $1" >&2; print_help; exit 2 ;;
  esac
done

if [[ ! -d "$DOC_PATH" ]]; then
  echo "文档目录不存在: $DOC_PATH" >&2
  exit 1
fi

warns=()
errors=()

# collect md files
mapfile -t files < <(find "$DOC_PATH" -type f -name "*.md" | sort)

# helper to print results
print_results() {
  echo "Validation Results:"
  if ((${#errors[@]}==0 && ${#warns[@]}==0)); then
    echo "✅ All checks passed! Document quality is good."
    return 0
  fi
  if ((${#errors[@]}>0)); then
    echo ""
    echo "❌ Found ${#errors[@]} errors:"
    for e in "${errors[@]}"; do echo "  • $e"; done
  fi
  if ((${#warns[@]}>0)); then
    echo ""
    echo "⚠️  Found ${#warns[@]} warnings:"
    for w in "${warns[@]}"; do echo "  • $w"; done
  fi
}

for f in "${files[@]}"; do
  # main title
  if ! grep -qE '^#\s+' "$f"; then
    warns+=("File $(basename "$f") is missing main title")
  fi

  # navigation links（可选）
  if (( CHECK_NAV==1 )); then
    if ! grep -qE '^>\s+📚 \*\*文档导航\*\*:' "$f"; then
      warns+=("File $(basename "$f") is missing navigation links")
    fi
  fi

  # update date
  if ! grep -qE '最后更新|更新时间|Last updated' "$f"; then
    warns+=("File $(basename "$f") is missing update date information")
  fi

  # code block language markers (only opening fences)
  inside=0
  lineno=0
  while IFS='' read -r line; do
    lineno=$((lineno+1))
    if [[ "$line" =~ ^```([A-Za-z0-9_-]+)?[[:space:]]*$ ]]; then
      if ((inside==0)); then
        lang=${BASH_REMATCH[1]:-}
        if [[ -z "${lang}" ]]; then
          warns+=("File $(basename "$f") has unmarked language code block at line $lineno")
        fi
        inside=1
      else
        inside=0
      fi
    fi
  done < "$f"

  # link existence (exclude code blocks, external links, and anchors)
  inside=0
  lineno=0
  while IFS='' read -r line; do
    lineno=$((lineno+1))
    if [[ "$line" =~ ^``` ]]; then
      (( inside = 1 - inside ))
      continue
    fi
    ((inside==1)) && continue
    while [[ "$line" =~ \[([^\]]+)\]\(([^)]+)\) ]]; do
      text=${BASH_REMATCH[1]}
      url=${BASH_REMATCH[2]}
      # trim rest for next loop
      idx=$(expr index "$line" ")")
      line=${line:$idx}
      # external
      [[ "$url" =~ ^https?:// ]] && continue
      # anchors
      [[ "$url" =~ ^# ]] && continue
      # normalize path
      if [[ "$url" =~ ^/ ]]; then
        target="${PWD}/${url#/}"
      else
        dir=$(dirname "$f")
        target="$dir/$url"
      fi
      # strip anchor part if any
      target="${target%%#*}"
      if [[ ! -e "$target" ]]; then
        warns+=("File $(basename "$f") link '$text' -> '$url' points to non-existent file: $target")
      fi
    done
  done < "$f"

done

print_results

# exit strategy
if (( ${#errors[@]} > 0 )); then
  exit 1
fi

if (( STRICT==1 && ${#warns[@]} > 0 )); then
  exit 2
fi

exit 0
