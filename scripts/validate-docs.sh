#!/usr/bin/env bash
set -euo pipefail
DOC_PATH=${1:-docs}

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

  # navigation links
  if ! grep -qE '^>\s+📚 \*\*文档导航\*\*:' "$f"; then
    warns+=("File $(basename "$f") is missing navigation links")
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
# exit non-zero only on errors
((${#errors[@]}>0)) && exit 1 || exit 0
