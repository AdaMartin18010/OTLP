#!/bin/bash
# ICSE 2026 Paper Compilation Script (Bash)
# Usage: ./compile.sh [clean]

MAIN_FILE="ICSE2026_Paper_Main"

echo "========================================"
echo "ICSE 2026 Paper Compilation Script"
echo "========================================"
echo ""

# Check if pdflatex is available
if ! command -v pdflatex &> /dev/null; then
    echo "ERROR: pdflatex not found!"
    echo ""
    echo "Please install LaTeX first:"
    echo "  Ubuntu/Debian: sudo apt-get install texlive-full"
    echo "  Fedora/CentOS: sudo yum install texlive-scheme-full"
    echo "  macOS: brew install --cask mactex"
    echo ""
    exit 1
fi

# Clean mode
if [ "$1" = "clean" ]; then
    echo "Cleaning temporary files..."
    
    rm -f *.aux *.bbl *.blg *.log *.out *.toc *.lof *.lot
    rm -f *.fls *.fdb_latexmk *.synctex.gz *.nav *.snm *.vrb
    rm -f *.bcf *.run.xml
    
    echo "Cleanup complete!"
    exit 0
fi

# Compilation
echo "Step 1/4: First pdflatex pass..."
pdflatex -interaction=nonstopmode "${MAIN_FILE}.tex" > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "ERROR: First pdflatex pass failed!"
    echo "Check ${MAIN_FILE}.log for details"
    exit 1
fi
echo "  ✓ Complete"

echo "Step 2/4: Running bibtex..."
bibtex "${MAIN_FILE}" > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "WARNING: bibtex had issues (this may be OK)"
fi
echo "  ✓ Complete"

echo "Step 3/4: Second pdflatex pass..."
pdflatex -interaction=nonstopmode "${MAIN_FILE}.tex" > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "ERROR: Second pdflatex pass failed!"
    exit 1
fi
echo "  ✓ Complete"

echo "Step 4/4: Third pdflatex pass (resolving references)..."
pdflatex -interaction=nonstopmode "${MAIN_FILE}.tex" > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "ERROR: Third pdflatex pass failed!"
    exit 1
fi
echo "  ✓ Complete"

echo ""
echo "========================================"
echo "Compilation Successful! 🎉"
echo "========================================"
echo ""
echo "Output: ${MAIN_FILE}.pdf"
echo ""

# Check PDF size
if [ -f "${MAIN_FILE}.pdf" ]; then
    SIZE=$(du -h "${MAIN_FILE}.pdf" | cut -f1)
    echo "PDF Size: $SIZE"
    
    # Count pages (if pdfinfo is available)
    if command -v pdfinfo &> /dev/null; then
        PAGES=$(pdfinfo "${MAIN_FILE}.pdf" 2>/dev/null | grep Pages | awk '{print $2}')
        if [ -n "$PAGES" ]; then
            echo "Page Count: $PAGES pages"
        fi
    fi
fi

echo ""
echo "To clean temporary files, run: ./compile.sh clean"

