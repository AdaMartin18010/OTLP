# ICSE 2026 Paper Compilation Script (PowerShell)
# Usage: .\compile.ps1 [-clean]

param(
    [switch]$clean = $false
)

$MainFile = "ICSE2026_Paper_Main"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "ICSE 2026 Paper Compilation Script" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# Check if pdflatex is available
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    Write-Host "ERROR: pdflatex not found!" -ForegroundColor Red
    Write-Host ""
    Write-Host "Please install LaTeX first:" -ForegroundColor Yellow
    Write-Host "  - TeX Live: https://tug.org/texlive/" -ForegroundColor Yellow
    Write-Host "  - MiKTeX: https://miktex.org/" -ForegroundColor Yellow
    Write-Host ""
    exit 1
}

# Clean mode
if ($clean) {
    Write-Host "Cleaning temporary files..." -ForegroundColor Yellow
    
    $extensions = @("*.aux", "*.bbl", "*.blg", "*.log", "*.out", "*.toc", 
                    "*.lof", "*.lot", "*.fls", "*.fdb_latexmk", "*.synctex.gz",
                    "*.nav", "*.snm", "*.vrb", "*.bcf", "*.run.xml")
    
    foreach ($ext in $extensions) {
        Remove-Item $ext -ErrorAction SilentlyContinue
    }
    
    Write-Host "Cleanup complete!" -ForegroundColor Green
    exit 0
}

# Compilation
Write-Host "Step 1/4: First pdflatex pass..." -ForegroundColor Yellow
$result1 = pdflatex -interaction=nonstopmode "$MainFile.tex" 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: First pdflatex pass failed!" -ForegroundColor Red
    Write-Host "Check $MainFile.log for details" -ForegroundColor Red
    exit 1
}
Write-Host "  ✓ Complete" -ForegroundColor Green

Write-Host "Step 2/4: Running bibtex..." -ForegroundColor Yellow
$result2 = bibtex "$MainFile" 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "WARNING: bibtex had issues (this may be OK)" -ForegroundColor Yellow
}
Write-Host "  ✓ Complete" -ForegroundColor Green

Write-Host "Step 3/4: Second pdflatex pass..." -ForegroundColor Yellow
$result3 = pdflatex -interaction=nonstopmode "$MainFile.tex" 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: Second pdflatex pass failed!" -ForegroundColor Red
    exit 1
}
Write-Host "  ✓ Complete" -ForegroundColor Green

Write-Host "Step 4/4: Third pdflatex pass (resolving references)..." -ForegroundColor Yellow
$result4 = pdflatex -interaction=nonstopmode "$MainFile.tex" 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: Third pdflatex pass failed!" -ForegroundColor Red
    exit 1
}
Write-Host "  ✓ Complete" -ForegroundColor Green

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Compilation Successful! 🎉" -ForegroundColor Green
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "Output: $MainFile.pdf" -ForegroundColor Green
Write-Host ""

# Check PDF size
if (Test-Path "$MainFile.pdf") {
    $fileSize = (Get-Item "$MainFile.pdf").Length / 1MB
    Write-Host "PDF Size: $([math]::Round($fileSize, 2)) MB" -ForegroundColor Cyan
}

# Count pages (requires pdfinfo or similar tool)
Write-Host ""
Write-Host "To clean temporary files, run: .\compile.ps1 -clean" -ForegroundColor Yellow

