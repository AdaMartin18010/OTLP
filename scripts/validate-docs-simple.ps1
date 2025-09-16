# Simple document validation script
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Write-Host "OpenTelemetry Document Validation Tool" -ForegroundColor Green
Write-Host "=====================================" -ForegroundColor Green

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir
$docsPath = Join-Path $projectRoot "docs"

if (-not (Test-Path $docsPath)) {
    Write-Error "Document directory not found: $docsPath"
    exit 1
}

$errors = @()
$warnings = @()

# Get all Markdown files
$markdownFiles = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse

Write-Host "Found $($markdownFiles.Count) Markdown files" -ForegroundColor Yellow

# Check document format
Write-Host "`nChecking document format..." -ForegroundColor Cyan

foreach ($file in $markdownFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    
    # Check for main title
    if ($content -notmatch "^#\s+") {
        $warnings += "File $($file.Name) missing main title"
    }
    
    # Check for navigation links
    if ($content -notmatch "> 📚 \*\*文档导航\*\*:") {
        $warnings += "File $($file.Name) missing navigation links"
    }
    
    # Check for code blocks without language
    $codeBlocks = [regex]::Matches($content, "```(\w+)?")
    foreach ($match in $codeBlocks) {
        if ($match.Groups[1].Value -eq "") {
            $warnings += "File $($file.Name) has code block without language at position $($match.Index)"
        }
    }
}

# Check links
Write-Host "`nChecking document links..." -ForegroundColor Cyan

foreach ($file in $markdownFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    
    # Find all links
    $linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
    $links = [regex]::Matches($content, $linkPattern)
    
    foreach ($link in $links) {
        $linkUrl = $link.Groups[2].Value
        
        # Skip external links
        if ($linkUrl -match "^https?://") {
            continue
        }
        
        # Handle relative path links
        $targetPath = if ($linkUrl -match "^/") {
            Join-Path $projectRoot $linkUrl.TrimStart("/")
        } else {
            $fileDir = Split-Path $file.FullName
            Join-Path $fileDir $linkUrl
        }
        
        # Check if file exists
        if (-not (Test-Path $targetPath)) {
            $errors += "File $($file.Name) has broken link '$linkUrl' pointing to non-existent file: $targetPath"
        }
    }
}

# Check content quality
Write-Host "`nChecking document content..." -ForegroundColor Cyan

foreach ($file in $markdownFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    
    # Check document length
    $lineCount = ($content -split "`n").Count
    if ($lineCount -lt 10) {
        $warnings += "File $($file.Name) content too short ($lineCount lines)"
    }
    
    # Check for code examples
    if ($content -notmatch "```") {
        $warnings += "File $($file.Name) missing code examples"
    }
}

# Output results
Write-Host "`nValidation Results:" -ForegroundColor Green
Write-Host "==================" -ForegroundColor Green

if ($errors.Count -eq 0 -and $warnings.Count -eq 0) {
    Write-Host "✅ All checks passed! Document quality is good." -ForegroundColor Green
    exit 0
}

if ($errors.Count -gt 0) {
    Write-Host "`n❌ Found $($errors.Count) errors:" -ForegroundColor Red
    foreach ($error in $errors) {
        Write-Host "  • $error" -ForegroundColor Red
    }
}

if ($warnings.Count -gt 0) {
    Write-Host "`n⚠️  Found $($warnings.Count) warnings:" -ForegroundColor Yellow
    foreach ($warning in $warnings) {
        Write-Host "  • $warning" -ForegroundColor Yellow
    }
}

Write-Host "`nRecommendations:" -ForegroundColor Cyan
Write-Host "• Fix all errors to ensure document usability" -ForegroundColor White
Write-Host "• Address warnings to improve document quality" -ForegroundColor White
Write-Host "• Run this script regularly to maintain document quality" -ForegroundColor White

exit ($errors.Count -gt 0 ? 1 : 0)
