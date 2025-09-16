param(
    [switch]$CheckLinks,
    [switch]$CheckFormat,
    [switch]$CheckContent,
    [switch]$All,
    [string]$DocPath = "docs"
)

# If -All is specified, check all items
if ($All) {
    $CheckLinks = $true
    $CheckFormat = $true
    $CheckContent = $true
}

# If no check items are specified, check all by default
if (-not ($CheckLinks -or $CheckFormat -or $CheckContent)) {
    $CheckLinks = $true
    $CheckFormat = $true
    $CheckContent = $true
}

Write-Host "OpenTelemetry Documentation Validation Tool" -ForegroundColor Green
Write-Host "===========================================" -ForegroundColor Green

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir
$docsPath = Join-Path $projectRoot $DocPath

if (-not (Test-Path $docsPath)) {
    Write-Error "Documentation directory does not exist: $docsPath"
    exit 1
}

$errors = @()
$warnings = @()

# Get all Markdown files
$markdownFiles = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse

Write-Host "Found $($markdownFiles.Count) Markdown files" -ForegroundColor Yellow

# Check document format
if ($CheckFormat) {
    Write-Host "`nChecking document format..." -ForegroundColor Cyan
    
    foreach ($file in $markdownFiles) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        
        # Check title format
        if ($content -notmatch "^#\s+") {
            $warnings += "File $($file.Name) is missing main title"
        }
        
        # Check navigation links
        if ($content -notmatch "> 📚 \*\*文档导航\*\*:") {
            $warnings += "File $($file.Name) is missing navigation links"
        }
        
        # Check code block language markers
        $codeBlocks = [regex]::Matches($content, "```(\w+)?")
        foreach ($match in $codeBlocks) {
            if ($match.Groups[1].Value -eq "") {
                $warnings += "File $($file.Name) has unmarked language code block at position $($match.Index)"
            }
        }
        
        # Check table format
        $tableLines = $content -split "`n" | Where-Object { $_ -match "^\|.*\|$" }
        if ($tableLines.Count -gt 0) {
            $hasHeader = $false
            $hasSeparator = $false
            foreach ($line in $tableLines) {
                if ($line -match "^\|.*\|$" -and $line -notmatch "^\|[\s\-:]+\|$") {
                    $hasHeader = $true
                }
                if ($line -match "^\|[\s\-:]+\|$") {
                    $hasSeparator = $true
                }
            }
            if ($hasHeader -and -not $hasSeparator) {
                $warnings += "File $($file.Name) has table but missing separator row"
            }
        }
    }
}

# Check links
if ($CheckLinks) {
    Write-Host "`nChecking document links..." -ForegroundColor Cyan
    
    foreach ($file in $markdownFiles) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        
        # Find all links
        $linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
        $links = [regex]::Matches($content, $linkPattern)
        
        foreach ($link in $links) {
            $linkText = $link.Groups[1].Value
            $linkUrl = $link.Groups[2].Value
            
            # Skip external links
            if ($linkUrl -match "^https?://") {
                continue
            }
            
            # Handle anchor links
            if ($linkUrl -match "^#") {
                $targetFile = $file.FullName
                $anchor = $linkUrl.Substring(1)
                $targetContent = Get-Content $targetFile -Raw -Encoding UTF8
                if ($targetContent -notmatch "^\s*#{1,6}\s+$anchor\b") {
                    $errors += "File $($file.Name) anchor link '$linkText' -> '$linkUrl' points to non-existent title '$anchor'"
                }
                continue
            }
            
            # Handle relative path links
            if ($linkUrl -match "^/") {
                $targetPath = Join-Path $projectRoot $linkUrl.TrimStart("/")
            } else {
                $fileDir = Split-Path $file.FullName
                $targetPath = Join-Path $fileDir $linkUrl
            }
            
            # Check if file exists
            if (-not (Test-Path $targetPath)) {
                $errors += "File $($file.Name) link '$linkText' -> '$linkUrl' points to non-existent file: $targetPath"
            }
        }
    }
}

# Check content quality
if ($CheckContent) {
    Write-Host "`nChecking document content..." -ForegroundColor Cyan
    
    foreach ($file in $markdownFiles) {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8
        
        # Check document length
        $lineCount = ($content -split "`n").Count
        if ($lineCount -lt 10) {
            $warnings += "File $($file.Name) content is too short ($lineCount lines)"
        }
        
        # Check if there are code examples
        if ($content -notmatch '```') {
            $warnings += "File $($file.Name) is missing code examples"
        }
        
        # Check if there is update date
        if ($content -notmatch "最后更新|更新时间|Last updated") {
            $warnings += "File $($file.Name) is missing update date information"
        }
    }
}

# Output results
Write-Host "`nValidation Results:" -ForegroundColor Green
Write-Host "===================" -ForegroundColor Green

if ($errors.Count -eq 0 -and $warnings.Count -eq 0) {
    Write-Host "✅ All checks passed! Document quality is good." -ForegroundColor Green
    exit 0
}

if ($errors.Count -gt 0) {
    Write-Host "`n❌ Found $($errors.Count) errors:" -ForegroundColor Red
    foreach ($errorItem in $errors) {
        Write-Host "  • $errorItem" -ForegroundColor Red
    }
}

if ($warnings.Count -gt 0) {
    Write-Host "`n⚠️  Found $($warnings.Count) warnings:" -ForegroundColor Yellow
    foreach ($warning in $warnings) {
        Write-Host "  • $warning" -ForegroundColor Yellow
    }
}

Write-Host "`nSuggestions:" -ForegroundColor Cyan
Write-Host "• Fix all errors to ensure document usability" -ForegroundColor White
Write-Host "• Handle warnings to improve document quality" -ForegroundColor White
Write-Host "• Run this script regularly to maintain document quality" -ForegroundColor White

if ($errors.Count -gt 0) {
    exit 1
} else {
    exit 0
}
