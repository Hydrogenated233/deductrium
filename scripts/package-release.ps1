[CmdletBinding()]
param(
    [string]$ReleaseDate = $env:DEDUCTRIUM_RELEASE_DATE
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$projectRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot ".."))
$productName = "Deductrium-HoTT-Optimization"

if (-not $ReleaseDate) {
    $ReleaseDate = [DateTimeOffset]::UtcNow.ToOffset([TimeSpan]::FromHours(8)).ToString("yyyy.MM.dd", [Globalization.CultureInfo]::InvariantCulture)
}
if ($ReleaseDate -notmatch "^\d{4}\.\d{2}\.\d{2}$") {
    throw "Release date must use YYYY.MM.DD format."
}
$releaseVersion = $ReleaseDate

$releaseRoot = [IO.Path]::GetFullPath((Join-Path $projectRoot "release"))
$releaseName = "$productName-$releaseVersion"
$packageDirectory = [IO.Path]::GetFullPath((Join-Path $releaseRoot $releaseName))
$archivePath = [IO.Path]::GetFullPath((Join-Path $releaseRoot "$releaseName.zip"))

function Assert-ChildPath {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Parent
    )

    $fullPath = [IO.Path]::GetFullPath($Path)
    $fullParent = [IO.Path]::GetFullPath($Parent).TrimEnd([IO.Path]::DirectorySeparatorChar, [IO.Path]::AltDirectorySeparatorChar)
    $prefix = $fullParent + [IO.Path]::DirectorySeparatorChar
    if (-not $fullPath.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing to modify a path outside the release directory: $fullPath"
    }
}

Assert-ChildPath -Path $packageDirectory -Parent $releaseRoot
Assert-ChildPath -Path $archivePath -Parent $releaseRoot

$npmCommand = Get-Command "npm.cmd" -ErrorAction SilentlyContinue
if (-not $npmCommand) {
    $npmCommand = Get-Command "npm" -ErrorAction Stop
}
$nodeCommand = Get-Command "node.exe" -ErrorAction SilentlyContinue
if (-not $nodeCommand) {
    $nodeCommand = Get-Command "node" -ErrorAction Stop
}

Push-Location $projectRoot
try {
    Write-Host "[1/7] Running regression tests..."
    & $npmCommand.Source test
    if ($LASTEXITCODE -ne 0) { throw "Regression tests failed." }

    Write-Host "[2/7] Type-checking..."
    & $npmCommand.Source run typecheck
    if ($LASTEXITCODE -ne 0) { throw "TypeScript type-check failed." }

    Write-Host "[3/7] Building..."
    & $npmCommand.Source run build
    if ($LASTEXITCODE -ne 0) { throw "TypeScript build failed." }

    Write-Host "[4/7] Preparing release directory..."
    New-Item -ItemType Directory -Path $releaseRoot -Force | Out-Null
    foreach ($target in @($packageDirectory, $archivePath)) {
        if (Test-Path -LiteralPath $target) {
            Remove-Item -LiteralPath $target -Recurse -Force
        }
    }
    New-Item -ItemType Directory -Path $packageDirectory -Force | Out-Null

    $runtimeFiles = @(
        "index.html",
        "gui.css",
        "README.md",
        "README_EN.md",
        "package.json",
        "server.mjs",
        "tt-process.mjs",
        "start.cmd",
    )
    foreach ($relativePath in $runtimeFiles) {
        $source = Join-Path $projectRoot $relativePath
        if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
            throw "Required release file is missing: $relativePath"
        }
        Copy-Item -LiteralPath $source -Destination $packageDirectory -Force
    }

    $javascriptDirectory = Join-Path $projectRoot "js"
    if (-not (Test-Path -LiteralPath $javascriptDirectory -PathType Container)) {
        throw "Build output directory is missing: js"
    }
    Copy-Item -LiteralPath $javascriptDirectory -Destination $packageDirectory -Recurse -Force

    Write-Host "[5/7] Validating release contents..."
    $requiredPaths = @($runtimeFiles + "js")
    foreach ($relativePath in $requiredPaths) {
        if (-not (Test-Path -LiteralPath (Join-Path $packageDirectory $relativePath))) {
            throw "Packaged release is missing: $relativePath"
        }
    }
    foreach ($forbiddenPath in @("src", "node_modules")) {
        if (Test-Path -LiteralPath (Join-Path $packageDirectory $forbiddenPath)) {
            throw "Packaged release unexpectedly contains: $forbiddenPath"
        }
    }

    Write-Host "[6/7] Starting packaged process smoke test..."
    & $nodeCommand.Source (Join-Path $projectRoot "tests/tt-process-package-smoke.mjs") $packageDirectory
    if ($LASTEXITCODE -ne 0) { throw "Packaged type-theory process smoke test failed." }

    Write-Host "[7/7] Compressing release..."
    Compress-Archive -Path (Join-Path $packageDirectory "*") -DestinationPath $archivePath -CompressionLevel Optimal

    Write-Host "Release ready."
    $archive = Get-Item -LiteralPath $archivePath
    $sha256 = [Security.Cryptography.SHA256]::Create()
    $archiveStream = [IO.File]::OpenRead($archivePath)
    try {
        $hash = [BitConverter]::ToString($sha256.ComputeHash($archiveStream)).Replace("-", "")
    } finally {
        $archiveStream.Dispose()
        $sha256.Dispose()
    }
    Write-Host "Directory: $packageDirectory"
    Write-Host "Archive:   $archivePath"
    Write-Host ("Size:      {0:N0} bytes" -f $archive.Length)
    Write-Host "SHA256:    $hash"
} finally {
    Pop-Location
}
