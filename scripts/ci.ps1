# Full verification pipeline: proofs -> hygiene -> Node tests -> browser tests.
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root
try {
  Write-Output '=== lake build (library + #guard vectors + axiom snapshots + CLI) ==='
  lake build
  if ($LASTEXITCODE -ne 0) { throw 'lake build failed' }

  Write-Output '=== sorry/native_decide hygiene ==='
  & (Join-Path $PSScriptRoot 'check-no-sorry.ps1')
  if ($LASTEXITCODE -ne 0) { throw 'hygiene check failed' }

  Write-Output '=== node --test (round trips, zlib reference, tar.exe interop, Lean differential) ==='
  node --test "test/*.test.mjs"
  if ($LASTEXITCODE -ne 0) { throw 'node tests failed' }

  Write-Output '=== playwright (vanilla ES6 core in Chromium) ==='
  npx playwright test
  if ($LASTEXITCODE -ne 0) { throw 'playwright tests failed' }

  Write-Output 'CI: all green'
} finally {
  Pop-Location
}
