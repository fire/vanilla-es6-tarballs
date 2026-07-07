# SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
# SPDX-License-Identifier: MIT

# Fails if any Lean source contains sorry/admit, or native_decide inside TarGz/.
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
$leanSources = @(Get-ChildItem -Path $root -Filter *.lean -File) +
               @(Get-ChildItem -Path (Join-Path $root 'TarGz'), (Join-Path $root 'Tests') -Filter *.lean -File -Recurse)
$bad = $leanSources | Select-String -Pattern '\b(sorry|admit)\b'
if ($bad) { $bad | ForEach-Object { Write-Output $_.ToString() }; Write-Output 'FAIL: sorry/admit found'; exit 1 }
$nd = @(Get-ChildItem -Path (Join-Path $root 'TarGz') -Filter *.lean -File -Recurse) + @(Get-Item (Join-Path $root 'TarGz.lean')) |
      Select-String -Pattern 'native_decide'
if ($nd) { $nd | ForEach-Object { Write-Output $_.ToString() }; Write-Output 'FAIL: native_decide in TarGz/'; exit 1 }
Write-Output 'OK: no sorry/admit anywhere; no native_decide in TarGz/'
exit 0
