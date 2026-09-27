$A = "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-juez/check"
$files = Get-ChildItem -Path $A -Recurse -Filter *.lean | ForEach-Object { $_.FullName }
$files | ForEach-Object -ThrottleLimit 4 -Parallel {
  Set-Location E:/dropbox/github/lean4/ROBINSON_PlusPlus
  $f = $_
  $o = lake env lean "$f" 2>&1 | Out-String -Width 300
  $code = $LASTEXITCODE
  $errs = ($o -split "`n" | Where-Object { $_ -match "error" } | Select-Object -First 3) -join " || "
  "EXIT=$code $f :: $errs"
}
