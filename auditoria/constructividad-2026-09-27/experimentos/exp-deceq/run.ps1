param([string[]]$files)
Set-Location E:/dropbox/github/lean4/ROBINSON_PlusPlus
foreach ($f in $files) {
  $p = "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-deceq/$f"
  Write-Output "===== $f ====="
  lake env lean $p 2>&1 | Out-String -Width 400
}
