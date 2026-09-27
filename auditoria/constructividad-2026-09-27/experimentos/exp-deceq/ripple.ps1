Set-Location E:/dropbox/github/lean4/ROBINSON_PlusPlus
$d = "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-deceq/ripple"
foreach ($m in @('Henkin0','Fresh0','HenkinLimit0','Lindenbaum0','Canonical0','Compacity0','Skolem0','SkolemN0')) {
  foreach ($v in @('orig','dec')) {
    $f = "$d/${m}_$v.lean"
    $o = "$d/${m}_$v.out"
    lake env lean $f 2>&1 | Out-String -Width 400 | Set-Content -Encoding utf8 $o
    Write-Output "$m $v exit=$LASTEXITCODE"
  }
}
