$A = "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit"
$files = @(
 "exp-deceq/E0.lean","exp-deceq/E1.lean","exp-deceq/E2.lean","exp-deceq/E3.lean","exp-deceq/E3b.lean","exp-deceq/E3c.lean","exp-deceq/E4.lean","exp-deceq/E5.lean","exp-deceq/E6.lean",
 "exp-bnd-invOf/Exp.lean","exp-bnd-invOf/ExpFresh.lean","exp-bnd-invOf/ExpAll.lean","exp-bnd-invOf/ProbeUnshift.lean",
 "exp-string/E1.lean","exp-string/E3.lean","exp-string/E4.lean","exp-string/E7.lean","exp-string/E8.lean","exp-string/E9.lean",
 "exp-varios/Eq0orig.lean","exp-varios/Eq4min.lean","exp-varios/EmA.lean","exp-varios/EmB.lean","exp-varios/Disj.lean","exp-varios/Tac.lean",
 "exp-esencial/E1_Solidez.lean","exp-esencial/E2_SolidezEstable.lean","exp-esencial/E2b_LKcDecidible.lean","exp-esencial/E3_MaxCons.lean","exp-esencial/E4_Lindenbaum.lean","exp-esencial/E4b_String.lean","exp-esencial/E5_Cociente.lean","exp-esencial/E6_Skolem.lean","exp-esencial/E6b_Henkin.lean","exp-esencial/E7_ModelExistence.lean","exp-esencial/E8_HenkinSintactico.lean",
 "exp-inv/Accidental.lean","exp-inv/Bnd.lean","exp-inv/Enum.lean","exp-inv/Fresh.lean","exp-inv/TFInst.lean","exp-inv/StringCmp.lean"
)
$files | ForEach-Object -ThrottleLimit 4 -Parallel {
  $A = $using:A
  Set-Location E:/dropbox/github/lean4/ROBINSON_PlusPlus
  $f = $_
  $name = ($f -replace '/', '__') -replace '\.lean$',''
  $sw = [Diagnostics.Stopwatch]::StartNew()
  $o = lake env lean "$A/$f" 2>&1 | Out-String -Width 400
  $code = $LASTEXITCODE
  $sw.Stop()
  Set-Content -Path "$A/exp-juez/out/$name.out" -Value ("EXIT=$code SECS=" + [int]$sw.Elapsed.TotalSeconds + "`n" + $o) -Encoding utf8
}
"DONE" | Set-Content "$A/exp-juez/out/_DONE.txt"
