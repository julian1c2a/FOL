param([string]$f)
Set-Location E:/dropbox/github/lean4/ROBINSON_PlusPlus
lake env lean $f 2>&1
