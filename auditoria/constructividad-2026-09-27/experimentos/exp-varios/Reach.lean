import ROBINSON_PlusPlus
import FOL
import TheoryFramework
open Lean

/-! Alcance en el entorno COMPLETO (RPP + FOL + TheoryFramework):
  (a) titulares de check-footprints (RPP) que alcanzan el trío `subst_comm_succ`, y si
      perderían `Classical.choice` si el trío quedara limpio;
  (b) constantes (fuera de FOL.Tactics) que usan DIRECTAMENTE una constante de FOL.Tactics;
  (c) constantes que dependen de los 4 axiomas de FOL.MetaRules, por módulo;
  (d) usuarios (directos o transitivos) de derives0_em / derives0_peirce. -/

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_local

def usedOf (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let base := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    match ci with
    | .inductInfo iv => base ++ iv.ctors.toArray
    | _ => base

/-- Conjunto de constantes alcanzables desde `roots` (incluidas). -/
def reachable (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    for d in usedOf env c do
      unless seen.contains d do stack := stack.push d
  return seen

/-- Dentro de `R`, las constantes desde las que se alcanza algún `target`, sin atravesar `cut`. -/
def reachesAny (env : Environment) (R : NameSet) (targets : NameSet) (cut : NameSet) : NameSet := Id.run do
  -- grafo inverso restringido a R
  let mut rev : Std.HashMap Name (Array Name) := {}
  for c in R.toList do
    for d in usedOf env c do
      rev := rev.insert d ((rev.getD d #[]).push c)
  let mut bad : NameSet := {}
  let mut stack : Array Name := targets.toList.toArray
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if bad.contains c then continue
    if cut.contains c then continue
    bad := bad.insert c
    for u in rev.getD c #[] do
      unless bad.contains u do stack := stack.push u
  return bad

def isFOLMod (m : Name) : Bool :=
  let s := m.toString
  s == "FOL" || s.startsWith "FOL." || s == "TheoryFramework" || s.startsWith "TheoryFramework."

#eval show CoreM Unit from do
  let env ← getEnv
  let dir := "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-varios/"
  let tabla ← IO.FS.lines (dir ++ "tabla_rpp.txt")
  let mut tit : Array (Name × String) := #[]
  for l in tabla do
    let parts := l.splitOn "|"
    if parts.length < 2 then continue
    let n := parts[0]!.trim.toName
    if env.contains n then tit := tit.push (n, parts[1]!)
    else IO.println s!"NO ENCONTRADO: {parts[0]!}"
  IO.println s!"titulares resueltos: {tit.size}"
  -- (a)
  let trio : NameSet := ({} : NameSet) |>.insert `FOL.substTerm_subst_comm_succ._f
      |>.insert `FOL.substTerm_subst_comm_succ |>.insert `FOL.substTerms_subst_comm_succ
      |>.insert `FOL.subst_subst_comm_succ
  let allNames : Array Name := env.constants.toList.toArray.map (·.1)
  let proj : Array Name := allNames.filter (fun c => let m := modOf env c; isFOLMod m || m.toString.startsWith "ROBINSON_PlusPlus")
  IO.println s!"constantes de proyecto (FOL+TF+RPP): {proj.size}"
  let R := reachable env (tit.map (·.1))
  IO.println s!"constantes alcanzables desde los titulares: {R.size}"
  let choiceT : NameSet := ({} : NameSet).insert ``Classical.choice
  let withChoice := reachesAny env R choiceT {}
  let withChoiceSinTrio := reachesAny env R choiceT trio
  let alcanzaTrio := reachesAny env R trio {}
  let mut nChoice := 0
  for (n, _) in tit do
    if withChoice.contains n then nChoice := nChoice + 1
    if alcanzaTrio.contains n then
      IO.println s!"(a) alcanza trio: {n}  choice_hoy={withChoice.contains n}  choice_si_trio_limpio={withChoiceSinTrio.contains n}"
  IO.println s!"(a) titulares con choice (medido aqui): {nChoice}"
  -- usuarios directos del trío en todo el entorno
  for c in proj do
    if trio.contains c then continue
    for d in usedOf env c do
      if trio.contains d then IO.println s!"(a) usuario directo del trio: {c} [{modOf env c}] usa {d}"
  -- (b)
  let tacMod : Name := `FOL.Tactics
  for c in proj do
    if modOf env c == tacMod then continue
    for d in usedOf env c do
      if modOf env d == tacMod then IO.println s!"(b) {c} [{modOf env c}] usa {d}"
  IO.println "(b) fin"
  -- (c)
  let mr : NameSet := ({} : NameSet) |>.insert `FOL.MetaRules.imp_intro |>.insert `FOL.MetaRules.raa
      |>.insert `FOL.MetaRules.or_elim |>.insert `FOL.MetaRules.ex_elim
  let Rall : NameSet := proj.foldl (fun s c => s.insert c) {}
  let dependMR := reachesAny env Rall mr {}
  let mut porMod : Std.HashMap Name Nat := {}
  for c in dependMR.toList do
    let m := modOf env c
    porMod := porMod.insert m (porMod.getD m 0 + 1)
    if isFOLMod m then IO.println s!"(c) FOL depende de MetaRules: {c} [{m}]"
  IO.println s!"(c) total constantes que dependen de MetaRules (incl. los 4 axiomas): {dependMR.size}"
  let mut rppTot := 0
  for (m, k) in porMod.toList do
    unless isFOLMod m do rppTot := rppTot + k
  IO.println s!"(c) de ellas fuera de FOL/TheoryFramework: {rppTot} en {porMod.size} modulos (con FOL incluidos)"
  -- (d)
  let emp : NameSet := ({} : NameSet) |>.insert `FOL.Canonical0.derives0_em |>.insert `FOL.Canonical0.derives0_peirce
  let usaEm := reachesAny env Rall emp {}
  for c in usaEm.toList do
    unless emp.contains c do IO.println s!"(d) depende de derives0_em/peirce: {c} [{modOf env c}]"
  IO.println "(d) fin"
