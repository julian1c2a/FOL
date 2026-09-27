import Lean
import FOL.Enumeration
open Lean

/-! Censo en v4.31: todas las constantes del NUCLEO (modulos Init.*) de los espacios
`String`, `ByteArray`, `Char`, `List.utf8*` — cuantas llevan Classical.choice — y, para las que
lo llevan, de que constante FUERA de esos espacios lo heredan directamente (la raiz). -/

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_local

def inScope (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "String." || s.startsWith "ByteArray." || s.startsWith "Char." ||
  s.startsWith "List.utf8" || s.startsWith "instDecidableEqString" || s.startsWith "instLawfulBEqString"

#eval show CoreM Unit from do
  let env ← getEnv
  let out := "C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-string/"
  let mut rows : Array String := #["modulo\tnombre\tchoice"]
  let mut roots : Array String := #["nombre\traiz_externa"]
  let mut nTot := 0
  let mut nCh := 0
  for (c, ci) in env.constants.toList do
    let m := modOf env c
    unless m.toString.startsWith "Init" do continue
    unless inScope c do continue
    if c.isInternal then continue
    nTot := nTot + 1
    let axs ← collectAxioms c
    let ch := axs.contains ``Classical.choice
    if ch then nCh := nCh + 1
    rows := rows.push s!"{m}\t{c}\t{ch}"
    if ch then
      let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
      let mut seen : NameSet := {}
      for d in used do
        if seen.contains d then continue
        seen := seen.insert d
        if inScope d then continue
        let daxs ← collectAxioms d
        if daxs.contains ``Classical.choice then
          roots := roots.push s!"{c}\t{d}"
  IO.FS.writeFile (out ++ "core_string.tsv") ("\n".intercalate rows.toList ++ "\n")
  IO.FS.writeFile (out ++ "core_string_roots.tsv") ("\n".intercalate roots.toList ++ "\n")
  IO.println s!"constantes nucleo en alcance (no internas): {nTot}; con choice: {nCh}"
