import FOL
import TheoryFramework
import TheoryFramework.Instances.FOL
import FOL.Core
open Lean

/-! Auditoría de constructividad de FOL: para CADA constante de los módulos `FOL*` y
`TheoryFramework*`, sus axiomas (vía `collectAxioms`, precomputados por módulo en v4.31),
si es `noncomputable`, y —si arrastra `Classical.choice`— las constantes que usa DIRECTAMENTE
y que también lo arrastran (de FOL o de fuera). Salida: dos TSV en `actual/`; `analyze.py` los resume.
El estado del 2026-09-27 está en `antes/` (antes de D1) y `despues/`. -/

def isFOLMod (m : Name) : Bool :=
  let s := m.toString
  s == "FOL" || s.startsWith "FOL." || s == "TheoryFramework" || s.startsWith "TheoryFramework."

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_local

#eval show CoreM Unit from do
  let env ← getEnv
  -- Se lanza desde la raíz de ROBINSON_PlusPlus: `lake env lean ../FOL/auditoria/constructividad-2026-09-27/Audit.lean`
  let out := "../FOL/auditoria/constructividad-2026-09-27/actual/"
  IO.FS.createDirAll out
  let mut decls : Array String := #["modulo\tnombre\tclase\tnoncomputable\taxiomas"]
  let mut edges : Array String := #["modulo\tnombre\tusa\tmodulo_usa\tes_fol"]
  let mut n := 0
  for (c, ci) in env.constants.toList do
    let m := modOf env c
    unless isFOLMod m do continue
    n := n + 1
    let axs ← collectAxioms c
    let nc := isNoncomputable env c
    decls := decls.push s!"{m}\t{c}\t{kindOf ci}\t{nc}\t{",".intercalate (axs.toList.map toString)}"
    if axs.contains ``Classical.choice then
      let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
      let mut seen : NameSet := {}
      for d in used do
        if seen.contains d then continue
        seen := seen.insert d
        let daxs ← collectAxioms d
        if daxs.contains ``Classical.choice then
          let md := modOf env d
          edges := edges.push s!"{m}\t{c}\t{d}\t{md}\t{isFOLMod md}"
  IO.FS.writeFile (out ++ "decls.tsv") ("\n".intercalate decls.toList ++ "\n")
  IO.FS.writeFile (out ++ "choice_edges.tsv") ("\n".intercalate edges.toList ++ "\n")
  IO.println s!"constantes FOL: {n}; aristas con choice: {edges.size - 1}"
