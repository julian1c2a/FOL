import ROBINSON_PlusPlus.Meta.Hilbert
open Lean

def usedOf (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let base := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    match ci with
    | .inductInfo iv => base ++ iv.ctors.toArray
    | _ => base

/-- ¿alcanza `Classical.choice` desde `c` sin atravesar `cut`? devuelve un camino testigo. -/
partial def path (env : Environment) (cut : NameSet) (c : Name) (seen : IO.Ref NameSet) : IO (Option (List Name)) := do
  if c == ``Classical.choice then return some [c]
  if cut.contains c then return none
  if (← seen.get).contains c then return none
  seen.modify (·.insert c)
  for d in usedOf env c do
    if let some p ← path env cut d seen then return some (c :: p)
  return none

#eval show CoreM Unit from do
  let env ← getEnv
  let trio : NameSet := ({} : NameSet) |>.insert `FOL.substTerm_subst_comm_succ._f
      |>.insert `FOL.substTerm_subst_comm_succ |>.insert `FOL.substTerms_subst_comm_succ
      |>.insert `FOL.subst_subst_comm_succ
  let c := `ROBINSON_PlusPlus.Meta.Hilbert.list_induction_derives
  IO.println s!"axiomas hoy: {(← collectAxioms c).toList}"
  let r ← IO.mkRef ({} : NameSet)
  match ← path env trio c r with
  | some p => IO.println s!"con trio limpio SIGUE con choice, camino: {p}"
  | none => IO.println "con trio limpio, list_induction_derives quedaria SIN choice"
