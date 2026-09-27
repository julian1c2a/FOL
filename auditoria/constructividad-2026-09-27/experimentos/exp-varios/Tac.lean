import FOL.Theorems.Impl
open Lean
/-! (2) El choice de FOL.Tactics viene del marco meta de Lean, no de FOL. -/
#print axioms tryMem
#print axioms Lean.Meta.MetaM
#print axioms Lean.Meta.Context
#print axioms Lean.Meta.State
#print axioms Lean.Core.CoreM
#print axioms Lean.Elab.Tactic.TacticM
#print axioms Lean.Elab.Tactic.Tactic
-- un teorema cuya prueba USA la táctica `derive_hyp`
#print axioms FOL.Theorems.Impl.id_impl
#eval show MetaM Unit from do
  let env ← getEnv
  for n in [`tryMem, `_aux_FOL_Tactics___elabRules_tacticDerive_hyp_1, `getAllPositions] do
    match env.find? n with
    | some ci => IO.println s!"{n} : {← Meta.ppExpr ci.type}  (opaque={match ci with | .opaqueInfo _ => true | _ => false})"
    | none => IO.println s!"{n}: no encontrado"
