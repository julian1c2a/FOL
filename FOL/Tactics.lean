import FOL.FOL
import Lean
open Lean Meta Elab Tactic

partial def getAllPositions (f : Formula) : List Pos :=
  match f with
  | .impl f1 f2 => .root :: (getAllPositions f1).map .left ++ (getAllPositions f2).map .right
  | .forall f1 => .root :: (getAllPositions f1).map .body
  | _ => [.root]

-- A tactic to close the goal `Γ ⊢ f` if `f ∈ Γ`.
partial def tryMem (g : MVarId) : MetaM Unit := do
  try
    let _ ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.head)
    pure ()
  catch _ =>
    let newGoals ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.tail)
    if h : newGoals.length = 1 then
      tryMem newGoals[0]
    else
      throwError "prove_mem failed"

elab "derive_hyp" : tactic => do
  evalTactic (← `(tactic| apply Derives.hyp))
  let goal ← getMainGoal
  tryMem goal
  setGoals []

-- Tactic to automate rewrite_at
-- It tries to close the goal `Γ ⊢ f'` by finding `f ∈ Γ`, a position `p`, and a `LocalRule`
-- such that `f` rewrites to `f'`.

elab "derive_rewrite" : tactic => do
  -- Not implemented yet, just a placeholder
  pure ()
