import PropLogic.PL
import Lean
open Lean Meta Elab Tactic

open PropLogic

partial def PL.getAllPositions (f : Formula) : List Pos :=
  match f with
  | .impl f1 f2 => .root :: (PL.getAllPositions f1).map .left ++ (PL.getAllPositions f2).map .right
  | .and  f1 f2 => .root :: (PL.getAllPositions f1).map .left ++ (PL.getAllPositions f2).map .right
  | .or   f1 f2 => .root :: (PL.getAllPositions f1).map .left ++ (PL.getAllPositions f2).map .right
  | _ => [.root]

partial def PL.tryMem (g : MVarId) : MetaM Unit := do
  try
    let _ ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.head)
    pure ()
  catch _ =>
    let newGoals ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.tail)
    if h : newGoals.length = 1 then
      PL.tryMem newGoals[0]
    else
      throwError "prove_mem failed"

elab "derive_hyp" : tactic => do
  evalTactic (← `(tactic| apply PropLogic.Derives.hyp))
  let goal ← getMainGoal
  PL.tryMem goal
  setGoals []

syntax "derive_rewrite " term " at " term : tactic

macro_rules
  | `(tactic| derive_rewrite $rule at $pos) => `(tactic| apply PropLogic.Derives.rewrite_at $pos <;> exact $rule)

syntax "derive_weaken " term : tactic

macro_rules
  | `(tactic| derive_weaken $thm) => `(tactic| apply PropLogic.Derives.weakening $thm; repeat (apply List.subset_cons <|> exact List.Subset.refl _))
