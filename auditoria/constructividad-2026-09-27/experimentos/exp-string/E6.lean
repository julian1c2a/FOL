import Lean
import FOL.Enumeration
open Lean

/-! Camino de choice: desde una constante, sigue en profundidad la primera dependencia directa
que lleva Classical.choice hasta llegar a una que lo usa DIRECTAMENTE (o a un axioma). -/

partial def pathToChoice (c : Name) (fuel : Nat) : CoreM (List Name) := do
  if fuel = 0 then return [c]
  let env ← getEnv
  let some ci := env.find? c | return [c]
  let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  if used.contains ``Classical.choice then return [c, ``Classical.choice]
  -- preferir una dependencia NO auxiliar si la hay
  let mut cands : Array Name := #[]
  for d in used do
    if d == c then continue
    let axs ← collectAxioms d
    if axs.contains ``Classical.choice then cands := cands.push d
  match cands[0]? with
  | none => return [c]
  | some d => return c :: (← pathToChoice d (fuel - 1))

def show1 (c : Name) : CoreM Unit := do
  let p ← pathToChoice c 60
  IO.println s!"{c}:\n   {" -> ".intercalate (p.map toString)}"

#eval show CoreM Unit from do
  show1 ``String.toList
  show1 ``ByteArray.utf8DecodeChar?
  show1 ``String.length
  show1 ``String.instOrd
  show1 ``String.instLawfulEqOrd
  show1 ``String.instTransOrd
  show1 ``String.le_antisymm
  show1 ``String.ofList_injective
