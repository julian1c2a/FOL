/-! s2 · Las afirmaciones laterales de a2 y a3 sobre dónde entra `propext` (o `choice`). -/

namespace S2Trampas

-- (a) `match` con patrones SOLAPADOS frente a DISJUNTOS
def relSolap {D : Type} (R : D → Prop) : List D → Prop
  | [d] => R d
  | _ => False

def relDisj {D : Type} (R : D → Prop) : List D → Prop
  | [] => False
  | [d] => R d
  | _ :: _ :: _ => False

theorem usaSolap {D : Type} (R : D → Prop) (d : D) (h : R d) : relSolap R [d] := h
theorem usaDisj {D : Type} (R : D → Prop) (d : D) (h : R d) : relDisj R [d] := h

end S2Trampas

#print axioms S2Trampas.relSolap
#print axioms S2Trampas.relDisj
#print axioms S2Trampas.usaSolap
#print axioms S2Trampas.usaDisj
-- (b) lemas del núcleo
#print axioms List.length_replicate
#print axioms Nat.mod_eq_of_lt
#print axioms List.Nodup.length_le_of_subset
