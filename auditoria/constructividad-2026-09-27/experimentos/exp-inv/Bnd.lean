import FOL.HenkinLimit0

/-! Experimento de auditoría: `HenkinLimit0.bnd` es `(cst_bound_formula f).choose` (`Exists.choose`
⇒ `Classical.choice`, `noncomputable`). ¿Hay una cota COMPUTABLE con la misma especificación
(`bnd_spec`), sin elección? La cota: el mayor tamaño en bytes de los símbolos de función. -/

namespace Exp
open FOL FOL.Fresh0 FOL.Eigenvariable

theorem size_cst : ∀ m : Nat, (cst m).utf8ByteSize = m + 1
  | 0 => rfl
  | m + 1 => by
      show ("a" ++ cst m).utf8ByteSize = m + 1 + 1
      rw [String.utf8ByteSize_append, size_cst m]
      have : "a".utf8ByteSize = 1 := rfl
      rw [this, Nat.add_comm]

mutual
def symBoundT : Term → Nat
  | .var _ => 0
  | .func s ts => max s.utf8ByteSize (symBoundTs ts)
def symBoundTs : List Term → Nat
  | [] => 0
  | t :: ts => max (symBoundT t) (symBoundTs ts)
end

def symBoundF : Formula → Nat
  | .bottom => 0
  | .atom _ ts => symBoundTs ts
  | .eq t u => max (symBoundT t) (symBoundT u)
  | .impl a b => max (symBoundF a) (symBoundF b)
  | .forall a => symBoundF a
  | .and a b => max (symBoundF a) (symBoundF b)
  | .or a b => max (symBoundF a) (symBoundF b)
  | .ex a => symBoundF a

mutual
theorem occT_bound (m : Nat) : ∀ t : Term, occursTerm (cst m) t → m + 1 ≤ symBoundT t
  | .var _, h => h.elim
  | .func s ts, h => by
      cases h with
      | inl he =>
          have : s.utf8ByteSize = m + 1 := by rw [he]; exact size_cst m
          show m + 1 ≤ max s.utf8ByteSize (symBoundTs ts)
          rw [← this]; exact Nat.le_max_left _ _
      | inr ht =>
          exact Nat.le_trans (occTs_bound m ts ht) (Nat.le_max_right _ _)
theorem occTs_bound (m : Nat) : ∀ ts : List Term, occursTerms (cst m) ts → m + 1 ≤ symBoundTs ts
  | [], h => h.elim
  | t :: ts, h => by
      cases h with
      | inl ht => exact Nat.le_trans (occT_bound m t ht) (Nat.le_max_left _ _)
      | inr hts => exact Nat.le_trans (occTs_bound m ts hts) (Nat.le_max_right _ _)
end

theorem occF_bound (m : Nat) : ∀ f : Formula, occursFormula (cst m) f → m + 1 ≤ symBoundF f
  | .bottom, h => h.elim
  | .atom _ ts, h => occTs_bound m ts h
  | .eq t u, h => h.elim (fun h1 => Nat.le_trans (occT_bound m t h1) (Nat.le_max_left _ _))
                         (fun h2 => Nat.le_trans (occT_bound m u h2) (Nat.le_max_right _ _))
  | .impl a b, h => h.elim (fun h1 => Nat.le_trans (occF_bound m a h1) (Nat.le_max_left _ _))
                           (fun h2 => Nat.le_trans (occF_bound m b h2) (Nat.le_max_right _ _))
  | .forall a, h => occF_bound m a h
  | .and a b, h => h.elim (fun h1 => Nat.le_trans (occF_bound m a h1) (Nat.le_max_left _ _))
                          (fun h2 => Nat.le_trans (occF_bound m b h2) (Nat.le_max_right _ _))
  | .or a b, h => h.elim (fun h1 => Nat.le_trans (occF_bound m a h1) (Nat.le_max_left _ _))
                         (fun h2 => Nat.le_trans (occF_bound m b h2) (Nat.le_max_right _ _))
  | .ex a, h => occF_bound m a h

/-- La cota computable, con EXACTAMENTE la especificación de `HenkinLimit0.bnd_spec`. -/
def bnd (f : Formula) : Nat := symBoundF f

theorem bnd_spec (f : Formula) : ∀ m, bnd f ≤ m → Not (occursFormula (cst m) f) :=
  fun m hm hocc => Nat.not_succ_le_self m (Nat.le_trans (occF_bound m f hocc) hm)

end Exp

#print axioms Exp.bnd
#print axioms Exp.bnd_spec
#print axioms FOL.HenkinLimit0.bnd
#print axioms FOL.HenkinLimit0.bnd_spec
