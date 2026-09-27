import FOL.HenkinLimit0

/-!
# Anexo (entrada de `Fresh0`, NO de este experimento): `cst_ne_shift` y `cst_zero_ne` sin choice

Se mide sólo para saber si, quitadas `bnd` e `invOf`, la frescura de la cadena
(`hen_fresh_at`) queda limpia o sigue arrastrando choice por `String`.
-/

namespace ExpF

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0

theorem cst_size : ∀ n : Nat, (cst n).utf8ByteSize = n + 1
  | 0 => rfl
  | n + 1 => by
      show ("a" ++ cst n).utf8ByteSize = n + 1 + 1
      rw [String.utf8ByteSize_append, cst_size n]
      show 1 + (n + 1) = n + 1 + 1
      rw [Nat.add_comm]

/-- `cst_zero_ne` contando bytes (sin `String.instOrd`). -/
theorem cst_zero_ne' (n : Nat) : cst 0 ≠ cst (n + 1) := fun h =>
  absurd ((cst_size 0).symm.trans ((congrArg String.utf8ByteSize h).trans (cst_size (n + 1))))
    (fun h' => Nat.succ_ne_zero n (Nat.succ.inj h').symm)

/-- Dos cadenas de 1 byte distintas no pueden empezar igual. -/
theorem ne_of_head {a b x y : String} (ha : a.toByteArray.size = b.toByteArray.size)
    (hab : a ≠ b) : a ++ x ≠ b ++ y := fun h => by
  have hb : a.toByteArray ++ x.toByteArray = b.toByteArray ++ y.toByteArray := by
    rw [← String.toByteArray_append, ← String.toByteArray_append, h]
  exact hab (String.toByteArray_inj.mp (ByteArray.append_inj_left hb ha))

theorem g_eq : "g" = "g" ++ "" := by decide

/-- ⭐ `cst_ne_shift` sin `not_eq_of_beq_eq_false` (sin `String.instOrd`). -/
theorem cst_ne_shift' : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, s => by
      show "g" ≠ "f" ++ s
      rw [g_eq]
      exact ne_of_head rfl (by decide)
  | n + 1, s => by
      show "a" ++ cst n ≠ "f" ++ s
      exact ne_of_head rfl (by decide)

mutual
theorem not_occurs_shiftTerm' (n : Nat) : ∀ t : Term,
    Not (occursTerm (cst n) (renameTerm shift t))
  | .var _ => fun h => h
  | .func s ts => fun h => by
      cases h with
      | inl he => exact cst_ne_shift' n s he.symm
      | inr ht => exact not_occurs_shiftTerms' n ts ht

theorem not_occurs_shiftTerms' (n : Nat) : ∀ ts : List Term,
    Not (occursTerms (cst n) (renameTerms shift ts))
  | [] => fun h => h
  | t :: ts => fun h => by
      cases h with
      | inl ht => exact not_occurs_shiftTerm' n t ht
      | inr hts => exact not_occurs_shiftTerms' n ts hts
end

theorem not_occurs_shiftFormula' (n : Nat) : ∀ f : Formula,
    Not (occursFormula (cst n) (renameFormula shift f)) := by
  intro f
  induction f with
  | bottom => exact fun h => h
  | atom _ ts => exact not_occurs_shiftTerms' n ts
  | eq t u => exact fun h => h.elim (not_occurs_shiftTerm' n t) (not_occurs_shiftTerm' n u)
  | impl _ _ iha ihb => exact fun h => h.elim iha ihb
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun h => h.elim iha ihb
  | or _ _ iha ihb => exact fun h => h.elim iha ihb
  | ex _ ih => exact ih

theorem shiftTheory_fresh' {S : Formula → Prop} (n : Nat) :
    ∀ g, shiftTheory S g → Not (occursFormula (cst n) g) := by
  intro g hg hocc
  obtain ⟨h, _, he⟩ := hg
  exact not_occurs_shiftFormula' n h (he ▸ hocc)

end ExpF

#print axioms ExpF.cst_zero_ne'
#print axioms ExpF.ne_of_head
#print axioms ExpF.g_eq
#print axioms ExpF.cst_ne_shift'
#print axioms ExpF.shiftTheory_fresh'
