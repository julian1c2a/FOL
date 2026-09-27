import FOL.Fresh0

/-! Experimento de auditoría: el `Classical.choice` de `FOL.Fresh0` por `String`, ¿es evitable?
(1) `cst_zero_ne`/`cst_ne_shift`: la síntesis de `ReflBEq String` para `not_eq_of_beq_eq_false`
elige una ruta por `Ord` (`String.instOrd`/`instLawfulEqOrd`/`instTransOrd`, con choice); se le
pasa la de `instLawfulBEqString` (sin axiomas). (2) `cst_bound_sym` sin tercio excluso: cota por
tamaño en bytes. -/

#print axioms String.utf8ByteSize_append

namespace Exp
open FOL.Fresh0

abbrev rb : ReflBEq String := @LawfulBEq.toReflBEq String _ instLawfulBEqString

theorem cst_zero_ne (n : Nat) : cst 0 ≠ cst (n + 1) :=
  @not_eq_of_beq_eq_false String _ rb _ _ rfl

theorem cst_ne_shift : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, _ => @not_eq_of_beq_eq_false String _ rb _ _ rfl
  | _ + 1, _ => @not_eq_of_beq_eq_false String _ rb _ _ rfl

theorem cst_inj : ∀ m n : Nat, cst m = cst n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (cst_zero_ne _)
  | _ + 1, 0, h => absurd h.symm (cst_zero_ne _)
  | m + 1, n + 1, h => congrArg (· + 1) (cst_inj m n ((String.append_right_inj "a").mp h))

theorem size_cst : ∀ m : Nat, (cst m).utf8ByteSize = m + 1
  | 0 => rfl
  | m + 1 => by
      show ("a" ++ cst m).utf8ByteSize = m + 1 + 1
      rw [String.utf8ByteSize_append, size_cst m]
      have : "a".utf8ByteSize = 1 := rfl
      rw [this, Nat.add_comm]

theorem cst_bound_sym (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.utf8ByteSize, fun m hm he => by
    have h := congrArg String.utf8ByteSize he
    rw [size_cst m] at h
    rw [← h] at hm
    exact absurd hm (Nat.not_succ_le_self m)⟩

end Exp

#print axioms Exp.cst_zero_ne
#print axioms Exp.cst_ne_shift
#print axioms Exp.cst_inj
#print axioms Exp.size_cst
#print axioms Exp.cst_bound_sym
#print axioms FOL.Fresh0.cst_inj

/-- La instancia `FreshSym String` con los lemas de arriba (el árbol: `[propext, Classical.choice, Quot.sound]`). -/
def Exp.freshString : FOL.FreshSym String where
  shift := FOL.Fresh0.shift
  cst := FOL.Fresh0.cst
  shift_inj := FOL.Fresh0.shift_inj
  cst_inj := Exp.cst_inj
  cst_ne_shift := Exp.cst_ne_shift
#print axioms Exp.freshString
#print axioms FOL.Fresh0.instFreshSymString
