import FOL.Fresh0
import FOL.Enumeration

namespace Exp
open FOL.Fresh0 (cst shift)

/-! Variantes de las cuatro entradas «String», mismos enunciados. -/

-- (1) cst_zero_ne: la misma comprobacion por reduccion, pero por `decide` (instancia
-- `instDecidableEqString = String.decEq`, cero axiomas) en vez de por `BEq`+`ReflBEq`,
-- cuya busqueda de instancia encontraba `ReflBEq` via `Std.LawfulBEqOrd` (String.instOrd).
theorem cst_zero_ne_A (n : Nat) : cst 0 ≠ cst (n + 1) := of_decide_eq_false rfl

-- (1') la prueba original, fijando a mano la instancia ReflBEq buena
theorem cst_zero_ne_B (n : Nat) : cst 0 ≠ cst (n + 1) :=
  @not_eq_of_beq_eq_false String _ (@LawfulBEq.toReflBEq String _ instLawfulBEqString) _ _ rfl

theorem cst_ne_shift_A : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, _ => of_decide_eq_false rfl
  | _ + 1, _ => of_decide_eq_false rfl

theorem cst_inj_A : ∀ m n : Nat, cst m = cst n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (cst_zero_ne_A _)
  | _ + 1, 0, h => absurd h.symm (cst_zero_ne_A _)
  | m + 1, n + 1, h => congrArg (· + 1) (cst_inj_A m n ((String.append_right_inj "a").mp h))

-- (3) cst_bound_sym sin tercio excluso: cota por el TAMANO EN BYTES (utf8ByteSize,
-- un campo cacheado; no decodifica), no por String.length.
theorem cst_utf8ByteSize : ∀ m : Nat, (cst m).utf8ByteSize = m + 1
  | 0 => rfl
  | m + 1 => by
      show ("a" ++ cst m).utf8ByteSize = m + 1 + 1
      rw [String.utf8ByteSize_append, cst_utf8ByteSize m]
      show 1 + (m + 1) = m + 1 + 1
      omega

theorem cst_bound_sym_A (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.utf8ByteSize, fun m hm he => by
    have h := congrArg String.utf8ByteSize he
    rw [cst_utf8ByteSize] at h
    omega⟩

-- (4) natToString_surj sin String.toList: eliminar el testigo de `isValidUTF8`
-- (String.exists_eq_ofList, solo propext).
open FOL.Metamath.Enumeration in
theorem natToString_surj_A (s : String) : ∃ n, natToString n = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  obtain ⟨n, hn⟩ := natToList_surj (l.map Char.toNat)
  exact ⟨n, congrArg String.ofList (by rw [hn, map_ofNat_toNat])⟩

end Exp

#print axioms Exp.cst_zero_ne_A
#print axioms Exp.cst_zero_ne_B
#print axioms Exp.cst_ne_shift_A
#print axioms Exp.cst_inj_A
#print axioms Exp.cst_utf8ByteSize
#print axioms Exp.cst_bound_sym_A
#print axioms Exp.natToString_surj_A
