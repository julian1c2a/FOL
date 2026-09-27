import FOL.Enumeration
import FOL.Fresh0

/-! Variante «parche minimo»: exactamente el texto que sustituiria a las cuatro pruebas en el
arbol real, SIN declaraciones nuevas (la cota de tamano va como `have` local). -/
namespace ExpMin
open FOL.Fresh0 (cst shift cst_inj)

theorem cst_zero_ne (n : Nat) : cst 0 ≠ cst (n + 1) := of_decide_eq_false rfl

theorem cst_ne_shift : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, _ => of_decide_eq_false rfl
  | _ + 1, _ => of_decide_eq_false rfl

theorem cst_bound_sym (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s := by
  have hsz : ∀ m, (cst m).utf8ByteSize = m + 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        show ("a" ++ cst m).utf8ByteSize = m + 1 + 1
        rw [String.utf8ByteSize_append, ih]
        show 1 + (m + 1) = m + 1 + 1
        omega
  refine ⟨s.utf8ByteSize, fun m hm he => ?_⟩
  have h := congrArg String.utf8ByteSize he
  rw [hsz] at h
  omega

open FOL.Metamath.Enumeration in
theorem natToString_surj (s : String) : ∃ n, natToString n = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  obtain ⟨n, hn⟩ := natToList_surj (l.map Char.toNat)
  exact ⟨n, congrArg String.ofList (by rw [hn, map_ofNat_toNat])⟩

end ExpMin
#print axioms ExpMin.cst_zero_ne
#print axioms ExpMin.cst_ne_shift
#print axioms ExpMin.cst_bound_sym
#print axioms ExpMin.natToString_surj
