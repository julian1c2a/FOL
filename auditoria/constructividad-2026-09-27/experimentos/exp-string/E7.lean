import FOL.Fresh0

/-! Controles adversariales: los analogos FALSOS de las variantes NO deben compilar. -/
namespace ExpCtl
open FOL.Fresh0 (cst shift)

-- (a) falso: cst 1 = "a" ++ cst 0 literalmente. Debe FALLAR.
theorem bad_a : cst 1 ≠ "a" ++ cst 0 := of_decide_eq_false rfl

-- (b) falso con variable libre: cst (n+1) = "a" ++ cst n. Debe FALLAR.
theorem bad_b (n : Nat) : cst (n + 1) ≠ "a" ++ cst n := of_decide_eq_false rfl

-- (c) falso: cst 0 = shift s para s = ""? no: shift "" = "f" ≠ "g". Probamos el falso
-- "fg" = shift "g": debe FALLAR.
theorem bad_c : ("fg" : String) ≠ shift "g" := of_decide_eq_false rfl

-- (d) cota falsa de tamano: debe FALLAR.
theorem bad_d : ∀ m : Nat, (cst m).utf8ByteSize = m
  | 0 => rfl
  | m + 1 => by
      show ("a" ++ cst m).utf8ByteSize = m + 1
      rw [String.utf8ByteSize_append, bad_d m]
      show 1 + m = m + 1
      omega

-- (e) control positivo: verdadero, debe COMPILAR
theorem ok_e (n : Nat) : cst (n + 1) ≠ shift "x" := of_decide_eq_false rfl
end ExpCtl
#print axioms ExpCtl.ok_e
