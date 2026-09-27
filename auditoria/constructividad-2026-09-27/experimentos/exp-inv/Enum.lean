import FOL.Enumeration

/-! Experimento de auditoría: ¿el `Classical.choice` de `natToString_surj` es del núcleo o de la
ruta elegida? `String.toList`/`String.ofList_toList` lo llevan; `String.exists_eq_ofList`, ¿no? -/

#print axioms String.exists_eq_ofList
#print axioms String.ofList_inj

namespace Exp
open FOL.Metamath.Enumeration

theorem natToString_surj (s : String) : ∃ n, natToString n = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  obtain ⟨n, hn⟩ := natToList_surj (l.map Char.toNat)
  refine ⟨n, ?_⟩
  show String.ofList ((natToList n).map Char.ofNat) = String.ofList l
  rw [hn, map_ofNat_toNat]

end Exp

#print axioms Exp.natToString_surj
#print axioms FOL.Metamath.Enumeration.natToString_surj

def Exp.enumString : FOL.EnumSym String := ⟨FOL.Metamath.Enumeration.natToString, Exp.natToString_surj⟩
#print axioms Exp.enumString
#print axioms FOL.Metamath.Enumeration.instEnumSymString
