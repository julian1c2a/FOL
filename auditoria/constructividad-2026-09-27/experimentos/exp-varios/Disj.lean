import FOL.Inconsistencia
import FOL.Finitary0
open FOL FOL.Finitary0

/-! Extra (4'): `derives0_no_disjunction_property` hereda choice de `derives0_not_complete`
    (semántica de Tarski a `Prop`). Variante por la valuación booleana de `FOL.Finitary0`. -/
namespace Exp

theorem derives0_not_negP_fin : Not (([] : List Formula) ⊢₀ neg (Formula.atom "P" [])) := by
  intro h
  have hc := FOL.NDtoLK0.ndToLK (FOL.Derives2.derives0_iff_derives2.mp h)
  rcases lkc_tval hc true
    (by intro _ hx; exact absurd hx (List.not_mem_nil)) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [tval, neg])
  | tail _ hm => exact absurd hm (List.not_mem_nil)

theorem derives0_not_complete_fin :
    ∃ A : Formula, And (Not (([] : List Formula) ⊢₀ A)) (Not (([] : List Formula) ⊢₀ neg A)) :=
  ⟨_, derives0_not_P_fin, derives0_not_negP_fin⟩

theorem derives0_no_disjunction_property : Not FOL.Inconsistencia.DisjunctionProperty₀ := by
  intro hdp
  obtain ⟨A, hA, hnA⟩ := derives0_not_complete_fin
  rcases hdp A (neg A) (FOL.Propositional0.derives0_em_ctx [] A) with h | h
  · exact hA h
  · exact hnA h

end Exp

#print axioms FOL.Inconsistencia.derives0_no_disjunction_property
#print axioms FOL.Metamath.Soundness0.derives0_not_complete
#print axioms FOL.Finitary0.derives0_not_P_fin
#print axioms Exp.derives0_not_negP_fin
#print axioms Exp.derives0_not_complete_fin
#print axioms Exp.derives0_no_disjunction_property
