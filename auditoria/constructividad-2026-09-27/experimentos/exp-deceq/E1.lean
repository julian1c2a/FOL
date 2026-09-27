import FOL.DecEq
import FOL.Henkin0

/-! E1 · `henkin_step_consistent₀` con la instancia de `FOL.DecEq` y SIN `open Classical`.
Prueba copiada literalmente del módulo; sólo cambia el entorno de instancias. -/

namespace Exp
open FOL.Eigenvariable
open FOL.Lift0
open FOL.Henkin0

theorem henkin_step_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  have hΓ' : ∀ g, g ∈ Γ.filter (fun x => decide (Not (x = henkinAx c A))) → S g := by
    intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  have hsub : ∀ x, x ∈ Γ → x ∈ henkinAx c A :: Γ.filter (fun y => decide (Not (y = henkinAx c A))) := by
    intro x hx
    by_cases heq : x = henkinAx c A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)
  have hnH : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  have hex : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.ex A :=
    neg_impl_left hnH
  have hnq : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀
      neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  have hfresh : ∀ g, g ∈ Γ.filter (fun y => decide (Not (y = henkinAx c A))) →
      Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  have hall : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  exact hCons ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

end Exp

#print axioms FOL.Henkin0.henkin_step_consistent₀
#print axioms Exp.henkin_step_consistent₀
