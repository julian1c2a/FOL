/-
E8 · (d) La conservatividad del axioma de HENKIN (el caso n = 0, t̄ = [] de `skolem_conservative₀`,
que es `henkin_conservative₀`) sale SIN choice por la vía SINTÁCTICA:
  · `henkin_step_pos`: la prueba de `henkin_step_consistent₀` enunciada en POSITIVO
    (una derivación de ⊥ desde S ∪ {H} se transforma en una desde S), con el `DecidableEq Formula`
    real en vez de `Classical.propDecidable`;
  · `henkin_conservative_syn`: (H :: Γ) ⊢₀ φ → Γ ⊢₀ φ, con c fresco.
-/
import FOL.Skolem0
import FOL.DecEq

namespace Exp

open FOL.Henkin0 (DerivesSet₀ henkinAx neg_impl_left neg_impl_right abs_neg_witness)
open FOL.Eigenvariable
open FOL.Lift0

theorem henkin_step_pos {S : Formula → Prop} (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A))
    (hbot : DerivesSet₀ (fun x => Or (S x) (x = henkinAx c A)) Formula.bottom) :
    DerivesSet₀ S Formula.bottom := by
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
  have hex := neg_impl_left hnH
  have hnq := neg_impl_right hnH
  have hfresh : ∀ g, g ∈ Γ.filter (fun y => decide (Not (y = henkinAx c A))) →
      Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  have hall : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  exact ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

/-- ⭐ **Conservatividad de Henkin, sintáctica y sin choice.** -/
theorem henkin_conservative_syn {c : String} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (henkinAx c A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ := by
  -- (H :: ¬φ :: Γ) ⊢₀ ⊥
  have hbot : (henkinAx c A :: neg φ :: Γ) ⊢₀ Formula.bottom := by
    refine Derives₀.elim_impl _ φ Formula.bottom
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
    refine Derives₀.weakening _ _ _ h ?_
    intro x hx
    cases hx with
    | head => exact List.Mem.head _
    | tail _ hx' => exact List.Mem.tail _ (List.Mem.tail _ hx')
  have hS : DerivesSet₀ (fun x => Or (x ∈ Γ) (x = neg φ)) Formula.bottom := by
    refine henkin_step_pos c A ?_ hA ⟨_, ?_, hbot⟩
    · intro g hg
      cases hg with
      | inl hm => exact hΓ g hm
      | inr he => subst he; exact fun ho => ho.elim hφ (fun h => h)
    · intro x hx
      cases hx with
      | head => exact Or.inr rfl
      | tail _ hx' =>
        cases hx' with
        | head => exact Or.inl (Or.inr rfl)
        | tail _ hx'' => exact Or.inl (Or.inl hx'')
  obtain ⟨Δ, hΔ, hD⟩ := hS
  -- sacar ¬φ del contexto finito y cerrar con dne
  have hsub : ∀ x, x ∈ Δ → x ∈ neg φ :: Δ.filter (fun y => decide (Not (y = neg φ))) := by
    intro x hx
    by_cases heq : x = neg φ
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)
  have hnn : (Δ.filter (fun y => decide (Not (y = neg φ)))) ⊢₀ neg (neg φ) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  refine Derives₀.weakening _ _ _ (Derives₀.dne_rule _ _ hnn) ?_
  intro x hx
  have h1 := List.mem_filter.mp hx
  have hne := of_decide_eq_true h1.2
  cases hΔ x h1.1 with
  | inl hm => exact hm
  | inr he => exact absurd he hne

/-- Mismo enunciado que `FOL.Skolem0.skolem_conservative_n_zero`/`henkin_conservative₀`
(`skolemAxT c [] A` es `henkinAx c A` por `rfl`). -/
example {c : String} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g)) (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ)) (h : (FOL.Skolem0.skolemAxT c [] A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ :=
  henkin_conservative_syn hΓ hA hφ h

end Exp

#print axioms Exp.henkin_step_pos
#print axioms Exp.henkin_conservative_syn
#print axioms FOL.Skolem0.henkin_conservative₀
