import FOL.Lindenbaum0

/-! E4 · SIN `FOL.DecEq` y SIN `open Classical`: no se decide ninguna igualdad. La hipótesis ya
da, para cada `g ∈ Γ`, la disyunción `S g ∨ g = H`; como la meta es una `Prop` (`False` o un
`∃`), se parte el contexto por inducción sobre `Γ` eliminando esa `Or`. -/

namespace Exp
open FOL.Eigenvariable
open FOL.Lift0
open FOL.Henkin0
open FOL.Lindenbaum0

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

/-- Partir un contexto finito sin decidir la igualdad. -/
theorem ctx_split {S : Formula → Prop} {H : Formula} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → Or (S g) (g = H)) →
    ∃ Γ' : List Formula, And (∀ g, g ∈ Γ' → S g) (∀ x, x ∈ Γ → x ∈ H :: Γ')
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨Γ', hS, hsub⟩ := ctx_split Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      cases hΓ g (List.Mem.head _) with
      | inl hg =>
        refine ⟨g :: Γ', ?_, ?_⟩
        · intro x hx
          cases hx with
          | head => exact hg
          | tail _ hx => exact hS x hx
        · intro x hx
          cases hx with
          | head => exact List.Mem.tail _ (List.Mem.head _)
          | tail _ hx =>
            cases hsub x hx with
            | head => exact List.Mem.head _
            | tail _ h => exact List.Mem.tail _ (List.Mem.tail _ h)
      | inr hg =>
        refine ⟨Γ', hS, ?_⟩
        intro x hx
        cases hx with
        | head => rw [hg]; exact List.Mem.head _
        | tail _ hx => exact hsub x hx

theorem henkin_step_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := henkinAx c A) Γ hΓ
  have hnH : Γ' ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  have hex : Γ' ⊢₀ Formula.ex A := neg_impl_left hnH
  have hnq : Γ' ⊢₀ neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  have hfresh : ∀ g, g ∈ Γ' → Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  have hall : Γ' ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  exact hCons ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := A) Γ hΓ
  exact ⟨Γ', hΓ', Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)⟩

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : S f := by
  refine Classical.byContradiction (fun hNot => ?_)
  have hInc : (fun x => Or (S x) (x = f)) ⊢₀* Formula.bottom :=
    Classical.byContradiction (fun hC => hMax.2 f hNot hC)
  exact hMax.1 (derivesSet0_elim_impl (derivesSet0_intro_impl hInc) h)

end Exp

#print axioms Exp.ctx_split
#print axioms Exp.henkin_step_consistent₀
#print axioms Exp.derivesSet0_intro_impl
#print axioms Exp.max_cons_contains
#print axioms FOL.Henkin0.neg_impl_left
#print axioms FOL.Lift0.derives0_ex_forall_neg_absurd
#print axioms FOL.Eigenvariable.derives0_gen_fresh
#print axioms FOL.Henkin0.abs_neg_witness
