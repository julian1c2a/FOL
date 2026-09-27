import FOL.Lindenbaum0

/-! E3c · CONTROL: la misma copia SIN `import FOL.DecEq` y CON `open Classical` (debe reproducir el choice). -/

namespace Exp
open FOL.Henkin0
open FOL.Lindenbaum0
open Classical

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ.filter (fun y => decide (Not (y = A))), ?_, ?_⟩
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  · refine Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD ?_)
    intro x hx
    by_cases heq : x = A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : S f := by
  refine Classical.byContradiction (fun hNot => ?_)
  have hInc : (fun x => Or (S x) (x = f)) ⊢₀* Formula.bottom :=
    Classical.byContradiction (fun hC => hMax.2 f hNot hC)
  exact hMax.1 (derivesSet0_elim_impl (derivesSet0_intro_impl hInc) h)

end Exp

#print axioms FOL.Lindenbaum0.derivesSet0_intro_impl
#print axioms Exp.derivesSet0_intro_impl
#print axioms FOL.Lindenbaum0.max_cons_contains
#print axioms Exp.max_cons_contains
#print axioms FOL.Lindenbaum0.derivesSet0_elim_impl
#print axioms Classical.byContradiction
