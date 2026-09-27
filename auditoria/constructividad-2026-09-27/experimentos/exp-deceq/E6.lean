import FOL.Lindenbaum0

/-! E6 · ¿Qué `Classical.byContradiction` de `max_cons_contains` es esencial? El interior
(`¬¬(S∪{f} ⊢ ⊥) → S∪{f} ⊢ ⊥`) se evita reordenando; el exterior (`¬¬ S f → S f`, con `S` un
predicado arbitrario) no. Se mide la versión «doble negada» con el `intro_impl` de E4. -/

namespace Exp
open FOL.Henkin0
open FOL.Lindenbaum0

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

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

theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := A) Γ hΓ
  exact ⟨Γ', hΓ', Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)⟩

/-- Sin el `byContradiction` exterior: cerrado por derivación **hasta doble negación**. -/
theorem max_cons_contains_nn {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : Not (Not (S f)) := fun hNot =>
  hMax.2 f hNot (fun hInc => hMax.1 (derivesSet0_elim_impl (derivesSet0_intro_impl hInc) h))

/-- Con el exterior (único `Classical.byContradiction` que queda). -/
theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : S f :=
  Classical.byContradiction (max_cons_contains_nn hMax h)

-- ¿`LindenbaumStep` ES el oráculo instanciado con la decisión clásica? (definicional)
end Exp

#print axioms Exp.max_cons_contains_nn
#print axioms Exp.max_cons_contains
