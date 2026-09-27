/-
E4 · (c) ¿Es ESENCIAL el `if IsConsistent₀ (Sₙ ∪ {φₙ})` de LindenbaumStep para el ENUNCIADO de
`lindenbaum_lemma₀` (∃ T maximal consistente ⊇ S, con `IsMaximalConsistent₀` tal como está)?
Variante: la etapa n+1 NO decide la condición Π⁰₁; la METE en el predicado (Prop impredicativo):
      Step (n+1) x  :=  Step n x  ∨  (x = e n ∧ IsConsistent₀ (Step n ∪ {e n}))
La consistencia de cada etapa es un enunciado NEGATIVO, así que basta ¬¬(C ∨ ¬C), que es
intuicionista. La maximalidad de `IsMaximalConsistent₀` también es negativa.
La enumeración se toma como PARÁMETRO (e, e_surj) para aislarla de `natToFormula_surj`.
-/
import FOL.Lindenbaum0

namespace Exp

open FOL.Henkin0 (DerivesSet₀ IsConsistent₀)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ derivesSet0_weakening)

def Step (e : Nat → Formula) (S : Formula → Prop) : Nat → Formula → Prop
  | 0 => S
  | n + 1 => fun x => Or (Step e S n x)
      (And (x = e n) (IsConsistent₀ (fun y => Or (Step e S n y) (y = e n))))

def Limit (e : Nat → Formula) (S : Formula → Prop) (f : Formula) : Prop := ∃ n, Step e S n f

theorem nn_em (C : Prop) : Not (Not (Or C (Not C))) := fun h => h (Or.inr (fun c => h (Or.inl c)))

theorem step_consistent {e : Nat → Formula} {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (Step e S n)
  | 0 => hCons
  | n + 1 => by
      intro hbot
      apply nn_em (IsConsistent₀ (fun y => Or (Step e S n y) (y = e n)))
      intro hem
      cases hem with
      | inl hC =>
        exact hC (derivesSet0_weakening hbot (fun x hx => hx.elim Or.inl (fun h => Or.inr h.1)))
      | inr hNC =>
        exact step_consistent hCons n
          (derivesSet0_weakening hbot (fun x hx => hx.elim id (fun h => absurd h.2 hNC)))

theorem step_mono {e : Nat → Formula} {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : Step e S n x) : Step e S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact Or.inl ih

theorem limit_bound {e : Nat → Formula} {S : Formula → Prop} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → Limit e S g) → ∃ N, ∀ g, g ∈ Γ → Step e S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨ng, hng⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := limit_bound Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max ng N, fun x hx => ?_⟩
      cases hx with
      | head => exact step_mono (Nat.le_max_left _ _) hng
      | tail _ hx' => exact step_mono (Nat.le_max_right _ _) (hN x hx')

/-- ⭐ **Lindenbaum sin decidir nada**: mismo enunciado que `lindenbaum_lemma₀`, para cualquier
enumeración sobreyectiva. -/
theorem lindenbaum_nochoice (e : Nat → Formula) (he : ∀ f, ∃ n, e n = f)
    {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T) (∀ f, S f → T f) := by
  refine ⟨Limit e S, ⟨?_, ?_⟩, fun f hf => ⟨0, hf⟩⟩
  · intro hbot
    obtain ⟨Γ, hΓ, hD⟩ := hbot
    obtain ⟨N, hN⟩ := limit_bound Γ hΓ
    exact step_consistent hCons N ⟨Γ, hN, hD⟩
  · intro f hNot hExt
    obtain ⟨n, hn⟩ := he f
    have hConsN : IsConsistent₀ (fun x => Or (Step e S n x) (x = e n)) := by
      intro hbot
      refine hExt (derivesSet0_weakening hbot ?_)
      intro x hx
      cases hx with
      | inl hS => exact Or.inl ⟨n, hS⟩
      | inr hE => exact Or.inr (hE.trans hn)
    exact hNot ⟨n + 1, Or.inr ⟨hn.symm, hConsN⟩⟩

/-- Con la enumeración del proyecto: lo único que queda es el `choice` de `natToFormula_surj`. -/
theorem lindenbaum_nochoice_nat {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T) (∀ f, S f → T f) :=
  lindenbaum_nochoice FOL.Metamath.Enumeration.natToFormula
    FOL.Metamath.Enumeration.natToFormula_surj hCons

end Exp

#print axioms Exp.step_consistent
#print axioms Exp.lindenbaum_nochoice
#print axioms Exp.lindenbaum_nochoice_nat
#print axioms FOL.Metamath.Enumeration.natToFormula_surj
#print axioms FOL.Metamath.Enumeration.natToFormula
