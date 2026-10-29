import FOL.Compacity0

/-! MUTANTES de la comprobación `type_of% … := rfl`: los TRES deben FALLAR (si no, la
comprobación no discrimina). -/

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)
open FOL.Compacity0 (CountableDom InfiniteDom HasLargeModels)
open FOL.Eigenvariable (occursFormula)
open FOL.Fresh0 (cst)

-- M1: `→` en lugar de `Iff` (más débil): debe fallar
example : (∀ S : Formula → Prop, (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) →
    IsSatisfiable (fun x => x ∈ Γ)) → IsSatisfiable S) = type_of% @FOL.Compacity0.compactness := rfl

-- M2: sin `InfiniteDom` en la conclusión de §3: debe fallar
example : (∀ {S : Formula → Prop}, (∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) →
    HasLargeModels S → ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (CountableDom D) (∀ f, S f → evalFormula M v f))
    = type_of% @FOL.Compacity0.infinite_model_of_large_fresh := rfl

-- M3: el enunciado correcto de §3 (control positivo: ÉSTE debe compilar)
example : (∀ {S : Formula → Prop}, (∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) →
    HasLargeModels S → ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f))
    = type_of% @FOL.Compacity0.infinite_model_of_large_fresh := rfl

-- M4: sin la hipótesis de frescura (más fuerte que el real): debe fallar
example : (∀ {S : Formula → Prop},
    HasLargeModels S → ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f))
    = type_of% @FOL.Compacity0.infinite_model_of_large_fresh := rfl
