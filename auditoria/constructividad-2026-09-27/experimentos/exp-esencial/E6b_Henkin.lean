/-
E6b · (d) `skolem_conservative₀` (argumentos FIJOS) usa, en su ruta SEMÁNTICA, que todo modelo se
expande con UN testigo `w` que valida `(∃A) → A[c(t̄)]` (by_cases + Exists.choose).
Ese enunciado semántico —el «bebedor dual» ∃w((∃y A y) → A w)— implica el tercio excluso.
Testigo: D := Option (PLift p), A y := «y es some».
(El `Exists.choose` en sí es prescindible: la meta es un Prop y basta `Exists.elim`.)
-/
import FOL.Skolem0

namespace Exp

open FOL.Metamath.Semantics
open FOL.Skolem0
open FOL.Eigenvariable

theorem henkin_expansion_implies_em
    (hH : ∀ (D : Type) (M : Model D) (v : Nat → D) (A : Formula), Not (occursFormula "c" A) →
      ∃ w : D, evalFormula (updateFunc M "c" (fun _ => w)) v (skolemAxT "c" [] A)) :
    ∀ p : Prop, Or p (Not p) := by
  intro p
  let M : Model (Option (PLift p)) :=
    ⟨fun _ _ => none, fun _ ds => match ds with
      | [d] => ∃ h, d = some h
      | _ => False⟩
  obtain ⟨w, hw⟩ := hH (Option (PLift p)) M (fun _ => none) (Formula.atom "R" [Term.var 0])
    (by show Not (Or False False); intro h; rcases h with h | h <;> exact h)
  have hw' : (∃ y : Option (PLift p), ∃ h, y = some h) → ∃ h, w = some h := by
    intro hy
    have hv := hw (by obtain ⟨y, hy'⟩ := hy; exact ⟨y, hy'⟩)
    rw [eval_substFormula_zero, evalTerm_newT] at hv
    exact hv
  match w, hw' with
  | none, hw' =>
    exact Or.inr (fun hp => by
      obtain ⟨_, hh⟩ := hw' ⟨some ⟨hp⟩, ⟨hp⟩, rfl⟩
      cases hh)
  | some h, _ => exact Or.inl h.down

end Exp

#print axioms Exp.henkin_expansion_implies_em
