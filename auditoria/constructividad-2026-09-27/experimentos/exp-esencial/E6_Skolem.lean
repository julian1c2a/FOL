/-
E6 · (d) ¿Es ESENCIAL el choice de skF / skF_spec?
`skF`/`skF_spec`/`eval_skolemAxN` dicen, juntos: TODO modelo admite una expansión de Skolem que
valida `skolemAxN c n A`. Se toma ESE enunciado (con n = 1) como hipótesis y se deriva
  (i)  el axioma de elección ∀∃ → ∃f para cualquier relación en cualquier tipo habitado, y
  (ii) de (i), el tercio excluso (Diaconescu–Goodman–Myhill).
-/
import FOL.SkolemN0

namespace Exp

open FOL.Metamath.Semantics
open FOL.Skolem0
open FOL.SkolemN0
open FOL.Eigenvariable

def AR : Formula := Formula.atom "R" [Term.var 1, Term.var 0]

theorem AR_fresh : Not (occursFormula "c" AR) := by
  show Not (Or False (Or False False))
  intro h
  rcases h with h | h | h <;> exact h

def relOf {α : Type} (r : α → α → Prop) : List α → Prop
  | [a, b] => r a b
  | _ => False

def Mr {α : Type} (a0 : α) (r : α → α → Prop) : Model α := ⟨fun _ _ => a0, fun _ ds => relOf r ds⟩

/-- (i) El ENUNCIADO «todo modelo tiene expansión de Skolem» implica AC para relaciones. -/
theorem skolem_expansion_implies_ac
    (hSk : ∀ (D : Type) (M : Model D) (v : Nat → D) (A : Formula), Not (occursFormula "c" A) →
      ∃ F : List D → D, evalFormula (updateFunc M "c" F) v (skolemAxN "c" 1 A)) :
    ∀ (α : Type) (a0 : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x) := by
  intro α a0 r
  obtain ⟨F, hF⟩ := hSk α (Mr a0 r) (fun _ => a0) AR AR_fresh
  refine ⟨fun x => F [x], fun x hx => ?_⟩
  have hY := hF x (by obtain ⟨y, hy⟩ := hx; exact ⟨y, hy⟩)
  rw [eval_substFormula_zero] at hY
  have hc : evalTerm (updateFunc (Mr a0 r) "c" F) (shiftEnv (fun _ => a0) x)
      (Term.func "c" (vars 1)) = F [x] := by
    show (if ("c" : String) = "c"
          then F (evalTerms (updateFunc (Mr a0 r) "c" F) (shiftEnv (fun _ => a0) x) (vars 1))
          else (Mr a0 r).func "c"
            (evalTerms (updateFunc (Mr a0 r) "c" F) (shiftEnv (fun _ => a0) x) (vars 1))) = F [x]
    rw [if_pos rfl]
    rfl
  rw [hc] at hY
  exact hY

/-- (ii) Diaconescu: AC para relaciones (en la forma de (i)) implica el tercio excluso. -/
theorem ac_implies_em
    (hAC : ∀ (α : Type) (a0 : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x)) :
    ∀ p : Prop, Or p (Not p) := by
  intro p
  let D := Sum (Bool → Prop) Bool
  let r : D → D → Prop := fun x y => match x, y with
    | Sum.inl P, Sum.inr b => P b
    | _, _ => False
  let U : Bool → Prop := fun b => Or (b = true) p
  let V : Bool → Prop := fun b => Or (b = false) p
  obtain ⟨f, hf⟩ := hAC D (Sum.inr true) r
  have hU : r (Sum.inl U) (f (Sum.inl U)) := hf _ ⟨Sum.inr true, Or.inl rfl⟩
  have hV : r (Sum.inl V) (f (Sum.inl V)) := hf _ ⟨Sum.inr false, Or.inl rfl⟩
  have key : p → f (Sum.inl U) = f (Sum.inl V) := by
    intro hp
    have : U = V := funext (fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩)
    rw [this]
  revert hU hV key
  cases f (Sum.inl U) with
  | inl _ => intro hU; exact hU.elim
  | inr bu =>
    cases f (Sum.inl V) with
    | inl _ => intro _ hV; exact hV.elim
    | inr bv =>
      intro hU hV key
      cases hU with
      | inr hp => exact Or.inl hp
      | inl hbu =>
        cases hV with
        | inr hp => exact Or.inl hp
        | inl hbv =>
          refine Or.inr (fun hp => ?_)
          have h := key hp
          rw [hbu, hbv] at h
          cases h

/-- Control: los objetos reales cumplen la hipótesis de (i). -/
example : ∀ (α : Type) (a0 : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x) :=
  skolem_expansion_implies_ac (fun _ M v A hA =>
    ⟨skF M A v (v 0), eval_skolemAxN M "c" 1 A v (v 0) hA⟩)

end Exp

#print axioms Exp.skolem_expansion_implies_ac
#print axioms Exp.ac_implies_em
