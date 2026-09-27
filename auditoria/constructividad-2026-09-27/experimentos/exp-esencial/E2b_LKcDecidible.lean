/-
E2b · (a) ALTERNATIVA para `lkc_sound`: restringida a modelos cuya evaluación es DECIDIBLE, la
solidez multiconclusión sale SIN choice. `implR` decide `eval A`; `allR` decide `eval (∀A)` y usa la
decidibilidad de `eval (∃¬A)` para sacar el contraejemplo.
-/
import FOL.SequentSound0

namespace Exp

open FOL.Metamath.Semantics
open FOL.Sequent0
open FOL.SequentSound0 (eqInstance_valid)

theorem lkc_sound_dec {D : Type} (M : Model D)
    (hdec : ∀ (v : Nat → D) (f : Formula), Decidable (evalFormula M v f)) :
    ∀ {Γ Δ : List Formula}, LKc Γ Δ → ∀ (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hΓ hΔ => intro v hv; exact ⟨A, hΔ, hv A hΓ⟩
  | botL Γ Δ hbot => intro v hv; exact absurd (hv _ hbot) (fun hx => hx)
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro v hv
      obtain ⟨d, hd, hval⟩ := ih v (fun g hg => hv g (hsΓ g hg))
      exact ⟨d, hsΔ d hd, hval⟩
  | implR Γ Δ A B _ ih =>
      intro v hv
      match hdec v A with
      | isTrue hA =>
        obtain ⟨d, hd, hval⟩ := ih v (fun g hg => by
          cases hg with
          | head => exact hA
          | tail _ h' => exact hv g h')
        cases hd with
        | head => exact ⟨Formula.impl A B, List.Mem.head _, fun _ => hval⟩
        | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hval⟩
      | isFalse hA => exact ⟨Formula.impl A B, List.Mem.head _, fun hx => absurd hx hA⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro v hv
      have hAB : evalFormula M v A → evalFormula M v B := hv _ (List.Mem.head _)
      have hvt : ∀ g, g ∈ Γ → evalFormula M v g := fun g hg => hv g (List.Mem.tail _ hg)
      obtain ⟨d, hd, hval⟩ := ih1 v hvt
      cases hd with
      | head =>
          exact ih2 v (fun g hg => by
            cases hg with
            | head => exact hAB hval
            | tail _ h' => exact hvt g h')
      | tail _ hd' => exact ⟨d, hd', hval⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro v hv
      obtain ⟨d1, hd1, hval1⟩ := ih1 v hv
      cases hd1 with
      | tail _ hd1' => exact ⟨d1, List.Mem.tail _ hd1', hval1⟩
      | head =>
          obtain ⟨d2, hd2, hval2⟩ := ih2 v hv
          cases hd2 with
          | tail _ hd2' => exact ⟨d2, List.Mem.tail _ hd2', hval2⟩
          | head => exact ⟨Formula.and A B, List.Mem.head _, And.intro hval1 hval2⟩
  | andL Γ Δ A B _ ih =>
      intro v hv
      have hAB : And (evalFormula M v A) (evalFormula M v B) := hv _ (List.Mem.head _)
      exact ih v (fun g hg => by
        cases hg with
        | head => exact hAB.1
        | tail _ h' =>
            cases h' with
            | head => exact hAB.2
            | tail _ h'' => exact hv g (List.Mem.tail _ h''))
  | orR Γ Δ A B _ ih =>
      intro v hv
      obtain ⟨d, hd, hval⟩ := ih v hv
      cases hd with
      | head => exact ⟨Formula.or A B, List.Mem.head _, Or.inl hval⟩
      | tail _ hd' =>
          cases hd' with
          | head => exact ⟨Formula.or A B, List.Mem.head _, Or.inr hval⟩
          | tail _ hd'' => exact ⟨d, List.Mem.tail _ hd'', hval⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro v hv
      have hAB : Or (evalFormula M v A) (evalFormula M v B) := hv _ (List.Mem.head _)
      have hvt : ∀ g, g ∈ Γ → evalFormula M v g := fun g hg => hv g (List.Mem.tail _ hg)
      cases hAB with
      | inl hA =>
          exact ih1 v (fun g hg => by
            cases hg with
            | head => exact hA
            | tail _ h' => exact hvt g h')
      | inr hB =>
          exact ih2 v (fun g hg => by
            cases hg with
            | head => exact hB
            | tail _ h' => exact hvt g h')
  | allR Γ Δ A _ ih =>
      intro v hv
      match hdec v (Formula.forall A) with
      | isTrue hall => exact ⟨Formula.forall A, List.Mem.head _, hall⟩
      | isFalse hall =>
        have hex : ∃ d : D, Not (evalFormula M (shiftEnv v d) A) :=
          match hdec v (Formula.ex (neg A)) with
          | isTrue h => h
          | isFalse h => absurd (fun d => match hdec (shiftEnv v d) A with
              | isTrue hd => hd
              | isFalse hnd => absurd ⟨d, hnd⟩ h) hall
        obtain ⟨d0, hd0⟩ := hex
        have hlift := (contextSatisfies_lift_zero M v d0 (Γ := Γ)).mpr hv
        obtain ⟨e, he, hval⟩ := ih (shiftEnv v d0) hlift
        cases he with
        | head => exact absurd hval hd0
        | tail _ he' =>
            obtain ⟨e0, he0, heq⟩ := List.mem_map.mp he'
            refine ⟨e0, List.Mem.tail _ he0, ?_⟩
            rw [← heq] at hval
            exact (eval_liftFormula_zero M v d0 e0).mp hval
  | allL Γ Δ A t _ ih =>
      intro v hv
      have hall : ∀ d : D, evalFormula M (shiftEnv v d) A := hv _ (List.Mem.head _)
      have hinst : evalFormula M v (substFormula 0 t A) :=
        (eval_substFormula_zero M v t A).mpr (hall (evalTerm M v t))
      exact ih v (fun g hg => by
        cases hg with
        | head => exact hinst
        | tail _ hg' => exact hv g (List.Mem.tail _ hg'))
  | exR Γ Δ A t _ ih =>
      intro v hv
      obtain ⟨d, hd, hval⟩ := ih v hv
      cases hd with
      | head =>
          exact ⟨Formula.ex A, List.Mem.head _,
            ⟨evalTerm M v t, (eval_substFormula_zero M v t A).mp hval⟩⟩
      | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hval⟩
  | exL Γ Δ A _ ih =>
      intro v hv
      obtain ⟨d0, hd0⟩ : ∃ d : D, evalFormula M (shiftEnv v d) A := hv _ (List.Mem.head _)
      have hctx : ∀ g, g ∈ A :: Γ.map (liftFormula 0) → evalFormula M (shiftEnv v d0) g := by
        intro g hg
        cases hg with
        | head => exact hd0
        | tail _ hg' =>
            exact (contextSatisfies_lift_zero M v d0 (Γ := Γ)).mpr
              (fun x hx => hv x (List.Mem.tail _ hx)) g hg'
      obtain ⟨e, he, hval⟩ := ih (shiftEnv v d0) hctx
      obtain ⟨e0, he0, heq⟩ := List.mem_map.mp he
      refine ⟨e0, he0, ?_⟩
      rw [← heq] at hval
      exact (eval_liftFormula_zero M v d0 e0).mp hval
  | eqAx Γ Δ g hg _ ih =>
      intro v hv
      exact ih v (fun x hx => by
        cases hx with
        | head => exact eqInstance_valid hg M v
        | tail _ h' => exact hv x h')
  | cut Γ Δ A _ _ ih1 ih2 =>
      intro v hv
      obtain ⟨d, hd, hval⟩ := ih1 v hv
      cases hd with
      | head =>
          exact ih2 v (fun g hg => by
            cases hg with
            | head => exact hval
            | tail _ h' => exact hv g h')
      | tail _ hd' => exact ⟨d, hd', hval⟩

end Exp

#print axioms Exp.lkc_sound_dec
