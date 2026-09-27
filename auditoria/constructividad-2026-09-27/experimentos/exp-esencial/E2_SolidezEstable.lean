/-
E2 · (a) ALTERNATIVA: la solidez de `Derives₀` restringida a modelos cuya evaluación es ¬¬‑ESTABLE
(en particular, los de evaluación decidible) NO necesita Classical.choice.
Es la misma inducción que `derives0_soundness`, con el modelo fijo; los tres casos clásicos
(`dne_rule`, `dne_schema`, `forall_not_ex_not`) usan la estabilidad en vez de `byContradiction`.
-/
import FOL.Soundness0

namespace Exp

open FOL.Metamath.Semantics

theorem sound_stable {D : Type} (M : Model D)
    (hstab : ∀ (v : Nat → D) (f : Formula), Not (Not (evalFormula M v f)) → evalFormula M v f)
    {Γ : List Formula} {f : Formula} (h : Γ ⊢₀ f) :
    ∀ v, contextSatisfies M v Γ → evalFormula M v f := by
  induction h with
  | hyp Γ' f' hIn => intro v hΓ; exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro v hΓ hA
    apply ih v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A => intro v hΓ; exact (ih_impl v hΓ) (ih_A v hΓ)
  | intro_and Γ' A B _ _ ihA ihB => intro v hΓ; exact ⟨ihA v hΓ, ihB v hΓ⟩
  | elim_and_l Γ' A B _ ih => intro v hΓ; exact (ih v hΓ).left
  | elim_and_r Γ' A B _ ih => intro v hΓ; exact (ih v hΓ).right
  | intro_or_l Γ' A B _ ih => intro v hΓ; exact Or.inl (ih v hΓ)
  | intro_or_r Γ' A B _ ih => intro v hΓ; exact Or.inr (ih v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro v hΓ
    cases ih_or v hΓ with
    | inl hA =>
      apply ih_A v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | intro_forall Γ' A _ ih =>
    intro v hΓ d
    exact ih (shiftEnv v d) ((contextSatisfies_lift_zero M v d).mpr hΓ)
  | elim_forall Γ' A t _ ih =>
    intro v hΓ
    exact (eval_substFormula_zero M v t A).mpr (ih v hΓ (evalTerm M v t))
  | intro_ex Γ' A t _ ih =>
    intro v hΓ
    exact ⟨evalTerm M v t, (eval_substFormula_zero M v t A).mp (ih v hΓ)⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro v hΓ
    obtain ⟨d, hd⟩ := ih_ex v hΓ
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    exact (eval_liftFormula_zero M v d B).mp (ih_B (shiftEnv v d) hCtx)
  | bot_elim Γ' A _ ih => intro v hΓ; exact (ih v hΓ).elim
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro v hΓ
    exact ih v (fun g hg => hΓ g (hSubset g hg))
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro v hΓ
    have hEquiv := replaceAt_soundness M v h_get (fun v' => rule_soundness M h_rule v')
    rw [h_replace]
    exact hEquiv.mp (ih v hΓ)
  -- ⭐ los tres casos clásicos: ESTABILIDAD en vez de Classical.byContradiction
  | dne_rule Γ' A _ ih => intro v hΓ; exact hstab v A (ih v hΓ)
  | dne_schema Γ' A => intro v _ hnn; exact hstab v A hnn
  | forall_not_ex_not Γ' A =>
    intro v _ hnf
    apply hstab v (Formula.ex (neg A))
    intro hne
    apply hnf
    intro d
    apply hstab (shiftEnv v d) A
    intro hnd
    exact hne ⟨d, hnd⟩
  | refl Γ' t => intro v _; rfl
  | subst Γ' t1 t2 f' _ _ ih_eq ih_f =>
    intro v hΓ
    have heq : evalTerm M v t1 = evalTerm M v t2 := ih_eq v hΓ
    have h1 := (eval_substFormula_zero M v t1 f').mp (ih_f v hΓ)
    rw [heq] at h1
    exact (eval_substFormula_zero M v t2 f').mpr h1

/-- Estable ⇐ decidible. -/
theorem stable_of_dec {D : Type} (M : Model D)
    (hdec : ∀ (v : Nat → D) (f : Formula), Decidable (evalFormula M v f)) :
    ∀ (v : Nat → D) (f : Formula), Not (Not (evalFormula M v f)) → evalFormula M v f :=
  fun v f hnn => match hdec v f with
    | isTrue h => h
    | isFalse h => absurd h hnn

end Exp

#print axioms Exp.sound_stable
#print axioms Exp.stable_of_dec
