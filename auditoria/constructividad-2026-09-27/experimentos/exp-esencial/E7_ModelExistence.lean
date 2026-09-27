/-
E7 · (b) El ENUNCIADO de `model_existence_lemma₀` (IsConsistent₀ S → IsSatisfiable S, con S un
predicado de Lean ARBITRARIO) implica el tercio excluso DÉBIL: ∀ P, ¬P ∨ ¬¬P.
Testigo: S_P := {Q ∨ R} ∪ {¬Q | P} ∪ {¬R | ¬P}. Es consistente SIN choice (¬¬(P ∨ ¬P) basta, y
cada caso se refuta con un modelo de un punto de evaluación decidible, vía `sound_stable`).
Q y R son átomos de ARIDAD distinta para no comparar `String`s.
-/
import FOL.Canonical0

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


open FOL.Henkin0 (DerivesSet₀ IsConsistent₀)
open FOL.Canonical0 (IsSatisfiable)

def decU (M : Model Unit) (hrel : ∀ p ds, Decidable (M.rel p ds)) :
    (v : Nat → Unit) → (f : Formula) → Decidable (evalFormula M v f)
  | _, .bottom => isFalse (fun h => h)
  | v, .atom p ts => hrel p (evalTerms M v ts)
  | _, .eq _ _ => isTrue rfl
  | v, .impl a b =>
    match decU M hrel v a, decU M hrel v b with
    | _, isTrue hb => isTrue (fun _ => hb)
    | isFalse ha, _ => isTrue (fun h => absurd h ha)
    | isTrue ha, isFalse hb => isFalse (fun h => hb (h ha))
  | v, .forall a =>
    match decU M hrel (shiftEnv v ()) a with
    | isTrue h => isTrue (fun _ => h)
    | isFalse h => isFalse (fun hall => h (hall ()))
  | v, .and a b =>
    match decU M hrel v a, decU M hrel v b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun h => ha h.1)
    | _, isFalse hb => isFalse (fun h => hb h.2)
  | v, .or a b =>
    match decU M hrel v a, decU M hrel v b with
    | isTrue ha, _ => isTrue (Or.inl ha)
    | _, isTrue hb => isTrue (Or.inr hb)
    | isFalse ha, isFalse hb => isFalse (fun h => h.elim ha hb)
  | v, .ex a =>
    match decU M hrel (shiftEnv v ()) a with
    | isTrue h => isTrue ⟨(), h⟩
    | isFalse h => isFalse (fun ⟨_, hd⟩ => h hd)

def relB (qv rv : Bool) : List Unit → Prop
  | [] => qv = true
  | _ :: _ => rv = true

instance (qv rv : Bool) (ds : List Unit) : Decidable (relB qv rv ds) :=
  match ds with
  | [] => inferInstanceAs (Decidable (qv = true))
  | _ :: _ => inferInstanceAs (Decidable (rv = true))

def MB (qv rv : Bool) : Model Unit := ⟨fun _ _ => (), fun _ ds => relB qv rv ds⟩

def Qf : Formula := Formula.atom "Q" []
def Rf : Formula := Formula.atom "Q" [Term.var 0]

def SP (P : Prop) : Formula → Prop := fun x =>
  Or (x = Formula.or Qf Rf) (Or (And (x = neg Qf) P) (And (x = neg Rf) (Not P)))

theorem nn_em (C : Prop) : Not (Not (Or C (Not C))) := fun h => h (Or.inr (fun c => h (Or.inl c)))

theorem SP_consistent (P : Prop) : IsConsistent₀ (SP P) := by
  intro ⟨Γ, hΓ, hD⟩
  apply nn_em P
  intro hem
  cases hem with
  | inl hP =>
    refine sound_stable (MB false true)
      (stable_of_dec _ (decU _ (fun _ ds => inferInstanceAs (Decidable (relB false true ds)))))
      hD (fun _ => ()) (fun g hg => ?_)
    rcases hΓ g hg with h | ⟨h, _⟩ | ⟨_, hn⟩
    · subst h; exact Or.inr rfl
    · subst h; exact fun hq => Bool.noConfusion hq
    · exact absurd hP hn
  | inr hnP =>
    refine sound_stable (MB true false)
      (stable_of_dec _ (decU _ (fun _ ds => inferInstanceAs (Decidable (relB true false ds)))))
      hD (fun _ => ()) (fun g hg => ?_)
    rcases hΓ g hg with h | ⟨_, hp⟩ | ⟨h, _⟩
    · subst h; exact Or.inl rfl
    · exact absurd hp hnP
    · subst h; exact fun hr => Bool.noConfusion hr

theorem model_existence_stmt_implies_wlem
    (hME : ∀ {S : Formula → Prop}, IsConsistent₀ S → IsSatisfiable S) :
    ∀ P : Prop, Or (Not P) (Not (Not P)) := by
  intro P
  obtain ⟨D, M, v, hM⟩ := hME (SP_consistent P)
  have hOr : Or (evalFormula M v Qf) (evalFormula M v Rf) := hM (Formula.or Qf Rf) (Or.inl rfl)
  have hPQ : P → Not (evalFormula M v Qf) := fun hP => hM (neg Qf) (Or.inr (Or.inl ⟨rfl, hP⟩))
  have hnPR : Not P → Not (evalFormula M v Rf) :=
    fun hnP => hM (neg Rf) (Or.inr (Or.inr ⟨rfl, hnP⟩))
  cases hOr with
  | inl hq => exact Or.inl (fun hP => hPQ hP hq)
  | inr hr => exact Or.inr (fun hnP => hnPR hnP hr)

example : ∀ P : Prop, Or (Not P) (Not (Not P)) :=
  model_existence_stmt_implies_wlem (fun h => FOL.Canonical0.model_existence_lemma₀ h)

end Exp

#print axioms Exp.SP_consistent
#print axioms Exp.model_existence_stmt_implies_wlem
