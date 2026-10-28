/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Soundness0, FOL.SequentSound0, FOL.Canonical0, FOL.DecEq, FOL.SkolemN0, FOL.Inconsistencia
-- @axiom_system: intuitionistic (ninguno de sus teoremas lleva Classical.choice: es lo que miden)
-- @importance: medium

import FOL.Soundness0
import FOL.SequentSound0
import FOL.Canonical0
import FOL.DecEq
import FOL.SkolemN0
import FOL.Inconsistencia

/-!
# `FOL.Esencialidad0` — la ESENCIALIDAD del `Classical.choice` de FOL, en el build (T19, ADR‑203 de RPP)

La auditoría de constructividad del 2026‑09‑27 (`auditoria/constructividad-2026-09-27/`, `AXIOMS.md` §4) midió que el
`Classical.choice` de varios titulares de FOL es ESENCIAL: se toma el ENUNCIADO como hipótesis y se deriva de él un
principio clásico sobre un `P : Prop` arbitrario sin `Classical.choice`; si compila, ninguna prueba del enunciado puede
evitarlo. Aquellos experimentos se compilaron contra FOL `537cc20`, con símbolos `String`, y desde D7 (`List Char`) no
compilaban: eran registro. Aquí están, en el build, con los símbolos de hoy y el mismo argumento (que no depende del
tipo de símbolo), cada uno en su subespacio:

* **E1** — el enunciado de `derives0_soundness` implica `¬¬P → P`; el de `lkc_sound`, `P ∨ ¬P`.
* **E2** — la ALTERNATIVA: la solidez de `Derives₀` en modelos de evaluación ¬¬‑ESTABLE (`sound_stable`; en particular
  los decidibles, `stable_of_dec`) no necesita `Classical.choice`. **E2b**, lo mismo para `LKc` (`lkc_sound_dec`).
* **E3** — los enunciados del lema de la verdad sobre un maximal ARBITRARIO (`max_cons_contains`, `max_cons_complete`,
  `max_cons_impl_iff`, `max_cons_or`) implican `¬¬P → P`.
* **E6** — «todo modelo admite expansión de Skolem» implica AC (`skolem_expansion_implies_ac`), y AC implica EM
  (`ac_implies_em`, Diaconescu).
* **E7** — el enunciado de la existencia de modelo implica WLEM, `¬P ∨ ¬¬P` (`model_existence_stmt_implies_wlem`).
* **ExElimFin** — y de E2 sale lo que `FOL.Inconsistencia` creía imposible: **`ex_elim` se refuta sin
  `Classical.choice`** (`ex_elim_refutable_fin`), porque el modelo de dos puntos de su refutación es DECIDIBLE y su
  solidez es la estable.

Nada de esto lo consume otro módulo: es la medida, en el build, con su fila de footprint en RPP.
-/

namespace FOL.Esencialidad0.E1

/-
E1 · (a) ¿Es ESENCIAL el Classical.choice de derives0_soundness y lkc_sound para el ENUNCIADO?
Se toma el ENUNCIADO como hipótesis (no el teorema) y se deriva de él un principio clásico sobre
un `P : Prop` ARBITRARIO. Si el footprint de la implicación no trae Classical.choice, el enunciado
implica ese principio en la teoría base de Lean ⇒ ninguna prueba del enunciado puede evitar choice.
-/


open FOL.Metamath.Semantics

/-- Modelo de un punto donde TODA relación vale `P`. -/
def MP (P : Prop) : Model Unit := ⟨fun _ _ => (), fun _ _ => P⟩

def Q : Formula := Formula.atom ['Q'] []

/-- El ENUNCIADO de `derives0_soundness` implica la doble negación para todo `P : Prop`. -/
theorem soundness_stmt_implies_dne
    (hS : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢₀ f) → satisfies Γ f) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have h := hS (Derives₀.dne_schema [] Q) Unit (MP P) (fun _ => ())
    (fun _ hf => absurd hf List.not_mem_nil)
  exact h hnn

/-- El ENUNCIADO de `lkc_sound` implica el tercio excluso para todo `P : Prop`. -/
theorem lkc_stmt_implies_em
    (hS : ∀ {Γ Δ : List Formula}, LKc Γ Δ → ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d)) :
    ∀ P : Prop, Or P (Not P) := by
  intro P
  have hd : LKc [] [neg Q, Q] :=
    LKc.implR [] [Q] Q Formula.bottom
      (LKc.ax [Q] [Formula.bottom, Q] Q (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  obtain ⟨d, hmem, hval⟩ := hS hd (MP P) (fun _ => ()) (fun _ h => absurd h List.not_mem_nil)
  cases hmem with
  | head => exact Or.inr hval
  | tail _ h' =>
    cases h' with
    | head => exact Or.inl hval
    | tail _ h'' => exact absurd h'' List.not_mem_nil

/-- Control: los teoremas reales cumplen las hipótesis (así las hipótesis no son vacías). -/
example : ∀ P : Prop, Not (Not P) → P :=
  soundness_stmt_implies_dne (fun h => FOL.Metamath.Soundness0.derives0_soundness h)
example : ∀ P : Prop, Or P (Not P) :=
  lkc_stmt_implies_em (fun h => FOL.SequentSound0.lkc_sound h)

end FOL.Esencialidad0.E1

namespace FOL.Esencialidad0.E2

/-
E2 · (a) ALTERNATIVA: la solidez de `Derives₀` restringida a modelos cuya evaluación es ¬¬‑ESTABLE
(en particular, los de evaluación decidible) NO necesita Classical.choice.
Es la misma inducción que `derives0_soundness`, con el modelo fijo; los tres casos clásicos
(`dne_rule`, `dne_schema`, `forall_not_ex_not`) usan la estabilidad en vez de `byContradiction`.
-/


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

end FOL.Esencialidad0.E2

namespace FOL.Esencialidad0.E2b

/-
E2b · (a) ALTERNATIVA para `lkc_sound`: restringida a modelos cuya evaluación es DECIDIBLE, la
solidez multiconclusión sale SIN choice. `implR` decide `eval A`; `allR` decide `eval (∀A)` y usa la
decidibilidad de `eval (∃¬A)` para sacar el contraejemplo.
-/


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

end FOL.Esencialidad0.E2b

namespace FOL.Esencialidad0.E3

/-
E3 · (b) ¿Es ESENCIAL el tercio excluso de max_cons_contains / max_cons_complete /
max_cons_impl_iff / max_cons_or para sus ENUNCIADOS (con `S` arbitrario)?
  Parte 1: cada ENUNCIADO, tomado como hipótesis, implica ¬¬P → P para todo P : Prop.
           Testigo: S_P := {x | Mtrue ⊨ x} ∩ {x | x = f₀ → P}, que es maximal consistente si ¬¬P.
           (La consistencia de Th(Mtrue) se prueba SIN choice con `sound_stable`, copiado de E2.)
  Parte 2: con `[DecidablePred S]` las cinco versiones salen SIN choice (y sin MP).
-/


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


open FOL.Henkin0 (DerivesSet₀ IsConsistent₀ neg_impl_left neg_impl_right)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ IsHenkin derivesSet0_hyp derivesSet0_weakening
  derivesSet0_elim_impl)
open FOL.Canonical0 (IsMemComplete derivesSet0_map derivesSet0_map2)
open FOL.Metamath.Soundness0 (Mtrue)

-- ═══ Parte 1 ═══════════════════════════════════════════════════════════════
def decTrue : (v : Nat → Unit) → (f : Formula) → Decidable (evalFormula Mtrue v f)
  | _, .bottom => isFalse (fun h => h)
  | _, .atom _ _ => isTrue trivial
  | _, .eq _ _ => isTrue rfl
  | v, .impl a b =>
    match decTrue v a, decTrue v b with
    | _, isTrue hb => isTrue (fun _ => hb)
    | isFalse ha, _ => isTrue (fun h => absurd h ha)
    | isTrue ha, isFalse hb => isFalse (fun h => hb (h ha))
  | v, .forall a =>
    match decTrue (shiftEnv v ()) a with
    | isTrue h => isTrue (fun _ => h)
    | isFalse h => isFalse (fun hall => h (hall ()))
  | v, .and a b =>
    match decTrue v a, decTrue v b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun h => ha h.1)
    | _, isFalse hb => isFalse (fun h => hb h.2)
  | v, .or a b =>
    match decTrue v a, decTrue v b with
    | isTrue ha, _ => isTrue (Or.inl ha)
    | _, isTrue hb => isTrue (Or.inr hb)
    | isFalse ha, isFalse hb => isFalse (fun h => h.elim ha hb)
  | v, .ex a =>
    match decTrue (shiftEnv v ()) a with
    | isTrue h => isTrue ⟨(), h⟩
    | isFalse h => isFalse (fun ⟨_, hd⟩ => h hd)

/-- La teoría del modelo de un punto con todo verdadero. -/
def T : Formula → Prop := fun x => evalFormula Mtrue (fun _ => ()) x

theorem T_consistent : IsConsistent₀ T := by
  intro ⟨Γ, hΓ, hD⟩
  exact sound_stable Mtrue (stable_of_dec Mtrue decTrue) hD (fun _ => ()) hΓ

def SP (f₀ : Formula) (P : Prop) : Formula → Prop := fun x => And (T x) (x = f₀ → P)

theorem SP_max {f₀ : Formula} {P : Prop} (hf₀ : T f₀) (hneg : ∀ g, Not (neg g = f₀))
    (hnn : Not (Not P)) : IsMaximalConsistent₀ (SP f₀ P) := by
  refine ⟨fun hbot => T_consistent (derivesSet0_weakening hbot (fun x hx => hx.1)), ?_⟩
  intro g hng hcons
  by_cases hg : g = f₀
  · subst hg
    exact hnn (fun hP => hng ⟨hf₀, fun _ => hP⟩)
  · have hTg : Not (T g) := fun hT => hng ⟨hT, fun h => absurd h hg⟩
    have hTng : SP f₀ P (neg g) := ⟨fun hx => hTg hx, fun h => absurd h (hneg g)⟩
    apply hcons
    refine ⟨[neg g, g], ?_, ?_⟩
    · intro x hx
      cases hx with
      | head => exact Or.inl hTng
      | tail _ hx' =>
        cases hx' with
        | head => exact Or.inr rfl
        | tail _ hx'' => exact absurd hx'' List.not_mem_nil
    · exact Derives₀.elim_impl _ g Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _))
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

def f0 : Formula := Formula.eq (Term.var 0) (Term.var 0)
def fI : Formula := Formula.impl f0 f0
def fO : Formula := Formula.or f0 f0

theorem f0_T : T f0 := rfl
theorem fI_T : T fI := fun h => h
theorem fO_T : T fO := Or.inl rfl
theorem f0_notneg : ∀ g, Not (neg g = f0) := fun _ h => by cases h
theorem fI_notneg : ∀ g, Not (neg g = fI) := fun _ h => by cases h
theorem fO_notneg : ∀ g, Not (neg g = fO) := fun _ h => by cases h

theorem contains_stmt_implies_dne
    (hmc : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {f : Formula}, DerivesSet₀ S f → S f) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := f0) (P := P) f0_T f0_notneg hnn
  have h := hmc hMax (f := f0) ⟨[], fun _ h => absurd h List.not_mem_nil, Derives₀.refl [] (Term.var 0)⟩
  exact h.2 rfl

theorem complete_stmt_implies_dne
    (hmc : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → IsMemComplete S) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := f0) (P := P) f0_T f0_notneg hnn
  cases hmc hMax f0 with
  | inl h => exact h.2 rfl
  | inr h => exact absurd f0_T h.1

theorem impl_iff_stmt_implies_dne
    (hmi : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {A B : Formula},
      S (Formula.impl A B) ↔ (S A → S B)) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := fI) (P := P) fI_T fI_notneg hnn
  have hf0 : SP fI P f0 := ⟨f0_T, fun h => by cases h⟩
  exact ((hmi hMax (A := f0) (B := f0)).mpr (fun _ => hf0)).2 rfl

theorem or_stmt_implies_dne
    (hmo : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {A B : Formula},
      S (Formula.or A B) ↔ Or (S A) (S B)) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := fO) (P := P) fO_T fO_notneg hnn
  have hf0 : SP fO P f0 := ⟨f0_T, fun h => by cases h⟩
  exact ((hmo hMax (A := f0) (B := f0)).mpr (Or.inl hf0)).2 rfl

-- controles: los teoremas reales cumplen las hipótesis
example : ∀ P : Prop, Not (Not P) → P :=
  contains_stmt_implies_dne (fun hMax _ h => FOL.Lindenbaum0.max_cons_contains hMax h)
example : ∀ P : Prop, Not (Not P) → P :=
  complete_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_complete hMax)
example : ∀ P : Prop, Not (Not P) → P :=
  impl_iff_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_impl_iff hMax)
example : ∀ P : Prop, Not (Not P) → P :=
  or_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_or hMax)

-- ═══ Parte 2 · con S DECIDIBLE ═════════════════════════════════════════════
/-- `derivesSet0_intro_impl` con el `DecidableEq Formula` real (FOL.DecEq), no `propDecidable`. -/
theorem intro_impl' {S : Formula → Prop} {A B : Formula}
    (h : DerivesSet₀ (fun x => Or (S x) (x = A)) B) : DerivesSet₀ S (Formula.impl A B) := by
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

section Dec
variable {S : Formula → Prop} [DecidablePred S]

theorem contains' (hMax : IsMaximalConsistent₀ S) {f : Formula} (h : DerivesSet₀ S f) : S f :=
  if hs : S f then hs else
    absurd (fun hInc => hMax.1 (derivesSet0_elim_impl (intro_impl' hInc) h)) (hMax.2 f hs)

theorem impl_iff' (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.impl A B) ↔ (S A → S B) := by
  refine ⟨fun hI hA => contains' hMax (derivesSet0_elim_impl (derivesSet0_hyp hI) (derivesSet0_hyp hA)),
    fun hFn => ?_⟩
  by_cases hI : S (Formula.impl A B)
  · exact hI
  · exfalso
    apply hMax.2 _ hI
    intro hInc
    have hN : DerivesSet₀ S (neg (Formula.impl A B)) := intro_impl' hInc
    have hA : S A := contains' hMax (derivesSet0_map (fun _ hd => neg_impl_left hd) hN)
    have hnB : DerivesSet₀ S (neg B) := derivesSet0_map (fun _ hd => neg_impl_right hd) hN
    exact hMax.1 (derivesSet0_elim_impl hnB (derivesSet0_hyp (hFn hA)))

theorem complete' (hMax : IsMaximalConsistent₀ S) : IsMemComplete S := fun f =>
  if hs : S f then Or.inl hs else Or.inr ((impl_iff' hMax).mpr (fun h => absurd h hs))

theorem or' (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.or A B) ↔ Or (S A) (S B) := by
  constructor
  · intro hOr
    by_cases hA : S A
    · exact Or.inl hA
    by_cases hB : S B
    · exact Or.inr hB
    exfalso
    apply hMax.2 A hA; intro hIA
    apply hMax.2 B hB; intro hIB
    have hnA := intro_impl' hIA
    have hnB := intro_impl' hIB
    refine hMax.1 (derivesSet0_map2 (fun Γ hd hn => ?_) (derivesSet0_hyp hOr)
      (derivesSet0_map2 (fun Γ h1 h2 => Derives₀.intro_and Γ (neg A) (neg B) h1 h2) hnA hnB))
    refine Derives₀.elim_or Γ A B Formula.bottom hd ?_ ?_
    · refine Derives₀.elim_impl _ A Formula.bottom ?_ (Derives₀.hyp _ _ (List.Mem.head _))
      exact Derives₀.elim_and_l _ (neg A) (neg B)
        (Derives₀.weakening _ _ _ hn (fun x hx => List.Mem.tail _ hx))
    · refine Derives₀.elim_impl _ B Formula.bottom ?_ (Derives₀.hyp _ _ (List.Mem.head _))
      exact Derives₀.elim_and_r _ (neg A) (neg B)
        (Derives₀.weakening _ _ _ hn (fun x hx => List.Mem.tail _ hx))
  · intro hOr
    cases hOr with
    | inl hA =>
      exact contains' hMax
        (derivesSet0_map (fun Γ hd => Derives₀.intro_or_l Γ A B hd) (derivesSet0_hyp hA))
    | inr hB =>
      exact contains' hMax
        (derivesSet0_map (fun Γ hd => Derives₀.intro_or_r Γ A B hd) (derivesSet0_hyp hB))

theorem forall' (hMax : IsMaximalConsistent₀ S) (hHenkin : IsHenkin S) {A : Formula} :
    S (Formula.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    refine contains' hMax ⟨[Formula.forall A], ?_, ?_⟩
    · intro g hg
      cases hg with
      | head => exact hAll
      | tail _ hT => exact absurd hT List.not_mem_nil
    · exact Derives₀.elim_forall _ A t (Derives₀.hyp _ _ (List.Mem.head _))
  · intro hAll
    by_cases hS : S (Formula.forall A)
    · exact hS
    exfalso
    apply hMax.2 _ hS; intro hInc
    have hNegForall := intro_impl' hInc
    have hExNeg : DerivesSet₀ S (Formula.ex (neg A)) :=
      derivesSet0_map (fun Γ hd =>
        Derives₀.elim_impl Γ (neg (Formula.forall A)) (Formula.ex (neg A))
          (Derives₀.forall_not_ex_not Γ A) hd) hNegForall
    obtain ⟨t, ht⟩ := hHenkin (neg A) (contains' hMax hExNeg)
    refine hMax.1 ⟨[neg (substFormula 0 t A), substFormula 0 t A], ?_, ?_⟩
    · intro g hg
      cases hg with
      | head => exact ht
      | tail _ hT =>
        cases hT with
        | head => exact hAll t
        | tail _ hT2 => exact absurd hT2 List.not_mem_nil
    · exact Derives₀.elim_impl _ (substFormula 0 t A) Formula.bottom
        (Derives₀.hyp _ _ (List.Mem.head _))
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

end Dec

end FOL.Esencialidad0.E3

namespace FOL.Esencialidad0.E6

/-
E6 · (d) ¿Es ESENCIAL el choice de skF / skF_spec?
`skF`/`skF_spec`/`eval_skolemAxN` dicen, juntos: TODO modelo admite una expansión de Skolem que
valida `skolemAxN c n A`. Se toma ESE enunciado (con n = 1) como hipótesis y se deriva
  (i)  el axioma de elección ∀∃ → ∃f para cualquier relación en cualquier tipo habitado, y
  (ii) de (i), el tercio excluso (Diaconescu–Goodman–Myhill).
-/


open FOL.Metamath.Semantics
open FOL.Skolem0
open FOL.SkolemN0
open FOL.Eigenvariable

def AR : Formula := Formula.atom ['R'] [Term.var 1, Term.var 0]

theorem AR_fresh : Not (occursFormula ['c'] AR) := by
  show Not (Or False (Or False False))
  intro h
  rcases h with h | h | h <;> exact h

def relOf {α : Type} (r : α → α → Prop) : List α → Prop
  | [a, b] => r a b
  | _ => False

def Mr {α : Type} (a0 : α) (r : α → α → Prop) : Model α := ⟨fun _ _ => a0, fun _ ds => relOf r ds⟩

/-- (i) El ENUNCIADO «todo modelo tiene expansión de Skolem» implica AC para relaciones. -/
theorem skolem_expansion_implies_ac
    (hSk : ∀ (D : Type) (M : Model D) (v : Nat → D) (A : Formula), Not (occursFormula ['c'] A) →
      ∃ F : List D → D, evalFormula (updateFunc M ['c'] F) v (skolemAxN ['c'] 1 A)) :
    ∀ (α : Type) (_ : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x) := by
  intro α a0 r
  obtain ⟨F, hF⟩ := hSk α (Mr a0 r) (fun _ => a0) AR AR_fresh
  refine ⟨fun x => F [x], fun x hx => ?_⟩
  have hY := hF x (by obtain ⟨y, hy⟩ := hx; exact ⟨y, hy⟩)
  rw [eval_substFormula_zero] at hY
  have hc : evalTerm (updateFunc (Mr a0 r) ['c'] F) (shiftEnv (fun _ => a0) x)
      (Term.func ['c'] (vars 1)) = F [x] := by
    show (if (['c'] : List Char) = ['c']
          then F (evalTerms (updateFunc (Mr a0 r) ['c'] F) (shiftEnv (fun _ => a0) x) (vars 1))
          else (Mr a0 r).func ['c']
            (evalTerms (updateFunc (Mr a0 r) ['c'] F) (shiftEnv (fun _ => a0) x) (vars 1))) = F [x]
    rw [ite_eq_left rfl]
    rfl
  rw [hc] at hY
  exact hY

/-- (ii) Diaconescu: AC para relaciones (en la forma de (i)) implica el tercio excluso. -/
theorem ac_implies_em
    (hAC : ∀ (α : Type) (_ : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x)) :
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
example : ∀ (α : Type) (_ : α) (r : α → α → Prop), ∃ f : α → α, ∀ x, (∃ y, r x y) → r x (f x) :=
  skolem_expansion_implies_ac (fun _ M v A hA =>
    ⟨skF M A v (v 0), eval_skolemAxN M ['c'] 1 A v (v 0) hA⟩)

end FOL.Esencialidad0.E6

namespace FOL.Esencialidad0.E7

/-
E7 · (b) El ENUNCIADO de `model_existence_lemma₀` (IsConsistent₀ S → IsSatisfiable S, con S un
predicado de Lean ARBITRARIO) implica el tercio excluso DÉBIL: ∀ P, ¬P ∨ ¬¬P.
Testigo: S_P := {Q ∨ R} ∪ {¬Q | P} ∪ {¬R | ¬P}. Es consistente SIN choice (¬¬(P ∨ ¬P) basta, y
cada caso se refuta con un modelo de un punto de evaluación decidible, vía `sound_stable`).
Q y R son átomos de ARIDAD distinta para no comparar `String`s.
-/


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

def Qf : Formula := Formula.atom ['Q'] []
def Rf : Formula := Formula.atom ['Q'] [Term.var 0]

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

end FOL.Esencialidad0.E7

namespace FOL.Esencialidad0.ExElimFin

open FOL.Metamath.Semantics

/-- El modelo de dos puntos de la refutación de `ex_elim` (en `FOL.Inconsistencia`, privado): `P` sólo vale en
    `true`, y todo término vale `false`. -/
def MB : Model Bool := ⟨fun _ _ => false, fun _ ds => ds = [true]⟩
def vB : Nat → Bool := fun _ => false
def PA : Formula := Formula.atom ['P'] [Term.var 0]

/-- En `MB` la evaluación es DECIDIBLE: el dominio es finito y la relación decidible; por recursión sobre la fórmula. -/
def decEval : (f : Formula) → (v : Nat → Bool) → Decidable (evalFormula MB v f)
  | .bottom, _ => isFalse (fun h => h)
  | .atom _ ts, v => (inferInstance : Decidable (evalTerms MB v ts = [true]))
  | .eq t1 t2, v => (inferInstance : Decidable (evalTerm MB v t1 = evalTerm MB v t2))
  | .impl f1 f2, v =>
      match decEval f1 v, decEval f2 v with
      | _, isTrue h2 => isTrue (fun _ => h2)
      | isTrue h1, isFalse h2 => isFalse (fun h => h2 (h h1))
      | isFalse h1, _ => isTrue (fun h => absurd h h1)
  | .and f1 f2, v =>
      match decEval f1 v, decEval f2 v with
      | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
      | isFalse h1, _ => isFalse (fun h => h1 h.1)
      | _, isFalse h2 => isFalse (fun h => h2 h.2)
  | .or f1 f2, v =>
      match decEval f1 v, decEval f2 v with
      | isTrue h1, _ => isTrue (Or.inl h1)
      | _, isTrue h2 => isTrue (Or.inr h2)
      | isFalse h1, isFalse h2 => isFalse (fun h => h.elim h1 h2)
  | .forall f1, v =>
      match decEval f1 (shiftEnv v true), decEval f1 (shiftEnv v false) with
      | isTrue ht, isTrue hf => isTrue (fun d => match d with | true => ht | false => hf)
      | isFalse ht, _ => isFalse (fun h => ht (h true))
      | _, isFalse hf => isFalse (fun h => hf (h false))
  | .ex f1, v =>
      match decEval f1 (shiftEnv v true), decEval f1 (shiftEnv v false) with
      | isTrue ht, _ => isTrue ⟨true, ht⟩
      | _, isTrue hf => isTrue ⟨false, hf⟩
      | isFalse ht, isFalse hf => isFalse (fun ⟨d, hd⟩ => match d, hd with | true, h => ht h | false, h => hf h)

theorem stable_MB : ∀ (v : Nat → Bool) (f : Formula), Not (Not (evalFormula MB v f)) → evalFormula MB v f :=
  FOL.Esencialidad0.E2.stable_of_dec MB (fun v f => decEval f v)

/-- La solidez que hace falta, sin `Classical.choice`: `Derives` a `Derives₀` (`derives_to_derives0`) y la solidez
    estable en `MB`. -/
theorem sound_MB {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) :
    ∀ v, contextSatisfies MB v Γ → evalFormula MB v f :=
  FOL.Esencialidad0.E2.sound_stable MB stable_MB (FOL.Inconsistencia.derives_to_derives0 h)

/-- 🏁 **`ex_elim` es FALSO, sin `Classical.choice`**: la refutación de `FOL.Inconsistencia.ex_elim_refutable`, con la
    solidez estable en el modelo decidible `MB` en lugar de `derives_soundness`. En `MB`, `∃x P(x)` es verdadera y
    ningún término la testimonia; desde `[∃x P(x)]` no se deriva ningún `P(t)`, y la continuación vale vacuamente
    hacia `⊥`, que `MB` refuta. -/
theorem ex_elim_refutable_fin : Not FOL.Inconsistencia.ExElim := by
  intro hex
  have hΓ : contextSatisfies MB vB [Formula.ex PA] := by
    intro g hg
    cases hg with
    | head => exact ⟨true, rfl⟩
    | tail _ h => exact absurd h List.not_mem_nil
  have hterm : ∀ t : Term, evalTerm MB vB t = false := by
    intro t
    cases t with
    | var n => rfl
    | func f ts => rfl
  have hno : ∀ t : Term, Not ([Formula.ex PA] ⊢ substFormula 0 t PA) := by
    intro t ht
    have h1 : evalTerms MB vB [substTerm 0 t (Term.var 0)] = [true] := sound_MB ht vB hΓ
    have hs : substTerm 0 t (Term.var 0) = t := by
      show (if 0 = 0 then t else if 0 > 0 then Term.var (0 - 1) else Term.var 0) = t
      rw [ite_eq_left rfl]
    rw [hs] at h1
    have h2 : evalTerm MB vB t = true := List.head_eq_of_cons_eq h1
    rw [hterm t] at h2
    exact Bool.false_ne_true h2
  exact sound_MB (hex (Γ := [Formula.ex PA]) (A := PA) (C := Formula.bottom)
    (Derives.hyp _ _ (List.Mem.head _)) (fun t ht => absurd ht (hno t))) vB hΓ

end FOL.Esencialidad0.ExElimFin

#print axioms FOL.Esencialidad0.E1.soundness_stmt_implies_dne
#print axioms FOL.Esencialidad0.E1.lkc_stmt_implies_em
#print axioms FOL.Esencialidad0.E2.sound_stable
#print axioms FOL.Esencialidad0.E2.stable_of_dec
#print axioms FOL.Esencialidad0.E2b.lkc_sound_dec
#print axioms FOL.Esencialidad0.E3.T_consistent
#print axioms FOL.Esencialidad0.E3.SP_max
#print axioms FOL.Esencialidad0.E3.contains_stmt_implies_dne
#print axioms FOL.Esencialidad0.E3.complete_stmt_implies_dne
#print axioms FOL.Esencialidad0.E3.impl_iff_stmt_implies_dne
#print axioms FOL.Esencialidad0.E3.or_stmt_implies_dne
#print axioms FOL.Esencialidad0.E3.intro_impl'
#print axioms FOL.Esencialidad0.E3.contains'
#print axioms FOL.Esencialidad0.E3.impl_iff'
#print axioms FOL.Esencialidad0.E3.complete'
#print axioms FOL.Esencialidad0.E3.or'
#print axioms FOL.Esencialidad0.E3.forall'
#print axioms FOL.Esencialidad0.E6.skolem_expansion_implies_ac
#print axioms FOL.Esencialidad0.E6.ac_implies_em
#print axioms FOL.Esencialidad0.E7.SP_consistent
#print axioms FOL.Esencialidad0.E7.model_existence_stmt_implies_wlem
#print axioms FOL.Esencialidad0.ExElimFin.stable_MB
#print axioms FOL.Esencialidad0.ExElimFin.sound_MB
#print axioms FOL.Esencialidad0.ExElimFin.ex_elim_refutable_fin
