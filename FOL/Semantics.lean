/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: classical
-- @importance: high

import FOL.FOL

namespace FOL.Metamath.Semantics

-- ============================================================
-- Fase 5: Semántica y Modelos
-- ============================================================

structure Model (D : Type) where
  func : String → List D → D
  rel  : String → List D → Prop

mutual
def evalTerm {D : Type} (M : Model D) (v : Nat → D) (t : Term) : D :=
  match t with
  | .var n => v n
  | .func f ts => M.func f (evalTerms M v ts)

def evalTerms {D : Type} (M : Model D) (v : Nat → D) (ts : List Term) : List D :=
  match ts with
  | [] => []
  | t :: ts' => evalTerm M v t :: evalTerms M v ts'
end

def shiftEnv {D : Type} (v : Nat → D) (d : D) : Nat → D
  | 0 => d
  | n + 1 => v n

def updateEnv {D : Type} (c : Nat) (v : Nat → D) (d : D) : Nat → D :=
  fun n =>
    if n < c then v n
    else if n = c then d
    else v (n - 1)

@[simp]
theorem updateEnv_zero {D : Type} (v : Nat → D) (d : D) (n : Nat) :
    updateEnv 0 v d n = shiftEnv v d n := by
  cases n <;> simp [updateEnv, shiftEnv]

def evalFormula {D : Type} (M : Model D) (v : Nat → D) (f : Formula) : Prop :=
  match f with
  | .bottom => False
  | .atom p ts => M.rel p (evalTerms M v ts)
  | .impl f1 f2 => evalFormula M v f1 → evalFormula M v f2
  | .forall f1 => ∀ (d : D), evalFormula M (shiftEnv v d) f1
  | .and f1 f2 => evalFormula M v f1 ∧ evalFormula M v f2
  | .or f1 f2 => evalFormula M v f1 ∨ evalFormula M v f2
  | .ex f1 => ∃ (d : D), evalFormula M (shiftEnv v d) f1

def contextSatisfies {D : Type} (M : Model D) (v : Nat → D) (Γ : List Formula) : Prop :=
  ∀ f, f ∈ Γ → evalFormula M v f

def satisfies (Γ : List Formula) (f : Formula) : Prop :=
  ∀ (D : Type) (M : Model D) (v : Nat → D), contextSatisfies M v Γ → evalFormula M v f

-- ============================================================
-- Lemas de Sustitución Semántica (Lifting y Sustitución)
-- ============================================================

-- 1. Lemas generalizados para Términos (Profundidad 'c')

mutual
theorem eval_liftTerm_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (t : Term) :
    evalTerm M (updateEnv c v d) (liftTerm c t) = evalTerm M v t := by
  match t with
  | .var n =>
    unfold liftTerm
    by_cases h : n < c
    · simp [h, evalTerm, updateEnv]
    · simp [h, evalTerm, updateEnv]
      have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      simp [h1, h2]
  | .func f ts =>
    unfold liftTerm evalTerm
    have ih := eval_liftTerms_ext M v d c ts
    rw [ih]

theorem eval_liftTerms_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (ts : List Term) :
    evalTerms M (updateEnv c v d) (liftTerms c ts) = evalTerms M v ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold liftTerms evalTerms
    have ih1 := eval_liftTerm_ext M v d c t
    have ih2 := eval_liftTerms_ext M v d c ts'
    rw [ih1, ih2]
end

mutual
theorem eval_substTerm_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (t : Term) :
    evalTerm M v (substTerm c s t) = evalTerm M (updateEnv c v (evalTerm M v s)) t := by
  match t with
  | .var n =>
    unfold substTerm
    by_cases h1 : n = c
    · simp [h1, evalTerm, updateEnv]
    · by_cases h2 : c < n
      · have h_lt : ¬(n < c) := by omega
        have h_eq : ¬(n = c) := by omega
        simp [h_lt, h_eq, h2, evalTerm, updateEnv]
      · have h3 : n < c := by omega
        have hn_lt : ¬(c < n) := h2
        simp [h1, h3, hn_lt, evalTerm, updateEnv]
  | .func f ts =>
    unfold substTerm evalTerm
    have ih := eval_substTerms_ext M v s c ts
    rw [ih]

theorem eval_substTerms_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (ts : List Term) :
    evalTerms M v (substTerms c s ts) = evalTerms M (updateEnv c v (evalTerm M v s)) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold substTerms evalTerms
    have ih1 := eval_substTerm_ext M v s c t
    have ih2 := eval_substTerms_ext M v s c ts'
    rw [ih1, ih2]
end

-- 2. Lemas generalizados para Fórmulas (Firmas)

theorem shift_updateEnv_comm {D : Type} (c : Nat) (v : Nat → D) (d d' : D) :
    shiftEnv (updateEnv c v d) d' = updateEnv (c + 1) (shiftEnv v d') d := by
  funext n
  cases n
  · rfl
  · rename_i n
    dsimp [shiftEnv, updateEnv]
    by_cases h1 : n < c
    · have h2 : n + 1 < c + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : n = c
      · have h3 : n + 1 = c + 1 := by omega
        simp [h2]
      · have h3 : ¬(n + 1 < c + 1) := by omega
        simp [h1, h2, h3]
        cases n with
        | zero => omega
        | succ m => rfl

theorem eval_liftFormula_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (f : Formula) :
    evalFormula M (updateEnv c v d) (liftFormula c f) ↔ evalFormula M v f := by
  induction f generalizing v c
  case bottom => rfl
  case atom p ts =>
    unfold liftFormula evalFormula
    rw [eval_liftTerms_ext]
  case impl f1 f2 ih1 ih2 =>
    unfold liftFormula evalFormula
    rw [ih1, ih2]
  case and f1 f2 ih1 ih2 =>
    unfold liftFormula evalFormula
    rw [ih1, ih2]
  case or f1 f2 ih1 ih2 =>
    unfold liftFormula evalFormula
    rw [ih1, ih2]
  case «forall» f1 ih =>
    unfold liftFormula evalFormula
    apply forall_congr'
    intro d'
    rw [shift_updateEnv_comm, ih]
  case ex f1 ih =>
    unfold liftFormula evalFormula
    apply exists_congr
    intro d'
    rw [shift_updateEnv_comm, ih]

theorem shift_updateEnv_subst_comm {D : Type} (M : Model D) (c : Nat) (v : Nat → D) (t : Term) (d' : D) :
    shiftEnv (updateEnv c v (evalTerm M v t)) d' = updateEnv (c + 1) (shiftEnv v d') (evalTerm M (shiftEnv v d') (liftTerm 0 t)) := by
  have h : evalTerm M (shiftEnv v d') (liftTerm 0 t) = evalTerm M v t := by
    have h_shift : shiftEnv v d' = updateEnv 0 v d' := by
      funext n
      cases n <;> rfl
    rw [h_shift]
    rw [eval_liftTerm_ext]
  rw [h]
  exact shift_updateEnv_comm c v (evalTerm M v t) d'

theorem eval_substFormula_ext {D : Type} (M : Model D) (v : Nat → D) (t : Term) (c : Nat) (f : Formula) :
    evalFormula M v (substFormula c t f) ↔ evalFormula M (updateEnv c v (evalTerm M v t)) f := by
  induction f generalizing v c t
  case bottom => rfl
  case atom p ts =>
    unfold substFormula evalFormula
    rw [eval_substTerms_ext]
  case impl f1 f2 ih1 ih2 =>
    unfold substFormula evalFormula
    rw [ih1, ih2]
  case and f1 f2 ih1 ih2 =>
    unfold substFormula evalFormula
    rw [ih1, ih2]
  case or f1 f2 ih1 ih2 =>
    unfold substFormula evalFormula
    rw [ih1, ih2]
  case «forall» f1 ih =>
    unfold substFormula evalFormula
    apply forall_congr'
    intro d'
    rw [ih]
    rw [← shift_updateEnv_subst_comm]
  case ex f1 ih =>
    unfold substFormula evalFormula
    apply exists_congr
    intro d'
    rw [ih]
    rw [← shift_updateEnv_subst_comm]

@[simp]
theorem eval_liftFormula_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) (f : Formula) :
    evalFormula M (shiftEnv v d) (liftFormula 0 f) ↔ evalFormula M v f := by
  have h := eval_liftFormula_ext M v d 0 f
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [heq] at h
  exact h

@[simp]
theorem eval_substFormula_zero {D : Type} (M : Model D) (v : Nat → D) (t : Term) (f : Formula) :
    evalFormula M v (substFormula 0 t f) ↔ evalFormula M (shiftEnv v (evalTerm M v t)) f := by
  have h := eval_substFormula_ext M v t 0 f
  have heq : updateEnv 0 v (evalTerm M v t) = shiftEnv v (evalTerm M v t) := by
    funext n; exact updateEnv_zero v (evalTerm M v t) n
  rw [heq] at h
  exact h

theorem contextSatisfies_lift_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) {Γ : List Formula} :
    contextSatisfies M (shiftEnv v d) (Γ.map (liftFormula 0)) ↔ contextSatisfies M v Γ := by
  unfold contextSatisfies
  apply Iff.intro
  · intro h f hf
    have h1 := h (liftFormula 0 f) (by simp only [List.mem_map]; exact ⟨f, hf, rfl⟩)
    rw [eval_liftFormula_zero] at h1
    exact h1
  · intro h f' hf'
    simp only [List.mem_map] at hf'
    rcases hf' with ⟨f, hf, hEq⟩
    rw [← hEq]
    rw [eval_liftFormula_zero]
    exact h f hf

-- ============================================================
-- Lemas de Corrección de Reescritura Local
-- ============================================================

theorem rule_soundness {D : Type} (M : Model D) (v : Nat → D) {A B : Formula} (h : LocalRule A B) :
    evalFormula M v A ↔ evalFormula M v B := by
  sorry

theorem replaceAt_soundness {D : Type} (M : Model D) (v : Nat → D) {f sub sub' : Formula} {p : Pos}
    (hGet : getAt? f p = some sub) (hEq : evalFormula M v sub ↔ evalFormula M v sub') :
    evalFormula M v f ↔ evalFormula M v (replaceAt f p sub') := by
  sorry

end FOL.Metamath.Semantics
