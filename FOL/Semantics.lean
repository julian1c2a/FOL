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

@[simp]
theorem eval_liftFormula_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) (f : Formula) :
    evalFormula M (shiftEnv v d) (liftFormula 0 f) ↔ evalFormula M v f := by
  sorry

@[simp]
theorem eval_substFormula_zero {D : Type} (M : Model D) (v : Nat → D) (t : Term) (f : Formula) :
    evalFormula M v (substFormula 0 t f) ↔ evalFormula M (shiftEnv v (evalTerm M v t)) f := by
  sorry

theorem contextSatisfies_lift_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) {Γ : List Formula} :
    contextSatisfies M (shiftEnv v d) (Γ.map (liftFormula 0)) ↔ contextSatisfies M v Γ := by
  sorry

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
