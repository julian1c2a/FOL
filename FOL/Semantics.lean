/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL

namespace FOL.Semantics

-- ============================================================
-- Semántica y Modelos (Opción B de la Fase 5)
-- ============================================================

/-- Un modelo de Lógica de Primer Orden (Estructura) -/
structure Model (D : Type) where
  funcInterp : String → List D → D
  predInterp : String → List D → Prop

/-- Un entorno (asignación de variables libres para índices de De Bruijn) -/
def Env (D : Type) := Nat → D

mutual
  /-- Evaluación semántica de términos -/
  def evalTerm {D : Type} (M : Model D) (env : Env D) (t : Term) : D :=
    match t with
    | .var n => env n
    | .func f ts => M.funcInterp f (evalTerms M env ts)

  /-- Evaluación semántica de listas de términos -/
  def evalTerms {D : Type} (M : Model D) (env : Env D) (ts : List Term) : List D :=
    match ts with
    | [] => []
    | t :: ts' => evalTerm M env t :: evalTerms M env ts'
end

/-- Relación de satisfacción (⊨) para fórmulas -/
def satisfies {D : Type} (M : Model D) (env : Env D) (f : Formula) : Prop :=
  match f with
  | .bottom => False
  | .atom p ts => M.predInterp p (evalTerms M env ts)
  | .impl f1 f2 => satisfies M env f1 → satisfies M env f2
  | .and f1 f2 => satisfies M env f1 ∧ satisfies M env f2
  | .or f1 f2 => satisfies M env f1 ∨ satisfies M env f2
  | .forall f1 => ∀ (d : D),
      let new_env : Env D := fun n =>
        match n with
        | 0 => d
        | m + 1 => env m
      satisfies M new_env f1
  | .ex f1 => ∃ (d : D),
      let new_env : Env D := fun n =>
        match n with
        | 0 => d
        | m + 1 => env m
      satisfies M new_env f1

/-- Satisfacción de un contexto Γ (todas las fórmulas en Γ son verdaderas) -/
def satisfiesCtx {D : Type} (M : Model D) (env : Env D) (Γ : List Formula) : Prop :=
  ∀ f, f ∈ Γ → satisfies M env f

/-- Consecuencia Semántica: Γ ⊨ f si en todo modelo, satisfacer Γ implica satisfacer f -/
def semConsequence (Γ : List Formula) (f : Formula) : Prop :=
  ∀ (D : Type) (M : Model D) (env : Env D), satisfiesCtx M env Γ → satisfies M env f

-- Notación semántica amigable (es posible que requiera namespace open)
notation M " , " env " ⊨ " f => satisfies M env f
notation Γ " ⊨ " f => semConsequence Γ f

end FOL.Semantics