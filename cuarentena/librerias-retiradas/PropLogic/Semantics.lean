/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL
-- @axiom_system: classical
-- @importance: high

import PropLogic.PL

namespace PropLogic.Metamath.Semantics

open PropLogic

-- ============================================================
-- Semántica Proposicional
-- ============================================================

-- Una valuación asigna un valor de verdad a cada variable proposicional.
def Valuation := String → Prop

def evalFormula (v : Valuation) (f : Formula) : Prop :=
  match f with
  | .bottom    => False
  | .atom p    => v p
  | .impl f1 f2 => evalFormula v f1 → evalFormula v f2
  | .and  f1 f2 => evalFormula v f1 ∧ evalFormula v f2
  | .or   f1 f2 => evalFormula v f1 ∨ evalFormula v f2

def contextSatisfies (v : Valuation) (Γ : List Formula) : Prop :=
  ∀ f, f ∈ Γ → evalFormula v f

def satisfies (Γ : List Formula) (f : Formula) : Prop :=
  ∀ (v : Valuation), contextSatisfies v Γ → evalFormula v f

-- ============================================================
-- Corrección de Reglas Locales y Reescritura
-- ============================================================

theorem rule_soundness (v : Valuation) {A B : Formula} (h : LocalRule A B) :
    evalFormula v A ↔ evalFormula v B := by
  cases h with
  | commuteImpl A B C =>
    simp only [evalFormula]
    constructor
    · intro h hB hA; exact h hA hB
    · intro h hA hB; exact h hB hA

theorem replaceAt_soundness (v : Valuation) {f sub sub' : Formula} {p : Pos}
    (hGet : getAt? f p = some sub) (hEq : ∀ w : Valuation, evalFormula w sub ↔ evalFormula w sub') :
    evalFormula v f ↔ evalFormula v (replaceAt f p sub') := by
  induction p generalizing f v with
  | root =>
    simp only [getAt?, Option.some.injEq] at hGet
    subst hGet
    simp only [replaceAt]
    exact hEq v
  | left p ih =>
    match f with
    | .impl f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun h hf1' => h ((ih v hGet).mpr hf1'),
             fun h hf1  => h ((ih v hGet).mp  hf1)⟩
    | .and f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(ih v hGet).mp  h1, h2⟩,
             fun ⟨h1, h2⟩ => ⟨(ih v hGet).mpr h1, h2⟩⟩
    | .or f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun h => h.imp (ih v hGet).mp  id,
             fun h => h.imp (ih v hGet).mpr id⟩
    | .bottom | .atom _ =>
      simp only [getAt?] at hGet; exact absurd hGet (by simp)
  | right p ih =>
    match f with
    | .impl f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun h hf1 => (ih v hGet).mp  (h hf1),
             fun h hf1 => (ih v hGet).mpr (h hf1)⟩
    | .and f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (ih v hGet).mp  h2⟩,
             fun ⟨h1, h2⟩ => ⟨h1, (ih v hGet).mpr h2⟩⟩
    | .or f1 f2 =>
      simp only [getAt?] at hGet
      simp only [replaceAt, evalFormula]
      exact ⟨fun h => h.imp id (ih v hGet).mp,
             fun h => h.imp id (ih v hGet).mpr⟩
    | .bottom | .atom _ =>
      simp only [getAt?] at hGet; exact absurd hGet (by simp)

end PropLogic.Metamath.Semantics
