/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Semantics
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Semantics
import FOL.Deduction

namespace FOL.Metamath.Completeness

open FOL.Metamath.Semantics
open Classical

local instance : DecidableEq Formula := Classical.decEq

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Fase 5: Teorema de Completitud (Completeness)
-- ============================================================

-- Para abordar la completitud (construcción de Henkin), necesitamos extender
-- las derivaciones desde contextos finitos (List) a conjuntos arbitrarios (Formula → Prop),
-- ya que un conjunto máximamente consistente es infinito.

def DerivesSet (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ (Γ : List Formula), (∀ g, g ∈ Γ → S g) ∧ (Γ ⊢ f)

local notation:50 S " ⊢* " f => DerivesSet S f

def IsConsistent (S : Formula → Prop) : Prop :=
  ¬ (S ⊢* ⊥)

def IsMaximalConsistent (S : Formula → Prop) : Prop :=
  IsConsistent S ∧ ∀ f, ¬ S f → ¬ IsConsistent (fun x => S x ∨ x = f)

-- ============================================================
-- Propiedades Estructurales de DerivesSet
-- ============================================================

theorem DerivesSet_hyp {S : Formula → Prop} {f : Formula} (h : S f) : S ⊢* f := by
  use [f]
  constructor
  · intro g hg
    cases hg with
    | head _ => exact h
    | tail _ hTail => contradiction
  · apply Derives.hyp
    exact List.Mem.head _

theorem DerivesSet_weakening {S S' : Formula → Prop} {f : Formula}
    (h : S ⊢* f) (hSub : ∀ x, S x → S' x) : S' ⊢* f := by
  obtain ⟨Γ, hΓ, hDer⟩ := h
  use Γ
  exact ⟨fun g hg => hSub g (hΓ g hg), hDer⟩

theorem DerivesSet_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => S x ∨ x = A) ⊢* B) : S ⊢* .impl A B := by
  obtain ⟨Γ, hΓ, hDer⟩ := h
  let Γ' := Γ.filter (fun x => x ≠ A)
  use Γ'
  constructor
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have h2 := hΓ g h1.1
    cases h2 with
    | inl hS => exact hS
    | inr hEq => exfalso; exact h1.2 hEq
  · apply FOL.Metamath.Deduction.deduction_theorem
    apply Derives.weakening _ _ _ hDer
    intro x hx
    by_cases heq : x = A
    · subst heq
      exact List.Mem.head _
    · apply List.Mem.tail
      apply List.mem_filter.mpr
      exact ⟨hx, heq⟩

theorem DerivesSet_elim_impl {S : Formula → Prop} {A B : Formula}
    (hImpl : S ⊢* .impl A B) (hA : S ⊢* A) : S ⊢* B := by
  obtain ⟨Γ1, hΓ1, hDer1⟩ := hImpl
  obtain ⟨Γ2, hΓ2, hDer2⟩ := hA
  use Γ1 ++ Γ2
  constructor
  · intro g hg
    have h_or := List.mem_append.mp hg
    cases h_or with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · apply Derives.elim_impl (A := A)
    · apply Derives.weakening _ _ _ hDer1
      intro x hx
      apply List.mem_append.mpr
      exact Or.inl hx
    · apply Derives.weakening _ _ _ hDer2
      intro x hx
      apply List.mem_append.mpr
      exact Or.inr hx

-- ============================================================
-- Lema de Lindenbaum
-- ============================================================

-- Asumimos la enumerabilidad de las fórmulas
axiom formula_enum : Nat → Formula
axiom formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f

noncomputable def LindenbaumStep (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 =>
    let S_n := LindenbaumStep S n
    let f_n := formula_enum n
    if IsConsistent (fun x => S_n x ∨ x = f_n) then
      fun x => S_n x ∨ x = f_n
    else
      S_n

def LindenbaumLimit (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ n, LindenbaumStep S n f

lemma lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) (n : Nat) :
    IsConsistent (LindenbaumStep S n) := by
  induction n with
  | zero => exact hCons
  | succ n ih =>
    unfold LindenbaumStep
    split
    · rename_i h
      exact h
    · exact ih

-- Todo conjunto consistente puede extenderse a un conjunto máximamente consistente.
theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ (∀ f, S f → S' f) := by
  use LindenbaumLimit S
  constructor
  · constructor
    · -- Consistencia del límite (requiere lema de compacidad sintáctica)
      sorry
    · -- Maximalidad del límite
      intro f hNotLim hConsExt
      obtain ⟨n, hn⟩ := formula_enum_surj f
      -- Si S_∞ ∪ {f} fuera consistente, en el paso n+1 la fórmula se habría añadido
      -- lo que entra en contradicción con hNotLim.
      sorry
  · intro f hf
    exact ⟨0, hf⟩

-- El Teorema de Completitud (Objetivo Final)
theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  sorry

end FOL.Metamath.Completeness

export FOL.Metamath.Completeness (DerivesSet IsConsistent IsMaximalConsistent completeness)
