/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL, PropLogic.Semantics, PropLogic.Deduction, PropLogic.Theorems.Neg
-- @axiom_system: classical
-- @importance: high
--
-- Completitud para Lógica Proposicional.
-- Clave: sin cuantificadores, no se necesita extensión de Henkin.
-- El modelo canónico es simplemente la valuación v(p) := S(.atom p).

import PropLogic.PL
import PropLogic.Semantics
import PropLogic.Deduction
import PropLogic.Theorems.Neg

namespace PropLogic.Metamath.Completeness

open PropLogic
open PropLogic.Metamath.Semantics
open Classical

noncomputable local instance : DecidableEq Formula := fun a b => Classical.propDecidable (a = b)

local notation:50 Γ " ⊨ " f => PropLogic.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Derivación desde Conjuntos de Fórmulas (Infinitos)
-- ============================================================

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
  exists [f]
  constructor
  · intro g hg
    cases hg with
    | head _ => exact h
    | tail _ hTail => contradiction
  · apply Derives.hyp
    exact List.Mem.head _

theorem DerivesSet_weakening {S S' : Formula → Prop} {f : Formula}
    (h : S ⊢* f) (hSub : ∀ x, S x → S' x) : S' ⊢* f := by
  have ⟨Γ, hΓ, hDer⟩ := h
  exists Γ
  exact ⟨fun g hg => hSub g (hΓ g hg), hDer⟩

theorem DerivesSet_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => S x ∨ x = A) ⊢* B) : S ⊢* .impl A B := by
  have ⟨Γ, hΓ, hDer⟩ := h
  let Γ' := Γ.filter (fun x => decide (x ≠ A))
  exists Γ'
  constructor
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have h2 := hΓ g h1.1
    have hNeq := of_decide_eq_true h1.2
    cases h2 with
    | inl hS => exact hS
    | inr hEq => exfalso; exact hNeq hEq
  · apply PropLogic.Metamath.Deduction.deduction_theorem
    apply Derives.weakening _ _ _ hDer
    intro x hx
    by_cases heq : x = A
    · subst heq; exact List.Mem.head _
    · apply List.Mem.tail
      apply List.mem_filter.mpr
      exact ⟨hx, decide_eq_true heq⟩

theorem DerivesSet_elim_impl {S : Formula → Prop} {A B : Formula}
    (hImpl : S ⊢* .impl A B) (hA : S ⊢* A) : S ⊢* B := by
  have ⟨Γ1, hΓ1, hDer1⟩ := hImpl
  have ⟨Γ2, hΓ2, hDer2⟩ := hA
  exists Γ1 ++ Γ2
  constructor
  · intro g hg
    cases List.mem_append.mp hg with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · apply Derives.elim_impl (A := A)
    · apply Derives.weakening _ _ _ hDer1
      intro x hx; exact List.mem_append.mpr (Or.inl hx)
    · apply Derives.weakening _ _ _ hDer2
      intro x hx; exact List.mem_append.mpr (Or.inr hx)

-- ============================================================
-- Lema de Lindenbaum
-- ============================================================

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

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) (n : Nat) :
    IsConsistent (LindenbaumStep S n) := by
  induction n with
  | zero => exact hCons
  | succ n ih =>
    simp only [LindenbaumStep]
    by_cases h : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n)
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact ih

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  simp only [LindenbaumStep]
  by_cases hCons : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n)
  · rw [if_pos hCons]; exact Or.inl h
  · rw [if_neg hCons]; exact h

theorem lindenbaum_step_mono {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : LindenbaumStep S n x) : LindenbaumStep S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact lindenbaum_step_subset _ ih

theorem lindenbaum_limit_bound {S : Formula → Prop} (Γ : List Formula)
    (hΓ : ∀ g ∈ Γ, LindenbaumLimit S g) : ∃ N, ∀ g ∈ Γ, LindenbaumStep S N g := by
  induction Γ with
  | nil =>
    exists 0
    intro g hIn
    contradiction
  | cons g Γ' ih =>
    have ⟨n_g, hn_g⟩ := hΓ g (List.Mem.head _)
    have ⟨N', hN'⟩ := ih (fun g' hg' => hΓ g' (List.Mem.tail _ hg'))
    exact ⟨max n_g N', fun g' hg' => by
      cases hg' with
      | head _ => exact lindenbaum_step_mono (by omega) hn_g
      | tail _ hTail => exact lindenbaum_step_mono (by omega) (hN' g' hTail)⟩

theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ (∀ f, S f → S' f) := by
  exists LindenbaumLimit S
  constructor
  · constructor
    · intro hBot
      have ⟨Γ, hΓ, hDer⟩ := hBot
      have ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
      exact (lindenbaum_step_consistent hCons N) ⟨Γ, hN, hDer⟩
    · intro f hNotLim hConsExt
      have ⟨n, hn⟩ := formula_enum_surj f
      have hConsN : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n) := by
        intro hBot
        apply hConsExt
        apply DerivesSet_weakening hBot
        intro x hx
        cases hx with
        | inl hStep => exact Or.inl ⟨n, hStep⟩
        | inr hEq => exact Or.inr (by rw [← hn]; exact hEq)
      have hStep : LindenbaumStep S (n + 1) f := by
        simp only [LindenbaumStep]
        rw [if_pos hConsN]
        exact Or.inr hn.symm
      exact hNotLim ⟨n + 1, hStep⟩
  · intro f hf; exact ⟨0, hf⟩

-- ============================================================
-- Propiedades de Conjuntos Máximamente Consistentes
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent S) : ¬ S ⊥ :=
  fun h => hMax.left (DerivesSet_hyp h)

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent S) {f : Formula}
    (h : S ⊢* f) : S f := by
  apply Classical.byContradiction
  intro hNot
  have hInconsist : (fun x => S x ∨ x = f) ⊢* ⊥ := by
    apply Classical.byContradiction
    intro hC; exact hMax.right f hNot hC
  exact hMax.left (DerivesSet_elim_impl (DerivesSet_intro_impl hInconsist) h)

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.impl A B) ↔ (S A → S B) := by
  constructor
  · intro hImpl hA
    exact max_cons_contains hMax (DerivesSet_elim_impl (DerivesSet_hyp hImpl) (DerivesSet_hyp hA))
  · intro hFn
    apply max_cons_contains hMax
    apply DerivesSet_intro_impl
    by_cases hA : S A
    · apply DerivesSet_weakening (DerivesSet_hyp (hFn hA))
      intro x hx; exact Or.inl hx
    · have hInconsist : (fun x => S x ∨ x = A) ⊢* ⊥ := by
        apply Classical.byContradiction
        intro hC; exact hMax.right A hA hC
      have ⟨Γ, hΓ, hDer⟩ := hInconsist
      exact ⟨Γ, hΓ, Derives.bot_elim Γ B hDer⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.and A B) ↔ (S A ∧ S B) := by
  constructor
  · intro hAnd
    have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hAnd
    exact ⟨max_cons_contains hMax ⟨Γ, hΓ, Derives.elim_and_l Γ A B hDer⟩,
           max_cons_contains hMax ⟨Γ, hΓ, Derives.elim_and_r Γ A B hDer⟩⟩
  · intro ⟨hA, hB⟩
    have ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hA
    have ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hB
    apply max_cons_contains hMax
    exact ⟨Γ1 ++ Γ2, fun g hg => by
        cases List.mem_append.mp hg with
        | inl h1 => exact hΓ1 g h1
        | inr h2 => exact hΓ2 g h2,
      Derives.intro_and _ _ _
        (Derives.weakening _ _ _ hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
        (Derives.weakening _ _ _ hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx)))⟩

theorem max_cons_or {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.or A B) ↔ (S A ∨ S B) := by
  constructor
  · intro hOr
    apply Classical.byContradiction
    intro hNot
    have hNotA : ¬ S A := fun h => hNot (Or.inl h)
    have hNotB : ¬ S B := fun h => hNot (Or.inr h)
    have hInconsistA : (fun x => S x ∨ x = A) ⊢* ⊥ := by
      apply Classical.byContradiction; intro hC; exact hMax.right A hNotA hC
    have hInconsistB : (fun x => S x ∨ x = B) ⊢* ⊥ := by
      apply Classical.byContradiction; intro hC; exact hMax.right B hNotB hC
    have ⟨ΓOr, hΓOr, hDerOr⟩ := DerivesSet_hyp hOr
    have ⟨ΓA, hΓA, hDerA⟩ := DerivesSet_intro_impl hInconsistA
    have ⟨ΓB, hΓB, hDerB⟩ := DerivesSet_intro_impl hInconsistB
    exact hMax.left ⟨ΓOr ++ ΓA ++ ΓB, fun g hg => by
        cases List.mem_append.mp hg with
        | inl h12 =>
          cases List.mem_append.mp h12 with
          | inl h1 => exact hΓOr g h1
          | inr h2 => exact hΓA g h2
        | inr h3 => exact hΓB g h3,
      Derives.elim_or _ _ _ _
        (Derives.weakening _ _ _ hDerOr (fun x hx =>
          List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))))
        (Derives.elim_impl _ _ _
          (Derives.weakening _ _ _ hDerA (fun x hx =>
            List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))))
          (Derives.hyp _ _ (List.Mem.head _)))
        (Derives.elim_impl _ _ _
          (Derives.weakening _ _ _ hDerB (fun x hx =>
            List.Mem.tail _ (List.mem_append.mpr (Or.inr hx))))
          (Derives.hyp _ _ (List.Mem.head _)))⟩
  · intro hOr
    apply max_cons_contains hMax
    cases hOr with
    | inl hA =>
      have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hA
      exact ⟨Γ, hΓ, Derives.intro_or_l Γ A B hDer⟩
    | inr hB =>
      have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hB
      exact ⟨Γ, hΓ, Derives.intro_or_r Γ A B hDer⟩

-- ============================================================
-- Modelo Canónico Proposicional
-- ============================================================

-- La valuación canónica: v(p) := S(.atom p)
-- No se necesita Henkin ya que no hay cuantificadores.
def canonicalValuation (S : Formula → Prop) : Valuation :=
  fun p => S (.atom p)

def formulaComplexity : Formula → Nat
  | .bottom    => 0
  | .atom _    => 0
  | .impl f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .and  f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .or   f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1

theorem truth_lemma_lt {S : Formula → Prop} (hMax : IsMaximalConsistent S)
    (n : Nat) : ∀ f, formulaComplexity f < n →
    (evalFormula (canonicalValuation S) f ↔ S f) := by
  induction n with
  | zero => intro f hLt; contradiction
  | succ n_ih ih =>
    intro f hLt
    cases f with
    | bottom =>
      simp only [evalFormula]
      exact ⟨fun h => absurd h id, max_cons_bot hMax⟩
    | atom p =>
      simp only [evalFormula, canonicalValuation]
    | impl f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_impl hMax).symm
    | and f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_or hMax).symm

-- Lema de la Verdad: la semántica coincide con la sintaxis en el modelo canónico.
theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent S) (f : Formula) :
    evalFormula (canonicalValuation S) f ↔ S f :=
  truth_lemma_lt hMax (formulaComplexity f + 1) f (by omega)

-- ============================================================
-- Existencia de Modelo y Completitud
-- ============================================================

def IsSatisfiable (S : Formula → Prop) : Prop :=
  ∃ (v : Valuation), ∀ f, S f → evalFormula v f

-- En lógica proposicional, un conjunto consistente tiene modelo directamente
-- vía Lindenbaum, sin extensión de Henkin.
theorem model_existence_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    IsSatisfiable S := by
  have ⟨S', hMax, hSub⟩ := lindenbaum_lemma hCons
  exact ⟨canonicalValuation S', fun f hf =>
    (truth_lemma hMax f).mpr (hSub f hf)⟩

theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  apply Classical.byContradiction
  intro hNotDerive
  let S : Formula → Prop := fun x => (x ∈ Γ) ∨ (x = neg f)
  have hCons : IsConsistent S := by
    intro hBot
    have hImpl : (fun y => y ∈ Γ) ⊢* .impl (neg f) ⊥ := DerivesSet_intro_impl hBot
    have ⟨Γ_sub, hΓ_sub, hDer_impl⟩ := hImpl
    have hDNE : Γ_sub ⊢ .impl (neg (neg f)) f := PropLogic.Theorems.Neg.dne
    exact hNotDerive (Derives.weakening Γ_sub Γ f
      (Derives.elim_impl Γ_sub (neg (neg f)) f hDNE hDer_impl) hΓ_sub)
  have ⟨v, hModel⟩ := model_existence_lemma hCons
  have hSat : contextSatisfies v Γ := fun g hg => hModel g (Or.inl hg)
  exact (hModel (neg f) (Or.inr rfl)) (h v hSat)

end PropLogic.Metamath.Completeness

export PropLogic.Metamath.Completeness (
  DerivesSet
  IsConsistent
  IsMaximalConsistent
  IsSatisfiable
  model_existence_lemma
  completeness
)
