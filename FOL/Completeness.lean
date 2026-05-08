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
import FOL.Theorems.Neg
import FOL.Theorems.Quantifiers
import FOL.Theorems.Eq

namespace FOL.Metamath.Completeness

open FOL.Metamath.Semantics
open Classical

noncomputable local instance : DecidableEq Formula := fun a b => Classical.propDecidable (a = b)

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
  · apply FOL.Metamath.Deduction.deduction_theorem
    apply Derives.weakening _ _ _ hDer
    intro x hx
    by_cases heq : x = A
    · subst heq
      exact List.Mem.head _
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

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) (n : Nat) :
    IsConsistent (LindenbaumStep S n) := by
  induction n with
  | zero => exact hCons
  | succ n ih =>
    simp only [LindenbaumStep]
    by_cases h : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n)
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact ih

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  simp only [LindenbaumStep]
  by_cases hCons : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n)
  · rw [if_pos hCons]
    exact Or.inl h
  · rw [if_neg hCons]
    exact h

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
    have hg_lim := hΓ g (List.Mem.head _)
    have ⟨n_g, hn_g⟩ := hg_lim
    have hΓ'_lim : ∀ g' ∈ Γ', LindenbaumLimit S g' := fun g' hg' => hΓ g' (List.Mem.tail _ hg')
    have ⟨N', hN'⟩ := ih hΓ'_lim
    exists max n_g N'
    intro g' hg'
    cases hg' with
    | head _ =>
      have hLe : n_g ≤ max n_g N' := by omega
      exact lindenbaum_step_mono hLe hn_g
    | tail _ hTail =>
      have hLe : N' ≤ max n_g N' := by omega
      exact lindenbaum_step_mono hLe (hN' g' hTail)

-- Todo conjunto consistente puede extenderse a un conjunto máximamente consistente.
theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ (∀ f, S f → S' f) := by
  exists LindenbaumLimit S
  constructor
  · constructor
    · -- Consistencia del límite (Compacidad sintáctica)
      intro hBot
      have ⟨Γ, hΓ, hDer⟩ := hBot
      have ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
      have hConsN := lindenbaum_step_consistent hCons N
      exact hConsN ⟨Γ, hN, hDer⟩
    · -- Maximalidad del límite
      intro f hNotLim hConsExt
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
  · intro f hf
    exact ⟨0, hf⟩

-- ============================================================
-- Propiedades de Conjuntos Máximamente Consistentes
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent S) : ¬ S ⊥ := by
  intro h
  exact hMax.left (DerivesSet_hyp h)

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent S) {f : Formula} (h : S ⊢* f) : S f := by
  apply Classical.byContradiction
  intro hNot
  have hInconsist : (fun x => S x ∨ x = f) ⊢* ⊥ := by
    apply Classical.byContradiction
    intro hC
    exact hMax.right f hNot hC
  have hImpl : S ⊢* .impl f ⊥ := DerivesSet_intro_impl hInconsist
  have hBot : S ⊢* ⊥ := DerivesSet_elim_impl hImpl h
  exact hMax.left hBot

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.impl A B) ↔ (S A → S B) := by
  constructor
  · intro hImpl hA
    exact max_cons_contains hMax (DerivesSet_elim_impl (DerivesSet_hyp hImpl) (DerivesSet_hyp hA))
  · intro hFn
    apply max_cons_contains hMax
    apply DerivesSet_intro_impl
    by_cases hA : S A
    · have hB := hFn hA
      apply DerivesSet_weakening (DerivesSet_hyp hB)
      intro x hx
      exact Or.inl hx
    · have hInconsist : (fun x => S x ∨ x = A) ⊢* ⊥ := by
        apply Classical.byContradiction
        intro hC
        exact hMax.right A hA hC
      have ⟨Γ, hΓ, hDer⟩ := hInconsist
      exists Γ
      exact ⟨hΓ, Derives.bot_elim Γ B hDer⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.and A B) ↔ (S A ∧ S B) := by
  constructor
  · intro hAnd
    have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hAnd
    have hA : S ⊢* A := ⟨Γ, hΓ, Derives.elim_and_l Γ A B hDer⟩
    have hB : S ⊢* B := ⟨Γ, hΓ, Derives.elim_and_r Γ A B hDer⟩
    exact ⟨max_cons_contains hMax hA, max_cons_contains hMax hB⟩
  · intro ⟨hA, hB⟩
    have ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hA
    have ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hB
    apply max_cons_contains hMax
    exists Γ1 ++ Γ2
    constructor
    · intro g hg
      cases List.mem_append.mp hg with
      | inl h1 => exact hΓ1 g h1
      | inr h2 => exact hΓ2 g h2
    · apply Derives.intro_and
      · apply Derives.weakening _ _ _ hDer1
        intro x hx; exact List.mem_append.mpr (Or.inl hx)
      · apply Derives.weakening _ _ _ hDer2
        intro x hx; exact List.mem_append.mpr (Or.inr hx)

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
    have hBot : S ⊢* ⊥ := by
      exists ΓOr ++ ΓA ++ ΓB
      constructor
      · intro g hg
        -- ΓOr ++ ΓA ++ ΓB is (ΓOr ++ ΓA) ++ ΓB (left-associative)
        cases List.mem_append.mp hg with
        | inl h12 =>
          cases List.mem_append.mp h12 with
          | inl h1 => exact hΓOr g h1
          | inr h2 => exact hΓA g h2
        | inr h3 => exact hΓB g h3
      · apply Derives.elim_or (A := A) (B := B)
        · apply Derives.weakening _ _ _ hDerOr
          intro x hx
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
        · apply Derives.elim_impl (A := A) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerA
            intro x hx
            apply List.Mem.tail
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))
          · exact Derives.hyp _ _ (List.Mem.head _)
        · apply Derives.elim_impl (A := B) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerB
            intro x hx
            apply List.Mem.tail
            exact List.mem_append.mpr (Or.inr hx)
          · exact Derives.hyp _ _ (List.Mem.head _)
    exact hMax.left hBot
  · intro hOr
    cases hOr with
    | inl hA =>
      have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hA
      apply max_cons_contains hMax
      exists Γ
      exact ⟨hΓ, Derives.intro_or_l Γ A B hDer⟩
    | inr hB =>
      have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hB
      apply max_cons_contains hMax
      exists Γ
      exact ⟨hΓ, Derives.intro_or_r Γ A B hDer⟩

-- ============================================================
-- Equivalencia Sintáctica y Modelo Cociente
-- ============================================================

def termEqv (S : Formula → Prop) (t1 t2 : Term) : Prop :=
  S (.eq t1 t2)

theorem termEqv_refl {S : Formula → Prop} (hMax : IsMaximalConsistent S) (t : Term) :
    termEqv S t t := by
  apply max_cons_contains hMax
  exists []
  constructor
  · intro g hg; contradiction
  · exact Derives.refl [] t

theorem termEqv_symm {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 : Term}
    (hEq : termEqv S t1 t2) : termEqv S t2 t1 := by
  apply max_cons_contains hMax
  have ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hEq
  exists Γ
  exact ⟨hΓ, derive_eq_symm hDer⟩

theorem termEqv_trans {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 t3 : Term}
    (h12 : termEqv S t1 t2) (h23 : termEqv S t2 t3) : termEqv S t1 t3 := by
  apply max_cons_contains hMax
  have ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp h12
  have ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp h23
  exists Γ1 ++ Γ2
  constructor
  · intro g hg
    cases List.mem_append.mp hg with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · have hDer1' := Derives.weakening Γ1 (Γ1 ++ Γ2) _ hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx))
    have hDer2' := Derives.weakening Γ2 (Γ1 ++ Γ2) _ hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx))
    exact derive_eq_trans hDer1' hDer2'

def termSetoid (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Setoid Term where
  r := termEqv S
  iseqv := {
    refl := termEqv_refl hMax
    symm := termEqv_symm hMax
    trans := termEqv_trans hMax
  }

-- ============================================================
-- Modelo Canónico de Henkin
-- ============================================================

def canonicalModel (S : Formula → Prop) : Model Term where
  func := Term.func
  rel  := fun p ts => S (.atom p ts)

def canonicalEnv : Nat → Term := Term.var

mutual
theorem evalTerm_canonical (S : Formula → Prop) (t : Term) :
    evalTerm (canonicalModel S) canonicalEnv t = t := by
  cases t with
  | var n => rfl
  | func f ts =>
    unfold evalTerm
    have ih := evalTerms_canonical S ts
    rw [ih]; rfl

theorem evalTerms_canonical (S : Formula → Prop) (ts : List Term) :
    evalTerms (canonicalModel S) canonicalEnv ts = ts := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    unfold evalTerms
    have ih1 := evalTerm_canonical S t
    have ih2 := evalTerms_canonical S ts'
    rw [ih1, ih2]
end

-- Un conjunto S tiene la propiedad de Henkin si contiene testigos para sus existenciales.
def IsHenkin (S : Formula → Prop) : Prop :=
  ∀ f, S (.ex f) → ∃ (t : Term), S (substFormula 0 t f)

def formulaComplexity : Formula → Nat
  | .bottom => 0
  | .atom _ _ => 0
  | .eq _ _ => 0
  | .impl f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .forall f1 => formulaComplexity f1 + 1
  | .and f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .or f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .ex f1 => formulaComplexity f1 + 1

@[simp]
theorem complexity_substFormula (v : Nat) (t : Term) (f : Formula) :
    formulaComplexity (substFormula v t f) = formulaComplexity f := by
  induction f generalizing v t with
  | bottom => rfl
  | atom p ts => rfl
  | eq t1 t2 => rfl
  | impl f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | and f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | or f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | «forall» f1 ih => simp only [formulaComplexity, substFormula, ih]
  | ex f1 ih => simp only [formulaComplexity, substFormula, ih]

theorem max_cons_ex {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) {A : Formula} :
    S (.ex A) ↔ ∃ t, S (substFormula 0 t A) := by
  constructor
  · intro hEx
    exact hHenkin A hEx
  · intro ⟨t, ht⟩
    apply max_cons_contains hMax
    exists [substFormula 0 t A]
    constructor
    · intro g hg
      cases hg with
      | head _ => exact ht
      | tail _ hTail => contradiction
    · apply Derives.intro_ex
      apply Derives.hyp
      exact List.Mem.head _

theorem max_cons_forall {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) {A : Formula} :
    S (.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    apply max_cons_contains hMax
    exists [.forall A]
    constructor
    · intro g hg
      cases hg with
      | head _ => exact hAll
      | tail _ hTail => contradiction
    · apply Derives.elim_forall
      apply Derives.hyp
      exact List.Mem.head _
  · intro hAll
    apply Classical.byContradiction
    intro hNotAll
    have hInconsist : (fun x => S x ∨ x = .forall A) ⊢* ⊥ := by
      apply Classical.byContradiction
      intro hC
      exact hMax.right (.forall A) hNotAll hC
    have hNegForall : S ⊢* neg (.forall A) := DerivesSet_intro_impl hInconsist
    have hExNeg_impl : S ⊢* .impl (neg (.forall A)) (.ex (neg A)) := by
      exists []
      constructor
      · intro g hg; contradiction
      · exact FOL.Theorems.Quantifiers.forall_not_impl_exists_not
    have hExNeg : S ⊢* .ex (neg A) := DerivesSet_elim_impl hExNeg_impl hNegForall
    have hS_ExNeg : S (.ex (neg A)) := max_cons_contains hMax hExNeg
    have ⟨t, ht⟩ := hHenkin (neg A) hS_ExNeg
    have hS_NegA : S (neg (substFormula 0 t A)) := ht
    have hS_A : S (substFormula 0 t A) := hAll t
    have hBot : S ⊢* ⊥ := by
      exists [neg (substFormula 0 t A), substFormula 0 t A]
      constructor
      · intro g hg
        cases hg with
        | head _ => exact hS_NegA
        | tail _ hTail =>
          cases hTail with
          | head _ => exact hS_A
          | tail _ hT => contradiction
      · apply Derives.elim_impl (A := substFormula 0 t A) (B := .bottom)
        · apply Derives.hyp; exact List.Mem.head _
        · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    exact hMax.left hBot

theorem truth_lemma_lt {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    (n : Nat) : ∀ f, formulaComplexity f < n → (evalFormula (canonicalModel S) canonicalEnv f ↔ S f) := by
  induction n with
  | zero =>
    intro f hLt
    contradiction
  | succ n_ih ih =>
    intro f hLt
    cases f with
    | bottom =>
      simp only [evalFormula]
      apply Iff.intro
      · intro h; contradiction
      · exact max_cons_bot hMax
    | atom p ts =>
      simp only [evalFormula]
      have hEval := evalTerms_canonical S ts
      rw [hEval]
      rfl
    | eq t1 t2 =>
      sorry -- 🚧 ¡Alerta Matemática! Aquí falla el modelo de Henkin básico. Necesitamos el Modelo Cociente.
    | impl f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have ih1 := ih f1 hLt1
      have ih2 := ih f2 hLt2
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_impl hMax).symm
    | and f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have ih1 := ih f1 hLt1
      have ih2 := ih f2 hLt2
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have ih1 := ih f1 hLt1
      have ih2 := ih f2 hLt2
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_or hMax).symm
    | «forall» f1 =>
      simp only [evalFormula]
      have h_eq : (∀ d : Term, evalFormula (canonicalModel S) (shiftEnv canonicalEnv d) f1) ↔
                  (∀ d : Term, S (substFormula 0 d f1)) := by
        apply Iff.intro
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hEval := hSubst.symm.mp (h d)
          have hLt_f1 : formulaComplexity (substFormula 0 d f1) < n_ih := by
            rw [complexity_substFormula]
            simp only [formulaComplexity] at hLt
            omega
          exact (ih (substFormula 0 d f1) hLt_f1).mp hEval
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hLt_f1 : formulaComplexity (substFormula 0 d f1) < n_ih := by
            rw [complexity_substFormula]
            simp only [formulaComplexity] at hLt
            omega
          have hEval := (ih (substFormula 0 d f1) hLt_f1).mpr (h d)
          exact hSubst.mp hEval
      rw [h_eq]
      exact (max_cons_forall hMax hHenkin).symm
    | ex f1 =>
      simp only [evalFormula]
      have h_eq : (∃ d : Term, evalFormula (canonicalModel S) (shiftEnv canonicalEnv d) f1) ↔
                  (∃ d : Term, S (substFormula 0 d f1)) := by
        apply Iff.intro
        · intro ⟨d, hd⟩
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hEval := hSubst.symm.mp hd
          have hLt_f1 : formulaComplexity (substFormula 0 d f1) < n_ih := by
            rw [complexity_substFormula]
            simp only [formulaComplexity] at hLt
            omega
          exact ⟨d, (ih (substFormula 0 d f1) hLt_f1).mp hEval⟩
        · intro ⟨d, hd⟩
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hLt_f1 : formulaComplexity (substFormula 0 d f1) < n_ih := by
            rw [complexity_substFormula]
            simp only [formulaComplexity] at hLt
            omega
          have hEval := (ih (substFormula 0 d f1) hLt_f1).mpr hd
          exact ⟨d, hSubst.mp hEval⟩
      rw [h_eq]
      exact (max_cons_ex hMax hHenkin).symm

-- Lema de la Verdad (Truth Lemma): La semántica coincide con la sintaxis en el modelo canónico.
theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) (f : Formula) :
    evalFormula (canonicalModel S) canonicalEnv f ↔ S f :=
  truth_lemma_lt hMax hHenkin (formulaComplexity f + 1) f (by omega)

-- ============================================================
-- Extensión de Henkin
-- ============================================================

-- Todo conjunto consistente puede extenderse a uno máximamente consistente
-- que además contenga testigos para sus fórmulas existenciales.
-- (Su demostración constructiva requiere expandir el lenguaje con constantes).
axiom henkin_extension_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ IsHenkin S' ∧ (∀ f, S f → S' f)

def IsSatisfiable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D), ∀ f, S f → evalFormula M v f

theorem model_existence_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    IsSatisfiable S := by
  have ⟨S', hMax, hHenkin, hSub⟩ := henkin_extension_lemma hCons
  exact ⟨Term, canonicalModel S', canonicalEnv, by
    intro f hf
    exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)⟩

-- El Teorema de Completitud (Objetivo Final)
theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  apply Classical.byContradiction
  intro hNotDerive
  let S : Formula → Prop := fun x => (x ∈ Γ) ∨ (x = (neg f))
  have hCons : IsConsistent S := by
    intro hBot
    have hInconsist : (fun x => (fun y => y ∈ Γ) x ∨ x = neg f) ⊢* ⊥ := hBot
    have hImpl : (fun y => y ∈ Γ) ⊢* .impl (neg f) ⊥ := DerivesSet_intro_impl hInconsist
    have ⟨Γ_sub, hΓ_sub, hDer_impl⟩ := hImpl
    have hDNE : Γ_sub ⊢ .impl (neg (neg f)) f := FOL.Theorems.Neg.dne
    have hDer_f : Γ_sub ⊢ f := Derives.elim_impl Γ_sub (neg (neg f)) f hDNE hDer_impl
    have hDer_Γ : Γ ⊢ f := Derives.weakening Γ_sub Γ f hDer_f hΓ_sub
    exact hNotDerive hDer_Γ

  have ⟨D, M, v, hModel⟩ := model_existence_lemma hCons
  have hSat : contextSatisfies M v Γ := by
    intro g hg
    exact hModel g (Or.inl hg)
  have hEval_f : evalFormula M v f := h D M v hSat
  have hEval_neg_f : evalFormula M v (neg f) := hModel (neg f) (Or.inr rfl)
  exact hEval_neg_f hEval_f

end FOL.Metamath.Completeness

export FOL.Metamath.Completeness (
  DerivesSet
  IsConsistent
  IsMaximalConsistent
  IsSatisfiable
  model_existence_lemma
  completeness
)
