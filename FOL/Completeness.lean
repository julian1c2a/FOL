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

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) (n : Nat) :
    IsConsistent (LindenbaumStep S n) := by
  induction n with
  | zero => exact hCons
  | succ n ih =>
    unfold LindenbaumStep
    split
    · rename_i h
      exact h
    · exact ih

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  simp only [LindenbaumStep]
  split
  · exact Or.inl h
  · exact h

theorem lindenbaum_step_mono {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : LindenbaumStep S n x) : LindenbaumStep S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact lindenbaum_step_subset _ ih

theorem lindenbaum_limit_bound {S : Formula → Prop} (Γ : List Formula)
    (hΓ : ∀ g ∈ Γ, LindenbaumLimit S g) : ∃ N, ∀ g ∈ Γ, LindenbaumStep S N g := by
  induction Γ with
  | nil =>
    use 0
    intro g hIn
    contradiction
  | cons g Γ' ih =>
    have hg_lim := hΓ g (List.Mem.head _)
    obtain ⟨n_g, hn_g⟩ := hg_lim
    have hΓ'_lim : ∀ g' ∈ Γ', LindenbaumLimit S g' := fun g' hg' => hΓ g' (List.Mem.tail _ hg')
    obtain ⟨N', hN'⟩ := ih hΓ'_lim
    use max n_g N'
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
  use LindenbaumLimit S
  constructor
  · constructor
    · -- Consistencia del límite (Compacidad sintáctica)
      intro hBot
      obtain ⟨Γ, hΓ, hDer⟩ := hBot
      have ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
      have hConsN := lindenbaum_step_consistent hCons N
      apply hConsN
      use Γ
      exact ⟨hN, hDer⟩
    · -- Maximalidad del límite
      intro f hNotLim hConsExt
      obtain ⟨n, hn⟩ := formula_enum_surj f
      have hConsN : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n) := by
        rw [hn]
        intro hBot
        apply hConsExt
        apply DerivesSet_weakening hBot
        intro x hx
        cases hx with
        | inl hStep => exact Or.inl ⟨n, hStep⟩
        | inr hEq => exact Or.inr hEq
      have hStep : LindenbaumStep S (n + 1) f := by
        simp only [LindenbaumStep]
        split
        · exact Or.inr hn.symm
        · contradiction
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
  by_contra hNot
  have hInconsist : (fun x => S x ∨ x = f) ⊢* ⊥ := by
    by_contra hC
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
        by_contra hC
        exact hMax.right A hA hC
      obtain ⟨Γ, hΓ, hDer⟩ := hInconsist
      use Γ
      exact ⟨hΓ, Derives.bot_elim Γ B hDer⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.and A B) ↔ (S A ∧ S B) := by
  constructor
  · intro hAnd
    obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hAnd
    have hA : S ⊢* A := ⟨Γ, hΓ, Derives.elim_and_l Γ A B hDer⟩
    have hB : S ⊢* B := ⟨Γ, hΓ, Derives.elim_and_r Γ A B hDer⟩
    exact ⟨max_cons_contains hMax hA, max_cons_contains hMax hB⟩
  · intro ⟨hA, hB⟩
    obtain ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hA
    obtain ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hB
    apply max_cons_contains hMax
    use Γ1 ++ Γ2
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
    by_contra hNot
    have hNotA : ¬ S A := fun h => hNot (Or.inl h)
    have hNotB : ¬ S B := fun h => hNot (Or.inr h)
    have hInconsistA : (fun x => S x ∨ x = A) ⊢* ⊥ := by by_contra hC; exact hMax.right A hNotA hC
    have hInconsistB : (fun x => S x ∨ x = B) ⊢* ⊥ := by by_contra hC; exact hMax.right B hNotB hC
    obtain ⟨ΓOr, hΓOr, hDerOr⟩ := DerivesSet_hyp hOr
    obtain ⟨ΓA, hΓA, hDerA⟩ := DerivesSet_intro_impl hInconsistA
    obtain ⟨ΓB, hΓB, hDerB⟩ := DerivesSet_intro_impl hInconsistB
    have hBot : S ⊢* ⊥ := by
      use ΓOr ++ ΓA ++ ΓB
      constructor
      · intro g hg
        cases List.mem_append.mp hg with
        | inl h1 => exact hΓOr g h1
        | inr h23 => cases List.mem_append.mp h23 with
          | inl h2 => exact hΓA g h2
          | inr h3 => exact hΓB g h3
      · apply Derives.elim_or (A := A) (B := B)
        · apply Derives.weakening _ _ _ hDerOr
          intro x hx; exact List.mem_append.mpr (Or.inl hx)
        · apply Derives.elim_impl (A := A) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerA
            intro x hx; apply List.Mem.tail; apply List.mem_append.mpr; apply Or.inr; exact List.mem_append.mpr (Or.inl hx)
          · exact Derives.hyp _ _ (List.Mem.head _)
        · apply Derives.elim_impl (A := B) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerB
            intro x hx; apply List.Mem.tail; apply List.mem_append.mpr; apply Or.inr; exact List.mem_append.mpr (Or.inr hx)
          · exact Derives.hyp _ _ (List.Mem.head _)
    exact hMax.left hBot
  · intro hOr
    cases hOr with
    | inl hA =>
      obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hA
      apply max_cons_contains hMax
      use Γ
      exact ⟨hΓ, Derives.intro_or_l Γ A B hDer⟩
    | inr hB =>
      obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hB
      apply max_cons_contains hMax
      use Γ
      exact ⟨hΓ, Derives.intro_or_r Γ A B hDer⟩

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
  match t with
  | .var n => rfl
  | .func f ts =>
    unfold evalTerm
    have ih := evalTerms_canonical S ts
    rw [ih]

theorem evalTerms_canonical (S : Formula → Prop) (ts : List Term) :
    evalTerms (canonicalModel S) canonicalEnv ts = ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
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
  | forall f1 ih => simp only [formulaComplexity, substFormula, ih]
  | ex f1 ih => simp only [formulaComplexity, substFormula, ih]

theorem max_cons_ex {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) {A : Formula} :
    S (.ex A) ↔ ∃ t, S (substFormula 0 t A) := by
  constructor
  · intro hEx
    exact hHenkin A hEx
  · intro ⟨t, ht⟩
    apply max_cons_contains hMax
    use [substFormula 0 t A]
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
    use [.forall A]
    constructor
    · intro g hg
      cases hg with
      | head _ => exact hAll
      | tail _ hTail => contradiction
    · apply Derives.elim_forall
      apply Derives.hyp
      exact List.Mem.head _
  · intro hAll
    by_contra hNotAll
    have hInconsist : (fun x => S x ∨ x = .forall A) ⊢* ⊥ := by
      by_contra hC; exact hMax.right (.forall A) hNotAll hC
    have hNegForall : S ⊢* neg (.forall A) := DerivesSet_intro_impl hInconsist
    have hExNeg_impl : S ⊢* .impl (neg (.forall A)) (.ex (neg A)) := by
      use []
      constructor
      · intro g hg; contradiction
      · exact FOL.Theorems.Quantifiers.forall_not_impl_exists_not
    have hExNeg : S ⊢* .ex (neg A) := DerivesSet_elim_impl hExNeg_impl hNegForall
    have hS_ExNeg : S (.ex (neg A)) := max_cons_contains hMax hExNeg
    obtain ⟨t, ht⟩ := hHenkin (neg A) hS_ExNeg
    have hS_NegA : S (neg (substFormula 0 t A)) := ht
    have hS_A : S (substFormula 0 t A) := hAll t
    have hBot : S ⊢* ⊥ := by
      use [neg (substFormula 0 t A), substFormula 0 t A]
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

theorem truth_lemma_aux {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    (n : Nat) (f : Formula) (hEq : formulaComplexity f = n) :
    evalFormula (canonicalModel S) canonicalEnv f ↔ S f := by
  induction n using Nat.strongInductionOn generalizing f with
  | ind n ih =>
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
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_impl hMax).symm
    | and f1 f2 =>
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_or hMax).symm
    | forall f1 =>
      simp only [evalFormula]
      have h_eq : (∀ d : Term, evalFormula (canonicalModel S) (shiftEnv canonicalEnv d) f1) ↔
                  (∀ d : Term, S (substFormula 0 d f1)) := by
        apply Iff.intro
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hEval := hSubst.symm.mp (h d)
          exact (ih (formulaComplexity f1) (by omega) (substFormula 0 d f1) (by simp)).mp hEval
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hEval := (ih (formulaComplexity f1) (by omega) (substFormula 0 d f1) (by simp)).mpr (h d)
          exact hSubst.mpr hEval
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
          exact ⟨d, (ih (formulaComplexity f1) (by omega) (substFormula 0 d f1) (by simp)).mp hEval⟩
        · intro ⟨d, hd⟩
          have hSubst := eval_substFormula_zero (canonicalModel S) canonicalEnv d f1
          rw [evalTerm_canonical S d] at hSubst
          have hEval := (ih (formulaComplexity f1) (by omega) (substFormula 0 d f1) (by simp)).mpr hd
          exact ⟨d, hSubst.mpr hEval⟩
      rw [h_eq]
      exact (max_cons_ex hMax hHenkin).symm

-- Lema de la Verdad (Truth Lemma): La semántica coincide con la sintaxis en el modelo canónico.
theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) (f : Formula) :
    evalFormula (canonicalModel S) canonicalEnv f ↔ S f :=
  truth_lemma_aux hMax hHenkin (formulaComplexity f) f rfl

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
  obtain ⟨S', hMax, hHenkin, hSub⟩ := henkin_extension_lemma hCons
  use Term, canonicalModel S', canonicalEnv
  intro f hf
  exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)

-- El Teorema de Completitud (Objetivo Final)
theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  by_contra hNotDerive
  let S : Formula → Prop := fun x => x ∈ Γ ∨ x = neg f
  have hCons : IsConsistent S := by
    intro hBot
    have hInconsist : (fun x => (fun y => y ∈ Γ) x ∨ x = neg f) ⊢* ⊥ := hBot
    have hImpl : (fun y => y ∈ Γ) ⊢* .impl (neg f) ⊥ := DerivesSet_intro_impl hInconsist
    obtain ⟨Γ_sub, hΓ_sub, hDer_impl⟩ := hImpl
    have hDNE : Γ_sub ⊢ .impl (neg (neg f)) f := FOL.Theorems.Neg.double_neg_elim
    have hDer_f : Γ_sub ⊢ f := Derives.elim_impl Γ_sub (neg (neg f)) f hDNE hDer_impl
    have hDer_Γ : Γ ⊢ f := Derives.weakening Γ_sub Γ f hDer_f hΓ_sub
    exact hNotDerive hDer_Γ

  obtain ⟨D, M, v, hModel⟩ := model_existence_lemma hCons
  have hSat : contextSatisfies M v Γ := by
    intro g hg
    exact hModel g (Or.inl hg)
  have hEval_f : evalFormula M v f := h D M v hSat
  have hEval_neg_f : evalFormula M v (neg f) := hModel (neg f) (Or.inr rfl)
  exact hEval_neg_f hEval_f

end FOL.Metamath.Completeness

export FOL.Metamath.Completeness (DerivesSet IsConsistent IsMaximalConsistent IsSatisfiable model_existence_lemma completeness)
