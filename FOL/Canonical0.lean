/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Lindenbaum0, FOL.Eq0, FOL.Semantics
-- @axiom_system: classical
-- @importance: high

import FOL.Lindenbaum0
import FOL.Eq0
import FOL.Semantics
import FOL.Soundness0
import FOL.Complexity

/-!
# `FOL.Canonical0` — **el modelo canónico**, el lema de la verdad y la **COMPLETITUD**

El último tramo de `doc/PLAN-COMPLETITUD-FINITISTA.md` §6, vía W. Con él:

    completeness₀ : Γ ⊨ f → Γ ⊢₀ f

y, junto con `derives0_soundness` (ADR‑034), **`derives0_complete_iff : Γ ⊢₀ f ↔ Γ ⊨ f`**.

⭐⭐ Es la primera vez que este proyecto tiene **las dos direcciones** sobre un mismo cálculo de
FOL⁼. ⛔ Recuérdese que sobre `Derives` **no puede haberlas**: su solidez es FALSA
(`FOL/Inconsistencia.lean`) y `axioms ⊢` es sintácticamente completo (M‑10).

## El recorrido

1. **§1** — lo que falta de la familia `max_cons_*`: `impl` en forma de `↔`, `and`, `neg`, `or`, y
   `max_cons_complete`: el maximal es completo POR PERTENENCIA (`IsMemComplete`).
2. **§2** — la **equivalencia sintáctica** `t ≈ u :⇔ S (t ≐ u)` y su `Setoid`. Aquí pagan
   `derives0_eq_symm` y `derives0_eq_trans` (`FOL.Eq0`).
3. **§3** — `PointwiseEqv` y las dos **congruencias**, que es lo que hace que el cociente esté
   bien definido. ⭐ Se levantan de `Derives₀` a `⊢₀*` con `derivesSet0_map`/`map2`: *la regla
   viaja con su contexto finito.*
4. **§4** — el **modelo canónico**: el dominio es `Term / ≈`, `func` es la aplicación de símbolos
   y `rel` es la pertenencia a `S`. Más `evalTerm_canonical`: *evaluar un término en el modelo
   canónico es su propia clase.*
5. **§5** — `max_cons_ex` y `max_cons_forall`. ⭐ Aquí es donde paga `IsHenkin`, y **sólo aquí**.
6. **§6** — **`truth_lemma`**: la semántica coincide con la sintaxis. Inducción por
   **complejidad**, no por estructura, porque el caso `∀` pasa por `substFormula` —y por eso hace
   falta `complexity_substFormula`: *sustituir no cambia la complejidad*.
7. **§7** — ⭐ **el renombrado es semánticamente transparente** (`pullback`). Es la pieza que el
   ensamblaje necesita y que no estaba: `henkin_completion` entrega un modelo de `shiftTheory S`,
   no de `S`. Se reinterpretan los símbolos, y ya.
8. **§8** — `model_existence_lemma₀` y **`completeness₀`**.

## ⛔ Dónde está la no‑finitud, otra vez

**No aquí.** Todo este módulo es constructivo salvo el uso de `Classical.choose` en `quotientOut`
y el tercio excluso (`byContradiction`, `by_cases`, `em`, `byCases`). La no‑finitud del teorema está **una capa más abajo**, en el
`if IsConsistent₀ (Sₙ ∪ {φₙ})` de `FOL.Lindenbaum0` (Π⁰₁) — ADR‑040 §2.

⇒ El entregable de la vía W es, como el plan decía, **`completeness₀` con footprint
`[propext, Classical.choice, Quot.sound]`, cero axiomas del proyecto, y la nota de reducción al
lado**: ese `Classical.choice` es el WKL; la completitud para lenguajes numerables es **≡ WKL₀**
sobre RCA₀ (Simpson IV.3.3), y WKL₀ es **Π⁰₂‑conservativo sobre PRA** (Friedman).

🔑 **Un `Classical.choice` explicado vale más que un `Classical.choice` escondido.**
-/

namespace FOL.Canonical0

open FOL.Metamath.Semantics
open FOL.Henkin0
open FOL.Fresh0
open FOL.Rename
open FOL.Lindenbaum0
open FOL.Eq0
open FOL.Complexity
open Classical

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f
local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- §1 · Lo que falta de la familia `max_cons_*`
-- ============================================================

/-- Eleva una regla de `Derives₀` a `⊢₀*`: **el contexto finito viaja con ella**. -/
theorem derivesSet0_map {S : Formula → Prop} {A B : Formula}
    (rule : ∀ Γ, (Γ ⊢₀ A) → (Γ ⊢₀ B)) (h : S ⊢₀* A) : S ⊢₀* B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  exact ⟨Γ, hΓ, rule Γ hD⟩

/-- Igual con dos premisas: los dos contextos finitos se **concatenan**. -/
theorem derivesSet0_map2 {S : Formula → Prop} {A B C : Formula}
    (rule : ∀ Γ, (Γ ⊢₀ A) → (Γ ⊢₀ B) → (Γ ⊢₀ C)) (hA : S ⊢₀* A) (hB : S ⊢₀* B) : S ⊢₀* C := by
  obtain ⟨Γ1, hΓ1, hD1⟩ := hA
  obtain ⟨Γ2, hΓ2, hD2⟩ := hB
  refine ⟨Γ1 ++ Γ2, fun g hg => (List.mem_append.mp hg).elim (hΓ1 g) (hΓ2 g), ?_⟩
  exact rule _ (Derives₀.weakening _ _ _ hD1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
               (Derives₀.weakening _ _ _ hD2 (fun x hx => List.mem_append.mpr (Or.inr hx)))

theorem max_cons_impl_iff {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.impl A B) ↔ (S A → S B) := by
  refine ⟨fun hI hA => max_cons_impl hMax hI hA, fun hFn => ?_⟩
  refine max_cons_contains hMax (derivesSet0_intro_impl ?_)
  by_cases hA : S A
  · exact derivesSet0_weakening (derivesSet0_hyp (hFn hA)) (fun x hx => Or.inl hx)
  · have hInc : (fun x => Or (S x) (x = A)) ⊢₀* Formula.bottom :=
      Classical.byContradiction (fun hC => hMax.2 A hA hC)
    obtain ⟨Γ, hΓ, hD⟩ := hInc
    exact ⟨Γ, hΓ, Derives₀.bot_elim Γ B hD⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.and A B) ↔ And (S A) (S B) := by
  constructor
  · intro hAnd
    exact ⟨max_cons_contains hMax
             (derivesSet0_map (fun Γ hd => Derives₀.elim_and_l Γ A B hd) (derivesSet0_hyp hAnd)),
           max_cons_contains hMax
             (derivesSet0_map (fun Γ hd => Derives₀.elim_and_r Γ A B hd) (derivesSet0_hyp hAnd))⟩
  · intro h
    exact max_cons_contains hMax
      (derivesSet0_map2 (fun Γ h1 h2 => Derives₀.intro_and Γ A B h1 h2)
        (derivesSet0_hyp h.1) (derivesSet0_hyp h.2))

/-- ⭐ **La negación, en un maximal consistente, es la ausencia.** Falta en la familia `max_cons_*`,
y es la única conectiva que faltaba: `neg f` es `f ⇒ ⊥` por definición (`FOL/FOL.lean`), así que
sale de `max_cons_impl_iff` y `max_cons_bot` sin más. -/
theorem max_cons_neg {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula} :
    S (neg f) ↔ Not (S f) :=
  ⟨fun hN hf => max_cons_bot hMax ((max_cons_impl_iff hMax).mp hN hf),
   fun hNf => (max_cons_impl_iff hMax).mpr (fun hf => absurd hf hNf)⟩

/-- **Completo POR PERTENENCIA**: para cada fórmula `f`, **abiertas incluidas**, `S` contiene `f`
o contiene `neg f`. Es lo que `max_cons_complete` prueba de todo maximal consistente.

⛔ **NO es la «teoría completa»** de la teoría de modelos, que va por DERIVABILIDAD y sólo sobre
SENTENCIAS (`T ⊢ φ` o `T ⊢ ¬φ` para cada `φ` cerrada). Este árbol no tiene predicado de
sentencia, y el nombre deja libre el canónico para esa noción. Tampoco es
`TheoryFramework.IsSyntacticallyComplete`, que va por derivabilidad sobre todas las fórmulas.

La pertenencia no ve las consecuencias: un conjunto de axiomas no cerrado por derivación no la
cumple aunque su teoría decida cada sentencia (ningún conjunto FINITO la cumple: hay infinitas
fórmulas). Y no es una completitud nueva: sobre un conjunto consistente equivale a ser maximal
(si `f ∉ S`, entonces `neg f ∈ S` y `S ∪ {f} ⊢₀* ⊥`; argumento de libro, ese recíproco no se
enuncia aquí). Sólo cambia la forma: `IsMaximalConsistent₀` (`Lindenbaum0.lean`) se define por
NO‑AMPLIABILIDAD. -/
def IsMemComplete (S : Formula → Prop) : Prop :=
  ∀ f, Or (S f) (S (neg f))

/-- ⭐ **Todo maximal consistente es completo POR PERTENENCIA** (`IsMemComplete`; ⛔ no es
la «teoría completa» sobre sentencias). ⚠️ Usa el tercio excluido del METANIVEL
(`Classical.em` sobre `S f`), no el del cálculo: `S` es un predicado de Lean arbitrario. -/
theorem max_cons_complete {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) :
    IsMemComplete S := fun f =>
  (Classical.em (S f)).elim Or.inl (fun h => Or.inr ((max_cons_neg hMax).mpr h))

theorem max_cons_or {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.or A B) ↔ Or (S A) (S B) := by
  constructor
  · intro hOr
    refine Classical.byContradiction (fun hNot => ?_)
    have hNotA : Not (S A) := fun h => hNot (Or.inl h)
    have hNotB : Not (S B) := fun h => hNot (Or.inr h)
    have hIA : (fun x => Or (S x) (x = A)) ⊢₀* Formula.bottom :=
      Classical.byContradiction (fun hC => hMax.2 A hNotA hC)
    have hIB : (fun x => Or (S x) (x = B)) ⊢₀* Formula.bottom :=
      Classical.byContradiction (fun hC => hMax.2 B hNotB hC)
    have hnA : S ⊢₀* neg A := derivesSet0_intro_impl hIA
    have hnB : S ⊢₀* neg B := derivesSet0_intro_impl hIB
    -- `A ∨ B`, `¬A` y `¬B` se contradicen: dos `elim_impl` bajo un `elim_or`
    refine hMax.1 (derivesSet0_map2
      (fun Γ hd hn => ?_) (derivesSet0_hyp hOr) (derivesSet0_map2
        (fun Γ h1 h2 => Derives₀.intro_and Γ (neg A) (neg B) h1 h2) hnA hnB))
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
        exact max_cons_contains hMax
          (derivesSet0_map (fun Γ hd => Derives₀.intro_or_l Γ A B hd) (derivesSet0_hyp hA))
    | inr hB =>
        exact max_cons_contains hMax
          (derivesSet0_map (fun Γ hd => Derives₀.intro_or_r Γ A B hd) (derivesSet0_hyp hB))

-- ============================================================
-- §2 · La equivalencia sintáctica y su cociente
-- ============================================================

def termEqv (S : Formula → Prop) (t1 t2 : Term) : Prop := S (Formula.eq t1 t2)

theorem termEqv_refl {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) (t : Term) :
    termEqv S t t :=
  max_cons_contains hMax ⟨[], fun _ h => absurd h List.not_mem_nil, Derives₀.refl [] t⟩

theorem termEqv_symm {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {t1 t2 : Term}
    (h : termEqv S t1 t2) : termEqv S t2 t1 :=
  max_cons_contains hMax (derivesSet0_map (fun _ hd => derives0_eq_symm hd) (derivesSet0_hyp h))

theorem termEqv_trans {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {t1 t2 t3 : Term}
    (h12 : termEqv S t1 t2) (h23 : termEqv S t2 t3) : termEqv S t1 t3 :=
  max_cons_contains hMax
    (derivesSet0_map2 (fun _ h1 h2 => derives0_eq_trans h1 h2)
      (derivesSet0_hyp h12) (derivesSet0_hyp h23))

def termSetoid (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) : Setoid Term where
  r := termEqv S
  iseqv :=
    { refl := termEqv_refl hMax
      symm := termEqv_symm hMax
      trans := termEqv_trans hMax }

-- ============================================================
-- §3 · Congruencia en listas de argumentos
-- ============================================================

inductive PointwiseEqv (S : Formula → Prop) : List Term → List Term → Prop where
  | nil : PointwiseEqv S [] []
  | cons : ∀ {t1 t2 ts1 ts2}, termEqv S t1 t2 → PointwiseEqv S ts1 ts2 →
      PointwiseEqv S (t1 :: ts1) (t2 :: ts2)

theorem pointwiseEqv_symm {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S)
    {ts1 ts2 : List Term} (h : PointwiseEqv S ts1 ts2) : PointwiseEqv S ts2 ts1 := by
  induction h with
  | nil => exact PointwiseEqv.nil
  | cons ht _ ih => exact PointwiseEqv.cons (termEqv_symm hMax ht) ih

/-- ⭐ Se recorre **una posición cada vez**, con un prefijo `pre` que crece. Es lo que ADR‑031
descubrió: *lo que faltaba no era lógica sino LISTAS.* -/
theorem termEqv_func_congr {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) (f : String)
    {ts1 ts2 : List Term} (hEqv : PointwiseEqv S ts1 ts2) :
    termEqv S (Term.func f ts1) (Term.func f ts2) := by
  suffices H : ∀ pre : List Term,
      termEqv S (Term.func f (pre ++ ts1)) (Term.func f (pre ++ ts2)) from H []
  induction hEqv with
  | nil => intro pre; exact termEqv_refl hMax _
  | @cons t1 t2 r1 _ ht _ ih =>
      intro pre
      have step1 : termEqv S (Term.func f (pre ++ t1 :: r1)) (Term.func f (pre ++ t2 :: r1)) :=
        max_cons_contains hMax
          (derivesSet0_map (fun _ hd => derives0_eq_func_congr f pre r1 hd) (derivesSet0_hyp ht))
      have step2 := ih (pre ++ [t2])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at step2
      exact termEqv_trans hMax step1 step2

theorem termEqv_rel_congr {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) (p : String)
    {ts1 ts2 : List Term} (hEqv : PointwiseEqv S ts1 ts2) :
    S (Formula.atom p ts1) ↔ S (Formula.atom p ts2) := by
  have forward : ∀ {u1 u2 : List Term}, PointwiseEqv S u1 u2 →
      ∀ pre : List Term, S (Formula.atom p (pre ++ u1)) → S (Formula.atom p (pre ++ u2)) := by
    intro u1 u2 h
    induction h with
    | nil => intro _ hx; exact hx
    | @cons t1 t2 r1 _ ht _ ih =>
        intro pre hx
        have step1 : S (Formula.atom p (pre ++ t2 :: r1)) :=
          max_cons_contains hMax
            (derivesSet0_map2 (fun _ he ha => derives0_atom_congr p pre r1 he ha)
              (derivesSet0_hyp ht) (derivesSet0_hyp hx))
        have hnext := ih (pre ++ [t2])
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hnext
        exact hnext step1
  exact ⟨fun h => forward hEqv [] h, fun h => forward (pointwiseEqv_symm hMax hEqv) [] h⟩

-- ============================================================
-- §4 · El modelo canónico
-- ============================================================

noncomputable def quotientOut {α : Type u} {s : Setoid α} (q : Quotient s) : α :=
  Classical.choose (Quotient.exists_rep q)

theorem quotientOut_eq {α : Type u} {s : Setoid α} (q : Quotient s) :
    Quotient.mk s (quotientOut q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

/-- El dominio: **los términos módulo la igualdad demostrable**. -/
def QuotientDomain (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) : Type :=
  Quotient (termSetoid S hMax)

/-- ⭐ `func` **aplica el símbolo**, `rel` **es la pertenencia a `S`**. El modelo canónico no
interpreta nada: se interpreta a sí mismo. -/
noncomputable def canonicalModel (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) :
    Model (QuotientDomain S hMax) where
  func := fun f qs => Quotient.mk (termSetoid S hMax) (Term.func f (qs.map quotientOut))
  rel := fun p qs => S (Formula.atom p (qs.map quotientOut))

def canonicalEnv (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) :
    Nat → QuotientDomain S hMax := fun n => Quotient.mk (termSetoid S hMax) (Term.var n)

theorem pointwiseEqv_out_mk {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S)
    (ts : List Term) :
    PointwiseEqv S ((ts.map (Quotient.mk (termSetoid S hMax))).map quotientOut) ts := by
  induction ts with
  | nil => exact PointwiseEqv.nil
  | cons t ts' ih =>
    unfold List.map
    refine PointwiseEqv.cons ?_ ih
    exact Quotient.exact (quotientOut_eq (Quotient.mk (termSetoid S hMax) t))

-- ⭐⭐ **Evaluar un término en el modelo canónico es su propia clase.**
mutual
theorem evalTerm_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) (t : Term) :
    evalTerm (canonicalModel S hMax) (canonicalEnv S hMax) t
      = Quotient.mk (termSetoid S hMax) t := by
  cases t with
  | var n => rfl
  | func f ts =>
    unfold evalTerm
    rw [evalTerms_canonical S hMax ts]
    simp only [canonicalModel]
    exact Quotient.sound (termEqv_func_congr hMax f (pointwiseEqv_out_mk hMax ts))

theorem evalTerms_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S)
    (ts : List Term) :
    evalTerms (canonicalModel S hMax) (canonicalEnv S hMax) ts
      = ts.map (Quotient.mk (termSetoid S hMax)) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    unfold evalTerms
    rw [evalTerm_canonical S hMax t, evalTerms_canonical S hMax ts']
    rfl
end

-- ============================================================
-- §5 · Los dos cuantificadores — ⭐ aquí, y sólo aquí, paga `IsHenkin`
-- ============================================================

-- ⭐ `formulaComplexity` y `complexity_substFormula` **bajaron a `FOL.Complexity`**
-- el 2026‑09‑23 (encargo de PeanoRF §3): son puramente sintácticos y estaban detrás de
-- toda la cadena clásica de completitud. Los nombres NO cambian — entran por el `open`.

theorem max_cons_ex {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) (hHenkin : IsHenkin S)
    {A : Formula} : S (Formula.ex A) ↔ ∃ t, S (substFormula 0 t A) := by
  refine ⟨fun hEx => hHenkin A hEx, fun h => ?_⟩
  obtain ⟨t, ht⟩ := h
  refine max_cons_contains hMax ⟨[substFormula 0 t A], ?_, ?_⟩
  · intro g hg
    cases hg with
    | head => exact ht
    | tail _ hT => exact absurd hT List.not_mem_nil
  · exact Derives₀.intro_ex _ A t (Derives₀.hyp _ _ (List.Mem.head _))

theorem max_cons_forall {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S)
    (hHenkin : IsHenkin S) {A : Formula} :
    S (Formula.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    refine max_cons_contains hMax ⟨[Formula.forall A], ?_, ?_⟩
    · intro g hg
      cases hg with
      | head => exact hAll
      | tail _ hT => exact absurd hT List.not_mem_nil
    · exact Derives₀.elim_forall _ A t (Derives₀.hyp _ _ (List.Mem.head _))
  · intro hAll
    refine Classical.byContradiction (fun hNotAll => ?_)
    have hInc : (fun x => Or (S x) (x = Formula.forall A)) ⊢₀* Formula.bottom :=
      Classical.byContradiction (fun hC => hMax.2 (Formula.forall A) hNotAll hC)
    have hNegForall : S ⊢₀* neg (Formula.forall A) := derivesSet0_intro_impl hInc
    -- ⭐ `forall_not_ex_not` es un CONSTRUCTOR de `Derives₀`: aquí no hay nada que demostrar
    have hExNeg : S ⊢₀* Formula.ex (neg A) :=
      derivesSet0_map (fun Γ hd =>
        Derives₀.elim_impl Γ (neg (Formula.forall A)) (Formula.ex (neg A))
          (Derives₀.forall_not_ex_not Γ A) hd) hNegForall
    obtain ⟨t, ht⟩ := hHenkin (neg A) (max_cons_contains hMax hExNeg)
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

-- ============================================================
-- §6 · ⭐⭐ EL LEMA DE LA VERDAD
-- ============================================================

theorem truth_lemma_lt {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S)
    (hHenkin : IsHenkin S) (n : Nat) : ∀ f, formulaComplexity f < n →
    (evalFormula (canonicalModel S hMax) (canonicalEnv S hMax) f ↔ S f) := by
  induction n with
  | zero => intro f hLt; exact absurd hLt (Nat.not_lt_zero _)
  | succ n_ih ih =>
    intro f hLt
    cases f with
    | bottom =>
      simp only [evalFormula]
      exact ⟨fun h => h.elim, max_cons_bot hMax⟩
    | atom p ts =>
      simp only [evalFormula]
      show (canonicalModel S hMax).rel p (evalTerms (canonicalModel S hMax) _ ts) ↔ _
      rw [evalTerms_canonical S hMax ts]
      exact termEqv_rel_congr hMax p (pointwiseEqv_out_mk hMax ts)
    | eq t1 t2 =>
      simp only [evalFormula]
      rw [evalTerm_canonical S hMax t1, evalTerm_canonical S hMax t2]
      exact ⟨Quotient.exact (s := termSetoid S hMax), Quotient.sound (s := termSetoid S hMax)⟩
    | impl f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_impl_iff hMax).symm
    | and f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_or hMax).symm
    | «forall» f1 =>
      simp only [evalFormula]
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      have h_eq : (∀ d : QuotientDomain S hMax,
            evalFormula (canonicalModel S hMax) (shiftEnv (canonicalEnv S hMax) d) f1)
          ↔ (∀ d : Term, S (substFormula 0 d f1)) := by
        constructor
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) d f1
          rw [evalTerm_canonical S hMax d] at hSubst
          exact (ih (substFormula 0 d f1) (hLtSub d)).mp
            (hSubst.symm.mp (h (Quotient.mk (termSetoid S hMax) d)))
        · intro h d
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          exact hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr (h t))
      rw [h_eq]
      exact (max_cons_forall hMax hHenkin).symm
    | ex f1 =>
      simp only [evalFormula]
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      have h_eq : (∃ d : QuotientDomain S hMax,
            evalFormula (canonicalModel S hMax) (shiftEnv (canonicalEnv S hMax) d) f1)
          ↔ (∃ t, S (substFormula 0 t f1)) := by
        constructor
        · intro h
          obtain ⟨d, hd⟩ := h
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          exact ⟨t, (ih (substFormula 0 t f1) (hLtSub t)).mp (hSubst.symm.mp hd)⟩
        · intro h
          obtain ⟨t, ht⟩ := h
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          exact ⟨Quotient.mk (termSetoid S hMax) t,
                 hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr ht)⟩
      rw [h_eq]
      exact (max_cons_ex hMax hHenkin).symm

/-- ⭐⭐⭐ **La semántica coincide con la sintaxis en el modelo canónico.** -/
theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) (hHenkin : IsHenkin S)
    (f : Formula) : evalFormula (canonicalModel S hMax) (canonicalEnv S hMax) f ↔ S f :=
  truth_lemma_lt hMax hHenkin (formulaComplexity f + 1) f (Nat.lt_succ_self _)

-- ============================================================
-- §7 · ⭐ El renombrado es SEMÁNTICAMENTE TRANSPARENTE
-- ============================================================

/-- Reinterpreta cada símbolo de función `f` como `ρ f`. ⚠️ Los símbolos de relación no se tocan,
igual que en `renameFormula`. -/
def pullback {D : Type} (M : Model D) (ρ : String → String) : Model D where
  func := fun f ds => M.func (ρ f) ds
  rel := fun p ds => M.rel p ds

mutual
theorem eval_pullback_term {D : Type} (M : Model D) (ρ : String → String) (v : Nat → D) :
    ∀ t : Term, evalTerm (pullback M ρ) v t = evalTerm M v (renameTerm ρ t)
  | .var _ => rfl
  | .func f ts => by
      show (pullback M ρ).func f (evalTerms (pullback M ρ) v ts)
            = M.func (ρ f) (evalTerms M v (renameTerms ρ ts))
      rw [eval_pullback_terms M ρ v ts]
      rfl

theorem eval_pullback_terms {D : Type} (M : Model D) (ρ : String → String) (v : Nat → D) :
    ∀ ts : List Term, evalTerms (pullback M ρ) v ts = evalTerms M v (renameTerms ρ ts)
  | [] => rfl
  | t :: ts => by
      show evalTerm (pullback M ρ) v t :: evalTerms (pullback M ρ) v ts
            = evalTerm M v (renameTerm ρ t) :: evalTerms M v (renameTerms ρ ts)
      rw [eval_pullback_term M ρ v t, eval_pullback_terms M ρ v ts]
end

theorem eval_pullback_formula {D : Type} (M : Model D) (ρ : String → String) :
    ∀ (f : Formula) (v : Nat → D),
    evalFormula (pullback M ρ) v f ↔ evalFormula M v (renameFormula ρ f) := by
  intro f
  induction f with
  | bottom => intro _; exact Iff.rfl
  | atom p ts =>
      intro v
      show (pullback M ρ).rel p (evalTerms (pullback M ρ) v ts) ↔ _
      rw [eval_pullback_terms M ρ v ts]
      exact Iff.rfl
  | eq t u =>
      intro v
      show evalTerm (pullback M ρ) v t = evalTerm (pullback M ρ) v u ↔ _
      rw [eval_pullback_term M ρ v t, eval_pullback_term M ρ v u]
      exact Iff.rfl
  | impl _ _ iha ihb =>
      intro v
      exact Iff.intro
        (fun h hx => (ihb v).mp (h ((iha v).mpr hx)))
        (fun h hx => (ihb v).mpr (h ((iha v).mp hx)))
  | «forall» _ ih =>
      intro v
      exact Iff.intro (fun h d => (ih _).mp (h d)) (fun h d => (ih _).mpr (h d))
  | and _ _ iha ihb =>
      intro v
      exact Iff.intro
        (fun h => ⟨(iha v).mp h.1, (ihb v).mp h.2⟩)
        (fun h => ⟨(iha v).mpr h.1, (ihb v).mpr h.2⟩)
  | or _ _ iha ihb =>
      intro v
      exact Iff.intro
        (fun h => h.elim (fun x => Or.inl ((iha v).mp x)) (fun x => Or.inr ((ihb v).mp x)))
        (fun h => h.elim (fun x => Or.inl ((iha v).mpr x)) (fun x => Or.inr ((ihb v).mpr x)))
  | ex _ ih =>
      intro v
      exact Iff.intro
        (fun h => h.elim (fun d hd => ⟨d, (ih _).mp hd⟩))
        (fun h => h.elim (fun d hd => ⟨d, (ih _).mpr hd⟩))

-- ============================================================
-- §8 · ⭐⭐⭐ COMPLETITUD
-- ============================================================

def IsSatisfiable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D), ∀ f, S f → evalFormula M v f

/-- ⭐ **Volver del sublenguaje**: un modelo de `shiftTheory S` da un modelo de `S` sin más que
reinterpretar los símbolos. Es la pieza que faltaba para que `henkin_completion` se pueda usar. -/
theorem satisfiable_of_shift {S : Formula → Prop} (h : IsSatisfiable (shiftTheory S)) :
    IsSatisfiable S := by
  obtain ⟨D, M, v, hM⟩ := h
  refine ⟨D, pullback M shift, v, fun f hf => ?_⟩
  exact (eval_pullback_formula M shift f v).mpr (hM _ ⟨f, hf, rfl⟩)

/-- ⭐⭐ **Toda teoría consistente tiene modelo.** -/
theorem model_existence_lemma₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsSatisfiable S := by
  obtain ⟨T, hMax, hHenkin, hSub⟩ := henkin_completion hCons
  refine satisfiable_of_shift ⟨QuotientDomain T hMax, canonicalModel T hMax, canonicalEnv T hMax,
    fun f hf => ?_⟩
  exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)

/-- ⭐⭐⭐ **EL TEOREMA DE COMPLETITUD** para `Derives₀`.

⛔ Su `Classical.choice` es el `if IsConsistent₀ …` de `FOL.Lindenbaum0` (Π⁰₁) — es el **WKL**, y
va explicado en la cabecera de este módulo y en ADR‑040 §2. -/
theorem completeness₀ {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢₀ f := by
  refine Classical.byContradiction (fun hNot => ?_)
  have hCons : IsConsistent₀ (fun x => Or (x ∈ Γ) (x = neg f)) := by
    intro hBot
    have hImpl : (fun y => y ∈ Γ) ⊢₀* Formula.impl (neg f) Formula.bottom :=
      derivesSet0_intro_impl hBot
    obtain ⟨Γs, hΓs, hD⟩ := hImpl
    exact hNot (Derives₀.weakening Γs Γ f
      (Derives₀.elim_impl Γs (neg (neg f)) f (Derives₀.dne_schema Γs f) hD) hΓs)
  obtain ⟨D, M, v, hModel⟩ := model_existence_lemma₀ hCons
  exact hModel (neg f) (Or.inr rfl) (h D M v (fun g hg => hModel g (Or.inl hg)))

/-- ⭐⭐⭐⭐ **Y las DOS direcciones sobre el mismo cálculo**, que es lo que este proyecto no había
tenido nunca. La ida es `derives0_soundness` (ADR‑034). -/
theorem derives0_complete_iff {Γ : List Formula} {f : Formula} : (Γ ⊢₀ f) ↔ (Γ ⊨ f) :=
  ⟨FOL.Metamath.Soundness0.derives0_soundness, completeness₀⟩

-- ============================================================
-- §9 · ⚠️ CONTROL DE NO VACUIDAD
-- ============================================================

-- ⚠️ Un teorema de completitud puede ser cierto y **no servir para nada** si el consecuente es
-- trivial. Estas dos líneas lo descartan: producen derivaciones REALES de `Derives₀` que NO son
-- un constructor ni una cadena corta de ellos, pasando por el modelo canónico.

/-- ⭐ **El tercio excluso a nivel OBJETO, obtenido POR COMPLETITUD.** -/
theorem derives0_em (A : Formula) : [] ⊢₀ Formula.or A (neg A) :=
  completeness₀ (fun _ _ _ _ => Classical.em _)

/-- ⭐ **Peirce**, ídem: es el ejemplo canónico de tautología clásica que la lógica intuicionista
no demuestra. Si `completeness₀` fuera vacua, esto no compilaría. -/
theorem derives0_peirce (A B : Formula) :
    [] ⊢₀ Formula.impl (Formula.impl (Formula.impl A B) A) A := by
  refine completeness₀ (fun _ _ _ _ h => ?_)
  exact Classical.byCases (fun hA => hA) (fun hA => h (fun hx => absurd hx hA))

end FOL.Canonical0

#print axioms FOL.Canonical0.truth_lemma
#print axioms FOL.Canonical0.eval_pullback_formula
#print axioms FOL.Canonical0.model_existence_lemma₀
#print axioms FOL.Canonical0.completeness₀
#print axioms FOL.Canonical0.max_cons_neg
#print axioms FOL.Canonical0.max_cons_complete
#print axioms FOL.Canonical0.derives0_complete_iff
#print axioms FOL.Canonical0.derives0_em
#print axioms FOL.Canonical0.derives0_peirce
