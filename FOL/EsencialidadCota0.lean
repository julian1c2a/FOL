/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.EsencialidadSem0
-- @axiom_system: intuitionistic (sus teoremas, como mucho `[propext, Quot.sound]`: es lo que mide)
-- @importance: medium

import FOL.EsencialidadSem0

/-!
# `FOL.EsencialidadCota0` — la COTA POR ARRIBA de los semánticos: WLEM + ¬¬EM bastan (la pregunta 3 de T71, ADR‑275 de RPP)

`FOL.EsencialidadSem0` mide lo que los ENUNCIADOS de los cinco semánticos de `Compacity0` implican (WLEM, KSst, WKS).
Aquí, la otra dirección: con WLEM y ¬¬EM como hipótesis, y sin `Classical.choice`, se demuestran. (Los `example`
de control del final sí lo llevan, a propósito: comprueban que las dos hipótesis caben juntas.)

* **§1–§4 · El modelo canónico DOBLEMENTE NEGADO.** Sobre el límite concreto de Lindenbaum sobre el de Henkin, que es
  consistente, cerrado por derivación y maximal sin decidir nada (`Buena`), el dominio son los términos módulo
  `¬¬T(t = u)` y los átomos valen `¬¬T(R t̄)`. El lema de la verdad, `M ⊨ f ⟺ ¬¬T f` (`truthN`), sólo usa WLEM en el
  `∨` (De Morgan). En el `∃`, la constante de Henkin (el `∃ c`) sale fuera de la doble negación; lo que va dentro es
  `¬¬T(A[c])` (`henLimit_witness`).
* **§5 · La existencia de modelo ⟺ WLEM** (`model_existence_iff_wlem`). La vuelta es E7 de `FOL.Esencialidad0`.
  Herbelin y Kirst (TYPES 2023) publicaron el resultado; aquí está en el cálculo y la semántica de FOL. Que su cálculo
  sea el mismo no consta: sólo se leyó su resumen.
* **§6 · «Lo satisfacible es consistente» ⟺ ¬¬EM** (`consistency_iff_nnem`). Hacia la izquierda, la solidez para
  modelos estables (`sound_stable`). Hacia la derecha, la `σ` de E11 de `EsencialidadSem0`, que es satisfacible si
  `¬EM` y deriva `⊥` (`sigma_inconsistent`).
* **§7 · Los cinco semánticos, desde WLEM + ¬¬EM** (`cinco_of_wlem_nnem`). Son las pruebas cortas de `Compacity0`
  rehechas sobre §5 y §6. El propietario pidió la compacidad, LS↓ y `countable_infinite_of_infinite`; los dos de §3
  salen de paso, porque `countable_infinite_of_infinite` pasa por ellos.

**Dónde quedan**, con lo que `EsencialidadSem0` mide por abajo:

* la compacidad (E8) y los dos de §3 (E10) implican WLEM, así que quedan entre WLEM y WLEM + ¬¬EM;
* LS↓ y `countable_infinite_of_infinite` sólo implican KSst y WKS (E9), por debajo de WLEM, así que quedan entre KSst y
  WLEM + ¬¬EM.

Si la compacidad implica ¬¬EM sigue abierto (D1). El estudio de viabilidad, la bibliografía y el veredicto del escéptico:
`auditoria/t71-p3-p4-2026-11-19/`. Nada de esto lo consume otro módulo: es la medida, con sus filas de footprint en
RPP.
-/

set_option autoImplicit false

namespace FOL.EsencialidadCota0

open FOL.Metamath.Semantics
open FOL.Henkin0
open FOL.Fresh0
open FOL.Lindenbaum0
open FOL.HenkinLimit0
open FOL.Eq0
open FOL.Complexity
open FOL.Canonical0 (IsSatisfiable PointwiseEqv satisfiable_of_shift derivesSet0_map derivesSet0_map2 pullback
  eval_pullback_formula)
open FOL.Compacity0 (CountableDom IsSatisfiableCountable InfiniteDom HasLargeModels countable_of_shift infTheory
  infTheory_finSat neqAx hasLargeModels_shift)
open FOL.EsencialidadSem0 (WLEM CompactnessStmt LsDownStmt CountableInfStmt LargeStmt LargeFreshStmt)
open FOL.EsencialidadSem0.E11 (EM sigmaF rF Ssig nnem_iff_unsat_sigma)

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- §1 · El límite concreto, y lo que se le puede pedir SIN decidir
-- ============================================================

theorem nn_map {P Q : Prop} (f : P → Q) (h : Not (Not P)) : Not (Not Q) := fun hq => h (fun hp => hq (f hp))

theorem nn_map2 {P Q R : Prop} (f : P → Q → R) (hp : Not (Not P)) (hq : Not (Not Q)) : Not (Not R) :=
  fun hr => hp (fun p => hq (fun q => hr (f p q)))

/-- Lo que el límite concreto de Lindenbaum sobre el de Henkin cumple SIN tercio excluso: consistencia, cierre por
derivación, la maximalidad por no ampliabilidad y un testigo de Henkin para cada `A`. -/
structure Buena (T : Formula → Prop) : Prop where
  cons : IsConsistent₀ T
  closed : ∀ {f : Formula}, (T ⊢₀* f) → T f
  max : ∀ f, Not (T f) → Not (IsConsistent₀ (fun x => Or (T x) (x = f)))
  wit : ∀ A : Formula, ∃ c : List Char, T (henkinAx c A)

/-- ⭐ El límite concreto es `Buena`, sin `Classical.choice`: lo da `Lindenbaum0` (`lindenbaum_limit_max`,
`lindenbaum_limit_closed`) y `HenkinLimit0` (`henLimit_witness`). -/
theorem buena_limite {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    Buena (LindenbaumLimit (henLimit S)) := by
  have hH := henLimit_consistent₀ hCons
  exact ⟨(lindenbaum_limit_max hH).1, fun h => lindenbaum_limit_closed hH h, (lindenbaum_limit_max hH).2,
    fun A => (henLimit_witness S A).elim (fun c hc => ⟨c, ⟨0, hc⟩⟩)⟩

section Buena

variable {T : Formula → Prop}

theorem Buena.thm (hB : Buena T) {A : Formula} (r : ∀ Γ : List Formula, Γ ⊢₀ A) : T A :=
  hB.closed ⟨[], fun _ h => absurd h List.not_mem_nil, r []⟩

theorem Buena.rule1 (hB : Buena T) {A B : Formula} (r : ∀ Γ : List Formula, (Γ ⊢₀ A) → Γ ⊢₀ B) :
    T A → T B :=
  fun h => hB.closed (derivesSet0_map r (derivesSet0_hyp h))

theorem Buena.rule2 (hB : Buena T) {A B C : Formula}
    (r : ∀ Γ : List Formula, (Γ ⊢₀ A) → (Γ ⊢₀ B) → Γ ⊢₀ C) : T A → T B → T C :=
  fun h1 h2 => hB.closed (derivesSet0_map2 r (derivesSet0_hyp h1) (derivesSet0_hyp h2))

theorem Buena.mp (hB : Buena T) {A B : Formula} : T (Formula.impl A B) → T A → T B :=
  hB.rule2 (fun Γ h1 h2 => Derives₀.elim_impl Γ A B h1 h2)

theorem Buena.hyp_contra (hB : Buena T) {f : Formula} (h1 : T f) (h2 : T (neg f)) : False :=
  hB.cons (derivesSet0_elim_impl (derivesSet0_hyp h2) (derivesSet0_hyp h1))

/-- ⭐ La maximalidad, sin decidir: si `f` no está, `¬f` no puede faltar. -/
theorem Buena.neg_of_not (hB : Buena T) {f : Formula} (hn : Not (T f)) : Not (Not (T (neg f))) :=
  fun hk => hB.max f hn (fun hinc => hk (hB.closed (derivesSet0_intro_impl hinc)))

/-- `A ∨ B`, `¬A` y `¬B` no caben juntas. -/
theorem Buena.or_contra (hB : Buena T) {A B : Formula} (h1 : T (Formula.or A B)) (h2 : T (neg A))
    (h3 : T (neg B)) : False := by
  refine hB.cons ⟨[Formula.or A B, neg A, neg B], ?_, ?_⟩
  · intro g hg
    cases hg with
    | head => exact h1
    | tail _ hg =>
      cases hg with
      | head => exact h2
      | tail _ hg =>
        cases hg with
        | head => exact h3
        | tail _ hg => exact absurd hg List.not_mem_nil
  · refine Derives₀.elim_or _ A B Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _)) ?_ ?_
    · exact Derives₀.elim_impl _ A Formula.bottom
        (Derives₀.hyp _ (neg A) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        (Derives₀.hyp _ A (List.Mem.head _))
    · exact Derives₀.elim_impl _ B Formula.bottom
        (Derives₀.hyp _ (neg B) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        (Derives₀.hyp _ B (List.Mem.head _))

-- ============================================================
-- §2 · Las conectivas, doblemente negadas
-- ============================================================

/-- La pertenencia doblemente negada. -/
abbrev NN (T : Formula → Prop) : Formula → Prop := fun f => Not (Not (T f))

theorem implN (hB : Buena T) {A B : Formula} :
    Iff (NN T A → NN T B) (NN T (Formula.impl A B)) := by
  constructor
  · intro h hn
    refine hB.neg_of_not hn (fun hneg => ?_)
    have hA : T A := hB.rule1 (fun _ hd => neg_impl_left hd) hneg
    have hnB : T (neg B) := hB.rule1 (fun _ hd => neg_impl_right hd) hneg
    exact h (fun k => k hA) (fun hb => hB.hyp_contra hb hnB)
  · intro h hA hnB
    exact h (fun hI => hA (fun a => hnB (hB.mp hI a)))

theorem andN (hB : Buena T) {A B : Formula} :
    Iff (And (NN T A) (NN T B)) (NN T (Formula.and A B)) :=
  ⟨fun h => nn_map2 (hB.rule2 (fun Γ a b => Derives₀.intro_and Γ A B a b)) h.1 h.2,
   fun h => ⟨nn_map (hB.rule1 (fun Γ hd => Derives₀.elim_and_l Γ A B hd)) h,
     nn_map (hB.rule1 (fun Γ hd => Derives₀.elim_and_r Γ A B hd)) h⟩⟩

/-- ⭐ El único sitio que pide WLEM: el `∨`, por De Morgan. -/
theorem orN (hW : WLEM) (hB : Buena T) {A B : Formula} :
    Iff (Or (NN T A) (NN T B)) (NN T (Formula.or A B)) := by
  constructor
  · intro h
    exact h.elim (nn_map (hB.rule1 (fun Γ hd => Derives₀.intro_or_l Γ A B hd)))
      (nn_map (hB.rule1 (fun Γ hd => Derives₀.intro_or_r Γ A B hd)))
  · intro h
    cases hW (T A) with
    | inr hnnA => exact Or.inl hnnA
    | inl hnA =>
      refine Or.inr (fun hnB => h (fun hor => ?_))
      exact hB.neg_of_not hnA (fun hna => hB.neg_of_not hnB (fun hnb => hB.or_contra hor hna hnb))

theorem forallN (hB : Buena T) {A : Formula} :
    Iff (∀ t : Term, NN T (substFormula 0 t A)) (NN T (Formula.forall A)) := by
  constructor
  · intro h hn
    refine hB.neg_of_not hn (fun hneg => ?_)
    have hex : T (Formula.ex (neg A)) :=
      hB.rule1 (fun Γ hd => Derives₀.elim_impl Γ _ _ (Derives₀.forall_not_ex_not Γ A) hd) hneg
    obtain ⟨c, hc⟩ := hB.wit (neg A)
    have hna : T (neg (substFormula 0 (Term.func c []) A)) := hB.mp hc hex
    exact h (Term.func c []) (fun ha => hB.hyp_contra ha hna)
  · intro h t
    exact nn_map (hB.rule1 (fun Γ hd => Derives₀.elim_forall Γ A t hd)) h

/-- ⭐ El `∃`: el testigo de Henkin sale FUERA de la doble negación, sin decidir nada. -/
theorem exN (hB : Buena T) {A : Formula} :
    Iff (∃ t : Term, NN T (substFormula 0 t A)) (NN T (Formula.ex A)) := by
  constructor
  · intro ⟨t, ht⟩
    exact nn_map (hB.rule1 (fun Γ hd => Derives₀.intro_ex Γ A t hd)) ht
  · intro h
    obtain ⟨c, hc⟩ := hB.wit A
    exact ⟨Term.func c [], nn_map (fun hex => hB.mp hc hex) h⟩

-- ============================================================
-- §3 · El cociente por `¬¬T(t = u)`
-- ============================================================

/-- `t ≈ u` cuando `t = u` no puede faltar en `T`. -/
def eqvN (T : Formula → Prop) (t u : Term) : Prop := NN T (Formula.eq t u)

theorem eqvN_refl (hB : Buena T) (t : Term) : eqvN T t t :=
  fun hn => hn (hB.thm (fun Γ => Derives₀.refl Γ t))

theorem eqvN_symm (hB : Buena T) {t u : Term} (h : eqvN T t u) : eqvN T u t :=
  nn_map (hB.rule1 (fun _ hd => derives0_eq_symm hd)) h

theorem eqvN_trans (hB : Buena T) {t u w : Term} (h1 : eqvN T t u) (h2 : eqvN T u w) : eqvN T t w :=
  nn_map2 (hB.rule2 (fun _ a b => derives0_eq_trans a b)) h1 h2

def setoidN (hB : Buena T) : Setoid Term where
  r := eqvN T
  iseqv := { refl := eqvN_refl hB, symm := eqvN_symm hB, trans := eqvN_trans hB }

theorem pointwise_symmN (hB : Buena T) {ts1 ts2 : List Term} (h : PointwiseEqv (NN T) ts1 ts2) :
    PointwiseEqv (NN T) ts2 ts1 := by
  induction h with
  | nil => exact PointwiseEqv.nil
  | cons ht _ ih => exact PointwiseEqv.cons (eqvN_symm hB ht) ih

theorem pointwise_reflN (hB : Buena T) : ∀ ts : List Term, PointwiseEqv (NN T) ts ts
  | [] => PointwiseEqv.nil
  | t :: ts => PointwiseEqv.cons (eqvN_refl hB t) (pointwise_reflN hB ts)

theorem func_congrN (hB : Buena T) (f : List Char) {ts1 ts2 : List Term}
    (hE : PointwiseEqv (NN T) ts1 ts2) : eqvN T (Term.func f ts1) (Term.func f ts2) := by
  suffices H : ∀ pre : List Term, eqvN T (Term.func f (pre ++ ts1)) (Term.func f (pre ++ ts2)) from H []
  induction hE with
  | nil => intro pre; exact eqvN_refl hB _
  | @cons t1 t2 r1 _ ht _ ih =>
      intro pre
      have step1 : eqvN T (Term.func f (pre ++ t1 :: r1)) (Term.func f (pre ++ t2 :: r1)) :=
        nn_map (hB.rule1 (fun _ hd => derives0_eq_func_congr f pre r1 hd)) ht
      have step2 := ih (pre ++ [t2])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at step2
      exact eqvN_trans hB step1 step2

theorem rel_congrN (hB : Buena T) (p : List Char) {ts1 ts2 : List Term}
    (hE : PointwiseEqv (NN T) ts1 ts2) :
    Iff (NN T (Formula.atom p ts1)) (NN T (Formula.atom p ts2)) := by
  have forward : ∀ {u1 u2 : List Term}, PointwiseEqv (NN T) u1 u2 →
      ∀ pre : List Term, NN T (Formula.atom p (pre ++ u1)) → NN T (Formula.atom p (pre ++ u2)) := by
    intro u1 u2 h
    induction h with
    | nil => intro _ hx; exact hx
    | @cons t1 t2 r1 _ ht _ ih =>
        intro pre hx
        have step1 : NN T (Formula.atom p (pre ++ t2 :: r1)) :=
          nn_map2 (hB.rule2 (fun _ he ha => derives0_atom_congr p pre r1 he ha)) ht hx
        have hnext := ih (pre ++ [t2])
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hnext
        exact hnext step1
  exact ⟨fun h => forward hE [] h, fun h => forward (pointwise_symmN hB hE) [] h⟩

/-- El dominio: los términos módulo `¬¬T(t = u)`. -/
abbrev DomN (hB : Buena T) : Type := Quotient (setoidN hB)

def consQN (hB : Buena T) (a : Term) : Quot (PointwiseEqv (NN T)) → Quot (PointwiseEqv (NN T)) :=
  Quot.lift (fun as => Quot.mk (PointwiseEqv (NN T)) (a :: as))
    (fun _ _ h => Quot.sound (PointwiseEqv.cons (eqvN_refl hB a) h))

theorem consQN_resp (hB : Buena T) (a b : Term) (hab : eqvN T a b) (L : Quot (PointwiseEqv (NN T))) :
    consQN hB a L = consQN hB b L :=
  Quot.ind (β := fun L => consQN hB a L = consQN hB b L)
    (fun as => Quot.sound (PointwiseEqv.cons hab (pointwise_reflN hB as))) L

/-- La clase de la lista, a partir de la lista de clases: elección FINITA, por recursión. -/
def listQN (hB : Buena T) : List (DomN hB) → Quot (PointwiseEqv (NN T))
  | [] => Quot.mk _ []
  | q :: qs => Quotient.lift (s := setoidN hB) (fun a => consQN hB a (listQN hB qs))
      (fun a b hab => consQN_resp hB a b hab _) q

theorem listQN_mk (hB : Buena T) : ∀ ts : List Term,
    listQN hB (ts.map (Quotient.mk (setoidN hB))) = Quot.mk _ ts
  | [] => rfl
  | t :: ts => by
      show consQN hB t (listQN hB (ts.map (Quotient.mk (setoidN hB)))) = _
      rw [listQN_mk hB ts]
      rfl

/-- ⭐ El modelo canónico doblemente negado: `func` aplica el símbolo y `rel` es la pertenencia doblemente negada. -/
def modelN (hB : Buena T) : Model (DomN hB) where
  func := fun f qs => Quot.lift (fun ts => Quotient.mk (setoidN hB) (Term.func f ts))
    (fun _ _ h => Quotient.sound (func_congrN hB f h)) (listQN hB qs)
  rel := fun p qs => Quot.lift (fun ts => NN T (Formula.atom p ts))
    (fun _ _ h => propext (rel_congrN hB p h)) (listQN hB qs)

def envN (hB : Buena T) : Nat → DomN hB := fun n => Quotient.mk (setoidN hB) (Term.var n)

mutual
theorem evalTerm_N (hB : Buena T) (t : Term) :
    evalTerm (modelN hB) (envN hB) t = Quotient.mk (setoidN hB) t := by
  cases t with
  | var n => rfl
  | func f ts =>
    show Quot.lift _ _ (listQN hB (evalTerms (modelN hB) (envN hB) ts)) = _
    rw [evalTerms_N hB ts, listQN_mk]

theorem evalTerms_N (hB : Buena T) (ts : List Term) :
    evalTerms (modelN hB) (envN hB) ts = ts.map (Quotient.mk (setoidN hB)) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    unfold evalTerms
    rw [evalTerm_N hB t, evalTerms_N hB ts']
    rfl
end

-- ============================================================
-- §4 · ⭐⭐ EL LEMA DE LA VERDAD, doblemente negado
-- ============================================================

theorem truthN_lt (hW : WLEM) (hB : Buena T) (n : Nat) : ∀ f, formulaComplexity f < n →
    Iff (evalFormula (modelN hB) (envN hB) f) (NN T f) := by
  induction n with
  | zero => intro f hLt; exact absurd hLt (Nat.not_lt_zero _)
  | succ n_ih ih =>
    intro f hLt
    cases f with
    | bottom =>
      show Iff False (NN T Formula.bottom)
      exact ⟨False.elim, fun h => h (fun hb => hB.cons (derivesSet0_hyp hb))⟩
    | atom p ts =>
      show Iff (Quot.lift _ _ (listQN hB (evalTerms (modelN hB) (envN hB) ts))) _
      rw [evalTerms_N hB ts, listQN_mk]
    | eq t1 t2 =>
      show Iff (evalTerm (modelN hB) (envN hB) t1 = evalTerm (modelN hB) (envN hB) t2) _
      rw [evalTerm_N hB t1, evalTerm_N hB t2]
      exact ⟨Quotient.exact (s := setoidN hB), Quotient.sound (s := setoidN hB)⟩
    | impl f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      show Iff (evalFormula (modelN hB) (envN hB) f1 → evalFormula (modelN hB) (envN hB) f2) _
      rw [ih f1 hLt1, ih f2 hLt2]
      exact implN hB
    | and f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      show Iff (And (evalFormula (modelN hB) (envN hB) f1) (evalFormula (modelN hB) (envN hB) f2)) _
      rw [ih f1 hLt1, ih f2 hLt2]
      exact andN hB
    | or f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      show Iff (Or (evalFormula (modelN hB) (envN hB) f1) (evalFormula (modelN hB) (envN hB) f2)) _
      rw [ih f1 hLt1, ih f2 hLt2]
      exact orN hW hB
    | «forall» f1 =>
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      show Iff (∀ d : DomN hB, evalFormula (modelN hB) (shiftEnv (envN hB) d) f1) _
      have h_eq : Iff (∀ d : DomN hB, evalFormula (modelN hB) (shiftEnv (envN hB) d) f1)
          (∀ t : Term, NN T (substFormula 0 t f1)) := by
        constructor
        · intro h t
          have hSubst := eval_substFormula_zero (modelN hB) (envN hB) t f1
          rw [evalTerm_N hB t] at hSubst
          exact (ih (substFormula 0 t f1) (hLtSub t)).mp (hSubst.mpr (h (Quotient.mk (setoidN hB) t)))
        · intro h d
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (modelN hB) (envN hB) t f1
          rw [evalTerm_N hB t] at hSubst
          exact hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr (h t))
      rw [h_eq]
      exact forallN hB
    | ex f1 =>
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      show Iff (∃ d : DomN hB, evalFormula (modelN hB) (shiftEnv (envN hB) d) f1) _
      have h_eq : Iff (∃ d : DomN hB, evalFormula (modelN hB) (shiftEnv (envN hB) d) f1)
          (∃ t : Term, NN T (substFormula 0 t f1)) := by
        constructor
        · intro h
          obtain ⟨d, hd⟩ := h
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (modelN hB) (envN hB) t f1
          rw [evalTerm_N hB t] at hSubst
          exact ⟨t, (ih (substFormula 0 t f1) (hLtSub t)).mp (hSubst.mpr hd)⟩
        · intro h
          obtain ⟨t, ht⟩ := h
          have hSubst := eval_substFormula_zero (modelN hB) (envN hB) t f1
          rw [evalTerm_N hB t] at hSubst
          exact ⟨Quotient.mk (setoidN hB) t, hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr ht)⟩
      rw [h_eq]
      exact exN hB

/-- ⭐⭐⭐ **El lema de la verdad, doblemente negado**: `M ⊨ f ⟺ ¬¬T f`, con WLEM como única hipótesis además de que
`T` sea `Buena`. -/
theorem truthN (hW : WLEM) (hB : Buena T) (f : Formula) :
    Iff (evalFormula (modelN hB) (envN hB) f) (NN T f) :=
  truthN_lt hW hB (formulaComplexity f + 1) f (Nat.lt_succ_self _)

end Buena

-- ============================================================
-- §5 · ⭐⭐ La existencia de modelo ⟺ WLEM
-- ============================================================

/-- 🏁 **Con WLEM, toda teoría consistente tiene un modelo NUMERABLE**, sin `Classical.choice`. -/
theorem model_existence_countable_of_wlem (hW : WLEM) {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsSatisfiableCountable S := by
  have hB := buena_limite hCons
  refine countable_of_shift ⟨DomN hB, modelN hB, envN hB,
    ⟨fun n => Quotient.mk (setoidN hB) (FOL.Metamath.Enumeration.natToTerm n), ?_⟩,
    fun f hf => (truthN hW hB f).mpr (fun hn => hn ⟨0, shiftTheory_sub_henLimit S f hf⟩)⟩
  intro d
  obtain ⟨t, ht⟩ := Quotient.exists_rep d
  obtain ⟨n, hn⟩ := FOL.Metamath.Enumeration.natToTerm_surj t
  refine ⟨n, ?_⟩
  show Quotient.mk (setoidN hB) (FOL.Metamath.Enumeration.natToTerm n) = d
  rw [hn]; exact ht

theorem model_existence_of_wlem (hW : WLEM) : ∀ {S : Formula → Prop}, IsConsistent₀ S → IsSatisfiable S :=
  fun hCons => (model_existence_countable_of_wlem hW hCons).elim
    (fun D h => h.elim (fun M h => h.elim (fun v h => ⟨D, M, v, h.2⟩)))

/-- 🏁 **La existencia de modelo EQUIVALE a WLEM** (Herbelin–Kirst, TYPES 2023, aquí en FOL). La ida es E7 de
`FOL.Esencialidad0`. -/
theorem model_existence_iff_wlem :
    Iff (∀ {S : Formula → Prop}, IsConsistent₀ S → IsSatisfiable S) WLEM :=
  ⟨fun h => FOL.Esencialidad0.E7.model_existence_stmt_implies_wlem h, fun hW => model_existence_of_wlem hW⟩

-- ============================================================
-- §6 · ⭐⭐ «Lo satisfacible es consistente» ⟺ ¬¬EM
-- ============================================================

/-- Con ¬¬EM, un modelo hace consistente a su teoría: la meta es negativa, así que vale EM dentro, y con él cada
evaluación es estable (`sound_stable`). -/
theorem consistent_of_sat_of_nnem (hN : Not (Not EM)) {S : Formula → Prop} (h : IsSatisfiable S) :
    IsConsistent₀ S := by
  intro hBot
  obtain ⟨Γ, hΓ, hD⟩ := hBot
  obtain ⟨D, M, v, hM⟩ := h
  exact hN (fun hem => FOL.Esencialidad0.E2.sound_stable M
    (fun v' f hnn => (hem (evalFormula M v' f)).elim id (fun hn => (hnn hn).elim)) hD v
    (fun g hg => hM g (hΓ g hg)))

/-- `σ` deriva `⊥` en el cálculo clásico: de `∀x ¬¬R x`, por la doble negación y el `∀`‑intro, `∀x R x`. -/
theorem sigma_inconsistent : [sigmaF] ⊢₀ Formula.bottom := by
  have hσ : [sigmaF] ⊢₀ sigmaF := Derives₀.hyp _ _ (List.Mem.head _)
  have h1 : [sigmaF] ⊢₀ Formula.forall (neg (neg rF)) := Derives₀.elim_and_l _ _ _ hσ
  have h2 : [sigmaF] ⊢₀ neg (Formula.forall rF) := Derives₀.elim_and_r _ _ _ hσ
  have hAll : [sigmaF] ⊢₀ Formula.forall rF := by
    refine Derives₀.intro_forall _ _ ?_
    show [sigmaF] ⊢₀ rF
    exact Derives₀.dne_rule _ _ (Derives₀.elim_forall _ _ (Term.var 0) h1)
  exact Derives₀.elim_impl _ _ _ h2 hAll

/-- Y al revés: si toda teoría satisfacible es consistente, ¬¬EM (por E11: `σ` sería satisfacible con `¬EM`). -/
theorem nnem_of_consistency (H : ∀ {S : Formula → Prop}, IsSatisfiable S → IsConsistent₀ S) : Not (Not EM) :=
  nnem_iff_unsat_sigma.mpr (fun hs => H hs ⟨[sigmaF], fun g hg => by
    cases hg with
    | head => rfl
    | tail _ h => exact absurd h List.not_mem_nil, sigma_inconsistent⟩)

/-- 🏁 **«Lo satisfacible es consistente» EQUIVALE a ¬¬EM.** El enunciado de `Compacity0.consistency_of_satisfiable₀`
es el de la izquierda: el `Classical.choice` de su prueba no se puede quitar sin ¬¬EM. -/
theorem consistency_iff_nnem :
    Iff (∀ {S : Formula → Prop}, IsSatisfiable S → IsConsistent₀ S) (Not (Not EM)) :=
  ⟨fun H => nnem_of_consistency H, fun hN => consistent_of_sat_of_nnem hN⟩

-- ============================================================
-- §7 · 🏁 Los cinco semánticos, desde WLEM + ¬¬EM
-- ============================================================

theorem compactness_of (hW : WLEM) (hN : Not (Not EM)) : CompactnessStmt := by
  intro S
  constructor
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hE⟩ := hSat
    exact ⟨D, M, v, fun f hf => hE f (hSub f hf)⟩
  · intro hFin
    refine model_existence_of_wlem hW ?_
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    exact consistent_of_sat_of_nnem hN (hFin Γ hΓ) ⟨Γ, fun _ hg => hg, hDer⟩

theorem ls_down_of (hW : WLEM) (hN : Not (Not EM)) : LsDownStmt :=
  fun hSat => model_existence_countable_of_wlem hW (consistent_of_sat_of_nnem hN hSat)

theorem large_fresh_of (hW : WLEM) (hN : Not (Not EM)) : LargeFreshStmt := by
  intro S hFresh hLarge
  obtain ⟨D, M, v, hC, hM⟩ := ls_down_of hW hN
    ((compactness_of hW hN (infTheory S)).mpr (infTheory_finSat hFresh hLarge))
  refine ⟨D, M, v, ⟨hC, ⟨fun i => evalTerm M v (Term.func (cst i) []), fun i j hij => ?_⟩⟩,
    fun f hf => hM f (Or.inl hf)⟩
  exact Decidable.byContradiction (fun hne => hM (neqAx i j) (Or.inr ⟨i, j, hne, rfl⟩) hij)

theorem large_of (hW : WLEM) (hN : Not (Not EM)) : LargeStmt := by
  intro S hLarge
  obtain ⟨D, M, v, hDom, hM⟩ := large_fresh_of hW hN (S := shiftTheory S)
    (fun f hf m => shiftTheory_fresh m f hf) (hasLargeModels_shift hLarge)
  exact ⟨D, pullback M shift, v, hDom,
    fun f hf => (eval_pullback_formula M shift f v).mpr (hM _ ⟨f, hf, rfl⟩)⟩

theorem countable_inf_of (hW : WLEM) (hN : Not (Not EM)) : CountableInfStmt := by
  intro S h
  obtain ⟨D, M, v, ⟨e, he⟩, hM⟩ := h
  exact large_of hW hN (fun _ => ⟨D, M, v, hM, e, fun i j _ _ hij => he i j hij⟩)

/-- 🏁🏁 **WLEM + ¬¬EM bastan para los CINCO**, sin `Classical.choice`. Por abajo (`EsencialidadSem0`): la compacidad
y los dos de §3 implican WLEM (E8, E10); LS↓ y `countable_infinite_of_infinite`, sólo KSst (E9). -/
theorem cinco_of_wlem_nnem (hW : WLEM) (hN : Not (Not EM)) :
    And CompactnessStmt (And LsDownStmt (And CountableInfStmt (And LargeStmt LargeFreshStmt))) :=
  ⟨compactness_of hW hN, ls_down_of hW hN, countable_inf_of hW hN, large_of hW hN, large_fresh_of hW hN⟩

-- ⚠️ CONTROLES DE NO VACUIDAD: con la lógica clásica, las dos hipótesis se cumplen JUNTAS (y llevan
-- `Classical.choice`); y las conclusiones son los enunciados reales (las identidades de tipos de `EsencialidadSem0`).
example : WLEM := fun P => (Classical.em P).elim (fun h => Or.inr (fun hn => hn h)) Or.inl
example : Not (Not EM) := fun h => h Classical.em
example : And CompactnessStmt (And LsDownStmt (And CountableInfStmt (And LargeStmt LargeFreshStmt))) :=
  cinco_of_wlem_nnem (fun P => (Classical.em P).elim (fun h => Or.inr (fun hn => hn h)) Or.inl)
    (fun h => h Classical.em)

end FOL.EsencialidadCota0

#print axioms FOL.EsencialidadCota0.buena_limite
#print axioms FOL.EsencialidadCota0.implN
#print axioms FOL.EsencialidadCota0.orN
#print axioms FOL.EsencialidadCota0.forallN
#print axioms FOL.EsencialidadCota0.exN
#print axioms FOL.EsencialidadCota0.truthN
#print axioms FOL.EsencialidadCota0.model_existence_countable_of_wlem
#print axioms FOL.EsencialidadCota0.model_existence_iff_wlem
#print axioms FOL.EsencialidadCota0.consistent_of_sat_of_nnem
#print axioms FOL.EsencialidadCota0.sigma_inconsistent
#print axioms FOL.EsencialidadCota0.nnem_of_consistency
#print axioms FOL.EsencialidadCota0.consistency_iff_nnem
#print axioms FOL.EsencialidadCota0.compactness_of
#print axioms FOL.EsencialidadCota0.ls_down_of
#print axioms FOL.EsencialidadCota0.large_fresh_of
#print axioms FOL.EsencialidadCota0.large_of
#print axioms FOL.EsencialidadCota0.countable_inf_of
#print axioms FOL.EsencialidadCota0.cinco_of_wlem_nnem
