/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Eigenvariable
-- @axiom_system: none
-- @importance: high

import FOL.Eigenvariable

/-!
# `FOL.Lift0` — `Derives₀` respeta el LEVANTAMIENTO de índices

    derives0_lift : Γ ⊢₀ φ  →  ∀ k, Γ.map (liftFormula k) ⊢₀ liftFormula k φ

## Por qué hace falta, y por qué aparece justo ahora

Es la pieza **estructural** que el ensamblaje de Henkin descubre. El argumento clásico llega a

    Γ' ⊢₀ ∃A      y      Γ' ⊢₀ ∀(¬A)

y quiere `⊥`. En un cálculo **finitario** eso pasa obligatoriamente por `elim_ex`, cuya premisa
lateral vive en el contexto **levantado** `A :: Γ'.map (liftFormula 0)`. Hay que llevar allí el
`∀(¬A)`, y para eso hace falta exactamente este lema.

⭐ Una vez dentro, `elim_forall` en `Term.var 0` lo cierra, porque
`substFormula 0 (var 0) (liftFormula 1 (¬A)) = ¬A` — que es `substFormula_lift_var`, abajo.

## ⭐ Sin inducciones propias sobre la sintaxis (D5, 2026-09-26)

Este módulo **era** una copia de `FOL.Eigenvariable` —`absTerm c k` coincide con `liftTerm k` en
todo salvo en la constante `c`—. Desde D5 el núcleo es `absTerm' P` (genérico en un predicado de
símbolos, en `FOL.Eigenvariable`) y `liftTerm k` es su caso **sin símbolos**:

    absFormula'_none : absFormula' (fun _ => False) k f = liftFormula k f     -- §0

⇒ §1-§4 son **corolarios**: mismos nombres, mismos enunciados, sin inducción propia sobre
términos, fórmulas ni derivaciones. Sólo §5 —que no tiene gemelo en `FOL.Eigenvariable`— conserva
las suyas.

⚠️ **Lo que D5 compra, medido**: NO líneas —la vieja nota de ingeniería prometía «~150» y el par de
módulos pasó de 806 a 797 (−56 de código)—, sino **una** inducción de lift/subst/`getAt?`/
`replaceAt` y **un** transporte de 21 casos menos. Quedan otras inducciones sobre los constructores
de `Derives₀` (`Derives1`, `Derives2`, `NDtoLK0`, `Rename`, `Soundness0`…): D5 quita una, no todas.
-/

namespace FOL.Lift0

open FOL.Eigenvariable

-- ============================================================
-- §0 · El caso SIN SÍMBOLOS de `absTerm'` es `liftTerm`
-- ============================================================

theorem absTerm'_none (k : Nat) (t : Term) : absTerm' (fun _ => False) k t = liftTerm k t :=
  absTerm'_eq_lift (fun _ => False) k t (fun _ _ h => h)

theorem absTerms'_none (k : Nat) (ts : List Term) :
    absTerms' (fun _ => False) k ts = liftTerms k ts :=
  absTerms'_eq_lift (fun _ => False) k ts (fun _ _ h => h)

theorem absFormula'_none (k : Nat) (f : Formula) :
    absFormula' (fun _ => False) k f = liftFormula k f :=
  absFormula'_eq_lift (fun _ => False) f k (fun _ _ h => h)

theorem map_absFormula'_none (k : Nat) (Γ : List Formula) :
    Γ.map (absFormula' (fun _ => False) k) = Γ.map (liftFormula k) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, absFormula'_none, ih]

-- ============================================================
-- §1 · Lift contra lift, con `j ≤ k`
-- ============================================================

theorem liftTerm_lift : ∀ (j k : Nat) (_ : j ≤ k) (t : Term),
    liftTerm j (liftTerm k t) = liftTerm (k + 1) (liftTerm j t) := by
  intro j k hjk t
  simpa only [absTerm'_none] using absTerm'_lift (fun _ => False) j k hjk t

theorem liftTerms_lift : ∀ (j k : Nat) (_ : j ≤ k) (ts : List Term),
    liftTerms j (liftTerms k ts) = liftTerms (k + 1) (liftTerms j ts) := by
  intro j k hjk ts
  simpa only [absTerms'_none] using absTerms'_lift (fun _ => False) j k hjk ts

theorem liftFormula_lift : ∀ (f : Formula) (j k : Nat), j ≤ k →
    liftFormula j (liftFormula k f) = liftFormula (k + 1) (liftFormula j f) := by
  intro f j k h
  simpa only [absFormula'_none] using absFormula'_lift (fun _ => False) f j k h

-- ============================================================
-- §2 · Lift contra sustitución, con `v ≤ k`
-- ============================================================

theorem liftTerm_subst : ∀ (v k : Nat) (_ : v ≤ k) (s t : Term),
    liftTerm k (substTerm v s t) = substTerm v (liftTerm k s) (liftTerm (k + 1) t) := by
  intro v k hvk s t
  simpa only [absTerm'_none] using absTerm'_subst (fun _ => False) v k hvk s t

theorem liftTerms_subst : ∀ (v k : Nat) (_ : v ≤ k) (s : Term) (ts : List Term),
    liftTerms k (substTerms v s ts) = substTerms v (liftTerm k s) (liftTerms (k + 1) ts) := by
  intro v k hvk s ts
  simpa only [absTerm'_none, absTerms'_none] using absTerms'_subst (fun _ => False) v k hvk s ts

theorem liftFormula_subst : ∀ (f : Formula) (v k : Nat), v ≤ k → ∀ (s : Term),
    liftFormula k (substFormula v s f) = substFormula v (liftTerm k s) (liftFormula (k + 1) f) := by
  intro f v k h s
  simpa only [absTerm'_none, absFormula'_none] using absFormula'_subst (fun _ => False) f v k h s

-- ============================================================
-- §3 · Navegación
-- ============================================================

theorem lift_getAt? : ∀ (p : Pos) (k : Nat) (f : Formula),
    getAt? (liftFormula k f) p = (getAt? f p).map (liftFormula (k + posDepth p)) := by
  intro p k f
  rw [← absFormula'_none k f, abs'_getAt? (fun _ => False) p k f]
  cases getAt? f p with
  | none => rfl
  | some g => exact congrArg some (absFormula'_none _ g)

theorem lift_replaceAt : ∀ (p : Pos) (k : Nat) (f newSub : Formula),
    replaceAt (liftFormula k f) p (liftFormula (k + posDepth p) newSub)
      = liftFormula k (replaceAt f p newSub) := by
  intro p k f n
  simpa only [absFormula'_none] using abs'_replaceAt (fun _ => False) p k f n

theorem lift_localRule (k : Nat) {A B : Formula} (h : LocalRule A B) :
    LocalRule (liftFormula k A) (liftFormula k B) := by
  simpa only [absFormula'_none] using abs'_localRule (fun _ => False) k h

theorem map_lift_lift (k : Nat) (Γ : List Formula) :
    (Γ.map (liftFormula k)).map (liftFormula 0)
      = (Γ.map (liftFormula 0)).map (liftFormula (k + 1)) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, liftFormula_lift g 0 k (Nat.zero_le _), ih]

-- ============================================================
-- §4 · ⭐ EL LEMA
-- ============================================================

/-- **Debilitamiento bajo levantamiento.** Es `absDerives'` sin símbolos. ⚠️ El `∀ k` va
**dentro**: en `intro_forall` y `elim_ex` la hipótesis inductiva se usa a nivel `k + 1`. -/
theorem derives0_lift {Γ : List Formula} {φ : Formula} (h : Γ ⊢₀ φ) :
    ∀ k : Nat, (Γ.map (liftFormula k)) ⊢₀ liftFormula k φ := by
  intro k
  have h' := absDerives' (fun _ => False) h k
  rwa [map_absFormula'_none, absFormula'_none] at h'

-- ============================================================
-- §5 · La pieza que cierra el `∃`/`∀`
-- ============================================================

mutual
theorem substTerm_lift_var : ∀ (k : Nat) (t : Term),
    substTerm k (Term.var k) (liftTerm (k + 1) t) = t := by
  intro k t
  cases t with
  | var n =>
      by_cases h1 : n < k + 1
      · by_cases h2 : n = k
        · simp [liftTerm, substTerm, h2]
        · simp [liftTerm, substTerm, h1, h2, show ¬ n > k by omega]
      · have e1 : n + 1 ≠ k := by omega
        have e2 : n + 1 > k := by omega
        simp [liftTerm, substTerm, h1, e1, e2]
  | func s ts =>
      simp only [liftTerm, substTerm]
      congr 1
      exact substTerms_lift_var k ts

theorem substTerms_lift_var : ∀ (k : Nat) (ts : List Term),
    substTerms k (Term.var k) (liftTerms (k + 1) ts) = ts := by
  intro k ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_lift_var k t, substTerms_lift_var k ts'⟩
end

/-- ⭐ **`liftFormula (k+1)` se deshace sustituyendo la variable `k` por sí misma.**
Es lo que convierte `∀(¬A)` levantado en `¬A` dentro del contexto de `elim_ex`. -/
theorem substFormula_lift_var : ∀ (f : Formula) (k : Nat),
    substFormula k (Term.var k) (liftFormula (k + 1) f) = f := by
  intro f
  induction f with
  | bottom => intro k; rfl
  | atom p ts => intro k; simp only [liftFormula, substFormula, substTerms_lift_var]
  | eq t u => intro k; simp only [liftFormula, substFormula, substTerm_lift_var]
  | impl a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | «forall» a ih =>
      intro k
      have e : (liftTerm 0 (Term.var k) : Term) = Term.var (k + 1) := by simp [liftTerm]
      simp only [liftFormula, substFormula, e]
      exact congrArg Formula.forall (ih (k + 1))
  | and a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | or a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | ex a ih =>
      intro k
      have e : (liftTerm 0 (Term.var k) : Term) = Term.var (k + 1) := by simp [liftTerm]
      simp only [liftFormula, substFormula, e]
      exact congrArg Formula.ex (ih (k + 1))

/-- ⭐⭐ **`∃A` y `∀¬A` son contradictorios**, en forma finitaria: es el paso que el ensamblaje de
Henkin necesita y que obliga a tener `derives0_lift`. -/
theorem derives0_ex_forall_neg_absurd {Γ : List Formula} {A : Formula}
    (hex : Γ ⊢₀ Formula.ex A) (hall : Γ ⊢₀ Formula.forall (neg A)) :
    Γ ⊢₀ Formula.bottom := by
  refine Derives₀.elim_ex Γ A Formula.bottom hex ?_
  -- en el contexto levantado, `A` es la hipótesis del testigo
  have hlift : (Γ.map (liftFormula 0)) ⊢₀ liftFormula 0 (Formula.forall (neg A)) :=
    derives0_lift hall 0
  have hall' : (A :: Γ.map (liftFormula 0)) ⊢₀ Formula.forall (liftFormula 1 (neg A)) := by
    refine Derives₀.weakening _ _ _ hlift ?_
    intro x hx
    exact List.Mem.tail _ hx
  have hnegA : (A :: Γ.map (liftFormula 0)) ⊢₀ neg A := by
    have := Derives₀.elim_forall _ (liftFormula 1 (neg A)) (Term.var 0) hall'
    rwa [substFormula_lift_var (neg A) 0] at this
  exact Derives₀.elim_impl _ A Formula.bottom hnegA (Derives₀.hyp _ _ (List.Mem.head _))

end FOL.Lift0

#print axioms FOL.Lift0.derives0_lift
#print axioms FOL.Lift0.derives0_ex_forall_neg_absurd
