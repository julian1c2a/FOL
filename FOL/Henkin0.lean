/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Lift0
-- @axiom_system: classical
-- @importance: high

import FOL.Lift0

/-!
# `FOL.Henkin0` — **el paso de Henkin**: añadir un testigo preserva la consistencia

⭐⭐ El corazón del ensamblaje de `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2.

    henkin_step_consistent :
        IsConsistent₀ S  →  (c fresca en S y en A)  →
        IsConsistent₀ (S ∪ { (∃A) → A[c] })

Es **donde paga** `derives0_gen_fresh` (ADR‑036). Todo lo demás del ensamblaje —la iteración ω, el
suministro de constantes— es bookkeeping alrededor de este teorema.

## La prueba, en seis pasos

1. Si `S ∪ {H}` fuera inconsistente, hay un `Γ` **finito** con `Γ ⊢₀ ⊥`. Se filtra `H` fuera:
   `Γ' ⊆ S` y `H :: Γ' ⊢₀ ⊥`.
2. `intro_impl` —que aquí **es** el teorema de deducción, porque es un **constructor**— da
   `Γ' ⊢₀ ¬H`.
3. Clásicamente, de `¬(P → Q)` salen `P` y `¬Q` (`neg_impl_left` / `neg_impl_right`, con
   `dne_rule`).
4. ⭐ `c` es fresca en `Γ'` **porque `Γ' ⊆ S`** — y aquí está el punto fino: `derives0_gen_fresh`
   sólo pide frescura en el **contexto finito**, que es justo lo que `DerivesSet₀` entrega.
5. `derives0_gen_fresh` sobre `Γ' ⊢₀ ¬A[c]` da `Γ' ⊢₀ ∀(¬A)`, porque
   `absFormula c 0 (¬A[c]) = ¬A` — ahí se juntan `absFormula_subst`, `absFormula_eq_lift`
   (`c` no aparece en `A`) y `substFormula_lift_var`.
6. `∃A` y `∀¬A` se contradicen (`derives0_ex_forall_neg_absurd`, que es lo que obligó a tener
   `derives0_lift`).

## 🏁 Lo que ESTE módulo no hace — y dónde está ya hecho (2026‑09‑16, ADR‑039)

Este módulo da el **paso**. La **extensión completa** está construida en los dos módulos que
vienen encima:

* `FOL.Fresh0` — el **suministro de constantes frescas** (`shiftTheory`, `cst`, `exists_fresh`);
* `FOL.HenkinLimit0` — la **iteración ω** y el límite (`henLimit_consistent`, `henLimit_witness`).

⚠️⚠️ **Y aquí decía algo que la medición refutó.** El texto anterior era:

> ⚠️ **No construye la extensión completa.** Da el **paso**; falta la iteración ω y, sobre todo,
> el **suministro de constantes frescas** para un `S` arbitrario, que exige meter la teoría en un
> sublenguaje (`FOL.Rename`) y **eso** pasa por descomponer cadenas ⇒ `Classical.choice` por la
> vía del `String` del núcleo.
>
> 🔑 La parte **matemática** está aquí y es finitaria; lo que falta es **combinatoria de nombres**.

Lo del sublenguaje era correcto. Lo de **descomponer cadenas, no**: la construcción no descompone
ninguna — la conservatividad del renombrado se obtiene **mapeando con la inversa** (`invOf`), y el
`Classical.choice` que aparece viene de ahí y de `Exists.choose`, no de leer `String`. Y no era
«combinatoria de nombres»: son **dos** propiedades de `cst` (inyectividad y estar fuera de la
imagen del desplazamiento), tres líneas cada una.
-/

namespace FOL.Henkin0

open FOL.Eigenvariable
open FOL.Lift0

-- ⚠️ `open Classical` SÓLO por el `filter` del paso 1, que necesita `DecidableEq Formula`.
-- `Formula` deriva `BEq` y un `DecidableEq` real es construible (§14 del censo de choice); no se
-- ha hecho porque no es el cuello de botella.
open Classical

/-- Derivabilidad desde un CONJUNTO: existe un contexto **finito** dentro de `S` que lo deriva.
⭐ La compacidad sintáctica está metida en la definición, y es lo que hace que la frescura sólo
haga falta en un contexto finito. -/
def DerivesSet₀ (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ Γ : List Formula, (∀ g, g ∈ Γ → S g) ∧ (Γ ⊢₀ f)

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

def IsConsistent₀ (S : Formula → Prop) : Prop := Not (S ⊢₀* Formula.bottom)

/-- El axioma de Henkin para `A` con testigo la constante `c`. -/
def henkinAx (c : String) (A : Formula) : Formula :=
  Formula.impl (Formula.ex A) (substFormula 0 (Term.func c []) A)

-- ============================================================
-- §1 · Dos pasos clásicos sobre `¬(P → Q)`
-- ============================================================

theorem neg_impl_left {Γ : List Formula} {P Q : Formula}
    (h : Γ ⊢₀ neg (Formula.impl P Q)) : Γ ⊢₀ P := by
  refine Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_)
  have hH : (neg P :: Γ) ⊢₀ Formula.impl P Q := by
    refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
    exact Derives₀.elim_impl _ P Formula.bottom
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ _ Formula.bottom
    (Derives₀.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)) hH

theorem neg_impl_right {Γ : List Formula} {P Q : Formula}
    (h : Γ ⊢₀ neg (Formula.impl P Q)) : Γ ⊢₀ neg Q := by
  refine Derives₀.intro_impl _ _ _ ?_
  have hH : (Q :: Γ) ⊢₀ Formula.impl P Q :=
    Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  exact Derives₀.elim_impl _ _ Formula.bottom
    (Derives₀.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)) hH

-- ============================================================
-- §2 · ⭐ La ecuación que hace funcionar el paso
-- ============================================================

/-- ⭐⭐ **Abstraer `c` en `¬A[c]` devuelve `¬A`.** Es el punto exacto donde encajan las tres
piezas: `absFormula_subst` (conmutación), `absFormula_eq_lift` (`c` no aparece en `A`) y
`substFormula_lift_var` (el lift se deshace). -/
theorem abs_neg_witness (c : String) (A : Formula) (hcA : Not (occursFormula c A)) :
    absFormula c 0 (neg (substFormula 0 (Term.func c []) A)) = neg A := by
  show neg (absFormula c 0 (substFormula 0 (Term.func c []) A)) = neg A
  rw [absFormula_subst c A 0 0 (Nat.le_refl 0), absFormula_eq_lift c A 1 hcA]
  have hc : absTerm c 0 (Term.func c []) = Term.var 0 := by simp [absTerm]
  rw [hc, substFormula_lift_var A 0]

-- ============================================================
-- §3 · ⭐⭐ EL PASO DE HENKIN
-- ============================================================

/-- **Añadir el testigo de Henkin para `A` con una constante fresca preserva la consistencia.**

⚠️ La frescura se pide sobre `S` y sobre `A`, que es lo que la construcción puede garantizar. Y
⭐ basta con eso porque `DerivesSet₀` entrega un contexto **finito**: `derives0_gen_fresh` sólo
necesita frescura ahí. -/
theorem henkin_step_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  -- paso 1 · sacar `H` del contexto
  have hΓ' : ∀ g, g ∈ Γ.filter (fun x => decide (Not (x = henkinAx c A))) → S g := by
    intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  have hsub : ∀ x, x ∈ Γ → x ∈ henkinAx c A :: Γ.filter (fun y => decide (Not (y = henkinAx c A))) := by
    intro x hx
    by_cases heq : x = henkinAx c A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)
  -- paso 2 · `intro_impl` ES el teorema de deducción: es un constructor
  have hnH : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  -- paso 3 · las dos mitades clásicas
  have hex : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.ex A :=
    neg_impl_left hnH
  have hnq : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀
      neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  -- paso 4 · frescura en el contexto FINITO
  have hfresh : ∀ g, g ∈ Γ.filter (fun y => decide (Not (y = henkinAx c A))) →
      Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  -- paso 5 · eigenvariable
  have hall : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  -- paso 6 · `∃A` contra `∀¬A`
  exact hCons ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

end FOL.Henkin0

#print axioms FOL.Henkin0.henkin_step_consistent
