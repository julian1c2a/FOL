/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives0, FOL.Semantics
-- @axiom_system: classical
-- @importance: high

import FOL.Derives0
import FOL.Semantics

/-!
# `FOL.Soundness0` — **la solidez de `Derives₀`**, y lo que se sigue de ella

⭐⭐ **PASO 1 de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`.**

    derives0_soundness : Γ ⊢₀ f → Γ ⊨ f

## Por qué existe, y lo que aquí se leyó al revés

✏️ **2026‑10‑03 (por ADR‑114 §2 y ADR‑115 de RPP, del 2026‑10‑02) — esta sección decía que la solidez de `Derives` era
FALSA**: `FOL/Inconsistencia.lean` compilaba `False` a partir de cualquier teorema de esa forma (footprint
`[propext, FOL.MetaRules.raa]`), y se atribuía a M‑11 («los cuatro axiomas de `MetaRules` habitan el tipo,
así que la inducción sobre sus 22 constructores no cubre todos los habitantes»). **Era al revés.** El
recursor cubre a TODO habitante, también a los que fabrica un `axiom`: la solidez de `Derives` era
demostrable, y lo que daba `False` junto a ella era el `axiom raa`, refutable
(`FOL.Inconsistencia.raa_refutable`). Borrado `FOL/MetaRules.lean`, la solidez de `Derives` está en el build:
`FOL.Inconsistencia.derives_soundness`, que pasa por `derives_to_derives0` y por este módulo.

`Derives₀` tiene **cero habitantes‑axioma** (ADR‑033): es un cálculo sin postulados, y aquí está su
solidez. Sigue siendo el sujeto de FOL⁼.

⚠️ **Y no es contabilidad**: sin solidez, una completitud no dice nada. `Γ ⊢₀ f ↔ Γ ⊨ f` sólo
tiene contenido con **las dos** direcciones. ✏️ 2026‑10‑03: aquí se decía que «hasta el 2026‑09‑14 el
repo no tenía ninguna para FOL⁼». La de `Derives` (`FOL.Metamath.Soundness.soundness`, 18 casos, válida)
estuvo en el build hasta el 2026‑09‑11, cuando se apartó a `cuarentena/` por tenerla por falsa; lo cierto
es que del 2026‑09‑11 al 2026‑09‑14 el build no tuvo ninguna.

## Lo que sale como corolario, y es lo que importa

| | |
|---|---|
| 🏁 **`derives0_consistent`** | `¬ ([] ⊢₀ ⊥)` — **la primera prueba de CONSISTENCIA de un cálculo de FOL⁼ en el build desde que `consistency_of_satisfiable` (válida, vía `soundness`) salió de él el 2026‑09‑11** |
| 🏁🏁 **`derives0_not_complete`** | `Derives₀` **NO decide toda fórmula**: hay `A` con `[] ⊬₀ A` y `[] ⊬₀ ¬A` |

⭐⭐ El segundo es el que certifica que el **Paso 0 hizo lo que tenía que hacer**: `Derives₀` **no
decide toda fórmula**, y aquí está la prueba: dos modelos sobre `Unit`, uno con todas las relaciones
verdaderas y otro con todas falsas. ✏️ 2026‑10‑03: el contraste se hacía con `Derives`, del que se
decía que era sintácticamente **completo** porque `raa` tomaba una función de Lean («lo que no prueba
lo refuta») y que por eso no podía ser sujeto (ADR‑024, **M‑10**: completo ⇒ no r.e.). Eso valía sólo
con `raa` postulado, y `raa` era refutable; borrado `FOL/MetaRules.lean` (ADR‑115 de RPP), `Derives`
tampoco decide toda fórmula (`FOL.Inconsistencia.derives_not_P`, `derives_not_negP`).

⇒ 🔑 **`Derives₀` es sólido, consistente y no decide todo.** Es decir: es un cálculo del que se
puede decir algo, que es exactamente lo que el plan necesitaba.

## Procedencia

⭐ Los **18 casos originales** se rescataron del ya borrado `cuarentena/Soundness.lean`: la prueba **era correcta
caso por caso** —es deducción natural intuicionista y cada regla es semánticamente válida—.
✏️ 2026‑10‑03: aquí se decía que «lo que la invalidaba era el tipo sobre el que inducía». No la
invalidaba nada: era una inducción válida, y lo que la hacía chocar con `False` era el `axiom raa`
del entorno (ADR‑114 §2 de RPP). 🔑 *Cuando un teorema verdadero choca con un axioma, lo falso es el
axioma.* Cambiar el sujeto a `Derives₀` fue bueno por otra razón: es un cálculo sin postulados.

Los **tres nuevos** —`dne_rule`, `dne_schema`, `forall_not_ex_not`, constructores desde la D‑2 de ADR‑028— son
los únicos que necesitan **lógica clásica** en el metanivel (`Classical.byContradiction`), y por eso
`Classical.choice` aparece en el footprint. Es legítimo y esperado: la semántica es clásica.
⚠️ Sin Mathlib **no hay `by_contra`**; se usa `Classical.byContradiction` a mano.
-/

namespace FOL.Metamath.Soundness0

open FOL.Metamath.Semantics

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- La solidez
-- ============================================================

/-- **Solidez de `Derives₀`**: lo derivable es válido. Inducción sobre los **21** constructores
(`Derives₀` **no tiene habitantes‑axioma**, ADR‑033; si un postulado la contradijera, lo falso sería
el postulado: ADR‑114 §2 de RPP).
✏️ 2026‑10‑03: decía «legítima porque…»; la inducción es legítima siempre (ADR‑114 §2 de RPP). -/
theorem derives0_soundness {Γ f} (h : Γ ⊢₀ f) : Γ ⊨ f := by
  induction h with
  | hyp Γ' f' hIn =>
    intro D M v hΓ
    exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro D M v hΓ hA
    apply ih D M v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A =>
    intro D M v hΓ
    exact (ih_impl D M v hΓ) (ih_A D M v hΓ)
  | intro_and Γ' A B _ _ ihA ihB =>
    intro D M v hΓ
    exact ⟨ihA D M v hΓ, ihB D M v hΓ⟩
  | elim_and_l Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).left
  | elim_and_r Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).right
  | intro_or_l Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inl (ih D M v hΓ)
  | intro_or_r Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inr (ih D M v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro D M v hΓ
    cases ih_or D M v hΓ with
    | inl hA =>
      apply ih_A D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | intro_forall Γ' A _ ih =>
    intro D M v hΓ d
    have hCtx : contextSatisfies M (shiftEnv v d) (Γ'.map (liftFormula 0)) :=
      (contextSatisfies_lift_zero M v d).mpr hΓ
    exact ih D M (shiftEnv v d) hCtx
  | elim_forall Γ' A t _ ih =>
    intro D M v hΓ
    have hForall := ih D M v hΓ
    have hEval := hForall (evalTerm M v t)
    exact (eval_substFormula_zero M v t A).mpr hEval
  | intro_ex Γ' A t _ ih =>
    intro D M v hΓ
    have hA := ih D M v hΓ
    have hEval := (eval_substFormula_zero M v t A).mp hA
    exact ⟨evalTerm M v t, hEval⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro D M v hΓ
    have hEx := ih_ex D M v hΓ
    obtain ⟨d, hd⟩ := hEx
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    have hB := ih_B D M (shiftEnv v d) hCtx
    exact (eval_liftFormula_zero M v d B).mp hB
  | bot_elim Γ' A _ ih =>
    intro D M v hΓ
    have hBot := ih D M v hΓ
    contradiction
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro D M v hΓ
    apply ih D M v
    intro g hg
    exact hΓ g (hSubset g hg)
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro D M v hΓ
    have hEvalF := ih D M v hΓ
    have hSubEq : ∀ v', evalFormula M v' sub ↔ evalFormula M v' sub' :=
      fun v' => rule_soundness M h_rule v'
    have hEquiv := replaceAt_soundness M v h_get hSubEq
    rw [h_replace]
    exact hEquiv.mp hEvalF
  -- ⚠️ Los TRES siguientes son los constructores clásicos que la D‑2 de ADR‑028 añadió, y los únicos que
  -- necesitan lógica clásica en el METANIVEL. Sin Mathlib no hay `by_contra`.
  | dne_rule Γ' A _ ih =>
    intro D M v hΓ
    exact Classical.byContradiction (ih D M v hΓ)
  | dne_schema Γ' A =>
    intro D M v _ hnn
    exact Classical.byContradiction hnn
  | forall_not_ex_not Γ' A =>
    intro D M v _ hnf
    apply Classical.byContradiction
    intro hne
    apply hnf
    intro d
    apply Classical.byContradiction
    intro hnd
    exact hne ⟨d, hnd⟩
  | refl Γ' t =>
    intro D M v _
    rfl
  | subst Γ' t1 t2 f' _ _ ih_eq ih_f =>
    intro D M v hΓ
    have heq := ih_eq D M v hΓ
    have hf := ih_f D M v hΓ
    have h1 := (eval_substFormula_zero M v t1 f').mp hf
    have heq_eval : evalTerm M v t1 = evalTerm M v t2 := heq
    rw [heq_eval] at h1
    exact (eval_substFormula_zero M v t2 f').mpr h1

-- ============================================================
-- Dos modelos triviales sobre `Unit`, y lo que se saca de ellos
-- ============================================================

/-- Modelo sobre `Unit` con **todas** las relaciones verdaderas. -/
def Mtrue : Model Unit := ⟨fun _ _ => (), fun _ _ => True⟩

/-- Modelo sobre `Unit` con **todas** las relaciones falsas. -/
def Mfalse : Model Unit := ⟨fun _ _ => (), fun _ _ => False⟩

/-- 🏁 **CONSISTENCIA de `Derives₀`** — la primera de un cálculo de FOL⁼ en el build desde que
`consistency_of_satisfiable` (válida, vía `soundness`) salió de él el 2026‑09‑11.
✏️ 2026‑10‑03: aquí se decía que para `Derives` esto no se podía, por falsa su solidez. Era al revés:
con el `axiom raa` en el entorno, Lean era inconsistente; borrado (ADR‑115 de RPP), `Derives` es
consistente por `FOL.Inconsistencia.derives_to_derives0` y este teorema. -/
theorem derives0_consistent : ¬ (([] : List Formula) ⊢₀ Formula.bottom) := by
  intro h
  exact derives0_soundness h Unit Mtrue (fun _ => ()) (fun _ hf => absurd hf (List.not_mem_nil))

/-- Una fórmula atómica testigo. -/
def P : Formula := Formula.atom ['P'] []

theorem derives0_not_derives_P : ¬ (([] : List Formula) ⊢₀ P) := by
  intro h
  exact derives0_soundness h Unit Mfalse (fun _ => ()) (fun _ hf => absurd hf (List.not_mem_nil))

theorem derives0_not_derives_negP : ¬ (([] : List Formula) ⊢₀ neg P) := by
  intro h
  have := derives0_soundness h Unit Mtrue (fun _ => ()) (fun _ hf => absurd hf (List.not_mem_nil))
  exact this trivial

/-- 🏁🏁 **`Derives₀` NO es sintácticamente completo**: hay una fórmula que no demuestra y cuya
negación tampoco.

⭐⭐ **Y esto es lo que certifica que el Paso 0 sirvió para algo**: un cálculo consistente que
contenga a Q y fuese completo no sería r.e. (Gödel I). (M‑10 era la regla de la capa `⊢` de RPP,
retirada con ADR‑115.) ✏️ 2026‑10‑03: aquí se decía
que `Derives` sí era sintácticamente completo, porque `raa` tomaba una función de Lean. Lo era sólo con
`raa` postulado, y `raa` era refutable (`FOL.Inconsistencia.raa_refutable`); sin él, tampoco lo es
(`FOL.Inconsistencia.derives_not_P`, `derives_not_negP`). -/
-- ⚠️ `And` y `Not` EXPLÍCITOS, no `∧` ni `¬`: en este fichero la notación de FOL⁼ los tiene
-- tomados (`∧` es `Formula.and` y `¬ ` es `neg`), y el enunciado es META, no objeto.
-- Es una trampa de notación conocida, y vuelve a morder aquí.
theorem derives0_not_complete :
    ∃ A : Formula, And (Not (([] : List Formula) ⊢₀ A)) (Not (([] : List Formula) ⊢₀ neg A)) :=
  ⟨P, derives0_not_derives_P, derives0_not_derives_negP⟩

end FOL.Metamath.Soundness0

export FOL.Metamath.Soundness0 (derives0_soundness derives0_consistent derives0_not_complete)

-- ⚠️ CRITERIO DE ACEPTACIÓN del Paso 1 (`PLAN-COMPLETITUD-FINITISTA.md` §9): footprint sin
-- ningún axioma del proyecto. `Classical.choice` sí, y es legítimo: la semántica es clásica.
#print axioms FOL.Metamath.Soundness0.derives0_soundness
#print axioms FOL.Metamath.Soundness0.derives0_consistent
#print axioms FOL.Metamath.Soundness0.derives0_not_complete
