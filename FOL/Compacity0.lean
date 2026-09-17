/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Canonical0
-- @axiom_system: classical
-- @importance: high

import FOL.Canonical0

/-!
# `FOL.Compacity0` — 🏁 COMPACIDAD y 🏁 LÖWENHEIM–SKOLEM DESCENDENTE, sobre `Derives₀`

    compactness₀          : IsSatisfiable S ↔ (todo subconjunto FINITO de S es satisfacible)
    loewenheim_skolem_down: IsSatisfiable S → IsSatisfiableCountable S

## ⭐ Por qué esto repara algo, y no es adorno

`cuarentena/Compacity.lean` está apartado desde el 2026‑09‑11, y su `compactness_theorem` está
declarado **VACUO** —con esas palabras— en `cuarentena/README.md:90` y en `FOL.lean:89`: *«su
prueba pasaba por `soundness`»*, y la solidez de `Derives` es **falsa** (M‑11).
⇒ `compactness₀` es el mismo teorema con el **SUJETO** cambiado. 🔑 Es el patrón ya escarmentado
del proyecto: *cuando un teorema cae, su prueba suele estar bien — lo que cambia es el sujeto.*
Y de los tres módulos apartados, éste es el único cuyo defecto queda **reparado fuera**.

## ⭐⭐ La compacidad SINTÁCTICA ya estaba metida en la definición

`DerivesSet₀ S f := ∃ Γ : List Formula, (∀ g ∈ Γ, S g) ∧ (Γ ⊢₀ f)` (`FOL/Henkin0.lean:82`): la
derivabilidad desde un **conjunto** pide un contexto **finito** por construcción.
⇒ la mitad difícil de la compacidad no hay que demostrarla: **está en el tipo**. Lo único que hay
que hacer es cruzar `derives0_soundness` con `model_existence_lemma₀`, y son dos `obtain`.

## ⭐ Löwenheim–Skolem descendente: la obstrucción era el ENUNCIADO, no la prueba

⚠️ Sin Mathlib no hay `Cardinal` ni `Countable`. Aquí «numerable» se dice con lo único que hay:

    CountableDom D := ∃ e : Nat → D, ∀ d, ∃ n, e n = d

Y entonces la prueba es **componer dos cosas que ya existían**: el dominio del modelo canónico es
`QuotientDomain T hMax = Quotient (termSetoid T hMax)` (`FOL/Canonical0.lean:247`), y
`natToTerm_surj` (`FOL/Enumeration.lean`) enumera los términos ⇒ `Quotient.mk ∘ natToTerm` enumera
el dominio. 🔑 *El modelo que la completitud construye ya era numerable; lo que faltaba era poder
decirlo.*

⚠️ Y hay un detalle que no es gratis: `IsSatisfiable` esconde el dominio bajo un `∃`, así que la
numerabilidad **no se puede añadir a posteriori** — hay que rehacer `model_existence_lemma₀`
llevándola dentro (`model_existence_countable₀`), y con ella `satisfiable_of_shift`
(`countable_of_shift`). Son ocho líneas, pero son ocho líneas que el enunciado obliga a escribir.

## 📏 Footprint

`[propext, Classical.choice, Quot.sound]`. ⚠️ **Y el `Classical.choice` es el de siempre y está
explicado**: viene de `completeness₀` a través de `model_existence_lemma₀`, y es el `if
IsConsistent₀` Π⁰₁ de `FOL.Lindenbaum0` — el **WKL** (ADR‑041, plan §6.3). No se añade fuerza nueva.
⛔ Y por eso esto **no** es finitario, al revés que `FOL.Finitary0`: es vía W, no vía H.
-/

namespace FOL.Compacity0

open FOL.Henkin0
open FOL.Canonical0
open FOL.Fresh0
open FOL.Lindenbaum0
open FOL.Metamath.Semantics

-- ── §1 · COMPACIDAD ─────────────────────────────────────────────────────────
theorem consistency_of_satisfiable₀ {S : Formula → Prop} (hSat : IsSatisfiable S) :
    IsConsistent₀ S := by
  intro hBot
  obtain ⟨Γ, hΓ, hDer⟩ := hBot
  obtain ⟨D, M, v, hEval⟩ := hSat
  exact FOL.Metamath.Soundness0.derives0_soundness hDer D M v (fun g hg => hEval g (hΓ g hg))

theorem compactness₀ (S : Formula → Prop) :
    Iff (IsSatisfiable S)
        (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) := by
  constructor
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hEval⟩ := hSat
    exact ⟨D, M, v, fun f hf => hEval f (hSub f hf)⟩
  · intro hFin
    refine model_existence_lemma₀ ?_
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    obtain ⟨D, M, v, hEvalΓ⟩ := hFin Γ hΓ
    exact FOL.Metamath.Soundness0.derives0_soundness hDer D M v hEvalΓ

-- ── §2 · LÖWENHEIM–SKOLEM DESCENDENTE ───────────────────────────────────────
/-- «Numerable» sin Mathlib: hay una enumeración suprayectiva. -/
def CountableDom (D : Type) : Prop := ∃ e : Nat → D, ∀ d, ∃ n, e n = d

def IsSatisfiableCountable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D),
    And (CountableDom D) (∀ f, S f → evalFormula M v f)

theorem countable_of_shift {S : Formula → Prop}
    (h : IsSatisfiableCountable (shiftTheory S)) : IsSatisfiableCountable S := by
  obtain ⟨D, M, v, hC, hM⟩ := h
  exact ⟨D, pullback M shift, v, hC,
    fun f hf => (eval_pullback_formula M shift f v).mpr (hM _ ⟨f, hf, rfl⟩)⟩

theorem model_existence_countable₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsSatisfiableCountable S := by
  obtain ⟨T, hMax, hHenkin, hSub⟩ := henkin_completion hCons
  refine countable_of_shift ⟨QuotientDomain T hMax, canonicalModel T hMax, canonicalEnv T hMax,
    ⟨fun n => Quotient.mk (termSetoid T hMax) (FOL.Metamath.Enumeration.natToTerm n), ?_⟩,
    fun f hf => ?_⟩
  · intro d
    obtain ⟨t, ht⟩ := Quotient.exists_rep d
    obtain ⟨n, hn⟩ := FOL.Metamath.Enumeration.natToTerm_surj t
    refine ⟨n, ?_⟩
    show Quotient.mk (termSetoid T hMax) (FOL.Metamath.Enumeration.natToTerm n) = d
    rw [hn]; exact ht
  · exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)

/-- 🏁 **LÖWENHEIM–SKOLEM DESCENDENTE**: toda teoría satisfacible tiene un modelo NUMERABLE. -/
theorem loewenheim_skolem_down {S : Formula → Prop} (hSat : IsSatisfiable S) :
    IsSatisfiableCountable S :=
  model_existence_countable₀ (consistency_of_satisfiable₀ hSat)

end FOL.Compacity0

#print axioms FOL.Compacity0.consistency_of_satisfiable₀
#print axioms FOL.Compacity0.compactness₀
#print axioms FOL.Compacity0.model_existence_countable₀
#print axioms FOL.Compacity0.loewenheim_skolem_down
