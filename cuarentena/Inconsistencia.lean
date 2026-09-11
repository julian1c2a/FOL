/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.FOL
import FOL.MetaRules
import FOL.Semantics

/-!
# ⛔⛔ La EVIDENCIA COMPILADA: `Derives` no admite teorema de solidez

Medido el **2026‑09‑11**. Este fichero está en `cuarentena/` a propósito: **no forma parte de la
librería** (el glob de `lean_lib «FOL»` sólo recorre `FOL/`), así que su `False` no contamina nada.
Compruébalo a mano con `lake env lean cuarentena/Inconsistencia.lean` desde la raíz de
`ROBINSON_PlusPlus`.

## Qué se demuestra aquí

No es «la prueba de `cuarentena/Soundness.lean` tenía un fallo». Es más fuerte:

> **CUALQUIER función de tipo `∀ {Γ f}, (Γ ⊢ f) → satisfies Γ f` demuestra `False`.**

Es decir: el enunciado de solidez para `Derives` **no es demostrable porque es FALSO**, y ninguna
prueba más cuidadosa lo arreglaría.

## Por qué

`Derives` es un `inductive` de **18 constructores**, todos semánticamente válidos. Pero
`FOL/MetaRules.lean` declara **cinco `axiom`s que lo HABITAN** (`imp_intro`, `gen`, `raa`,
`or_elim`, `ex_elim`) — y tienen que ser axiomas, porque sus premisas son **funciones de Lean**, es
decir ocurrencias negativas que Lean rechazaría en un `inductive`.

⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**. Un teorema probado por
`induction` cubre los 18 casos, pero **se aplica a todos los habitantes**. Es el fallo clásico de
`axiom foo : UnInductivo`: rompe la garantía de «no hay basura».

El detonador concreto es `raa`: si `Γ ⊬ A`, la función `Γ ⊢ A → Γ ⊢ ⊥` existe **vacuamente**, luego
`raa` da `Γ ⊢ ¬A`. Con solidez eso obliga a `Γ ⊨ ¬A`, que es falso en cuanto `A` sea verdadera en
algún modelo de `Γ`. Y con `Γ = []` bastan **dos modelos triviales sobre `Unit`**.

## Qué NO dice

* ⚠️ **No dice que `ROBINSON_PlusPlus` sea inconsistente.** Medido: RPP **no importa** `FOL.Soundness`
  ni el barrel raíz `FOL`; sólo `FOL.FOL`, `FOL.MetaRules`, `FOL.Tactics`, `FOL.Deduction` y
  `FOL.Theorems.*`. Su árbol de 131 módulos y la cadena de Gödel no están en contexto inconsistente.
* ⚠️ **No dice que `FOL/Semantics.lean` esté mal.** Está bien, y es útil: es lo que permitió probar
  `prf0_soundness` en `ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.
* ⚠️ **No dice que las meta‑reglas estén mal.** Dicen lo que dicen: `⊢` es una noción metateórica de
  verdad, no una relación de derivabilidad. `Meta/OmegaStrength.lean` mide la otra cara —`⊢` decide
  toda sentencia— y de ahí que **no sea r.e.**

## La salida buena

Enunciar la solidez sobre un cálculo **sin axiomas habitándolo**. `ROBINSON_PlusPlus` tiene uno:
`Prf₀` (17 constructores, **cero** axiomas). `prf0_soundness` está probado, con footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open FOL.Metamath.Semantics

namespace FOL.Cuarentena.Inconsistencia

/-- Modelo trivial sobre `Unit` con TODAS las relaciones falsas. -/
def Mfalse : Model Unit := { func := fun _ _ => (), rel := fun _ _ => False }

/-- Modelo trivial sobre `Unit` con TODAS las relaciones verdaderas. -/
def Mtrue : Model Unit := { func := fun _ _ => (), rel := fun _ _ => True }

/-- Un átomo cualquiera. -/
def P : Formula := Formula.atom "P" []

/-- Con contexto vacío, `contextSatisfies` es trivial. -/
theorem ctx_nil {D : Type} (M : Model D) (v : Nat → D) : contextSatisfies M v [] := by
  intro f hf; cases hf

/-- ⛔⛔ **El resultado.** Cualquier testigo del enunciado de solidez para `Derives` da `False`,
    sin ninguna otra hipótesis. El argumento usa sólo `raa` y dos modelos sobre `Unit`. -/
theorem inconsistencia_de_cualquier_solidez
    (solidez : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢ f) → satisfies Γ f) : False := by
  -- (1) `P` no es derivable del contexto vacío: lo refuta el modelo con relaciones falsas.
  have hnd : ¬ ([] ⊢ P) := fun h => solidez h Unit Mfalse (fun _ => ()) (ctx_nil _ _)
  -- (2) Luego `raa` — cuya premisa es una función de Lean — refuta `P`.
  have hneg : [] ⊢ neg P := FOL.MetaRules.raa (fun h => absurd h hnd)
  -- (3) Pero `P` es verdadera en el modelo con relaciones verdaderas.
  have h := solidez hneg Unit Mtrue (fun _ => ()) (ctx_nil _ _)
  simp only [evalFormula, neg] at h
  exact h trivial

end FOL.Cuarentena.Inconsistencia

/-! ## FOOTPRINT — sólo `raa` y los tres de Lean. Ni un axioma más. -/
#print axioms FOL.Cuarentena.Inconsistencia.inconsistencia_de_cualquier_solidez
