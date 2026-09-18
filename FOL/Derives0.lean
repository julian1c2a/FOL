/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: none
-- @importance: high

import FOL.FOL

/-!
# `FOL.Derives0` — el cálculo del que SÍ se puede hablar

⭐⭐ **PASO 0 de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`.**

## Por qué existe

`Derives` no sirve como **sujeto** de ningún teorema metateórico, y está medido:

1. ⛔ **Es sintácticamente COMPLETO**: `raa` toma una **función de Lean**, así que si `Γ ⊬ A` esa
   función existe **vacuamente** y `Γ ⊢ ¬A`. Todo contexto decide toda fórmula, en tres líneas
   (`../ROBINSON_PlusPlus/sondeos/HenkinSaleDeRaa.lean`). ⇒ **no es r.e.**
2. ⛔ **No es SÓLIDO**: `cuarentena/Inconsistencia.lean` compila `False` a partir de cualquier
   teorema de solidez para `Derives`, con footprint `[propext, FOL.MetaRules.raa]`.
3. ⛔ **No admite INDUCCIÓN** (**M‑11**, ADR‑029, y es **permanente**): los cuatro axiomas de
   `FOL/MetaRules.lean` habitan el tipo y no son aplicaciones de constructor.

⇒ Es ADR‑024 otra vez: **`⊢` es la herramienta de trabajo, no el sujeto**.

## Qué es `Derives₀`

Los **21** constructores de `Derives` (que son 22) **menos `gen_rule`**, y **sin** los cuatro
axiomas de `MetaRules`. Es decir: **deducción natural clásica de primer orden con igualdad**,
finitaria, y **con cero habitantes‑axioma**.

| | `Derives` | `Derives₀` |
|---|---|---|
| constructores | 22 | **21** |
| axiomas que lo habitan | **4** (suelo permanente, ADR‑029) | **0** |
| ¿`induction`? | ⛔ **nunca** | ✅ **sí** |
| ¿ω‑regla `gen_rule`? | sí | ❌ **no** — premisa infinitaria |
| ¿sintácticamente completo? | ⛔ sí (patología) | se espera que no, y por eso vale |

### ⚠️ Por qué se quita también `gen_rule`

`gen_rule : (∀ n : Term, Γ ⊢ A[n]) → Γ ⊢ ∀A` tiene **premisa infinitaria**: es la ω‑regla sobre
términos. Un cálculo **finitario** no la lleva. La introducción de `∀` la da `intro_forall`
—la regla de la eigenvariable, con De Bruijn—, que es la estándar.

⭐ **Y el coste para lo que ya existe es CERO**: `cuarentena/Completeness.lean` usa **14**
constructores distintos de `Derives` y **`gen_rule` no está entre ellos** (medido). El desarrollo
de completitud ya vive dentro del fragmento finitario.

### ⚠️ Lo que NO se pierde al quitar los cuatro axiomas

**Sólo la fuerza META.** Medido en `../ROBINSON_PlusPlus/sondeos/DerivesSinMetaReglas.lean`: el
inductivo pelado ya tiene las versiones **objeto** de las cuatro, las seis con footprint
`[propext]`.

| meta‑regla (axioma, premisa‑FUNCIÓN) | equivalente OBJETO aquí |
|---|---|
| `imp_intro (Γ ⊢ A → Γ ⊢ B)` | `Derives₀.intro_impl` |
| `raa (Γ ⊢ A → Γ ⊢ ⊥)` | `Derives₀.intro_impl` con `B := ⊥` |
| `or_elim` | `Derives₀.elim_or` |
| `ex_elim` | `Derives₀.elim_ex` |
| `dne` | `Derives₀.dne_rule` / `Derives₀.dne_schema` |

## ⭐ Y esto NO toca a ROBINSON_PlusPlus

`Derives₀` es un objeto **NUEVO**, no un reemplazo. El puente va en **una** dirección:

    derives0_to_derives : Γ ⊢₀ f → Γ ⊢ f

RPP sigue con `Derives` y sus meta‑reglas exactamente igual —`gen` 323 usos, los cuatro axiomas
320, los constructores `Derives.*` 164 (censo del 2026‑09‑12)—: **ni una cita cambia**. Y este
módulo entra por el barrel `FOL`, que RPP **no importa**.

⇒ Es mucho más barato que la «reparación de fondo» de `cuarentena/README.md` §8 (partir
`Derives`/`DerivesW`), y da lo mismo para lo que hace falta: un cálculo sobre el que **M‑11 no
aplica**.

## ⬜ Lo que viene después (y va en este orden)

1. ⚠️⚠️ **`derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`** — el agujero de verdad del repo. Plantilla:
   `prf0_soundness`. Sin solidez, una completitud no dice nada.
2. El lema de **renombrado** sobre derivaciones, que desbloquea la extensión de Henkin de verdad.
3. Portar `cuarentena/Completeness.lean` a `Derives₀`.
-/

/-- **Deducción natural clásica de FOL⁼, finitaria y sin habitantes‑axioma.**
Los 21 constructores de `Derives` menos la ω‑regla `gen_rule`. ⇒ **se puede inducir sobre él**. -/
inductive Derives₀ {Sym : Type} : List (FormulaG Sym) → FormulaG Sym → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives₀ Γ f

  -- Reglas estándar de Deducción Natural
  | intro_impl : ∀ Γ A B, Derives₀ (A :: Γ) B → Derives₀ Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives₀ Γ (.impl A B) → Derives₀ Γ A → Derives₀ Γ B

  -- Conjunción
  | intro_and  : ∀ Γ A B, Derives₀ Γ A → Derives₀ Γ B → Derives₀ Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives₀ Γ (.and A B) → Derives₀ Γ A
  | elim_and_r : ∀ Γ A B, Derives₀ Γ (.and A B) → Derives₀ Γ B

  -- Disyunción
  | intro_or_l : ∀ Γ A B, Derives₀ Γ A → Derives₀ Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives₀ Γ B → Derives₀ Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives₀ Γ (.or A B) → Derives₀ (A :: Γ) C → Derives₀ (B :: Γ) C →
      Derives₀ Γ C

  -- Cuantificadores. ⚠️ `intro_forall` ES la regla de la eigenvariable: el contexto se LEVANTA,
  -- y eso es lo que hace las veces de «constante fresca» sin ampliar el lenguaje.
  | intro_forall : ∀ Γ A, Derives₀ (Γ.map (liftFormula 0)) A → Derives₀ Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives₀ Γ (.forall A) → Derives₀ Γ (substFormula 0 t A)
  | intro_ex : ∀ Γ A t, Derives₀ Γ (substFormula 0 t A) → Derives₀ Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives₀ Γ (.ex A) →
      Derives₀ (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives₀ Γ B

  -- Ex falso quodlibet
  | bot_elim : ∀ Γ A, Derives₀ Γ ⊥ → Derives₀ Γ A

  -- Debilitamiento
  | weakening : ∀ Γ Γ' f, Derives₀ Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives₀ Γ' f

  -- Reescritura en subexpresión exacta
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derives₀ Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derives₀ Γ f'

  -- Clásica. ⚠️ `gen_rule` NO está: su premisa es infinitaria (ω‑regla).
  | dne_rule : ∀ Γ A, Derives₀ Γ (neg (neg A)) → Derives₀ Γ A
  | dne_schema : ∀ Γ A, Derives₀ Γ (.impl (neg (neg A)) A)
  | forall_not_ex_not : ∀ Γ A, Derives₀ Γ (.impl (neg (.forall A)) (.ex (neg A)))

  -- Igualdad
  | refl  : ∀ Γ t, Derives₀ Γ (.eq t t)
  | subst : ∀ Γ t₁ t₂ f, Derives₀ Γ (.eq t₁ t₂) → Derives₀ Γ (substFormula 0 t₁ f) →
      Derives₀ Γ (substFormula 0 t₂ f)

infix:50 " ⊢₀ " => Derives₀

/-- **El encaje**: todo lo que `Derives₀` deriva, `Derives` lo deriva.

⭐ **Y esta prueba es la demostración de que el Paso 0 funciona**: es una **inducción sobre
`Derives₀`**, que sobre `Derives` sería ilegítima (M‑11). Cada caso es su constructor homónimo.

⚠️ La recíproca **NO vale, y a propósito**: `Derives` tiene los cuatro habitantes‑axioma y la
ω‑regla. Toda la metateoría vive de este lado; `Derives` se queda como herramienta. -/
theorem derives0_to_derives : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢₀ f) → (Γ ⊢ f) := by
  intro Γ f h
  induction h with
  | hyp Γ f hmem => exact Derives.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives.weakening Γ Γ' f ih hsub
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact Derives.rewrite_at Γ f f' p sub sub' ih hget hrule heq
  | dne_rule Γ A _ ih => exact Derives.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives.forall_not_ex_not Γ A
  | refl Γ t => exact Derives.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives.subst Γ t₁ t₂ f ih1 ih2

/-- Las versiones OBJETO de las meta‑reglas que en `Derives` **tienen** que ser axiomas.
Aquí son teoremas de una línea, y por eso `Derives₀` no pierde ninguna REGLA: sólo pierde la
fuerza **meta** (la premisa‑función), que es exactamente la patología. -/
theorem derives0_raa {Γ : List Formula} {A : Formula}
    (h : Derives₀ (A :: Γ) Formula.bottom) : Γ ⊢₀ neg A :=
  Derives₀.intro_impl Γ A Formula.bottom h

-- ⚠️ CRITERIO DE ACEPTACIÓN del Paso 0 (`PLAN-COMPLETITUD-FINITISTA.md` §9): el recursor no
-- puede depender de ningún axioma del proyecto. Se imprime en el build, a la vista.
#print axioms Derives₀.rec
#print axioms derives0_to_derives
#print axioms derives0_raa
