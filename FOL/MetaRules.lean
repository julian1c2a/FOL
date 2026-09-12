/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.FOL

/-!
# Meta-reglas de deducción (capa ω-meta sobre `Derives`)

Reglas de deducción en **formulación meta-función**, distintas de los
constructores de `Derives` (que usan hipótesis-en-contexto, `A :: Γ ⊢ B`).
Aquí las hipótesis son funciones Lean (`Γ ⊢ A → Γ ⊢ B`) y, en `gen`, la
**ω-regla** (`∀ n : Term, Γ ⊢ A[n] → Γ ⊢ ∀A`).

**Estatus**: `imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim` son **axiomas**.

⚠️⚠️ **DOCTRINA CORREGIDA EL 2026‑09‑12 (A‑4).** Este docstring decía que **los seis**
«no son derivables … **tienen que ser axiomas**». **Es falso para la mitad**, y está
**medido compilando**:

| | cuáles | por qué |
|---|---|---|
| ⛔ **TIENEN que ser `axiom`** | `imp_intro`, `raa`, `or_elim`, `ex_elim` | su premisa es `Γ ⊢ A → Γ ⊢ B`, una **ocurrencia NO POSITIVA**. El kernel lo rechaza literalmente: *«arg #3 … has a non positive occurrence of the datatypes being declared»* |
| ✅ **PODRÍAN ser CONSTRUCTORES** | `gen`, `dne` | son *shapes* legales. Un `inductive` que los incluya **typechequea** (`EXIT 0`, recursor sin axiomas) — **`gen` incluido**, pese a su premisa infinitaria sobre `Term` |

🔑 **El criterio que de verdad separa no es «meta‑regla» sino PREMISA‑FUNCIÓN.** Y de ahí
que «inevitable» fuese falso: ver la decisión abierta **D‑2** en `AXIOMS.md` §2 (mover los
evitables a constructores dejaría **13 → 9** axiomas sin tocar la fuerza del cálculo).

⛔⛔ **AVISO CAPITAL, MEDIDO EL 2026‑09‑11 — estos axiomas HABITAN un tipo
INDUCTIVO, y eso tiene una consecuencia que este docstring negaba.**

`Derives` es un `inductive` de 18 constructores. Estos **seis** axiomas producen habitantes suyos
que **no son aplicaciones de constructor** — y ⚠️ **no son los únicos**: el censo corregido el
2026‑09‑12 da **OCHO en esta librería** (falta un **segundo `dne`** en `Theorems/Neg.lean:57`, en
forma de esquema, y `forall_not_impl_exists_not` en `Theorems/Quantifiers.lean:115`) y **DOCE**
contando `ROBINSON_PlusPlus`. Por tanto:

> ⛔ **NINGÚN teorema sobre `Derives` puede demostrarse por INDUCCIÓN.** La
> inducción cubre los 18 constructores, pero el enunciado cuantifica sobre
> **todos** los habitantes, y los que producen estos axiomas no están cubiertos.

Eso no es una precaución teórica: `cuarentena/Soundness.lean` lo hacía, y de ahí
sale **`False` sin hipótesis** (`cuarentena/Inconsistencia.lean`, compilado).

⚠️ Y por eso **se ha retirado la frase que decía que el sistema resultante es
«sólido y completo relativo a ℕ»**: la solidez es precisamente lo que NO se
tiene. `ROBINSON_PlusPlus/Meta/OmegaStrength.lean` mide la otra cara: con `raa`,
`⊢` **decide toda sentencia** (lo que no prueba, lo refuta) ⇒ no es r.e.

⚠️ `gen` **no es la ω-regla**: su premisa recorre **todo `Term`**, no sólo los
numerales — premisa estrictamente mayor, luego regla más débil. La fuerza viene
de `raa` e `imp_intro`, que toman **funciones de Lean**.

Los constructores finitarios y sólidos para *todo* modelo son los 18 de
`Derives`; su solidez sí es demostrable, y lo está —para el cálculo de Hilbert
`Prf₀`, que **no tiene ningún axioma habitándolo**— en
`ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.

El resto (`mp`, `and_intro`, `and_elim_*`, `or_intro_*`, `false_elim`,
`ex_intro`, `iff_mp`, `iff_mpr`) son **wrappers derivables** de los
constructores de `Derives` (no axiomas).

**Procedencia**: extraídos de `ROBINSON_PlusPlus/Minimal/Axioms.lean`
(2026-06-12) — eran lógica pura de FOL= viviendo en el módulo de axiomas
aritméticos. `Minimal.Axioms` los re-exporta para compatibilidad. Ver ADR-008.
-/

namespace FOL.MetaRules

/-- Modus ponens: from `Γ ⊢ A ⇒ B` and `Γ ⊢ A`, conclude `Γ ⊢ B`. -/
def mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B h1 h2

/-- Implication introduction (meta-función → implicación object).
    **Meta-axioma** ω: sólido relativo al modelo estándar. -/
axiom imp_intro {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)

/-- Generalización universal: de `Γ ⊢ A[t]` **para todo TÉRMINO `t`** concluye `Γ ⊢ ∀A`.
    **Meta-axioma**: no derivable de `Derives.intro_forall` (que es finitario).

    ⚠️⚠️ **CORRECCIÓN 2026-09-11 — esto NO es la ω-regla, y llamarlo así confunde la fuerza del
    cálculo.** La ω-regla toma como premisa `A[n̄]` para cada **NUMERAL**; ésta la toma para
    **todo `Term`** — variables libres y aplicaciones de función incluidas. Su premisa es
    **estrictamente mayor**, así que como **regla de inferencia** es **MÁS DÉBIL** que la ω-regla:
    está más cerca de la generalización ordinaria con variable propia. (Su *soundness* sí depende de
    que el modelo esté generado por términos, que es lo que sugería el nombre.)

    ⛔ **De dónde viene de verdad la fuerza del cálculo**: de `imp_intro` y `raa`, que toman como
    premisa una **función de Lean**. Si `Γ ⊬ A`, esa función existe **vacuamente** ⇒ `raa` da
    `Γ ⊢ ¬A`. Consecuencia **medida** en `ROBINSON_PlusPlus/Meta/OmegaStrength.lean`:

        derives_completo (A) : (axioms ⊢ A) ∨ (axioms ⊢ ¬A)

    es decir, **`⊢` es sintácticamente COMPLETO**: decide toda sentencia, luego **no es r.e.** y
    **no puede ser el sujeto de un teorema de incompletitud**. -/
axiom gen {Γ : List Formula} {A : Formula} (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) :
    Γ ⊢ Formula.forall A

/-- Reducción al absurdo (clásica): de `Γ ⊢ A → ⊥` concluye `Γ ⊢ ¬A`.
    **Meta-axioma** ω. -/
axiom raa {Γ : List Formula} {A : Formula} (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A

/-- **Eliminación de doble negación** (lógica CLÁSICA): de `Γ ⊢ ¬¬A` concluye
    `Γ ⊢ A`. **Meta-axioma** — NO derivable de las reglas anteriores (todas
    intuicionistamente válidas). Convierte el sistema en clásico, sólido para el
    modelo estándar ℕ (coherente con la lectura ω-lógica "demostrabilidad =
    verdad en ℕ"). Necesario p. ej. para la segunda mitad del Primer Teorema de
    Gödel (`⊬ ¬G`). -/
axiom dne {Γ : List Formula} {A : Formula} (h : Γ ⊢ neg (neg A)) : Γ ⊢ A

/-- Conjunction introduction (wrapper de `Derives.intro_and`). -/
def and_intro {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ A) (h2 : Γ ⊢ B) : Γ ⊢ (A ∧ B) :=
  Derives.intro_and Γ A B h1 h2

/-- Left conjunction elimination (wrapper de `Derives.elim_and_l`). -/
def and_elim_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ A :=
  Derives.elim_and_l Γ A B h

/-- Right conjunction elimination (wrapper de `Derives.elim_and_r`). -/
def and_elim_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ B :=
  Derives.elim_and_r Γ A B h

/-- Left disjunction introduction (wrapper de `Derives.intro_or_l`). -/
def or_intro_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_l Γ A B h

/-- Right disjunction introduction (wrapper de `Derives.intro_or_r`). -/
def or_intro_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ B) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_r Γ A B h

/-- Disjunction elimination (case split meta-nivel).
    **Meta-axioma** ω: usa hipótesis meta-función `Γ ⊢ A → Γ ⊢ C`. -/
axiom or_elim {Γ : List Formula} {A B C : Formula}
    (h : Γ ⊢ (A ∨ B)) (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C

/-- False elimination / ex falso (wrapper de `Derives.bot_elim`). -/
def false_elim {Γ : List Formula} {A : Formula} (h : Γ ⊢ ⊥) : Γ ⊢ A :=
  Derives.bot_elim Γ A h

/-- Existential introduction (wrapper de `Derives.intro_ex`). -/
def ex_intro {Γ : List Formula} {A : Formula} (t : Term)
    (h : Γ ⊢ substFormula 0 t A) : Γ ⊢ Formula.ex A :=
  Derives.intro_ex Γ A t h

/-- Existential elimination (extracción de testigo meta-nivel).
    **Meta-axioma** ω: usa hipótesis meta-función. -/
axiom ex_elim {Γ : List Formula} {A C : Formula}
    (h : Γ ⊢ Formula.ex A)
    (cont : ∀ t : Term, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C

/-- Forward direction of biconditional (wrapper). -/
def iff_mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B (Derives.elim_and_l Γ (A ⇒ B) (B ⇒ A) h1) h2

/-- Backward direction of biconditional (wrapper). -/
def iff_mpr {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ B) : Γ ⊢ A :=
  Derives.elim_impl Γ B A (Derives.elim_and_r Γ (A ⇒ B) (B ⇒ A) h1) h2

end FOL.MetaRules
