# `cuarentena/` — ⛔ **tres módulos apartados el 2026‑09‑11**

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros

> ## `soundness : Γ ⊢ f → Γ ⊨ f` es **FALSO**, y junto con `raa` demostraba **`False` sin hipótesis**
>
> No es un fallo en la prueba. El **enunciado** no es demostrable, porque no es verdad.
> Evidencia compilada: **`cuarentena/Inconsistencia.lean`**.

---

## 1 · Qué se apartó, y por qué

| módulo | venía de | por qué |
|---|---|---|
| `Soundness.lean` | `FOL/Soundness.lean` | contiene el teorema falso |
| `Compacity.lean` | `FOL/Compacity.lean` | `compactness_theorem` se apoya en él |
| `Theorems_Soundness.lean` | `FOL/Theorems/Soundness.lean` | reexportaba `soundness` |

Y `FOL.lean` —el barrel raíz— importaba `FOL.MetaRules` **y** `FOL.Soundness` a la vez:
⇒ **`import FOL` era un módulo inconsistente.** Ya no los importa.

## 2 · La causa, exacta

`Derives` (`FOL/FOL.lean:165`) es un `inductive` de **18 constructores**, todos semánticamente
válidos — es deducción natural intuicionista. La solidez para ellos es cierta y su prueba era
correcta caso por caso.

Pero `FOL/MetaRules.lean` declara **cinco `axiom`s que HABITAN `Derives`**:

    axiom imp_intro (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)
    axiom gen       (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) : Γ ⊢ ∀A
    axiom raa       (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A
    axiom or_elim   …
    axiom ex_elim   …

⚠️ **Y tienen que ser axiomas**: sus premisas son **funciones de Lean**, o sea ocurrencias negativas
de `Derives` en su propio constructor. Lean rechaza ese `inductive`. No es un descuido: no hay
alternativa dentro del tipo.

⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**, y entonces:

> ⛔ **Ningún teorema sobre `Derives` puede demostrarse por `induction`.** La inducción cubre los
> 18 constructores; el enunciado cuantifica sobre **todos** los habitantes.

Es el fallo clásico de `axiom foo : UnInductivo`: rompe la garantía de «no hay basura» del tipo.

**Medido**: `soundness` era **el único** teorema de todo `FOL/` probado por inducción sobre
`Derives` (`grep -rn "induction h with" FOL/` → una sola línea). El radio del daño es ése.

## 3 · El detonador, en tres pasos

Con contexto **vacío** y dos modelos triviales sobre `Unit`:

1. `P` no es derivable de `[]` — lo refuta el modelo con todas las relaciones **falsas**, vía la
   propia solidez.
2. Luego `raa`, cuya premisa `[] ⊢ P → [] ⊢ ⊥` existe **vacuamente**, da `[] ⊢ ¬P`.
3. Pero `P` es verdadera en el modelo con todas las relaciones **verdaderas**. Solidez ⇒ `[] ⊨ ¬P`
   ⇒ contradicción.

Footprint medido: **`[propext, FOL.MetaRules.raa]`**. Ni `Classical.choice` hace falta.

## 4 · Qué NO significa

* ⚠️ **`ROBINSON_PlusPlus` NO está afectado.** Medido: no importa `FOL.Soundness` ni el barrel raíz
  `FOL` — sólo `FOL.FOL`, `FOL.MetaRules`, `FOL.Tactics`, `FOL.Deduction` y `FOL.Theorems.*`.
  Sus 131 módulos y la cadena de Gödel no están en contexto inconsistente.
* ⚠️ **`FOL/Semantics.lean` está BIEN** y se queda en la librería. Es sólido y es útil: es
  exactamente lo que permitió demostrar `prf0_soundness` (§6).
* ⚠️ **Las meta‑reglas no están «mal»**. Dicen lo que dicen: `⊢` es una noción metateórica de
  verdad, no una relación de derivabilidad. La otra cara está medida en
  `ROBINSON_PlusPlus/Meta/OmegaStrength.lean`: con `raa`, `⊢` **decide toda sentencia** (lo que no
  prueba, lo refuta) ⇒ **no es r.e.** Eso ya era sabido; lo nuevo es que **también impide la
  solidez**, y las dos cosas son la misma: un cálculo completo y sólido sobre una teoría con
  modelos no elementalmente equivalentes no existe.

## 5 · Lo que se perdió, y lo que no

`compactness_theorem` (`Compacity.lean`) era **vacuo**: su prueba pasaba por `soundness`.
`Completeness.lean` **no** está afectado —no importa ni `Soundness` ni `MetaRules`— y se queda.

## 6 · La salida buena, y ya está hecha

Enunciar la solidez sobre un cálculo **sin axiomas habitándolo**. `ROBINSON_PlusPlus` tiene uno:

    Prf₀ — 17 constructores, CERO axiomas habitándolo (medido)

`prf0_soundness : Prf₀ φ → satisfies axioms φ` está **demostrado**, por inducción sobre los 17
constructores, con footprint **`[propext, Classical.choice, Quot.sound]`** — net‑0 puro.
Está en `ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.

## 7 · La reparación de fondo, que NO se ha hecho

Lo de arriba **contiene**, no repara. La reparación real es que las meta‑reglas **no habiten
`Derives`**: declararlas sobre una relación aparte `DerivesW` con `Derives Γ f → DerivesW Γ f`, y
dejar `Derives` limpio para que su solidez sea un teorema de verdad.

⚠️ **Coste medido**: `ROBINSON_PlusPlus` usa constructores `Derives.*` **164 veces**
(`Derives.subst` 58, `Derives.refl` 40, `Derives.hyp` 18, `Derives.weakening` 13,
`Derives.intro_impl` 13, …), más toda la notación `⊢`. No es una tarde. **Queda como decisión del
propietario.**

---

**Véase también:** `cuarentena/Inconsistencia.lean` (la evidencia, compilable),
`FOL/MetaRules.lean` (el aviso en cabecera),
`ROBINSON_PlusPlus/Meta/OmegaStrength.lean` y `ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.
