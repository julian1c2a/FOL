# AXIOMS.md — el censo de `axiom` de FOL

> ## ESTADO REAL — 2026‑09‑12 · **13 `axiom` de Lean** · 0 `sorry` · Lean v4.31.0
>
> **Librerías en el build:** `FOL` (13 axiomas) · `TheoryFramework` (0).
> **Retiradas** el 2026‑09‑12: `FOLPure`, `PropLogic`, `FOL_poli` → `cuarentena/librerias-retiradas/`.

**Creado:** 2026‑09‑12 · **Autor:** Julián Calderón Almendros

---

## 0 · Por qué este documento existe

La auditoría del 2026‑09‑12 midió que **ningún control de este repo cuenta `axiom`**
(`grep -ln axiom *.bash` → vacío). El único que había, `check-sorry.bash`, daba **VERDE** con
**28 axiomas** en el árbol. Y el censo **pasó de 34 a 28 y luego a 13 sin que nada lo registrara**.

⛔ **Un `sorry` es visible y un `axiom` no.** Ésa es toda la razón.

> ### ⚠️ LA NOTA QUE HAY QUE LEER ANTES QUE NADA
>
> **`FOL/Completeness.lean` sustituyó un `sorry` por CINCO `axiom`** (commit `e9580a4`, titulado
> *«100 % sorry‑free»*). ⇒ **El Teorema de Completitud NO está demostrado** en el sentido en que
> `README.md` y `REFERENCE.md` lo publican. Está demostrado **módulo cinco postulados**, y tres de
> ellos son sustantivos.

---

## 1 · Los 13, uno a uno

### 1.1 · `FOL/MetaRules.lean` — las meta‑reglas (6)

| axioma | línea | forma | ¿usos en RPP? |
|---|---:|---|---:|
| `imp_intro` | 67 | `(Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)` | **83** |
| `gen` | 87 | `(∀ n : Term, Γ ⊢ A[n]) → Γ ⊢ ∀A` | **324** |
| `raa` | 92 | `(Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` | **27** |
| `dne` (regla) | 100 | `Γ ⊢ ¬¬A → Γ ⊢ A` | **13** |
| `or_elim` | 124 | premisas‑función | **127** |
| `ex_elim` | 138 | premisas‑función | **83** |

### 1.2 · Sueltos (2)

| axioma | dónde | ¿usos en RPP? |
|---|---|---:|
| `dne` (**esquema**) | `FOL/Theorems/Neg.lean:57` — `Γ ⊢ (¬¬A ⇒ A)`. ⚠️ **Es un SEGUNDO `dne`**, distinto del de `MetaRules` (que es regla). Lo consume `Completeness.lean:680` | 0 |
| `forall_not_impl_exists_not` | `FOL/Theorems/Quantifiers.lean:115` | **0** |

### 1.3 · `FOL/Completeness.lean` — los cinco del Teorema de Completitud (5)

| axioma | línea | qué postula | ¿inevitable? |
|---|---:|---|---|
| `formula_enum` | 119 | una enumeración `Nat → Formula` | ⛔ **NO**: `Formula` es un inductivo **numerable**; la enumeración es **construible** |
| `formula_enum_surj` | 120 | y que es suprayectiva | ⛔ **NO**, ídem |
| `termEqv_func_congr` | 389 | congruencia de la equivalencia de términos para `func` | 🔶 no medido |
| `termEqv_rel_congr` | 392 | ídem para `rel` | 🔶 no medido |
| `henkin_extension_lemma` | 657 | el lema de extensión de Henkin | 🔶 no medido — es **el sustantivo** |

⇒ **Ninguno llega a RPP** [medido]: `Completeness` no lo importa nadie.

---

## 2 · ⛔⛔ Los 8 que HABITAN el inductivo `Derives` — y la doctrina CORREGIDA

Los de §1.1 y §1.2 **habitan `Derives`**. Por **M‑11**
([ADR‑025](../ROBINSON_PlusPlus/DECISIONS.md)) eso **prohíbe demostrar nada sobre `Derives` por
inducción** — y es lo que hacía `soundness`, hoy en `cuarentena/`.

> ### ⚠️ LA DOCTRINA ESTABA MAL, y se corrigió el 2026‑09‑12 (A‑4)
>
> `MetaRules.lean` decía que **los seis** «no son derivables… **tienen que ser axiomas**».
> **Falso para cuatro de los ocho**, y está **medido compilando**:

| | axiomas | por qué |
|---|---|---|
| ⛔ **TIENEN que serlo** (4) | `imp_intro`, `raa`, `or_elim`, `ex_elim` | su premisa es `Γ ⊢ A → Γ ⊢ B`: **ocurrencia NO POSITIVA**. El kernel lo rechaza literalmente: *«arg #3 … has a non positive occurrence of the datatypes being declared»* |
| ✅ **PODRÍAN ser constructores** (4) | `gen`, `dne` (regla), `dne` (esquema), `forall_not_impl_exists_not` | son *shapes* legales. **Compilado**: un `inductive` que los incluye a los cuatro typechequea, `EXIT 0`, y su recursor no depende de ningún axioma — **`gen` incluido**, pese a su premisa infinitaria |

⇒ 🔑 **El criterio que de verdad separa no es «meta‑regla» sino PREMISA‑FUNCIÓN.**

⇒ ⬜ **Decisión abierta (D‑2)**: mover los cuatro evitables a constructores dejaría **13 → 9**
axiomas y la lista negra de `Derives` en **4**, **sin tocar la fuerza del cálculo** y con **cero
pruebas tocadas dentro de `FOL/`**.

---

## 3 · Lo que este censo NO dice

* ⚠️ **`#print axioms` no detecta la clase M‑11**: un teorema probado por inducción sobre un
  inductivo habitado tiene footprint **limpio** y es **injustificado**. El censo cuenta postulados,
  no mide esa patología.
* ⚠️ **ROBINSON_PlusPlus tiene su propio censo** (`../ROBINSON_PlusPlus/AXIOMS.md`), y **fabrica
  un habitante más** de `Derives` con premisa‑función: `ax_list_induction`.

---

**Véase también:** `cuarentena/README.md` (por qué `soundness` está apartado),
`FOL/MetaRules.lean` (la doctrina corregida),
`../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md` (de dónde sale este documento).
