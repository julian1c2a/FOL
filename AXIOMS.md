# AXIOMS.md — el censo de `axiom` de FOL

> ## ESTADO REAL — 2026‑09‑12 · **4 `axiom` de Lean** · 0 `sorry` · Lean v4.31.0
>
> **Librerías en el build:** `FOL` (**4** axiomas) · `TheoryFramework` (0).
> ⭐ **Y los cuatro son exactamente los que el kernel obliga a postular** — ver §1.
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

## 1 · Los CUATRO, uno a uno — y por qué son exactamente éstos

> 🏁 **2026‑09‑12: el censo pasó de 13 a 4**, por dos decisiones del propietario (**D‑2** y **D‑3**),
> y el resultado tiene una propiedad que conviene subrayar:
>
> ### **Los cuatro que quedan son EXACTAMENTE los que el kernel obliga a postular.**

| axioma | dónde | forma | ¿usos en RPP? |
|---|---|---|---:|
| `imp_intro` | `FOL/MetaRules.lean` | `(Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)` | **83** |
| `raa` | `FOL/MetaRules.lean` | `(Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` | **27** |
| `or_elim` | `FOL/MetaRules.lean` | premisas‑función | **127** |
| `ex_elim` | `FOL/MetaRules.lean` | premisas‑función | **83** |

Los cuatro tienen **premisa‑FUNCIÓN** (`Γ ⊢ A → Γ ⊢ B`), que es una **ocurrencia NO POSITIVA** de
`Derives` en su propio constructor. El kernel lo rechaza con estas palabras:

    (kernel) arg #3 of 'D.raa' has a non positive occurrence of the datatypes being declared

⇒ **no hay alternativa dentro del tipo**: o son axiomas, o no existen.

## 2 · De 13 a 4 — qué se fue y por dónde

### 2.1 · D‑2 · Cuatro pasaron a ser CONSTRUCTORES (13 → 9)

`gen`, `dne` (regla, `MetaRules`), `dne` (esquema, `Theorems/Neg.lean`) y
`forall_not_impl_exists_not` **no tenían por qué ser axiomas**: sus premisas son ocurrencias
**positivas**. Hoy son los constructores `Derives.gen_rule`, `Derives.dne_rule`,
`Derives.dne_schema` y `Derives.forall_not_ex_not`.

⚠️ **Los nombres y las firmas se conservan** (ahora como `theorem`), así que las **336 citas** de
ROBINSON_PlusPlus —`gen` sola se usa **323 veces**— no cambiaron ni una.

🔑 **Y no es contabilidad**: un `axiom` que habita un inductivo **afirma una falsedad sobre el punto
fijo**; un constructor **lo extiende**. La lista negra de `Derives` (M‑11) baja de **8 a 4** en el
lado FOL.

⭐ **Coste medido: CERO.** No hay ni una inducción sobre `Derives` en ninguno de los dos repos.

### 2.2 · D‑3 · `Completeness.lean` a cuarentena (9 → 4)

702 líneas y **cinco axiomas** en un módulo con **cero consumidores reales**: sólo lo importaban el
barrel y un fichero ya apartado. Dos de esos cinco —`formula_enum` y `formula_enum_surj`— son
**construibles** (`Formula` es un inductivo numerable) y se postularon en un commit titulado
«100 % sorry‑free». Los otros tres (`termEqv_func_congr`, `termEqv_rel_congr`,
`henkin_extension_lemma`) no se han medido.

⚠️ **Lo que esto significa, dicho claro**: **no hay Teorema de Completitud demostrado en este repo**
en el sentido en que `README.md` lo publicaba. Está en `cuarentena/Completeness.lean`, y volverá el
día que sus cinco postulados se paguen o se justifiquen.

### 2.3 · Lo que se fue antes

| | cuándo | qué |
|---|---|---|
| 6 axiomas | 2026‑09‑12 (`ef54c6f`) | `FOLPure` y `FOL_poli` — **el enunciado era FALSO** y la corrección de junio nunca se propagó |
| 15 axiomas | 2026‑09‑12 (D‑1) | retiradas `FOLPure`, `PropLogic`, `FOL_poli` |

⇒ **34 → 28 → 13 → 4** en un día.

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
