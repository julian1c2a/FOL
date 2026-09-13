# AXIOMS.md — el censo de `axiom` de FOL

> ## ESTADO REAL — 2026‑09‑13 · **4 `axiom` de Lean** en el build · 0 `sorry` · Lean v4.31.0
>
> **Librerías en el build:** `FOL` (**4** axiomas) · `TheoryFramework` (0).
> ⭐ **Y los cuatro son exactamente los que el kernel obliga a postular** — ver §1.
> **Retiradas** el 2026‑09‑12: `FOLPure`, `PropLogic`, `FOL_poli` → `cuarentena/librerias-retiradas/`.
>
> 🏁 **2026‑09‑13 · `cuarentena/Completeness.lean` pasa de 5 a 3** — ver §2.4. `formula_enum` y
> `formula_enum_surj` ya no se postulan: los **construye** `FOL/Enumeration.lean`, que está
> **dentro del build** y cuya sobreyectividad mide `[propext, Classical.choice, Quot.sound]`.
> ⭐ Efecto colateral medido: **`lindenbaum_lemma` queda net‑0 puro** — era el único consumidor
> de los dos axiomas retirados.

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
>
> ⭐ **2026‑09‑13: son TRES** — los dos que **no** eran sustantivos están construidos (§2.4). Y eso
> no cambia el titular: **sigue sin estar demostrado**, ahora módulo tres postulados. 🔑 La cifra
> baja; el veredicto no. Cambiarlo requeriría pagar `henkin_extension_lemma`.

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

### 2.4 · 2026‑09‑13 · los dos «construibles» quedan CONSTRUIDOS (5 → 3 en cuarentena)

`FOL/Enumeration.lean` — **nuevo, dentro del build**, cero axiomas — construye

    natToFormula      : Nat → Formula
    natToFormula_surj : ∀ f : Formula, ∃ n, natToFormula n = f

y `cuarentena/Completeness.lean` los consume conservando los **nombres** `formula_enum` y
`formula_enum_surj` (ahora `def` y `theorem`), así que **ni uno de sus ocho sitios de uso cambió**.

| medida | valor |
|---|---|
| footprint de `natToFormula_surj` | `[propext, Classical.choice, Quot.sound]` — **cero axiomas del proyecto** |
| footprint de `formula_enum_surj` | idéntico |
| ⭐ footprint de `lindenbaum_lemma` | `[propext, Classical.choice, Quot.sound]` — **net‑0 PURO** |
| footprint de `completeness` | los **tres** que quedan, y sólo ésos |
| axiomas en `FOL/` y `TheoryFramework/` | **4**, sin cambio (`check-axioms.bash` sigue en verde) |

⭐ **El Lema de Lindenbaum es ahora incondicional.** No era el objetivo —el objetivo era la cifra—
pero era el único consumidor de los dos postulados, así que al pagarlos quedó libre. Es la
recíproca de M‑1 otra vez: *cada axioma que se retira audita lo que se apoyaba en él.*

#### Cómo, y por qué no costó lo que parecía

⭐ **El par de Cantor NO se define con números triangulares.** La inversa habitual exige
`n = (a+b)(a+b+1)/2 + b` y con ella identidades de división entera, que sin Mathlib son caras.
`unpair` **camina la diagonal** en un paso estructural (`(0,0) (1,0) (0,1) (2,0) …`) y entonces la
sobreyectividad es una inducción doble, sin una sola división. 🔑 *La recursión se pone donde la
prueba la quiere, no donde la fórmula la sugiere.*

⚠️ **El punto que podía bloquearlo todo era `String`** (`Formula.atom : String → List Term → …`),
y se midió antes de construir: el núcleo de Lean da `Char.ofNat_toNat` y `String.ofList_toList`,
que es exactamente lo que hace falta. ⚠️ `String` ya **no** es `structure String where data : List Char`
en v4.31 —es UTF‑8 opaco— así que `String.mk s.data = s` **no** vale por `rfl`; el lema sí.

⚠️ **Las sobreyectividades de `Term` y `Formula` NO son inducción sobre el inductivo**, sino sobre
una COTA de tamaño (`∀ N, ∀ t, size t < N → …`), el mismo patrón de `truth_lemma_lt`. `Term` es un
inductivo **anidado** (contiene `List Term`) y así se esquiva escribir a mano su recursor mutuo.

#### Lo que NO se ha tocado

Los **tres** que quedan, por orden de dificultad medida:

| axioma | qué es | juicio |
|---|---|---|
| `termEqv_func_congr` | congruencia de `=` bajo `Term.func`, argumento a argumento | ⬜ **probablemente barato**: es inducción sobre `PointwiseEqv` más los axiomas de igualdad de `FOL/Theorems/Eq.lean`. No medido |
| `termEqv_rel_congr` | lo mismo para `Formula.atom` | ⬜ igual que el anterior |
| ⛔ `henkin_extension_lemma` | todo conjunto consistente se extiende a uno **máximamente consistente y con testigos** | ⛔ **es el caro de verdad**: su prueba clásica **amplía el lenguaje con constantes nuevas**, y eso aquí significa construir la extensión y su conservatividad |

⚠️ **Y mientras `henkin_extension_lemma` siga postulado, `completeness` no está demostrado.**
Bajar de 5 a 3 no mueve ese veredicto ni un milímetro.

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
