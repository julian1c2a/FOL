# AXIOMS.md — el censo de `axiom` de FOL

> ## ESTADO REAL — 2026‑09‑13 · **4 `axiom` de Lean** en el build · 0 `sorry` · Lean v4.31.0
>
> **Librerías en el build:** `FOL` (**4** axiomas) · `TheoryFramework` (0).
> ⭐ **Y los cuatro son exactamente los que el kernel obliga a postular** — ver §1.
> **Retiradas** el 2026‑09‑12: `FOLPure`, `PropLogic`, `FOL_poli` → `cuarentena/librerias-retiradas/`.
>
> 🏁🏁 **2026‑09‑13 · `cuarentena/Completeness.lean` pasa de 5 a 1.** Dos por la mañana (§2.4:
> `formula_enum`/`formula_enum_surj`, que **construye** `FOL/Enumeration.lean`) y dos por la tarde
> (§2.5: `termEqv_func_congr`/`termEqv_rel_congr`, **demostrados**).
> ⭐ Efecto medido, y es mayor que la cifra: **`lindenbaum_lemma`, `truth_lemma` y el modelo
> canónico entero quedan net‑0 puros**. `completeness` depende ya de **un solo** postulado del
> proyecto: `henkin_extension_lemma`.
>
> ⚠️⚠️ **Y ese último SE MIDIÓ el mismo día: también sale** (§2.6, `sondeos/HenkinSaleDeRaa.lean`).
> **No se ha aplicado, y a propósito**: el footprint de `completeness` pasaría de un postulado
> propio y con nombre a **`FOL.MetaRules.raa`**, el axioma que hace el cálculo **completo y no
> sólido**. 🔑 *La cifra mejoraría y el contenido empeoraría.* ⬜ Decisión del propietario.

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
> ⭐ **2026‑09‑13: es UNO.** Cuatro de los cinco están pagados: los dos de enumerabilidad (§2.4) y
> las dos congruencias de la igualdad (§2.5). Y eso **no cambia el titular**: sigue sin estar
> demostrado, ahora módulo **un** postulado.
>
> ⚠️⚠️ **Y el que queda no es «el caro»: es el INCÓMODO.** Se midió (§2.6) y **sale** — pero pagando
> con `raa`. ⇒ el módulo podría marcar **CERO axiomas** y seguir sin demostrar lo que su nombre
> promete, porque el cálculo del que hablaría **decide toda sentencia y no es sólido**.
> 🔑 **Un cero en este censo no significaría «Completitud demostrada».** Por eso el axioma sigue ahí.

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

#### Lo que en esa pasada NO se tocó

Los **tres** que quedaban entonces, con el juicio que se emitió — y conviene dejarlo escrito
porque **dos de los tres juicios se comprobaron el mismo día** (§2.5):

| axioma | qué es | juicio de la mañana |
|---|---|---|
| `termEqv_func_congr` | congruencia de `=` bajo `Term.func`, argumento a argumento | ⬜ «probablemente barato… **no medido**» → ✅ **medido y pagado** (§2.5) |
| `termEqv_rel_congr` | lo mismo para `Formula.atom` | ⬜ igual → ✅ **pagado** |
| ⚠️ `henkin_extension_lemma` | todo conjunto consistente se extiende a uno **máximamente consistente y con testigos** | ⛔ se clasificó como «el caro de verdad» (ampliar el lenguaje con constantes y probar conservatividad) → ⚠️⚠️ **MEDIDO el 2026‑09‑13 y el juicio ERA FALSO**: sale, y por la peor razón. Ver §2.6 |

### 2.5 · 2026‑09‑13 (tarde) · las DOS congruencias, DEMOSTRADAS (3 → 1)

`termEqv_func_congr` y `termEqv_rel_congr` eran `axiom`. Son teoremas.

| medida | valor |
|---|---|
| `termEqv_func_congr` / `termEqv_rel_congr` | `[propext, Classical.choice, Quot.sound]` |
| ⭐ `evalTerm_canonical` (el modelo canónico) | **net‑0 puro** |
| ⭐⭐ `truth_lemma` (el Lema de la Verdad) | **net‑0 puro** |
| `model_existence_lemma` / `completeness` | `henkin_extension_lemma`, y **nada más** |
| coste | **~45 líneas** en `FOL/Theorems/Eq.lean` (dentro del build) + **~55** en `Completeness.lean` |

🔑 **Lo que faltaba no era de LÓGICA, era de LISTAS.** `Derives.subst` es Leibniz con índice 0 —
sustituye **un** término— y `Term.func`/`Formula.atom` llevan una **lista** de argumentos. La
técnica es la misma que `derive_eq_symm`/`derive_eq_trans` ya usaban desde siempre (fórmula‑contexto
con `Term.var 0` en el hueco y `liftTerm 0` en el resto, cerrada por `substTerm_liftTerm`); lo único
que no existía era **abrir el hueco dentro de la lista**: partirla en `pre ++ x :: post` y saber que
`substTerms` distribuye sobre `++`. Ese lema —`substTerms_append`, cuatro líneas— es toda la pieza
que faltaba, y con él los otros tres salen seguidos.

Entran en `FOL/Theorems/Eq.lean`, que **está en el build**: `substTerms_append`,
`substTerms_lift_hole`, **`derive_eq_func_congr`** y **`derive_atom_congr`**. Son lemas generales de
igualdad que a la librería le faltaban, no andamiaje de la cuarentena. En `Completeness.lean` queda
sólo el traslado de `Derives` a `DerivesSet` (`DerivesSet_map`/`DerivesSet_map2`) y la inducción
sobre `PointwiseEqv`, que es un inductivo **sin axiomas habitándolo** ⇒ M‑11 no aplica.

⚠️ **Y el veredicto sigue sin moverse**: mientras `henkin_extension_lemma` esté postulado,
`completeness` **no está demostrado**. De 5 a 1 es una cifra; el que queda es el que costaba.

⚠️ **Lección de método, del propio §2.4**: allí se escribió *«derivable en principio, **no
medido**»*. Estaba bien dicho —era una estimación declarada como tal— y al medirla resultó cierta.
🔑 *Una estimación etiquetada como estimación no hace daño; la que se publica como medición, sí.*

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

### 2.6 · ⚠️⚠️ 2026‑09‑13 · `henkin_extension_lemma` SALE — y por eso no se ha tocado

`sondeos/HenkinSaleDeRaa.lean` (ROBINSON_PlusPlus), compilado.

🏁 **Es demostrable.** `IsMaximalConsistent S → IsHenkin S` es un teorema, y con él
`henkin_extension_lemma` es `lindenbaum_lemma` más tres líneas ⇒ este módulo llegaría a **CERO
axiomas propios**.

⚠️⚠️ **Y el precio está medido, y no es «1 → 0»:**

| | axiomas propios | footprint de `completeness` |
|---|---|---|
| hoy | **1** | `[propext, Classical.choice, Quot.sound, henkin_extension_lemma]` |
| pagándolo | **0** | `[propext, Classical.choice, Quot.sound, **FOL.MetaRules.raa**]` |

Es cambiar **un postulado propio, honesto y con nombre** por **el axioma que hace el cálculo
completo y no sólido** — el mismo que en `cuarentena/Inconsistencia.lean` da `False` en cuanto se
le junta cualquier teorema de solidez. Y obliga a que `Completeness.lean` **importe
`FOL.MetaRules`**, cosa que hoy **no hace** (medido: siete imports, ninguno es `MetaRules` — y
`cuarentena/README.md` §4 presentaba justamente eso como la razón de que este módulo no estuviera
en el radio de la inconsistencia).

#### Por qué sale

`raa` toma una **función de Lean**: si `Γ ⊬ A`, esa función existe **vacuamente** ⇒ `Γ ⊢ ¬A`.
⇒ **todo contexto decide toda fórmula** (`derives_complete`, tres líneas). Con eso el obstáculo
clásico —constantes frescas, conservatividad— **ni se plantea**: el testigo sale por completitud
sintáctica, no por ampliación del lenguaje. ⭐ La pieza limpia del argumento es
`no_instance_no_body` (footprint **`[propext]`**, sólo `intro_forall` + `elim_forall`), y ⭐ el
punto que parecía romperlo —contextos finitos distintos para cada instancia— **no se rompe**:
`max_cons_contains` deja el mismo `Γ0` para todas.

⚠️ **M‑11 no se viola**: no hay ni una inducción sobre `Derives`; sólo constructores, `raa` como
**introducción**, y tercio excluido sobre la `Prop` `Γ ⊢ A`. Las pruebas son legítimas.
⚠️ Pero **no valdrían para un cálculo sólido**: en uno sólido `derives_complete` es falso.
🔑 **Esta Henkin sale de la patología, no de la lógica.** Es ADR‑024 otra vez: *`⊢` es la
herramienta, no el sujeto*.

#### Lo que NO se sigue

**No** se sigue `False`: el detonador de `Inconsistencia.lean` es `raa` **más solidez**, y este
módulo no demuestra solidez y va en la dirección contraria.

⬜ **Decisión del propietario, y por eso está medido y no aplicado.** Un **0** en este censo se
leería como «Completitud demostrada», y lo que habría detrás es «completitud de un cálculo que,
cuando no deriva `A`, deriva `¬A`». 🔑 *La cifra mejoraría y el contenido empeoraría.*
