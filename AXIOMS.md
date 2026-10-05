# AXIOMS.md — el censo de `axiom` de FOL

> ## 🗑️ ESTADO REAL — 2026‑10‑02 · **0 `axiom` de Lean** · `FOL/MetaRules.lean` BORRADO por refutable
>
> *(ADR‑115 de RPP, ejecutado en FOL el 2026‑10‑02. La cifra del titular la vigila `check-axioms.bash`, que
> espera 0 en `FOL/`, en `TheoryFramework/` y en `cuarentena/`, y rompe si vuelve a aparecer uno.)*
>
> Ningún `axiom` del proyecto en los **54 módulos activos** (`FOL/` 43 + `FOL/Theorems/` 5 +
> `TheoryFramework/` 6), y ninguno en `cuarentena/` fuera de las librerías muertas de
> `cuarentena/librerias-retiradas/` (15, fuera del lakefile: `check-axioms.bash` las imprime y no las vigila).
> Los cuatro últimos —`imp_intro`, `raa`, `or_elim` y `ex_elim`, las meta‑reglas con premisa‑FUNCIÓN de
> `FOL/MetaRules.lean`— **se borraron con el módulo** (§1): sus ENUNCIADOS son **refutables sin usarlos**
> (`FOL/Inconsistencia.lean` §3), así que Lean más uno solo de ellos demostraba `False`.
>
> ⛔ **El diagnóstico que este documento repetía estaba AL REVÉS.** Decía que la solidez de `Derives` era
> FALSA y que M‑11 prohibía inducir sobre él. Lo falso era `raa` —y con él las otras tres—: los 22
> constructores de `Derives` son sólidos, y sin las meta‑reglas `Derives` es `Derives₀` más `gen_rule`,
> que es admisible (`FOL.Inconsistencia.derives_to_derives0`, una inducción sobre `Derives`, legítima).
> ⇒ `Derives` es **sólido** (`derives_soundness`), **no** es sintácticamente completo (`derives_not_P`,
> `derives_not_negP`) y se puede inducir sobre él. Lo que abajo dice lo contrario es registro, fechado, con
> su rectificación (✏️).
>
> ✅ **SALDADA el 2026‑10‑03** **— cinco módulos CONGELADOS** (🧊, `frozen_files.txt`) llevaban textos falsos —ya
> lo eran al escribirse: lo falso era `raa` (ADR‑114 §2 de RPP)— que el diagnóstico del 2026‑10‑02 dejó a la vista. El propietario autorizó el `thaw`: se corrigieron sólo sus comentarios (código idéntico a HEAD,
> comprobado sin comentarios) y se volvieron a congelar en el mismo ciclo. Lo que decían, como registro:
>
> | módulo 🧊 | lo que decía (corregido el 2026‑10‑03; líneas de antes del `thaw`) |
> |---|---|
> | `FOL/Soundness0.lean` | l. 27-30: «la solidez de `Derives` es FALSA», con `FOL/Inconsistencia.lean` y `[propext, FOL.MetaRules.raa]` por prueba y M‑11 por causa; l. 45-48 y 228-231: que `Derives` es sintácticamente completo; l. 56-60: que a la prueba de `cuarentena/Soundness.lean` la invalidaba «el tipo sobre el que inducía» y que el teorema «cae por M‑11»; l. 208: «su solidez es falsa» |
> | `FOL/Canonical0.lean` | l. 31-32: que sobre `Derives` «no puede haberlas» (solidez y completitud) porque «su solidez es FALSA», y que `axioms ⊢` es sintácticamente completo (M‑10), lo que venía de `raa` |
> | `FOL/Compacity0.lean` | l. 31: «la solidez de `Derives` es **falsa** (M‑11)» |
> | `FOL/Rename.lean` | l. 33 y 279: que inducir sobre `Derives` es ilegítimo («M‑11: cuatro axiomas lo habitan») |
> | `TheoryFramework/Instances/FOL.lean` | l. 29-30: llama FALSA a la solidez de `Derives` y da por prueba `FOL/Inconsistencia.lean`, que hoy demuestra lo contrario; l. 33-35: `Derives`, «el cálculo CONTAMINADO», y `SoundLogic` sobre él, «inhabitable»; l. 40: «sigue SIN instancia, y es correcto: su solidez es falsa» |
>
> ⚠️ **PeanoRF** (bloqueado por el propietario) importa `FOL.MetaRules` y deja de compilar con este borrado.
> El propietario lo previó por escrito al bloquearlo («se romperá en cuanto cambie esa base. Es lo esperado»,
> `../Peano-from-ROB-n-FOL/BLOQUEO-2026-10-01.md`), y no se toca (ADR‑115 de RPP §7).

> ## 🗄️ Registro del 2026‑09‑27 · los mismos cuatro `axiom` de entonces; lo que se midió es lo NO CONSTRUCTIVO — ver §4
>
> La auditoría de constructividad (`auditoria/constructividad-2026-09-27/`) midió, constante a
> constante, por dónde entra `Classical.choice` —que **no** es un `axiom` del proyecto, y por eso
> este censo no lo contaba—, y las decisiones D1–D8 del propietario quitaron lo evitable:
> **157 → 84** constantes con `Classical.choice`, **8 → 1** `noncomputable`, **55 → 34** titulares.
> ⛔ Y cae una tesis que el proyecto repetía: el `Classical.choice` de la completitud **no** es
> «el WKL del `if` de Lindenbaum» (§4.5).
> ⚠️ Esas cifras son del 2026‑09‑27 y no se han re‑medido tras el borrado de `MetaRules` (§4.6).

> ## 🗄️ Registro histórico — el «ESTADO REAL» del 2026‑09‑23: «4 `axiom` de Lean», y «NI UNO MÁS EN NINGUNA PARTE»
>
> `cuarentena/` **se vació de código** (decisiones E1/E2/E3 del cierre): los tres módulos con
> teoremas FALSOS y el `Completeness.lean` superado por `Canonical0.completeness₀` **se
> borraron**, y con ellos el único `axiom` del repositorio que vivía fuera del build
> (`henkin_extension_lemma`).
>
> ⚠️ **Esto NO revierte ADR‑032**, que decidió que ese axioma se quedaba: lo que desaparece
> es el **módulo** que lo alojaba, superado por un teorema que no lo necesita. La decisión de
> ADR‑032 queda **sin objeto**, no revocada.
>
> ⭐ Y `cuarentena/Inconsistencia.lean` —la **evidencia** de que la solidez de `Derives` es
> falsa— **subió al build** como `FOL/Inconsistencia.lean`: footprint
> `[propext, FOL.MetaRules.raa]`. 🔑 *Congelar un repositorio con su pieza de evidencia sin
> compilar es congelar una afirmación, no un hecho.*
>
> ✏️ **Rectificado el 2026‑10‑02** (ADR‑115 de RPP): no era la evidencia de eso, sino de que `raa` era
> falso. El módulo se reescribió: su §1 demuestra hoy la solidez de `Derives` (`derives_soundness`) y su §3
> refuta los enunciados de las cuatro meta‑reglas; el teorema de entonces, `inconsistencia_de_cualquier_solidez`,
> se borró porque su enunciado era falso (también entonces) y sólo se «demostraba» con `raa`. Y «ni uno más en ninguna parte» dejaba fuera los 15 de las
> librerías muertas de `cuarentena/librerias-retiradas/`, que siguen ahí, fuera del lakefile.

> ## 🗄️ Registro histórico — ESTADO del 2026‑09‑13 · «4 `axiom` de Lean» en el build · 0 `sorry` · Lean v4.31.0
>
> **Librerías en el build:** `FOL` (**4** axiomas) · `TheoryFramework` (0).
> ⭐ **Y los cuatro son exactamente los que el kernel obliga a postular** — ver §1.
> ✏️ **FALSO** (rectificado el 2026‑10‑02): el kernel sólo impedía que fueran constructores; no obligaba a
> postularlos, y postularlos hacía inconsistente a Lean. Se borraron (§1, ADR‑115 de RPP).
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
> ✅ **Y SE QUEDA, por decisión tomada** (ADR‑032, opción **(A)**, sanción del propietario): el
> footprint de `completeness` pasaría de un postulado propio y con nombre a **`FOL.MetaRules.raa`**,
> el axioma que hace el cálculo **completo y no sólido**. 🔑 *La cifra mejoraría y el contenido
> empeoraría.* ⛔ **Este 1 no es trabajo pendiente: es la cifra correcta.**
> ✏️ 2026‑10‑02: no era un cálculo «completo y no sólido»: `raa` era refutable, y Lean más `raa` demostraba
> `False` (§1). El módulo y su axioma se borraron el 2026‑09‑23 (registro de arriba).

**Creado:** 2026‑09‑12 · **Autor:** Julián Calderón Almendros
**Last updated:** 2026-10-05 — D7 ejecutada (ADR‑129 de RPP): los símbolos son `List Char`; notas ✏️ en §2.4, §4.3 y §4.4, donde se daba por vigente lo de `String` (nombres retirados o renombrados; «no hacía falta»). Antes, sin marca: el último cambio fue el del 2026-10-03 (la deuda de los cinco módulos 🧊, saldada).

---

## 0 · Por qué este documento existe

La auditoría del 2026‑09‑12 midió que **ningún control de este repo cuenta `axiom`**
(`grep -ln axiom *.bash` → vacío). El único que había, `check-sorry.bash`, daba **VERDE** con
**28 axiomas** en el árbol. Y el censo **pasó de 34 a 28 y luego a 13 sin que nada lo registrara**.

⛔ **Un `sorry` es visible y un `axiom` no.** Ésa es toda la razón.

> ### ⚠️ LA NOTA QUE HABÍA QUE LEER ANTES QUE NADA — ⛔ HISTÓRICA, superada el 2026-09-16
>
> 🏁 **Hay Teorema de Completitud demostrado, y sobre un cálculo SÓLIDO**:
> `Canonical0.completeness₀ : Γ ⊨ f → Γ ⊢₀ f`, footprint `[propext, Classical.choice, Quot.sound]`,
> **cero axiomas del proyecto**: ni `henkin_extension_lemma` ni `raa`. El `FOL/Completeness.lean` de
> abajo, sobre `Derives`, **se borró** el 2026-09-23. Lo que sigue es el registro de por qué aquello no
> bastaba.
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
> 🔑 **Un cero en este censo no significaría «Completitud demostrada».**
> ✅ **Decidido (ADR‑032, opción A): el axioma se queda.** Este documento existe porque *«un `sorry`
> es visible y un `axiom` no»*; un censo que baja a cero **comprando el cero con `raa`** dejaría de
> ser un censo.
>
> ✏️ **2026‑10‑02**: lo que le hacía «decidir toda sentencia» era `raa`, y `raa` era refutable (§1).
> `Derives` es sólido, y sin `raa` no decide toda sentencia. El cero que este censo marca hoy no se compró
> con `raa`: se obtuvo retirándolo.

---

## 1 · CERO `axiom` — y los cuatro últimos, BORRADOS por refutables (2026‑10‑02, ADR‑115 de RPP)

🗑️ **Desde el 2026‑10‑02 el censo está a cero.** `FOL/MetaRules.lean` se borró con sus cuatro `axiom`
(ADR‑115 de RPP, por la decisión 2 del propietario en ADR‑114 §4: «si dicen cosas falsas, las retiramos; no
hacemos uso de herramientas que no sean verdaderas»). `check-axioms.bash` espera **0** en `FOL/`, en
`TheoryFramework/` y en `cuarentena/`, y rompe si vuelve a aparecer uno.

### 1.1 · Registro de los cuatro: dónde estaban y por qué se borraron

> 🏁 **2026‑09‑12: el censo pasó de 13 a 4**, por dos decisiones del propietario (**D‑2** y **D‑3**), y
> este § se titulaba *«Los cuatro que quedan son EXACTAMENTE los que el kernel obliga a postular»*.
> ✏️ **Era falso** (rectificado el 2026‑10‑02): la razón, debajo de la tabla.

| axioma (borrado) | dónde estaba | forma | su enunciado, refutado sin usarlo | footprint de la refutación | usos en RPP (2026‑09‑12) |
|---|---|---|---|---|---:|
| `imp_intro` | `FOL/MetaRules.lean` | `(Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)` | `imp_intro_refutable` | `[propext, Quot.sound]` | 83 |
| `raa` | `FOL/MetaRules.lean` | `(Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` | `raa_refutable` | `[propext, Quot.sound]` | 27 |
| `or_elim` | `FOL/MetaRules.lean` | `(Γ ⊢ A ∨ B) → (Γ ⊢ A → Γ ⊢ C) → (Γ ⊢ B → Γ ⊢ C) → Γ ⊢ C` | `or_elim_refutable` | `[propext, Quot.sound]` | 127 |
| `ex_elim` | `FOL/MetaRules.lean` | `(Γ ⊢ ∃A) → (∀ t, Γ ⊢ A[t/0] → Γ ⊢ C) → Γ ⊢ C` | `ex_elim_refutable` | `[propext, Classical.choice, Quot.sound]` | 83 |

Las cuatro refutaciones están en `FOL/Inconsistencia.lean` §3 (en el build), sobre los enunciados escritos
como `Prop` (`ImpIntro`, `Raa`, `OrElim`, `ExElim`); la primera medición fue
`../ROBINSON_PlusPlus/sondeos/MetaReglasRefutables.lean` (2026‑10‑02; auditoría de la base: L1‑3 de ADR‑114 y
R2‑4‑1 de la ronda 2). Los usos en RPP son los del 2026‑09‑12: hoy ningún módulo de la librería de RPP importa
`FOL.MetaRules`, porque RPP retiró su capa `⊢` (ADR‑115 de RPP; §4.6).

**Por qué eran axiomas.** Los cuatro tienen **premisa‑FUNCIÓN** (`Γ ⊢ A → Γ ⊢ B`), una **ocurrencia NO
POSITIVA** de `Derives` que el kernel rechaza en un constructor:

    (kernel) arg #3 of 'D.raa' has a non positive occurrence of the datatypes being declared

⇒ **no había alternativa dentro del tipo**: o eran axiomas, o no existían. Hasta el 2026‑10‑02 fueron
axiomas; desde ADR‑115, **no existen**.

**Por qué eran falsos.** El kernel sólo impide que sean constructores; no obliga a postularlos. Y la misma
premisa‑función que los deja fuera del tipo los hace falsos: si `Γ ⊬ A`, la función `Γ ⊢ A → Γ ⊢ B` existe
**vacuamente**. Los 22 constructores de `Derives` son sólidos —por inducción sobre ellos, sin ningún axioma
del proyecto—, luego `⊬ P` y `⊬ ¬P` para un átomo `P`; con la premisa vacua `⊢ P → ⊢ ⊥`, `raa` (o
`imp_intro`) fabricaba `⊢ ¬P`. `or_elim` cae con el tercio excluso (`⊢ P ∨ ¬P`, con las dos ramas vacuas
hacia `⊥`), y `ex_elim` con un modelo de dos puntos en el que `∃x P(x)` es verdadera y ningún TÉRMINO la
testimonia.

### 1.2 · Lo que queda: `Derives` = `Derives₀` + `gen_rule`, admisible

Sin las meta‑reglas, los 22 constructores de `Derives` se traducen a `Derives₀` (21): veintiuno son el mismo
constructor, y `gen_rule` es **admisible** con una constante fresca
(`FOL.Inconsistencia.derives_to_derives0 : Γ ⊢ f → Γ ⊢₀ f`, `[propext, Quot.sound]`). ⇒ `Derives` es
**sólido** para Tarski (`derives_soundness`, `[propext, Classical.choice, Quot.sound]`), **no** es
sintácticamente completo (`derives_not_P`, `derives_not_negP`), y **la inducción sobre él es legítima**:
`derives_to_derives0` es una.

🔑 *M‑11 —«un `axiom` que habita un inductivo prohíbe inducir sobre él»— se quedaba corta: el recursor cubre
por definición a todo habitante, así que una inducción correcta que demuestra la solidez REFUTA el axioma que
la contradice. Lo que había que retirar era el axioma, no la inducción.*

## 2 · De 13 a 4 — qué se fue y por dónde

### 2.1 · D‑2 · Cuatro pasaron a ser CONSTRUCTORES (13 → 9)

`gen`, `dne` (regla, `MetaRules`), `dne` (esquema, `Theorems/Neg.lean`) y
`forall_not_impl_exists_not` **no tenían por qué ser axiomas**: sus premisas son ocurrencias
**positivas**. Hoy son los constructores `Derives.gen_rule`, `Derives.dne_rule`,
`Derives.dne_schema` y `Derives.forall_not_ex_not`.

⚠️ **Los nombres y las firmas se conservaron** (como `theorem`), así que las **336 citas** de
ROBINSON_PlusPlus —`gen` sola se usaba **323 veces**— no cambiaron ni una (medido el 2026‑09‑12).
🗑️ Desde el 2026‑10‑02 los envoltorios `gen` y `dne` (regla) ya no existen: vivían en `FOL/MetaRules.lean`,
borrado con ADR‑115 de RPP, y la librería de RPP ya no los usa (retiró su capa `⊢`). Siguen `dne` (esquema,
`Theorems/Neg.lean`) y `forall_not_impl_exists_not` (`Theorems/Quantifiers.lean`).

🔑 **Y no es contabilidad**: un `axiom` que habita un inductivo **afirma algo sobre el punto fijo** que
nada garantiza —si la regla no es admisible, es FALSO—; un constructor **lo extiende**. La lista negra de
`Derives` (M‑11) bajó entonces de **8 a 4** en el lado FOL, y con ADR‑115 (2026‑10‑02) **quedó en 0**:
`Derives` no tiene ya ningún habitante‑axioma.
(✏️ 2026‑10‑02: decía «afirma una falsedad», que no vale en general: `gen`, como axioma, era una regla
admisible —`derives_to_derives0` lo demuestra—; para los cuatro de premisa‑función sí era literal: el propio
recursor los refuta, §1.1)

⭐ **Coste medido: CERO** (2026‑09‑12): no había ni una inducción sobre `Derives` en el código compilado de los
dos repos (sí la de `cuarentena/Soundness.lean`, fuera del build, la que M‑11 condenaba).
Hoy sí las hay, y son legítimas: `FOL.Inconsistencia.derives_to_derives0` en FOL, y `derives_tval` y
`derives_to_derives0` en `../ROBINSON_PlusPlus/sondeos/MetaReglasRefutables.lean`.

### 2.2 · D‑3 · `Completeness.lean` a cuarentena (9 → 4)

702 líneas y **cinco axiomas** en un módulo con **cero consumidores reales**: sólo lo importaban el
barrel y un fichero ya apartado. Dos de esos cinco —`formula_enum` y `formula_enum_surj`— son
**construibles** (`Formula` es un inductivo numerable) y se postularon en un commit titulado
«100 % sorry‑free». Los otros tres (`termEqv_func_congr`, `termEqv_rel_congr`,
`henkin_extension_lemma`) no se han medido.

⚠️ **Lo que esto significa, dicho claro**: **no hay Teorema de Completitud demostrado en este repo**
en el sentido en que `README.md` lo publicaba. Está en `cuarentena/Completeness.lean`, y volverá el
día que sus cinco postulados se paguen o se justifiquen.

📝 Registro del 2026‑09‑12, superado: los tres «no medidos» se midieron el 2026‑09‑13 (§2.5 y §2.6); desde
el 2026‑09‑16 hay Teorema de Completitud, `Canonical0.completeness₀`, sobre el cálculo sólido `Derives₀` y
sin ningún axioma del proyecto; y `cuarentena/Completeness.lean` no volvió: se borró el 2026‑09‑23.

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

📝 **2026‑09‑27**: y ese lema era el que traía el `Classical.choice` de la tabla de arriba.
`String.toList` y `String.ofList_toList` **decodifican UTF‑8**, y en v4.31 el decodificador del
núcleo lleva `Classical.choice` (una prueba de `BitVec`/`Nat` dentro de su prueba de validez).
`natToString_surj` sale hoy por `String.exists_eq_ofList` (que sólo lleva `[propext]`) y queda,
con `natToFormula_surj`, en `[propext, Quot.sound]`; `lindenbaum_lemma₀` también, pero porque además su etapa dejó de
decidir nada (§4.4).
✏️ **2026‑10‑05** (D7 ejecutada, ADR‑129 de RPP): `Formula.atom` toma hoy un `List Char`, y el punto desaparece.
`natToString_surj` ya no existe: es `natToSym_surj` (`natToSym n = (natToList n).map Char.ofNat`), que sale de
`natToList_surj` y `map_ofNat_toNat` sin `String`; con `natToFormula_surj`, sigue en `[propext, Quot.sound]`
(`check-footprints` de RPP).

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

⇒ **34 → 28 → 13 → 4** en un día. Y **4 → 0** el 2026‑10‑02: `FOL/MetaRules.lean` borrado (§1, ADR‑115
de RPP). Los de `cuarentena/Completeness.lean` bajaron aparte: de 5 a 1 el 2026‑09‑13 y a 0 el 2026‑09‑23,
al borrarse el módulo.

## 3 · Lo que este censo NO dice

* ⚠️ **No dice que un `axiom` sea CONSISTENTE con el resto**, y `#print axioms` tampoco: los dos cuentan
  postulados, no los juzgan. ✏️ Esta viñeta decía que `#print axioms` no detecta «la clase M‑11»: *«un
  teorema probado por inducción sobre un inductivo habitado tiene footprint limpio y es injustificado»*.
  Era al revés (rectificado el 2026‑10‑02, ADR‑114/115 de RPP): esa inducción es **correcta**, porque el
  recursor cubre a todo habitante, y lo que la contradice es el axioma. El riesgo es un `axiom` sobre un
  inductivo, que puede ser **refutable por el propio recursor**: los cuatro de `MetaRules` lo eran (§1.1).
* ⚠️ **ROBINSON_PlusPlus tiene su propio censo** (`../ROBINSON_PlusPlus/AXIOMS.md`), hoy sin ningún
  `axiom` de Lean. Fabricaba tres habitantes más de `Derives`, hoy retirados: `ax_induction_prim`, `ax_list_induction` y
  `ax_axiomsCodeT_eq` (ADR‑114 §5 de RPP), retirados con la capa `⊢` (ADR‑115). `ax_list_induction`
  (retirado; con premisa‑función hasta ADR‑029, 2026‑09‑13; después con premisa objeto, positiva). También era refutable: su `φ : Term → Formula`
  mira la sintaxis del término y su `Γ` es libre, y él solo daba `[] ⊢ ⊥` (ADR‑114 L1‑2,
  `sondeos/ListInductionAxiomRefutable.lean`). Se retiró con la capa `⊢` de RPP (ADR‑115, 2026‑10‑02).
* ⚠️ **No mide constructividad.** `Classical.choice`, `propext` y `Quot.sound` son axiomas del
  núcleo de Lean, no del proyecto, y un footprint no dice de dónde viene un `Classical.choice`.
  Eso lo mide §4 (2026‑09‑27).

---

**Véase también:** `FOL/Inconsistencia.lean` (§1: `derives_to_derives0` y `derives_soundness`; §3: las cuatro
refutaciones), ADR‑114 y ADR‑115 de `../ROBINSON_PlusPlus/DECISIONS.md` (la auditoría de la base y el
borrado), `../ROBINSON_PlusPlus/doc/AUDITORIA-BASE-2026-10-02.md` y
`../ROBINSON_PlusPlus/sondeos/MetaReglasRefutables.lean` (la primera medición), `cuarentena/README.md` (el
registro de por qué se apartó `soundness`, escrito con el diagnóstico que ADR‑115 invirtió),
`../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md` (de dónde sale este documento).
🗑️ Aquí se citaba `FOL/MetaRules.lean` como «la doctrina corregida»: se borró el 2026‑10‑02 (ADR‑115 de RPP).

### 2.6 · ⚠️⚠️ 2026‑09‑13 · `henkin_extension_lemma` SALE — y por eso no se ha tocado

`sondeos/HenkinSaleDeRaa.lean` (ROBINSON_PlusPlus), compilado el 2026‑09‑13. 🗑️ No compila
desde el 2026‑10‑02: usa `FOL.MetaRules.raa` en el código (l. 94 y 114), y `FOL.Core`, su único import, ya no
trae `FOL.MetaRules` (borrado). ADR‑115 de RPP da el sondeo por caído; no se ha re‑ejecutado. Esta sección
es registro, y sus rectificaciones van marcadas ✏️.

🏁 **Es demostrable.** `IsMaximalConsistent S → IsHenkin S` es un teorema, y con él
`henkin_extension_lemma` es `lindenbaum_lemma` más tres líneas ⇒ este módulo llegaría a **CERO
axiomas propios**.

⚠️⚠️ **Y el precio está medido, y no es «1 → 0»:**

| | axiomas propios | footprint de `completeness` |
|---|---|---|
| el 2026‑09‑13 | **1** | `[propext, Classical.choice, Quot.sound, henkin_extension_lemma]` |
| pagándolo | **0** | `[propext, Classical.choice, Quot.sound, **FOL.MetaRules.raa**]` |

Es cambiar **un postulado propio, honesto y con nombre** por **el axioma que hace el cálculo
completo y no sólido** — el mismo que en `cuarentena/Inconsistencia.lean` da `False` en cuanto se
le junta cualquier teorema de solidez. Y obliga a que `Completeness.lean` **importe
`FOL.MetaRules`**, cosa que hoy **no hace** (medido: siete imports, ninguno es `MetaRules` — y
`cuarentena/README.md` §4 presentaba justamente eso como la razón de que este módulo no estuviera
en el radio de la inconsistencia).
✏️ 2026‑10‑02: a `raa` no había que juntarle nada. Su enunciado es refutable (`raa_refutable`), así que Lean
más `raa` ya demostraba `False` (ver «Lo que NO se sigue», abajo).

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
✏️ **Rectificado el 2026‑10‑02** (ADR‑114 L1‑3, ADR‑115 de RPP): la «patología» era un axioma FALSO.
`Derives` **es** sólido —sus 22 constructores: `FOL.Inconsistencia.derives_soundness`—, así que
`derives_complete` se demostraba en un entorno inconsistente, y «las pruebas son legítimas» sólo valía en ese
sentido: eran correctas, a partir de un postulado refutable. Y `⊢` ya no es la herramienta de RPP, que retiró esa capa
el mismo 2026‑10‑02.

#### Lo que NO se sigue

**No** se sigue `False`: el detonador de `Inconsistencia.lean` es `raa` **más solidez**, y este
módulo no demuestra solidez y va en la dirección contraria.

✏️ **FALSO** (rectificado el 2026‑10‑02; ADR‑114 §3 de RPP cita esta línea entre los textos falsos): `raa`
sola ya daba `False`. La solidez no era una hipótesis que hubiera que añadir: la de los 22 constructores
de `Derives` se demuestra por inducción sobre ellos, sin ningún axioma del proyecto, y con ella el enunciado
de `raa` se refuta (`raa_refutable`, `[propext, Quot.sound]`). Con `raa` en el entorno, `False` era
demostrable; que nadie lo escribiera no lo hacía consistente.

### 2.7 · ✅ Decidido: **(A)**, el axioma se queda — y cómo queda protegido

Sancionado por el propietario el **2026‑09‑13** (ADR‑032 §5). Un **0** en este censo se leería como
«Completitud demostrada», y lo que habría detrás es «completitud de un cálculo que, cuando no
deriva `A`, deriva `¬A`». 🔑 *La cifra mejoraría y el contenido empeoraría.*
✏️ 2026‑10‑02: el censo marca hoy **cero** por la razón contraria —no se compró con `raa`: se retiró `raa`—,
y la completitud demostrada es `Canonical0.completeness₀`, sobre el cálculo sólido `Derives₀` (desde el
2026‑09‑16). ADR‑032 quedó sin objeto el 2026‑09‑23, al borrarse el módulo.

⚠️ **Una decisión de NO hacer algo es la más fácil de deshacer por accidente**: el que llegue
después ve un axioma, ve que es demostrable, y lo «arregla». Tres guardas:

| dónde | qué |
|---|---|
| `cuarentena/Completeness.lean` (borrado el 2026‑09‑23), junto al `axiom` | el aviso **en el punto de uso**, con los dos footprints y la orden de **reabrir ADR‑032** antes de tocarlo. ⚠️ Sustituye al comentario que decía «requiere expandir el lenguaje con constantes», **medido FALSO** |
| `check-axioms.bash` | ~~`ESPERADO_CUAR=1` **rompe también si baja a 0**~~ — ⛔ hoy `ESPERADO_CUAR=0`: el 2026-09-23 se borró el módulo, y el axioma con él (ver el banner de cabecera) |
| aquí (§2.6) y `cuarentena/README.md` §9.2 | la medición, con el precio |

⭐ **El control no hubo que cambiarlo**: compara con una cifra **exacta**, no con una cota. Un
contador exacto convierte *«no pagar este axioma»* en algo que el build vigila **solo**.

## 4 · ⭐ Lo no constructivo (auditoría del 2026‑09‑27)

Este censo cuenta los `axiom` **del proyecto**. `Classical.choice` no es uno de ellos: es del núcleo
de Lean, y `#print axioms` lo imprime igual si viene de una elección matemática, de una instancia mal
elegida o de una prueba interna del núcleo. 🔑 *El footprint no distingue las causas*: esta sección
las distingue, **medidas**.

**Método.** `auditoria/constructividad-2026-09-27/Audit.lean` recorre el entorno compilado y, para
**cada** constante de los módulos `FOL*` y `TheoryFramework*`, anota sus axiomas (`collectAxioms`), si
es `noncomputable` y qué constantes usa directamente que también llevan `Classical.choice`. La
**frontera** son las constantes de FOL que usan directamente una constante **externa** con choice: por
ahí entra. La **esencialidad** se mide tomando el ENUNCIADO como hipótesis y derivando de él un
principio clásico sobre un `P : Prop` arbitrario **sin** `Classical.choice`: si compila, ninguna prueba
de ese enunciado puede evitarlo. Los experimentos y cómo relanzarlo:
`auditoria/constructividad-2026-09-27/README.md`. Las decisiones D1–D8: `NEXT-STEPS.md` (❄️) y
ADR‑110 de `../ROBINSON_PlusPlus/DECISIONS.md`.

### 4.1 · Las cifras, antes y después de D1–D8

| medida (`decls.tsv`) | antes (FOL `537cc20`) | después (2026‑09‑27) |
|---|---:|---:|
| constantes de FOL + TheoryFramework | 2978 | 3074 |
| con `Classical.choice` | **157**, en 17 módulos | **84**, en 11 módulos (3 son código meta de `FOL.Tactics`) |
| sólo `propext` y/o `Quot.sound` | 1002 | 1107 |
| sin ningún axioma | 1814 | 1878 |
| dependen de `MetaRules` (borrado el 2026‑10‑02, ADR‑115 de RPP) | 5 | 5 |
| `noncomputable` | 8 | **1** (`SkolemN0.skF`) |
| frontera: declaraciones lógicas por donde entra choice | 30 | **13** (y 3 de código meta, las dos veces) |
| titulares de FOL con choice (filas de `check-footprints`) | 55 de 252 | **34** de 252 |
| filas de `check-footprints` (RPP) | 513 | 517 (4 de `TheoryFramework.Instances`) |

### 4.2 · Por dónde entraba el 2026‑09‑27: las 13 declaraciones de la frontera, y las 3 meta

| clase | entrada | por qué | medida |
|---|---|---|---|
| **esencial** · la semántica de Tarski en `Prop` | `Soundness0.derives0_soundness` | su enunciado implica `¬¬P → P` | ✅ `exp-esencial/E1`, sin ningún axioma |
| | `SequentSound0.lkc_sound` | implica `P ∨ ¬P` (multiconclusión) | ✅ `E1` |
| **esencial** · el lema de la verdad sobre un maximal ARBITRARIO | `Lindenbaum0.max_cons_contains`; `Canonical0.max_cons_impl_iff`, `max_cons_or`, `max_cons_complete`, `max_cons_forall` | cada enunciado implica `¬¬P → P` (testigo: un maximal consistente hecho a medida de `P`) | ✅ `E3`, `[propext, Quot.sound]`; `max_cons_forall`, en `exp-esceptico/Esc2` |
| **esencial, como hipótesis** · Markov | `Canonical0.completeness₀`, su `byContradiction` final | la completitud para `Γ` finita implica MP (Kreisel; Forster–Kirst–Wehr 2021) | ⚠️ argumento, no compilado |
| **esencial** · las funciones de Skolem semánticas | `SkolemN0.skF`, `skF_spec` | «todo modelo admite expansión de Skolem» implica AC (`∀∃ → ∃f`), y AC implica EM (Diaconescu) | ✅ `E6`, `[propext, Quot.sound]` |
| **ruta semántica** de un enunciado SINTÁCTICO | `Skolem0.skolem_conservative₀` | la ruta por modelos pide un testigo `w` con `(∃A) → A[w]`, y eso implica EM; su caso Henkin (`t̄ = []`) ya sale sin choice, `henkin_conservative₀` | ✅ la ruta, `E6b`; la vía sintáctica general (Herbrand/ε), fuera de alcance |
| **control** (ADR‑061) | `Canonical0.derives0_em`, `derives0_peirce` | controles de no vacuidad de `completeness₀`: se prueban POR ella, a propósito. Los gemelos sin choice existen: `Propositional0.derives0_em_ctx` (ningún axioma), `derives0_peirce_prop` | — |
| **meta**, fuera del cómputo lógico | `FOL.Tactics`: `tryMem`, `tryMem._unsafe_rec` y el elaborador de `derive_hyp` | lo traen los TIPOS del marco meta de Lean (`MetaM`, `CoreM`, `TacticM`…); ninguna constante fuera del módulo las usa | `exp-varios/Tac` |

🗑️ **Y `Derives`** (la herramienta de RPP hasta el 2026‑10‑02), que no es cuestión de elección: desde ADR‑115
de RPP **no tiene ningún `axiom`**. Los cuatro del registro de §1.1 eran postulados suyos, y este párrafo los
llamaba «inconsistentes con cualquier semántica sólida», con `Inconsistencia.inconsistencia_de_cualquier_solidez`
(borrado; footprint `[propext, FOL.MetaRules.raa]`) por prueba. ✏️ Lo eran con **Lean mismo**: sus enunciados
se refutan sin usarlos (`FOL/Inconsistencia.lean` §3). Medido el 2026‑09‑27 sobre `537cc20`
(`exp-varios/Reach.lean`): dependían de ellos 5 constantes de FOL + TheoryFramework (los cuatro y aquel
teorema; `imp_intro`, `or_elim` y `ex_elim` no tenían ningún usuario en FOL) y 349 de RPP, 354 en el entorno
completo; tras D1–D8 las 5 de FOL eran las mismas. Hoy no depende de ellos nada: en FOL se borraron el módulo
y el teorema, y RPP retiró su capa `⊢` el mismo día.

### 4.3 · Los 34 titulares que conservan `Classical.choice`

| grupo | titulares | nº |
|---|---|---:|
| esenciales, MEDIDO: el enunciado implica un principio clásico | `derives0_soundness`, `lkc_sound`, `lk0_sound`, `max_cons_contains`, `max_cons_complete`, `max_cons_neg`, `truth_lemma₀` (`¬¬P → P` o `P ∨ ¬P`); `model_existence_lemma₀` (`¬P ∨ ¬¬P`); `consistency_of_satisfiable₀` (`¬¬∀n (P n ∨ ¬P n)`); `eval_skolemAxN` (AC) | 10 |
| esenciales por inclusión inmediata | `derives0_complete_iff`, `model_existence_iff₀`, `model_existence_countable₀` | 3 |
| esencial como hipótesis (Markov) | `completeness₀` | 1 |
| semánticos sin clasificar | `compactness`, `loewenheim_skolem_down`, `infinite_model_of_large_fresh`, `infinite_model_of_large`, `countable_infinite_of_infinite` | 5 |
| enunciado SINTÁCTICO; choice sólo por la ruta semántica | `skolem_conservative₀`, `skolem_conservative_n₀`, `skolem_conservative_nf₀`, `derives0_of_skolemNF`, `derives0_neg_iff_neg_skolemNF`, `herbrand_refutation₀`, `herbrand_validity₀`, `herbrand_validity_ctx₀` | 8 |
| corolarios de RUTA conservados a propósito (ADR‑061), todos con variante sin choice medida | `derives0_em`, `derives0_peirce` (controles); `derives0_consistent`, `derives0_not_complete` (`Soundness0` 🧊); `lk0_not_empty`, `lk0_to_derives0`, `lk0_to_derives2` (`SequentSound0` 🧊) | 7 |

Los 27 primeros son los **irreducibles** de la auditoría, con la clasificación que dejó el escéptico:
pasó `max_cons_neg` y `truth_lemma₀` de hipótesis a medidos, y `consistency_of_satisfiable₀`, que el
juez dejaba sin clasificar («probablemente constructiva»), a esencial medido.
Salieron **21** titulares: `derivesSet0_intro_impl`, `henkin_step_consistent₀`, `hen_consistent`,
`henLimit_consistent₀`, `henLimit_witness`, `lindenbaum_lemma₀`, `henkin_completion₀`,
`cst_bound_sym`, `cst_bound_formula`, `exists_fresh`, `instFreshSymString`, `derivesSet0_shift_inv`,
`shiftTheory_consistent₀`, `natToString_surj`, `natToFormula_surj`, `instEnumSymString`,
`evalTerm_updateCsts`, `infTheory_finSat`, `derives0_rename_conservative`, `henkin_conservative₀` y
`derives0_no_disjunction_property`.
✏️ 2026‑10‑05 (D7, ADR‑129 de RPP): tres de esos nombres eran de `String` y ya no existen: `instFreshSymString`
es hoy `FOL.Fresh0.instFreshSymListChar` (ningún axioma), `natToString_surj` es `natToSym_surj`, e
`instEnumSymString` se retiró (queda `instEnumSymListChar`, `[propext, Quot.sound]`). Y `evalTerm_updateCsts` ya
no depende de ningún axioma.

### 4.4 · Lo que D1–D8 quitó, con los mismos enunciados

| entrada, antes | causa medida | arreglo |
|---|---|---|
| `Fresh0.cst_zero_ne`, `cst_ne_shift` | la síntesis de `ReflBEq String` para `not_eq_of_beq_eq_false` pasaba por `String.instOrd`, y el orden de `String` decodifica UTF‑8 | `of_decide_eq_false rfl` (`String.decEq`, sin axiomas) ⇒ `[propext]`. ✏️ D7 (2026‑10‑05): la misma prueba, sobre la igualdad decidible de `List Char`; la instancia que los usa, `instFreshSymListChar`, no depende de ningún axioma |
| `Fresh0.cst_bound_sym` | tercio excluso sobre `∃ k, cst k = s` | una cota por tamaño en bytes (`cst_utf8ByteSize`) ⇒ `[propext, Quot.sound]`. ✏️ D7 (2026‑10‑05): la cota es hoy `s.length`, por `cst_length`; `cst_utf8ByteSize` ya no existe; mismo footprint |
| `Enumeration.natToString_surj` | `String.toList`/`ofList_toList` decodifican UTF‑8 | `String.exists_eq_ofList` ⇒ `[propext, Quot.sound]`. ✏️ D7 (2026‑10‑05): hoy es `natToSym_surj`, sin `String`; mismo footprint |
| `Henkin0.henkin_step_consistent₀`, `Lindenbaum0.derivesSet0_intro_impl` | un `open Classical` para decidir `x = H` en un `filter` | `ctx_split`, sin ningún axioma: el contexto finito se parte sin decidir la igualdad |
| `HenkinLimit0.bnd`, `bnd_spec` | `Exists.choose` sobre `cst_bound_formula` | `bnd` CALCULADA por recursión (`bndTerm`, `bndTerms`: el máximo de `utf8ByteSize`; ✏️ D7, 2026‑10‑05: hoy, de la longitud), sin axiomas; `bnd`, `hidx` y `hen`, computables |
| `Lindenbaum0.LindenbaumStep` y sus pruebas | `if IsConsistent₀ … then … else …`, decidido con `Classical.propDecidable` | la etapa IMPREDICATIVA (la condición va dentro del predicado) y `lindenbaum_limit_closed` |
| `Rename.invOf`, `invOf_spec` | una inversa global ELEGIDA (`Exists.choose`) | retiradas: `Fresh0.unshift` (inversa global y computable de `shift`, sobre bytes; ✏️ D7, 2026‑10‑05: hoy un `match` sobre `'f' :: t`, y `unshift_shift` es `rfl`) y `Rename.locInv` (inversa local sobre la lista finita de símbolos) |
| `Canonical0.quotientOut`, `quotientOut_eq` | `Classical.choose` de un representante | retiradas: el modelo canónico se levanta con `Quot.lift` sobre listas (`listQuot`). ⚠️ La CONSTANTE, con su especificación, implicaba el tercio excluso (medido): lo evitable era su USO |
| `substTerm_subst_comm_succ` y su familia (`Theorems/Eq`) | tres `simp` usaban `Nat.left_eq_add`/`Nat.add_eq_left`, que en v4.31 llevan choice | `simp [-Nat.left_eq_add, -Nat.add_eq_left, …]` ⇒ `[propext, Quot.sound]`; `FOL.Core` queda sin choice salvo el código meta de `Tactics` |
| `Skolem0.henkin_conservative₀` (D3, D5) | era el corolario `t̄ = []` de `skolem_conservative₀`, semántico | la vía SINTÁCTICA (`henkin_step_derives`, `ctx_split`, `dne_rule`) ⇒ `[propext, Quot.sound]` |
| `Inconsistencia.derives0_no_disjunction_property` (D3) | lo heredaba de `derives0_not_complete` (semántica en `Prop`) | la valuación booleana de `Finitary0` (`derives0_not_negP_fin`, `derives0_not_complete_fin`) ⇒ `[propext, Quot.sound]` |

🧊↩️ `Rename` estaba congelado: se descongeló con `thaw --confirm` para retirar `invOf` (D1).
⭐ Y lo que la auditoría NO tuvo que tocar: la migración `String` → `List Char` (D7 del 2026‑09‑26)
no hacía falta. Lo que trae `Classical.choice` en v4.31 es **decodificar UTF‑8** (y el orden de
`String`, que decodifica); la capa de bytes (`String.decEq`, `utf8ByteSize`, `toByteArray`,
`ofByteArray`) está limpia.
✏️ **2026‑10‑05 · D7 EJECUTADA** (ADR‑129 de RPP): el propietario la reabrió («completar la sustitución
String->List Char») y los símbolos son hoy `List Char`: ninguna aparición de `String` en el código (sin
comentarios) de `FOL/` y `TheoryFramework/`, medido. Lo de la capa de bytes era cierto para `String`, y es
registro. «No hacía falta» deja de valer: la migración se hizo por decisión del propietario, y en RPP 44 filas
pierden `Classical.choice`. En FOL ninguna de las 39 filas con él (con las de `TheoryFramework`) lo pierde; lo que
cambia es menor: `FOL.Fresh0.instFreshSymListChar` (la de `String`, `[propext, Quot.sound]`),
`Compacity0.evalFormula_updateCsts` y `evalTerm_updateCsts` (antes, `[propext]` y `[propext, Quot.sound]`) ya no
dependen de ningún axioma.

### 4.5 · ⛔ La tesis del WKL, rectificada (D2)

ADR‑040 §2 y ADR‑041 §4 (RPP) y muchas docstrings decían que el `Classical.choice` de la completitud
«es el WKL del `if IsConsistent₀` de Lindenbaum», y que ahí cabía «toda la no‑finitud». **En Lean es
FALSO, y está medido**: un predicado en `Prop` no tiene que ser decidible, y la etapa de Lindenbaum se define con la condición
DENTRO, sin decidirla, y `lindenbaum_lemma₀` y `henkin_completion₀` son hoy `[propext, Quot.sound]`.

* El WKL es necesario en aritmética de segundo orden —completitud ⇔ WKL₀ sobre RCA₀ (Simpson,
  *SOSOA* IV.3.3)— porque allí la extensión maximal tiene que EXISTIR como conjunto definible. En CIC
  el conjunto se define gratis; lo clásico aparece al USARLO.
* Lo clásico de la completitud, en Lean, es lo de §4.2: el lema de la verdad sobre un maximal
  ARBITRARIO, la semántica de Tarski en `Prop` y el `byContradiction` final de `completeness₀`.
* Regla de redacción (D2, opción b): se corrige toda afirmación de LOCALIZACIÓN («el choice de X es
  el WKL», «aquí está toda la no‑finitud», «el WKL de Lindenbaum»); «el WKL» puede quedar como apodo
  de la FUERZA lógica: *la completitud tiene la fuerza del WKL sobre RCA₀*.
* 🧊 ✅ **Rectificado el 2026‑09‑28 en `FOL/SequentSound0.lean`**, el único congelado al que la regla
  no había llegado: su cabecera decía dos veces que las versiones de `Finitary0`/`Interpolation0`
  miden `[propext, Quot.sound]` «en vez del **WKL**», y el docstring de `lk0_not_empty`, que arrastra
  «el `Classical.choice` que ADR‑041 identificó como el **WKL**». `thaw --confirm` autorizado por el
  propietario, tres correcciones de texto (código idéntico) y congelado de nuevo en el mismo ciclo. Los
  otros 22 congelados no lo LOCALIZAN: o no lo nombran, o lo citan para rectificarlo o como apodo de la
  FUERZA (medido con `grep WKL`, 2026‑09‑27).

### 4.6 · Lo que esta sección NO dice

* ⚠️ `propext` y `Quot.sound` son extensionalidad, no decisión ni elección: sin `Classical.choice` no
  dan el tercio excluso (Diaconescu necesita elección). Por eso los experimentos de esencialidad pueden
  concluir con footprint `[propext, Quot.sound]`.
* ⚠️ Lo irreducible lo es **para los enunciados tal como están** (un maximal arbitrario, la semántica
  en `Prop`). Las variantes constructivas (`[DecidablePred S]`, semántica ¬¬ o de Kripke, los modelos
  «explosivos» de Krivine) y la vía sintáctica general de Skolem (Herbrand/ε) quedan fuera de alcance
  (`NEXT-STEPS.md`).
* ⚠️ Las cifras de esta sección son del 2026‑09‑27 y **no se han re‑medido** tras ADR‑115 (2026‑10‑02), que
  borró `FOL/MetaRules.lean` y reescribió `FOL/Inconsistencia.lean`: salen `inconsistencia_de_cualquier_solidez`
  y su auxiliar `ctx_nil`, y entran `derives_to_derives0`, `derives_soundness` y las cuatro refutaciones con
  sus auxiliares. Según los footprints medidos ese día (el bloque FOOTPRINT al final de aquel fichero),
  `derives_to_derives0`, `imp_intro_refutable`, `raa_refutable` y `or_elim_refutable` quedan en
  `[propext, Quot.sound]`, y `derives_soundness` y `ex_elim_refutable` llevan `Classical.choice`, por los
  modelos de Tarski en `Prop`.
* ⚠️ La columna de usos en RPP del registro de §1.1 es del 2026‑09‑12. Hoy ningún módulo de la librería de
  RPP (`ROBINSON_PlusPlus/`) importa ni usa `FOL.MetaRules` (medido el 2026‑10‑02: `grep -F 'FOL.MetaRules'`
  da un comentario de registro; con `MetaRules`, seis comentarios en seis módulos de la librería de RPP, y los
  tres que este borrado dejaba desfasados —`Meta/ReprPrf.lean:47`, `Minimal/Axioms.lean:1060`,
  `Meta/HilbertDeduction.lean:67`— se corrigen en el paso de RPP que sigue, ADR‑115 §8). Fuera de la librería
  aún lo usan en código algunos ficheros de `sondeos/` y de `Probe/`, que citan nombres borrados (los de
  `sondeos/` los clasifica ADR‑115 de RPP §5).
