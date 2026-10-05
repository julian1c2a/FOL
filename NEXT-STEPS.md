# Próximos Pasos — FOL

> # ⛔⛔ AVISO DE ESTADO — 2026-09-26, retocado el 2026-10-02 (reescrito: el del 2026-09-12 había quedado FALSO). LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | 🏁 **Sí, sobre `Derives₀`** (2026-09-14): `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` (`FOL/Soundness0.lean`), y con ella `derives0_consistent`. 🏁 **Y sobre `Derives`**, el enunciado de la columna izquierda, desde el 2026-10-02: `derives_soundness : Γ ⊢ f → Γ ⊨ f` (`FOL/Inconsistencia.lean` §1), porque sin meta‑reglas `Derives` se traduce a `Derives₀` (`derives_to_derives0`: `gen_rule` es admisible). Hasta ese día esta celda decía que la de `Derives` era «FALSA en presencia de `FOL/MetaRules.lean`»: lo falso era `raa` (`raa_refutable`, §3), y el módulo se borró (ADR‑115 de RPP) |
> | «Compacidad» ✅ | 🏁 `compactness`, `loewenheim_skolem_down` y el modelo infinito `infinite_model_of_large`, en `FOL/Compacity0.lean`. El `Compacity.lean` vacuo **se borró** el 2026-09-23 |
> | «Completitud» ✅ / «1 sorry» | 🏁 `completeness₀ : Γ ⊨ f → Γ ⊢₀ f` (`FOL/Canonical0.lean`, 2026-09-16), con **cero axiomas del proyecto**: `[propext, Classical.choice, Quot.sound]`. Ese `Classical.choice` viene del lema de la verdad sobre un maximal arbitrario (`max_cons_*`) y del `byContradiction` final de `completeness₀`; **no** del `if` de `Lindenbaum0`, que ya no decide nada (`lindenbaum_lemma₀` es `[propext, Quot.sound]`). Hasta el 2026-09-27 esta celda decía que era «el WKL de `Lindenbaum0`» (ADR-041): refutado, ADR-110 y `AXIOMS.md` §4. `Completeness.lean` y su último postulado, `henkin_extension_lemma`, **se borraron** el 2026-09-23. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **0 `axiom`**: los cuatro de `FOL/MetaRules.lean` (`imp_intro`, `raa`, `or_elim`, `ex_elim`), refutables sin usarlos (`FOL/Inconsistencia.lean` §3), se borraron con el módulo el 2026-10-02 (ADR‑115 de RPP). Esta celda decía «4 `axiom`, los de `MetaRules` que el kernel obliga»: el kernel sólo impedía que fueran constructores (premisa‑función, ocurrencia no positiva), no obligaba a tenerlos · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026-09-12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Los seis teoremas del cierre (T1 a T6, 2026-09-23 y 2026-09-26) están en el árbol**, sobre `Derives₀`; el catálogo, en `CURRENT-STATUS-PROJECT.md` («Estado vigente») y `REFERENCE.md` §6. ⛔ Y lo que NO hay: la propiedad de disyunción para `Derives₀` es **FALSA** (`derives0_no_disjunction_property`).
> (Este aviso decía que «lo único sólido MEDIDO» era `prf0_soundness` (hoy `prfI_soundness`), en RPP: dejó de serlo el 2026-09-14.)
> ✅ **2026-10-03 · deuda saldada**: los cinco módulos 🧊 que conservaban el texto anterior al borrado de `FOL/MetaRules.lean` (`Soundness0`, `Canonical0`, `Compacity0`, `Rename`, `TheoryFramework/Instances/FOL`) se descongelaron con autorización del propietario, se corrigieron sólo sus comentarios y se volvieron a congelar: registro por línea, abajo, en «Lo que queda».
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md` · ADR‑114 y ADR‑115 de `../ROBINSON_PlusPlus/DECISIONS.md` (2026-10-02)

**Last updated:** 2026-10-05 — D7 ejecutada (ADR‑129 de RPP): la fila D7 de «Decisiones del propietario» pasa de «CERRADA como ABANDONADA» a EJECUTADA (los símbolos son `List Char`), con lo que decía como registro; una nota en «Hecho» y otra en ❄️ (16 de los 23 congelados, descongelados para la sustitución). Antes, 2026-10-03 — la deuda de los cinco módulos 🧊 con textos falsos, SALDADA: `thaw` autorizado por el propietario, sólo comentarios, re‑congelados en el mismo ciclo; y la línea de `SequentSound0` (D2), puesta al día. Antes, 2026-10-02 — 🗑️ `FOL/MetaRules.lean` borrado (ADR‑115 de RPP: sus cuatro `axiom` eran refutables): aviso, sección nueva al principio de «Lo que queda» con la deuda de cinco módulos 🧊 que esperan un `thaw` autorizado, y la fila X1 (PeanoRF cae: importa `FOL.MetaRules`). Antes (2026-09-27): N5 y N7, resueltas por el propietario (N5: los nombres técnicos son auxiliares, regla escrita en `NAMING-CONVENTIONS.md` §9; N7: `herbrand_of_skolemNF₀` reforzado con la ecuación); 🧊 tercer lote congelado (8 módulos: 23 en total; de los 19 de la tercera criba sólo queda fuera `Inconsistencia`, por X1). Antes, el mismo día: 🧊 segundo lote congelado (10 módulos: 15 en total); quedan N5, N7 y X1. Antes, el mismo día: la tercera criba con refutación: 10 congelables (4 ya, 6 con sus correcciones aplicadas), decisiones N5 y N7; N6 aplicada. Antes, el mismo día: la auditoría de constructividad y las decisiones D1‑D8 del propietario, ejecutadas (`Classical.choice` 157 → 84 constantes; Lindenbaum y Henkin sin él; la tesis del WKL, rectificada; la instancia de `TheoryFramework`, declarada; `Rename` descongelado para retirar `invOf`); los 17 candidatos, sólo bloqueados. Antes, el mismo día: N1‑N4 resueltas y aplicadas (13 renombres, dos duplicados retirados; `PrenexNF0`/`SequentSound0` descongelados y re‑congelados); los 10 congelables, sólo bloqueados. Antes, el mismo día: la segunda criba con refutación (71 correcciones). Antes, el mismo día: P4 hecha (`QFDecide0`). Antes, el mismo día: 🧊 cinco módulos congelados; P2 (18 renombres) y P3 (`sub_*` en `Sequent0`) hechas. Antes, el mismo día: W2, W3 y W4 hechas; la criba de congelación, pasada con refutación (1 congelable ya, 4 tras arreglos —aplicados—, 18 todavía no). Antes (2026-09-26): aviso reescrito y sección «Lo que queda» nueva; el plan de fases de abajo es HISTÓRICO (2026-05-16).
**Autor**: Julián Calderón Almendros

## ⬜ Lo que queda para CERRAR FOL — 2026-09-26 (noche); al día el 2026-10-02

**Hecho**: los seis teoremas del catálogo del cierre (T1-T6) más `inv_allR`/`inv_exL` (RPP-100), y
las decisiones D1, D2, D4, D5, D6 y D7 del propietario, **ejecutadas** el 2026-09-26 (RPP-101, RPP-102;
`CHANGELOG.md`; ✏️ 2026-10-05: D7 EJECUTADA, ADR‑129 de RPP: la de entonces la cerraba como ABANDONADA; fila D7, abajo); y las D1‑D8 de la auditoría de constructividad, el 2026‑09‑27 (RPP‑110; abajo, en ❄️).
El estado vigente, en `CURRENT-STATUS-PROJECT.md`. Lo que queda:

### 🗑️ 2026-10-02 · `FOL/MetaRules.lean` BORRADO (ADR‑115 de RPP) — y la deuda que deja

Decisión del propietario (ADR‑114 §4, punto 2, de RPP: «no hacemos uso de herramientas que no sean
verdaderas»), ejecutada en RPP como ADR‑115 y en FOL el mismo día:

| qué | estado |
|---|---|
| `FOL/MetaRules.lean` y sus cuatro `axiom` (`imp_intro`, `raa`, `or_elim`, `ex_elim`) | 🗑️ **borrados**: eran REFUTABLES sin usarlos. `FOL.Core` ya no lo importa |
| `FOL/Inconsistencia.lean` | ✅ **reescrito**: §1 `derives_to_derives0` (`gen_rule` es admisible) y `derives_soundness`; §2, la propiedad de disyunción, sin cambios; §3, los enunciados `ImpIntro`, `Raa`, `OrElim`, `ExElim` y sus refutaciones. `inconsistencia_de_cualquier_solidez` **se borró**: su enunciado era FALSO (sólo se «demostraba» con `raa`). Sigue fuera de la congelación (X1) |
| censo | `axiom` de Lean: 4 → **0** (`check-axioms.bash`, `ESPERADO_FOL=0`) · módulos activos: 55 → **54** (`FOL/`: 44 → 43) |
| ✅ cinco módulos 🧊 CONGELADOS con textos falsos (ya lo eran al escribirse; el diagnóstico del 2026-10-02 los dejó a la vista) | **saldada el 2026-10-03**: `thaw` autorizado por el propietario, sólo comentarios, re‑congelados en el mismo ciclo. La lista, debajo, como registro |
| PeanoRF (X1) | ⛔ cae `PeanoRF/Prelim.lean` (importa `FOL.MetaRules`) y lo que lo importa; los módulos de `Calculus/`, no (fila X1). El propietario lo previó por escrito al bloquearlo; PeanoRF está bloqueado y no se toca |
| RPP, en el push que sigue a éste | `check-estratos` (`Derives` 22 · 0), las filas `FOL.Inconsistencia.*` de `check-footprints.bash` y el prefijo de la caché de la CI (ADR‑115 §7) |

La deuda, por fichero, como REGISTRO (saldada el 2026-10-03; citas sin su negrita, con las líneas de antes del `thaw`):

* `FOL/Soundness0.lean` — l. 27‑30 («La solidez de `Derives` es FALSA», con footprint
  `[propext, FOL.MetaRules.raa]` y la causa en M‑11), l. 45‑48 y 228‑231 («`Derives` es sintácticamente
  completo» porque `raa` toma una función de Lean), l. 56‑60 («lo que la invalidaba era el tipo sobre el
  que inducía»; «Cuando un teorema cae por M‑11 … lo que hay que cambiar es el sujeto») y l. 208 («Para
  `Derives` esto no se puede: su solidez es falsa»).
* `FOL/Canonical0.lean` — l. 31‑32 («sobre `Derives` no puede haberlas: su solidez es FALSA … y
  `axioms ⊢` es sintácticamente completo»).
* `FOL/Compacity0.lean` — l. 31 («la solidez de `Derives` es falsa (M‑11)»).
* `FOL/Rename.lean` — l. 33 («Sobre `Derives` es ilegítimo (M‑11: cuatro axiomas lo habitan)») y l. 279
  («Sobre `Derives` esto sería M‑11 en estado puro»).
* `TheoryFramework/Instances/FOL.lean` — l. 29‑30 («`FOL.Metamath.Soundness.soundness` (FALSA: con las
  meta‑reglas, cualquier testigo suyo da `False`, `FOL/Inconsistencia.lean`)»), l. 33‑34 («el cálculo
  CONTAMINADO … `SoundLogic` (inhabitable)») y l. 40 («La herramienta `Derives` sigue SIN instancia, y es
  correcto: su solidez es falsa»).

Lo que es verdad hoy, y contra lo que se contrastaron en el `thaw`: sin meta‑reglas, `Derives` es
`Derives₀` más una regla admisible; es **sólido** (`derives_soundness`), **no** es sintácticamente
completo (`⊬ P` y `⊬ ¬P`: `derives_not_P`, `derives_not_negP`) y la inducción sobre él es legítima. Lo
falso eran las meta‑reglas, no la solidez.

### Decisiones del propietario

| # | qué | estado |
|---|---|---|
| D1 | `Tactics2.lean` | ✅ **borrado** (idéntico, salvo el `import`, a la copia de `FOL_poli`) |
| D2 | `IsSyntacticallyComplete₀`, por pertenencia | ✅ **`IsMemComplete`** (sin subíndice: no depende de cálculo; y libre el nombre canónico para la teoría completa sobre sentencias) |
| D3 | Las dos **ABIERTA** de `[G.2]` (el propietario: «vamos a por D3») | ✅ **CERRADA, las dos.** **D3b**: `SkolemHerbrand0.herbrand_validity_ctx₀` — `Γ ⊢₀ φ` sii certificado de Herbrand para la forma de Herbrand de `Γ ⇒ φ`; no había que mover la negación, sino skolemizar lo que se refuta. **D3a**: `Interpolation0.craig₀` — Craig para `⊢₀` CON igualdad, `[propext, Quot.sound]`, vía el puente `lk0_to_lkp`; sin borrar predicados (la partición de Maehara basta) |
| D4 | La vía de `ModelG` | ✅ medida TERMINADA y **CERRADA definitiva** (sin receta de reapertura; fuera de `[G.2]`) |
| D5 | El refactor de `Lift0` | ✅ **hecho**: núcleo genérico `absTerm'` en `Eigenvariable`; 40 nombres conservados; −56 líneas de código (no «~150»); una inducción y un transporte menos |
| D6 | ¿Qué marca `₀`? | ✅ **regla decidida** (`NAMING-CONVENTIONS.md` §9, FOL **y** RPP): `₀` clásico, `ᵢ` intuicionista, sin subíndice lo que no depende de cálculo. Renombres: `model_existence_iff₀`, `compactness`, `IsHenkin`, `DisjunctionProperty₀`; RPP `Prf₀` → `Prfᵢ`. Y `Prf` (el Hilbert clásico de RPP) **se queda sin subíndice**: decisión del propietario (2026‑09‑26), excepción histórica como `Derives` en FOL |
| D7 | Migración `String`→`List Char` | ✅ **EJECUTADA el 2026‑10‑05** (ADR‑129 de RPP). El propietario la reabrió: «la decisión es completar la sustitución String->List Char, D7 se cierra solo cuando esté completamente lista y terminada la sustitución». `Term`, `Formula` y `Model` van sobre `List Char`; `Fresh0` (`shift s = 'f' :: s`, `cst_length`, `unshift` por `match`), `Enumeration` (`natToSym`, `natToSym_surj`) y el resto de la cadena, sin `String`; retirados `Coe String Formula`, la instancia `EnumSym String` y la de medida de `SymClasses`. Prueba de cierre, medida: ninguna aparición de `String` en el código (sin comentarios) de `FOL/` y `TheoryFramework/`, y ningún literal de símbolo. Footprints: las 39 filas de FOL y `TheoryFramework` con `Classical.choice` lo siguen llevando; `instFreshSymListChar`, `evalFormula_updateCsts` y `evalTerm_updateCsts` no dependen de ningún axioma; en RPP, 44 filas pierden `Classical.choice`. Los 16 módulos 🧊 que toca se descongelaron con `thaw --confirm` (autorizado por la decisión) y se vuelven a congelar tras el commit (❄️). ⚠️ Hasta ese día esta celda decía «✅ **CERRADA como ABANDONADA en FOL** (no estaba terminada; instanciar no mueve ningún footprint titular)» (2026‑09‑26) y, 📝 2026‑09‑27, «y no hacía falta»: lo que trae `Classical.choice` a `String` en v4.31 es DECODIFICAR UTF‑8 (y el orden de `String`), y la auditoría de constructividad lo quitó de `Fresh0`/`Enumeration` sin migrar. Era cierto para `String`; «no hacía falta» valía para el `Classical.choice` de FOL, no para el de RPP |

### Externo

| # | qué |
|---|---|
| X0 | ⛔ **Condición del propietario, no negociable: FOL no depende de nada más allá de sí mismo.** ✅ Comunicada: `RESPUESTA-PEANORF-2026-09-26.md` (lo que hoy la incumple, con file:line: los siete importan `PeanoRF.Prelim`, que trae RPP y Peano; `Collapse`/`Eq` usan `zero`/`succ` de RPP; `Eq` recibe `FOL.substTerm_liftTerm` a través de RPP; y el parámetro de `collapseT` tiene que ser un SÍMBOLO, no «un término cerrado») |
| X1 | **PeanoRF**, propuesta (C): los siete módulos de `Calculus/`, hechos por PeanoRF según su `BLOQUEO-2026-10-01.md` («ya está hecha por vuestra parte (PRF‑050)») y sin integrar en FOL. Al recibirlos: namespace de FOL, los renombres de D6 en `Slash` (`derivesI_…`), `fdepth` fuera, filas de footprint, `[G.2]`, proyección, y `lock` para `Eq`/`Collapse`/`Slash`. 📨 **D8 (2026‑09‑27)**: no responde desde el 2026‑09‑23; sin plazo fijado: la información va en una carta que se deja en su repositorio (`../Peano-from-ROB-n-FOL/`), y el propietario se la pasa. ⛔ **2026‑10‑02**: `PeanoRF/Prelim.lean` importa `FOL.MetaRules`, borrado (ADR‑115 de RPP), y `Omega/Basic.lean` crea alias de sus axiomas ⇒ cae el build de PeanoRF (`Prelim` y lo que lo importa: la raíz `PeanoRF.lean`, `Omega/Basic`, `Meta/AxiomCheck`, `_template`). Los módulos de `Calculus/` NO caen por esto: no importan `Prelim` ni `FOL.Core`/`FOL.MetaRules` (medido el 2026‑10‑02, sólo lectura). El propietario previó la rotura por escrito al bloquearlo (`../Peano-from-ROB-n-FOL/BLOQUEO-2026-10-01.md`); PeanoRF sigue bloqueado y no se toca. |

### Trabajo

| # | qué |
|---|---|
| W1 | ✅ **hecha** la pasada de higiene de docstrings (58 correcciones en 16 módulos) |
| W2 | ✅ `REFERENCE.md` contrastado con el árbol: §2 regenerado de las líneas `import`, §3.13, §7.1, §3.1/§3.10‑§3.12 (módulos borrados) y ~20 afirmaciones falsas más (60 ediciones, 2026‑09‑27) |
| W3 | ✅ `DEPENDENCIES.md` **regenerado** por `py gen-dependencies.py` (54 módulos, 97 aristas; `--check` dice si está al día); fuera de la deuda de `[E]` |
| W4 | ✅ `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`: filas obsoletas anotadas (Barendregt general, la tabla de §8, citas a `Completeness.lean`, `ESPERADO_CUAR`, §6.11/§6.12, §9) |

### ❄️ Congelación

🧊 **Congelados el 2026‑09‑27** (confirmado por el propietario tras la criba con refutación, RPP‑104):
`PrenexNF0`, `Prenex0`, `SequentSound0`, `Soundness0`, `Rename`.
🧊 **Segundo lote, el mismo día** (propietario: «congela lo congelable», tras la tercera criba; RPP‑112):
`Compacity0`, `Inversion0`, `QFDecide0`, `SkolemN0`, `Craig0`, `Interpolation0`, `Canonical0`, `Fresh0`,
`HenkinLimit0` y `TheoryFramework/Instances/FOL`. ⇒ **15 congelados**. 🧊 **Tercer lote, el mismo día** (N5 y N7 resueltas, abajo; RPP‑112): `Henkin0`, `Skolem0`, `Lindenbaum0`, `SkolemNF0`, `SkolemHerbrand0`, `Hauptsatz0`, `HerbrandBlock0` y `BlockExtraction0` ⇒ **23 congelados**. ⚠️ `Fresh0` 🧊 cita por su título
la sección «Dónde está, y dónde NO está, lo clásico de la completitud» de `Lindenbaum0` (🧊 también, desde el tercer lote):
ese título no debe cambiar.
🧊↩️ **2026‑10‑05 · D7** (ADR‑129 de RPP): 16 de los 23 —los 14 cuyo código cambia con la sustitución, y
`Compacity0` y `Lindenbaum0`, sólo prosa— se descongelaron con `thaw --confirm`, autorizado por la decisión
del propietario, y se vuelven a congelar tras el commit (fila D7, arriba); y se re‑bloquean los 27 que salieron
de `locked_files.txt`.

Decisiones de la criba, resueltas el mismo día: **P2** ✅ los 18 titulares renombrados por la regla de
subíndices (`hauptsatz₀`, `cut_elimination₀`, `herbrand₀`, `herbrand_block₀`, `truth_lemma₀`,
`lindenbaum_lemma₀`, `skolem_conservative*₀`…; y `maeharaₚ`/`craigₚ` para `LKp`); **P3** ✅ los cinco
`sub_*` deduplicados en `Sequent0`; **P4** ✅ la OFERTA de `Hauptsatz0` (versión acotada de
`derives0_qf_iff`), **HECHA** (propietario: «hacemos la versión acotada»; RPP‑107): `FOL/QFDecide0.lean`,
`derives0_qf_iff_bounded` y `decideDerives0QF`, `[propext, Quot.sound]`; la cota ingenua por subtérminos
es FALSA y la correcta añade «mezclas de prefijo» (un paso, no un cierre); decisor de juguete (2^átomos).

**Segunda criba con refutación (2026‑09‑27, RPP‑108)**, sobre los 18 que deja pasar la parte medible:
71 correcciones de comentarios y docstrings aplicadas (código idéntico; `CHANGELOG.md`). Veredicto:
10 congelables — `Interpolation0`, `Craig0`, `QFDecide0`, `Inversion0`, `Skolem0`, `SkolemN0`,
`SkolemHerbrand0`, `Canonical0`, `Compacity0`, `Henkin0` — y 8 retenidos por cuatro decisiones.

**Las decisiones, resueltas por el propietario el mismo día (RPP‑109):**

| # | pregunta | decisión | hecho |
|---|---|---|---|
| N1 | once definiciones POR DERIVABILIDAD sin marca, contra la regla 1 de §9 | **renombrar** (no escribir excepción) | ✅ `CutAdm₀`, `CutAt₀`, `CutBelow₀`, `LeftPrin₀`, `CutElim₀`, `NDtoLK₀`, `HerbrandExtraction₀`, `HerbrandExtractionBlock₀`, `ImpAll₀`, `IffAll₀`, `PwEq₂`. `PrenexNF0` (define `ImpAll₀`/`IffAll₀`) y `SequentSound0` (cita `CutElim₀`) se **descongelaron** (`thaw --confirm`, autorizado) y se volvieron a congelar en el mismo ciclo |
| N2 | `henLimit_consistent`, `shiftTheory_consistent`: ¿titulares? | **titulares** | ✅ `henLimit_consistent₀`, `shiftTheory_consistent₀` (y sus filas de footprint) |
| N3 | `quantFree_subst` duplicado en `SkolemNF0` y `Sequent0` | **se retira** el duplicado | ✅ `SkolemNF0` usa el de `FOL.Sequent0` |
| N4 | `Mfalse`/`Mtrue`/`P` de `Inconsistencia` repiten los de `Soundness0` | a criterio (se deduplica, como P3 y N3) | ✅ `Inconsistencia` usaba los de `Soundness0`; desde su reescritura (2026‑10‑02, ADR‑115 de RPP) no los necesita |

* 🔒 **Los 10 congelables quedan BLOQUEADOS, no congelados** (propietario: «sólo bloqueo»). Con
  N1‑N3 resueltas, `Hauptsatz0`, `HerbrandBlock0`, `BlockExtraction0`, `HenkinLimit0`,
  `Lindenbaum0`, `Fresh0` y `SkolemNF0` salen del cono de las decisiones; congelar cualquiera de los
  17 pide su confirmación explícita (y, para los 7, una pasada de refutación sobre sus renombres).
* Siguen fuera los 15 de la cadena de PeanoRF (`Complexity` incluido, que `Slash` importará al
  retirar `fdepth`), hasta que la entrega compile aquí; e `Inconsistencia` (su §2 cambia con ella).

**La auditoría de constructividad (2026‑09‑27, RPP‑110)** — `auditoria/constructividad-2026-09-27/`
(metaprograma, datos antes/después, experimentos; su `README.md`), y la clasificación vigente en
`AXIOMS.md` §4. Midió, constante a constante, por dónde entra `Classical.choice`, y encontró que 11 de
los 17 candidatos afirmaban cosas falsas sobre él: sobre todo, que el de la completitud «es el WKL del
`if` de Lindenbaum». Las decisiones del propietario (⚠️ no confundir con las D1‑D7 del 2026‑09‑26, de
arriba):

| # | pregunta | decisión | hecho |
|---|---|---|---|
| D1 | ¿se elimina lo eliminable MEDIDO antes de congelar? | «elimina lo eliminable antes de congelar» | ✅ con los mismos enunciados: `Fresh0` (`of_decide_eq_false`, la cota `utf8ByteSize`, `unshift` sobre bytes; ✏️ desde D7, 2026‑10‑05: `s.length` y un `match`), `Enumeration` (`String.exists_eq_ofList`), `Henkin0` (`ctx_split`, `henkin_step_derives`), `Lindenbaum0` (etapa sin decidir, `lindenbaum_limit_closed`), `HenkinLimit0` (`bnd` calculada), `Canonical0` (modelo canónico por `Quot.lift` sobre listas; fuera `quotientOut`), `Compacity0` (`unshift`), `Theorems/Eq` (tres `simp`) y `Rename` 🧊↩️ (descongelado con `thaw --confirm` para retirar `invOf`; `locInv`, inversa local) |
| D2 | la tesis «el choice de la completitud es el WKL del `if` de Lindenbaum», refutada: ¿cómo se reescribe? | «Ok» a la opción (b) | ✅ se corrige toda afirmación de LOCALIZACIÓN (docstrings, `AXIOMS.md` §4.5, ADR‑110 en RPP, notas en el PLAN de RPP); «el WKL» queda sólo como apodo de la FUERZA de la completitud sobre RCA₀ |
| D3 | `henkin_conservative₀` y `derives0_no_disjunction_property`: ¿se reprueban sin elección? | «se reprueban sin elección» | ✅ los dos en `[propext, Quot.sound]`. Los corolarios de ruta de `Soundness0`/`SequentSound0` 🧊 y los controles `derives0_em`/`derives0_peirce` se quedan como están (ADR‑061) |
| D4 | variantes constructivas de lo irreducible | no se preguntó: fuera de alcance, como recomendó la auditoría | ⛔ abajo, en «Fuera de alcance» |
| D5 | el caso Henkin de Skolem (~60 líneas, medido): ¿antes de congelar `Skolem0`? | «se hace antes de congelar `Skolem0`» | ✅ es `henkin_conservative₀`, por la vía sintáctica (el mismo trabajo que D3); el caso general, fuera de alcance |
| D6 | los tres `simp` de `Theorems/Eq` | no se preguntó aparte: entra con D1 | ✅ `FOL.Core` sin `Classical.choice` salvo el código meta de `Tactics`; ninguna fila de RPP cambia |
| D7 | la instancia de `TheoryFramework` (las 2 DIFERIDA de `[G.2]`) | «declara la instancia» | ✅ `fol0System : LogicSystem Formula` sobre `Derives₀` (ningún axioma), `fol0Sound`, `fol0Complete`, `fol0_proves_iff_models`; `[G.2]` baja a 12 marcadores |
| D8 | PeanoRF (X1) no responde desde el 2026‑09‑23 | sin plazo: el propietario le pasa la información | ✅ la información va en una carta que se deja en su repositorio (fila X1, arriba) |

Cifras (`decls.tsv` de la auditoría): constantes con `Classical.choice`, **157 → 84** (3 son código
meta de `FOL.Tactics`); `noncomputable`, **8 → 1** (`SkolemN0.skF`); titulares de FOL con choice,
**55 → 34** de 252; `check-footprints`, 513 → 517 filas (4 de la instancia). Los 34 que quedan son los
27 irreducibles de la auditoría y 7 corolarios de ruta conservados a propósito.

* 🔒 (Hoy los 17 están 🧊: nueve en el segundo lote y ocho en el tercero; ver abajo.) Los **17 candidatos** (los 10 de la segunda criba y los 7 que liberaron N1‑N3) siguen **sólo
  BLOQUEADOS**, no congelados: congelar cualquiera pide confirmación explícita del propietario. D1 y
  D2, que retenían a 11 de ellos, están ejecutadas. ⚠️ Pero los veredictos de las cribas son de ANTES
  de esta tanda: `Henkin0`, `HenkinLimit0`, `Lindenbaum0`, `Fresh0`, `Canonical0`, `Compacity0` y
  `Skolem0` cambiaron de código hoy, y otros candidatos, de docstrings (D2).
* 🧊 `Rename` estaba congelado (RPP‑105): es su primer `thaw`, autorizado por D1 (la auditoría ya
  advertía que retirar `invOf` pedía descongelarlo), y vuelve a congelarse en el mismo ciclo.
* 🧊 ✅ D2 llegó a `SequentSound0` el 2026‑09‑28: `thaw` autorizado, las tres localizaciones del WKL de su
  cabecera y del docstring de `lk0_not_empty` rectificadas y re‑congelado (`AXIOMS.md` §4.5). Esta línea
  decía que esperaban su próximo `thaw`.

**Tercera criba con refutación (2026‑09‑27, tras D1‑D8; RPP‑111)**, sobre los 19 que deja pasar la
parte medible (los 17 más `Inconsistencia` y `TheoryFramework/Instances/FOL.lean`): 31 correcciones de
comentarios y docstrings aplicadas (código idéntico), y **N6** aplicada por la política de P3/N3/N4 («si
está duplicado, se retira»): `Lindenbaum0.not_not_em` repetía nombre y enunciado de `not_not_em` del
núcleo y se retiró. Veredicto:

* 🧊 **CONGELADOS** (confirmado por el propietario, RPP‑112): los 4 congelables ya —`Compacity0`,
  `Inversion0`, `QFDecide0`, `SkolemN0`— y los 6 con sus correcciones —`Craig0` e `Interpolation0`,
  `Canonical0`, `Fresh0`, `HenkinLimit0`, `TheoryFramework/Instances/FOL`—.
* ⬜ **Retenidos por decisiones nuevas del propietario**:

| # | pregunta | retiene |
|---|---|---|
| N5 | Los nombres nuevos o técnicos que dependen de un cálculo y no llevan marca, pero la cabecera de su módulo los nombra como piezas: ¿titulares (→ marca) o auxiliares? (a) `henkin_step_derives`; (b) `lindenbaum_limit_consistent/_max/_closed`; (c) `skolemizeF_impAll` (con fila); (d) `cutElim_of`, `cutPrinAux`, `cutLeftAux` (con fila), `leftPrin_mono`, `leftPrin_lift`, `herbrand_block_iff`. ⚠️ «Titular = lo que tiene fila» no sirve como regla: 220 de las 256 filas no llevan marca, y 138 tampoco prefijo de cálculo (`inv_allR`, `max_cons_neg`, las de `Prenex0` 🧊…) | `Henkin0`, `Skolem0` (a); `Lindenbaum0` (b); `SkolemNF0` (c); `Hauptsatz0`, `HerbrandBlock0`, `BlockExtraction0` (d) |
| N7 | `herbrand_of_skolemNF₀` no ata `ψ` a la matriz: su `↔` lo cumple cualquier `P : Prop` (medido). ¿(A) se dice en la docstring, o (B) se refuerza el enunciado con `skolemize k (prenex φ) = allBlock m ψ`, como los de §3 (medido: misma prueba, `[propext, Quot.sound]`, sin consumidores)? | `SkolemHerbrand0` |

**N5 y N7, resueltas por el propietario el mismo día (RPP‑112):**

| # | decisión | hecho |
|---|---|---|
| N5 | **auxiliares**, los cuatro grupos (a)‑(d) (las letras de la pregunta son grupos de nombres, no opciones), y la regla, escrita | ✅ `NAMING-CONVENTIONS.md` §9, regla 3, «Qué es TITULAR»: titular es el RESULTADO que la cabecera de su módulo presenta como entrega; los pasos de una prueba, los lemas de un límite, las formas intermedias, las pasadas de una inducción y los consumidores condicionales son auxiliares aunque la cabecera los nombre o tengan fila de footprint. Ningún renombre. La regla alcanza también a `Herbrand0.herbrand_iff`, gemelo de `herbrand_block_iff` |
| N7 | **(B)**, reforzar el enunciado | ✅ `herbrand_of_skolemNF₀ : ∃ m ψ, skolemize k (prenex φ) = allBlock m ψ ∧ QuantFree ψ ∧ ([] ⊢₀ ¬(skolemize k (prenex φ)) ↔ ∃ tss E, HerbrandCertBlock m (¬ψ) tss E)`. Misma prueba, mismo footprint (`[propext, Quot.sound]`); sin consumidores |

* 🧊 **CONGELADOS** (tercer lote, RPP‑112): los siete que retenía N5 —`Henkin0`, `Skolem0`, `Lindenbaum0`, `SkolemNF0`, `Hauptsatz0`, `HerbrandBlock0`, `BlockExtraction0`— y `SkolemHerbrand0`, que retenía N7. ⇒ **23 congelados**: los 17 candidatos, `TheoryFramework/Instances/FOL` y los cinco del primer lote.
* Sigue retenida por X1 `Inconsistencia` (su §2 cambia con la entrega de PeanoRF). El 2026‑10‑02 se reescribieron sus §1 y §3, al borrarse `FOL/MetaRules.lean` (ADR‑115 de RPP; arriba, al principio de «Lo que queda»).

⛔ **Fuera de alcance, con su motivo**: LS↑ (ver `Compacity0` §3); un decisor PRÁCTICO del fragmento sin cuantificadores
(cierre de congruencia con certificado: el de `QFDecide0` es de juguete); Beth y Robinson (el puente `LK₀`→`LKp`
ya existe, `Interpolation0.lk0_to_lkp`; piden además renombrar símbolos de relación); la noción de **sentencia** (bloqueo transversal: sin ella no se
enuncian bien la equivalencia elemental ni la categoricidad); y la propiedad de disyunción para
`Derives₀`, que es **FALSA**. Y desde el 2026‑09‑27, de la auditoría de constructividad:
**D4**, las variantes constructivas de lo irreducible, que lo es para enunciados sobre un maximal
ARBITRARIO con semántica en `Prop` — un módulo con `[DecidablePred S]` (medido: las cinco `max_cons_*`
salen con `[propext]`), la semántica ¬¬ (Gödel–Gentzen) o de Kripke, o los modelos «explosivos» de
Krivine (Berardi–Valentini, Forster–Kirst–Wehr), con la completitud debilitada a `⊨ → ¬¬⊢`; iría en
módulos nuevos y no impide congelar; y la **vía sintáctica GENERAL de Skolem** (Herbrand/ε): los
ocho titulares de enunciado sintáctico que sólo llevan `Classical.choice` por la ruta semántica
(`skolem_conservative₀` con `t̄` cualquiera, `skolem_conservative_n₀`, `skolem_conservative_nf₀`, los de
Herbrand de `SkolemHerbrand0`…); el caso Henkin ya está hecho (D5).

## Plan de fases — ⚠️ HISTÓRICO (2026-05-16)

> Este archivo hace un seguimiento de las fases de desarrollo planificadas para el proyecto de Lógica de Primer Orden (FOL).
> **Nota:** Para el detalle exhaustivo de reglas lógicas y teoremas a demostrar, consulta [STARTING_FOL.md](STARTING_FOL.md).

---

## Fase 1: Fundamentos Lógicos (Deducción Natural)

**Objetivo**: Completar las reglas base de deducción en `FOL/FOL.lean`.

**Tareas**:

- [x] Implementar la regla de Reductio ad Absurdum (RAA) en `Derives` para habilitar la lógica clásica.
- [x] Implementar la regla de debilitamiento (Weakening).
- [x] Refinar las reglas de cuantificadores ($\forall$ y $\exists$) con gestión de variables libres (índices de De Bruijn).

**Dependencias**: Ninguna (Nivel 0)
**Complejidad**: Media

---

## Fase 2: Primeros Teoremas (Nivel 1 y 2)

**Objetivo**: Demostrar las tautologías fundamentales descritas en `STARTING_FOL.md`.

**Módulos propuestos**:

- [x] `FOL/Theorems/Impl.lean` — Tautologías de implicación (Identidad, K, S, Silogismo).
- [x] `FOL/Theorems/Neg.lean` — Propiedades de la negación (Doble negación, Contrapositivas, Explosión).

**Dependencias**: Fase 1 completada.
**Complejidad**: Media

---

## Fase 3: Conectivos Derivados y Cuantificadores (Nivel 3 y 4)

**Objetivo**: Establecer y demostrar el comportamiento de $\land$, $\lor$, $\Leftrightarrow$ y la interacción de $\forall$ / $\exists$.

**Módulos propuestos**:

- [x] `FOL/Theorems/Derived.lean` — Leyes de De Morgan, Conmutatividad, Tercio Excluso.
- [x] `FOL/Theorems/Quantifiers.lean` — Dualidad y distribución de cuantificadores.

**Dependencias**: Fase 2 completada.
**Complejidad**: Media / Alta (por la gestión de sustituciones y De Bruijn).

---

## Fase 4: Automatización y Tácticas

**Objetivo**: Facilitar la escritura de pruebas mediante metaprogramación o automatización básica en Lean 4.

**Tareas**:

- [x] Investigar la creación de una táctica que aplique `rewrite_at` automáticamente buscando posiciones válidas.
- [x] Automatizar la regla de identidad y debilitamiento.
- [x] Implementar macros finales para `derive_rewrite` y `derive_weaken`.

**Dependencias**: Fase 3 completada.
**Complejidad**: Alta

---

## Fase 5: Metamatemática y Completitud

**Objetivo**: Estudiar las propiedades formales del sistema deductivo y establecer la semántica completa de la Lógica de Primer Orden.

**Tareas**:

- [x] **Teorema de Deducción:** Demostrar que si $Γ, A \vdash B$, entonces $Γ \vdash A \Rightarrow B$.
- [x] **Semántica y Modelos (Opción B):** Definir noción de modelo y relación de satisfacción ($\models$).
- [x] **Teorema de Corrección (Soundness):** Demostrar que si $Γ \vdash A$, entonces $Γ \models A$.
- [x] Demostrar los 5 lemas semánticos auxiliares en `Semantics.lean`.
- [x] **Teorema de Completitud:** Demostrar que si $Γ \models A$, entonces $Γ \vdash A$.
- [x] **Consistencia:** Demostrar la consistencia del sistema (`consistency_of_satisfiable`).
- [x] **Teorema de Compacidad:** Demostrar que un conjunto de fórmulas es satisfacible si y solo si todo subconjunto finito lo es (`compactness_theorem`).

**Dependencias**: Fase 1-4 completadas.
**Complejidad**: Muy Alta

---

## Fase 6: FOL con Igualdad (FOL=)

**Objetivo**: Extender el lenguaje y el sistema deductivo para soportar el predicado de igualdad lógica (`=`).

**Tareas**:

- [x] Modificar la sintaxis en `FOL.lean` añadiendo el constructor de igualdad a `Formula` (`eq : Term → Term → Formula`).
- [x] Añadir las reglas de inferencia para la igualdad (Reflexividad y Sustitución de Leibniz) en `Derives`.
- [x] Actualizar la semántica en `Semantics.lean` para que la igualdad sintáctica coincida con la igualdad semántica del modelo.
- [x] Adaptar las pruebas de Soundness y Completeness a la nueva sintaxis y reglas.

**Dependencias**: Fase 5 completada.
**Complejidad**: Alta

---

## Fase 7: Fundamentación de la Aritmética y Gödelización

**Objetivo**: Utilizar el sistema FOL= para construir una base para la aritmética, definir tuplas, listas y funciones, y establecer las bases para la autorreferencia.

**Tareas**:

- [ ] **Axiomatización**: Introducir los axiomas de la Aritmética de Peano (restringida, sin inducción general) en una nueva teoría.
- [ ] **Codificación de Tuplas**: Implementar la función de apareamiento de Cantor para codificar pares de números naturales `⟨x,y⟩` como un único número.
- [ ] **Codificación de Listas**: Definir listas finitas como una construcción sobre las tuplas (`Cons(h,t)`).
- [ ] **Codificación de Funciones**: Definir funciones discretas como listas de pares (grafos funcionales).
- [ ] **Gödelización**: Esbozar el mapeo de símbolos y fórmulas a números de Gödel, permitiendo que el sistema hable de sus propias fórmulas y derivaciones.

**Dependencias**: Fase 6 completada.
**Complejidad**: Muy Alta

---

## Fase 6b: FOLPure — FOL sin Igualdad

**Objetivo**: Variante de FOL sin el predicado `=`, con Completitud y Compacidad completas y 0 sorries.

**Estado**: ✅ Completo — librería `FOLPure` separada en el mismo repo.

---

## Fase 6c: PropLogic — Lógica Proposicional

**Objetivo**: Subconjunto sin cuantificadores con el mismo stack metamatemático (Deducción, Corrección, Completitud, Compacidad).

**Estado**: ✅ Completo — librería `PropLogic` separada, 0 sorries.

---

## Fase 6d: TheoryFramework — Marco Genérico de Teorías

**Objetivo**: Capa de abstracción `class LogicSystem (F : Type)` que unifica las tres lógicas y permite demostrar metateorémas una sola vez.

**Tareas completadas**:
- [x] `Logic.lean`: `LogicSystem`, `DerivesSet`, `EntailsSet`
- [x] `Theory.lean`: `structure Theory`, `proves`, `models`, `empty`, `fromList`, `singleton`
- [x] `Properties.lean`: `IsConsistent`, `IsSyntacticallyComplete`, `IsAxiomRedundant`, `IsMaximalConsistent`
- [x] `Relations.lean`: `LE (Theory F)`, `TheoryEquivalent`, `IsConservativeExtension`, `TheoryUnion`, `TheoryIntersection`
- [x] `MetaTheorems.lean`: `proves_iff_models`, `proves_monotone`, `inconsistent_upward`, `equiv_of_conservative`, etc.
- [x] Instancias para `PropLogic`, `FOLPure` y `FOL`

**Estado**: ✅ Completo.

---

## Fase 7: Fundamentación de la Aritmética y Gödelización

**Objetivo**: Utilizar el sistema FOL= para construir una base para la aritmética, definir tuplas, listas y funciones, y establecer las bases para la autorreferencia.

**Tareas**:

- [ ] **Axiomatización**: Introducir los axiomas de la Aritmética de Peano (restringida, sin inducción general) en una nueva teoría.
- [ ] **Codificación de Tuplas**: Implementar la función de apareamiento de Cantor para codificar pares de números naturales `⟨x,y⟩` como un único número.
- [ ] **Codificación de Listas**: Definir listas finitas como una construcción sobre las tuplas (`Cons(h,t)`).
- [ ] **Codificación de Funciones**: Definir funciones discretas como listas de pares (grafos funcionales).
- [ ] **Gödelización**: Esbozar el mapeo de símbolos y fórmulas a números de Gödel, permitiendo que el sistema hable de sus propias fórmulas y derivaciones.

**Dependencias**: Fase 6 completada.
**Complejidad**: Muy Alta

---

## Fase 8: Consolidación y Teorías Concretas

**Objetivo**: Cerrar deudas técnicas y añadir teorías de ejemplo sobre el `TheoryFramework`.

**Tareas**:

- [ ] Cerrar el `sorry` de igualdad en `FOL/Completeness.lean` (modelo cociente completo para `Formula.eq`).
- [ ] Definir una teoría concreta de ejemplo (ej. grupos, orden total) usando `TheoryFramework`.
- [ ] Demostrar la independencia de axiomas en alguna teoría usando `IsAxiomRedundant`.
- [ ] Explorar extensiones conservativas entre `PropLogic` y `FOLPure` via `IsConservativeExtension`.

**Dependencias**: Fases 6a–6d completadas.
**Complejidad**: Alta

---

## Resumen de Estado

| Fase | Descripción | Estado |
|-------|-------------|--------|
| 1 | Fundamentos Lógicos | ✅ Completo |
| 2 | Primeros Teoremas | ✅ Completo |
| 3 | Conectivos y Cuantificadores | ✅ Completo |
| 4 | Automatización | ✅ Completo |
| 5 | Metamatemática | ✅ Completo |
| 6 | FOL con Igualdad (FOL^=) | ✅ Completo |
| 6b | FOLPure (sin igualdad, 0 sorries) | ✅ Completo |
| 6c | PropLogic (proposicional) | ✅ Completo |
| 6d | TheoryFramework (marco genérico) | ✅ Completo |
| 7 | Fundamentación de la Aritmética | ❌ Pendiente |
| 8 | Consolidación y Teorías Concretas | ❌ Pendiente |
