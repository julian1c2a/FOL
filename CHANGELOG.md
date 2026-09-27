# Changelog

**Last updated:** 2026-09-27
**Author**: Julián Calderón Almendros

> ⛔⛔ **ESTE FICHERO ESTUVO CONGELADO EN 2026-05-16 CON 115 COMMITS DETRÁS**, y no fue un
> descuido inocuo: el control `[E]` de `check-doc-sync.bash` usaba **la entrada más reciente de
> este CHANGELOG como referencia** para juzgar si los titulares de los demás documentos se habían
> quedado atrás. Con la referencia congelada, ningún documento podía estar «por detrás» de ella
> ⇒ **el control aprobaba siempre** (ADR-072).
> 🔑 *Un diario que nadie escribe no es sólo un diario vacío: es una referencia falsa para
> todo lo que se apoye en él.*
> ⚠️ Las entradas de abajo, del 2026-09-11 en adelante, se han reconstruido desde `git log` y
> desde las ADR de `../ROBINSON_PlusPlus/DECISIONS.md`. Son un **ÍNDICE de lo que aterrizó**, no
> un inventario exhaustivo de los 115 commits; la fuente de verdad de cada pieza es su ADR.

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 2026-09-27 (7) — La tercera criba de congelación, tras D1‑D8

* 🔎 Sobre los 19 que deja pasar `criba-congelacion.py` (los 17, `Inconsistencia` y la instancia de
  `TheoryFramework`): cuatro lentes de verdad, nomenclatura, consumidores, un juez y dos escépticos.
* ✏️ **31 correcciones** de comentarios y docstrings (código idéntico; `[G.2]` intacto): resúmenes de
  footprint que decían «en todo» donde había constantes con menos axiomas; `Fresh0.exists_fresh`, que
  la iteración de `HenkinLimit0` nunca usó; el presente de `Hauptsatz0` §4 sobre una mitad que el propio
  módulo demuestra; `TheoryFramework/Logic` y `MetaTheorems`, que D7 había dejado desfasados.
* ✂️ **N6**: `Lindenbaum0.not_not_em` repetía nombre y enunciado del `not_not_em` del núcleo: retirado.
* ❄️ **10 congelables** (4 ya, 6 con sus correcciones), ⬜ pendientes de confirmación; retenidos por
  **N5** (¿titulares o auxiliares los nombres técnicos que la cabecera nombra?) y **N7**
  (`herbrand_of_skolemNF₀`), e `Inconsistencia` por X1. Ver `NEXT-STEPS.md`.

## 2026-09-27 (6) — La auditoría de constructividad, y D1‑D8 ejecutadas: `Classical.choice` 157 → 84

* 🔎 **Auditoría de constructividad** (`auditoria/constructividad-2026-09-27/`, guardada en el repo por
  decisión del propietario): el metaprograma `Audit.lean` mide, para CADA constante de FOL y
  TheoryFramework, sus axiomas, si es `noncomputable` y por dónde le entra `Classical.choice`; seis
  tareas de experimento, un juez y un escéptico que recompiló los 42 experimentos y refutó 13 de 25
  puntos con medida. La clasificación, en `AXIOMS.md` §4 (nueva).
* ⛔ **El hallazgo**: la tesis «el `Classical.choice` de la completitud es el WKL del `if IsConsistent₀`
  de Lindenbaum» (ADR‑040 §2, ADR‑041 §4, docstrings) es FALSA en Lean: `Prop` es impredicativo y la
  etapa se define con la condición dentro, sin decidirla. Lo clásico está en el lema de la verdad sobre
  un maximal ARBITRARIO (`max_cons_*`), en la semántica de Tarski en `Prop` y en el `byContradiction`
  final de `completeness₀`. **D2**: se corrigen las afirmaciones de LOCALIZACIÓN; «el WKL» queda sólo
  como apodo de la FUERZA de la completitud sobre RCA₀. Las entradas de abajo que dicen otra cosa
  (2026‑09‑16, 2026‑09‑26) son historia: no se tocan.
* ✂️ **D1 — lo eliminable, eliminado**, con los mismos enunciados de los titulares:
  - `Fresh0`: `cst_zero_ne`/`cst_ne_shift` por `of_decide_eq_false` (la síntesis de `ReflBEq String`
    pasaba por `String.instOrd`); `cst_bound_sym` por la cota `utf8ByteSize` (`cst_utf8ByteSize`);
    nuevas `valid_tail`, `unshift` (inversa global y computable de `shift`, sobre bytes), `shift_bytes`,
    `unshift_shift`; `derivesSet0_shift_inv` usa `unshift`.
  - `Enumeration`: `natToString_surj` por `String.exists_eq_ofList` (sin decodificar UTF‑8).
  - `Henkin0`: nuevos `ctx_split` (partir un contexto finito sin decidir la igualdad: ningún axioma) y
    `henkin_step_derives` (el paso de Henkin en positivo); `henkin_step_consistent₀`, su corolario;
    fuera el `open Classical`.
  - `Lindenbaum0`: `LindenbaumStep` IMPREDICATIVA (deja de ser `noncomputable`); nuevos `not_not_em`,
    `lindenbaum_limit_consistent`, `lindenbaum_limit_max`, `lindenbaum_limit_closed`;
    `derivesSet0_intro_impl` por `ctx_split`; **`lindenbaum_lemma₀` y `henkin_completion₀`,
    `[propext, Quot.sound]`**. `max_cons_contains` conserva su `byContradiction` (esencial).
  - `HenkinLimit0`: `bnd` CALCULADA por recursión (`bndTerm`, `bndTerms`, sus `_spec`,
    `cst_ne_of_size`); `bnd`, `hidx` y `hen`, computables.
  - `Canonical0`: fuera `quotientOut`, `quotientOut_eq` y `pointwiseEqv_out_mk`; el modelo canónico se
    levanta con `Quot.lift` sobre listas (`pointwiseEqv_refl`, `consQ`, `consQ_resp`, `listQuot`,
    `listQuot_mk`); `canonicalModel`, computable; `QuotientDomain`, `abbrev`.
  - 🧊↩️ `Rename`, congelado, **descongelado** (`thaw --confirm`, su primer `thaw`) para retirar `invOf` e
    `invOf_spec`: nuevos `symsTerm`/`symsTerms`/`symsFormula`/`symsList`, `locInv` (inversa LOCAL sobre la
    lista finita de símbolos), `locInv_spec` y los `rename_rename_*_loc`; `derives0_rename_conservative`
    sin choice. Vuelve a congelarse en el mismo ciclo.
  - `Compacity0`: `hasLargeModels_shift` con `Fresh0.unshift`.
  - `Theorems/Eq` (D6): tres `simp` sin `Nat.left_eq_add`/`Nat.add_eq_left` (lemas del núcleo con
    choice) ⇒ `FOL.Core` sin choice salvo el código meta de `Tactics`.
* 🔁 **D3 y D5**: `Skolem0.henkin_conservative₀` por la vía SINTÁCTICA (`henkin_step_derives`,
  `ctx_split`, `dne_rule`) —es el caso Henkin de Skolem de D5—, e
  `Inconsistencia.derives0_no_disjunction_property` por la valuación booleana de `Finitary0` (nuevos
  `derives0_not_negP_fin`, `derives0_not_complete_fin`; importa `FOL.Finitary0`): los dos
  `[propext, Quot.sound]`. Los corolarios de ruta de `Soundness0`/`SequentSound0` 🧊 y los controles
  `derives0_em`/`derives0_peirce` se quedan (ADR‑061).
* 🏁 **D7 — la instancia de `TheoryFramework`, declarada**: `fol0System : LogicSystem Formula` sobre
  `Derives₀` (ningún axioma), `fol0Sound`, `fol0Complete` y `fol0_proves_iff_models`
  (`[propext, Classical.choice, Quot.sound]`). `Derives` sigue sin instancia. Salen las 2 DIFERIDA de
  `[G.2]` (14 → 12 marcadores); 4 filas nuevas en `check-footprints` de RPP.
* 📨 **D8**: PeanoRF, sin plazo; la información va en una carta en su repositorio. D4 (variantes
  constructivas) y la vía sintáctica general de Skolem, a «fuera de alcance» de `NEXT-STEPS.md`.
* 📏 **Cifras** (`decls.tsv`): constantes 2978 → 3074; con `Classical.choice` **157 → 84** (3 son código
  meta); `noncomputable` **8 → 1** (`SkolemN0.skF`); la frontera por donde entra choice, 30 → **13**
  declaraciones lógicas (más 3 meta); titulares de FOL con choice **55 → 34** de 252 (21 filas de
  `check-footprints` lo pierden); `check-footprints`, 513 → 517. Axiomas del proyecto: los mismos 4.
* ⭐ La migración `String` → `List Char` (D7 del 2026‑09‑26) no hacía falta: lo que trae
  `Classical.choice` en v4.31 es DECODIFICAR UTF‑8 (y el orden de `String`); la capa de bytes está limpia.
* 🔒 Los 17 candidatos a congelar siguen sólo bloqueados; congelarlos pide confirmación.

## 2026-09-27 (5) — N1‑N4 resueltas: 13 renombres y dos duplicados retirados

* 🏷️ **N1** (propietario: renombrar): las once definiciones POR DERIVABILIDAD que no llevaban marca
  la llevan ya — `CutAdm₀`, `CutAt₀`, `CutBelow₀`, `LeftPrin₀`, `CutElim₀`, `NDtoLK₀`,
  `HerbrandExtraction₀`, `HerbrandExtractionBlock₀`, `ImpAll₀`, `IffAll₀`, `PwEq₂`. La regla 1 de
  `NAMING-CONVENTIONS.md` §9 vuelve a ser verdad en el árbol, sin excepción.
* 🧊↩️ Para ello se **descongelaron** `PrenexNF0` (define `ImpAll₀`/`IffAll₀`) y `SequentSound0`
  (cita `CutElim₀` en su prosa), con `thaw --confirm` autorizado por el propietario, y se volvieron
  a congelar en el mismo ciclo. Sólo cambian esos nombres.
* 🏷️ **N2** (propietario: son titulares): `henLimit_consistent₀`, `shiftTheory_consistent₀`, con sus
  filas de footprint en RPP.
* ✂️ **N3**: `SkolemNF0` deja su copia de `quantFree_subst` y usa la de `FOL.Sequent0` (importa
  `FOL.Sequent0`: una arista más en `DEPENDENCIES.md`). **N4**: `Inconsistencia` deja sus copias de
  `Mfalse`/`Mtrue`/`P` y usa las de `FOL.Soundness0`.
* 🔒 Los 10 congelables de la segunda criba quedan **bloqueados, no congelados** (propietario).

## 2026-09-27 (4) — La segunda criba de congelación, con refutación

* 🔎 Sobre los **18** que deja pasar `criba-congelacion.py` (liberados por P2, P3 y P4): cuatro lentes
  de VERDAD por grupos, dos de ESTABILIDAD (nomenclatura; consumidores y decisiones), un juez y dos
  escépticos (uno contra el veredicto, otro contra las ediciones). Resultados en RPP‑108.
* ✏️ **71 correcciones** de comentarios y docstrings en los 18, más `Finitary0` (código IDÉNTICO,
  comprobado token a token; `[G.2]` intacto). Las de más peso:
  - `Craig0` e `Interpolation0` decían que, para sentencias, la condición de variables «es vacua»:
    FALSO. El enunciado no da `C` cerrada; sobre `∀xP(x) ⟹ ∃xP(x)` Maehara devuelve `C = P(x₀)`.
  - Las firmas de cabecera de `herbrand_block₀` (`BlockExtraction0`) y `herbrand_validity₀`
    (`SkolemHerbrand0`) omitían una hipótesis (`QuantFree φ`; constantes de Skolem frescas) sin la
    que el bicondicional es falso.
  - `QFDecide0`: `qfT` da UN paso de mezclas, no un cierre; `List.find?` no pide `LawfulBEq`; el
    footprint de `ext_eqInstance`/`qfCheck_iff` es `[propext]`.
  - Procedencias de `Classical.choice` incompletas o invertidas (`Fresh0`, `Henkin0`, `Compacity0`,
    `Canonical0`, `Skolem0`, `SkolemN0`, `Lindenbaum0`, `HenkinLimit0`); cuatro citas a memorias
    privadas (`trampa §12/§13`); prosa temporal sin fecha.
* ❄️ **Veredicto**: 10 congelables, ⬜ pendientes de confirmación del propietario (`Interpolation0`,
  `Craig0`, `QFDecide0`, `Inversion0`, `Skolem0`, `SkolemN0`, `SkolemHerbrand0`, `Canonical0`,
  `Compacity0`, `Henkin0`); 7 retenidos por tres decisiones nuevas (N1, N2, N3: ver
  `NEXT-STEPS.md`) y `Inconsistencia` por la entrega de PeanoRF.

## 2026-09-27 (3) — P4: el fragmento sin cuantificadores, ACOTADO y DECIDIDO

* 🏁🏁 **`FOL/QFDecide0.lean`** (módulo nuevo ⇒ **55 módulos**): `derives0_qf_iff_bounded` —
  `Γ ⊢₀ φ` sii `EqPropCert Γ φ (qfInst Γ φ)` para `Γ`, `φ` sin cuantificadores, con UNA lista finita
  FIJA de instancias— y `decideDerives0QF : Decidable (Γ ⊢₀ φ)`. El primer resultado de
  DECIDIBILIDAD del proyecto. **`[propext, Quot.sound]`**, calculable en el kernel. Compiló a la
  primera en el árbol (portado del borrador «semántico» de RPP‑106).
* ⛔ **La cota ingenua (subtérminos) es FALSA** y el módulo lo compila como control: `EqInstance.func`
  cambia un argumento, y `[a≐b, c≐d] ⟹ g(a,c) ≐ g(b,d)` pasa por `g(b,c)` o por `g(a,d)`. La
  correcta añade a los subtérminos sus **mezclas de prefijo** (un paso, no un cierre) y SUSTITUYE `E`.
* ⭐ **La poda** (`eqPropCert_prune`) extiende la valuación con un núcleo de congruencia composicional:
  no usa el Hauptsatz ni `QuantFree`.
* ⚠️ **El decisor es de juguete**: tabla de verdad de `2^(átomos distintos)`.
* Sale la OFERTA de `Hauptsatz0` de `[G.2]` (14 marcadores); sus docstrings y la de
  `Herbrand0.instDecidablePTaut` remiten a `QFDecide0`.

## 2026-09-27 (2) — 🧊 Los cinco primeros módulos CONGELADOS; P2 y P3 resueltas

* 🧊 **FREEZE** (permanente; extensión sólo vía `*Ext.lean`) de `PrenexNF0`, `Prenex0`, `SequentSound0`,
  `Soundness0` y `Rename`: los cinco que sobrevivieron a la criba con refutación, confirmados por el
  propietario. Medido antes: ninguno usa los nombres renombrados ni los `sub_*` movidos.
* 🏷️ **P2 · 18 titulares renombrados** por la regla de subíndices (`NAMING-CONVENTIONS.md` §9, regla 3:
  los titulares llevan siempre la marca): `hauptsatz₀`, `cut_elimination₀`, `herbrand₀`,
  `herbrand_extraction₀`, `herbrand_block₀`, `herbrand_extraction_block₀`, `herbrand_of_skolemNF₀`,
  `lindenbaum_lemma₀`, `henkin_completion₀`, `henkin_step_consistent₀`, `truth_lemma₀`,
  `skolem_conservative₀`, `henkin_conservative₀`, `skolem_conservative_n₀`, `skolem_conservative_nf₀`;
  y los de `LKp`, con marca propia **`ₚ`** (nueva fila de la tabla): `maeharaₚ`, `craigₚ`, `craig_implₚ`.
  140 sustituciones en 23 ficheros, 18 filas de `check-footprints` en RPP; compiló a la primera.
* ♻️ **P3 · los cinco `sub_*`** (`sub_refl`, `sub_wk`, `sub_cons`, `sub_drop`, `swap_cons`), duplicados
  literalmente en `Hauptsatz0` y `Craig0`, viven ahora en `FOL.Sequent0`.

## 2026-09-27 — Documentación al día, y la criba de congelación con refutación

* 📝 **W2 · `REFERENCE.md`** contrastado con el árbol (60 ediciones): §2 regenerado de las líneas
  `import` (54 módulos), §3.13 (34 filas, no «veintiún»; la vía H ya tiene su Hauptsatz), §7.1 sin
  módulos retirados, §3.1/§3.10‑§3.12 marcados BORRADOS con quién los sustituye, y unas veinte
  afirmaciones falsas más (símbolos que no existen, firmas sin `h_dne`, `LocalRule`, `folSystem`…).
* 🔧 **W3 · `DEPENDENCIES.md` REGENERADO** por `gen-dependencies.py` (nuevo): 54 módulos, 97 aristas,
  profundidad 12, ningún módulo fuera del build, ningún import externo salvo `Lean`. Se CALCULA
  (`--check`); sale de la deuda de `[E]`.
* 📝 **W4 · el plan de RPP**: filas obsoletas anotadas (16 ediciones).
* ❄️ **Criba de congelación con refutación** (dos lentes —estabilidad y verdad de lo escrito— y un
  juez): de los 23 que pasan los criterios medibles, **1 congelable ya** (`PrenexNF0`), **4 tras
  arreglos** (`Prenex0`, `SequentSound0`, `Soundness0`, `Rename`; arreglos aplicados), **18 todavía
  no** (la entrega de PeanoRF, y tres decisiones del propietario: nombres de los titulares sin
  subíndice, los `sub_*` duplicados en `Hauptsatz0`/`Craig0`, y la OFERTA de `Hauptsatz0`).
  59 correcciones de docstrings en 18 módulos (falsedades medidas: `Craig0` llamaba «CONFIRMADA» la
  obstrucción que `craig₀` refutó; `SkolemNF0` decía que `herbrand` pide un `∀`; `SequentSound0`
  contaba 14 constructores de `LKc`; `Fresh0`/`Compacity0` atribuían `Classical.choice` a comparar
  `String`…). `criba-congelacion.py` ve ahora la OFERTA y el consumidor futuro de `Complexity`.
* 🏷️ **`Prf` (el Hilbert clásico de RPP) se queda sin subíndice**: decisión del propietario.

## 2026-09-26 (madrugada, 2) — D3a: la interpolación de Craig para `Derives₀`, CON igualdad

* 🏁🏁 **`FOL/Interpolation0.lean`** (módulo nuevo ⇒ **54 módulos activos**): `craig₀ : [A] ⊢₀ B → ∃ C,
  [A] ⊢₀ C ∧ [C] ⊢₀ B ∧ PredSub C [A] ∧ PredSub C [B]`, y `craig_ctx₀` con contexto. La igualdad es
  símbolo lógico; la condición va sobre los símbolos de relación. **`[propext, Quot.sound]`**: ni un
  `Classical.choice`. Compiló a la primera (síntesis de dos diseños independientes y un juez).
* ⭐ **El puente** `lk0_to_lkp`: una derivación de `LK₀` da una de `LKp` con las instancias de igualdad
  en el antecedente, cerradas con `∀` (`EqGen`) para atravesar `allR`/`exL`.
* ⭐⭐ **Sin borrar predicados**: cada instancia menciona a lo sumo un símbolo de relación; las de
  predicados ajenos a `A` van al lado de Maehara donde la intersección de lenguajes no las deja pasar.
* ⭐ **Dividendo**: `lk0_to_derives0_fin`, `LK₀ → ⊢₀` SINTÁCTICO (la única traducción del árbol era
  `SequentSound0.lk0_to_derives0`, que es la completitud).
* ⚠️ Control con lenguajes incomparables y la igualdad trabajando (`craig₀_example`); los controles
  con `A := ⊤` o un `B` sin predicados se descartaron por VACUOS (se cumplen con `C := ⊤` / `C := B`).
* Sale la última ABIERTA de `[G.2]` (`Craig0`): el censo queda en 15 (0 ABIERTA). ⇒ **D3, cerrada.**

## 2026-09-26 (madrugada) — D3b: el teorema de Herbrand para `φ` y `Γ` cualesquiera

* 🏁🏁 **`SkolemHerbrand0` §3**: `herbrand_validity_ctx₀` — `Γ ⊢₀ φ` si y sólo si hay un certificado
  de Herbrand de bloque para la matriz de `skolemize k (prenex ¬(Γ ⇒ φ))`, que es la **forma de
  Herbrand** de `Γ ⇒ φ`. Con `herbrand_refutation₀` (`⊢₀ ¬φ` sii certificado para la de Skolem de `φ`)
  y `herbrand_validity₀` (contexto vacío). La cabecera declaraba la deuda como «mover la negación a
  través de la skolemización, ⬜ no medido»: no hace falta moverla, se skolemiza lo que se **refuta**
  (`derives0_neg_iff_neg_skolemNF`). Sale la ABIERTA de `SkolemHerbrand0` de `[G.2]`.
* ⚠️ La ecuación `skolemize … = allBlock m ψ` va dentro de los enunciados: sin ella `ψ` quedaría
  suelta. Footprint `[propext, Classical.choice, Quot.sound]`: retirar los axiomas de Skolem pasa por
  la completitud (el WKL); `herbrand_of_skolemNF` sigue sin `Classical.choice`.

## 2026-09-26 (noche) — D2, D4, D5, D6 y D7 ejecutadas; la regla de subíndices, también en RPP

* 🔧 **D5 · el refactor de `Lift0`, HECHO.** El núcleo es `absTerm' P` (`FOL/Eigenvariable.lean`),
  genérico en un predicado de símbolos: `absTerm c` es su caso `(· = c)` por definición, y `liftTerm k`
  su caso sin símbolos por un lema (`Lift0.absFormula'_none`), sin tocar `FOL/FOL.lean`. Los 40 nombres
  de antes se conservan con su enunciado; footprints idénticos; compiló a la primera. ⚠️ La vieja nota
  prometía «~150 líneas»: el par pasa de 806 a 797 (−56 de código). Lo que compra es **una** inducción
  de lift/subst/`getAt?`/`replaceAt` y **un** transporte de 21 casos menos (de ocho). Sale la DIFERIDA
  de `Lift0` de `[G.2]`.
* 📐 **D6 · la regla de subíndices** (`NAMING-CONVENTIONS.md` §9): el subíndice nombra un CÁLCULO —`₀`
  el clásico, `ᵢ` el intuicionista— y sin subíndice va lo que no depende de ninguno. Renombres:
  `model_existence_iff` → **`model_existence_iff₀`** (T1), `compactness₀` → **`compactness`**,
  `IsHenkin₀` → **`IsHenkin`**, `DisjunctionProperty` → **`DisjunctionProperty₀`**; y en RPP, `Prf₀`
  (que era el INTUICIONISTA) → **`Prfᵢ`** (RPP‑102).
* 🏷️ **D2** · `IsSyntacticallyComplete₀` → **`IsMemComplete`**: completa POR PERTENENCIA, sin
  subíndice (no depende de cálculo), y dejando libre el nombre canónico para la teoría completa sobre
  sentencias.
* ⛔ **D4 · la vía de `ModelG`, CERRADA definitiva**: medida terminada (lo decidido, en el árbol;
  `FreshSym`/`EnumSym` sin consumidores). Sale su marcador de `[G.2]` (19 → 17 con el de `Lift0`).
* ⛔ **D7 · la migración `String`→`List Char`, CERRADA como ABANDONADA en FOL**: la parte de FOL está
  hecha como parámetro; instanciar no movería ningún footprint titular.
* 📝 **Higiene de docstrings** (58 correcciones en 16 módulos): citas a ficheros borrados de
  `cuarentena/`, prosa en futuro caducada, cifras de constructores/axiomas de `Inconsistencia`, la
  etiqueta «LS↑ hasta ℵ₀», `Complexity` («cero axiomas» con `[propext]` medido).
* 📨 **Carta a PeanoRF** (`RESPUESTA-PEANORF-2026-09-26.md`): la condición «FOL no depende de nada más
  allá de sí mismo», lo que hoy la incumple (los siete), el aviso de D5 y la nomenclatura de D6.

## 2026-09-26 (tarde) — Las decisiones D1-D7 del propietario, y `Tactics2.lean` borrado

* 🗑️ **D1 · `FOL/Tactics2.lean` BORRADO**: era idéntico, salvo la línea del `import`, a
  `cuarentena/librerias-retiradas/FOL_poli/Tactics2.lean`, no lo importaba nadie y ningún build lo
  compilaba. El 2026-09-23 se había comparado sólo con `Tactics.lean` y se concluyó «no es duplicado»:
  el término de comparación era el equivocado. Cifra canónica: **53 módulos activos** (`FOL/` 42).
* 📝 **Decididas y en curso** (`NEXT-STEPS.md`): D2 renombrar `IsSyntacticallyComplete₀` antes de
  congelar `Canonical0`; D4 cerrar la vía de `ModelG` si está terminada; D5 hacer el refactor de
  `Lift0`; D6 averiguar qué marca `₀`, con el cálculo intuicionista a la vista. D3, aplazada al final.
* ⛔ **D7**: la migración `String`→`List Char` **no está terminada** (el `abbrev` sigue en `String`) ⇒
  no se cierra.
* ⛔ **Condición para la entrega de PeanoRF**: FOL no puede depender de nada más allá de sí mismo.

## 2026-09-26 — Los seis, completos: el fragmento sin cuantificadores (T4), el modelo infinito (T6) y las dos inversiones que faltaban

Cierran el catálogo de seis teoremas decidido el 2026-09-23 (T1-T3 y T5, en la entrada de abajo).
Ningún módulo nuevo. Detalle en `../ROBINSON_PlusPlus/DECISIONS.md`, **RPP-100**.

* 🏁 **T4 · `FOL/Hauptsatz0.lean` §9 — el fragmento sin cuantificadores, CARACTERIZADO.**
  `derives0_qf_iff : (Γ ⊢₀ φ) ↔ ∃ E, EqPropCert Γ φ E` para `Γ` y `φ` sin cuantificadores: derivable
  **sii** la conclusión es consecuencia PROPOSICIONAL del contexto más una lista finita `E` de
  instancias de la igualdad. La ⟹ es `lk0_herbrand` con `φ := ⊥` sobre la derivación sin corte; la ⟸
  no necesita la hipótesis `QuantFree`. `[propext, Quot.sound]`; `peval_true_eqInstance`, ningún axioma.
* ⛔ **Lo que T4 NO es.** «Decidible por tabla de verdad» es FALSO (`[] ⊢₀ c ≐ c` por `refl`, y `peval`
  trata `≐` como un átomo). Y **caracteriza, no decide**: `E` no tiene cota. La versión ACOTADA no está
  probada y su coste no se ha medido (OFERTA en `[G.2]`).
* ⚠️ **La duda de vacuidad del catálogo, resuelta**: la `E` sin cota no vuelve vacuo el enunciado (el
  precedente vacuo era el Maehara relativizado de RPP-067). La valuación constante `true` satisface toda
  `EqInstance`, luego `EqPropCert [] ⊥ E` es falso para toda `E`; dos `example` lo compilan. ⚠️ Esos
  controles no separan la ⟹ de `Finitary0.tval`, y el propio comentario lo dice.
* 🏁 **T6 · `FOL/Compacity0.lean` §3 — el modelo infinito numerable.** `infinite_model_of_large`: si para
  todo `n` hay un modelo de `S` con `n` elementos distintos (`HasLargeModels S`), hay uno **numerable e
  infinito**. Sin hipótesis de frescura: la teoría se muda a `shiftTheory` y vuelve por `pullback`.
  Piezas: `InfiniteDom` (`Nat` se inyecta en `D`), `infTheory` (`S` más `cᵢ ≠ cⱼ`, vía `neqAx`) con
  `infTheory_finSat`, y `updateCsts`, el `updateFunc` de `Skolem0` iterado. Corolario:
  `countable_infinite_of_infinite`. Cuatro controles de no vacuidad. `Compacity0` importa `FOL.Skolem0`.
* ⛔ **Lo que T6 NO es**: LS↑ (nada sube de un modelo infinito a uno de cardinal mayor: con `String` sólo
  hay ℵ₀ constantes y la 2ª entrega de `ModelG` está cerrada). La biyección con `Nat` no se construye.
* 📏 **Footprints de T6**: los titulares, `infTheory_finSat` y `evalTerm_updateCsts`,
  `[propext, Classical.choice, Quot.sound]` — ⚠️ con procedencias distintas: el WKL de la completitud,
  el `Classical.choice` de `Fresh0` (`cst_bound_list`, `cst_inj`) y el de `Rename.invOf`.
  `evalFormula_updateCsts`, sólo `[propext]`; `hasLargeModels_empty` y `not_hasLargeModels_one`, ninguno.
* 🏁 **T5, completo: `inv_allR` e `inv_exL`** (`FOL/Inversion0.lean`). Su DIFERIDA decía que la identidad
  `substFormula 0 (var 0) (liftFormula 1 A) = A` «no se ha medido», y **existía**
  (`Lift0.substFormula_lift_var`); el diseño de las dos estaba en el journal del 2026-09-23. Compilaron a
  la primera, `[propext, Quot.sound]`. Sale una fila DIFERIDA de `[G.2]`.
* 📝 **Correcciones de la revisión adversarial**: la cabecera de footprint de `Hauptsatz0` (atribuía
  `[propext, Quot.sound]` a `lk0_to_lkh`, que mide `[propext]`); el docstring de
  `Herbrand0.instDecidablePTaut` (se leía como «la versión relativa DECIDE»); citas a ficheros borrados
  y el «(hasta ℵ₀)» de `Compacity0`.
* 🔧 **Controles**: `git-lock.bash` borraba por SUBCADENA (`grep -Fv` sin `-x`) en `unlock` y `thaw`: al
  desbloquear `FOL.lean` se llevó también `FOL/FOL.lean` de `locked_files.txt` (d961bb2). Arreglado aquí
  y en RPP, y `FOL/FOL.lean` vuelve a la lista. `[G.2]` reconoce ahora «no está medido/a».
  `criba-congelacion.py` entra en el repo (vivía en un scratchpad).
* 📏 **14 filas nuevas** en `../ROBINSON_PlusPlus/check-footprints.bash` (4 de T4, 8 de T6, 2 de las
  inversiones). FOL **57 jobs** en verde.
* 📝 **Documentación**: los avisos de cabecera del 2026-09-12 (negaban Corrección, Completitud y
  Compacidad) reescritos en `CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md`, `README.md`, `REFERENCE.md` y
  `PLANNING.md`; `REFERENCE.md` proyecta T1-T6 (T1-T3 no se habían proyectado); `DEPENDENCIES.md`,
  marcado DESFASADO; `NEXT-STEPS.md`, con lo que queda. `README.md` y `NEXT-STEPS.md` salen de la deuda
  de `[E]`.

## 2026-09-23 — El CIERRE de FOL: lo que los cálculos NO son, y un censo que mira lo que se dice

⚠️ Registrada el mismo día: el sondeo de candidatos señaló que este CHANGELOG **no recogía el
cierre** —la misma forma que dejó congelado el control `[E]` (ADR‑072)—. Detalle en
`../ROBINSON_PlusPlus/DECISIONS.md`, **RPP‑098** y **RPP‑099**.

* ⛔⛔ **La propiedad de disyunción para `Derives₀` es FALSA** (`Derives₀` es ND **clásica**).
  Contraejemplo: `derives0_em_ctx` + `derives0_not_complete`, dos piezas que ya estaban en el árbol.
  Aterriza como `FOL.Inconsistencia.derives0_no_disjunction_property`. La que sí se quería —la de
  `Derivesᵢ`, el fragmento intuicionista— está probada en PeanoRF.
* ⭐ **`FOL/Inconsistencia.lean` SUBE AL BUILD** desde `cuarentena/`: era la evidencia de que la
  solidez de `Derives` es falsa, y vivía donde nada se compila.
* 🗑️ **`cuarentena/` se vacía de código**: borrados `Soundness`, `Compacity`, `Theorems_Soundness`
  (teoremas falsos) y `Completeness` (superado por `completeness₀`) ⇒ **4 `axiom` y ninguno más en
  ninguna parte**.
* 🗑️ **Borrados dos duplicados literales**: `FOL/Theorems/Deduction.lean` (el `deduction_theorem` de
  `FOL/Deduction.lean`) y `FOL/Classical.lean` (dos `def` de las librerías retiradas). ⬜ `Tactics2.lean`
  no lo es, y queda sin decidir.
* 🔧 **`[G.2]`** en `check-doc-sync.bash`: el censo de marcadores de deuda con trinquete en los dos
  sentidos. Tapa el hueco medido de `[G.1]`, que sólo miraba docstrings pegados a un `def X : Prop`.
* 📝 **Nueve cabeceras** anunciaban abierto lo que estaba probado al lado; corregidas nombrando quién
  las paga.
* ⭐ **`FOL/Complexity.lean`** (encargo §3 de PeanoRF): `formulaComplexity` y `complexity_substFormula`,
  puramente sintácticos, bajan de `Canonical0`.
* ⛔ **`folSystem` retirada** y la vía de `TheoryFramework` **cerrada con su mapa de vuelta escrito**.
* ⛔ **La vía de la 2ª entrega de `ModelG` queda CERRADA**: su única justificación escrita (LS
  ascendente) estaba bloqueada por otra cosa —la indexación por `Nat` de la cadena de completitud—, y
  `EnumSym` es falsa para los tipos no numerables que LS↑ necesita. El parámetro se queda.
* ⭐ **Propuesta (C) aceptada con PeanoRF**: `Subst`, `DerivesI`, `SubstDerives`, `Consistency`, `Eq`,
  `Collapse` y `Slash` bajan a FOL (siete, no tres: su corrección). `Slash` entrará con `lock`, no con
  `freeze`.
* ❄️ **Política de congelación** (propietario): FOL no se congela hasta estar terminado; se trabaja
  con `lock` por fichero, y se congela **fichero a fichero lo que se MIDA como intocable**.
* 🏁 **Y por la tarde, cuatro de los seis teoremas del catálogo del cierre** (`f9efd94`, `d961bb2`;
  esta entrada se escribió antes y no los recogía):
  * **T1** — `Compacity0.model_existence_iff : IsConsistent₀ S ↔ IsSatisfiable S`, la forma de Henkin
    de la completitud. Las dos mitades ya estaban, una en cada módulo.
  * **T2** — `Canonical0.max_cons_neg`, `IsSyntacticallyComplete₀` y `max_cons_complete`: todo maximal
    consistente decide cada fórmula por PERTENENCIA. ⚠️ No es todavía la «teoría completa» de la
    teoría de modelos (sobre sentencias, por derivabilidad): decisión pendiente.
  * **T3** — `Herbrand0.pcheck_complete`, `ptautCheck_iff` e `instDecidablePTaut : Decidable (PTaut φ)`:
    el certificado proposicional ya se REFUTA, no sólo se confirma. `pcheck_complete` y
    `ptautCheck_iff`, **`[propext]`**; la instancia no lleva `#print axioms`, pero los `decide` compilan. ⛔ Con
    control por `decide`: `c ≐ c` NO es `PTaut` aunque sea derivable.
  * **T5** — `FOL/Inversion0.lean`: las nueve reglas proposicionales de `LK₀` son invertibles, un corte
    cada una; `[propext, Quot.sound]`. `allR`/`exL` fuera (entraron el 2026-09-26).
  * Footprints de T1 y T2: `[propext, Classical.choice, Quot.sound]`.

## 2026-09-22 — `ModelG`: el símbolo, parámetro también en la SEMÁNTICA

* **`ModelG (S D : Type)`** sustituye a `Model (D : Type)`, y `Model` queda como
  `abbrev Model (D : Type) := ModelG String D`. `evalTerm`, `evalTerms`, `evalFormula` y
  `contextSatisfies` pasan a `{S D}` sobre `TermG S` / `FormulaG S`.
* ⭐⭐ **Alcance 9 ficheros, trabajo 1.** `Model` se citaba en nueve ficheros (68 veces); con el
  `abbrev`, **ninguno de los ocho restantes cambió**. FOL **54 jobs** y RPP **145 jobs** verdes a
  la primera. Es la lección de ADR‑068 otra vez: *medir el ALCANCE de un tipo no es medir el
  TRABAJO*.
* ~~⬜ **Segunda entrega pendiente**: `Canonical0` (el modelo canónico) sigue en `String`.~~
  ⛔ **CERRADA el 2026‑09‑23** — ver la entrada de arriba.

## [Unreleased]

### Added (2026-09-18) — el tipo de los SÍMBOLOS pasa a ser un PARÁMETRO

- **ADR-068** — `TermG (S : Type)` / `FormulaG (S : Type)` en `FOL/FOL.lean`, con
  `abbrev Term := TermG String` y `abbrev Formula := FormulaG String`, más los `export` de
  constructores y `injEq` y **tres shims** (`Term.noConfusion`, `Formula.noConfusion`,
  `Formula.ex.inj`): para un inductivo CON parámetro, Lean 4.31 genera el `noConfusion`
  **heterogéneo** y **no** genera `Ctor.inj`. Coste medido: **3 ficheros**, 147 footprints
  idénticos.
- **ADR-069** — la **capa de operaciones** genérica en `Sym`: `neg`/`top`/`iff`, `lift*`,
  `subst*`, `getAt?`/`replaceAt`, más `occurs*`/`abs*` (`Eigenvariable`) y `rename*` (`Rename`).
  Nuevo módulo **`FOL/SymClasses.lean`** con las clases `FreshSym` y `EnumSym` y la instancia
  `FreshSym (List Char)`; las de `String` viven donde viven sus pruebas.
  ⛔ `Derives` y `LocalRule` se dejan en `String` — decisión, no olvido.
- **ADR-071** — `Derives₀` y `LocalRule` genéricos, con el parámetro **implícito** para que la
  notación `⊢₀` sobreviva. Dos firmas, cero errores en los 22 ficheros consumidores.
  ⛔ Rectifica ADR-069: `LocalRule` sigue a `Derives₀`, no a `Derives`.
- **ADR-072** — el control `[E]` de `check-doc-sync.bash`, **rearmado**: la referencia deja de ser
  este fichero y pasa a calcularse por documento (`git log -1` del propio documento), con tabla
  de deuda declarada y rotura en los dos sentidos.

### Added (2026-09-17) — el HAUPTSATZ, el catálogo clásico y la forma normal de Skolem

- **ADR-050/051/052** — `FOL/Hauptsatz0.lean`: **`hauptsatz : CutAdm`**, `cut_elimination`,
  `herbrand_extraction` y **`herbrand`** ya incondicional. `[propext, Quot.sound]`.
- **ADR-053…056** — el catálogo clásico: `derives0_consistent_fin` (consistencia **sin**
  `Classical.choice`), `compactness₀`, `loewenheim_skolem_down`, `derives0_exBlock_of_cert`,
  `henkin_conservative`.
- **ADR-057…060** — la capa **prenexa** (`Prenex0`, `PrenexNF0`) y **Skolem** (`Skolem0`,
  `SkolemN0`), incluido el axioma bajo un prefijo `∀ⁿ`.
- **ADR-061** — FOL adopta `check-doc-sync.bash`; en su primera ejecución encuentra nueve cosas.
- **CI** — FOL vuelve a tener CI: no la tenía desde mayo, y las dos veces que había corrido
  **falló en 0 s**. El gate de `sorry` pasa a ser **bloqueante**.

### Added (2026-09-16) — COMPLETITUD, y la vía H

- **ADR-039/040/041** — `FOL/Canonical0.lean`: **`completeness₀ : Γ ⊨ f → Γ ⊢₀ f`** y
  `derives0_complete_iff`, con **cero axiomas del proyecto**. La no-finitud queda en **una línea**
  Π⁰₁ (el `if IsConsistent₀` de `LindenbaumStep`): es el **WKL**.
- **ADR-042…049** — la vía H: `Derives₁`, `Derives₂`, el certificado de Herbrand,
  `LK₀`/`LKc`, `ndToLK`, y la solidez del cálculo de secuentes.

### Added (2026-09-14) — `Derives₀`, y con él una metateoría que significa algo

- **ADR-033** — **`Derives₀`**: los 21 constructores **sin la ω-regla ni los cuatro
  habitantes-axioma** ⇒ se puede inducir sobre él (M-11 no aplica).
- **ADR-034…037** — `derives0_soundness` (el repo tiene por fin un cálculo de FOL⁼ **sólido**),
  el renombrado y su recíproca, el paso de **eigenvariable**, y `henkin_step_consistent`.

### Added (2026-09-13) — la Completitud, de cinco axiomas a uno

- **ADR-030** — la enumerabilidad de `Formula` deja de ser un postulado (`FOL/Enumeration.lean`).
- **ADR-031** — las dos congruencias de la igualdad, demostradas.
- **ADR-032** — `henkin_extension_lemma` **medido**: sale, y **por eso no se paga**; queda
  protegido por `check-axioms.bash`, que rompe **también si el contador baja a 0**.

### Changed (2026-09-12) — la cuarentena, los axiomas y la doctrina

- FOL pasa de **13 a 4** `axiom`, y los cuatro son los que el kernel obliga.
- Se retiran tres librerías, entra `TheoryFramework`, y `git-lock` deja de proteger lo que no era.

### Removed (2026-09-11) — ⛔ `soundness` era FALSO

- `soundness : Γ ⊢ f → Γ ⊨ f` **no es demostrable porque no es verdad**, y junto con `raa`
  demostraba **`False` sin hipótesis**. Evidencia compilada en `cuarentena/Inconsistencia.lean`.
  De aquí sale **M-11**: *un `axiom` que HABITA un inductivo prohibe demostrar nada sobre él por
  INDUCCIÓN*. ⚠️ Y `gen` **no** es la ω-regla — su docstring lo decía y era falso.

### Changed (2026-05-28 … 2026-07-12) — lo que hubo entre medias

- `subst_lift_cancel_formula` era un **`axiom` FALSO**; pasa a teorema en su forma restringida
  verdadera (2026-06-23), y la corrección se propaga a `FOLPure`/`FOL_poli` en septiembre.
- Conmutaciones De Bruijn en `Theorems/Eq.lean`, meta-reglas ω en `MetaRules.lean`, `dne`,
  semantica polimórfica, modelo cociente para FOL⁼.
- Toolchain a **Lean v4.31.0** (2026-07-04) y plantilla unificada de gobernanza (2026-07-12).

### Added (2026-05-16)

- **TheoryFramework** — nueva `lean_lib` con marco genérico de teorías:
  - `Logic.lean`: `class LogicSystem (F : Type)` con campos `derives`, `bottom`, `neg`, `semanticEntails`, `sound`, `complete`.
  - `Theory.lean`: `structure Theory F`, operaciones `proves`, `models`, `empty`, `fromList`, `singleton`.
  - `Properties.lean`: `IsConsistent`, `IsSyntacticallyComplete`, `IsAxiomRedundant`, `IsIrredundant`, `IsMaximalConsistent`.
  - `Relations.lean`: `LE (Theory F)` (extensión de teorías), `TheoryEquivalent`, `IsConservativeExtension`, `TheoryUnion`, `TheoryIntersection`, lemas de monotonía.
  - `MetaTheorems.lean`: `proves_iff_models`, `proves_monotone`, `models_monotone`, `inconsistent_upward`, `consistent_of_le`, `equiv_of_conservative`, `TheoryEquivalent.symm/trans`, `empty_le`.
  - Instancias: `LogicSystem PropLogic.Formula`, `LogicSystem Formula` (FOLPure), `LogicSystem Formula` (FOL^=, heredando el sorry de Completeness).
- **FOLPure** — nueva `lean_lib` con FOL sin igualdad (0 sorries):
  - Misma arquitectura que `FOL` pero sin `Formula.eq`, `refl`, `subst`.
  - Completitud de Gödel y Compacidad demostradas sin sorries.
- **PropLogic** — nueva `lean_lib` con lógica proposicional (0 sorries):
  - Subconjunto de FOLPure sin cuantificadores.
  - Stack metamatemático completo: Deducción, Soundness, Completeness, Compacity.
  - Módulos `Theorems/Impl.lean`, `Theorems/Neg.lean`, `Theorems/Derived.lean`.

### Added (2026-05-08 18:22)

- **Fase 6 Completada (FOL con Igualdad)**:
  - Refactorización del modelo canónico a un modelo cociente (`CanonicalDomain`) basado en la equivalencia sintáctica (`termEqv`).
  - Demostración de los teoremas de congruencia y "lift" de funciones y predicados al nuevo dominio.
  - Adaptación y demostración del Lema de la Verdad (`truth_lemma`) para el modelo cociente.
  - Demostración del Teorema de Completitud de Gödel para FOL con Igualdad.
  - Demostración del Teorema de Compacidad Semántica como corolario en `Compacity.lean`.

### Added (2026-04-25 22:00)

- El proyecto base de Lógica de Primer Orden (FOL) se congela en su versión 1.0.0.
- Inicio de la nueva arquitectura para incluir Igualdad (`=`) en una nueva rama.

### Added (2026-04-25 21:30)

- Declaración del axioma `henkin_extension_lemma` para manejar la expansión de constantes.
- Formalización del Teorema de Compacidad (`compactness_theorem`) y Consistencia (`consistency_of_satisfiable`) en `Compacity.lean`.
- El proyecto alcanza oficialmente **0 sorries** en su totalidad. ¡Hito final completado!
- Build status: ✅ Passing, 0 warnings.

### Added (2026-04-25 21:00)

- Formalización de la construcción de Henkin en `Completeness.lean`.
- Demostración formal del Lema de Lindenbaum (`lindenbaum_lemma`) y Compacidad Sintáctica.
- Demostración del Lema de la Verdad (`truth_lemma`) mediante inducción fuerte sobre la complejidad de fórmulas.
- Demostración del Teorema de Completitud de Gödel (`completeness`).

### Added (2026-04-25 20:30)

- Demostración completa de los lemas de sustitución semántica y reescritura en `FOL/Semantics.lean`, resolviendo la "trampa de De Bruijn" mediante inducción generalizada.
- El proyecto alcanza 0 sorries en toda la formalización de la sintaxis, deducción natural y corrección semántica (Soundness).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-25 20:00)

- Demostración completa del Teorema de Deducción en `FOL/Deduction.lean`.
- Definición de Modelos y Semántica de la lógica de primer orden en `FOL/Semantics.lean` (`Model`, `evalFormula`, `satisfies`).
- Demostración completa del Teorema de Corrección (Soundness) en `FOL/Soundness.lean` apoyada en los lemas semánticos.
- Implementación de la táctica `derive_raa` en `FOL/Tactics.lean`.
- Estado del Build: 0 errores, 5 sorries activos en `Semantics.lean` correspondientes a los lemas de sustitución y reescritura.

### Added (2026-04-25)

- Implementación de tácticas de automatización en `FOL/Tactics.lean`: `derive_hyp`, `derive_rewrite` y `derive_weaken`.
- Finalización oficial de la Fase 4 (Automatización).
- Inicio formal de la Fase 5 (Metamatemática y Completitud).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-20 00:00)

- Initial project structure from lean4-project-template

---

## [0.2.0] - 2026-04-20

### Added

- `NAMING-CONVENTIONS.md`: Full Mathlib-style naming dictionary with 12 formation rules, symbol-to-word dictionary, and migration tables
- `NEXT-STEPS.md`: Development phase planning template
- `THOUGHTS.md`: Design journal template for recording ideas and alternatives
- `REFERENCE.md` §0: Naming conventions quick-reference guide for the reader
- `REFERENCE.md` §Compliance: Checklist against AI-GUIDE.md requirements
- `AI-GUIDE.md` §22-23: Directory and subdirectory organization protocol
- `AI-GUIDE.md` §24-25: Annotation system (`@axiom_system`, `@importance`)
- `AI-GUIDE.md` §26-28: Cross-reference files documentation
- `AI-GUIDE.md`: Symbol-to-word dictionary and theorem formation rules summary in Naming Conventions section
- `DECISIONS.md`: ADR-004 (Mathlib naming), ADR-005 (directory-aligned namespaces), ADR-006 (annotation system), ADR-007 (separate NAMING-CONVENTIONS.md)
- `_template.lean`: Added naming convention reminders, annotation metadata, expanded section structure
- `CURRENT-STATUS-PROJECT.md`: Development phases tracking table

### Changed

- `README.md`: Added naming conventions summary table, documentation table format, subdirectory-aware project structure
- `DEPENDENCIES.md`: Added subdirectory-aware structure, multi-level dependency hierarchy example, Mermaid subgraph example

---

## [0.1.0] - 2026-04-20

### Added

- `Prelim.lean`: preliminary definitions

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/ProjectName)
- [Issues](https://github.com/julian1c2a/ProjectName/issues)
