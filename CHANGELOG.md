# Changelog

**Last updated:** 2026-09-26
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
