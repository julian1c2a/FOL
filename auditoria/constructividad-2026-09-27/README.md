# La auditoría de constructividad de FOL — 2026‑09‑27

**Last updated:** 2026-09-27 — creado con la auditoría y la ejecución de D1–D8.

**Sobre:** FOL `537cc20` / RPP `7487ca1` (antes) y el árbol tras las decisiones D1–D8 (después) ·
**Autor:** Julián Calderón Almendros ·
**Decisiones:** `../../NEXT-STEPS.md` (❄️ Congelación) y ADR‑110 de `../../../ROBINSON_PlusPlus/DECISIONS.md` ·
**Clasificación vigente:** `../../AXIOMS.md` §4

## Qué es esta carpeta

La medida de **qué hay de no constructivo en FOL, dónde y por qué**, guardada para poder repetirla y
contrastarla (el propietario pidió conservarla en el repo). `#print axioms` dice *que* una constante
lleva `Classical.choice`, no *por qué*: aquí está el porqué, constante a constante.

🔑 *El footprint no distingue las causas.* La auditoría separó tres: las **esenciales** (el enunciado
implica un principio clásico, medido sin `Classical.choice`), las **evitables** (una instancia mal
elegida, un `open Classical` para un `filter`, un `Exists.choose` de algo calculable, lemas del núcleo
que decodifican UTF‑8) y las de **ruta** (corolarios que pasan a propósito por la completitud o la
solidez). D1–D8 retiraron las evitables; lo que queda está en la tabla de abajo y en `AXIOMS.md` §4.

| fichero | qué es |
|---|---|
| `Audit.lean` | el metaprograma. Para CADA constante de los módulos `FOL*` y `TheoryFramework*` del entorno compilado: sus axiomas (`collectAxioms`), si es `noncomputable` y, si lleva `Classical.choice`, las constantes que usa DIRECTAMENTE y que también lo llevan. Escribe `actual/decls.tsv` y `actual/choice_edges.tsv` |
| `analyze.py` | resume un directorio con esos dos TSV: clases de footprint, axiomas declarados, `noncomputable`, fuentes externas de `Classical.choice` y el reparto por módulo (sin las constantes generadas) |
| `antes/` | FOL `537cc20`, antes de D1 |
| `despues/` | el árbol tras D1–D8 (2026‑09‑27) |
| `experimentos/` | los ficheros de experimento, compilados con `lake env lean` (abajo, uno por línea) |
| `auditoria-juez-esceptico.json` | los informes: el de cada tarea, el del juez y el del escéptico |

## Cómo se relanza

Desde la raíz de `../ROBINSON_PlusPlus` (FOL no se construye desde FOL, M‑3), con FOL y
TheoryFramework compilados (`lake build "@FOL/FOL" "@FOL/TheoryFramework"`):

```bash
lake env lean ../FOL/auditoria/constructividad-2026-09-27/Audit.lean
#   → escribe ../FOL/auditoria/constructividad-2026-09-27/actual/{decls,choice_edges}.tsv
py ../FOL/auditoria/constructividad-2026-09-27/analyze.py
#   → resume actual/ (sin argumento, el actual/ que está junto al script)
py ../FOL/auditoria/constructividad-2026-09-27/analyze.py ../FOL/auditoria/constructividad-2026-09-27/despues
#   → o cualquier otro directorio con decls.tsv y choice_edges.tsv
```

`actual/` se crea al relanzar; lo guardado son `antes/` y `despues/`. Para ver qué cambió desde la
última medida, se compara el `resumen.txt` de `despues/` con la salida nueva.

## `antes/` y `despues/`

| fichero | qué es |
|---|---|
| `decls.tsv` | una fila por constante: `modulo`, `nombre`, `clase` (`thm`, `def`, …), `noncomputable`, `axiomas` |
| `choice_edges.tsv` | una fila por arista entre una constante con `Classical.choice` y otra que usa directamente y que también lo lleva: `modulo`, `nombre`, `usa`, `modulo_usa`, `es_fol` |
| `frontera.txt` | la **frontera**: las constantes de FOL que usan directamente una constante EXTERNA con choice (las filas con `es_fol = false` de `choice_edges.tsv`). Por ahí entra |
| `resumen.txt` | la salida de `analyze.py` sobre ese directorio |
| `origenes_titulares.txt` (sólo en `antes/`) | para cada titular con choice, las entradas de la frontera de las que lo hereda. ⚠️ En 8 casos omite al propio titular como origen; lo recalcula `experimentos/exp-juez/scen.py` |

⚠️ La línea `modulos:` de `resumen.txt` cuenta los módulos CON constantes: 53 antes y 54 después
(`TheoryFramework.Instances.FOL` estaba vacío hasta D7; `FOL.Core` sólo importa). La cifra canónica de
módulos es la de `check-doc-sync.bash`.

## `experimentos/`

Uno por tarea. Todo se compiló con `lake env lean` desde la raíz de RPP y se cerró con `#print axioms`.

| carpeta | qué midió |
|---|---|
| `exp-deceq/` | E0–E6: el choice de `henkin_step_consistent₀` y `derivesSet0_intro_impl` venía de un `open Classical` que decidía `x = H` en un `filter`; con `FOL.DecEq` desaparece (E1–E3), y también sin decidir nada, con `ctx_split` (E4, la variante que entró). E5–E6: qué parte de `LindenbaumStep` y de `max_cons_contains` es la condición Π⁰₁ y qué `byContradiction` es esencial |
| `exp-bnd-invOf/` | `Exp`, `ExpAll`, `ExpFresh`: `bnd` se calcula por recursión con `utf8ByteSize`, sin axiomas; la inversa LOCAL de `shift` (`locInv`). `Probe*`: qué constantes de `String`/`ByteArray` del núcleo llevan choice. `ProbeUnshift`: cuatro `unshift` por la API de `String`, todas con choice (lo supera `exp-esceptico/U2`, sobre bytes). `sim.py`: el efecto sobre los titulares |
| `exp-string/` | E1–E9: la raíz del choice de `String` en v4.31 es el DECODIFICADOR UTF‑8 (E5–E6: censo del núcleo y camino hasta `Classical.propDecidable`; `core_string*.tsv`); la trampa de `ReflBEq String` por `String.instOrd` (E9); las cuatro variantes de `Fresh0`/`Enumeration` (E3, E8) y su propagación (E4). E7 son controles FALSOS: no deben compilar, y no compilan |
| `exp-varios/` | los tres `simp` de `Theorems/Eq` (`Eq*`); el choice de `FOL.Tactics` lo traen los tipos del marco meta (`Tac`); `derives0_em`/`derives0_peirce` sin completitud (`EmA`/`EmB`/`EmC`); `derives0_no_disjunction_property` por `Finitary0` (`Disj`); el alcance de `MetaRules` y del trío de `Eq` en RPP (`Reach*`, `reach_out.txt`, `tabla_rpp.txt`) |
| `exp-esencial/` | E1–E8 y `medidas.log`: la ESENCIALIDAD. Solidez ⇒ `¬¬P → P` y `lkc_sound` ⇒ `P ∨ ¬P`, sin ningún axioma (E1); `max_cons_*` ⇒ `¬¬P → P` (E3); `model_existence_lemma₀` ⇒ `¬P ∨ ¬¬P` (E7); expansión de Skolem ⇒ AC ⇒ EM (E6, E6b). Y lo NO esencial: Lindenbaum impredicativo (E4), cociente por listas (E5), Henkin sintáctico (E8); solidez para modelos ¬¬‑estables o decidibles (E2, E2b) |
| `exp-inv/` | el inventario: qué choice era accidental, con variantes (`Fresh`, `Enum`, `Bnd`, `StringCmp`), y la instancia de `TheoryFramework` sobre `Derives₀` (`TFInst`); `edits.*`, sus ediciones. ⚠️ `Accidental.lean` NO compila (un `omega` deja `sorryAx` en su `cst_zero_ne`): la misma medida sale de `Fresh.lean` y de `exp-string/E3` y `E8` |
| `exp-juez/` | el juez. `Comb.lean` combina todas las variantes y mide `lindenbaum_lemma₀` y `henkin_completion₀` con los MISMOS enunciados en `[propext, Quot.sound]` (el hallazgo); `Twins.lean`, los corolarios de ruta con variante sin choice y la esencialidad de `lk0_sound`; `scen.py`, los escenarios sobre el grafo; `edits_juez.*`, las 32 ediciones de documentación; `out/`, salidas |
| `exp-esceptico/` | el escéptico. `Same.lean`: 24 comprobaciones `rfl` de que cada variante tiene el MISMO tipo que el original; `Esc2.lean`: esencialidad de `quotientOut` como constante (EM), de `max_cons_forall`, `max_cons_neg` y `truth_lemma₀` (`¬¬P → P`) y de `consistency_of_satisfiable₀`; `U2.lean`: una inversa GLOBAL de `shift` sin choice, sobre bytes (el origen de `Fresh0.unshift`); `mine.py`/`mine.out`, un recálculo independiente del grafo; `out/`, la recompilación de los 42 experimentos más tres sondas propias (45 salidas) |

⚠️ **Son el registro de la medida, no controles.** Se compilaron contra FOL `537cc20`: los que citan
constantes que D1 retiró (`Rename.invOf`, `Canonical0.quotientOut`, …) o reprueban sobre la definición
antigua de `LindenbaumStep` o de `bnd` no compilan contra el árbol de después, o miden otra cosa. Las
rutas que citan los informes del JSON (`…/scratchpad/audit/exp-*`) son las de la carpeta de trabajo
donde se hicieron; su contenido es el de `experimentos/`, salvo las copias editadas de los módulos
(`check/`, `orig/`), que no se guardaron.

## `auditoria-juez-esceptico.json`

* `informe`: las seis tareas (`exp:deceq`, `exp:bnd-invOf`, `exp:string`, `exp:varios`,
  `analisis:esencial`, `inventario`), cada una con su resumen y sus experimentos o fuentes.
* `juez`: el resumen; las 33 entradas de la frontera, clasificadas; titulares liberables,
  irreducibles, `noncomputable`, axiomas del proyecto y extensionalidad; 10 pendientes; las 8
  decisiones D1–D8 que se plantearon al propietario; y 32 ediciones de documentación.
* `contra`: el escéptico. Resumen y 25 veredictos, de los que refutó 13 con medida: entre ellos, que
  una inversa global de `shift` sin choice «no era viable», que `quotientOut` fuera eliminable como
  constante (lo era su uso) y que `max_cons_neg`, `truth_lemma₀` y `consistency_of_satisfiable₀`
  fueran sólo hipótesis.

## Resumen

| medida | antes (`537cc20`) | después (D1–D8) |
|---|---:|---:|
| constantes de FOL + TheoryFramework | 2978 | 3074 |
| con `Classical.choice` | 157, en 17 módulos | **84**, en 11 módulos (3 son código meta de `FOL.Tactics`) |
| sólo `propext` y/o `Quot.sound` | 1002 | 1107 |
| sin ningún axioma | 1814 | 1878 |
| dependen de los axiomas de `MetaRules` | 5 | 5 |
| `noncomputable` | 8 | **1** (`SkolemN0.skF`) |
| frontera: declaraciones lógicas por donde entra choice | 30 | **13** (más 3 meta, las dos veces) |
| titulares de FOL con choice (filas de RPP `check-footprints.bash`) | 55 de 252 | **34** de 252 |
| filas de `check-footprints.bash` | 513 | 517 (4 nuevas de `TheoryFramework.Instances`) |

**La frontera de después**, clasificada: esenciales y medidas, `derives0_soundness`, `lkc_sound` (la
semántica de Tarski en `Prop`), `max_cons_contains`, `max_cons_impl_iff`, `max_cons_or`,
`max_cons_complete`, `max_cons_forall` (el lema de la verdad sobre un maximal ARBITRARIO), `skF` y
`skF_spec` (las funciones de Skolem semánticas); esencial como hipótesis, el `byContradiction` final de
`completeness₀` (forma de Markov); de ruta, `skolem_conservative₀` (enunciado sintáctico, prueba por
modelos); controles, `derives0_em` y `derives0_peirce`. Y el código meta de `FOL.Tactics`.

**Los 34 titulares con choice**: los 27 irreducibles (10 esenciales medidos, 3 por inclusión,
`completeness₀` como hipótesis, 5 semánticos sin clasificar y 8 de enunciado sintáctico que sólo lo
llevan por la ruta semántica) y 7 corolarios de ruta conservados a propósito (ADR‑061). El detalle,
en `AXIOMS.md` §4.3.

⚠️ **84, y no los 65–66 que proyectaban el juez y el escéptico**: aquella proyección reprobaba también
los corolarios de ruta de `Soundness0`, `SequentSound0` y `Canonical0` (se conservaron a propósito,
D3) y no contaba ni los lemas nuevos del cociente por listas (`listQuot`, `consQ` y sus auxiliares,
que heredan el choice de `termSetoid`: sus pruebas pasan por `max_cons_contains`) ni la instancia de
`TheoryFramework`.

⛔ **El hallazgo principal**: el `Classical.choice` de la completitud **no** es «el WKL del `if
IsConsistent₀` de Lindenbaum». `Prop` es impredicativo y la etapa se define con la condición dentro,
sin decidirla: `lindenbaum_lemma₀` y `henkin_completion₀` son hoy `[propext, Quot.sound]`. El WKL
(completitud ⇔ WKL₀ sobre RCA₀, Simpson IV.3.3) nombra la FUERZA lógica de la completitud, no el sitio
de un `Classical.choice` en Lean.
