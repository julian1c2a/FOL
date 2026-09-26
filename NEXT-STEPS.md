# Próximos Pasos — FOL

> # ⛔⛔ AVISO DE ESTADO — 2026-09-26 (reescrito: el del 2026-09-12 había quedado FALSO). LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | 🏁 **Sí, sobre `Derives₀`** (2026-09-14): `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` (`FOL/Soundness0.lean`), y con ella `derives0_consistent`. ⛔ La de **`Derives`** sigue siendo **FALSA** en presencia de `FOL/MetaRules.lean`: `FOL/Inconsistencia.lean`, hoy **en el build** |
> | «Compacidad» ✅ | 🏁 `compactness₀`, `loewenheim_skolem_down` y el modelo infinito `infinite_model_of_large`, en `FOL/Compacity0.lean`. El `Compacity.lean` vacuo **se borró** el 2026-09-23 |
> | «Completitud» ✅ / «1 sorry» | 🏁 `completeness₀ : Γ ⊨ f → Γ ⊢₀ f` (`FOL/Canonical0.lean`, 2026-09-16), con **cero axiomas del proyecto**: `[propext, Classical.choice, Quot.sound]`, y ese `Classical.choice` es el WKL de `Lindenbaum0` (ADR-041). `Completeness.lean` y su último postulado, `henkin_extension_lemma`, **se borraron** el 2026-09-23. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **4 `axiom`**, los de `MetaRules` que el kernel obliga, y ninguno más fuera de las librerías retiradas · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026-09-12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Los seis teoremas del cierre (T1 a T6, 2026-09-23 y 2026-09-26) están en el árbol**, sobre `Derives₀`; el catálogo, en `CURRENT-STATUS-PROJECT.md` («Estado vigente») y `REFERENCE.md` §6. ⛔ Y lo que NO hay: la propiedad de disyunción para `Derives₀` es **FALSA** (`derives0_no_disjunction_property`).
> (Este aviso decía que «lo único sólido MEDIDO» era `prf0_soundness`, en RPP: dejó de serlo el 2026-09-14.)
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md`

**Last updated:** 2026-09-26 — aviso reescrito y sección «Lo que queda» nueva; el plan de fases de abajo es HISTÓRICO (2026-05-16).
**Autor**: Julián Calderón Almendros

## ⬜ Lo que queda para CERRAR FOL — 2026-09-26

**Hecho**: los seis teoremas del catálogo del cierre (T1-T6) más `inv_allR`/`inv_exL`
(`CHANGELOG.md`, entradas del 2026-09-23 y del 2026-09-26; `../ROBINSON_PlusPlus/DECISIONS.md`,
RPP-100). El estado vigente, en `CURRENT-STATUS-PROJECT.md`. Lo abierto, medido el 2026-09-26 por la
auditoría de cierre (8 agentes con refutación):

### Decisiones del propietario — contestadas el 2026-09-26 (salvo D3)

| # | qué | decisión | estado |
|---|---|---|---|
| D1 | `FOL/Tactics2.lean`: **idéntico**, salvo la línea del `import`, a `cuarentena/librerias-retiradas/FOL_poli/Tactics2.lean` (diff medido); no lo importaba nadie y ningún build lo compilaba | «de acuerdo, bórralo» | ✅ **BORRADO** (53 módulos activos) |
| D2 | T2: `IsSyntacticallyComplete₀` está definida por **pertenencia** (`∀ f, S f ∨ S (¬f)`), no como la «teoría completa» de la teoría de modelos (sobre **sentencias**, por **derivabilidad**; el árbol no tiene noción de sentencia) | **renombrarla** antes de congelar `Canonical0` | ⬜ nombre medido y propuesto: **`IsMemComplete₀`** (0 colisiones en FOL/RPP/PeanoRF); dos líneas de código (la `def` y el tipo de `max_cons_complete`), ninguna fila de footprint cambia |
| D3 | Las dos **ABIERTA** de `[G.2]`: el puente `LK₀`→`LKp` (`Craig0`) y volver a φ y Γ con `skolem_conservative_nf` (`SkolemHerbrand0`) | «lo hablamos al final» | ⏸ aplazada a la conversación final |
| D4 | La DIFERIDA de `ModelG` (`FOL/FOL.lean`, «Para reabrirla») | declararla **CERRADA** «si efectivamente está terminada» | ✅ **verificado: TERMINADA** — todo lo decidido (ADR‑068/069/071/083) está en el árbol; `FreshSym`/`EnumSym` no tienen consumidores; RPP y PeanoRF sólo instancian `String` ⇒ ⬜ se cierra en el próximo paso (quitar el marcador y su fila: `[G.2]` 19→18; tocar `FOL/FOL.lean` recompila todo) |
| D5 | La DIFERIDA de `Lift0` (refactor `absTerm'`, ~150 l. de enunciados; su disparador ya se cumplió) | «**hacemos el refactor**» | ⬜ los DOS diseñadores convergen en el **genérico**: núcleo `absTermP` en `Eigenvariable` con el predicado de símbolos como parámetro, `absTerm` como caso `(· = c)` y `liftTerm` enlazado por lema (sin tocar `FOL/FOL.lean`); el puente por constante fresca se descarta con números. Juez adversarial en curso. PeanoRF sólo usa `posDepth` de `Eigenvariable` |
| D6 | Nombre de T1 (`model_existence_iff` o `…₀`) | *«Tendremos modelo para el FOL fundamental, que es intuicionista; ₀ no sé qué es lo que realmente marcaba»* ⇒ **pregunta**: qué marca `₀` | ⬜ **medido**: `₀` no sigue ninguna regla formulable. Nació como ordinal de plan («PASO 0», ADR‑033); lo llevan 12 de 817 declaraciones, 3 sin mencionar ningún cálculo (`IsHenkin₀`, `IsSyntacticallyComplete₀`, `compactness₀`), y 89 de las 177 que dependen de `Derives₀` no lo llevan (la marca dominante es el prefijo `derives0_`/`lk0_`). ⚠️ En RPP, `Prf₀` es la capa INTUICIONISTA. Propuesta: el subíndice nombra un cálculo (₀ clásico, ᵢ intuicionista), nada sin cálculo lleva subíndice ⇒ T1 = `model_existence_iff₀` y 3 renombres. ⬜ decisión |
| D7 | Migración `String`→`List Char` (`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §7.3) | cerrarla «si está terminada» | ⛔ **NO lo está** (medido: `abbrev Term := TermG String`, `abbrev Formula := FormulaG String`; sólo existen el parámetro, las clases y `FreshSym (List Char)`) ⇒ **no se cierra por terminada**. Medido: terminarla no cambia ningún footprint de T1‑T6 (su `Classical.choice` es el WKL) y, en FOL, como mucho 5 de las 51 filas con choice lo deben sólo a `String`; lo que se ganaría está en RPP. Recomendación: **cerrarla como ABANDONADA en FOL**. ⬜ decisión |

### Externo

| # | qué |
|---|---|
| X0 | ⛔ **Condición del propietario (2026-09-26), no negociable: FOL no puede depender de nada más allá de sí mismo.** Los siete módulos tienen que llegar sin ningún `import`, `open` ni identificador de PeanoRF, RPP o Peano. Medido: **los siete la incumplen hoy** (todos importan `PeanoRF.Prelim` de forma transitiva, que trae RPP y Peano; `Collapse` y `Eq` usan `zero`/`zero_sym`/`succ` de RPP; y `Eq` usa `FOL.substTerm_liftTerm`, que hoy le llega **a través de RPP**). ⬜ Carta a PeanoRF, redactada, sin enviar |
| X1 | **PeanoRF**, propuesta (C) aceptada: `Subst`, `DerivesI`, `SubstDerives`, `Consistency`, `Eq`, `Collapse` y `Slash` (éste con `lock`). Sin entregar (su último commit, 55288bb, 2026-09-23). Falta: parametrizar `collapseT` (`Collapse.lean:61`), sacar `eqI_congr_succ` de `Eq`, y ⚠️ **re-apuntar el `import PeanoRF.Prelim` de `Subst`/`DerivesI`**: la tanda 1 tampoco compila en FOL sin eso, y nuestra respuesta (2) decía «condición: ninguna». Su cierre transitivo toca 14 módulos de FOL |

### Trabajo

| # | qué |
|---|---|
| W1 | **Pasada de higiene de docstrings** antes de cualquier `freeze`: citas a ficheros borrados (`cuarentena/…`) y prosa en futuro caducada en `Canonical0`, `Inconsistencia` (dice estar en `cuarentena/`), `Soundness0`, `Lindenbaum0`, `Fresh0`, `HenkinLimit0`, `Henkin0`, `Rename`, `SequentSound0`, `Skolem0`; `Complexity` dice «cero axiomas» y mide `[propext]`; la cabecera de `Finitary0` (l. 20/26) contradice su §«Dónde NO paga el Hauptsatz»; y `FOL/FOL.lean` llama «LS↑ hasta ℵ₀» a lo que no es LS↑ (tocarlo recompila todo) |
| W2 | `REFERENCE.md`: §3.13 dice «veintiún módulos», §2 no tiene la capa `₀`, §7.1 lista módulos retirados, §3.10 presenta `soundness` como «✅ Completo» |
| W3 | `DEPENDENCIES.md`: regenerarlo desde las líneas `import` (53 módulos, 95 aristas, medido tras borrar `Tactics2`) o borrarlo |
| W4 | `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`: tres filas obsoletas (l. 569, 1404-1405, 1421-1425) |

### ❄️ Congelación

`py criba-congelacion.py` (criterios medibles 1, 3 y 4): **16** módulos pasan. La refutación
adversarial objeta **13**; sólo resisten `Prenex0`, `PrenexNF0` y `SkolemN0`. ⇒ **no congelar nada**
hasta W1, D2-D5 y la entrega de PeanoRF (cuyo cierre transitivo no debe congelarse antes de que
compile aquí).

⛔ **Fuera de alcance, con su motivo**: LS↑ (ver `Compacity0` §3); la versión ACOTADA de
`derives0_qf_iff` (OFERTA en `[G.2]`, coste no medido); Beth y Robinson (piden el puente `LK₀`→`LKp`
y renombrar símbolos de relación); la noción de **sentencia** (bloqueo transversal: sin ella no se
enuncian bien la equivalencia elemental ni la categoricidad); y la propiedad de disyunción para
`Derives₀`, que es **FALSA**.

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
