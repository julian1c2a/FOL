# Current Project Status — FOL Ecosystem

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
> ✅ **2026-10-03 · deuda saldada**: los cinco módulos 🧊 que conservaban el texto anterior al borrado de `FOL/MetaRules.lean` (`Soundness0`, `Canonical0`, `Compacity0`, `Rename`, `TheoryFramework/Instances/FOL`) se descongelaron con autorización del propietario, se corrigieron sólo sus comentarios y se volvieron a congelar: «Estado vigente», abajo, y `NEXT-STEPS.md`.
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md` · ADR‑114 y ADR‑115 de `../ROBINSON_PlusPlus/DECISIONS.md` (2026-10-02)

**Last updated:** 2026-10-05 — D7 ejecutada (ADR‑129 de RPP): los símbolos son `List Char` («Estado vigente», una línea nueva bajo la tabla; y las ℵ₀ constantes de LS↑). Antes, 2026-10-03 — la deuda de los cinco módulos 🧊 con textos falsos, SALDADA (`thaw` autorizado, sólo comentarios, re‑congelados). Antes, 2026-10-02 — 🗑️ `FOL/MetaRules.lean` borrado (ADR‑115 de RPP: sus cuatro `axiom` eran refutables): cifras canónicas (0 `axiom`, **54 módulos activos**), aviso, «Estado vigente» (la solidez de `Derives` pasa a lo que hay; `Derives₀` ya no se define por diferencia con `MetaRules`) y la deuda de cinco módulos 🧊 que esperan un `thaw` autorizado; en el cuerpo HISTÓRICO, sólo la fila de `Soundness.lean`. Antes (2026-09-27): 🧊 23 módulos congelados (tres lotes: 5 + 10 + 8), tras N5 (los nombres técnicos, auxiliares) y N7 (`herbrand_of_skolemNF₀`, reforzado con la ecuación): `NEXT-STEPS.md` ❄️. Antes, el mismo día: la auditoría de constructividad y sus decisiones D1–D8: `Classical.choice` en 84 constantes (eran 157) y en 34 titulares (eran 55); Lindenbaum y la extensión de Henkin, sin `Classical.choice`; la tesis del WKL, rectificada; la instancia `fol0System` de `TheoryFramework`, declarada. Antes, el mismo día, P4: el fragmento sin cuantificadores, acotado y DECIDIDO (`QFDecide0`, **55 módulos**). Antes, 🧊 cinco módulos congelados; 18 titulares renombrados por la regla de subíndices (`hauptsatz₀`, `herbrand₀`, `craigₚ`…). Antes (2026-09-26): D3 cerrada: Craig para `⊢₀` con igualdad (`Interpolation0`, **54 módulos**) y Herbrand para `φ`/`Γ` cualesquiera. Antes, D3b: Herbrand para `φ` y `Γ` cualesquiera. Antes, D2/D4/D5/D6/D7 ejecutadas: refactor `absTerm'` (D5), regla de subíndices y sus renombres (T1 = `model_existence_iff₀`, T2 = `IsMemComplete`, `compactness`), vía de `ModelG` y migración a `List Char` CERRADAS, higiene de docstrings. Antes, 🗑️ D1: `Tactics2.lean` borrado ⇒ **53 módulos activos**. Antes, el mismo día: ⭐ entran T4 (`Hauptsatz0` §9) y T6 (`Compacity0` §3): **los seis teoremas del cierre están en el árbol**; aviso de cabecera reescrito (el del 2026-09-12 negaba Corrección, Completitud y Compacidad) y sección «Estado vigente» nueva. Antes (2026-09-23): entra `FOL/Complexity.lean` (encargo PeanoRF §3) y la cifra canónica pasa a **54 módulos**. ⚠️ La marca decía **2026-09-18 15:40** y `[E]` la cazó el mismo día que se movió el cuerpo — que es para lo que está el control.
**Author**: Julián Calderón Almendros

> 📐 **CIFRAS CANÓNICAS — medidas, no copiadas** (`bash check-doc-sync.bash`, 2026-10-02, tras borrar `FOL/MetaRules.lean`):
> **54 módulos activos** (`FOL/` 43 + `FOL/Theorems/` 5 + `TheoryFramework/` 6) ·
> **0 módulos en `cuarentena/`** · **0 `axiom` de Lean** en el build ·
> **0 sorry**.
> (Registro: hasta el 2026-10-02 eran «55» módulos activos, «44» en `FOL/`, y «4» `axiom`, los de `MetaRules`.)
>
> ⚠️ Esta línea existe para que el control tenga **contra qué comparar**: sin ella,
> `check-doc-sync.bash` calcula las cifras del árbol, no encuentra dónde contrastarlas e imprime
> «control VACÍO» — y sale **verde sin haber comprobado nada**. 🔑 *Un control sin nada que
> contrastar no aprueba: se abstiene, y la abstención se lee como aprobado.*
>
> ⛔ La cifra de **jobs** NO se publica aquí: FOL no se construye desde FOL (M‑3), y quien la
> mide es `../ROBINSON_PlusPlus`: `lake build "@FOL/FOL" "@FOL/TheoryFramework"` desde su raíz (⚠️ el `lake build` a secas de RPP sólo compila lo que RPP importa, y deja fuera la capa `₀`).

---

## 🏁 Estado vigente — 2026-10-02

El sujeto de la metateoría es **`Derives₀`** (`FOL/Derives0.lean`): los constructores de `Derives`
sin la ω‑regla `gen_rule`, que es admisible (`derives_to_derives0 : Γ ⊢ f → Γ ⊢₀ f`): los dos
cálculos derivan lo mismo, y sobre los dos se puede inducir. Hasta el 2026-10-02 la diferencia incluía
además los cuatro habitantes‑axioma de `FOL/MetaRules.lean`, borrado ese día por refutable (ADR‑115 de
RPP); hoy ningún cálculo de FOL tiene habitantes‑axioma. Todo lo de esta tabla compila sin `sorry` y
**sin axiomas del proyecto**; los footprints son los de `#print axioms`, vigilados por
`../ROBINSON_PlusPlus/check-footprints.bash` (las filas de `FOL.Inconsistencia.*` que cambian el
2026-10-02 las pone al día RPP en el push que sigue a éste: ADR‑115 §7).

| resultado | declaración | módulo | footprint |
|---|---|---|---|
| Corrección, consistencia | `derives0_soundness`, `derives0_consistent` | `Soundness0` | `[propext, Classical.choice, Quot.sound]` |
| **Corrección de `Derives`**, sin meta‑reglas (2026-10-02, ADR‑115 de RPP) | `derives_to_derives0` (`gen_rule` es admisible), `derives_soundness` | `Inconsistencia` §1 | `derives_to_derives0`: `[propext, Quot.sound]`; `derives_soundness`: `[propext, Classical.choice, Quot.sound]` (medidos el 2026-10-02: la sección «FOOTPRINT» al pie del módulo) |
| Consistencia finitaria | `derives0_consistent_fin` | `Finitary0` | `[propext, Quot.sound]` |
| Lindenbaum; la extensión de Henkin (maximal consistente con testigos) | `lindenbaum_lemma₀`, `henkin_completion₀` | `Lindenbaum0` | `[propext, Quot.sound]` (desde el 2026-09-27) |
| Completitud | `completeness₀`, `derives0_complete_iff` | `Canonical0` | `[propext, Classical.choice, Quot.sound]` |
| **T1** · existencia de modelo | `model_existence_iff₀` | `Compacity0` | ídem |
| **T2** · el maximal consistente decide cada fórmula (por pertenencia; ⚠️ aún no la «teoría completa» sobre sentencias) | `max_cons_neg`, `IsMemComplete`, `max_cons_complete` | `Canonical0` | ídem |
| Compacidad, LS↓ | `compactness`, `loewenheim_skolem_down` | `Compacity0` | ídem |
| **T6** · modelo numerable e infinito | `infinite_model_of_large` | `Compacity0` §3 | ídem |
| Hauptsatz, Herbrand | `hauptsatz₀`, `cut_elimination₀`, `herbrand₀` | `Hauptsatz0` | `[propext, Quot.sound]` |
| **Herbrand para `φ` y `Γ` cualesquiera** (D3) | `herbrand_validity₀`, `herbrand_validity_ctx₀` | `SkolemHerbrand0` §3 | `[propext, Classical.choice, Quot.sound]` |
| **T4** · fragmento sin cuantificadores | `derives0_qf_iff` (caracteriza) | `Hauptsatz0` §9 | `[propext, Quot.sound]` |
| **Decisor del fragmento sin cuantificadores** (P4) | `derives0_qf_iff_bounded`, `decideDerives0QF` | `QFDecide0` | `[propext, Quot.sound]` |
| **T3** · decisor proposicional | `ptautCheck_iff`, `instDecidablePTaut` | `Herbrand0` | `[propext]` (`ptautCheck_iff`) |
| **T5** · inversión de `LK₀` | las nueve proposicionales, `inv_allR` e `inv_exL` | `Inversion0` | `[propext, Quot.sound]` |
| Craig (fragmento puro `LKp`) | `craigₚ`, `craig_implₚ` | `Craig0` | `[propext, Quot.sound]` |
| **Craig para `⊢₀` CON igualdad** (D3) | `craig₀`, `craig_ctx₀` | `Interpolation0` | `[propext, Quot.sound]` |
| Skolem bajo prefijo | `skolem_conservative_n₀` | `SkolemN0` | `[propext, Classical.choice, Quot.sound]` |
| Conservatividad del axioma de Henkin (vía sintáctica) | `henkin_conservative₀` | `Skolem0` | `[propext, Quot.sound]` (desde el 2026-09-27) |
| **`TheoryFramework` sobre `Derives₀`** (D7, 2026-09-27) | `fol0System`, `fol0Sound`, `fol0Complete`, `fol0_proves_iff_models` | `TheoryFramework/Instances/FOL` | `fol0System`: ninguno; los otros tres, `[propext, Classical.choice, Quot.sound]` |

🔤 **Los símbolos son `List Char`** desde el 2026-10-05 (D7 de las decisiones del 2026-09-26, reabierta y ejecutada: ADR‑129 de RPP; fila D7 de `NEXT-STEPS.md`): `Term`, `Formula` y `Model` sobre `List Char`, y ninguna aparición de `String` en el código de `FOL/` y `TheoryFramework/`. Ninguna fila de FOL o `TheoryFramework` de `check-footprints` gana ni pierde `Classical.choice`; `evalFormula_updateCsts`, `evalTerm_updateCsts` (`Compacity0`) y la instancia `FOL.Fresh0.instFreshSymListChar` ya no dependen de ningún axioma.

📍 **Dónde está el `Classical.choice`** (auditoría de constructividad, 2026-09-27; `AXIOMS.md` §4):
lo llevan 84 de las 3074 constantes de FOL y TheoryFramework (eran 157) y 34 de las 252 filas de `check-footprints` (no todas son titulares tras N5, `NAMING-CONVENTIONS.md` §9) de
FOL (eran 55); `noncomputable` sólo queda `SkolemN0.skF`. Entra por **13** declaraciones: la
semántica de Tarski en `Prop` (`derives0_soundness`, `lkc_sound`) y el lema de la verdad sobre un
maximal ARBITRARIO (`max_cons_contains`, `max_cons_impl_iff`, `max_cons_or`, `max_cons_complete`,
`max_cons_forall`), esenciales y medidas; el `byContradiction` final de `completeness₀` (forma de
Markov: esencial como hipótesis); las funciones de Skolem semánticas (`skF`, `skF_spec`, esenciales) y
la ruta semántica de `skolem_conservative₀`, cuyo enunciado es sintáctico; y los controles
`derives0_em`/`derives0_peirce`. Más el código meta de `FOL.Tactics`. ⛔ **No** el `if` de
Lindenbaum: la tesis «el choice de la completitud es el WKL de Lindenbaum» está refutada; «el WKL»
nombra sólo la FUERZA de la completitud sobre RCA₀.
⚠️ Cifras de la auditoría del 2026-09-27, **sin re‑medir** tras el 2026-10-02: ese día salieron las
constantes de `FOL/MetaRules.lean` (borrado) y entraron `derives_soundness` y `ex_elim_refutable`, que
según su módulo llevan `Classical.choice` por los modelos de Tarski en `Prop` (la vía de `derives0_soundness`).

⛔ **Lo que NO hay, y está medido**: la propiedad de disyunción para `Derives₀` (FALSA:
`derives0_no_disjunction_property`, sin `Classical.choice` desde el 2026-09-27; `FOL/Inconsistencia.lean`
§2); un testigo de los enunciados de las cuatro meta‑reglas borradas (`ImpIntro`, `Raa`, `OrElim`,
`ExElim`, refutados sin postularlos en §3: `imp_intro_refutable`, `raa_refutable` y `or_elim_refutable`
en `[propext, Quot.sound]`, `ex_elim_refutable` —con un modelo de dos puntos— en `[propext,
Classical.choice, Quot.sound]`; no se pueden volver a postular sin hacer inconsistente a Lean); LS↑ a
cardinal arbitrario (no está en el árbol: con `List Char` —`String` hasta el 2026-10-05— sólo hay ℵ₀ constantes y la 2ª entrega de `ModelG`
está cerrada); y una instancia de `TheoryFramework` sobre `Derives` (`folSystem` se retiró el
2026-09-23, cuando su solidez se tenía por falsa —con `raa` postulado, cualquier testigo suyo daba `False`—; desde el 2026-10-02 `derives_soundness` la
haría posible, pero no se ha declarado: la que hay es la de `Derives₀`, `fol0System`, desde el
2026-09-27). Hasta el 2026-10-02 este párrafo abría con «la solidez de `Derives` (FALSA con
`MetaRules`: `inconsistencia_de_cualquier_solidez`)»: lo falso eran las meta‑reglas, y aquel teorema se
borró con ellas (ADR‑115 de RPP): su enunciado era falso (también entonces) y sólo se «demostraba» con `raa`. Lo que falta: **`NEXT-STEPS.md`**.

✅ **Deuda saldada el 2026-10-03: cinco módulos 🧊 CONGELADOS decían lo contrario.** Eran FALSOS
—ya al escribirse: lo falso era `raa`— y el borrado de `FOL/MetaRules.lean` los dejó a la vista: `FOL/Soundness0.lean` («la solidez de `Derives` es
FALSA», con la causa en M‑11, y «`Derives` es sintácticamente completo» por `raa`), `FOL/Canonical0.lean`
(«sobre `Derives` no puede haberlas: su solidez es FALSA»), `FOL/Compacity0.lean` («la solidez de
`Derives` es falsa (M‑11)»), `FOL/Rename.lean` («sobre `Derives` es ilegítimo (M‑11: cuatro axiomas lo
habitan)») y `TheoryFramework/Instances/FOL.lean` («`Derives` sigue SIN instancia, y es correcto: su
solidez es falsa»). El propietario autorizó el `thaw`: se corrigieron sólo sus comentarios (código
idéntico a HEAD) y se volvieron a congelar en el mismo ciclo. Registro por línea: `NEXT-STEPS.md`.

---

## ⚠️ HISTÓRICO — de aquí al final, el documento de 2026-05-16 sin reescribir

## Executive Summary

| Metric | Value |
|--------|-------|
| Lean libraries (`lean_lib`) | 4 |
| Total modules | ~43 |
| Modules with 0 sorry | ~42 / ~43 |
| Total sorries | **0** — ⚠️ pero el de `Completeness` se sustituyó por 5 `axiom`, hoy **1** (el 2026‑09‑13 cayeron cuatro: la enumeración y las dos congruencias) |
| Build status | ✅ Passing (all 4 libs) |
| Lean version | v4.28.0 |
| Naming convention | Mathlib-style (see NAMING-CONVENTIONS.md) |

---

## Libraries

### `FOL` — Lógica de Primer Orden con Igualdad (FOL^=)

| Module | Theorems | Sorry | Status |
|--------|----------|-------|--------|
| `Prelim.lean` | 5 | 0 | ✅ Complete |
| `FOL.lean` | 0 | 0 | ✅ Complete |
| `Tactics.lean` | 0 | 0 | ✅ Complete |
| `Deduction.lean` | 1 | 0 | ✅ Complete |
| `Semantics.lean` | 13 | 0 | ✅ Complete |
| ~~`Soundness.lean`~~ | — | — | ⛔ **CUARENTENA** — su teorema se tuvo por FALSO: con `raa` postulado, cualquier testigo suyo daba `False`. ✏️ Desde el 2026-10-02 (`FOL/MetaRules.lean` borrado, ADR‑115 de RPP) su enunciado es un teorema, `derives_soundness`: lo falso era `raa` |
| `Completeness.lean` | 22 | 0 | ⚠️ **1 `axiom`** — eran 5 (ver `AXIOMS.md`) |
| ~~`Compacity.lean`~~ | — | — | ⛔ **CUARENTENA — vacuo** |
| `Theorems/Impl.lean` | 4 | 0 | ✅ Complete |
| `Theorems/Neg.lean` | 5 | 0 | ✅ Complete |
| `Theorems/Derived.lean` | 17 | 0 | ✅ Complete |
| `Theorems/Quantifiers.lean` | 10 | 0 | ✅ Complete |
| `Theorems/Eq.lean` | ~3 | 0 | ✅ Complete |

> El `sorry` en `Completeness.lean` corresponde al caso de igualdad en la construcción de Henkin (modelo cociente para `Formula.eq`). Es matemáticamente correcto pero formalmente pendiente.

### `FOLPure` — Lógica de Primer Orden sin Igualdad

| Module | Sorry | Status |
|--------|-------|--------|
| `FOL.lean`, `Tactics.lean`, `Deduction.lean` | 0 | ✅ |
| `Semantics.lean`, `Soundness.lean`, `Completeness.lean` | 0 | ✅ |
| `Classical.lean`, `Compacity.lean` | 0 | ✅ |
| `Theorems/Impl.lean`, `Neg.lean`, `Derived.lean`, `Quantifiers.lean` | 0 | ✅ |

⚠️ **0 sorries — pero eso NO es «demostrado»**: ver `AXIOMS.md`.

### `PropLogic` — Lógica Proposicional (subconjunto sin cuantificadores)

| Module | Sorry | Status |
|--------|-------|--------|
| `PL.lean`, `Tactics.lean`, `Deduction.lean` | 0 | ✅ |
| `Semantics.lean`, `Soundness.lean`, `Completeness.lean` | 0 | ✅ |
| `Classical.lean`, `Compacity.lean` | 0 | ✅ |
| `Theorems/Impl.lean`, `Neg.lean`, `Derived.lean` | 0 | ✅ |

**0 sorries.**

### `TheoryFramework` — Marco Genérico para Teorías

Capa de abstracción (`class LogicSystem`) sobre las tres lógicas base.

| Module | Sorry | Status |
|--------|-------|--------|
| `Logic.lean` | 0 | ✅ |
| `Theory.lean` | 0 | ✅ |
| `Properties.lean` | 0 | ✅ |
| `Relations.lean` | 0 | ✅ |
| `MetaTheorems.lean` | 0 | ✅ |
| `Instances/PropLogic.lean` | 0 | ✅ |
| `Instances/FOLPure.lean` | 0 | ✅ |
| `Instances/FOL.lean` | 1 (heredado) | ⚠️ |

**0 sorries propios.** La instancia `FOL` hereda el sorry de `FOL.Completeness`.

---

## Recent Achievements

- **FOL^= completo** (Fases 1–6): sintaxis De Bruijn, deducción natural, corrección, completitud de Gödel con modelo cociente, compacidad.
- **FOLPure añadida**: versión sin igualdad, 0 sorries, Completitud y Compacidad totales.
- **PropLogic añadida**: subconjunto proposicional, 0 sorries, mismo stack metamatemático.
- **TheoryFramework**: typeclass `LogicSystem (F : Type)` que unifica las tres lógicas. Metateorémas genéricos (monotonía, corrección↔completitud lifted, inconsistencia upward, equivalencia conservativa).

---

## Pending Work

- [ ] **Fase 7**: Proyecto `ROBINSON_PlusPlus` — Axiomas de Peano sobre `FOLPure`/`FOL`.
- [ ] **Fase 7**: Función de Cantor, codificación de tuplas y listas.
- [ ] **Fase 8**: Cerrar el sorry de igualdad en `FOL/Completeness.lean` con el modelo cociente completo.
- [ ] **Fase 8**: Añadir teorías concretas usando `TheoryFramework` (ej. teoría de grupos, teoría de orden).

---

## Architecture

```
repo/
├── FOL/                     # FOL^= (con igualdad)
│   ├── FOL.lean             # Sintaxis + Derives (incl. eq, refl, subst)
│   ├── Tactics.lean
│   ├── Deduction.lean
│   ├── Semantics.lean
│   ├── Soundness.lean
│   ├── Completeness.lean    # ⚠️ hoy en `cuarentena/`: cero sorry y un postulado
│   │                        #    (`henkin_extension_lemma`) — histórico este árbol
│   ├── Compacity.lean
│   └── Theorems/
├── FOLPure/                 # FOL pura (sin igualdad) — 0 sorries
│   └── [misma estructura]
├── PropLogic/               # Lógica proposicional — 0 sorries
│   └── [estructura análoga, sin Quantifiers]
├── TheoryFramework/         # Marco genérico de teorías
│   ├── Logic.lean           # class LogicSystem
│   ├── Theory.lean          # structure Theory
│   ├── Properties.lean      # IsConsistent, IsComplete, ...
│   ├── Relations.lean       # LE, TheoryExtension, TheoryEquivalent, ...
│   ├── MetaTheorems.lean    # proves_iff_models, monotonía, ...
│   └── Instances/
│       ├── PropLogic.lean
│       ├── FOLPure.lean
│       └── FOL.lean
├── FOL.lean                 # Barrel FOL^=
├── FOLPure.lean             # Barrel FOLPure
├── PropLogic.lean           # Barrel PropLogic
└── TheoryFramework.lean     # Barrel TheoryFramework (sin instancias)
```

---

## Development Phases

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Fundamentos Lógicos (Deducción Natural) | ✅ Complete |
| 2 | Primeros Teoremas (Impl, Neg) | ✅ Complete |
| 3 | Conectivos Derivados y Cuantificadores | ✅ Complete |
| 4 | Automatización y Tácticas | ✅ Complete |
| 5 | Metamatemática (Deducción, Corrección, Completitud) | ✅ Complete |
| 6 | FOL con Igualdad (FOL^=) | ⚠️ **NO completa** — ver el aviso de estado de arriba: cero sorry, pero la completitud se apoya en un postulado en `cuarentena/` |
| 6b | FOLPure (sin igualdad, 0 sorries) | ✅ Complete |
| 6c | PropLogic (subconjunto proposicional) | ✅ Complete |
| 6d | TheoryFramework (marco genérico) | ✅ Complete |
| 7 | ROBINSON_PlusPlus (Aritmética sobre FOL) | 🔄 Pendiente |
| 8 | Cerrar sorry FOL^= + teorías concretas | 🔄 Pendiente |

> Ver [NEXT-STEPS.md](NEXT-STEPS.md) y [PLANNING.md](PLANNING.md) para el detalle.

---

**Author**: Julián Calderón Almendros
*Cuerpo histórico de 2026-05-16; la marca vigente es la de la cabecera.*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
