# Current Project Status — FOL Ecosystem

> # ⛔⛔ AVISO DE ESTADO — 2026-09-26 (reescrito: el del 2026-09-12 había quedado FALSO). LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | 🏁 **Sí, sobre `Derives₀`** (2026-09-14): `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` (`FOL/Soundness0.lean`), y con ella `derives0_consistent`. ⛔ La de **`Derives`** sigue siendo **FALSA** en presencia de `FOL/MetaRules.lean`: `FOL/Inconsistencia.lean`, hoy **en el build** |
> | «Compacidad» ✅ | 🏁 `compactness`, `loewenheim_skolem_down` y el modelo infinito `infinite_model_of_large`, en `FOL/Compacity0.lean`. El `Compacity.lean` vacuo **se borró** el 2026-09-23 |
> | «Completitud» ✅ / «1 sorry» | 🏁 `completeness₀ : Γ ⊨ f → Γ ⊢₀ f` (`FOL/Canonical0.lean`, 2026-09-16), con **cero axiomas del proyecto**: `[propext, Classical.choice, Quot.sound]`, y ese `Classical.choice` es el WKL de `Lindenbaum0` (ADR-041). `Completeness.lean` y su último postulado, `henkin_extension_lemma`, **se borraron** el 2026-09-23. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **4 `axiom`**, los de `MetaRules` que el kernel obliga, y ninguno más fuera de las librerías retiradas · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026-09-12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Los seis teoremas del cierre (T1 a T6, 2026-09-23 y 2026-09-26) están en el árbol**, sobre `Derives₀`; el catálogo, en `CURRENT-STATUS-PROJECT.md` («Estado vigente») y `REFERENCE.md` §6. ⛔ Y lo que NO hay: la propiedad de disyunción para `Derives₀` es **FALSA** (`derives0_no_disjunction_property`).
> (Este aviso decía que «lo único sólido MEDIDO» era `prf0_soundness` (hoy `prfI_soundness`), en RPP: dejó de serlo el 2026-09-14.)
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md`

**Last updated:** 2026-09-26 — D2/D4/D5/D6/D7 ejecutadas: refactor `absTerm'` (D5), regla de subíndices y sus renombres (T1 = `model_existence_iff₀`, T2 = `IsMemComplete`, `compactness`), vía de `ModelG` y migración a `List Char` CERRADAS, higiene de docstrings. Antes, 🗑️ D1: `Tactics2.lean` borrado ⇒ **53 módulos activos**. Antes, el mismo día: ⭐ entran T4 (`Hauptsatz0` §9) y T6 (`Compacity0` §3): **los seis teoremas del cierre están en el árbol**; aviso de cabecera reescrito (el del 2026-09-12 negaba Corrección, Completitud y Compacidad) y sección «Estado vigente» nueva. Antes (2026-09-23): entra `FOL/Complexity.lean` (encargo PeanoRF §3) y la cifra canónica pasa a **54 módulos**. ⚠️ La marca decía **2026-09-18 15:40** y `[E]` la cazó el mismo día que se movió el cuerpo — que es para lo que está el control.
**Author**: Julián Calderón Almendros

> 📐 **CIFRAS CANÓNICAS — medidas, no copiadas** (`bash check-doc-sync.bash`, 2026-09-26):
> **53 módulos activos** (`FOL/` 42 + `FOL/Theorems/` 5 + `TheoryFramework/` 6) ·
> **0 módulos en `cuarentena/`** · **4 `axiom` de Lean** en el build ·
> **0 sorry**.
>
> ⚠️ Esta línea existe para que el control tenga **contra qué comparar**: sin ella,
> `check-doc-sync.bash` calcula las cifras del árbol, no encuentra dónde contrastarlas e imprime
> «control VACÍO» — y sale **verde sin haber comprobado nada**. 🔑 *Un control sin nada que
> contrastar no aprueba: se abstiene, y la abstención se lee como aprobado.*
>
> ⛔ La cifra de **jobs** NO se publica aquí: FOL no se construye desde FOL (M‑3), y quien la
> mide es `../ROBINSON_PlusPlus`: `lake build "@FOL/FOL" "@FOL/TheoryFramework"` desde su raíz (⚠️ el `lake build` a secas de RPP sólo compila lo que RPP importa, y deja fuera la capa `₀`).

---

## 🏁 Estado vigente — 2026-09-26

El sujeto de la metateoría es **`Derives₀`** (`FOL/Derives0.lean`): los constructores de `Derives`
sin la ω-regla y sin los habitantes-axioma de `MetaRules`, así que se puede inducir sobre él. Todo lo
de esta tabla compila sin `sorry` y **sin axiomas del proyecto**; los footprints son los de
`#print axioms`, vigilados por `../ROBINSON_PlusPlus/check-footprints.bash`.

| resultado | declaración | módulo | footprint |
|---|---|---|---|
| Corrección, consistencia | `derives0_soundness`, `derives0_consistent` | `Soundness0` | `[propext, Classical.choice, Quot.sound]` |
| Consistencia finitaria | `derives0_consistent_fin` | `Finitary0` | `[propext, Quot.sound]` |
| Completitud | `completeness₀`, `derives0_complete_iff` | `Canonical0` | `[propext, Classical.choice, Quot.sound]` |
| **T1** · existencia de modelo | `model_existence_iff₀` | `Compacity0` | ídem |
| **T2** · el maximal consistente decide cada fórmula (por pertenencia; ⚠️ aún no la «teoría completa» sobre sentencias) | `max_cons_neg`, `IsMemComplete`, `max_cons_complete` | `Canonical0` | ídem |
| Compacidad, LS↓ | `compactness`, `loewenheim_skolem_down` | `Compacity0` | ídem |
| **T6** · modelo numerable e infinito | `infinite_model_of_large` | `Compacity0` §3 | ídem |
| Hauptsatz, Herbrand | `hauptsatz`, `cut_elimination`, `herbrand` | `Hauptsatz0` | `[propext, Quot.sound]` |
| **T4** · fragmento sin cuantificadores | `derives0_qf_iff` (caracteriza, NO decide) | `Hauptsatz0` §9 | `[propext, Quot.sound]` |
| **T3** · decisor proposicional | `ptautCheck_iff`, `instDecidablePTaut` | `Herbrand0` | `[propext]` (`ptautCheck_iff`) |
| **T5** · inversión de `LK₀` | las nueve proposicionales, `inv_allR` e `inv_exL` | `Inversion0` | `[propext, Quot.sound]` |
| Craig | `craig`, `craig_impl` | `Craig0` | `[propext, Quot.sound]` |
| Skolem bajo prefijo | `skolem_conservative_n` | `SkolemN0` | `[propext, Classical.choice, Quot.sound]` |

⛔ **Lo que NO hay, y está medido**: la solidez de `Derives` (FALSA con `MetaRules`:
`inconsistencia_de_cualquier_solidez`); la propiedad de disyunción para `Derives₀` (FALSA:
`derives0_no_disjunction_property`; las dos en `FOL/Inconsistencia.lean`); LS↑ a cardinal arbitrario
(no está en el árbol: con `String` sólo hay ℵ₀ constantes y la 2ª entrega de `ModelG` está cerrada); y una instancia de `TheoryFramework`
(`folSystem` retirada el 2026-09-23). Lo que falta: **`NEXT-STEPS.md`**.

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
| ~~`Soundness.lean`~~ | — | — | ⛔ **CUARENTENA — su teorema es FALSO** |
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
