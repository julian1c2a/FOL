# Current Project Status — FOL Ecosystem

> # ⛔⛔ AVISO DE ESTADO — 2026‑09‑12. LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | ⛔ **NO HAY teorema de Corrección.** `soundness` es **FALSO** en presencia de `FOL/MetaRules.lean`: cualquier testigo suyo demuestra `False` sin hipótesis (`cuarentena/Inconsistencia.lean`, compilado). Está en **`cuarentena/`** |
> | «Compacidad» ✅ | ⛔ Su prueba pasaba por `soundness` ⇒ **vacua**. En `cuarentena/` |
> | «Completitud» ✅ / «1 sorry» | ⚠️ **0 `sorry`, pero UN SOLO `axiom`**: el `sorry` se sustituyó por CINCO postulados en un commit titulado «100 % sorry‑free»; el 2026‑09‑13 cayeron CUATRO (la enumeración de fórmulas y las dos congruencias de la igualdad) y queda **UNO**: `henkin_extension_lemma`. ⭐ `truth_lemma` y el modelo canónico son ya **net‑0 puros**; ⚠️ pero la completitud **sigue sin estar demostrada** en el sentido que aquí se publica. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **4 `axiom`** en el build (+1 en `cuarentena/Completeness.lean`) · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026‑09‑12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Lo único sólido MEDIDO del ecosistema** es `prf0_soundness` sobre `Prf₀`
> (`../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`), net‑0 puro.
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md`

**Last updated:** 2026-09-18 15:40
**Author**: Julián Calderón Almendros

> 📐 **CIFRAS CANÓNICAS — medidas, no copiadas** (`bash check-doc-sync.bash`, 2026‑09‑23):
> **54 módulos activos** (`FOL/` 42 + `FOL/Theorems/` 6 + `TheoryFramework/` 6) ·
> **5 módulos en `cuarentena/`** · **4 `axiom` de Lean** en el build (+1 en `cuarentena/`) ·
> **0 sorry**.
>
> ⚠️ Esta línea existe para que el control tenga **contra qué comparar**: sin ella,
> `check-doc-sync.bash` calcula las cifras del árbol, no encuentra dónde contrastarlas e imprime
> «control VACÍO» — y sale **verde sin haber comprobado nada**. 🔑 *Un control sin nada que
> contrastar no aprueba: se abstiene, y la abstención se lee como aprobado.*
>
> ⛔ La cifra de **jobs** NO se publica aquí: FOL no se construye desde FOL (M‑3), y quien la
> mide es `../ROBINSON_PlusPlus` (`lake build FOL TheoryFramework`).

---

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
*Last updated: 2026-05-16*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
