# Consumidores de FOL — registro y política

**Last updated:** 2026-10-28 — T50 (ADR‑214 de RPP): el registro, nuevo; los cuatro consumidores viejos, ARCHIVADOS por
decisión del propietario, cada uno fijado al commit de FOL que le corresponde.

Un consumidor es un proyecto que hace `require FOL from "../FOL"` (por RUTA: compila el árbol de trabajo de FOL, no
una versión fijada). Medido el 2026‑10‑28 en el disco y en git de cada uno.

## Política

1. **Por ruta, el mismo toolchain** (M‑1 de `DECISIONS.md`): un consumidor por ruta construye FOL en el `.lake` de
   FOL; con otro toolchain lo mezcla. Un bump mueve el par —FOL y RPP— a la vez; un consumidor vivo, también.
2. **FOL no promete compatibilidad.** Un cambio que rompe a un consumidor vivo lo dice su ADR, con la lista de lo que
   rompe.
3. **Archivado** quiere decir: no se construye contra el `master` de FOL, y queda fijado al commit de FOL que le
   corresponde (el último de `master` anterior a su último commit). Para revivirlo, cambiar su `require` por
   `require FOL from git "https://github.com/julian1c2a/FOL" @ "<sha>"` con ese sha, o portarlo a la versión de hoy.
4. **El consumidor vivo es ROBINSON_PlusPlus**: su CI construye contra el `master` de FOL a propósito (ADR‑073 de RPP),
   y registra el par en «../ROBINSON_PlusPlus/doc/control/fol-sha.txt».

## Registro

| consumidor | toolchain | último commit | FOL fijado | estado |
|---|---|---|---|---|
| ROBINSON_PlusPlus | v4.35.0 | — | el `master` (el par, en su «doc/control/fol-sha.txt») | ✅ vivo |
| PeanoRF («../Peano-from-ROB-n-FOL») | v4.31.0 | `70d79fc`, 2026‑09‑28 | `b4db33d` (2026‑09‑28) | ⛔ bloqueado por el propietario (sólo lectura); no compila contra el FOL de hoy: la lista de lo que debe adaptar, en «../ROBINSON_PlusPlus/doc/registro/2026-10-28-t50/peanorf.txt» |
| FOL_Compiler | v4.30.0 | `3c94524`, 2026‑06‑05 | `4b262bf` (2026‑05‑28) | 🗄️ archivado |
| FOL_CompStructs | v4.29.1 | `db17ff5`, 2026‑06‑11 (sin remoto) | `a16a111` (2026‑06‑09) | 🗄️ archivado |
| Lean4_vs_PureLogic (remoto: DeepArith) | v4.29.0 | `ef3a407`, 2026‑06‑27 | `cca78ac` (2026‑06‑24) | 🗄️ archivado |
| Ordinals_Induction_Recursion | v4.30.0 | `83a92e3`, 2026‑06‑09 | `a16a111` (2026‑06‑09) | 🗄️ archivado |

El «FOL fijado» se calculó con `git rev-list -1 --before=<fecha del último commit del consumidor> master` en FOL. Los
cuatro archivados siguen con su `require` por ruta en su propio repositorio: no se han tocado. Construir uno de ellos
hoy escribiría en el `.lake` de FOL con otro toolchain; no se hace (política, 1 y 3).
