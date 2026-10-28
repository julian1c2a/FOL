# Consumidores de FOL — registro y política

**Last updated:** 2026-10-28 — T51 (ADR‑218 de RPP): la entrega X1 de PeanoRF y «sym!», en FOL (su fila). Antes, el mismo día — ADR‑216 de RPP: los cuatro consumidores viejos, FIJADOS en su propio `lakefile.lean` al
commit de FOL que les corresponde, y los tres que tienen remoto, ARCHIVADOS también en GitHub (decisión del propietario).
Antes, el mismo día — T50 (ADR‑214 de RPP): el registro, nuevo; los cuatro, archivados por decisión del propietario.

Un consumidor es un proyecto que hace `require FOL from "../FOL"` (por RUTA: compila el árbol de trabajo de FOL, no
una versión fijada). Medido el 2026‑10‑28 en el disco y en git de cada uno.

## Política

1. **Por ruta, el mismo toolchain** (M‑1 de `DECISIONS.md`): un consumidor por ruta construye FOL en el `.lake` de
   FOL; con otro toolchain lo mezcla. Un bump mueve el par —FOL y RPP— a la vez; un consumidor vivo, también.
2. **FOL no promete compatibilidad.** Un cambio que rompe a un consumidor vivo lo dice su ADR, con la lista de lo que
   rompe.
3. **Archivado** quiere decir: no se construye contra el `master` de FOL, y queda fijado al commit de FOL que le
   corresponde (el último de `master` anterior a su último commit), en su propio repositorio:
   `require FOL from git "https://github.com/julian1c2a/FOL" @ "<sha>"` y la entrada de git en su `lake-manifest.json`.
   Así se construye con su FOL, clonado en su `.lake`, sin tocar el de FOL. Para revivirlo: desarchivarlo en GitHub y
   portarlo a la versión de hoy (el mismo toolchain, política 1).
4. **El consumidor vivo es ROBINSON_PlusPlus**: su CI construye contra el `master` de FOL a propósito (ADR‑073 de RPP),
   y registra el par en «../ROBINSON_PlusPlus/doc/control/fol-sha.txt».

## Registro

| consumidor | toolchain | último commit | FOL fijado | estado |
|---|---|---|---|---|
| ROBINSON_PlusPlus | v4.35.0 | — | el `master` (el par, en su «doc/control/fol-sha.txt») | ✅ vivo |
| PeanoRF («../Peano-from-ROB-n-FOL») | v4.31.0 | `70d79fc`, 2026‑09‑28 | `b4db33d` (2026‑09‑28) | ⛔ bloqueado por el propietario (sólo lectura); no compila contra el FOL de hoy: la lista de lo que debe adaptar, en «../ROBINSON_PlusPlus/doc/registro/2026-10-28-t50/peanorf.txt». ✏️ 2026‑10‑28 (T51, ADR‑218 de RPP): su entrega X1 ya está en FOL (`FOL/Calculus/`), y «sym!» también (`FOL/SymLit.lean`): al adaptarse, los importa en vez de llevarlos |
| FOL_Compiler | v4.30.0 | `3c94524`, 2026‑06‑05 | `4b262bf` (2026‑05‑28) | 🗄️ archivado: fijado en `b67e3cb`; archivado en GitHub |
| FOL_CompStructs | v4.29.1 | `db17ff5`, 2026‑06‑11 (sin remoto) | `a16a111` (2026‑06‑09) | 🗄️ archivado: fijado en `ae959ec`, sólo local (no hay repositorio en GitHub) |
| Lean4_vs_PureLogic (remoto: DeepArith) | v4.29.0 | `ef3a407`, 2026‑06‑27 | `cca78ac` (2026‑06‑24) | 🗄️ archivado: fijado en `a5afe48`; archivado en GitHub |
| Ordinals_Induction_Recursion | v4.30.0 | `83a92e3`, 2026‑06‑09 | `a16a111` (2026‑06‑09) | 🗄️ archivado: fijado en `1b0c294`; archivado en GitHub |

El «FOL fijado» se calculó con `git rev-list -1 --before=<fecha del último commit del consumidor> master` en FOL. El
2026‑10‑28 (ADR‑216 de RPP) cada uno pasó de la ruta a ese commit en un commit propio (la columna «estado»): su
`lakefile.lean`, su `lake-manifest.json` y, si lo tiene, un aviso en su README. Comprobado con `lake` en el toolchain de
cada uno, sobre una copia: clona FOL en esa revisión (y Ordinals, también sus otras dos dependencias) y no pide
`lake update`; el control negativo —el manifiesto con otra revisión— sí lo pide. No se han reconstruido. ⚠️ El push de
Ordinals lanzó su CI, que salió verde con «Build completed successfully (0 jobs)»: su `lean_lib` no es
`@[default_target]`, así que `lake build` no construye nada, y ese verde no comprueba nada. Lo que había sin commit en sus
árboles se ha dejado como estaba.
