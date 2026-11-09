# Decisiones de Diseño — FOL

**Last updated:** 2026-11-09 — ADR‑262 de RPP: en los ADR, que son registro, las citas de lo retirado o borrado (las meta‑reglas y su módulo, las tres sub‑librerías, los dos scripts de T15, los módulos sin barril de la nota de ADR‑010), con su marcador detrás; lo que no es un nombre del entorno (el FirstOrder de Mathlib, los ejemplos addZ/mulQ, las anotaciones de ADR‑008), en texto plano; y una fecha de la nota de ADR‑010, corregida. Antes, 2026-11-05 — M‑3, la M‑11 de RPP copiada (FOL0912:R‑9, ADR‑257 de RPP). Antes, 2026-11-02 — T56 (ADR‑245 de RPP): el cuerpo, revisado contra el árbol; ADR‑004, 005, 006, 007, 008 y 010, con su estado de hoy (las sub-librerías retiradas el 2026‑09‑12, la propuesta nunca hecha, las anotaciones en desuso); ADR‑003, con lo que hay hoy; el aviso de fichero dormido, con el número de hoy. Antes, 2026-10-28 — §MANDATORIES: M-1, el mismo toolchain que RPP (T16, ADR-205 de RPP), y M-2, ramas, stash y worktrees (T79, ADR-204 de RPP). Antes, 2026-07-12
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero reemplaza la versión anterior, que era la plantilla genérica de
> `lean4-project-template` sin adaptar (título "ProjectName" literal, `ADR-001` con la
> justificación sin rellenar) — no había contenido real que preservar. Ver
> `AI-GUIDE.md` para lo universal; aquí solo lo específico de FOL.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto)

| # | MANDATORY | Origen | Verificación |
|---|---|---|---|
| **M-1** | ⛔ **FOL, ROBINSON_PlusPlus y todo consumidor de FOL por ruta, en el MISMO toolchain: un bump mueve el par a la vez** (FOL primero: M‑12 de RPP). Con el mismo toolchain da lo mismo construir FOL desde aquí o desde la raíz de RPP (MEDIDO en un par clonado: código 0, ningún módulo reconstruido, ningún «incompatible header»; `doc/registro/2026-10-28-t16/` de RPP); con toolchains distintos, los dos escribirían en el mismo .lake de FOL | T16; ADR‑202 y ADR‑205 de RPP (es su M‑3, reescrita) | la CI compara los dos toolchains (el paso «El mismo toolchain en FOL y en RPP» de `.github/workflows/build.yml`); en local, `guarda-toolchain.bash` antes de cada lake del `Makefile` y de `check-axioms.bash`; el bump, sólo desde RPP (el `update-toolchain.bash` de aquí está retirado) |
| **M-2** | **Ramas, stash y worktrees.** Una rama se borra, local y remota, en cuanto su punta está en `master`; una rama que se abandona sin fusionar se archiva antes en una etiqueta anotada `archivo/<rama>-<fecha de su último commit>`, subida, y después se borra, cada paso en su propia orden; un stash o un worktree no sobreviven a la sesión que los crea | T79; ADR‑204 de RPP | a mano al cerrar una sesión: `git branch -a --no-merged master`, `git stash list` y `git worktree list` |
| **M-3** | ⛔⛔ **Antes de POSTULAR un `axiom` cuya conclusión es un inductivo (lo HABITA), comprobar que no contradice lo que se demuestra por inducción sobre él.** El recursor cubre a TODO habitante, también a los que fabrica un axioma: un teorema probado por inducción sobre un inductivo habitado es VÁLIDO; lo que puede ser falso es el axioma. Así cayeron los cuatro de FOL/MetaRules.lean, módulo ya borrado (imp_intro, raa, or_elim y ex_elim, retirados): con la solidez, Lean + ellos ⊢ `False` (borrados con el módulo, ADR‑115 de RPP). ⚠️ `#print axioms` es CIEGO a esto. 🔑 Una regla que se quiere añadir a una relación inductiva se añade como CONSTRUCTOR, nunca como `axiom`. Hoy FOL no tiene ningún `axiom`. ✏️ *(2026‑11‑05, FOL0912:R‑9 de la auditoría de FOL, ADR‑257 de RPP: copiada aquí; la regla que gobernaba el defecto más grave de FOL vivía sólo en RPP)* | la M‑11 de `../ROBINSON_PlusPlus/DECISIONS.md` (ADR‑114 §2, ADR‑133 de RPP) | `check-axioms.bash` (cero `axiom`, por entorno) y, sobre los doce estratos de los dos repos, `../ROBINSON_PlusPlus/check-estratos.bash` (ningún `axiom` habita una noción de derivabilidad) |

> **Sobre `Classical.*`:** a diferencia de proyectos hermanos como AczelSetTheory, **FOL no lo prohíbe**; la frontera
> exacta del `Classical.choice`, MEDIDA, está en `AXIOMS.md` §4. *(✏️ 2026‑10‑28, T16: aquí decía «Sin MANDATORIES
> declaradas» y «42 usos verificados en 2026-07-12», una cifra de entonces que nadie re‑ejecuta.)*

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: objetivo educativo — formalizar lógica de primer orden desde cero,
incluyendo su propia infraestructura de sustitución/elevación de De Bruijn, sin
apoyarse en el FirstOrder de Mathlib.

**Consecuencias**: toda la infraestructura necesaria (`ExistsUnique` (borrado el 2026‑05‑05), sustitución,
decidibilidad, etc.) se construye desde cero en cada sub-librería.

---

## ADR-002: `autoImplicit = false`

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

✏️ **Rectificado el 2026-10-05 (ADR‑128 de RPP)**: `moreServerArgs` sólo llega al servidor del EDITOR, así que
`lake build` aceptaba variables implícitas automáticas (medido con un módulo sonda). Hoy la opción es
`leanOptions`, con `autoImplicit` y `relaxedAutoImplicit` a `false`, que vale para el editor y para el build.

**Justificación**: las anotaciones de tipo explícitas evitan problemas accidentales de
polimorfismo de universos y hacen el código más legible y mantenible.

**Consecuencias**: todas las variables deben declararse o anotarse explícitamente.

---

## ADR-003: Sistema de bloqueo de archivos

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: usar `git-lock.bash` + `locked_files.txt`/`frozen_files.txt` + hook
`pre-commit` para prevenir ediciones accidentales de módulos terminados.

**Justificación**: las pruebas de Lean 4 son frágiles — cambios pequeños en módulos
terminados pueden romper pruebas dependientes.

**Consecuencias**: el flujo de trabajo exige bloquear/desbloquear ficheros (ver
`AI-GUIDE.md` §20-21). **Nota de auditoría (2026-07-12)**: `locked_files.txt` llevaba
vacío desde siempre pese a tener módulos "✅ Completos" — el protocolo no se estaba
aplicando en la práctica. Se corrige aquí también un bug real en `git-lock.bash`
(`unlock`/`thaw` no vaciaban la lista al quitar el último fichero, por el exit code 1
de `grep -Fv` cortocircuitando el `&&` previo al `mv`).
✏️ *Nota del 2026-11-02 (T56, ADR‑245 de RPP)*: hoy hay 51 entradas en `locked_files.txt` y 39 en `frozen_files.txt`; el gancho es `.githooks/pre-commit`, versionado y activo por `core.hooksPath` (T14, ADR‑234 de RPP), con su hermano `.githooks/commit-msg`, que exige el ADR de cada thaw; y la CI lo vigila con `check-congelados.bash` y `check-gancho.bash`.

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): la decisión sigue (`NAMING-CONVENTIONS.md`); lo que dice de `MetaRules.lean`, borrado el 2026‑10‑02, es registro

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio.

**Consecuencias**: ver `NAMING-CONVENTIONS.md` para el diccionario completo y las 12
reglas de formación. **Nota**: la antigua "REGLA 13" (sufijos de dominio addZ/mulQ)
no se sigue en este proyecto — los axiomas de `MetaRules.lean` (borrado el 2026‑10‑02)
(`imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim`, retirados todos) usaban nombres descriptivos planos, sin prefijo de
dominio (`TAG_`) ni sufijo de estructura.
✏️ *Nota del 2026-10-02*: `gen` y `dne` (los de MetaRules, borrados con el módulo el 2026-10-02) dejaron de ser axiomas el 2026-09-12 —pasaron a
teoremas que envolvían los constructores `gen_rule` y `dne_rule` (D‑2 de ADR‑028 de RPP)—; los
cuatro restantes, refutables sin usarlos, se borraron con `FOL/MetaRules.lean` el 2026-10-02
(ADR‑115 de RPP), y aquellos dos envoltorios con ellos. Hoy FOL no tiene ningún `axiom`; la
entrada vigente es `NAMING-CONVENTIONS.md` §9.

---

## ADR-005: Namespaces alineados con directorios

**Fecha**: 2026-04-20
**Estado**: Aceptado, con excepciones — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): FOLPure, PropLogic y FOL_poli se retiraron el 2026‑09‑12 (FOL `b97ee6d`; `cuarentena/librerias-retiradas/`). Y la regla no se cumple en todo el árbol: `Theorems/Eq.lean` y `SymClasses.lean` declaran en `FOL`, y los módulos de `Calculus/` en `FOL.Calculus`. El espacio de nombres de cada módulo, el de hoy, lo da la §6 de `REFERENCE.md`, que se genera de las fuentes

**Decisión**: cada subdirectorio corresponde a un sub-namespace:
`FOL/Theorems/Eq.lean` → `namespace FOL.Theorems.Eq` (y análogamente para
`FOLPure`, `PropLogic`, `FOL_poli` (retiradas el 2026‑09‑12), `TheoryFramework`).

**Justificación**: mapeo 1:1 claro entre sistema de ficheros y jerarquía de
namespaces.

**Consecuencias**: `new-module.bash` (retirado el 2026‑10‑18) debe soportar creación en subdirectorios;
`gen-root.bash` (retirado el mismo día) debe escanear recursivamente. Ver ADR-010 sobre la relación entre las
5 sub-librerías.

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: 2026-04-20
**Estado**: Obsoleto en lo que dice de las sub-librerías — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): de las cinco quedan dos (`FOL` y `TheoryFramework`, desde el 2026‑09‑12). `FOL/Theorems/` conserva los cinco módulos del núcleo de `Derives`; la metateoría vive en los `FOL/*0.lean` y en `FOL/Calculus/`, y `TheoryFramework/Instances/` tiene sus dos instancias. El barril de cada subdirectorio, como pedía: `FOL/Core.lean` para el núcleo

**Decisión**: cada sub-librería (`FOL`, `FOLPure`, `PropLogic`, `FOL_poli` [estas tres, retiradas el 2026‑09‑12],
`TheoryFramework`) agrupa sus teoremas derivados en un subdirectorio `Theorems/`
(o `Instances/` para `TheoryFramework`).

**Justificación**: separar el núcleo (sintaxis, semántica, deducción) de los
teoremas derivados facilita localizar cada pieza.

**Consecuencias**: cada subdirectorio con 2+ módulos requiere un barrel
(`AI-GUIDE.md` §18).

---

> ## ⛔⛔ ESTE FICHERO ESTÁ DORMIDO DESDE ADR‑010 — aviso añadido el 2026‑09‑23
>
> **El log de decisiones VIVO de FOL es `../ROBINSON_PlusPlus/DECISIONS.md`**, que iba por
> ADR‑098 al escribir este aviso (por ADR‑115 el 2026‑10‑02; por ADR‑245 el 2026‑11‑02). Todas las decisiones sobre este repositorio desde el 2026‑09‑12 están ahí — entre
> ellas ADR‑047 (la corrección de PeanoRF), ADR‑061 (`check-doc-sync` adoptado), ADR‑065,
> ADR‑072 (el control `[E]` rearmado y `[G.1]`), ADR‑083 (`ModelG`) y ADR‑098 (el cierre); y,
> el 2026‑10‑02, ADR‑114 (la auditoría de la base) y ADR‑115 (la capa `⊢` retirada de RPP y,
> con ella, `FOL/MetaRules.lean` borrado: sus cuatro `axiom` eran refutables).
>
> ⚠️ **Y hay una colisión de numeración con PeanoRF**: los dos repositorios tienen un
> ADR‑047 y los dos son sobre esta misma relación. Prefijo obligatorio en los dos sentidos:
> **`RPP‑047`** / **`PRF‑047`**.
>
> 🔑 *Un log de decisiones que nadie escribe no es un log vacío: es un puntero falso.*
> Es la misma causa que congeló el `CHANGELOG` y con él el control `[E]` (ADR‑072).

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: 2026-04-20
**Estado**: Obsoleto — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): nunca se implementó, y tres de las cuatro sub-librerías para las que se proponía se retiraron el 2026‑09‑12. `REFERENCE.md` documenta las dos `lean_lib` vivas; su §6, el catálogo de lo que exporta cada módulo, se genera de las fuentes (`gen-reference.py`, con `--check` en la CI)

**Decisión**: `REFERENCE.md` debería ser solo el índice raíz, con el detalle de cada
sub-librería en nodos temáticos bajo `doc/REFERENCE-{tema}.md`.

**Justificación**: `REFERENCE.md` actual (617 líneas) solo documenta la librería
`FOL`; `FOLPure` (retirada), `PropLogic` (retirada), `TheoryFramework` y `FOL_poli` (retirada) no tienen sección propia
pese a estar "✅ Completos". No existe todavía directorio `doc/` en este proyecto.

**Consecuencias**: **pendiente de implementar** — crear `doc/REFERENCE-FOLPure.md`, `doc/REFERENCE-PropLogic.md`, `doc/REFERENCE-TheoryFramework.md` y `doc/REFERENCE-FOL_poli.md`,
y reducir `REFERENCE.md` a índice con enlaces. Ver
DEPENDENCIES.md para el estado real de las 5 sub-librerías mientras tanto.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: 2026-04-20
**Estado**: En desuso — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): las llevan sólo las entradas de §3 de los módulos de abril (y las del apéndice R de `REFERENCE.md`); ningún módulo de la capa ₀ ni posterior las tiene, y nada las lee

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones @axiom_system y
@importance.

**Justificación**: ayuda a los asistentes de IA a priorizar qué módulos/teoremas
cargar como contexto.

**Consecuencias**: las anotaciones deben mantenerse al actualizar módulos.

---

## ADR-009: `NAMING-CONVENTIONS.md` como fichero separado

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: las convenciones de nombres viven en un `NAMING-CONVENTIONS.md`
dedicado, con un resumen en `AI-GUIDE.md`.

**Justificación**: el diccionario completo con 12 reglas es demasiado extenso para
`AI-GUIDE.md` solo.

**Consecuencias**: si divergen, `NAMING-CONVENTIONS.md` es autoritativo.

---

## ADR-010: Cinco sub-librerías independientes, no una jerarquía de extensión

**Fecha**: 2026-07-12
**Estado**: Obsoleto — ✏️ 2026‑11‑02 (T56, ADR‑245 de RPP): desde el 2026‑09‑12 (FOL `b97ee6d`) el lakefile declara dos `lean_lib`, `FOL` y `TheoryFramework`; FOLPure, PropLogic y FOL_poli están en `cuarentena/librerias-retiradas/`, fuera del lakefile (`cuarentena/README.md` §7: dos de ellas eran inconsistentes). Lo de abajo es registro de la arquitectura de julio. *(Era: «Aceptado (decisión retroactiva — documenta una arquitectura ya existente)».)*

**Contexto**: el proyecto declara 5 `lean_lib` en `lakefile.lean`: `FOL` (con
igualdad), `FOLPure` (retirada; sin igualdad), `PropLogic` (retirada; proposicional, sin cuantificadores
ni términos), `FOL_poli` (retirada; variante paralela de `FOL`) y `TheoryFramework` (marco
abstracto sobre cualquier `LogicSystem`).

**Decisión**: `FOL`, `FOLPure`, `PropLogic` y `FOL_poli` [estas tres, retiradas el 2026‑09‑12] son implementaciones
paralelas independientes (cada una define su propio `Formula`, `Term`, etc. a nivel
raíz), no una jerarquía donde una extienda a otra. `TheoryFramework` es agnóstico y
se instancia por separado sobre cada una vía `TheoryFramework/Instances/*.lean`.

**Justificación**: `TheoryFramework.lean` (el barrel raíz) documenta explícitamente
por qué **no** importa `Instances/`: `FOLPure` (retirada) y `FOL` definen ambas un `Formula` a
nivel raíz, y hacerlo produciría colisión de nombres. Mantener las instancias como
imports opt-in (`import TheoryFramework.Instances.FOL`, etc.) evita el conflicto sin
sacrificar la genericidad del marco.

**Consecuencias**: quien quiera usar `TheoryFramework` sobre una lógica concreta debe
importar explícitamente la instancia correspondiente, nunca `TheoryFramework` +
`Instances/` a la vez para dos lógicas distintas en el mismo fichero.

**Nota de auditoría (2026-07-12)**: `FOL.lean` y `FOL_poli.lean` —el segundo, retirado el 2026‑09‑12— (los barrels raíz de
esas dos sub-librerías) no importan actualmente `Classical.lean`, `Tactics2.lean` (hoy borrados o retirados) (o,
en `FOL`, `Theorems.Deduction`/`Theorems.Eq`/`Theorems.Soundness`, hoy borrados el primero y el tercero) — 5 módulos
existentes en disco y no wireados en el barrel de cada una. No está claro si es
intencional (variantes experimentales) o un olvido; **pendiente de decidir y
documentar** en una revisión posterior — no se ha tocado el barrel en esta sesión
para no alterar el comportamiento del build sin confirmación del autor.
✏️ *Nota del 2026-11-02 (T56)*: de aquellos cinco módulos sin barril, `Classical.lean` y `Tactics2.lean` ya no existen (el segundo se borró en D1, 2026‑09‑26, FOL `9804fcd`; ✏️ 2026‑11‑09, ADR‑262 de RPP: aquí decía 2026‑09‑27, el día de las D1–D8 de la auditoría de constructividad), y `Theorems/Eq.lean` entra por `FOL/Core.lean`; desde T15 (ADR‑163 de RPP) los `globs` del lakefile compilan todo el directorio, y [L] de `check-doc-sync.bash` comprueba que todo módulo esté en el cierre de imports de un barril.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
