# Decisiones de Diseño — FOL

**Última actualización:** 2026-07-12
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero reemplaza la versión anterior, que era la plantilla genérica de
> `lean4-project-template` sin adaptar (título "ProjectName" literal, `ADR-001` con la
> justificación sin rellenar) — no había contenido real que preservar. Ver
> `AI-GUIDE.md` para lo universal; aquí solo lo específico de FOL.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto)

**Sin MANDATORIES declaradas** — este proyecto no tiene directivas fundacionales no
negociables más allá de los ADR de abajo. En particular, a diferencia de proyectos
hermanos como AczelSetTheory, **FOL no prohíbe `Classical.*`**: se usa con normalidad
(42 usos verificados en 2026-07-12) en las pruebas de completitud (`Completeness.lean`)
y en los módulos `Classical.lean` de cada sub-librería.

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: objetivo educativo — formalizar lógica de primer orden desde cero,
incluyendo su propia infraestructura de sustitución/elevación de De Bruijn, sin
apoyarse en el `FirstOrder` de Mathlib.

**Consecuencias**: toda la infraestructura necesaria (`ExistsUnique`, sustitución,
decidibilidad, etc.) se construye desde cero en cada sub-librería.

---

## ADR-002: `autoImplicit = false`

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

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

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio.

**Consecuencias**: ver `NAMING-CONVENTIONS.md` para el diccionario completo y las 12
reglas de formación. **Nota**: la antigua "REGLA 13" (sufijos de dominio `addZ`/`mulQ`)
no se sigue en este proyecto — los axiomas de `MetaRules.lean` (`imp_intro`, `gen`,
`raa`, `dne`, `or_elim`, `ex_elim`) usan nombres descriptivos planos, sin prefijo de
dominio (`TAG_`) ni sufijo de estructura.

---

## ADR-005: Namespaces alineados con directorios

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: cada subdirectorio corresponde a un sub-namespace:
`FOL/Theorems/Eq.lean` → `namespace FOL.Theorems.Eq` (y análogamente para
`FOLPure`, `PropLogic`, `FOL_poli`, `TheoryFramework`).

**Justificación**: mapeo 1:1 claro entre sistema de ficheros y jerarquía de
namespaces.

**Consecuencias**: `new-module.bash` debe soportar creación en subdirectorios;
`gen-root.bash` debe escanear recursivamente. Ver ADR-010 sobre la relación entre las
5 sub-librerías.

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: cada sub-librería (`FOL`, `FOLPure`, `PropLogic`, `FOL_poli`,
`TheoryFramework`) agrupa sus teoremas derivados en un subdirectorio `Theorems/`
(o `Instances/` para `TheoryFramework`).

**Justificación**: separar el núcleo (sintaxis, semántica, deducción) de los
teoremas derivados facilita localizar cada pieza.

**Consecuencias**: cada subdirectorio con 2+ módulos requiere un barrel
(`AI-GUIDE.md` §18).

---

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: 2026-04-20
**Estado**: Propuesto (no implementado)

**Decisión**: `REFERENCE.md` debería ser solo el índice raíz, con el detalle de cada
sub-librería en nodos temáticos bajo `doc/REFERENCE-{tema}.md`.

**Justificación**: `REFERENCE.md` actual (617 líneas) solo documenta la librería
`FOL`; `FOLPure`, `PropLogic`, `TheoryFramework` y `FOL_poli` no tienen sección propia
pese a estar "✅ Completos". No existe todavía directorio `doc/` en este proyecto.

**Consecuencias**: **pendiente de implementar** — crear `doc/REFERENCE-FOLPure.md`,
`doc/REFERENCE-PropLogic.md`, `doc/REFERENCE-TheoryFramework.md` y
`doc/REFERENCE-FOL_poli.md`, y reducir `REFERENCE.md` a índice con enlaces. Ver
DEPENDENCIES.md para el estado real de las 5 sub-librerías mientras tanto.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: 2026-04-20
**Estado**: Aceptado

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones `@axiom_system` y
`@importance`.

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
**Estado**: Aceptado (decisión retroactiva — documenta una arquitectura ya existente)

**Contexto**: el proyecto declara 5 `lean_lib` en `lakefile.lean`: `FOL` (con
igualdad), `FOLPure` (sin igualdad), `PropLogic` (proposicional, sin cuantificadores
ni términos), `FOL_poli` (variante paralela de `FOL`) y `TheoryFramework` (marco
abstracto sobre cualquier `LogicSystem`).

**Decisión**: `FOL`, `FOLPure`, `PropLogic` y `FOL_poli` son implementaciones
paralelas independientes (cada una define su propio `Formula`, `Term`, etc. a nivel
raíz), no una jerarquía donde una extienda a otra. `TheoryFramework` es agnóstico y
se instancia por separado sobre cada una vía `TheoryFramework/Instances/*.lean`.

**Justificación**: `TheoryFramework.lean` (el barrel raíz) documenta explícitamente
por qué **no** importa `Instances/`: `FOLPure` y `FOL` definen ambas un `Formula` a
nivel raíz, y hacerlo produciría colisión de nombres. Mantener las instancias como
imports opt-in (`import TheoryFramework.Instances.FOL`, etc.) evita el conflicto sin
sacrificar la genericidad del marco.

**Consecuencias**: quien quiera usar `TheoryFramework` sobre una lógica concreta debe
importar explícitamente la instancia correspondiente, nunca `TheoryFramework` +
`Instances/` a la vez para dos lógicas distintas en el mismo fichero.

**Nota de auditoría (2026-07-12)**: `FOL.lean` y `FOL_poli.lean` (los barrels raíz de
esas dos sub-librerías) no importan actualmente `Classical.lean`, `Tactics2.lean` (o,
en `FOL`, `Theorems.Deduction`/`Theorems.Eq`/`Theorems.Soundness`) — 5 módulos
existentes en disco y no wireados en el barrel de cada una. No está claro si es
intencional (variantes experimentales) o un olvido; **pendiente de decidir y
documentar** en una revisión posterior — no se ha tocado el barrel en esta sesión
para no alterar el comportamiento del build sin confirmación del autor.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
