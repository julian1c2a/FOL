# Guía Maestra de la IA — Estándares de Documentación y Desarrollo

**Last updated:** 2026-11-09 — revisado contra el árbol ([ADR‑262 de RPP](../ROBINSON_PlusPlus/DECISIONS.md)): las 44 citas muertas de [B], arregladas; los nombres de la plantilla, por los de FOL; los controles de su CI, en la tabla de scripts; y notas fechadas, medidas, donde la regla no describe FOL (sin nodos temáticos, el recordatorio de §11, el `export` en 6 de 70, los barriles, los bloqueos y los congelados, la cabecera de copyright, la hora de §22). Antes, 2026-07-12
**Autor:** Julián Calderón Almendros

> Este documento define lo **universal**: aplica a cualquier proyecto Lean 4 que nazca
> de esta plantilla, sin cambios. Lo **específico de un proyecto concreto** (sus
> MANDATORIES, sus ADRs, sus decisiones de arquitectura matemática) va en `DECISIONS.md`,
> no aquí. Si al copiar esta plantilla sientes la tentación de añadir aquí una regla
> que solo aplica a tu proyecto, no lo hagas — va en `DECISIONS.md` §MANDATORIES.

Este archivo es el **primer documento** que un asistente de IA debe leer. Define el
protocolo de documentación del proyecto, las convenciones de nomenclatura (por
referencia a `NAMING-CONVENTIONS.md`), la política de bloqueo de archivos, el formato
de código y los comandos interactivos disponibles. **Léelo completamente antes de
modificar cualquier archivo `.lean` o de documentación.**

---

## 0. Sistema REFERENCE — Arquitectura en Árbol

### (0.) Naturaleza de la documentación

Esta documentación es puramente técnica, no para usuarios finales. Es una referencia
para asistentes de IA y desarrolladores experimentados de Lean 4. Debe ser clara,
precisa y completa, pero no pedagógica — cero explicaciones de lo que ya dicen los
nombres bien elegidos.

### (0.5.) REFERENCE.md es un SISTEMA, no un fichero único

**Regla fundamental, incumplida con frecuencia: `REFERENCE.md` NUNCA debe crecer como
un único fichero monolítico.** Es el índice raíz de un árbol de documentos
interconectados:

- **Índice raíz** (`REFERENCE.md`, en la raíz del repositorio): catálogo general (tabla §1 con todos
  los módulos, una fila por fichero `.lean`) y mapa de navegación hacia los nodos
  temáticos. No contiene el detalle exhaustivo de cada definición/teorema — eso vive
  en los nodos.
- **Nodos temáticos** (`doc/REFERENCE-{campo-temático}.md`): un fichero
  por rama matemática o subsistema (p. ej., en la plantilla,
  `REFERENCE-Arithmetic.md`, `REFERENCE-GroupTheory.md` o `REFERENCE-Rationals.md`, hipotéticos aquí). Ahí van las firmas Lean 4,
  la notación matemática, las dependencias y el detalle de cada símbolo exportado.
- **Navegación fuerte obligatoria** — cada nodo temático **DEBE**:
  - enlazar de vuelta al índice raíz (`[REFERENCE.md](../REFERENCE.md)`);
  - enlazar de forma cruzada a otros nodos temáticos relacionados (no dejar nodos
    aislados — si `REFERENCE-Rationals.md` (hipotético) depende de `REFERENCE-Arithmetic.md`, debe
    decirlo y enlazarlo explícitamente, y viceversa);
  - enlazar a los ficheros `.lean` concretos que documenta.
- La fila de cada módulo en la tabla §1 del índice raíz **debe enlazar** a su nodo
  temático correspondiente (no solo nombrarlo en texto plano).
- Cuando un subsistema crece lo bastante para tener su propio nodo temático y aún no
  lo tiene, **crear el nodo antes de seguir añadiendo filas sueltas al índice raíz**.
  Un índice raíz que intenta documentar el detalle completo de +100 módulos en una
  sola tabla deja de ser navegable — ese es exactamente el síntoma a evitar.

> ✏️ **2026‑11‑09 · en FOL no hay nodos temáticos** (ADR‑262 de RPP). `doc/` tiene sólo `doc/indice.tsv` y
> `doc/control/`, y el sistema REFERENCE es un único fichero, `REFERENCE.md`, con su §6 («Exports») GENERADA de las
> fuentes (`gen-reference.py`, con `--check` en la CI). Lo recoge su ADR‑007 (`DECISIONS.md`), que proponía el árbol
> `doc/REFERENCE-{tema}.md`: Obsoleto, nunca se implementó (T56, ADR‑245 de RPP). Donde esta guía dice «nodo
> temático», aquí es `REFERENCE.md`. Un árbol que sigue la regla, el de RPP (`../ROBINSON_PlusPlus/REFERENCE.md` §1 y
> sus `doc/REFERENCE-*.md`).

### (1.) Catálogo de módulos Lean

El índice raíz (`REFERENCE.md`) debe listar todos los archivos `.lean` (en la raíz del
proyecto y subdirectorios) con su ubicación, espacio de nombres (*namespace*),
dependencias, estado, y enlace a su nodo temático correspondiente.

### (2.) Dependencias de módulos

Cada módulo debe documentar claramente (en su nodo temático) de qué módulos depende y
qué módulos dependen de él. Crítico para que la IA navegue sin cargar el proyecto
completo.

### (3.) Espacios de nombres (Namespaces)

Los namespaces no son necesariamente iguales a los módulos. Documentar qué namespaces
existen, a qué módulos pertenecen y cómo se relacionan. Todos derivan del namespace
raíz del proyecto.

### (4.) Definiciones introducidas

Para cada módulo y namespace, documentar todas las definiciones en su nodo temático:

- **(4.1) Firma y notación**: firma exacta en Lean 4 más la notación matemática pura
  (sin explicaciones — el público son matemáticos y expertos en Lean 4).
- **(4.2) Computabilidad**: si es `computable` o `noncomputable`, si tiene contraparte
  booleana, y si es decidible.
- **(4.3) Buena fundación**: si incluye prueba de terminación (la cláusula termination_by de Lean).
- **(4.4) Notación**: notaciones introducidas (infijo, prefijo, macros), símbolos y
  prioridades.

### (5.) Axiomas introducidos

Cada axioma documenta su ubicación (módulo, namespace, orden de declaración) y su
relación con las definiciones.

### (6.) Formato estricto para axiomas y definiciones

Siempre:

- **(6.1)** Notación matemática pura (legibilidad humana, sin explicaciones).
- **(6.2)** Firma exacta en Lean 4.
- **(6.3)** Dependencias necesarias para construir la definición o el axioma.

### (7.) Teoremas (sin pruebas)

Los teoremas principales se documentan **sin ningún tipo de prueba**, solo con:

- **(7.1)** Notación matemática.
- **(7.2)** Firma exacta en Lean 4.
- **(7.3)** Dependencias necesarias para probar el teorema.

### (8.) Prohibición de contenido no probado

**Cero contenido no probado entra en el sistema REFERENCE.** Cero TODOs, cero teoremas
pendientes, cero `sorry` documentados como si estuvieran cerrados. Solo lo que ya
compila y está demostrado en los ficheros `.lean`.

### (9.) Trazabilidad y actualización

Actualizar el nodo temático correspondiente cada vez que se modifique un fichero
`.lean`. Registrar la fecha de la actualización **y** la fecha de última modificación
del `.lean` proyectado, para poder detectar desincronización.

### (10.) Autosuficiencia

El sistema REFERENCE completo (índice + nodos) debe bastar para escribir nuevos
módulos o pruebas **sin cargar el resto del proyecto**.

### (11.) Recordatorio de proyección

Al leer un fichero `.lean`, añadir o verificar su comentario de cabecera que recuerda
proyectarlo a REFERENCE.md.
✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: lo llevan 44 de los 70 `.lean` de `FOL/` y `TheoryFramework/`
(«-- REFERENCE.md: project this file after every modification.»; en RPP, ninguno), y ningún control lo mira.

### (12.) Qué significa "proyectar"

"Proyectar" un `.lean` significa trasladar todo lo público (el bloque `export`) al
nodo temático que le corresponde, siguiendo los puntos (1)–(10).

### (13.) Qué es "información relevante"

Toda definición, notación, axioma y teorema no privado, y cualquier otro contenido
necesario para entender el proyecto, usarlo como referencia, o construir pruebas
sobre él.

### (14.) Todo lo exportable debe proyectarse

Todo lo que aparezca en un bloque `export` de un `.lean` **DEBE** estar proyectado en
su nodo temático de REFERENCE.md.

---

## Formato y Estilo de Código

### (15.) Argumentos implícitos y alineación

Para mantener la legibilidad en firmas complejas, las declaraciones largas se dividen.
`:=` y `by` van tabulados o en líneas separadas de forma limpia:

```lean
private theorem singleton_eq_pair {a b c : Type}
  (h : singleton a = pair b c) :
    a = b ∧ a = c
      := by
  ...
```

### (16.) Excepción de una línea (one-liner term-mode)

Si la declaración completa (nombre, parámetros, tipo, `:=` y cuerpo) cabe en una sola
línea (≤ 90 caracteres) y la prueba es un término trivial, se prefiere la forma
compacta:

```lean
theorem subset_refl (A : Type) : A ⊆ A := fun _ h => h
```

### (16b.) Regla de directorio raíz (No-Root Rule)

**NUNCA** crear módulos de trabajo (ficheros `.lean` con teoremas, definiciones, etc.)
en el directorio raíz del repositorio (donde está `lakefile.lean`). Todo módulo de
trabajo vive dentro del directorio del proyecto (aquí, `FOL/` y `TheoryFramework/`, uno por `lean_lib`) o en
subdirectorios temáticos dentro de él. El único `.lean` permitido en la raíz es el
barril raíz de cada `lean_lib` (aquí, `FOL.lean` y `TheoryFramework.lean`), curado a mano, y el ejecutable si
existe (FOL no tiene). (✏️ 2026‑11‑09, ADR‑262 de RPP: decía los nombres de la plantilla, ProjectName/,
ProjectName.lean y Main.lean.)
(✏️ 2026‑10‑18, T15 y ADR‑163 de RPP: decía «autogenerado, vía `gen-root.bash`»; el script se retiró.)

**Ficheros scratch/temporales de sesión (`scratch*.lean`, `temp_*.lean`, `fix_*.py`, `fix-*.ps1`; hoy no existe
ninguno versionado) nunca se commitean.** Van en `.gitignore` desde el primer commit del
proyecto (ver plantilla de `.gitignore` de este repositorio). Si necesitas
experimentar, hazlo en uno de esos ficheros y bórralo (o dótalo de nombre definitivo e
impórtalo) antes de terminar la sesión — nunca lo dejes `git add`eado "por si acaso".
(✏️ 2026‑11‑09, ADR‑262 de RPP: medido, el `.gitignore` de FOL no los lista, ni los ha listado nunca
—`git log --all -S scratch -- .gitignore`, vacío—, y tampoco el de RPP ni el de la plantilla lean4-project-template:
no los aparta git, sino quien no los commitea.)

---

## Arquitectura de Exportaciones y Directorios

### (17.) Bloques de exportación (*export blocks*)

Todo módulo de producción (hoja, no barrel) **DEBE** terminar con un bloque `export`
que liste todas las definiciones, teoremas y lemas públicos:

```lean
namespace MyNamespace

def myDef : Type := ...
theorem myTheorem : ... := ...

end MyNamespace

-- Export: todas las declaraciones públicas de este módulo
export MyNamespace (myDef myTheorem)
```

Reglas:

1. El `export` va DESPUÉS de `end namespace`, a nivel de fichero.
2. Lista TODOS los `def`/`theorem`/`lemma`/`instance` no privados.
3. NUNCA exportar declaraciones `private` ni auxiliares con el sufijo _aux.
4. Lista alfabética dentro de cada namespace.
5. Si un módulo contribuye a varios namespaces, un `export` por namespace.
6. `notation`/`macro`/`syntax` NO se listan en `export` — se propagan solas al
   importar.

El bloque `export` es la **lista canónica** de la API pública de un módulo: añadir,
renombrar o borrar una declaración pública exige actualizar el `export` (y, por (14),
proyectarlo a REFERENCE.md).

> ✏️ **2026‑11‑09** (ADR‑262 de RPP), **medido** con un grep de `^export ` en los 70 `.lean` de `FOL/` y
> `TheoryFramework/`: llevan el bloque seis —`Deduction`, `Soundness0` y `Theorems/Derived`, `Impl`, `Neg` y
> `Quantifiers`—, y nada lo comprueba: el §6 de `REFERENCE.md` («Exports») se genera de las DECLARACIONES
> (`gen-reference.py`), no de los `export`. En RPP esta misma regla se enmendó: el bloque es OPCIONAL (ADR‑206 de
> RPP, decisión del propietario). Aquí sigue escrita como estaba; enmendarla también es decisión suya.

### (18.) Archivos "barrel" (paraguas)

Cualquier subdirectorio con 2+ módulos **DEBE** tener un fichero barrel al mismo nivel
que el directorio (p. ej., en la plantilla, Algebra.lean para Algebra/) que importe todos sus
submódulos. Los barrels **no contienen código**, solo `import` (y opcionalmente un
comentario catalogando la API pública del directorio). El barrel raíz del proyecto
(aquí, `FOL.lean` y `TheoryFramework.lean`) prefiere importar barrels de subdirectorio en vez de listar cada
submódulo suelto. Los barrels se curan a mano (✏️ 2026‑10‑18, T15 y ADR‑163 de RPP: los regeneraba, borrando sus
comentarios, `gen-root.bash`, retirado). Los `globs` del lakefile compilan todo el directorio, y `[L]` de
`check-doc-sync.bash` exige que cada fichero esté en el cierre de imports de las raíces (`cierre-imports.bash`).
✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: la regla de los barriles no se cumple en todo el árbol —`FOL/Calculus/`
(7 módulos), `FOL/Theorems/` (5; los importa `FOL/Core.lean`) y `TheoryFramework/Instances/` (2) no tienen barril,
y `FOL.lean` importa módulos sueltos, ningún barril de subdirectorio—, y ningún control la mira: lo que se exige
es `[L]`.

### (19.) Organización por subdirectorios temáticos

A medida que el proyecto crece, organizar los módulos en subdirectorios temáticos
(UpperCamelCase, reflejando el sub-namespace). Cada subdirectorio puede tener su
propio Basic.lean fundacional (en FOL, ninguno). El módulo `Theorems/Impl` es `FOL/Theorems/Impl.lean`, con
namespace `FOL.Theorems.Impl`, y se importa desde su barril (aquí, `FOL/Core.lean`: ver §18). (✏️ 2026‑11‑09,
ADR‑262 de RPP: el ejemplo era el de la plantilla, Nat/Add en ProjectName/. Y medido: «reflejando el sub-namespace»
no vale en todo el árbol: `FOL/Calculus/` declara en `FOL.Calculus`, `TheoryFramework/Instances/` en
`TheoryFramework.Instances`, y `Theorems/Eq.lean` y `SymClasses.lean` en `FOL`; el estado de ADR‑005, en
`DECISIONS.md`, recoge los de `FOL/`.) (✏️ 2026‑10‑18, T15 y ADR‑163 de RPP: lo creaba
`new-module.bash` (retirado) desde una plantilla, `_template.lean`, que ya no existía; el script se retiró.)

---

## Sistema de Bloqueo de Archivos

`git-lock.bash` implementa dos niveles de protección de escritura. **Este sistema
existe para ser usado de verdad, no para quedar documentado y vacío** — si
`locked_files.txt`/`frozen_files.txt` llevan vacíos varias sesiones seguidas pese a
haber módulos "✅ Completos", el protocolo no se está siguiendo.

| Nivel | Comando | Reversible | Propósito |
|---|---|---|---|
| **Lock** | `lock` / `unlock` | Sí | Un solo fichero desbloqueado a la vez durante el desarrollo |
| **Freeze** | `freeze` / `thaw --confirm` | Solo en emergencia | Módulo terminado — inmutable para siempre |

> **Nota de plataforma**: en Windows/NTFS, `chmod a-w` (usado internamente por
> `git-lock.bash`) **no impide realmente la escritura del fichero** — el lock es un
> contrato social reforzado por el hook `pre-commit` (que sí bloquea el commit cuando está activo:
> `bash git-lock.bash init`, una vez por clon, porque git no activa ganchos solo; sin él, el cambio de un
> congelado lo detiene la CI —`check-congelados.bash`—, y el de un bloqueado, nada), no
> una protección real del sistema de ficheros. No asumas que "está bloqueado" significa
> "no se puede editar"; significa "el commit fallará si lo tocas sin desbloquearlo
> antes", con el gancho activo. *(✏️ 2026‑11‑09, ADR‑262 de RPP: decía «(que sí bloquea el commit)», sin la
> condición; en RPP lo corrigió ADR‑235.)*

### (20.) Protocolo de bloqueo de sesión

Como máximo un `.lean` desbloqueado en cada momento.
✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: hoy 19 de los 70 `.lean` de `FOL/` y `TheoryFramework/` no están ni
bloqueados ni congelados (`locked_files.txt`, `frozen_files.txt`).

```bash
bash git-lock.bash lock   ProjectName/Module.lean   # bloqueo temporal
bash git-lock.bash unlock ProjectName/Module.lean   # desbloqueo temporal
bash git-lock.bash list                             # lista bloqueados y congelados
bash git-lock.bash init                             # activa los ganchos versionados (.githooks/, core.hooksPath)
```

Protocolo de sesión:

1. **Inicio de sesión**: ejecutar `list`. Desbloquear solo el fichero objetivo.
2. **Cambio de fichero**: bloquear el actual ANTES de desbloquear el siguiente.
3. **Fin de sesión**: bloquear todos los ficheros modificados. Commitear
   `locked_files.txt`.
4. El hook `pre-commit` bloquea commits que toquen ficheros bloqueados o congelados.
   ✏️ 2026‑10‑31 (T14, ADR‑234 de RPP): los ganchos están VERSIONADOS en `.githooks/` —`pre-commit`, el
   de los congelados y bloqueados, y `commit-msg`: un thaw cita en su mensaje el ADR de RPP que lo autoriza,
   «ADR-NNN de RPP»— y `init` los activa con `core.hooksPath` (una vez por clon: git no activa ganchos
   solo). Corre el fichero versionado, no una copia en .git/hooks/. La CI no depende de que estén
   activos: `check-congelados.bash` (el thaw y su ADR) y `check-gancho.bash` (los ganchos, probados en un
   repositorio de juguete); que el ADR exista y recoja la decisión del propietario, la CI de RPP
   (su scripts/thaws-fol.bash). ✏️ 2026‑11‑09 (ADR‑262 de RPP): eso vale para los congelados; un bloqueado sólo
   lo para el gancho (la CI no lee el `locked_files.txt` del repositorio).

### (21.) Protocolo de congelado (freeze) de módulos completos

Cuando un módulo alcanza estado ✅ Completo en REFERENCE.md, debe **congelarse**. Un
módulo congelado es inmutable para siempre: no se puede desbloquear, solo extender.
✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: están congelados 47 de los 70 `.lean` de `FOL/` y `TheoryFramework/`
(`frozen_files.txt`); los demás no, aunque el catálogo los dé por «✅ Completo». Qué se congela lo criba
`criba-congelacion.py` (los criterios medibles; los otros piden juicio) y lo decide el propietario (p. ej., ADR‑219 de
RPP: «Congela la cadena X1»).

```bash
bash git-lock.bash freeze ProjectName/Module.lean
bash git-lock.bash thaw   ProjectName/Module.lean --confirm   # solo emergencias
```

**Protocolo de extensión de un módulo congelado** Foo.lean (un nombre de ejemplo):

1. Crear FooExt.lean (o, mejor, un nombre semántico como FooDivisibility.lean) en
   el mismo directorio.
2. Importar el módulo congelado y reabrir su namespace.
3. Añadir FooExt.lean al barrel/raíz y a REFERENCE.md.
4. Foo.lean permanece congelado e intacto.

✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: en FOL ningún `.lean` es una extensión así (ninguno se llama …Ext.lean);
cuando un congelado ha tenido que cambiar, se ha descongelado con su ADR de RPP: los thaws de antes de ADR‑234, en
`../ROBINSON_PlusPlus/doc/control/thaws-fol.tsv`; desde entonces, citado en el mensaje del thaw (§20).

**Códigos de estado en REFERENCE.md:**

| Código | Significado |
|---|---|
| 🔄 En progreso | En desarrollo activo |
| 🔶 Parcial | Documentado parcialmente |
| ✅ Completo | Proyectado por completo. Puede seguir bloqueado (temporal) |
| 🧊 Congelado | Congelado para siempre. Solo extensible vía un módulo de extensión (FooExt.lean, arriba) |

Transición: 🔄 → 🔶 → ✅ → 🧊 (el estado 🧊 es final).

---

## Scripts Disponibles

| Script | Propósito |
|---|---|
| `bash git-lock.bash lock <file>` · `bash git-lock.bash unlock <file>` | Bloqueo temporal |
| `bash git-lock.bash freeze <file>` · `bash git-lock.bash thaw <file> --confirm` | Congelado permanente / deshielo de emergencia (un thaw, sólo con el ADR de RPP que lo autoriza, citado en su mensaje: §20) |
| `bash git-lock.bash list` | Lista de bloqueados y congelados |
| `bash git-lock.bash init` | Activa los ganchos versionados (`.githooks/`, `core.hooksPath`; T14, ADR‑234 de RPP) |
| `bash cierre-imports.bash` | El cierre de imports de las raíces: el universo de los módulos (`[L]`, `[A]` y `[C]` de `check-doc-sync.bash`; T15 y ADR‑163 de RPP). `--autotest` lo comprueba. (✏️ 2026‑10‑18: aquí estaban `new-module.bash` y `gen-root.bash`, retirados) |
| `bash check-sorry.bash` | Busca como TOKEN `sorry`, `sorryAx`, `admit` y `stop`, sin comentarios ni literales (`strip-lean.awk`, con una prueba de humo del despojador), en todo `.lean` del árbol (sin .lake/, _rpp/ ni Probe/). Rojo (sale con 1; con 2 si no puede medir); en la CI (y `make sorry`) |
| `bash check-axioms.bash` | Los `axiom` de Lean de FOL y de TheoryFramework, contados en el ENTORNO de Lean (con un grep sin comentarios de contraste; la cuarentena, por grep), contra lo que dice `AXIOMS.md`: hoy, cero (`ESPERADO_FOL=0`, `ESPERADO_TF=0`; en `cuarentena/librerias-retiradas/` el script espera 15, `ESPERADO_RET`); y las constantes que nombran `sorryAx`. Rojo; en la CI (y `make axioms`) |
| `bash check-doc-sync.bash` | Que la documentación cuadra con el código (portado de RPP, ADR‑061 de RPP; los bloques, como en la §27 de `../ROBINSON_PlusPlus/AI-GUIDE.md`): aquí [L], [EOL], [H], [A], [A2], [E], [B], [C], [D], [F], [G] y [G.2]; sale con 1 si algo no cuadra; en la CI. No ejecuta `lake build`: los jobs de FOL los mide RPP |
| `bash check-congelados.bash [BASE]` | Ningún congelado cambia entre la base (por omisión, el master remoto) y HEAD sin salir antes de `frozen_files.txt` (su thaw), y cada thaw cita «ADR-NNN de RPP» en su mensaje (R3‑4‑01, ADR‑212 de RPP; T14, ADR‑234 de RPP); con autotest. Rojo; en la CI |
| `bash check-gancho.bash` | Prueba los ganchos de `.githooks/` en un repositorio de juguete, siete casos (un congelado, un bloqueado, un renombre, un libre, dos thaws y un re-freeze), y que la expresión del thaw sea la de `check-congelados.bash` (T14, ADR‑234 de RPP). En la CI |
| `bash check-indice.bash [--rehacer]` | El índice de las constantes de FOL y TheoryFramework, `doc/indice.tsv` (nombre, clase, módulo y enunciado), contra lo que se genera del entorno de Lean (L5‑11, ADR‑254 de RPP); con `--rehacer` lo reescribe, en el commit que cambia una declaración. Rojo; en la CI (y `make indice`) |
| `bash guarda_y_bloquea.bash <fichero> "<mensaje>"` | Commitea un fichero BLOQUEADO sin tocar la lista y lo vuelve a bloquear, sin push; rechaza un congelado (T52, ADR‑201 de RPP). `--autotest`, en un repositorio de prueba: en la CI |
| `bash guarda-toolchain.bash` | Se niega (código 1) si RPP, al lado, lleva otro `lean-toolchain` (M‑1 de `DECISIONS.md`); sin RPP al lado lo dice y deja seguir. Lo llaman `make build`, `make build-all` y `check-axioms.bash` |
| `python3 gen-dependencies.py [--check]` | Escribe `DEPENDENCIES.md` desde los `import` de `FOL/` y `TheoryFramework/`; con `--check` sale con 1 si lo versionado no es lo que se generaría, y así corre en la CI |
| `python3 gen-reference.py [--check]` | Regenera el §6 de `REFERENCE.md` («Exports») desde las declaraciones (T56, ADR‑245 de RPP); `--check`, en la CI |
| `py criba-congelacion.py` | La criba de CONGELACIÓN: los criterios medibles para congelar un módulo; sólo lectura, y su salida es una criba, no un permiso de `freeze` |
| ~~`bash update-toolchain.bash vX.Y.Z`~~ | ⛔ Retirado aquí (2026‑10‑20, T42, ADR‑176 de RPP): compilaba FOL desde este directorio (contra la M‑3 de RPP de entonces, que reescribió ADR‑205 de RPP) y commiteaba solo. El par se prueba desde RPP: `cd ../ROBINSON_PlusPlus && bash update-toolchain.bash [vX.Y.Z]`, en árboles aparte y sin commit |
| ~~`bash setup.bash`~~ | ⛔ Retirado (T52, ADR‑201 de RPP): era el inicializador de la plantilla; hoy sólo avisa y sale con 1 |
| `make help` | Lista los targets del Makefile |

✏️ 2026‑11‑09 (ADR‑262 de RPP): la tabla no nombraba ningún control de la CI (`.github/workflows/build.yml`). Las filas
de `check-axioms.bash` a `criba-congelacion.py` y la de `setup.bash`, añadidas, leídas de las cabeceras de los
scripts; la de `check-sorry.bash` decía «Localiza todos los `sorry` (excluyendo comentarios)», y las de
`git-lock.bash`, lock/unlock y freeze/thaw.

---

## Trazabilidad y Documentación Anexa

### (22.) Marcas de tiempo

Todos los ficheros de documentación técnica (`REFERENCE.md` y sus nodos, `CHANGELOG.md`,
`DEPENDENCIES.md`, `CURRENT-STATUS-PROJECT.md`, y cualquier resumen técnico) deben
incluir una marca de tiempo bajo el título en formato `YYYY-MM-DD HH:MM` (ISO 8601
abreviado) — **no solo `YYYY-MM-DD`**: la hora permite detectar desincronización
incluso dentro de una misma sesión de trabajo.
✏️ 2026‑11‑09 (ADR‑262 de RPP), medido: de los documentos que nombra, ninguno lleva la hora justo detrás de su
sello (`**Last updated:** AAAA-MM-DD — …`); [D] de `check-doc-sync.bash` mira sólo que `REFERENCE.md`,
`CURRENT-STATUS-PROJECT.md` y `DEPENDENCIES.md` lleven la etiqueta, y [E], sólo la fecha: la hora no la pide ningún
control.

### (23.) Autoría y licencia

- README.md, REFERENCE.md y CURRENT-STATUS-PROJECT.md declaran el autor.
- Créditos visibles en README.md: recursos educativos, referencias bibliográficas,
  herramientas de IA usadas.
- Licencia MIT, indicada en `LICENSE`, `README.md` (pie y badge) y el pie de
  `CURRENT-STATUS-PROJECT.md`.
- Todo fichero `.lean`, sin excepción, empieza con cabecera de copyright antes de
  cualquier `import`:

```lean
/-
Copyright (c) YYYY. All rights reserved.
Author: [Nombre del Autor]
License: MIT
-/
```

✏️ 2026‑11‑09 (ADR‑262 de RPP), medido (la línea «Copyright» antes del primer `import`): no la llevan 83 de los 186
`.lean` versionados: 68 de `auditoria/`, 10 de `cuarentena/`, `lakefile.lean` y cuatro de la librería —`FOL/Tactics.lean`
y tres congelados, `FOL/FOL.lean`, `FOL/SymClasses.lean` y `FOL/Theorems/Eq.lean`—. Ningún control lo mira.

### (24.) Anotaciones de módulo para REFERENCE.md

**A nivel de módulo** (en la tabla §1 o en el nodo temático):

```markdown
**@axiom_system**: `ZFC` | `Peano` | `BoolAlg` | `none`
**@importance**: `foundational` | `high` | `medium` | `low`
```

### (25.) Anotaciones de teorema para REFERENCE.md

**A nivel de teorema/definición** (en el nodo temático):

```markdown
**@importance**: `high` | `medium` | `low`
```

`high` = usado por 3+ módulos o es un axioma/definición clave; `medium` = usado por
1–2 módulos; `low` = utilidad interna, solo usada dentro de su propio módulo. Ayuda a
la IA a priorizar qué cargar.

### (26.) Ficheros de referencia cruzada

| Fichero | Propósito |
|---|---|
| `REFERENCE.md` + `doc/REFERENCE-*.md` | Sistema de referencia en árbol (ver §0.5; en FOL, sólo `REFERENCE.md`) |
| `NAMING-CONVENTIONS.md` | Diccionario de nombres + 12 reglas de formación (nombres en inglés, prosa en español) |
| `DECISIONS.md` | ADRs formales + sección **MANDATORIES** con las directivas no negociables *de este proyecto concreto* |
| `DEPENDENCIES.md` | Grafo y tabla maestra de dependencias entre módulos: GENERADO por `gen-dependencies.py`; no se edita a mano |
| `PLANNING.md` | Visión a largo plazo — ideas y direcciones que aún necesitan madurar |
| `NEXT-STEPS.md` | Pasos inmediatos y concretos, listos para ejecutar (nombre canónico con guión — nunca `NEXT_STEPS.md`, que no existe) |
| `THOUGHTS.md` | Diario de diálogo diseño usuario↔IA — nunca normativo, nunca sustituye una regla de esta guía |
| `WORKFLOW.md` | Metodología operativa de Git, IA y Lean |
| `CURRENT-STATUS-PROJECT.md` | Snapshot en vivo del build, jobs y estado de módulos |
| `CHANGELOG.md` | Historial de cambios |

`PLANNING.md` → `NEXT-STEPS.md`: los ítems migran solo cuando están lo bastante
maduros para ejecutarse (objetivo claro, dependencias conocidas, sin preguntas de
diseño abiertas). `THOUGHTS.md` → `PLANNING.md`: las ideas maduran ahí antes de
convertirse en plan.

---

## Comandos Interactivos para la IA

La IA debe obedecer estos comandos exactos cuando el usuario los invoque en el chat.

### «actualiza doc»

**Propósito:** pasada completa de documentación — sincronizar todos los ficheros
vivos con el estado real del código tras una sesión de desarrollo.

**Pasos (en orden):**

1. Ejecutar `lake build` — anotar jobs, errores, `sorry`, warnings.
2. Leer el estado previo de `NEXT-STEPS.md`, `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md`.
3. Identificar qué cambió: qué `sorry` se cerraron, qué módulos/teoremas se añadieron,
   qué módulos cambiaron de estado (🔄→🔶→✅→🧊).
4. Actualizar `CHANGELOG.md`: nueva entrada `[YYYY-MM-DD]` con los cambios de la sesión.
5. Actualizar `NEXT-STEPS.md`: mover lo completado, refrescar la tabla de `sorry`
   vigentes (fichero:línea).
6. Actualizar `CURRENT-STATUS-PROJECT.md`: snapshot de build y tabla de estado de
   módulos.
7. Actualizar el árbol de directorios de este fichero (§22) si hubo cambios
   estructurales. (✏️ 2026‑11‑09, ADR‑262 de RPP: esta guía no tiene árbol de directorios —su §22 es «Marcas de
   tiempo», y el paso viene así de la plantilla—; el grafo de los módulos es `DEPENDENCIES.md`, generado:
   `python3 gen-dependencies.py`.)
8. Proyectar a REFERENCE.md los ficheros `.lean` tocados en la sesión (§1–§14).
9. **Verificar consistencia**: el recuento de `sorry` debe coincidir entre
   `NEXT-STEPS.md`, `CHANGELOG.md` y `check-sorry.bash`; toda declaración pública
   nueva aparece en su bloque `export`.
10. Reportar en el chat un resumen breve: `sorry` cerrados, declaraciones nuevas,
    ficheros tocados, `sorry` restantes y su ubicación.

### «actualiza_documentacion»

**Propósito:** sincronizar los documentos de alto nivel (estado, dependencias,
decisiones, flujo), no el detalle técnico módulo a módulo.

**Ficheros afectados:** `README.md`, `CURRENT-STATUS-PROJECT.md`, `DECISIONS.md`,
`DEPENDENCIES.md`, `WORKFLOW.md`.

**Pasos:** ejecutar `lake build` para datos frescos → actualizar
`CURRENT-STATUS-PROJECT.md` → actualizar métricas de `README.md` → añadir un ADR nuevo
a `DECISIONS.md` si hubo una decisión arquitectónica → regenerar `DEPENDENCIES.md` (`python3 gen-dependencies.py`) si se
crearon/movieron módulos → revisar `WORKFLOW.md` si la sesión reveló una regla
operativa nueva.

### «pon_al_dia_el_plan»

**Propósito:** limpiar y sincronizar la planificación, eliminando el ruido de tareas
ya completadas — **aplicar con disciplina**, no dejar que `NEXT-STEPS.md`/`PLANNING.md`
crezcan indefinidamente con entradas históricas ya resueltas.

**Ficheros afectados:** `NEXT-STEPS.md`, `PLANNING.md`, `THOUGHTS.md`.

**Pasos:** cruzar lo logrado en la sesión con `THOUGHTS.md`/`PLANNING.md` → purgar de
`NEXT-STEPS.md` todo lo ya hecho → promover objetivos maduros de `PLANNING.md` a
`NEXT-STEPS.md`.

### «revisa_pensamientos»

**Propósito:** analizar `THOUGHTS.md` y proponer próximos pasos, sin modificar ficheros.

**Pasos:** leer `THOUGHTS.md` íntegro → categorizar las ideas (decisiones pendientes,
refactors imaginados, dudas) → responder en el chat qué ideas están maduras para pasar
a `NEXT-STEPS.md`, cuáles necesitan más pensamiento, y posibles respuestas a los
dilemas planteados.

**Protocolo pasivo:** la IA debe leer `THOUGHTS.md` tras completar cualquier tarea
(fix, doc, paso de prueba) antes de cerrar su turno; si hay una pregunta sin resolver,
la plantea en su respuesta en vez de ignorarla en silencio. `THOUGHTS.md` nunca es
normativo — nunca invalida una regla de esta guía.

### «compila_y_comprueba»

**Propósito:** comprobación exhaustiva con registro verboso.

**Ficheros afectados:** build_report.txt, en la raíz (se sobrescribe en cada llamada; el `.gitignore` lo aparta).

**Pasos:** ejecutar `lake build` completo → capturar toda la salida → volcarla en
build_report.txt → informar en el chat del resultado global (éxito/fallo, nº de
errores) invitando a revisar el fichero para más detalle.

### «dame situación»

**Propósito:** informe de solo lectura del estado actual. No modifica ningún fichero.

**Pasos (en paralelo cuando sea posible):** `check-sorry.bash` → `lake build` (jobs,
errores, warnings) → leer la tabla de `sorry` vigentes de `NEXT-STEPS.md` → leer la
tabla de estado de módulos de `CURRENT-STATUS-PROJECT.md` → leer la última entrada de
`CHANGELOG.md`.
✏️ 2026‑11‑09 (ADR‑262 de RPP): en FOL, `NEXT-STEPS.md` no tiene tabla de `sorry` (hay cero: `check-sorry.bash`), y
el estado de cada módulo está en el catálogo de `REFERENCE.md` §1.1; `CURRENT-STATUS-PROJECT.md` tiene la tabla de
los resultados («Estado vigente»).

**Formato de salida (siempre en este orden):**

```text
## Situación — YYYY-MM-DD

### Build
- Jobs: N  |  Errores: 0  |  Sorries activos: N  |  Warnings: N

### Sorries vigentes
| Archivo | Línea | Teorema | Estrategia |
|---------|-------|---------|------------|
| ...     | ...   | ...     | ...        |

### Último cambio documentado
- Fecha: YYYY-MM-DD
- Resumen: <primera línea del último bloque de CHANGELOG.md>

### Módulos con estado incompleto
| Módulo | Estado | Bloqueado por |
|--------|--------|---------------|
| ...    | ...    | ...           |

### Próximo objetivo
<extraído de NEXT-STEPS.md>
```

### «proyecta»

**Propósito:** actualización local del sistema REFERENCE para un fichero o sesión
concreta.

**Pasos:** identificar los `.lean` modificados en la sesión → extraer su bloque
`export` → traducir cada símbolo a notación matemática + firma Lean 4 + dependencias
(§1–§14) → insertarlos en el nodo temático correspondiente de `doc/REFERENCE-*.md` (en FOL, en `REFERENCE.md`:
§0.5; su §6 se regenera con `python3 gen-reference.py`) →
actualizar el índice raíz `REFERENCE.md` si es un nodo nuevo → verificar que todo lo
del `export` block quedó proyectado y que nada privado se filtró.

### «repasa_y_proyecta»

**Propósito:** sincronización masiva y profunda de todo el árbol REFERENCE.

**Pasos:** recorrer módulo a módulo todo el proyecto → por cada `.lean`, leer su
`export` y verificar que cada símbolo está bien documentado en su nodo temático →
detectar y eliminar "elementos fantasma" (declaraciones borradas, renombradas o vueltas
`private` en el código que siguen documentadas como vigentes) → asegurar coherencia de
fechas, jerarquía de dependencias y enlaces de navegación fuerte → actualizar el
índice raíz.

### «guarda_y_sube»

**Propósito:** flujo de Git seguro y ciclo completo de actualización del repositorio
preservando los bloqueos locales.

**Pasos exactos:**

1. Ejecutar `lake build` para garantizar que no hay errores de compilación.
   ✏️ 2026‑11‑09 (ADR‑262 de RPP): la CI corre además `bash check-doc-sync.bash`,
   `python3 gen-dependencies.py --check`, `python3 gen-reference.py --check` y `bash check-indice.bash`: antes del
   commit, y en el mismo, los dos `.py` sin `--check` (regeneran) y, si cambió una declaración,
   `bash check-indice.bash --rehacer`.
2. Desbloquear los ficheros `.lean` en los que se ha trabajado:
   `bash git-lock.bash unlock <ficheros>` (para commitear uno bloqueado sin tocar la lista,
   `bash guarda_y_bloquea.bash`: la tabla de scripts)
3. Añadir los cambios al staging area (ficheros concretos, evitar `git add -A`/`*`
   ciego si el conjunto de cambios no se ha revisado antes con `git status`).
4. Crear el commit: `git commit -m "mensaje muy descriptivo de lo hecho"`.
5. Subir al remoto: `git push`.
6. Volver a bloquear los mismos ficheros por seguridad:
   `bash git-lock.bash lock <ficheros>`

> ✏️ **2026‑10‑19 · `master` PROTEGIDO, como el de RPP** (ADR‑168 de RPP; antes ADR‑136 allí). Sólo admite un commit
> cuya comprobación «lake build» de la CI ya salió verde, sin excepción para el administrador; ni force push ni borrar
> la rama. El paso 5 va entonces en tres tiempos:
> 1. `git push origin HEAD:refs/heads/ci/<nombre>` — la CI corre en esa rama (`build.yml` corre en las ramas «ci/…»);
> 2. esperar el verde: `gh run watch` (o `gh run list --branch ci/<nombre>`);
> 3. `git push origin HEAD:refs/heads/master` —un avance rápido hasta lo ya comprobado— y borrar la rama:
>    `git push origin --delete ci/<nombre>`.
>
> M‑12 sigue: FOL antes que RPP. Visto fallar: un commit sin CI empujado a master se rechaza («GH006 … Required status
> check "lake build" is expected»).
>
> ✏️ 2026‑11‑09 (ADR‑262 de RPP): dos reglas de ADR‑204 de RPP valen también aquí. **Tras el avance de `master`, se
> vigila también SU run** (`gh run watch <id> --exit-status`): el push dispara otro run sobre el mismo commit. Y las
> ramas, el stash y los worktrees siguen la M‑2 de `DECISIONS.md`.

---

## Lista de Cumplimiento

Antes de dar por completa y al día la documentación de una sesión, verificar que
`REFERENCE.md` (+ nodos), los ficheros `.lean` y el resto de documentación cumplen:

- [ ] Puntos (0)–(26) de esta guía.
- [ ] Reglas de exportación (§17 «Bloques de exportación», §18 «Barrels»).
- [ ] `NAMING-CONVENTIONS.md` (diccionario de símbolos, REGLA 1–12 de formación de
      nombres, y §5–§8 de estructura de archivos/namespaces/variables/typeclasses).
- [ ] Ningún placeholder `YYYY-MM-DD`/`[Nombre del Autor]` sin rellenar en documentos
      que ya no son plantilla (si esto ES la plantilla, déjalos — son intencionales).
- [ ] `locked_files.txt`/`frozen_files.txt` reflejan el estado real de la sesión, no
      quedan vacíos por inercia.
