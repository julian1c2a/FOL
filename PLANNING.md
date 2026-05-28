# Hoja de Ruta Fundacional — Plan Estratégico

**Última actualización:** 2026-05-16
**Autor**: Julián Calderón Almendros

> Este documento describe la visión estratégica y la planificación a largo plazo. La arquitectura ha crecido: ahora hay **4 lean_libs** en el mismo repositorio.

---

## 1. Visión General

El objetivo es trascender la lógica pura para abordar la **fundamentación de las matemáticas**. El ecosistema actual se compone de:

- **`FOL`** — FOL con igualdad (FOL^=), base estable.
- **`FOLPure`** — FOL sin igualdad, 0 sorries, Completitud y Compacidad totales.
- **`PropLogic`** — Lógica proposicional, 0 sorries.
- **`TheoryFramework`** — Capa genérica (`class LogicSystem`) sobre las tres lógicas.

---

## 2. Arquitectura de Proyectos

### Librería 1: `FOL` — FOL con Igualdad (FOL^=)

- **Rol**: Fundamento Lógico con igualdad.
- **Estado**: Estable. 1 sorry en `Completeness.lean` (caso eq/Henkin, documentado).

### Librería 2: `FOLPure` — FOL sin Igualdad

- **Rol**: FOL pura, sin predicado `=`. 0 sorries. Completitud y Compacidad completas.
- **Estado**: ✅ Completo.

### Librería 3: `PropLogic` — Lógica Proposicional

- **Rol**: Subconjunto de FOL sin cuantificadores. Stack metamatemático completo.
- **Estado**: ✅ Completo.

### Librería 4: `TheoryFramework` — Marco Genérico

- **Rol**: `class LogicSystem (F : Type)` que abstrae las tres lógicas. Permite definir teorías y demostrar propiedades genéricas (consistencia, independencia, extensiones conservativas).
- **Estado**: ✅ Completo.

### Proyecto Externo: `ROBINSON_PlusPlus` (Nuevo Proyecto)

- **Rol**: **Fundamento Aritmético**.
- **Descripción**: Proyecto dedicado a formalizar sistemas axiomáticos para la aritmética sobre `FOL`/`FOLPure`. Objetivo: fundar los naturales, las tuplas y listas.
- **Dependencia**: `FOL` o `FOLPure` + `TheoryFramework`.

### Proyecto Externo: `FOL_Compiler` (Nuevo Proyecto)

- **Rol**: **Especificación Material**.
- **Descripción**: Parser `String → Formula` y pretty-printer `Formula → String`.
- **Dependencia**: `FOL`.

---

## 3. El Proyecto `ROBINSON_PlusPlus` en Detalle

### 3.1. Filosofía y Justificación

Este proyecto aborda la cuestión de "qué se necesita para construir X". La idea de empezar con un sistema minimalista (como la aritmética de Robinson o el sistema de 22 axiomas) no es proponerlo como el sistema final, sino como un ejercicio fundacional para responder a la pregunta: *¿Cuál es la base mínima de la que podemos derivar la función de Cantor y, por tanto, las tuplas y listas?*

La aparente inconsistencia de usar recursión para `+` y `*` pero no para otras funciones es deliberada: se trata de un sistema "eximio" que nos fuerza a adoptar como axiomas propiedades (como la conmutatividad) que intuimos como "obvias" pero que no podemos demostrar sin inducción.

### 3.2. Estructura de Módulos

El proyecto se organizará en tres directorios principales, cada uno representando un sistema axiomático de fortaleza creciente:

1. **`Minimal/`**:
    - **Sistema**: Los 22 axiomas descritos en `TuplasFuncionesYListas.md`. No incluye un esquema de inducción.
    - **Objetivo**: Demostrar que este sistema es suficiente para construir la función de Cantor y, con ella, una teoría de tuplas y listas (Bloques I a VI del documento).

2. **`Intermediate/`**:
    - **Sistema**: Un sistema reducido (13 axiomas) más un **esquema de inducción restringido** a un conjunto finito de fórmulas, como se describe en el Apéndice B de `TuplasFuncionesYListas.md`.
    - **Objetivo**: Demostrar que los 9 axiomas algebraicos y de orden del sistema `Minimal` son ahora **teoremas** derivables del principio de inducción finito.

3. **`Full/`**:
    - **Sistema**: Los axiomas de Peano puros con el **esquema de inducción general** sobre todas las fórmulas del lenguaje (Apéndice C).
    - **Objetivo**: Demostrar que este es el sistema canónico donde todos los demás axiomas (álgebra, orden, TFA, etc.) se convierten en teoremas.

### 3.3. Objetivo de Paridad

El objetivo final de `ROBINSON_PlusPlus` es establecer formalmente los **embeddings** entre estos sistemas:
`Minimal ⊂ Intermediate ⊂ Full`
Esto se logrará demostrando que los axiomas de un nivel son teoremas en el nivel superior.

---

## 4. El Proyecto `FOL_Compiler` en Detalle

Este proyecto se centrará en la ingeniería de software para crear una interfaz tangible con nuestro sistema lógico.

- **Objetivo**: Construir un parser que convierta `String → Formula` y un pretty-printer `Formula → String`.
- **Justificación Fundacional**: Servirá para probar la paridad entre la especificación formal de `FOL=` y un "modelo material" cuyo universo de discurso es el **Universo de Herbrand** (el conjunto de todos los términos). Esto nos permitirá estudiar la relación entre nuestro sistema polimórfico (`Type u`) y un modelo concreto basado en la sintaxis.

---

## 5. El Problema de la Especificación de Lean 4

Un tema transversal a todos los proyectos fundacionales es la necesidad de ser explícitos sobre qué características del sistema anfitrión (Lean 4 y su Cálculo de Construcciones Inductivas) estamos utilizando.

- **Acción**: Cada proyecto (`FOL`, `ROBINSON_PlusPlus`, etc.) deberá mantener un documento `FOUNDATIONS.md`.
- **Contenido**: Este documento actuará como un "diccionario fundacional", explicando el "valor real" de cada primitiva de Lean utilizada. Por ejemplo:
  - "Usamos `inductive Formula ...`. Esto corresponde en nuestra metateoría a la definición de un conjunto por sus reglas de formación y nos concede el principio de inducción estructural sobre las fórmulas."
  - "Usamos `fun x => ...` de Lean, que corresponde al concepto de función en nuestra metateoría."

---

## 6. Hoja de Ruta General

1. **Estabilizar `FOL`**: Considerar la versión actual como `v1.0` y tratarla como una dependencia externa estable.
2. **Iniciar `ROBINSON_PlusPlus`**:
    a. Crear el nuevo proyecto con `FOL` como dependencia.
    b. Establecer la estructura de directorios (`Minimal`, `Intermediate`, `Full`).
    c. Comenzar la implementación de `Minimal/`, traduciendo los 22 axiomas y las primeras fases de `TuplasFuncionesYListas.md`.
    d. El objetivo clave es llegar a la **fundamentación de las listas (Teo L1 y L2)**.
3. **Iniciar `FOL_Compiler`**: Una vez la aritmética esté más avanzada, se puede abordar el parser.
4. **Consolidación**: A largo plazo, los resultados de `ROBINSON_PlusPlus` permitirán refactorizar otros proyectos (como el proyecto Peano existente) para que se apoyen en una base formalmente verificada desde `FOL=`.
5. **Futuro Lejano**: Con una base sólida para la aritmética y los conjuntos finitos (listas), el camino hacia teorías de conjuntos constructivas como la de Aczel (CZF) se vuelve mucho más claro.
