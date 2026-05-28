# Próximos Pasos — FOL

**Última actualización:** 2026-05-16
**Autor**: Julián Calderón Almendros

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
