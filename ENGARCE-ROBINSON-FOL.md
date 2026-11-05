# El Engarce Fundacional: FOL, ROBINSON++ y los Tipos Inductivos de Lean 4

**Last updated:** 2026-11-05 — ADR‑258 de RPP: §A, con `FOL.DecEq` entre lo que RPP importa y sin `Lean` en su cierre. Antes, el mismo día — FOL0912:M‑3 de la auditoría de FOL (ADR‑257 de RPP): el engarce que HAY, medido (§A), y el texto de junio, rotulado como lo que es: una hoja de ruta, nada formalizado (§B). Antes, 2026-06-12 —su última revisión con diez líneas nuevas o más, `db24399`—, sin el cuerpo revisado: deuda de contenido de `[E]`, saldada hoy.

> ⛔ **Hasta el 2026‑11‑05 este documento describía un engarce que NO EXISTE.** encodeList, encodeList_bijective,
> IsList, el lema β y los W‑types no aparecen en ningún `.lean` de FOL ni de ROBINSON_PlusPlus (medido con grep ese
> día), y su última frase —«cada flecha es una reducción formalmente demostrada en Lean»— era falsa. No mencionaba lo
> que sí existe: la sintaxis, la semántica y el puente de derivaciones. Lo que existe está en §A; el texto de antes,
> sin tocar, en §B.

## §A · El engarce que HAY (medido el 2026‑11‑05)

1. **La dependencia.** ROBINSON_PlusPlus declara `require FOL from "../FOL"` en su `lakefile.lean`: FOL es una
   dependencia local, construida con el mismo toolchain (M‑1 de aquí, M‑3 de RPP), y RPP registra el FOL que certifica
   en `../ROBINSON_PlusPlus/doc/control/fol-sha.txt`.
2. **Lo que RPP importa**: diez módulos de FOL —`FOL.FOL` (en 20 módulos de RPP), `FOL.Theorems.Eq` (17),
   `FOL.Theorems.Quantifiers` (10), `FOL.Semantics` (2), y `FOL.SymLit`, `FOL.Sentence`, `FOL.Lift0`, `FOL.Derives1`,
   `FOL.Canonical0` y `FOL.DecEq` (uno cada uno; ✏️ éste, desde ADR‑258 de RPP, que retiró su copia)—; de TheoryFramework,
   ninguno. Ninguno le trae ya `Lean` (ADR‑258 de RPP: `FOL.Theorems.Impl` dejó de importar `FOL.Tactics`).
3. **Lo que toma de FOL**: la sintaxis (`Formula`, los términos, la sustitución y el lift), la semántica de Tarski con
   la que construye sus modelos (`evalFormula` y `Model`), la noción de sentencia, los literales de símbolo («sym!») y,
   para el puente, `Derives₀`, `Derives₁` y la existencia de modelo. Las declaraciones de FOL y TheoryFramework que
   alguna constante de RPP nombra directamente son 58 de 1399 (`../ROBINSON_PlusPlus/doc/control/fol-sin-uso.tsv`,
   ADR‑254 de RPP; ✏️ ADR‑258: eran 56 de 1402).
4. **El puente de las derivaciones** (`../ROBINSON_PlusPlus/ROBINSON_PlusPlus/Meta/PuenteFOL.lean`): una derivación de
   FOL desde la teoría da una del cálculo `Prf` de RPP (`prf_of_derivesSet`, T67, ADR‑195 de RPP), y al revés sobre
   las clausuras universales de sus axiomas (`prf_iff_derivesSet_clausuras`, ADR‑253 de RPP); con él, Gödel I y II
   también en la lógica de primer orden de aquí (`goedel_I_fol`).
5. **La aritmetización vive en RPP, no aquí.** El código de una fórmula es `codeNat`
   (`../ROBINSON_PlusPlus/ROBINSON_PlusPlus/Minimal/Axioms.lean`), con el par de Cantor (`consN`: `cons a b = σ (pair a
   b)`, ADR‑113 de RPP) y su inyectividad (`codeNat_inj`, `consN_inj`); en el lenguaje objeto, las funciones sobre
   códigos las dan sus ecuaciones —los 85 axiomas de codificación—, y la inducción de listas es una regla de `Prf`
   (`listInd`), admisible desde la inducción aritmética (ADR‑244 de RPP). Ni lema β ni W‑types.

## §B · PROYECTADO: hoja de ruta, NADA formalizado (el texto de junio de 2026, tal cual)

Este documento detalla la arquitectura lógica y metamatemática necesaria para conectar la sintaxis de primer orden (en `FOL`), la aritmética recursiva (en `ROBINSON++`) y los tipos inductivos nativos de Lean 4 (especialmente listas, tuplas y tipos inductivos bien fundados o W-Types).

El objetivo es establecer un puente de **Interpretabilidad Relativa** que permita justificar formalmente cómo las estructuras de datos inductivas de Lean 4 pueden ser recreadas, interpretadas y demostradas de manera rigurosa dentro de una teoría aritmética de primer orden clásica con inducción restringida.

---

## 1. El Concepto Central: Aritmetización de Estructuras (Gödelización)

En la teoría de tipos inductivos de Lean 4, las listas, árboles y la propia sintaxis (fórmulas, términos, derivaciones) se definen de manera constructiva directa. En cambio, en una teoría de primer orden como `ROBINSON++`, no existen los tipos inductivos como tales; solo disponemos del tipo primitivo de los números naturales ($\mathbb{N}$) y la lógica de primer orden clásica con igualdad ($FOL^=$).

Para conectar ambos mundos, el puente fundamental es la **aritmetización** (o codificación de Gödel):
1. Cada elemento de una estructura finita (como una lista de naturales o un nodo de un árbol sintáctico) se asocia biyectivamente con un único número natural $c \in \mathbb{N}$ mediante funciones de apareamiento (como la función de Cantor).
2. Las operaciones estructurales (como insertar un elemento en una lista o extraer el elemento cabeza) se representan como **funciones aritméticas** o **relaciones binarias funcionales** dentro del lenguaje de primer orden.

---

## 2. Pilares de la Recreación Inductiva en Primer Orden

Para demostrar que los tipos inductivos de Lean 4 pueden ser creados y operados formalmente dentro de `ROBINSON++`, la teoría aritmética debe demostrar como teoremas aritméticos de primer orden los pilares que Lean asume por definición para sus tipos inductivos:

### A. Inyectividad y Disyunción de los Constructores
En Lean 4, al declarar `inductive List`, el compilador asume por definición que los constructores son disjuntos (`nil ≠ cons x xs`) y que `cons` es inyectivo. En `ROBINSON++`, debemos demostrar estas propiedades formalmente a partir de los axiomas del apareamiento aritmético:

* **Disyunción (Axioma de Aritmeticidad):**
  $$\text{ROBINSON++} \vdash \forall x\ l, \ \text{code\_nil} \neq \text{code\_cons}(x, l)$$
  
* **Inyectividad de Constructores:**
  $$\text{ROBINSON++} \vdash \forall x\ y\ l_1\ l_2, \ \text{code\_cons}(x, l_1) = \text{code\_cons}(y, l_2) \implies x = y \land l_1 = l_2$$

*(Esto se demuestra directamente utilizando las propiedades de inyectividad y las funciones de proyección izquierda/derecha de la función de apareamiento de Cantor).*

---

### B. La Demostración del Principio de Inducción Estructural
Lean 4 genera automáticamente el principio de inducción estructural `List.rec` para realizar pruebas sobre listas. Para recrear este principio en `ROBINSON++`, debemos demostrar el **meta-teorema de inducción estructural** para cualquier fórmula $\varphi$ del lenguaje de primer orden:

$$\text{ROBINSON++} \vdash \varphi(\text{code\_nil}) \land (\forall x\ l, \ \varphi(l) \to \varphi(\text{code\_cons}(x, l))) \to \forall l, \ \text{IsList}(l) \to \varphi(l)$$

#### Estrategia de Prueba dentro de `ROBINSON++`:
Dado que en primer orden solo disponemos de la inducción matemática ordinaria sobre los números naturales ($\mathbb{N}$), la demostración procede de la siguiente manera:
1. **Definir la Longitud Aritmética:** Se define una relación funcional $\text{len}(l, n)$ en primer orden que calcula la longitud $n$ de la lista codificada $l$.
2. **Inducción Matemática sobre la Longitud:** Se aplica el axioma de inducción matemática estándar sobre la variable $n$:
   * **Caso Base ($n=0$):** Se demuestra que la única lista de longitud 0 es `code_nil`, y dado que $\varphi(\text{code\_nil})$ se asume, la propiedad se cumple.
   * **Paso Inductivo ($n \to n+1$):** Se demuestra que cualquier lista de longitud $n+1$ es de la forma `code_cons(x, l)` para alguna lista $l$ de longitud $n$. Aplicando la hipótesis de inducción para $l$ y el paso inductivo estructural $\varphi(l) \to \varphi(\text{code\_cons}(x, l))$, se concluye la propiedad para la lista de longitud $n+1$.
3. **Generalización:** Puesto que toda lista válida $\text{IsList}(l)$ posee una longitud finita $n \in \mathbb{N}$, la inducción matemática ordinaria concluye que la propiedad $\varphi(l)$ vale para todas las listas.

---

### C. Existencia y Unicidad de Funciones Recursivas
En Lean 4, las funciones sobre tipos inductivos se definen mediante recursión y *pattern matching*. En primer orden, las funciones se representan como **relaciones binarias funcionales** ($R(x, y)$ tal que $\forall x, \exists! y, R(x, y)$).

Para recrear funciones recursivas (como `map`, `filter` o `fold`) dentro de `ROBINSON++`, debemos demostrar el **Teorema de Recursión General**:
1. **El Historial de Computación:** Se utiliza el **Lema $\beta$ de Gödel** para empaquetar toda la traza de computación (la secuencia de estados de la evaluación recursiva) en un único número natural $h$.
2. **Definibilidad de la Relación:** Se demuestra que existe una fórmula aritmética que valida que $h$ es un historial coherente de evaluación para una entrada dada.
3. **Demostración de Funcionalidad:** Se demuestra usando inducción matemática en la longitud de la entrada que para toda lista existe un único historial coherente, garantizando así la existencia y unicidad del resultado de la función recursiva.

---

## 3. El Isomorfismo Semántico (El Engarce Final)

El engarce definitivo se completa en la metateoría de Lean 4 al demostrar la paridad semántica entre el tipo inductivo nativo y su contraparte aritmética codificada:

1. **La Codificación Formal:**
   Se define en Lean una función de codificación computable que mapea el tipo inductivo real a los números naturales:
   ```lean
   def encodeList : List Nat → Nat
     | [] => code_nil
     | x :: xs => code_cons x (encodeList xs)
   ```

2. **Demostración del Isomorfismo:**
   Se demuestra en Lean que `encodeList` establece una **biyección** entre el tipo inductivo nativo `List Nat` y el subconjunto de números naturales que satisfacen el predicado lógico `IsList` demostrado en `ROBINSON++`:
   ```lean
   theorem encodeList_bijective : Bijective encodeList := by ...
   ```
   Esto asegura que trabajar con el tipo inductivo nativo de Lean y trabajar con los números que satisfacen la teoría aritmética de primer orden son aproximaciones **isomorfas y fundacionalmente equivalentes**.

---

## 4. El Camino hacia Aczel (W-Types y Conjuntos)

Este puente aritmético sobre tuplas y listas es el cimiento necesario para modelar estructuras infinitas bien fundadas. 

Al haber demostrado la existencia y la inducción de listas/árboles en `ROBINSON++`, obtienes la capacidad de representar y codificar sintácticamente los **W-Types** (árboles inductivos bien fundados de Peter Aczel) que sirven para modelar la teoría de conjuntos clásica y constructiva (`CZF` / `ZFC`). 

La correspondencia fundacional queda así unificada:
$$\text{FOL} \longrightarrow \text{ROBINSON++} \longrightarrow \text{W-Types / Bisimilitud} \longrightarrow \text{ZFC / CZF Model}$$

Donde cada flecha es una reducción formalmente demostrada en Lean, garantizando que todo el edificio matemático se apoya de forma explícita y transparente sobre los axiomas lógicos mínimos de primer orden. *(✏️ 2026‑11‑05, FOL0912:M‑3: FALSO. Ninguna de estas flechas está formalizada; lo formalizado, en §A.)*
