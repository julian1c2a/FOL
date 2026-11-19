# T71, preguntas 3 y 4 — el estudio de viabilidad de la 3 y lo hecho de la 4 (2026‑11‑19)

**Last updated:** 2026-11-19 — ADR‑275 de RPP: el plan de §1, HECHO (la nota de §1). Antes, el mismo día — creado con ADR‑274 de RPP.

**Sobre:** FOL `3f86996` y este cambio · Lean v4.35.0 · **Autor:** Julián Calderón Almendros, con Claude ·
**Decisión:** ADR‑274 de `../../../ROBINSON_PlusPlus/DECISIONS.md` · **Las preguntas:**
`../t71-semanticos-2026-10-29/README.md`, «Lo que queda abierto», y `../d1-2026-11-18/README.md` · **Lo medido, en el
build:** `../../FOL/EsencialidadSem0.lean`, E12

## Qué es esta carpeta

T71 dejó cuatro preguntas abiertas; D1 hizo la 1 y la 2. Para la 3 y la 4, el propietario decidió (2026‑11‑19):

* **La 3:** primero un estudio de viabilidad, con una estimación etiquetada; después decide si se pasa a Lean. El
  alcance, si se hace: la compacidad y los dos numerables (LS↓ y `countable_infinite_of_infinite`).
* **La 4:** la bibliografía primero, compilar la reducción y buscar un contramodelo en papel.
* **El método:** en solitario, con un escéptico al final.

| # | la pregunta | lo de hoy | cómo se sabe |
|---|---|---|---|
| 3 | ¿Bastan WLEM + ¬¬EM para los cinco semánticos? | **Viable.** Que la existencia de modelo equivale a WLEM está publicado (Herbelin y Kirst, 2023); en FOL sólo está compilada la dirección fácil (E7). La difícil —el modelo canónico sin elección, con la elevación de las listas de clases— no está hecha. La consistencia de lo satisfacible equivale a ¬¬EM (argumentado aquí) | §1: la bibliografía, lo MEDIDO de FOL y el plan; ESTIMACIÓN |
| 4 | ¿KSst es estrictamente más fuerte que WKS sin Markov? | **Reducida:** KSst ⟺ toda `P` estable tiene un representante de WKS con Markov. En los modelos de haces sobre espacios de Stone, la separación es un problema de topología | E12 MEDIDO; §2, ARGUMENTADO 🟡 |

## §1 · Pregunta 3: el estudio de viabilidad

### La bibliografía

Cómo se leyó cada fuente:

* **Leídos directamente:** el resumen de Herbelin–Kirst (el PDF de su web), el texto de Kirst–Zeng (arXiv, v2) y las
  transparencias de Moschovakis (2018).
* **Por el resumen de una herramienta de lectura, no por mí:** van Atten (2018).
* **De memoria, sin referencia comprobada:** lo de Ščepin y la κ‑normalidad perfecta.
* **No visto:** Krol' (1978).

* **Herbelin y Kirst, TYPES 2023**, «New Observations on the Constructive Content of First‑Order Completeness
  Theorems». Su ámbito: contextos arbitrarios, signatura numerable, toda la sintaxis y semántica en `Prop`.
  * **Teorema 2:** la existencia de modelo (todo contexto consistente tiene modelo) **equivale a WLEM**. En un sentido,
    WLEM convierte las teorías estables «cuasi primas» en primas. En el otro, es el testigo
    `{P₀ ∨ ¬P₀} ∪ {P₀ | p} ∪ {¬P₀ | ¬p}`, el de nuestro E7.
  * **Teorema 1:** la cuasi‑completitud (`Γ ⊨ φ → ¬¬(Γ ⊢ φ)`) equivale a **WLEMS**,
    `∀p : ℕ → Prop, ¬¬∀n (¬p n ∨ ¬¬p n)`. WLEMS se sigue de DNS y de WLEM.
* **Kirst y Zeng, arXiv 2601.12592 (2026)**, sobre el LS↓ «elemental». Dicen que su forma débil, la de la existencia de
  modelo (un modelo elementalmente equivalente), sólo pide WLEM [Herbelin–Kirst], y que no conocen una prueba de que
  la pida. Es otro enunciado que el nuestro.
* **Forster, Kirst y Wehr (2021):** la existencia de modelo, constructiva en el fragmento negativo; con EM, para toda
  la sintaxis.

FOL ya tiene compilada una mitad del Teorema 2: E7 de `FOL.Esencialidad0`, `model_existence_stmt_implies_wlem`. Lo que
falta es la otra, la de WLEM a la existencia de modelo, y lo que añade la 3: la consistencia de lo satisfacible.

### Lo MEDIDO de FOL

`p3-huellas.lean.txt` y su salida, `p3-huellas-salida.txt`: 159 constantes, salida 0.

* **Sin `Classical.choice`:**
  * Lindenbaum y Henkin, con la etapa sin decidir. El límite concreto está CERRADO por derivación sin tercio excluso
    (`lindenbaum_limit_closed`), y el testigo de Henkin de cada `A` está en él (`henLimit_witness`).
  * El cambio de lenguaje (`shiftTheory`, `satisfiable_of_shift`, `countable_of_shift`, `hasLargeModels_shift`) y la
    teoría de los modelos grandes (`infTheory_finSat`).
  * La enumeración de los términos (`natToTerm_surj`), la sustitución semántica (`eval_substFormula_ext`) y la
    solidez para los modelos ESTABLES (`Esencialidad0.E2.sound_stable`).
* **Con `Classical.choice`:**
  * Todo el modelo canónico de `Canonical0`: `termSetoid`, `listQuot`, `canonicalModel`, `truth_lemma₀`, los
    `max_cons_*`.
  * La solidez (`derives0_soundness`) y `consistency_of_satisfiable₀`.
  * El origen es uno: `max_cons_contains` es `Classical.byContradiction` sobre un enunciado `¬¬` que se prueba sin
    nada (`Lindenbaum0.lean`, línea 284).

### El plan (si el propietario lo aprueba)

> ✏️ 2026‑11‑19 (ADR‑275 de RPP): **el propietario lo aprobó entero, con los dos sentidos del paso 3, y está HECHO**:
> `../../FOL/EsencialidadCota0.lean`, 18 teoremas, como mucho `[propext, Quot.sound]` y ninguno con
> `Classical.choice` (`medidas-cota-2026-11-19.txt`). Compiló a la primera; son 540 líneas (`wc -l`), dentro de la
> ESTIMACIÓN de 500 a 900. La elevación de las listas, el riesgo que señaló el escéptico, no arrastró nada.

Un módulo nuevo de FOL. Sólo IMPORTA los congelados, sin thaw (el protocolo de `git-lock.bash`: lo nuevo va en otro
fichero). Cuatro piezas:

1. **El modelo canónico DOBLEMENTE NEGADO**, sobre el límite concreto `T := LindenbaumLimit (henLimit S)`:
   * el dominio, los términos módulo `t ≈ u :⟺ ¬¬T(t = u)`;
   * los átomos, `¬¬T(R t̄)`.

   Es el de `Canonical0` con la relación negada dos veces; la construcción del cociente se rehace.

   ⚠️ **Lo más delicado:** el modelo pide `func : List D → D` y `rel : List D → Prop` sobre el cociente, y hace falta
   elevar las listas de clases sin elección, por recursión sobre la lista (lo que en `Canonical0` es `listQuot`). Si
   algo arrastra `Classical.choice`, es esto.
2. **El lema de la verdad, `M ⊨ f ⟺ ¬¬T f`**, caso a caso:

   | caso | qué lo da |
   |---|---|
   | ⊥ | la consistencia |
   | átomo, `=` | la definición |
   | `∧`, `→` | el cierre y la maximalidad, sin nada |
   | `∨` | WLEM, como De Morgan |
   | `∀` | dentro de `¬¬`, la maximalidad da `T ⊢ ¬∀x A`, y de ahí `T ⊢ ∃x ¬A` (un paso clásico, válido en `Derives₀`); el límite cerrado da `T(∃x ¬A)`, y su testigo de Henkin contradice la hipótesis de inducción |
   | `∃` | `henLimit_witness` da la constante sin decidir nada |

   El resultado: `WLEM → IsConsistent₀ S → IsSatisfiableCountable S`, y con E7, **existencia de modelo ⟺ WLEM**.
3. **La consistencia de lo satisfacible ⟺ ¬¬EM.**
   * (⇐) `sound_stable`: la meta, `¬(S ⊢ ⊥)`, es negativa, y dentro de ella vale EM.
   * (⇒) `{σ}`, el de E11, es satisfacible si `¬EM` y deriva `⊥` en el cálculo clásico. Hace falta esa derivación,
     con un `∀`‑intro.
4. **Los semánticos, con las pruebas cortas de `Compacity0` rehechas sobre 2 y 3:**
   * la compacidad (la finita satisfacibilidad da la consistencia por 3, y el modelo por 2);
   * LS↓ y `countable_infinite_of_infinite`, el alcance decidido;
   * los dos de §3, si salen con lo mismo.

**Lo que respondería:** los cinco quedan entre WLEM (E8, E10: lo implican) y WLEM + ¬¬EM (los implica). La
compacidad ⟹ ¬¬EM sigue abierta (D1). Es el hueco exacto, y no está en la ruta: (3) pide ¬¬EM porque el camino pasa
por la consistencia, pero la compacidad podría no pasar por ahí.

**ESTIMACIÓN** (no medida): de 500 a 900 líneas, una sesión. Lo más largo es rehacer el cociente y el lema de la verdad
(unas 400 líneas en `Canonical0`). Los riesgos:

* lemas auxiliares de `Canonical0` que hereden `Classical.choice` del `termSetoid` y haya que rehacer;
* la derivación de `⊥` desde `σ` (sólo para el (⇒) de 3, que es opcional);
* el camino de §3 por el cambio de lenguaje.

## §2 · Pregunta 4: lo hecho

### La bibliografía

* **Los nombres.** Nuestro WKS (`¬P ⟺ ∀n ¬β n`) es el «WWKS» de Moschovakis («A Logical Look at Kripke's Idea of
  Choice Sequence», 2018) y el KS⁻ de Dragálin, que es sólo la bi‑implicación. El WKS de Kripke, Myhill y Troelstra es
  el BKS⁻ de van Atten y el KS′ de Kirst–Zeng. Para una `P` estable, nuestro WKS implica ese BKS⁻ (`wks_stable_bks`).
  KSst es el KS de siempre restringido a las `P` estables.
* **Krol' (1978)**, «Distinct variants of Kripke's schema in intuitionistic analysis» (Soviet Math. Dokl. 19,
  474–477). Demuestra la conjetura de Scott, BKS⁻ más débil que BKS⁺, con un modelo topológico del análisis
  intuicionista. Es para proposiciones cualesquiera. No conseguí el texto, ni la reseña de J. Moschovakis (JSL 46,
  1981, 660–661), así que no sé si la proposición que separa es estable. Si lo es, la 4 está resuelta para ese
  sistema, pero no para Lean.
* **Kirst y Zeng (2026)** dibujan KS ⟹ KS′ como implicación «presumiblemente estricta»: en su marco (CIC) no la dan
  por demostrada.
* **Moschovakis (1980)**, citado por van Atten (Teorema 55): BKS⁻ + MP ⟹ DNE.

### Lo MEDIDO: E12 de `FOL.EsencialidadSem0` (tres teoremas sin ningún axioma)

* **`ksst_iff_rep_mp`:** KSst ⟺ toda `P` estable tiene un representante de WKS (una sucesión decidible nula si y sólo
  si `¬P`) que cumple Markov.
* **`wks_mp_implies_ksst`:** WKS más Markov para las sucesiones decidibles implica KSst. Es la de
  `../t71-semanticos-2026-10-29/a2-LSWKS.lean`, ya en el build.
* **`wks_stable_bks`:** para `P` estable, un representante de WKS cumple BKS⁻.

La pregunta queda así: ¿da WKS, para cada `P` estable, ALGÚN representante con Markov? Los representantes de una
misma `P` dan el mismo `¬¬∃n β n`, pero Markov para uno no lo da para otro.

### El contramodelo en papel (ARGUMENTADO, 🟡; sin ejemplo)

* **Por qué los modelos de Kripke no sirven:** con ℕ constante, una sucesión decidible en un nodo es clásica desde
  él, vale Markov y las dos coinciden.
* **Los haces sobre el espacio de Stone `X` de un álgebra de Boole `A`.** Las proposiciones decidibles son los
  abiertos‑cerrados. La validez interna se reduce a los abiertos‑cerrados, porque un recubrimiento de un compacto
  tiene uno finito por abiertos‑cerrados. Así:
  * **WKS** vale si y sólo si todo abierto regular contiene un abierto denso que es unión numerable de
    abiertos‑cerrados (en `A`: todo elemento de la compleción es supremo de una familia numerable de `A`). Basta que
    `A` sea ccc: una anticadena maximal dentro del abierto regular.
  * **KSst** vale si y sólo si todo abierto regular es unión numerable de abiertos‑cerrados (todo ideal normal de `A`
    está numerablemente generado). En un compacto cero‑dimensional, eso es que todo abierto regular sea F_σ: `X` es
    **perfectamente κ‑normal**.
* **⇒ Una separación espacial** pide un compacto cero‑dimensional con la propiedad de densidad (por ejemplo, ccc) que
  no sea perfectamente κ‑normal. Ninguno de los candidatos naturales sirve:
  * los cubos `2^κ` son perfectamente κ‑normales (Ščepin), y en ellos los abiertos regulares dependen de numerables
    coordenadas;
  * las álgebras completas: todo ideal normal es principal;
  * las de intervalos de un orden ccc: un abierto es unión numerable de intervalos, cada uno de carácter numerable;
  * `ω₁ + 1`: fallan las dos, con el abierto regular de los puntos aislados `λ + 1`, `λ` límite. Es no acotado, y
    cerca de `ω₁` un abierto‑cerrado dentro de él es finito.

  No encontré en la bibliografía un compacto ccc que no sea perfectamente κ‑normal. Queda como la forma precisa de la
  pregunta, en este tipo de modelos. Un modelo no espacial (realizabilidad) podría ser otro camino.
* ⚠️ **El alcance** (lo señaló el escéptico): un topos de haces es un modelo de la lógica de orden superior
  intuicionista, no de la teoría de tipos de Lean. Una separación así lo sería en ese marco. Para Lean hace falta
  además el hueco común de T71 y D1: que Lean sin `Classical.choice` sea correcto en el topos, con sus universos.

**El veredicto del escéptico** (2026‑11‑19; leyó el registro, E12 y las fuentes de FOL, sin recompilar):

* **Sin fallo:**
  * el plan del lema de la verdad, caso a caso, incluidos `∀`, `∃` (el testigo sale fuera de la doble negación) y
    `∨` (De Morgan desde WLEM);
  * la consistencia de lo satisfacible ⟺ ¬¬EM, en los dos sentidos;
  * que en `Compacity0` no quede otro ingrediente clásico;
  * E12;
  * la reducción espacial.
* **Huecos, arreglados aquí:**
  * la elevación de las listas no estaba nombrada como riesgo;
  * la cabecera decía «la mitad ya se conoce», sin decir que lo difícil no está hecho;
  * las atribuciones no decían cómo se leyeron;
  * el alcance de los modelos de haces;
  * el abierto de `ω₁ + 1`, sin decir cuál era.

## Lo que queda abierto

* **La 3:** la decisión del propietario sobre el plan de §1. Si se hace, queda la compacidad ⟹ ¬¬EM, la pregunta 2
  de D1 para la compacidad.
* **La 4:** si WKS da representantes con Markov; espacialmente, un compacto cero‑dimensional ccc que no sea
  perfectamente κ‑normal; el contenido de Krol' (1978).

## Los ficheros

| fichero | qué es |
|---|---|
| `p3-huellas.lean.txt` | la medida de §1: `#print axioms` de las 159 constantes de `Lindenbaum0`, `Canonical0`, `HenkinLimit0`, `Compacity0`, `Fresh0` y `Henkin0` (las de `doc/indice.tsv`, sin constructores ni sintaxis) y de las sueltas que usaría el plan |
| `p3-huellas-salida.txt` | su salida, con el código de salida de `lean` |
| `medidas-cota-2026-11-19.txt` | la salida de `lake env lean ../FOL/FOL/EsencialidadCota0.lean`, con su código de salida: los 18 teoremas del plan de §1 |
| `medidas-2026-11-19.txt` | la salida de `lake env lean ../FOL/FOL/EsencialidadSem0.lean`, con su código de salida, y las tres líneas de E12, literales |
