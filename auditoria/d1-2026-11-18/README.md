# D1 — las preguntas 1 y 2 que T71 dejó abiertas (2026‑11‑18)

**Last updated:** 2026-11-18 — creado con D1 (ADR‑273 de RPP).

**Sobre:** FOL `3770333` y este cambio · Lean v4.35.0 · **Autor:** Julián Calderón Almendros, con Claude ·
**Decisión:** ADR‑273 de `../../../ROBINSON_PlusPlus/DECISIONS.md` · **El plan:**
`../../../ROBINSON_PlusPlus/doc/PLAN-A7-A9-B1-D1.md` §5 · **Las preguntas:** `../t71-semanticos-2026-10-29/README.md`,
«Lo que queda abierto» · **Lo medido, en el build:** `../../FOL/EsencialidadSem0.lean`, E11

## Qué es esta carpeta

T71 (ADR‑220 y ADR‑221 de RPP) clasificó los cinco semánticos de `FOL/Compacity0.lean` y dejó cuatro preguntas
abiertas. El propietario eligió las dos primeras (D1); la 3 y la 4 siguen escritas como problemas abiertos.

| # | la pregunta | la respuesta | cómo se sabe |
|---|---|---|---|
| 1 | ¿El enunciado de la compacidad implica Markov para las ecuaciones diofánticas, como el de la completitud? | **No.** Y, con un paso sólo esbozado, ninguno de los cinco | ARGUMENTADO con un modelo (§1), 🟡 |
| 2 | ¿Alguno de los cinco implica DNS o ¬¬EM? | Para los cuatro que dan modelos numerables, las dos preguntas son UNA | MEDIDO (E11, sin ningún axioma) |
| | | LS↓ y `countable_infinite_of_infinite`: no implican ninguna de las dos | ARGUMENTADO (§2), 🟡 |
| | | La compacidad y los dos de §3: sigue abierta | lo intentado, en §2 |

Lo MEDIDO lo dice `medidas-2026-11-18.txt`: la salida literal de `lake env lean` sobre el módulo, con su código de
salida. Lo ARGUMENTADO son argumentos de modelos, como los de T71, con el mismo hueco común: se supone, sin
formalizarlo, que Lean sin `Classical.choice` es correcto en los modelos usados.

## §1 · Pregunta 1: la compacidad no implica Markov diofántico

### Dónde se rompe el molde de `Markov0`

`FOL/Markov0.lean` saca `∃ν, p(ν) = q(ν)` de `¬¬∃ν` en cinco pasos. El que hace el trabajo es el 3. El enunciado de la
completitud convierte la validez de `¬¬kreiselF` en una DERIVACIÓN, que es un objeto finito. Después, Herbrand y el
modelo estándar la convierten en el testigo. La compacidad no da ningún objeto finito, y sólo se puede usar de dos
maneras:

* **Hacia delante**, da un modelo. Lo que un modelo dice de su teoría es negativo, o una disyunción finita
  (`info_negativa`, en `../t71-semanticos-2026-10-29/b1-Colapso.lean`). El testigo de Kreisel–Markov tiene un modelo
  sin ninguna hipótesis (`colapso_MP`).
* **Contrarrecíproca**, de la teoría de Herbrand `H := {¬ instancia de la matriz}`, que es insatisfacible si `¬¬∃ν`,
  sólo da `¬¬∃Γ`: algún trozo finito de `H` es insatisfacible, pero no cuál. Encontrar ese `Γ` es Markov para un
  predicado decidible, y el argumento vuelve al punto de partida.

### Por qué los modelos de T71 no lo separaban

**Markov para CÓDIGOS vale en todo topos de Grothendieck sobre `Set`**, sobre cualquier sitio (y en el efectivo,
donde vale Markov entero).

* Un código `(p, q)` es una sección del haz constante `Poly`, así que es localmente constante.
* `Poly.eval` sólo mira las `k` primeras coordenadas de `ν`, así que `∃ν : ℕ → ℕ` equivale a `∃x̄ ∈ ℕ^k`, y `ℕ^k` es
  constante.
* En cada trozo donde el código es constante, la existencia de una solución se decide en `Set`: hay una solución
  constante, o ninguna sección local lo es, porque dos numerales distintos son iguales sólo en el abierto vacío.
* Así el valor de verdad de `∃ν` tiene complemento, y es ¬¬‑estable.

Los modelos de Kripke, los de `βℕ` y los de Cantor de T71 cumplen todos Markov diofántico. Lo que falla en `βℕ` es
Markov para SUCESIONES: `n ↦ χ_{n}` no es localmente constante como sucesión. Para separar Markov diofántico hace falta
un modelo en el que un enunciado Σ₁ sobre un código ESTÁNDAR cambie de verdad de una etapa a otra, es decir, con una
etapa de aritmética no estándar.

### El modelo

* **Los ingredientes.**
  * `T` es ZFC más los inaccesibles que pidan los universos de Lean. `M` es un modelo (de conjunto) de `T + ¬Con(T)`,
    que existe si `T` es consistente (Gödel II).
  * ⚠️ El `¬Con` tiene que ser el de `T`, no el de ZFC: un modelo con un inaccesible ya cumple Con(ZFC). Lo vio el
    escéptico; la primera redacción decía ZFC + ¬Con(ZFC), y ese modelo no existe.
  * `E` es el topos de los conjuntos de `M`: bien punteado, booleano, con elección, y con un objeto de números
    naturales `ω^M` no estándar. Es un topos elemental pequeño, no de Grothendieck, y por eso no le alcanza lo de
    arriba.
  * `Γ : E → Set` lleva `X` a `{x | M ⊨ x ∈ X}`, y es exacto por la izquierda.
* **El pegado.** `Gl` es el pegado de Artin de `Set` a lo largo de `Γ`. Sus objetos son `(X₁ ∈ E, X₀ conjunto,
  X₀ → Γ X₁)`. Su lógica es la de Kripke sobre `{0 < 1}`: el nodo 1 es `E`, clásico, y el nodo 0 es `Set` visto a
  través de `Γ`. Los valores de verdad globales forman una cadena de tres.
* **Markov diofántico falla en 0.**
  * MRDP es un teorema de PA, y por tanto vale también en `M`. Da un par estándar `(p, q)` con
    `∃ν p(ν) = q(ν) ⟺ ¬Con(T)`.
  * En el nodo 1 tiene solución, no estándar.
  * En el nodo 0 no. Un `ν` allí es un par compatible `(ν₀, ν₁)`: la compatibilidad obliga a `ν₁` a llevar numerales
    estándar a numerales estándar, y la ecuación es la de `ν₀` en ℕ, que no tiene solución si `Con(T)` es cierta.
  * Por tanto `¬¬∃ν` vale en 0 y `∃ν` no.
* **La compacidad vale en 0.**
  * La teoría interna es `S` (`S₀ ⊆ Formula`, `S₁ ∈ M`, con `S₀ → Γ S₁`). Su satisfacibilidad finita interna en 0
    incluye la del nodo 1, así que la compacidad de `M` da `N₁ ∈ M` con `N₁ ⊨ S₁`.
  * El modelo pegado es `(N₁, Γ N₁, id)`. El forzamiento en 0 de una fórmula con parámetros en `Γ N₁` es la verdad en
    `M`. Se ve por inducción: los átomos, por definición; `→` y `∀`, porque el nodo 1 es clásico y bien punteado; `∃`,
    porque `M` tiene elección y un `∃` verdadero en `M` tiene un testigo global.
  * Toda `f ∈ S₀` está en `S₁`, así que se fuerza en 0. La otra dirección de la compacidad es un teorema sin choice.
* **Los otros cuatro, ESBOZADO** (un paso más débil que el de la compacidad). Con `D₀ = Γ N₁` el argumento no
  sirve: `CountableDom` pide que todo `d ∈ D₀` sea `e(n)` con `n` ESTÁNDAR.
  * El modelo de `M` se toma numerable en `M`, y además infinito, con su inyección `ι`, para
    `countable_infinite_of_infinite` y §3.
  * `D₀` son los valores de los términos de Skolem ESTÁNDAR: los de las funciones de Skolem de `M` para las fórmulas
    estándar, sobre el entorno y los `ι(k)` con `k` estándar.
  * El forzamiento en 0 es la verdad en `M`: Tarski–Vaught con las funciones de Skolem, que sólo hace falta para las
    fórmulas estándar, las únicas del nodo 0.
  * ⚠️ Lo que falta: construir en `M` la enumeración `e₁` de modo que su parte estándar enumere exactamente `D₀`.
    Hace falta un código de los términos cuyos números estándar sean los de los términos estándar, y que `D₀` sea
    cerrado bajo los símbolos de nombre estándar. Es plausible, pero no está hecho.
* **El resto del modelo.**
  * Valen en él WLEM, DNS y ¬¬EM, porque la raíz ve un nodo clásico. Fallan EM y la elección.
  * El enunciado de la completitud falla, como debe: implica Markov diofántico (ADR‑220).

**Los huecos**, además del común:

* que el pegado interprete los universos de Lean (el pegado a lo largo de un funtor exacto por la izquierda, al estilo
  de Shulman) y sus tipos inductivos (`Formula`, `Poly`, `Model`) en un topos elemental pequeño;
* para los cuatro numerables, la enumeración `e₁` de arriba.

**El veredicto del escéptico** (2026‑11‑18; leyó el README y E11, sin recompilar):

* Sin fallo en Markov para códigos en los topos de Grothendieck, ni en el pegado y su lógica de Kripke.
* Sin fallo en que Markov diofántico falle en 0, ni en la inducción del forzamiento de la compacidad.
* Hueco en el modelo `M` (arreglado: `T + ¬Con(T)`) y en la `e₁` de los cuatro numerables (escrito arriba).

**Lo que se sigue.**

1. La compacidad no implica Markov diofántico (🟡). Los otros cuatro, tampoco, con el hueco de `e₁` (🟡, más débil).
2. El enunciado de la compacidad no implica el de la completitud.
3. El `Classical.choice` de los dos teoremas es de naturaleza distinta. El de `completeness₀` contiene una BÚSQUEDA
   (Markov). El de `compactness` no contiene ninguna; contiene una DECISIÓN (WLEM, E8).

## §2 · Pregunta 2: DNS y ¬¬EM

### Lo MEDIDO: E11 de `FOL.EsencialidadSem0` (15 teoremas, ninguno con axiomas, ni `propext`)

Aquí, `EM := ∀P, P ∨ ¬P` es UNA proposición, y `¬¬EM` su doble negación. La de cada instancia es un teorema.
`DNS := ∀P : ℕ → Prop, (∀n ¬¬P n) → ¬¬∀n P n`. La pieza clave es una sola fórmula, `σ := ∀x ¬¬R x ∧ ¬∀x R x`, que es
clásicamente insatisfacible.

| teorema | dice |
|---|---|
| `sat_sigma_iff_not_em` | `σ` es satisfacible ⟺ `¬EM` (el modelo: dominio `Prop`, `R P := P ∨ ¬P`) |
| `nnem_iff_unsat_sigma` | `¬¬EM` ⟺ `σ` no tiene modelo |
| `dns_iff_unsatCountable_sigma` | DNS ⟺ `σ` no tiene modelo NUMERABLE (la enumeración lleva el `∀d` del dominio a un `∀n`) |
| `nnem_implies_dns` | `¬¬EM ⟹ DNS`, en lógica pura |
| `ls_down_stmt_dns_implies_nnem`, `countable_infinite_stmt_dns_implies_nnem`, `infinite_large_stmt_dns_implies_nnem`, `infinite_large_fresh_stmt_dns_implies_nnem` | con el enunciado de cada uno, DNS ⟹ ¬¬EM: el modelo `Prop × ℕ` de `σ`, que existe si `¬EM`, es infinito y tiene modelos de todo tamaño, y el enunciado lo vuelve numerable |
| `ls_down_stmt_nnem_iff_dns` | con LS↓, ¬¬EM ⟺ DNS |

Con esto, para los cuatro que dan modelos numerables, «¿implica DNS?» y «¿implica ¬¬EM?» son la MISMA pregunta:
«¿refuta la satisfacibilidad numerable de `σ`?». La compacidad no da modelos numerables, y para ella las dos preguntas
siguen separadas. Los controles de no vacuidad (`example`, con los teoremas REALES y con `Classical.em`) están en el
módulo, y las hipótesis son los enunciados reales por las identidades de tipos de su cabecera.

### Lo ARGUMENTADO

* **LS↓ y `countable_infinite_of_infinite` no implican ni DNS ni ¬¬EM** (🟡). El modelo son los haces sobre el
  espacio de Cantor `C`, donde T71 argumentó (🟡, «el paso central sin verificar») que valen los dos enunciados. Allí
  fallan DNS y ¬¬EM:
  * **DNS.** Sea `(x_n)` densa y `U_n := C \ {x_n}`. Cada `U_n` es un abierto denso (`C` no tiene puntos aislados),
    así que `¬¬P_n = ⊤`. Pero `⋂ U_n = C \ {x_n | n}` tiene interior vacío, así que `∀n P n` vale `∅` y su doble
    negación también.
  * **¬¬EM.** Ningún abierto no vacío `V` tiene haces booleanos: `V \ {x}` es abierto y no cerrado en `V`. Así
    `⟦EM⟧ = ∅`, y su doble negación también.

  Cuadra con E11: bajo LS↓, las dos van juntas.
* **Una consecuencia de E11, sin más hipótesis.** En todo modelo en el que DNS valga y ¬¬EM no, fallan LS↓,
  `countable_infinite_of_infinite` y los dos de §3. Un ejemplo es el modelo de Kripke sobre `ω₁`, una cadena sin
  máximo y de cofinalidad no numerable:
  * DNS vale: una familia numerable de conos `↑α_n` se corta en `↑sup α_n`.
  * ¬¬EM falla: no hay nodos maximales.
  * WLEM sí vale, porque el marco es dirigido.
* **La compacidad y §3.**
  * Todos los modelos conocidos de ellos tienen un conjunto DENSO de puntos clásicos, y en todos valen DNS y ¬¬EM:
    Kripke finito con máximo, los haces sobre `βℕ` y el pegado de §1.
  * Hay dos candidatos a contramodelo, y no se sabe si la compacidad vale en ninguno:
    * **Kripke sobre `ω`.** Vale WLEM; fallan DNS y ¬¬EM; vale `¬EM`, así que `σ` tiene modelo, incluso numerable.
    * **Los haces sobre un espacio extremadamente disconexo sin puntos aislados** (el recubrimiento de Gleason de
      Cantor, separable por su π‑base numerable). Vale WLEM; DNS y ¬¬EM fallan con el mismo cálculo que en Cantor.
  * Ni el argumento de T71 para `βℕ` (modelos clásicos en los puntos aislados) ni el modelo constante sirven: un trozo
    finito de la teoría puede no ser clásico, como el propio `σ`.
  * Para las teorías PROPOSICIONALES (átomos sin argumentos, sin cuantificadores), la compacidad sí vale en Kripke
    sobre `ω` (🟡, esbozado). En un modelo sobre `ω`, un átomo vale `∅` o `[j, ∞)`.
    * Pasados los `j` finitos de los átomos de un `Γ` finito, el modelo es constante, y allí forzar es la verdad
      clásica de la valoración límite. Así, un `Γ` finito forzado en algún nodo es clásicamente satisfacible.
    * La compacidad clásica da una valoración de la unión de las `S_k`, y el modelo constante que la tiene las fuerza
      todas.
    * Con cuantificadores esto se rompe, porque los dominios crecen sin estabilizarse, como en `σ`.

**El veredicto del escéptico:**

* Sin fallo en el cálculo de Cantor ni en el de `ω₁`; en `ω₁` lo comprobó también para las sucesiones internas de
  cada nodo.
* Sin fallo en los cálculos de Kripke sobre `ω` y de Gleason.
* La compacidad proposicional en Kripke sobre `ω` no tenía argumento en la primera redacción; ahora lo tiene,
  esbozado.

### Lo que se intentó en positivo, y por qué no sale

No es una prueba de independencia.

* **Los artilugios de E8 y E10.** Un modelo da hechos negativos y decisiones finitas. Con las hipótesis de un fallo de
  DNS (`∀n ¬¬P n`), toda pertenencia condicionada a `¬P n` es vacía, y la condicionada a `P n` sólo devuelve `¬¬P n`.
  La guarda «hay al menos `k+1` elementos» de E10 no cambia eso: lo que se activa en un modelo infinito sigue siendo
  pertenencia condicionada.
* **Por E11, la compacidad ⟹ ¬¬EM diría que la compacidad refuta la satisfacibilidad de UNA fórmula.** La compacidad
  relaciona una teoría infinita con sus trozos finitos, y para `{σ}` es trivial. Una prueba tendría que sacar de un
  modelo de `σ` una teoría finitamente satisfacible e insatisfacible. Los candidatos naturales quieren decir que «sólo
  finitamente muchos quedan sin decidir», y eso no se expresa en primer orden: tienen modelos con los indecididos como
  constantes nuevas.

## Lo que queda abierto

* **La pregunta 2 para la compacidad y §3.** Su forma más precisa: ¿vale la compacidad, o §3, en el modelo de Kripke
  sobre `ω`? Si vale, no implican ni DNS ni ¬¬EM.
* **Las preguntas 3 y 4**, sin atacar por decisión del propietario: la cota por arriba (¿bastan WLEM + ¬¬EM para los
  cinco?) y si KSst es estrictamente más fuerte que WKS sin Markov. El pegado de §1 dice algo de la 3: WLEM + ¬¬EM no
  implican Markov diofántico.

## Los ficheros

| fichero | qué es |
|---|---|
| `medidas-2026-11-18.txt` | la salida de `lake env lean ../FOL/FOL/EsencialidadSem0.lean`, con su código de salida, y las quince líneas de E11, literales |
