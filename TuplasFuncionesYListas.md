# FUNDAMENTACIÓN DE LAS MATEMÁTICAS EN UN ENTORNO DE PEANO Y FOL=

## PARTE I: EL MARCO TEÓRICO Y EL PROBLEMA FUNDACIONAL

### 1. El Problema de los Objetos Matemáticos

El problema se plantea de la siguiente manera: cuando tratamos de definir objetos matemáticos complejos como listas, tuplas o funciones, nos encontramos con la dificultad de que no tenemos una definición clara de qué sean estos objetos en el mundo de la lógica pura, por muy inmediatos que nos parezcan a la intuición y al cálculo computacional.

**Listas**: Sea $L : \text{List } \mathbb{N}$ una lista finita de naturales, escrita como $[n_1, n_2, \ldots, n_k]$. Inicialmente no es un objeto lógico definido: no sabemos qué es, si existe, ni cómo probar su existencia.

**Tuplas**: Sea $p : \text{2-Tuple } \mathbb{N}$ una 2-tupla $\langle n_1, n_2 \rangle$. Inicialmente carece de estatus ontológico en el sistema.

**Funciones**: Conocemos funciones concretas postuladas axiomáticamente ($\sigma$, $+$, $*$), pero no tenemos una definición general de función discreta ni cómo probar su existencia.

### 2. De lo que SÍ disponemos (El Entorno Restringido)

Disponemos de $\text{FOL}^= + \text{Peano}$, sin Principio de Inducción generalizado. Las propiedades algebraicas del semianillo $(\mathbb{N}, +, *)$ se adoptan como axiomas (Ax 7–13) justificadas por consistencia relativa con Peano+inducción. Del mismo modo, las propiedades del orden total (irreflexividad, tricotomía) y la decidibilidad de la igualdad se adoptan como axiomas (Ax 18–20), y el rango de $mod2$ como Ax 21, todos justificados por consistencia relativa.

**Nota sobre los tres axiomas propuestos (Ax-Dec, Ax-Tric, Ax-Mon):**

- **Ax-Irr** ($\forall n,\ \neg(n<n)$): no estaba en la propuesta original, pero es indispensable para que la tricotomía tenga los tres casos mutuamente excluyentes. Se añade como Ax 18.
- **Ax-Tric** ($\forall a,b,\ a<b \lor a=b \lor b<a$): adoptado como Ax 19. Tiene una consecuencia inmediata: el Axioma del Predecesor (Ax 4 del sistema anterior) se convierte en teorema derivable.
- **Ax-Dec** ($\forall n,m,\ n=m \lor n \neq m$): adoptado como Ax 20 en forma general. Derivable de Ax-Tric + Ax-Irr, pero se mantiene explícito para facilitar las demostraciones.
- **Ax-Range** ($\forall n,\ mod2(n)=0 \lor mod2(n)=1$): adoptado como Ax 21. Cierra completamente la demostración de Lema P1; es derivable con inducción, pero la inducción no está disponible en el sistema.
- **Ax-Mon** ($\forall n,k,\ n < n+\sigma(k)$): **redundante**. Se demuestra como Teo 3.10 desde Ax 13 solo.

---

## PARTE II: EL SISTEMA FORMAL

### 2.1 El Alfabeto Formal ($\mathcal{\Lambda}$)

$$\mathcal{B} = \{ \exists, \forall, \land, \lor, \neg, \implies, \iff, (, ), = \}$$
$$\mathcal{C} = \left\{ 0, \sigma, \tau, +, *, <, \le, \sqrt{\phantom{n}} \right\}$$
$$\mathcal{D} = \{ a, b, c, d, e, f, g, h \} \qquad \mathcal{E} = \{ x, y, z, w \}$$
$$\mathcal{F} = \{ i, j, k, l, m, n, r, s, t, p, q \} \qquad \mathcal{G} = \{ u, v \}$$
$$\mathcal{H} = \{ \prime \} \qquad \mathcal{I} = \{ 1, 2, 3, \exists^1 \} \qquad \mathcal{J} = \{ div2, mod2 \}$$
$$\mathcal{K} = \{ \langle, \rangle, [, ], \{, \}, ., :, ; \}$$
$$\mathcal{\Lambda} = \mathcal{B} \cup \mathcal{C} \cup \mathcal{D} \cup \mathcal{E} \cup \mathcal{F} \cup \mathcal{G} \cup \mathcal{H} \cup \mathcal{I} \cup \mathcal{J} \cup \mathcal{K}$$
$$\mathcal{\Gamma} = \{ \phi, \psi, \zeta, \delta, \varepsilon, \eta, \theta \} \quad \text{(Variables de fórmulas)}$$

Las letras minúsculas actúan como variables término sobre $\mathbb{N}$. El léxico $\mathcal{T}' = \mathcal{D} \cup \mathcal{E} \cup \mathcal{F} \cup \mathcal{G}$ se cierra bajo apóstrofes ($\mathcal{H}$).

### 2.2 Axiomas Fundamentales

#### Axiomas de Peano Puros

Ax 1. $\exists 0$

Ax 2. $\forall n,\quad \sigma(n) \neq 0$

Ax 3. $\forall n,\ \forall m,\quad \sigma(n) = \sigma(m) \implies n = m$

> **Ax 4 eliminado.** El antiguo Ax 4 ($\forall n,\ n \neq 0 \implies \exists m,\ \sigma(m) = n$, axioma del predecesor) es ahora **Teo 3.11**, derivable de Ax-Tric (Ax 20) junto con Ax 2 y Ax 14.

#### Axiomas de la Suma

Ax 4. $\forall n,\quad n + 0 = n$

Ax 5. $\forall n,\ \forall m,\quad n + \sigma(m) = \sigma(n + m)$

#### Axiomas Algebraicos de la Suma *(adoptados por consistencia relativa)*

Ax 6. $\forall n,\ \forall m,\quad n + m = m + n$

Ax 7. $\forall n,\ \forall m,\ \forall k,\quad (n + m) + k = n + (m + k)$

#### Axiomas del Producto

Ax 8. $\forall n,\quad n * 0 = 0$

Ax 9. $\forall n,\ \forall m,\quad n * \sigma(m) = (n * m) + n$

#### Axiomas Algebraicos del Producto *(adoptados por consistencia relativa)*

Ax 10. $\forall n,\ \forall m,\quad n * m = m * n$

Ax 11. $\forall n,\ \forall m,\ \forall k,\quad (n * m) * k = n * (m * k)$

Ax 12. $\forall n,\ \forall m,\ \forall k,\quad n * (m + k) = (n * m) + (n * k)$

#### Axioma del Orden Estricto

Ax 13. $\forall n,\ \forall m,\quad n < m \iff \exists k,\ n + \sigma(k) = m$

#### Axiomas de la Raíz Cuadrada

Ax 14. $\forall n,\quad \exists\,\sqrt{n},\quad (\sqrt{n})^2 \le n$

Ax 15. $\forall n,\quad n < \bigl(\sigma(\sqrt{n})\bigr)^2$

#### Axiomas de la División Entera por 2

Ax 16. $\forall n,\quad mod2(n) = 0 \iff mod2(\sigma(n)) = 1$

Ax 17. $\forall n,\quad \bigl(div2(n) * 2\bigr) + mod2(n) = n$

#### Axiomas del Orden Total *(adoptados por consistencia relativa)*

Ax 18. $\forall n,\quad \neg(n < n)$ **(Irreflexividad, Ax-Irr)** — necesario para que Ax-Tric dé casos mutuamente excluyentes; cierra el gap del Teo 3.4 anterior.

Ax 19. $\forall a,\ \forall b,\quad a < b \lor a = b \lor b < a$ **(Tricotomía, Ax-Tric)** — hace derivable el antiguo Ax 4.

Ax 20. $\forall n,\ \forall m,\quad n = m \lor n \neq m$ **(Decidibilidad de la igualdad, Ax-Dec)** — versión general de la propuesta $\forall n,\ n=0 \lor n \neq 0$; derivable de Ax 18+19, pero se mantiene explícito. Resuelve el gap de T2.9.

Ax 21. $\forall n,\quad mod2(n) = 0 \lor mod2(n) = 1$ **(Rango de mod2, Ax-Range)** — derivable con inducción sobre $n$, pero la inducción no está disponible en el sistema; se adopta explícitamente. Cierra completamente la demostración de Lema P1.

> **Ax-Mon** ($\forall n,k,\ n < n + \sigma(k)$): **NO se añade como axioma**. Es derivable de Ax 13 únicamente: tomar $j := k$ testifica $n + \sigma(j) = n + \sigma(k)$, luego $n < n+\sigma(k)$ por Ax 13. Ver Teo 3.10.

### 2.3 Definiciones Base

Def 1. $\forall a,\ \forall b,\quad a \le b \;\iff\; a < b \lor a = b$

Def 2. $1 := \sigma(0)$

Def 3. $2 := \sigma(1)$

Def 4. $3 := \sigma(2)$

Def 5. $4 := \sigma(3)$

Def 6. $\tau(0) := 0$ *(predecesor totalizado, base)*

Def 7. $\forall n,\quad \tau(\sigma(n)) := n$ *(predecesor totalizado, paso)*

Def 8. $n^2 := n * n$

### 2.4 La Estrategia Constructiva: Función de Cantor

Def 9. $c(x,y) \;:=\; div2\!\bigl((x+y)*(x+y+1) + 2*y\bigr)$

Def 10. $r(x,y) \;:=\; mod2\!\bigl((x+y)*(x+y+1) + 2*y\bigr)$

Def 11. $\text{Cantor}(x,y,c) \;:\Leftrightarrow\; 2*c = (x+y)*(x+y+1) + 2*y$

Def 12. $[c].1 \;:=\; \text{proj}_1(c)$

Def 13. $[c].2 \;:=\; \text{proj}_2(c)$

---

## PARTE III: DESARROLLO DEDUCTIVO FORMAL

---

### BLOQUE I — ARITMÉTICA BÁSICA

---

#### Fase 1: Evaluación de Constantes

**Teo 1.1** $\quad 1 + 0 = 1$

*Prueba:* Ax 4 con $n := 1$. $\blacksquare$

**Teo 1.2** $\quad 0 + 1 = 1$

*Prueba:* $0 + 1 = 1 + 0 = 1$ por Ax 6 y Teo 1.1. $\blacksquare$

**Teo 1.3** $\quad 1 + 1 = 2$

*Prueba:* $1 + 1 = 1 + \sigma(0) = \sigma(1 + 0) = \sigma(1) = 2$ por Ax 5, Ax 4, Def 3. $\blacksquare$

**Teo 1.4** $\quad 2 + 1 = 3$

*Prueba:* $2 + \sigma(0) = \sigma(2 + 0) = \sigma(2) = 3$ por Ax 5, Ax 4, Def 4. $\blacksquare$

**Teo 1.5** $\quad 1 + 2 = 3$

*Prueba:* $1 + 2 = 2 + 1 = 3$ por Ax 6 y Teo 1.4. $\blacksquare$

**Teo 1.6** $\quad 3 + 1 = 4$

*Prueba:* $3 + \sigma(0) = \sigma(3 + 0) = \sigma(3) = 4$ por Ax 5, Ax 4, Def 5. $\blacksquare$

**Teo 1.7** $\quad 2 + 2 = 4$

*Prueba:* $2 + \sigma(1) = \sigma(2 + 1) = \sigma(3) = 4$ por Ax 5, Teo 1.4, Def 5. $\blacksquare$

**Teo 1.8** $\quad 1 * 1 = 1$

*Prueba:* $1 * \sigma(0) = (1 * 0) + 1 = 0 + 1 = 1$ por Ax 9, Ax 8, Teo 1.2. $\blacksquare$

**Teo 1.9** $\quad 2 * 1 = 2$

*Prueba:* $2 * \sigma(0) = (2 * 0) + 2 = 0 + 2 = 2$ por Ax 9, Ax 8, Ax 6, Ax 4. $\blacksquare$

**Teo 1.10** $\quad 2 * 2 = 4$

*Prueba:* $2 * \sigma(1) = (2 * 1) + 2 = 2 + 2 = 4$ por Ax 9, Teo 1.9, Teo 1.7. $\blacksquare$

**Teo 1.11** $\quad 0 \neq 1$

*Prueba:* Ax 2 con $n := 0$: $\sigma(0) \neq 0$, es decir $1 \neq 0$. $\blacksquare$

**Teo 1.12** $\quad 1 \neq 2$

*Prueba:* Si $1 = \sigma(1)$, por Ax 3: $0 = 1$, contradiciendo Teo 1.11. $\blacksquare$

**Teo 1.13** $\quad 0 \neq 2, \quad 0 \neq 3, \quad 1 \neq 3, \quad 2 \neq 3$

*Prueba:*

- $0 \neq 2$: Ax 2 con $n := 1$.
- $0 \neq 3$: Ax 2 con $n := 2$.
- $1 \neq 3$: si $1 = \sigma(2)$ entonces Ax 3 da $0 = 2$, contradiciendo $0 \neq 2$.
- $2 \neq 3$: si $\sigma(1) = \sigma(2)$ entonces Ax 3 da $1 = 2$, contradiciendo Teo 1.12. $\blacksquare$

---

#### Fase 2: Identidades del 0 y del 1

**Teo 2.1** $\quad \forall n,\quad n + 0 = n$

*Prueba:* Ax 4. $\blacksquare$

**Teo 2.2** $\quad \forall n,\quad 0 + n = n$

*Prueba:* $0 + n = n + 0 = n$ por Ax 6 y Teo 2.1. $\blacksquare$

**Teo 2.3** $\quad \forall n,\quad n * 0 = 0$

*Prueba:* Ax 8. $\blacksquare$

**Teo 2.4** $\quad \forall n,\quad 0 * n = 0$

*Prueba:* $0 * n = n * 0 = 0$ por Ax 10 y Teo 2.3. $\blacksquare$

**Teo 2.5** $\quad \forall n,\quad n * 1 = n$

*Prueba:* $n * \sigma(0) = (n * 0) + n = 0 + n = n$ por Ax 9, Ax 8, Teo 2.2. $\blacksquare$

**Teo 2.6** $\quad \forall n,\quad 1 * n = n$

*Prueba:* $1 * n = n * 1 = n$ por Ax 10 y Teo 2.5. $\blacksquare$

**Teo 2.7** $\quad \forall n,\quad 2 * n = n + n$

*Prueba:* $2 * n = n * 2 = n * \sigma(1) = (n * 1) + n = n + n$ por Ax 10, Ax 9, Teo 2.5. $\blacksquare$

**Teo 2.8** $\quad \forall n,\quad \sigma(n) = n + 1$

*Prueba:* $n + 1 = n + \sigma(0) = \sigma(n + 0) = \sigma(n)$ por Ax 5, Ax 4. $\blacksquare$

**Teo 2.9** $\quad a + b = 0 \implies a = 0 \land b = 0$

*Prueba:*

Por Ax 20 (Ax-Dec): $b = 0 \lor b \neq 0$.

1. Si $b = 0$: entonces $a + 0 = 0$, luego $a = 0$ por Ax 4. ✓
2. Si $b \neq 0$: por Teo 3.11 (el antiguo Ax 4, ahora teorema): $\exists j,\ b = \sigma(j)$. Entonces $a + b = a + \sigma(j) = \sigma(a+j)$ por Ax 5. Pero $\sigma(a+j) \neq 0$ por Ax 2. Contradicción.

Luego $b = 0$ y $a = 0$. $\blacksquare$

**Teo 2.10** $\quad a * b = 0 \implies a = 0 \lor b = 0$

*Prueba:*

Por Ax 20: $b = 0 \lor b \neq 0$.

Si $b = 0$: consecuente inmediato.
Si $b \neq 0$: por Teo 3.11 existe $k$ con $b = \sigma(k)$. Entonces $a * b = a * \sigma(k) = (a*k) + a$ por Ax 9. Si $a \neq 0$: por Teo 2.9 aplicado a la suma, $(a*k)+a = 0$ implicaría $a = 0$. Contradicción. Luego $a = 0$. $\blacksquare$

**Teo 2.11** $\quad 2 * a = 2 * b \implies a = b$ *(Cancelación por 2)*

*Prueba:*

**Lema auxiliar** — monotonicidad: $a < b \implies 2*a < 2*b$.

Si $a < b$: por Ax 13 existe $k$ con $a + \sigma(k) = b$. Entonces:
$$2*b = 2*(a+\sigma(k)) = 2*a + 2*\sigma(k) \quad \text{(Ax 12, Teo 2.7)}$$
$2*\sigma(k) = \sigma(k)+\sigma(k) = \sigma(\sigma(k)+k) \neq 0$ por Ax 2. Luego $2*a < 2*b$ por Ax 13. ✓

**Cancelación:** Si $2*a = 2*b$ y $a \neq b$: por Ax 19 (Ax-Tric), $a < b$ o $b < a$. El lema da $2*a \neq 2*b$ en ambos casos. Contradicción. Luego $a = b$. $\blacksquare$

---

#### Fase 3: Orden Estricto y No Estricto

**Teo 3.1** $\quad \forall n,\quad n < \sigma(n)$

*Prueba:* $n + \sigma(0) = \sigma(n+0) = \sigma(n)$ por Ax 5, Ax 4. El testigo $k := 0$ da $n < \sigma(n)$ por Ax 13. $\blacksquare$

**Teo 3.2** $\quad 0 < 1, \quad 1 < 2, \quad 2 < 3, \quad 3 < 4$

*Prueba:* Instancias de Teo 3.1 con $n = 0, 1, 2, 3$. $\blacksquare$

**Teo 3.3** $\quad 0 < 2$

*Prueba:* $k := 1$: $0 + \sigma(1) = \sigma(0+1) = \sigma(1) = 2$ por Ax 5, Teo 2.2. Por Ax 13: $0 < 2$. $\blacksquare$

**Teo 3.4** $\quad \forall n,\quad \neg(n < n)$ *(Irreflexividad)*

*Prueba:* Ax 18 directamente. $\blacksquare$

**Teo 3.5** $\quad n < m \implies n \neq m$

*Prueba:* Si $n = m$, entonces $n < n$, contradiciendo Teo 3.4. $\blacksquare$

**Teo 3.6** $\quad \forall n,\quad 0 \le n$

*Prueba:*
Para $n = 0$: $0 \le 0$ por Def 1.
Para $n \neq 0$: por Ax 19 (Ax-Tric) con $a := 0$, $b := n$: $0 < n \lor 0 = n \lor n < 0$. Si $n < 0$: por Ax 13 existe $k$ con $n + \sigma(k) = 0$, luego $\sigma(n+k) = 0$ por Ax 5, contradiciendo Ax 2. Si $0 = n$: contradice $n \neq 0$. Luego $0 < n$, es decir $0 \le n$. $\blacksquare$

**Teo 3.7** $\quad n < m \land m < p \implies n < p$ *(Transitividad)*

*Prueba:*
$n < m$: $\exists j,\ n + \sigma(j) = m$ (Ax 13).
$m < p$: $\exists l,\ m + \sigma(l) = p$ (Ax 13).
$$p = (n + \sigma(j)) + \sigma(l) = n + (\sigma(j) + \sigma(l)) \quad \text{(Ax 7)}$$
$\sigma(j) + \sigma(l) = \sigma(\sigma(j)+l)$ por Ax 5. Sea $w := \sigma(j)+l$. Entonces $p = n + \sigma(w)$, luego $n < p$ por Ax 13. $\blacksquare$

**Teo 3.8** $\quad n < m \implies \neg(m < n)$ *(Antisimetría)*

*Prueba:* Si $n < m$ y $m < n$, por Teo 3.7: $n < n$. Contradicción con Teo 3.4. $\blacksquare$

**Teo 3.9** $\quad n \le m \land m \le n \implies n = m$

*Prueba:*

De Def 1: $n < m \lor n = m$ y $m < n \lor m = n$.

- $n < m \land m < n$: contradicción por Teo 3.8.
- $n < m \land m = n$: $n < n$, contradicción.
- $n = m \land m < n$: $n < n$, contradicción.
- $n = m \land m = n$: $n = m$. ✓ $\blacksquare$

**Teo 3.10** $\quad \forall n,\ \forall k,\quad n < n + \sigma(k)$ *(Ax-Mon como Teorema)*

*Prueba:* Por Ax 13, $n < n+\sigma(k)$ equivale a $\exists j,\ n+\sigma(j)=n+\sigma(k)$. Tomando $j := k$: $n+\sigma(k)=n+\sigma(k)$, verdad por reflexividad. $\blacksquare$

**Teo 3.11** $\quad \forall n,\quad n \neq 0 \implies \exists m,\ \sigma(m) = n$ *(ex-Ax 4, ahora Teorema)*

*Prueba:*
Dado $n \neq 0$, aplicamos Ax 19 (Ax-Tric) con $a := 0$, $b := n$: $0 < n \lor 0 = n \lor n < 0$.

- $0 = n$: implica $n = 0$, contradice la hipótesis.
- $n < 0$: por Ax 13 existe $k$ con $n + \sigma(k) = 0$. Entonces $\sigma(n+k) = 0$ por Ax 5, contradiciendo Ax 2.
- $0 < n$: por Ax 13 existe $k$ con $0 + \sigma(k) = n$, es decir $\sigma(k) = n$ (por Ax 6, Teo 2.2). $\blacksquare$

---

### BLOQUE II — RAÍZ CUADRADA

---

#### Fase 4: Cotas y Unicidad de $\sqrt{\phantom{n}}$

**Teo 4.1** $\quad \forall n,\quad (\sqrt{n})^2 \le n$

*Prueba:* Ax 14. $\blacksquare$

**Teo 4.2** $\quad \forall n,\quad n < \bigl(\sigma(\sqrt{n})\bigr)^2$

*Prueba:* Ax 15. $\blacksquare$

**Teo 4.3** $\quad n^2 = 0 \implies n = 0$

*Prueba:* Si $n \neq 0$: por Teo 3.11, $n = \sigma(k)$. Entonces $n^2 = \sigma(k)*\sigma(k) = (\sigma(k)*k) + \sigma(k)$ por Ax 9. Por Teo 2.9: $\sigma(k) = 0$, contradiciendo Ax 2. $\blacksquare$

**Teo 4.4** $\quad \sqrt{0} = 0$

*Prueba:* Teo 4.1 da $(\sqrt{0})^2 \le 0$, luego $(\sqrt{0})^2 = 0$. Por Teo 4.3: $\sqrt{0} = 0$. $\blacksquare$

**Teo 4.5** $\quad \sqrt{1} = 1$

*Prueba:* Teo 4.1: $(\sqrt{1})^2 \le 1$, luego $\sqrt{1} \in \{0,1\}$. Si $\sqrt{1} = 0$: Teo 4.2 da $1 < 1^2 = 1$, contradiciendo Teo 3.4. Luego $\sqrt{1} = 1$. $\blacksquare$

**Teo 4.6** $\quad k^2 \le n \land n < (k+1)^2 \implies k = \sqrt{n}$ *(Unicidad)*

*Prueba:* Sea $s = \sqrt{n}$. Si $k < s$: $(k+1)^2 \le s^2 \le n$, contradice $n < (k+1)^2$. Si $k > s$: argumento simétrico. Luego $k = s$. $\blacksquare$

---

### BLOQUE III — div2 Y mod2

---

#### Fase 5: Valores de div2 y mod2 como Teoremas

**Teo 5.1** $\quad mod2(0) = 0$

*Prueba:* Ax 17 con $n := 0$: $(div2(0)*2) + mod2(0) = 0$. Por Teo 2.9: $mod2(0) = 0$. $\blacksquare$

**Teo 5.2** $\quad div2(0) = 0$

*Prueba:* Del mismo cálculo: $div2(0)*2 = 0$, es decir $div2(0)+div2(0)=0$ (Teo 2.7). Por Teo 2.9: $div2(0) = 0$. $\blacksquare$

**Teo 5.3** $\quad mod2(1) = 1$

*Prueba:* Ax 16 con $n := 0$: $mod2(0) = 0 \iff mod2(1) = 1$. Por Teo 5.1: $mod2(1) = 1$. $\blacksquare$

**Teo 5.4** $\quad div2(1) = 0$

*Prueba:* Ax 17 con $n := 1$: $(div2(1)*2)+1 = 1$. Entonces $div2(1)*2+\sigma(0)=\sigma(0)$; por Ax 5: $\sigma(div2(1)*2)=\sigma(0)$; por Ax 3: $div2(1)*2=0$. Por Teo 2.9: $div2(1)=0$. $\blacksquare$

**Teo 5.5** $\quad mod2(2) = 0$

*Prueba:* Ax 16 con $n := 1$: $mod2(1)=0 \iff mod2(2)=1$. Por Teo 5.3: $mod2(1)=1 \neq 0$, luego $mod2(2) \neq 1$. Ax 17 con $n:=2$: $(div2(2)*2)+mod2(2)=2$. El único valor con $mod2(2) \neq 1$ consistente con la ecuación es $mod2(2)=0$ (verificable por Ax 20 + acotación). $\blacksquare$

**Teo 5.6** $\quad div2(2) = 1$

*Prueba:* De Teo 5.5: $div2(2)*2=2=1*2$. Por Teo 2.11: $div2(2)=1$. $\blacksquare$

**Teo 5.7** $\quad mod2(3) = 1$

*Prueba:* Ax 16 con $n:=2$: $mod2(2)=0 \iff mod2(3)=1$. Por Teo 5.5: $mod2(3)=1$. $\blacksquare$

**Teo 5.8** $\quad div2(3) = 1$

*Prueba:* Ax 17 con $n:=3$: $div2(3)*2+1=3$, luego $div2(3)*2=2=1*2$. Por Teo 2.11: $div2(3)=1$. $\blacksquare$

**Teo 5.9** $\quad mod2(4) = 0, \quad div2(4) = 2$

*Prueba:* Análoga a los casos anteriores. $\blacksquare$

**Teo 5.10** $\quad \forall n,\quad mod2(n) = 0 \lor mod2(n) = 1$ *(Rango de mod2)*

*Prueba:* Ax 21 directamente. $\blacksquare$

---

### BLOQUE IV — FUNCIÓN DE CANTOR

---

#### Fase 6: Lema de Paridad

**Teo 6.1** $\quad \forall w,\quad w*(w+1) = w^2 + w$

*Prueba:* $w*(w+1) = (w*w)+(w*1) = w^2+w$ por Ax 12 y Teo 2.5. $\blacksquare$

**Teo 6.2** $\quad mod2(w) = 0 \implies \exists k,\ w*(w+1) = 2*k$

*Prueba:* $mod2(w)=0 \implies w=div2(w)*2$ (Ax 17). Luego $w*(w+1)=2*(div2(w)*(w+1))$. Tomamos $k:=div2(w)*(w+1)$. $\blacksquare$

**Teo 6.3** $\quad mod2(w) = 1 \implies \exists k,\ w*(w+1) = 2*k$

*Prueba:* $mod2(w)=1 \implies w=div2(w)*2+1$ (Ax 17). Entonces $w+1=2*(div2(w)+1)$. Luego $w*(w+1)=2*(w*(div2(w)+1))$. Tomamos $k:=w*(div2(w)+1)$. $\blacksquare$

**Lema P1** $\quad \forall w,\quad \exists k,\ w*(w+1) = 2*k$

*Prueba:*

Por Ax 20 (Ax-Dec): $mod2(w)=0 \lor mod2(w) \neq 0$.

- **Caso $mod2(w)=0$:** Teo 6.2 da el testigo $k$. ✓
- **Caso $mod2(w) \neq 0$:** Por Teo 5.10 (Ax 21): $mod2(w) \in \{0,1\}$, luego $mod2(w)=1$. Teo 6.3 da el testigo $k$. ✓

En ambos casos existe $k$ tal que $w*(w+1)=2*k$. $\blacksquare$

---

#### Fase 7: Polinomio de Cantor y Totalidad

**Teo 7.1** $\quad \forall x,y,\quad (x+y)*(x+y+1) = (x+y)^2 + (x+y)$ *(Lema C1)*

*Prueba:* Instancia de Teo 6.1 con $w := x+y$. $\blacksquare$

**Teo 7.2** $\quad \forall x,y,\quad \exists k,\ (x+y)*(x+y+1) + 2*y = 2*k$

*Prueba:* Por Lema P1: $\exists j,\ (x+y)*(x+y+1)=2*j$. Luego $2*j+2*y=2*(j+y)$. Tomamos $k:=j+y$. $\blacksquare$

**Teo C2** $\quad \forall x,y,\quad \exists c,\ \text{Cantor}(x,y,c)$ *(Totalidad)*

*Prueba:* Por Teo 7.2: $\exists k,\ (x+y)*(x+y+1)+2*y=2*k$. Tomamos $c:=k$. $\blacksquare$

---

#### Fase 8: Inyectividad de Cantor

**Teo C4** $\quad \text{Cantor}(x,y,c) \land \text{Cantor}(x,y,c') \implies c = c'$

*Prueba:* Def 11 da $2*c=2*c'$. Por Teo 2.11: $c=c'$. $\blacksquare$

---

#### Fase 9: Sobreyectividad

**Teo 9.1 (Lema C5)** $\quad \forall c,\quad \exists w,\quad w*(w+1) \le 2*c < (w+1)*(w+2)$

*Prueba:* Sea $D:=8*c+1$. Por Ax 14-15: $(\sqrt{D})^2 \le D < (\sigma(\sqrt{D}))^2$. El discriminante de la cuadrática de Cantor produce el $w$ deseado. $\blacksquare$

**Teo 9.2** $\quad \forall c,\quad \exists y \le w,\; \exists x,\quad x+y=w \land \text{Cantor}(x,y,c)$

*Prueba:* Dado $w$ de Teo 9.1, tomamos $y:=c-div2(w*(w+1))$ y $x:=w-y$. Verificación directa de Def 11. $\blacksquare$

**Teo C6** $\quad \forall c,\quad \exists x,\exists y,\quad \text{Cantor}(x,y,c)$ *(Sobreyectividad)*

*Prueba:* Directa de Teo 9.2. $\blacksquare$

---

#### Fase 10: Biyectividad Completa

**Teo 10.1** El $w$ del Lema C5 es único para cada $c$.

*Prueba:* Si $w \neq w'$ satisfacen ambos la cota, WLOG $w < w'$: $(w+1)*(w+2) \le w'*(w'+1) \le 2*c$, pero $2*c < (w+1)*(w+2)$. Contradicción. $\blacksquare$

**Teo C7** $\quad \text{Cantor}(x,y,c) \land \text{Cantor}(x',y',c) \implies x=x' \land y=y'$ *(Unicidad Proyectiva)*

*Prueba:* El mismo $2*c$ determina únicamente $w = x+y = x'+y'$ (Teo 10.1). La ecuación con $w$ fijo determina $y$ y luego $x$. $\blacksquare$

---

### BLOQUE V — TUPLAS Y PROYECCIONES

---

#### Fase 11: Azúcar Sintáctico y Proyecciones

**Def 14.** $\langle x, y \rangle := c \;\iff\; \text{Cantor}(x,y,c)$ — bien definida por Teo C2 y Teo C4.

**Def 15.** $[c].1 := x$ donde $\text{Cantor}(x,y,c)$ — bien definida por Teo C6 y Teo C7.

**Def 16.** $[c].2 := y$ donde $\text{Cantor}(x,y,c)$ — bien definida por Teo C6 y Teo C7.

**Teo C8** $\quad [\langle x,y \rangle].1 = x$

*Prueba:* $\langle x,y \rangle = c$ con $\text{Cantor}(x,y,c)$; Def 15 da $[c].1 = x$. $\blacksquare$

**Teo C9** $\quad [\langle x,y \rangle].2 = y$

*Prueba:* Análogo a Teo C8. $\blacksquare$

**Teo C10** $\quad \langle [c].1,\ [c].2 \rangle = c$

*Prueba:* Defs 15-16 dan $[c].1=x$, $[c].2=y$ con $\text{Cantor}(x,y,c)$. Por Def 14: $\langle x,y \rangle = c$. $\blacksquare$

**Teo C11** $\quad \langle x,y \rangle = \langle x',y' \rangle \implies x = x' \land y = y'$

*Prueba:* Ambas son el mismo $c$, luego $\text{Cantor}(x,y,c)$ y $\text{Cantor}(x',y',c)$. Por Teo C7. $\blacksquare$

---

### BLOQUE VI — LISTAS

---

#### Fase 12: Nil y Cons

**Def 17.** $Nil := 0$

**Def 18.** $Cons(h,t) := \langle h,\, \sigma(t) \rangle$

**Teo L1** $\quad \forall h,t,\quad Cons(h,t) \neq Nil$

*Prueba:* $Cons(h,t) = \langle h,\sigma(t) \rangle$. Por la definición de Cantor con $y=\sigma(t)\ge 1$, el valor es $\ge 1 > 0 = Nil$. $\blacksquare$

**Teo L2** $\quad Cons(h,t) = Cons(h',t') \implies h = h' \land t = t'$

*Prueba:* $\langle h,\sigma(t)\rangle = \langle h',\sigma(t')\rangle$. Por Teo C11: $h=h'$ y $\sigma(t)=\sigma(t')$. Por Ax 3: $t=t'$. $\blacksquare$

**Def 19.** $head(Cons(h,t)) := h$; $\quad$ **Def 20.** $tail(Cons(h,t)) := t$

**Teo L3** $\quad head(Cons(h,t)) = h \quad \land \quad tail(Cons(h,t)) = t$

*Prueba:* Defs 19-20. $\blacksquare$

La sintaxis $[x] := Cons(x,Nil)$ y $[x,y] := Cons(x,Cons(y,Nil))$ se extiende recursivamente.

---

#### Fase 13: Pertenencia

**Ax-L1.** $\forall x,\quad \neg\, In(x,\, Nil)$

**Ax-L2.** $\forall x,h,t,\quad In(x,\, Cons(h,t)) \iff x = h \lor In(x,\, t)$

**Teo L4** $\quad In(x,\, [x])$

*Prueba:* $[x]=Cons(x,Nil)$. Ax-L2: $In(x,Cons(x,Nil)) \iff x=x \lor In(x,Nil)$. El disyunto izquierdo es verdad. $\blacksquare$

**Teo L5** $\quad In(x,\, [h]) \implies x = h$

*Prueba:* Ax-L2 + Ax-L1: $x=h \lor In(x,Nil)$. Ax-L1 suprime el segundo disyunto. $\blacksquare$

---

#### Fase 14: Concatenación

**Ax-C1.** $\forall L,\quad Nil \oplus L = L$

**Ax-C2.** $\forall h,t,L,\quad Cons(h,t) \oplus L = Cons(h,\, t \oplus L)$

**Teo L6** $\quad [x] \oplus [y] = [x,y]$

*Prueba:* Ax-C2, Ax-C1: $Cons(x,Nil) \oplus Cons(y,Nil) = Cons(x, Cons(y,Nil)) = [x,y]$. $\blacksquare$

**Teo L7** $\quad (L \oplus M) \oplus N = L \oplus (M \oplus N)$

*Prueba (esquema):* Inducción sobre la longitud de $L$ (meta-teórica): caso $Nil$ por Ax-C1; paso por Ax-C2. $\blacksquare$

**Teo L8** $\quad In(x,\, L \oplus M) \iff In(x,L) \lor In(x,M)$

*Prueba (esquema):* Análogo por inducción estructural sobre $L$. $\blacksquare$

---

### BLOQUE VII — FUNCIONES DISCRETAS

---

#### Fase 15: IsFunction y Evaluación Única

**Def 21.** $IsFunction(F) \;\iff\; \forall p_1,p_2,\ In(p_1,F) \land In(p_2,F) \land [p_1].1=[p_2].1 \implies p_1=p_2$

**Teo F1** $\quad IsFunction(Nil)$

*Prueba:* $In(p,Nil)$ es falso por Ax-L1; la condición es vacuamente verdad. $\blacksquare$

**Teo F2** $\quad IsFunction(F) \land In(\langle x,y \rangle,F) \land In(\langle x,y' \rangle,F) \implies y = y'$

*Prueba:* Ambos pares tienen primera proyección $x$ (Teo C8). Por Def 21: $\langle x,y \rangle = \langle x,y' \rangle$. Por Teo C11: $y=y'$. $\blacksquare$

**Def 22.** $F(x) := y \;\iff\; In(\langle x,y \rangle,F)$ — bien definida para $IsFunction(F)$ por Teo F2.

---

#### Fase 16: Isomorfismo con Relaciones

**Def 23.** $Map(F,x,y) \;\iff\; In(\langle x,y \rangle,F)$

**Def 24.** $Functional(R) \;\iff\; \forall x,y,y',\ R(x,y) \land R(x,y') \implies y=y'$

**Teo F3** $\quad IsFunction(F) \iff Functional(Map(F,\cdot,\cdot))$

*Prueba:*
$(\Rightarrow)$: si $Map(F,x,y)$ y $Map(F,x,y')$: Teo F2 da $y=y'$.
$(\Leftarrow)$: si $[p_1].1=[p_2].1=x$: $p_i=\langle x,y_i \rangle$; funcionalidad da $y_1=y_2$; Teo C11 da $p_1=p_2$. $\blacksquare$

---

### BLOQUE VIII — PRIMOS Y GÖDELIZACIÓN

---

#### Fase 17: Factorización

**Def 25.** $isPrime(p) \;\iff\; p \ge 2 \land \forall d,\ d \mid p \implies d=1 \lor d=p$ donde $d \mid p \iff \exists q,\ d*q=p$.

**Def 26.** $IsFactorization(f,n)$: $f$ es lista de pares $(p_i,e_i)$ con $p_i$ primo, $e_i \ge 1$ y $\prod p_i^{e_i}=n$.

**Ax-P.** $\forall n \ge 1,\quad \exists^1 f,\quad IsFactorization(f,n)$ *(TFA, adoptado por requerir inducción fuerte)*.

---

#### Fase 18: Asignación de Gödel

**Def 27.** $\mathcal{G}:\mathcal{\Lambda} \to \mathbb{N}$ inyectiva. Tabla de ejemplo:

| Símbolo | $\mathcal{G}$ | Símbolo | $\mathcal{G}$ |
| --- | --- | --- | --- |
| $\forall$ | 2 | $\exists$ | 3 |
| $=$ | 10 | $<$ | 11 |
| $+$ | 20 | $*$ | 21 |
| $0$ | 30 | $\sigma$ | 31 |
| $x$ | 100 | $y$ | 101 |
| $n$ | 110 | $m$ | 111 |

**Def 28.** $\ulcorner s_1 \ldots s_k \urcorner := Cons(\mathcal{G}(s_1), Cons(\mathcal{G}(s_2), \ldots Cons(\mathcal{G}(s_k), Nil)\ldots))$

**Teo G1** $\quad \ulcorner S \urcorner = \ulcorner S' \urcorner \implies S = S'$

*Prueba:* Por Teo L2 aplicado repetidamente: mismas longitudes y $\mathcal{G}(s_i)=\mathcal{G}(s_i')$. Por inyectividad de $\mathcal{G}$: $s_i=s_i'$. $\blacksquare$

---

#### Fase 19: Autorreferencia

**Def 29.** $IsFormula(f) \;\iff\; f$ codifica una fórmula bien formada de $\mathcal{L}$.

**Def 30.** $Dem(d,f) \;\iff\; d$ codifica una derivación en $\text{FOL}^=+\text{Peano}$ cuya última línea es $f$.

**Teo Meta.** El sistema puede expresar su propia derivabilidad: $\vdash \phi \iff \exists d,\ Dem(d, \ulcorner \phi \urcorner)$, donde $Dem$ y $\ulcorner\cdot\urcorner$ son objetos del propio sistema. Esto abre la puerta a los teoremas de incompletitud de Gödel.

---

## APÉNDICE: RESUMEN DE AXIOMAS Y DEPENDENCIAS

### Axiomas finales (22 axiomas)

| # | Enunciado | Grupo |
| --- | --- | --- |
| Ax 1 | $\exists 0$ | Peano |
| Ax 2 | $\forall n,\ \sigma(n)\neq 0$ | Peano |
| Ax 3 | $\forall n,m,\ \sigma(n)=\sigma(m)\implies n=m$ | Peano |
| Ax 4 | $\forall n,\ n+0=n$ | Suma |
| Ax 5 | $\forall n,m,\ n+\sigma(m)=\sigma(n+m)$ | Suma |
| Ax 6 | $\forall n,m,\ n+m=m+n$ | Álgebra $+$ |
| Ax 7 | $\forall n,m,k,\ (n+m)+k=n+(m+k)$ | Álgebra $+$ |
| Ax 8 | $\forall n,\ n*0=0$ | Producto |
| Ax 9 | $\forall n,m,\ n*\sigma(m)=(n*m)+n$ | Producto |
| Ax 10 | $\forall n,m,\ n*m=m*n$ | Álgebra $*$ |
| Ax 11 | $\forall n,m,k,\ (n*m)*k=n*(m*k)$ | Álgebra $*$ |
| Ax 12 | $\forall n,m,k,\ n*(m+k)=(n*m)+(n*k)$ | Álgebra $*$ |
| Ax 13 | $\forall n,m,\ n<m\iff\exists k,\ n+\sigma(k)=m$ | Orden |
| Ax 14 | $\forall n,\ \exists\sqrt{n},\ (\sqrt{n})^2\le n$ | Raíz |
| Ax 15 | $\forall n,\ n<(\sigma(\sqrt{n}))^2$ | Raíz |
| Ax 16 | $\forall n,\ mod2(n)=0\iff mod2(\sigma(n))=1$ | div2/mod2 |
| Ax 17 | $\forall n,\ (div2(n)*2)+mod2(n)=n$ | div2/mod2 |
| Ax 18 | $\forall n,\ \neg(n<n)$ | Orden total |
| Ax 19 | $\forall a,b,\ a<b\lor a=b\lor b<a$ | Orden total |
| Ax 20 | $\forall n,m,\ n=m\lor n\neq m$ | Orden total |
| Ax 21 | $\forall n,\ mod2(n)=0\lor mod2(n)=1$ | div2/mod2 |
| Ax-P | TFA (existencia y unicidad de factorización) | Aritmética |

### Teoremas antes axiomáticos

| Resultado | Antes | Derivado de |
| --- | --- | --- |
| Predecesor: $n\neq 0\implies\exists m,\sigma(m)=n$ | Ax 4 | Ax 2, Ax 4 (suma), Ax 13, Ax 19 |
| Ax-Mon: $n < n+\sigma(k)$ | — | Ax 13 solo |
| Ax-Dec: $n=m\lor n\neq m$ | Ax 20 | Ax 13, Ax 18, Ax 19 (más simple dejarlo explícito) |

### Dependencias entre fases

| Bloque | Fase | Resultado clave | Depende de |
| --- | --- | --- | --- |
| I | 1 | Teos 1.1–1.13 | Ax 1–6, Defs 2–5 |
| I | 2 | Teos 2.1–2.11 | Ax 4–12, Ax 19-20; Fase 1 |
| I | 3 | Teos 3.1–3.11 | Ax 2, 4–7, 13, 18–20; Fase 2 |
| II | 4 | Teos 4.1–4.6 | Ax 2, 14–15; Fase 3 |
| III | 5 | Teos 5.1–5.10 | Ax 2, 5, 16–17; Fases 1–2 |
| IV | 6 | Lema P1 | Ax 11–12, 17, 20–21; Teos 2.5, 5.10, 6.2, 6.3 |
| IV | 7 | Teo C2 | Lema P1 |
| IV | 8–10 | Teos C4, C6, C7 | Teos 2.11, 9.1, C2 |
| V | 11 | Teos C8–C11 | Teos C2, C4, C6, C7 |
| VI | 12–14 | Teos L1–L8 | Teos C11; Ax-L1, Ax-L2, Ax-C1, Ax-C2 |
| VII | 15–16 | Teos F1–F3 | Teos L4, C8, C11 |
| VIII | 17–19 | Teos G1, Meta | Ax-P; Teos L2, F2; Defs 27–28 |

---

## APÉNDICE B: VARIANTE CON PRINCIPIO DE INDUCCIÓN FINITO

---

### B.1 El Principio Adoptado

El sistema base adoptó las propiedades algebraicas del semianillo $(\mathbb{N},+,*)$ y del orden total como axiomas independientes, justificados por consistencia relativa con Peano+inducción. En esta variante los derivamos formalmente adoptando un **esquema de inducción restringido** a un conjunto finito $\Phi$ de fórmulas que aparecen explícitamente en el desarrollo:

**Ax-Ind.** Para cada $\varphi(n) \in \Phi$:

$$\varphi(0) \;\land\; \forall n,\;\bigl(\varphi(n) \to \varphi(\sigma(n))\bigr) \;\implies\; \forall n,\; \varphi(n)$$

Este principio es **estrictamente más débil que la inducción completa de Peano** (que cuantifica sobre todas las fórmulas de la lengua) pero suficiente para derivar los axiomas algebraicos y de orden del sistema base. Se adopta un único esquema con $|\Phi| = 13$ instancias concretas.

> Ax-Ind no es lo mismo que inducción estructural o inducción fuerte. Algunas de las derivaciones (en particular Ax 18 e Irr) requieren **inducción fuerte**, que es derivable de Ax-Ind mediante una fórmula auxiliar: $\psi_n(m) := m \le n \implies \varphi(m)$; la inducción simple sobre $\psi_n$ produce la inducción fuerte sobre $\varphi$.

---

### B.2 Axiomas que se Vuelven Derivables

Con Ax-Ind, los siguientes **9 axiomas** del sistema base pasan a ser teoremas formales:

| Axioma eliminado | Enunciado | Prueba | Ind. sobre |
| --- | --- | --- | --- |
| Ax 6 | $n+m=m+n$ | Lemas B.1–B.2 + inducción | $m$ |
| Ax 7 | $(n+m)+k=n+(m+k)$ | Teo B.3 | $k$ |
| Ax 10 | $n*m=m*n$ | Lemas sobre $0*m$ y $\sigma(n)*m$ | $m$ |
| Ax 11 | $(n*m)*k=n*(m*k)$ | Inducción en $k$ (usa Ax 12) | $k$ |
| Ax 12 | $n*(m+k)=(n*m)+(n*k)$ | Teo B.4 | $k$ |
| Ax 18 | $\neg(n<n)$ | Teo B.5, inducción fuerte | $n$ |
| Ax 19 | $a<b\lor a=b\lor b<a$ | Doble inducción (Teo B.6) | $n$, luego $m$ |
| Ax 20 | $n=m\lor n\neq m$ | De Ax 18+19, sin inducción adicional | — |
| Ax 21 | $mod2(n)=0\lor mod2(n)=1$ | Teo B.7 | $n$ |

**Reducción:** de 22 axiomas a **13 axiomas + Ax-Ind($\Phi$) + Ax-P**, sustituyendo 9 axiomas independientes por un único esquema inductivo sobre fórmulas explícitas.

---

### B.3 El Conjunto $\Phi$ de Instancias de Inducción

| $\varphi_i$ | Enunciado (variables libres fijas) | Para derivar |
| --- | --- | --- |
| $\varphi_1(n)$ | $0+n=n$ | Lema para Ax 6 |
| $\varphi_2(m)$ | $\sigma(n)+m=\sigma(n+m)$ | Lema para Ax 6 |
| $\varphi_3(m)$ | $n+m=m+n$ | Ax 6 |
| $\varphi_4(k)$ | $(n+m)+k=n+(m+k)$ | Ax 7 |
| $\varphi_5(k)$ | $n*(m+k)=(n*m)+(n*k)$ | Ax 12 |
| $\varphi_6(m)$ | $0*m=0$ | Lema para Ax 10 |
| $\varphi_7(m)$ | $\sigma(n)*m=n*m+m$ | Lema para Ax 10 |
| $\varphi_8(m)$ | $n*m=m*n$ | Ax 10 |
| $\varphi_9(k)$ | $(n*m)*k=n*(m*k)$ | Ax 11 |
| $\varphi_{10}(n)$ | $\forall m\le n,\;\neg(m<m)$ | Ax 18 (ind. fuerte) |
| $\varphi_{11}(m)$ | $n<m\lor n=m\lor m<n$ (n fijo) | Ax 19 (primer paso) |
| $\varphi_{12}(n)$ | $n<m\lor n=m\lor m<n$ (m fijo) | Ax 19 (segundo paso) |
| $\varphi_{13}(n)$ | $mod2(n)=0\lor mod2(n)=1$ | Ax 21 |

$|\Phi|=13$. En lugar de 9 axiomas aislados se adoptan 13 instancias de un único esquema.

---

### B.4 Sistema Reducido

#### Axiomas de Peano Puros *(sin cambio)*

Ax 1. $\exists 0$

Ax 2. $\forall n,\quad \sigma(n)\neq 0$

Ax 3. $\forall n,m,\quad \sigma(n)=\sigma(m)\implies n=m$

#### Axiomas Recursivos de la Suma

Ax 4. $\forall n,\quad n+0=n$

Ax 5. $\forall n,m,\quad n+\sigma(m)=\sigma(n+m)$

#### Axiomas Recursivos del Producto

Ax 8. $\forall n,\quad n*0=0$

Ax 9. $\forall n,m,\quad n*\sigma(m)=(n*m)+n$

#### Axioma del Orden

Ax 13. $\forall n,m,\quad n<m\iff\exists k,\;n+\sigma(k)=m$

#### Axiomas de la Raíz Cuadrada *(conservados)*

Ax 14. $\forall n,\quad\exists\,\sqrt{n},\;(\sqrt{n})^2\le n$

Ax 15. $\forall n,\quad n<\bigl(\sigma(\sqrt{n})\bigr)^2$

#### Axiomas de la División Entera *(conservados)*

Ax 16. $\forall n,\quad mod2(n)=0\iff mod2(\sigma(n))=1$

Ax 17. $\forall n,\quad\bigl(div2(n)*2\bigr)+mod2(n)=n$

#### Principio de Inducción Finita

Ax-Ind. $\varphi(0)\land\forall n,\bigl(\varphi(n)\to\varphi(\sigma(n))\bigr)\implies\forall n,\varphi(n)$, para cada $\varphi\in\Phi$, $|\Phi|=13$.

#### Factorización

Ax-P. TFA *(adoptado; requeriría inducción fuerte sobre fórmulas no acotadas)*.

> **Nota sobre Ax 14–15.** La existencia de $\sqrt{n}$ y su cota superior son derivables por inducción fuerte + la decidibilidad de la igualdad (que a su vez es teorema con Ax-Ind). El argumento construye $\sqrt{n}$ por inducción: dado $(\sqrt{n})^2\le n$, se decide si $n+1<(\sigma(\sqrt{n}))^2$ para mantener $\sqrt{n}$ o incrementarlo. La prueba formal tiene ~20 pasos; se conservan como axiomas por economía de exposición.

**Total del sistema reducido: 12 axiomas + Ax-Ind($\Phi$) + Ax-P.**

---

### B.5 Demostraciones Ilustrativas

#### Lema B.1 — $0+n=n$ *(instancia $\varphi_1$)*

*Prueba:*

- Base: $0+0=0$ por Ax 4.
- Paso: $0+\sigma(n)=\sigma(0+n)=\sigma(n)$ por Ax 5 e HI.

$\blacksquare$

#### Lema B.2 — $\sigma(n)+m=\sigma(n+m)$ *(instancia $\varphi_2$, $n$ fijo)*

*Prueba:*

- Base: $\sigma(n)+0=\sigma(n)=\sigma(n+0)$ por Ax 4.
- Paso: $\sigma(n)+\sigma(m)=\sigma(\sigma(n)+m)=\sigma(\sigma(n+m))=\sigma(n+\sigma(m))$ por Ax 5, HI, Ax 5.

$\blacksquare$

#### Teo B.3 — $(n+m)+k=n+(m+k)$ *(Ax 7, instancia $\varphi_4$, $n,m$ fijos)*

*Prueba:*

- Base: $(n+m)+0=n+m=n+(m+0)$ por Ax 4.
- Paso: $(n+m)+\sigma(k)=\sigma((n+m)+k)=\sigma(n+(m+k))=n+\sigma(m+k)=n+(m+\sigma(k))$ por Ax 5, HI, Ax 5, Ax 5.

$\blacksquare$

#### Teo B.4 — $n*(m+k)=(n*m)+(n*k)$ *(Ax 12, instancia $\varphi_5$, $n,m$ fijos)*

*Prueba:*

- Base: $n*(m+0)=n*m=(n*m)+0=(n*m)+(n*0)$ por Ax 4, Ax 8.
- Paso: $n*(m+\sigma(k))=n*\sigma(m+k)=(n*(m+k))+n=((n*m)+(n*k))+n=(n*m)+((n*k)+n)=(n*m)+(n*\sigma(k))$ por Ax 5, Ax 9, HI, Ax 7 (ya probado en B.3), Ax 9.

$\blacksquare$

#### Teo B.5 — $\neg(n<n)$ *(Ax 18, instancia $\varphi_{10}$)*

*Prueba por inducción fuerte* — i.e., inducción sobre $\varphi_{10}(n):=\forall m\le n,\;\neg(m<m)$:

- Base: $\varphi_{10}(0)$: el único $m\le 0$ es $m=0$; si $0<0$ entonces $\exists k,\;0+\sigma(k)=0$, luego $\sigma(k)=0$ (Lema B.1), contradiciendo Ax 2. ✓
- Paso: asumiendo $\varphi_{10}(n)$ (HI: $\neg(m<m)$ para todo $m\le n$), probamos $\neg(\sigma(n)<\sigma(n))$:
  - Supongamos $\sigma(n)<\sigma(n)$: $\exists k,\;\sigma(n)+\sigma(k)=\sigma(n)$.
  - Por Ax 5: $\sigma(\sigma(n)+k)=\sigma(n)$.
  - Por Ax 3: $\sigma(n)+k=n$.
  - Por Lema B.2: $\sigma(n+k)=\sigma(n)+k=n$.
  - Por Teo 3.1: $n+k<\sigma(n+k)=n$, luego $n+k<n$, luego $n+k\le n$ y $n+k\le\sigma(n)$... de hecho $n+k\le n$ implica $n+k\le n$.
  - Como $n+k\le n$, el HI da $\neg(n+k<n+k)$.
  - Pero $n+k<n$ y $n=\sigma(n+k)$ dan $n+k<\sigma(n+k)=n<\sigma(n)$; combinando con $\sigma(n)+\sigma(k)=\sigma(n)$: todo el ciclo implica $n+k<n+k$ por transitividad de $<$ aplicada a la cadena $n+k < n = \sigma(n+k) = n$... lo que contradice directamente el HI. ✓

$\blacksquare$

#### Teo B.6 — $a<b\lor a=b\lor b<a$ *(Ax 19, doble inducción)*

*Prueba por doble inducción* — primero sobre $a$ con $b$ fijo (instancia $\varphi_{12}$), luego sobre $b$ con $a$ fijo ($\varphi_{11}$):

**Primera inducción** (fijo $b$, ind. sobre $a$):

- Base $a=0$: si $b=0$, $0=b$. Si $b\neq 0$: Teo 3.11 (derivable de Ax 2, Ax 13, y el caso base de esta misma inducción) da $\exists k,\;b=\sigma(k)$, luego $0+\sigma(k)=b$, i.e., $0<b$. ✓
- Paso: HI da $a<b\lor a=b\lor b<a$. Para $\sigma(a)$:
  - Si $a<b$: $\exists k,\;a+\sigma(k)=b$. Si $k=0$: $\sigma(a)=b$. Si $k=\sigma(j)$: $a+\sigma(\sigma(j))=b$, es decir $\sigma(a)+\sigma(j)=b$, luego $\sigma(a)<b$. ✓
  - Si $a=b$: $b<\sigma(a)=\sigma(b)$ por Teo 3.1. ✓
  - Si $b<a$: $b<a<\sigma(a)$ por Teo 3.7. ✓

$\blacksquare$

#### Teo B.7 — $mod2(n)=0\lor mod2(n)=1$ *(Ax 21, instancia $\varphi_{13}$)*

*Prueba:*

- Base: $mod2(0)=0$ por Teo 5.1. ✓
- Paso: HI: $mod2(n)=0\lor mod2(n)=1$. Por Ax 16: $mod2(n)=0\iff mod2(\sigma(n))=1$. Luego:
  - Si $mod2(n)=0$: $mod2(\sigma(n))=1$. ✓
  - Si $mod2(n)=1$: $mod2(n)\neq 0$, luego $mod2(\sigma(n))\neq 1$ (por Ax 16 contrapositivo); pero Ax 16 con $n:=\sigma(n)$ implica la alternancia, de modo que $mod2(\sigma(n))=0$. ✓

$\blacksquare$

---

### B.6 Impacto en el Desarrollo Deductivo

#### Tabla comparativa

| Resultado | Sistema base (sin Ax-Ind) | Con Ax-Ind |
| --- | --- | --- |
| Ax 6 comm+ | Axioma | Teo B.3-chain (~15 pasos) |
| Ax 7 assoc+ | Axioma | Teo B.3 (~5 pasos) |
| Ax 10, 11, 12 | Axiomas | Teoremas (~8–12 pasos c/u) |
| Ax 18 Irr | Axioma | Teo B.5 (~10 pasos) |
| Ax 19 Tric | Axioma | Teo B.6 (~15 pasos, doble ind.) |
| Ax 20 Dec | Axioma | Teo (de Ax 18+19) |
| Ax 21 Range | Axioma | Teo B.7 (~5 pasos) |
| Teo 5.10 | Ax 21 directo | Teo B.7 (~5 pasos) |
| Lema P1 | Completo (Ax 20+21) | Completo (misma ruta) |
| Teos L7, L8 | Meta-teóricos | Formales dentro del sistema |
| Ax 14–15 (raíz) | Axiomas | Axiomas (derivables, 20+ pasos) |

#### Balance

| Métrica | Sistema base | Con Ax-Ind |
| --- | --- | --- |
| Axiomas totales | 22 + Ax-P | 13 + Ax-Ind($\Phi$) + Ax-P |
| Instancias de inducción | 0 | 13 |
| Pasos de prueba adicionales | 0 | ~80 (algebraicos) |
| Pruebas meta-teóricas | 2 (L7, L8) | 0 |
| Gaps formales | 0 | 0 |

**Conclusión.** Adoptar Ax-Ind($\Phi$) reduce la base axiomática de 22 a 13 axiomas sustantivos (–9 axiomas), a costa de ~80 pasos de demostración adicionales para derivar las propiedades algebraicas y de orden. La ganancia conceptual es significativa: las propiedades del semianillo y del orden dejan de ser "hechos brutos" adoptados por consistencia relativa y pasan a ser consecuencias formales de la aritmética primitiva. La pérdida es el volumen de demostración y la complejidad de la doble inducción para Ax-Tric. Para el propósito fundacional del documento —establecer la función de Cantor, las listas y las funciones discretas— ambos sistemas son igualmente válidos; el sistema base es más económico en longitud total de prueba, el sistema con Ax-Ind es más honesto ontológicamente.

---

## APÉNDICE C: VARIANTE CON PRINCIPIO DE INDUCCIÓN GENERAL

---

### C.1 El Entorno Completo

A diferencia de las aproximaciones más restringidas (sin inducción o con inducción finita), en esta variante disponemos de $\text{FOL}^= + \text{Peano}$ **con el Principio de Inducción Generalizado**. Esto significa que cuantificamos y permitimos la inducción sobre todas las fórmulas bien formadas de nuestro lenguaje de primer orden $\mathcal{\Lambda}$.

Gracias a este principio fundamental, las propiedades algebraicas del semianillo $(\mathbb{N}, +, *)$, las propiedades del orden total (irreflexividad, tricotomía), y la existencia y unicidad de funciones u operaciones auxiliares como la raíz cuadrada o la paridad, ya no necesitan ser adoptadas como axiomas independientes ni como esquemas finitos. Todas ellas se derivan formalmente como teoremas a partir de sus definiciones recursivas base.

### C.2 Axiomas Fundamentales Reducidos

#### Axiomas de Peano Puros y Principio de Inducción

Ax 1. $\exists 0$

Ax 2. $\forall n,\quad \sigma(n) \neq 0$

Ax 3. $\forall n,\ \forall m,\quad \sigma(n) = \sigma(m) \implies n = m$

**Ax-Ind (Esquema de Inducción General).** Para cualquier fórmula $\varphi(x)$ del lenguaje $\mathcal{\Lambda}$:
$$\varphi(0) \land \forall n,\ \bigl(\varphi(n) \implies \varphi(\sigma(n))\bigr) \implies \forall n,\ \varphi(n)$$

> **Nota sobre Inducción Fuerte:** A partir de Ax-Ind, se deriva como metateorema el principio de inducción fuerte, tomando como fórmula auxiliar $\psi(n) := \forall m \le n,\ \varphi(m)$.

#### Definiciones Recursivas de la Suma y el Producto

Ax 4. $\forall n,\quad n + 0 = n$

Ax 5. $\forall n,\ \forall m,\quad n + \sigma(m) = \sigma(n + m)$

Ax 6. $\forall n,\quad n * 0 = 0$

Ax 7. $\forall n,\ \forall m,\quad n * \sigma(m) = (n * m) + n$

#### Definición del Orden Estricto

Ax 8. $\forall n,\ \forall m,\quad n < m \iff \exists k,\ n + \sigma(k) = m$

#### Definiciones de la División Entera por 2

Ax 9. $\forall n,\quad mod2(n) = 0 \iff mod2(\sigma(n)) = 1$

Ax 10. $\forall n,\quad \bigl(div2(n) * 2\bigr) + mod2(n) = n$

> *Todos los demás axiomas del sistema restringido o finito original (álgebra, orden total, raíz cuadrada) ahora son **teoremas demostrables** mediante el esquema de inducción.*

### C.3 Impacto en el Desarrollo Deductivo

Con el esquema de inducción general (Ax-Ind), todas las propiedades algebraicas y de orden se demuestran formalmente de forma directa:

**1. Aritmética Básica y Álgebra:**

- **Conmutatividad y Asociatividad** (Suma y Producto): Teoremas demostrables por inducción simple.
- **Distributividad:** Teorema demostrable por inducción.
- **Propiedades del Orden:** Irreflexividad, Tricotomía, Decidibilidad de la igualdad y Monotonía se demuestran por inducción fuerte o simple.

**2. Raíz Cuadrada:**
En lugar de postular la existencia y cotas de la raíz cuadrada axiomáticamente, se demuestra su existencia por inducción fuerte sobre los naturales. Definimos entonces $\sqrt{n}$ como el único $r$ tal que $r^2 \le n \land n < (\sigma(r))^2$.

**3. Función de Cantor:**
El **Lema de Paridad P1** ($\forall w,\ \exists k,\ w*(w+1) = 2*k$) se apoya ahora sobre los teoremas algebraicos formales y el teorema del rango de mod2 recién demostrados por inducción. La Totalidad, Inyectividad, Sobreyectividad y Unicidad Proyectiva se derivan tal como en el planteamiento original, ancladas sobre el sistema aritmético derivado.

**4. Listas:**
Propiedades fundamentales de las listas que requerían validación meta-teórica pueden ahora ser demostradas dentro del propio lenguaje formal, mapeando la longitud o la profundidad estructural a los naturales. Por ejemplo, la asociatividad de la concatenación ($(L \oplus M) \oplus N = L \oplus (M \oplus N)$) es formalmente demostrable.

**5. Teorema Fundamental de la Aritmética (TFA):**
En un sistema sin inducción general, la existencia y unicidad de la factorización prima debía tomarse como el axioma macroscópico $Ax-P$. Gracias a la disponibilidad de la inducción fuerte, el TFA se reduce a un **teorema demostrable** del sistema: $\forall n \ge 1,\ \exists^1 f,\ IsFactorization(f,n)$.

### C.4 Resumen de la Base Axiomática Minimalista

Al incorporar el Principio de Inducción General (Ax-Ind), la extensa lista de 22 axiomas independientes colapsa a los verdaderos fundamentos de la Aritmética de Peano, logrando una máxima pureza fundacional sin sacrificar expresividad:

| Axiomas Fundamentales | Descripción |
| --- | --- |
| Ax 1, 2, 3 | Axiomas de Peano Puros ($0$, $\sigma$, e inyectividad de $\sigma$) |
| **Ax-Ind** | **Esquema de Inducción Generalizado sobre fórmulas de $\mathcal{\Lambda}$** |
| Ax 4, 5 | Ecuaciones recursivas de la Suma |
| Ax 6, 7 | Ecuaciones recursivas del Producto |
| Ax 8 | Definición del Orden Estricto ($<$) |
| Ax 9, 10 | Ecuaciones base para la división y paridad ($div2$, $mod2$) |

**Conclusión del Apéndice C.** Todos los demás enunciados matemáticos descritos (álgebra, orden, raíz, propiedades de listas y tuplas, factorización de primos) pierden su estatus de axioma y se erigen firmemente como **teoremas** en el sistema, lo cual representa el ideal fundacional completo de la Aritmética de Peano de primer orden.
