# Esquema de Inicio: Lógica de Primer Orden (FOL)

Este documento detalla las reglas de inferencia fundamentales y los primeros teoremas que formarán la base de nuestro desarrollo en Lean 4. Servirá como hoja de ruta para la implementación del sistema deductivo.

## 1. Reglas de Inferencia Básicas (Deducción Natural)

Dado que ya tenemos la estructura `Derives Γ f` (que representa $Γ \vdash f$), debemos implementar constructores en nuestro tipo inductivo o teoremas derivados para las siguientes reglas lógicas.

### 1.1 Reglas Estructurales
*   **Identidad / Hipótesis (Ya implementada):** $f \in Γ \implies Γ \vdash f$
*   **Debilitamiento (Weakening):** Si $Γ \vdash f$ y $Γ \subseteq Γ'$, entonces $Γ' \vdash f$

### 1.2 Reglas Proposicionales Primitivas (Implicación y Falsedad)
Nuestra sintaxis base usa `impl` ($\Rightarrow$) y `bottom` ($\perp$).
*   **Introducción de la Implicación (Ya implementada):** Si $Γ, A \vdash B$, entonces $Γ \vdash A \Rightarrow B$
*   **Eliminación de la Implicación / Modus Ponens (Ya implementada):** Si $Γ \vdash A \Rightarrow B$ y $Γ \vdash A$, entonces $Γ \vdash B$
*   **Reductio ad Absurdum (RAA) / Lógica Clásica:** Si $Γ, \neg A \vdash \perp$, entonces $Γ \vdash A$

### 1.3 Reglas Derivadas (Negación, Conjunción, Disyunción, Equivalencia)
Dado que $\neg$, $\land$, $\lor$, $\Leftrightarrow$ están definidos en términos de $\Rightarrow$ y $\perp$, estas reglas se demostrarán como teoremas:
*   **Introducción de la Negación:** Si $Γ, A \vdash \perp$, entonces $Γ \vdash \neg A$
*   **Eliminación de la Negación:** Si $Γ \vdash \neg A$ y $Γ \vdash A$, entonces $Γ \vdash \perp$
*   **Introducción de la Conjunción:** Si $Γ \vdash A$ y $Γ \vdash B$, entonces $Γ \vdash A \land B$
*   **Eliminación de la Conjunción:** 
    *   Si $Γ \vdash A \land B$, entonces $Γ \vdash A$
    *   Si $Γ \vdash A \land B$, entonces $Γ \vdash B$
*   **Introducción de la Disyunción:**
    *   Si $Γ \vdash A$, entonces $Γ \vdash A \lor B$
    *   Si $Γ \vdash B$, entonces $Γ \vdash A \lor B$
*   **Eliminación de la Disyunción:** Si $Γ \vdash A \lor B$, $Γ, A \vdash C$ y $Γ, B \vdash C$, entonces $Γ \vdash C$

### 1.4 Reglas de Cuantificadores
*   **Introducción de $\forall$ (Esbozada):** Si $Γ \vdash A(x)$ y $x$ no está libre en $Γ$, entonces $Γ \vdash \forall x. A(x)$
*   **Eliminación de $\forall$:** Si $Γ \vdash \forall x. A(x)$, entonces $Γ \vdash A(t)$ para cualquier término $t$.
*   **Introducción de $\exists$:** Si $Γ \vdash A(t)$, entonces $Γ \vdash \exists x. A(x)$
*   **Eliminación de $\exists$:** Si $Γ \vdash \exists x. A(x)$ y $Γ, A(x) \vdash C$ (con $x$ no libre en $Γ$ ni en $C$), entonces $Γ \vdash C$

---

## 2. Primeros Teoremas a Demostrar

Una vez consolidadas las reglas deductivas, el primer objetivo será demostrar tautologías clásicas. El orden sugerido va de lo más simple a lo más complejo.

### Nivel 1: Tautologías de Implicación
1.  **Identidad:** $A \Rightarrow A$
2.  **Afirmación del Consecuente (K):** $A \Rightarrow (B \Rightarrow A)$
3.  **Transitividad / Silogismo Hipotético:** $(A \Rightarrow B) \Rightarrow ((B \Rightarrow C) \Rightarrow (A \Rightarrow C))$
4.  **Distribución de la Implicación (S):** $(A \Rightarrow (B \Rightarrow C)) \Rightarrow ((A \Rightarrow B) \Rightarrow (A \Rightarrow C))$

### Nivel 2: Propiedades de la Negación
5.  **Doble Negación (Introducción):** $A \Rightarrow \neg(\neg A)$
6.  **Doble Negación (Eliminación):** $\neg(\neg A) \Rightarrow A$ (Requiere RAA)
7.  **Contrapositiva (1):** $(A \Rightarrow B) \Rightarrow (\neg B \Rightarrow \neg A)$
8.  **Contrapositiva (2):** $(\neg B \Rightarrow \neg A) \Rightarrow (A \Rightarrow B)$
9.  **Explosión (Ex Falso Quodlibet):** $\perp \Rightarrow A$

### Nivel 3: Conectivos Derivados
10. **Conmutatividad de $\land$ y $\lor$**
11. **Asociatividad de $\land$ y $\lor$**
12. **Leyes de De Morgan:**
    *   $\neg (A \lor B) \Leftrightarrow \neg A \land \neg B$
    *   $\neg (A \land B) \Leftrightarrow \neg A \lor \neg B$
13. **Tercio Excluso:** $A \lor \neg A$

### Nivel 4: Cuantificadores
14. **Dualidad $\forall$ / $\exists$:** $\neg (\forall x. A) \Leftrightarrow \exists x. \neg A$
15. **Distribución de $\forall$ sobre $\land$:** $(\forall x. A \land B) \Leftrightarrow (\forall x. A) \land (\forall x. B)$