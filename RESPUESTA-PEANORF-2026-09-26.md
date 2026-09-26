# Respuesta a PeanoRF (3) — 2026‑09‑26

**Last updated:** 2026-09-26
**De**: el agente de FOL · **Para**: PeanoRF
**Responde a**: `doc/RESPUESTA-FOL-2026-09-23c.md` (vuestro commit `55288bb`). **Rectifica**: nuestra `RESPUESTA-PEANORF-2026-09-23b.md` §1 y §3.

> ## En una línea
>
> La propuesta (C) sigue en pie, con los siete, pero ahora tiene una condición del propietario que **no se negocia**: **FOL no puede depender de nada más allá de sí mismo.** Medido hoy, **los siete** la incumplen, no uno.

---

## 0 · La condición, en términos que se pueden comprobar

Después de la entrega, en `FOL/`:

1. no hay ningún `import` que no sea `FOL.*` o el core de Lean;
2. no hay en el código ningún identificador, `open` ni `namespace` de ROBINSON_PlusPlus, Peano o PeanoRF;
3. FOL sigue **sin `require`** en su lakefile, como hoy (medido).

**El control es el compilador, no el grep.** Como FOL no tiene `require`, cualquier import ajeno rompe su build propio. La entrega cuenta cuando compila **en el build de FOL**, y no antes. El §1.4 muestra por qué el grep no basta.

La condición vale también para el futuro. Si H3ter necesita algo con RPP **dentro** de estos módulos, esa parte no baja: se queda en PeanoRF como extensión vuestra sobre el módulo de FOL.

---

## 1 · Lo que hoy la incumple (medido en `55288bb`, sólo lectura)

### 1.1 · Imports: los siete

| dónde | qué |
|---|---|
| `Calculus/Subst.lean:7`, `Calculus/DerivesI.lean:7` | `import PeanoRF.Prelim` |
| `PeanoRF/Prelim.lean:31` | `import ROBINSON_PlusPlus.Minimal.Axioms` |
| `PeanoRF/Prelim.lean:32` | `import Peano.PeanoNat.Axioms`, que trae `Peano.PeanoNat` (`Axioms.lean:9`), y éste `Peano.Prelim.ExistsUnique` (`PeanoNat.lean:9`) |

Los otros cinco lo heredan a través de Subst o DerivesI: `SubstDerives:7-8`, `Consistency:7`, `Eq:7`, `Collapse:7-8`, `Slash:7-10`.

**Rectificación.** Nuestra (2) §3 decía de la tanda 1: «condición: ninguna, cero acoplamiento». **Era falso:** el acoplamiento está en el import. Y vuestro 23c §2 («seis de los siete dan CERO») contó identificadores, no imports. Cometimos los dos el mismo error, el que nosotros mismos os habíamos enunciado.

### 1.2 · Identificadores en el código

| dónde | qué |
|---|---|
| `Collapse.lean:72, 134, 174, 320, 395, 397, 398, 428` | `zero` de RPP (en `collapseT`, `collapseT_lift`, `collapseT_subst`, `collapseT_substT`, `collapseT_zero`, `grounded_zero`) |
| `Collapse.lean:396` | `zero_sym` de RPP |
| `Eq.lean:71-72, 74-91` | `ROBINSON_PlusPlus.Minimal.Axioms.succ` y `succ`: todo dentro de `eqI_congr_succ` |

Los demás, cero. Los `zero`/`succ` de `Subst:188-329`, `SubstDerives:98-99`, `Collapse:307-308` y `Slash:624-789` son etiquetas de `Nat` en `cases … with`, no de RPP.

### 1.3 · `open`

`Collapse.lean:61` (de fichero) y `Eq.lean:73, 80, 87, 90` (`open … in`): `ROBINSON_PlusPlus.Minimal.Axioms`.

### 1.4 · La que no se ve con grep

`Eq.lean` usa `substTerm_liftTerm` en 16 líneas (l. 38-255), 14 de ellas fuera de `eqI_congr_succ`: entre otras, `eqI_symm` (l. 34), que Slash usa. Es **nuestro** `FOL.substTerm_liftTerm` (`FOL/Theorems/Eq.lean:29`), pero a `Eq.lean` sólo le llega por este camino: `Prelim` → `ROBINSON_PlusPlus/Minimal/Axioms.lean:8` (`import FOL.Theorems.Eq`).

Si se re-apunta `Prelim` a `FOL.FOL`, el entorno de `Eq` se queda en `{FOL.FOL, FOL.Derives0}`. Que no compile lo deducimos del grafo; no lo hemos compilado. **La solución es un `import FOL.Theorems.Eq` propio en `Eq`.** El import de RPP estaba llevando una dependencia de FOL.

### 1.5 · Namespace

`namespace PeanoRF.Calculus` aparece en los siete: `Subst:54`, `DerivesI:57`, `SubstDerives:33`, `Consistency:42`, `Eq:21`, `Collapse:58`, `Slash:103`.

Dentro de FOL van bajo namespace de FOL. **El nombre de módulo y el de namespace los fijamos aquí al recibir.**

### 1.6bis · La nomenclatura, ya decidida (D6, 2026‑09‑26)

El propietario ha fijado la regla de subíndices, para FOL **y** para RPP: **el subíndice nombra un
CÁLCULO — `₀` el clásico (`Derives₀`), `ᵢ` el intuicionista — y sin subíndice va lo que no depende
de ninguno**; en snake_case, `derives0_…` / `derivesI_…`. Está entera en `FOL/NAMING-CONVENTIONS.md` §9.

⇒ Vuestro `Derivesᵢ` / `⊢ᵢ` / `derivesI_…` **encaja tal cual**. Al recibir, lo que la regla pide
renombrar en `Slash` es poco y os lo decimos ya, para que la tabla de `HA/*` y `Meta/AxiomCheck` no os
pille por sorpresa:

| hoy (`Slash`) | en FOL | por qué |
|---|---|---|
| `derives_empty_of_slashed`, `derives_rewrite_subst`, `derives_rewrite_back` | `derivesI_…` | `derives_…` sin marca queda reservado a `Derives` (`⊢`) |
| `disjunction_property`, `existence_property` | `derivesI_disjunction_property`, `derivesI_existence_property` | en FOL ya vive `DisjunctionProperty₀` —la de `⊢₀`, que es **FALSA** (`derives0_no_disjunction_property`)—; la vuestra es la **verdadera**, y sin marca las dos se confundirían |

Los `eqI_*`, `specI` y `consistI_syn` pasan como están.

⚠️ **Y un renombre en RPP que os toca de refilón**: el Hilbert intuicionista de RPP, `Prf₀`, pasa a
**`Prfᵢ`** (`prf0_…` → `prfI_…`; RPP ADR‑102), porque con `₀` decía lo contrario que en FOL. En
vuestro árbol sólo lo citan comentarios (`Meta/AxiomCheck.lean:207`, `sondeos/audit_2026-09-17b.lean:12,22`):
nada deja de compilar, pero la cita quedará vieja.

### 1.6 · Prosa (no bloquea la compilación, pero tampoco puede quedar como referencia viva)

- Citas a rutas vuestras: `DerivesI:18` (REFERENCE de RPP), `DerivesI:54` (`PeanoRF/Meta/AxiomCheck.lean`), `Collapse:15, 93, 296` (`sondeos/…`), `Slash:827` (`HA/Numerals.lean`), `Slash:831, 874` (`sondeos/junk_probe.lean`), y `Consistency:12, 21` (`Calculus/Soundness.lean`, que se queda con vosotros).
- `Subst:45-53`: en FOL el token `σ` no está reservado.
- Dos que son **nuestras**:
  - `DerivesI:31` cita `FOL/cuarentena/Inconsistencia.lean`, que ya no existe: es `FOL/Inconsistencia.lean`.
  - `Slash:114` dice que `fdepth` duplica `FOL.Canonical0.formulaComplexity`. Hoy el original es `FOL.Complexity.formulaComplexity` (`Complexity.lean:58`), idéntico salvo nombres. Ofrecisteis retirar `fdepth` en el mismo movimiento, y lo tomamos como parte de la entrega: FOL no admite duplicados literales.

Criterio: **la procedencia sí** («procede de PeanoRF, `55288bb`»); **las rutas y ADR de otro árbol como referencia viva, no**. Si preferís, las reescribimos nosotros al recibir.

---

## 2 · El parámetro de `collapseT`: «cerrado» no basta

En nuestra (2) §1 dimos por buena la frase de `Collapse.lean:41-43`: *«lo único que se usa del reemplazo es que sea cerrado»*. Leyendo las pruebas, **no es así**:

- `collapseT_idem` (l. 401) pasa por `collapseT_zero` (l. 395), que necesita `collapseT L d = d` **para toda `L`**.
- Eso vale para una constante `.func c []`, y falla para un término cerrado cualquiera. Razonado a mano, no compilado: con `d = .func s [.func c []]`, `L s 1 = true` y `L c 0 = false`, sale `collapseT L d = .func s [d]`, que no es `d`.
- Y `grounded_zero` (l. 428) cierra `substT ρ d = d` por `rfl`, que sólo es inmediato para una constante.

**Sugerencia** (sin compilar): parametrizad por el **símbolo**, `(c : String)`, con término por defecto `.func c []`. Las pruebas conservan su texto, cambiando `zero` por `.func c []` y `zero_sym` por `c`. HA instancia `c := zero_sym`, y `zero` es `.func zero_sym []` por definición (RPP `Minimal/Axioms.lean:66`). Si preferís un término, la hipótesis es «cerrado **y** fijo por el colapso», no «cerrado».

Y una cosa de paso: fuera de `Eq`, `eqI_congr_succ` debería salir en `HA/*` como `eqI_congr_fun1 succ_sym` (`Eq.lean:114`), por defeq al desplegar `succ`. Tampoco lo hemos compilado.

---

## 3 · Aviso: `FOL.Eigenvariable` se ha refactorizado (D5, ya en `master`)

Hecho el 2026‑09‑26: un `absTerm'` parametrizado por un predicado de símbolos junta el `absTerm` de `Eigenvariable` con los lemas de levantamiento de `Lift0`. **Se conservan los 40 nombres** (25 de `Eigenvariable`, 15 de `Lift0`) con su enunciado literal, `posDepth` es byte a byte el mismo, y los footprints no se movieron.

Lo que vuestros siete usan de esa zona, medido: **sólo `FOL.Eigenvariable.posDepth`** (`Eigenvariable.lean:235`), a través de `open FOL.Eigenvariable` (`SubstDerives:36`, `Slash:106`) y desplegado con `simp` (`SubstDerives:51-68, 156`; `Slash:410-411`). No usáis nada de `absTerm`/`absFormula`/`absDerives`/`occurs*`, y nada de `Lift0` salvo en prosa (`SubstDerives:12, 30`).

**Os garantizamos, hasta que vuestra entrega compile aquí:**

- `FOL.Eigenvariable.posDepth` con el mismo nombre (se sigue resolviendo con `open FOL.Eigenvariable`) y las mismas cuatro ecuaciones: `root` da 0; `left`/`right` de `p` dan `posDepth p`; `body p` da `posDepth p + 1`.
- `liftTerm`, `liftTerms`, `liftFormula`, `substTerm`, `substTerms`, `substFormula`, `getAt?`, `replaceAt`, `Pos` y `LocalRule` de `FOL.FOL` **con las mismas definiciones**, porque las desplegáis. D5 añade `absTerm'` y demuestra `liftTerm` como caso suyo; no lo redefine.
- El resto de lo que usáis, sin cambios:
  - `Derives₀` y sus 18 constructores, con su nombre y su orden de argumentos (`DerivesI:121-141`);
  - `_root_.derives0_to_derives` (`Derives0.lean:158`);
  - `FOL.Finitary0.{derives0_consistent_fin, derives0_not_P_fin, lkc_tval, tval}`;
  - `FOL.NDtoLK0.ndToLK`, `FOL.Derives2.derives0_iff_derives2`, `FOL.Propositional0.derives0_em_ctx` y `FOL.substTerm_liftTerm`;
  - y `Term`/`Formula` = `TermG String`/`FormulaG String` (`Collapse` y `Eq` escriben `String`).

**Rectificación de nuestra (2) §3:** no eran «cuatro módulos de FOL». Son **ocho por nombre** (`FOL`, `Derives0`, `Eigenvariable`, `Finitary0`, `NDtoLK0`, `Derives2`, `Propositional0`, `Theorems.Eq`) y **catorce contando el cierre**. Ninguno de los catorce se congela hasta que la entrega compile aquí.

---

## 4 · Lo que preguntamos, y es todo

1. **Fecha y forma de la entrega**: una tanda o dos.
2. **¿Prevé H3ter algo *dentro* de estos siete que necesite RPP o Peano?** Si es así, esa parte no baja (§0).

Del namespace, los nombres y la prosa nos encargamos aquí al recibir, salvo que prefiráis traerlo hecho. Desde aquí no se toca nada vuestro.
