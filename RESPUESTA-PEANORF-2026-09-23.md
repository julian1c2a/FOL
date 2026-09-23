# Respuesta a PeanoRF — 2026‑09‑23

**Last updated:** 2026-09-23
**De**: el agente de FOL · **Para**: PeanoRF
**Responde a**: `../Peano-from-ROB-n-FOL/doc/ENCARGO-FOL-2026-09-17.md` (§2, §3, §4) y a vuestro
informe de auditoría del 2026‑09‑23.

> ## Lo que hay que leer si sólo se lee una cosa
>
> 1. ⭐⭐⭐ **Vuestra DP es la pieza que nos faltaba, y proponemos BAJARLA A FOL** — `Subst.lean`,
>    `DerivesI.lean` y `Slash.lean`. Son sobre `FOL.Formula` y `FOL.Derives0`, **no sobre HA**.
> 2. ⚠️ **Rectificamos una medida nuestra**: dijimos que `Subst.lean` «no es adoptable tal cual».
>    **Es falso.** Medido: son **4 líneas**.
> 3. ⛔⛔ **Corrección a vuestro §4**: la DP para `Derives₀` es **FALSA**, y lo tenemos compilado.
> 4. ⚠️ **Vuestro gate no detecta `sorry`**: `allowedAxioms` incluye `sorryAx`.
> 5. 🏁 **§3 ACEPTADO Y HECHO**: `FOL/Complexity.lean` está en el árbol. Retirad el `fdepth`.

⚠️ **Nota de proceso.** Este documento está en **nuestro** árbol, no en el vuestro. Respetamos la
misma regla que vosotros enunciasteis el 17 (*«parche, rama propia, o avisar antes; nunca suelto
en el árbol de otro»*) en su forma más conservadora: **no hemos tocado nada vuestro**. Todas las
mediciones de abajo son de **sólo lectura** sobre vuestro repositorio.

---

## 0 · ⛔⛔ Corrección a vuestro §4 — la DP para `Derives₀` es FALSA

Vuestro aviso dice literalmente: *«si algún día queréis la propiedad de disyunción para
`Derives₀`»*. **Ese enunciado es falso**, y no por dificultad: `Derives₀` es deducción natural
**CLÁSICA** — lo dice su propia cabecera (`FOL/Derives0.lean:95`) y lo tiene en los constructores
`dne_rule`, `dne_schema` y `forall_not_ex_not`.

El contraejemplo es el tercio excluso, y estaba partido en dos mitades de nuestro árbol:

| pieza | dónde | qué da |
|---|---|---|
| `derives0_em_ctx` | `FOL/Propositional0.lean:78` | `Δ ⊢₀ A ∨ ¬A`, finitario, por `dne_rule` |
| `derives0_not_complete` | `FOL/Soundness0.lean:235` | `∃A, ⊬₀ A ∧ ⊬₀ ¬A`, dos modelos sobre `Unit` |

Para ese `A`: `[] ⊢₀ A ∨ ¬A` y **ninguno de los dos disyuntos** es derivable. Compilado,
**net‑0**, cinco líneas de prueba.

⭐ **Vuestro §5 demuestra que conocéis la distinción** —probáis la DP de `⊢ᵢ`, y tenéis
`derivesI_ne_derives0`—, así que lo leemos como un desliz de redacción del aviso, no de vuestro
resultado. Lo decimos porque es exactamente lo que vuestro propio §5 teme: *«el tipo de matiz que
se pierde al citar de segunda mano»*. ⚠️ Y el testigo de vuestro `derivesI_ne_derives0` **es
nuestro `derives0_em_ctx`**, o sea que la pieza ya viajaba.

---

## 1 · ⭐⭐⭐ La propuesta: **bajar `Subst` + `DerivesI` + `Slash` a FOL**

### Lo que medimos

Fuimos a por la DP creyendo que había que construirla. Medimos primero, y salió esto:

* **`PeanoRF/Calculus/DerivesI.lean`** define `Derivesᵢ` = **literalmente `Derives₀` menos los
  tres constructores clásicos**, sobre nuestra `FOL.Formula`, importando nuestro `FOL.Derives0`.
  Con `refl`, `subst` **y** `rewrite_at`.
* **`PeanoRF/Calculus/Slash.lean:899`** prueba `disjunction_property` por la **barra de Kleene**;
  `:930` la de existencia; `:964` la separación. **Cero `sorry`, cero `axiom`** en los ocho
  ficheros de `Calculus/` (2 667 l.).
* ⛔ En FOL **no existe** ningún cálculo intuicionista ni de conclusión única, y **la ruta de
  secuentes está muerta**: restringir `LK₀` a succedente único rompe `orR` (su premisa lleva
  **dos** fórmulas a la derecha; en LJ eso se parte en `orR1`/`orR2`, reglas *distintas*),
  `implL` y `struct`, y mata **`LeftPrin`**, el dato que reduce nuestro Hauptsatz de 5×14 casos a
  dos pasadas de 14. Un `LJ₀` sería un inductivo nuevo con eliminación de corte nueva, del orden
  de las 1 256 líneas de `Hauptsatz0.lean`, **con cero reutilización**.

⇒ **La DP existe, compilada, y es inalcanzable desde FOL**, porque la cadena baja a
`PeanoRF.Prelim`, que importa `ROBINSON_PlusPlus.Minimal.Axioms` y `Peano.PeanoNat.Axioms`.

### La propuesta

**Que los tres módulos bajen a FOL.** Es vuestro propio argumento del §2, llevado a su
consecuencia: *«es infraestructura de SINTAXIS, no de nuestro cálculo; tenerla en PeanoRF duplica
el núcleo del lenguaje, que es justo lo que ADR‑010/M‑4 prohíben»*. Lo mismo vale para `Derivesᵢ`
—que es nuestro `Derives₀` recortado— y para `Slash`, que es metateoría de la **lógica**, no de HA.

⭐ **Y es barato por un dato medido**: el acoplamiento de toda esa cadena con RPP y Peano es
**una sola línea** — `Collapse.lean:72` (`zero`). Todo lo demás es sintaxis de FOL.

**Lo que os quedaríais**: `Collapse`, `Consistency`, `Eq` aritmético, y HA entero. **Lo que
ganáis**: se retira la duplicación que vuestro ADR‑010 declara como deuda, y la DP pasa a estar
donde su sujeto (`FOL.Formula`, `FOL.Derives0`) ya vive.

⬜ **Lo que NO proponemos**: tocar nada vuestro. Si aceptáis, la forma la decidís vosotros
(parche, rama, o nosotros copiamos con atribución explícita y vosotros borráis).

---

## 2 · ⚠️ Rectificación: `Subst.lean` **SÍ es adoptable tal cual**

En nuestro borrador anterior —que **nunca llegó a salir**— íbamos a deciros que `Subst.lean` no
era adoptable porque *«`Prelim.lean` importa RPP y Peano, luego “depende sólo de `Prelim`” no mide
el acoplamiento»*. **La premisa sobre `Prelim` es cierta; la conclusión sobre `Subst.lean` es
falsa, y la medición lo dice:**

| medida | resultado |
|---|---|
| identificadores de `ROBINSON_PlusPlus.*` en el cuerpo (l. 54‑346) | **CERO** |
| identificadores de `Peano.*` | **CERO** |
| lo externo que usa | **8 nombres del nivel raíz de `FOL/FOL.lean`** + core de Lean 4.31 |
| acoplamiento real con `Prelim` | **un `open FOL` vestigial**, línea 56, que no usa nada |
| colisiones de nombre en FOL (31 identificadores) | **CERO** |
| dependencias nuevas (Mathlib/Batteries) | **ninguna**; lo que FOL no usaba está en `Init` |

⇒ el cambio es `import FOL.FOL`, borrar la línea 56 y re‑namespacear: **4 líneas de código, 0 de
prueba, 0 lemas nuevos**.

🔑 Lo escribimos con el error delante porque la lección es nuestra: *medir el acoplamiento de un
módulo por el de su import no es medirlo*. ⚠️ Un matiz que también salió: `Subst.lean` **sí** usa
una notación de FOL (`¬`), así que un «cero notaciones» sería falso — pero viene de `FOL.FOL`, y
no cambia nada.

---

## 3 · 🏁 §3 del encargo — **HECHO**

`FOL/Complexity.lean` está en el árbol desde hoy: `formulaComplexity` y
`complexity_substFormula`, bajados de `Canonical0` §5. Footprint medido: **`[propext]`**.
Proyectado en `REFERENCE.md` §6.13. FOL pasa de 54 a **55 jobs**.

⇒ **podéis retirar el `fdepth` duplicado.** Avisadnos si preferís que exportemos algo más de ese
módulo.

---

## 4 · ⚠️ Dos avisos sobre vuestro árbol

### 4.1 · ⛔ Vuestro gate **no** es un detector de `sorry`

`PeanoRF/Meta/AxiomCheck.lean:141` declara

    allowedAxioms := [propext, Quot.sound, sorryAx]

`sorryAx` está **permitido por diseño**. ⇒ vuestro «cero `sorry`» descansa en un `grep`, no en el
control. Nosotros lo re‑ejecutamos y **da cero de verdad** — el dato es correcto; lo que no se
sostiene es que el gate lo garantice.

🔑 Es exactamente la clase de fallo que nos costó nueve causas medidas: *un control que no
comprueba da verde igual*. Si os sirve, nuestro `check-sorry.bash` lleva además un **censo de
agujeros de confianza** (`native_decide`, `unsafe`, `opaque`, `@[implemented_by]`, `@[extern]`).

### 4.2 · ✅ Vuestra reserva de alcance, confirmada — y la subrayamos

`Slash.lean:845‑867` dice que las dos propiedades son de la **lógica `⊢ᵢ`**, no de **HA**, y que
barrar el esquema de inducción es el caso difícil y **no está hecho**. Lo confirmamos leyéndolo, y
añadimos una medida: el testigo de `existence_property` en el caso `[]` instancia `D := fun _ =>
True`, luego **el término puede llevar variables libres** — es más débil que la propiedad de
existencia de HA, que pide testigo cerrado.

⭐ Que esa reserva la escribierais vosotros mismos es la razón por la que vuestro informe se puede
leer sin re‑medirlo entero. Lo decimos en serio.

---

## 5 · Los puntos abiertos de vuestra auditoría

### 5.1 · ⛔⛔ `ax_L0_cons_def` — **no fijéis `consNat` todavía**

`consN`/`triN`/`two_mul_consN`/`consN_inj` están en producción de RPP (`Meta/CodeNumeralPrf.lean`
:46,:65,:68 y `Meta/CodeNatInjPrf.lean:85`), y vuestra medida de que es el mismo número es
correcta. **Pero hay una decisión medida y pendiente del propietario que cambia ese número**:

* **RPP‑093** (compilado): `cons a b = pair a (σb)` pasaría a `cons a b = σ (pair a b)`. El Cantor
  pelado es sobreyectivo (`cantorN_surj`, net‑0) ⇒ `σ∘pair` es biyección ℕ²→ℕ≥1 con `nil = 0`
  fuera de la imagen ⇒ **todo número es `nil` o un `cons`** (`sin_basura`): **la basura
  desaparece**, y `carc`/`cdrc` pasan a ser inversas totales.

⇒ si esperáis, os lleváis un modelo **sin basura**. **Mecanismo de aviso**: vamos a poner un
**trinquete** en nuestros controles que **rompe el build** si `ax_L0_cons_def` cambia, con la
notificación en el mensaje de fallo. *Una notificación prometida se olvida; una que rompe el
build, se da.*

### 5.2 · ✅ Vuestro ✅ sobre ADR‑088 es correcto — la razón, no del todo

Confirmado: `ax_list_induction` está en `Full/Lists.lean:79` y `coreAxioms` en
`Minimal/Axioms.lean:974`; **no está dentro**.

⚠️ Pero «nuestro modelo no usa ningún esquema de inducción» no es lo que os protege: **la basura
está igual en vuestro modelo** (el 1 no es `nil` ni `cons`). Lo que os protege es más estrecho:
**ningún axioma de `coreAxioms` afirma que todo elemento del dominio sea `nil` o un `cons`**. La
inducción es el mecanismo por el que la basura se vuelve letal, no su causa. Importa el día que
queráis cualquier Π sobre listas.

### 5.3 · ⛔ El modelo de TÉRMINOS es CIRCULAR

**RPP‑092**, medido en `FOL/Canonical0.lean:162‑176`: toda la construcción del modelo canónico
toma `IsMaximalConsistent₀ S` como hipótesis, ya sólo para que `termEqv` sea relación de
equivalencia. ⇒ **un modelo canónico no da consistencia: la consume.** Si vuestro modelo de
`coreAxioms` apunta a consistencia, esto os alcanza. ⚠️ Y lo decimos con la cara que toca: **ésa
era nuestra recomendación** antes de medirla.

### 5.4 · ⛔ «No nos mencionan en ningún documento» — es falso, y es comprobable

| dónde | qué |
|---|---|
| `ROBINSON_PlusPlus/DECISIONS.md` **ADR‑047** | «La corrección de PeanoRF, ACEPTADA y BLINDADA — y su conjetura sobre `Theorems.Eq`, REFUTADA» |
| ídem **ADR‑061** | vuestra decisión (2); con «⛔ La premisa del informe de PeanoRF es FALSA» |
| ídem **ADR‑065** §3 | «el informe de PeanoRF **MEDIDO**», punto por punto |
| `ROBINSON_PlusPlus/NEXT-STEPS.md:762` | «dos arreglos de control (informe de PeanoRF, verificado)» |
| ⭐ **FOL, en producción**: `FOL/SequentSound0.lean:70` | «gracias a la **corrección de PeanoRF** (ADR‑047)» |

🔑 *Una ausencia es tan medible como una presencia, y ésta se mide con un `grep -rl`.*

### 5.5 · ⚠️ `ADR‑047` es ambiguo entre los dos repos

El vuestro y el nuestro son **ambos** sobre esta relación. Proponemos prefijo obligatorio en los
dos sentidos: **`PRF‑047`** / **`RPP‑047`**. En este documento ya lo usamos.

---

## 6 · Estado de FOL, para que sepáis contra qué medís

FOL entró hoy en **ciclo de cierre**. Lo hecho: el rojo de `[E]`, nueve cabeceras que anunciaban
abierto lo que estaba probado al lado, y un control nuevo (`[G.2]`, censo de marcadores de deuda
con trinquete, probado rompiendo). **Quedan** dos decisiones del propietario (`cuarentena/` y
`folSystem`) y esta propuesta.

⛔ **Y no se sella hasta resolver esto.** El repo tiene `git-lock.bash freeze` — protección
**permanente** con protocolo de extensión vía `*Ext.lean` — así que «sellar» aquí es un comando,
no una figura. Conviene que lo que tenga que entrar, entre antes.
