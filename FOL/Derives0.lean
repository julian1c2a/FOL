/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: none
-- @importance: high

import FOL.FOL

/-!
# `FOL.Derives0` — el cálculo del que SÍ se puede hablar

⭐⭐ **PASO 0 de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`.**

## Por qué existe

🗑️ **2026‑10‑02 · las tres razones de abajo describían `Derives` CON `FOL/MetaRules.lean`, y ese
módulo se BORRÓ (ADR‑115 de RPP).** Sus cuatro `axiom` eran refutables sin usarlos
(`FOL/Inconsistencia.lean` §3). Sin ellos, `Derives` es `Derives₀` más `gen_rule`, que es
**admisible**: `FOL.Inconsistencia.derives_to_derives0`, por inducción sobre `Derives`. ⇒ Hoy
`Derives` **es sólido** (`derives_soundness`), **no** es sintácticamente completo (no decide `P`:
`derives_not_P`, `derives_not_negP`) y **admite inducción**. La conclusión sigue en pie por otra
razón: el sujeto de la metateoría es `Derives₀`, el cálculo **finitario**, y `Derives` deriva
exactamente lo mismo (los dos puentes).

Lo que se escribió el 2026‑09‑14, como registro: `Derives` no servía como **sujeto** de ningún
teorema metateórico, y estaba medido:

1. ⛔ **Era sintácticamente COMPLETO**: `raa` tomaba una **función de Lean**, así que si `Γ ⊬ A`
   esa función existía **vacuamente** y `Γ ⊢ ¬A`. Todo contexto decidía toda fórmula, en tres
   líneas (`../ROBINSON_PlusPlus/sondeos/HenkinSaleDeRaa.lean`, que cita el `raa` borrado y por
   eso ya no compila). ⇒ **no era r.e.**
2. ⛔ **«No es SÓLIDO»**: `FOL/Inconsistencia.lean` compilaba `False` a partir de cualquier
   teorema de solidez para `Derives`, con footprint `[propext, FOL.MetaRules.raa]`. Se leyó al
   revés: lo falso era `raa`, no la solidez.
3. ⛔ **«No admite INDUCCIÓN»** (**M‑11**, ADR‑029, que la declaraba **permanente**): los cuatro
   axiomas de `FOL/MetaRules.lean` habitaban el tipo y no eran aplicaciones de constructor. El
   recursor los cubría igual: lo que había que retirar eran los axiomas, no la inducción.

⇒ Era ADR‑024 otra vez: **`⊢` era la herramienta de trabajo de RPP, no el sujeto**. RPP retiró
esa capa el 2026‑10‑02 (ADR‑115 de RPP).

## Qué es `Derives₀`

Los constructores de `Derives` (que son 22) **menos `gen_rule`**: **21**. Es decir: **deducción
natural clásica de primer orden con igualdad**, finitaria, y **con cero habitantes‑axioma**.
(Hasta el 2026‑10‑02 se definía además por diferencia, «**sin** los cuatro axiomas de
`MetaRules`»; 🗑️ borrado ese módulo con ADR‑115 de RPP, `Derives` tampoco tiene ninguno.)

| | `Derives` | `Derives₀` |
|---|---|---|
| constructores | 22 | **21** |
| axiomas que lo habitan | **0** (eran 4 hasta ADR‑115 de RPP; ADR‑029 los llamaba «un suelo de cuatro» y declaraba M‑11 PERMANENTE) | **0** |
| ¿`induction`? | ✅ **sí** (M‑11 la prohibía hasta ADR‑115 de RPP) | ✅ **sí** |
| ¿ω‑regla `gen_rule`? | sí, y es **admisible** (`derives_to_derives0`) | ❌ **no** — premisa infinitaria |
| ¿sólido? | ✅ sí (`derives_soundness`, demostrada el 2026‑10‑02; lo era también antes, cuando lo falso era `raa`) | ✅ sí (`derives0_soundness`) |
| ¿sintácticamente completo? | ❌ **no** (`derives_not_P`, `derives_not_negP`); con `raa` postulado lo era (patología) | ❌ no (`derives0_not_complete`), y por eso vale |

### ⚠️ Por qué se quita también `gen_rule`

`gen_rule : (∀ n : Term, Γ ⊢ A[n]) → Γ ⊢ ∀A` tiene **premisa infinitaria**: es la ω‑regla sobre
términos. Un cálculo **finitario** no la lleva. La introducción de `∀` la da `intro_forall`
—la regla de la eigenvariable, con De Bruijn—, que es la estándar.

⭐ **Y el coste para lo que ya existía fue CERO**: `cuarentena/Completeness.lean` (borrado el
2026‑09‑23) usaba **14** constructores de `Derives` y **`gen_rule` no estaba entre ellos** (medido). El desarrollo
de completitud ya vive dentro del fragmento finitario.

### ⚠️ Lo que NO se pierde al quitar los cuatro axiomas

**Se pierde sólo la fuerza META**, y era falsa: los cuatro enunciados se refutan sin usarlos
(`FOL/Inconsistencia.lean` §3), y por eso se borraron (ADR‑115 de RPP). Medido en
`../ROBINSON_PlusPlus/sondeos/DerivesSinMetaReglas.lean`: el inductivo pelado ya tiene las
versiones **objeto** de las cuatro, las seis con footprint `[propext]`.

| meta‑regla de `MetaRules` (premisa‑FUNCIÓN; 🗑️ borradas con ADR‑115 de RPP) | equivalente OBJETO aquí |
|---|---|
| `imp_intro (Γ ⊢ A → Γ ⊢ B)` | `Derives₀.intro_impl` |
| `raa (Γ ⊢ A → Γ ⊢ ⊥)` | `Derives₀.intro_impl` con `B := ⊥` |
| `or_elim` | `Derives₀.elim_or` |
| `ex_elim` | `Derives₀.elim_ex` |
| `dne` | `Derives₀.dne_rule` / `Derives₀.dne_schema` |

## ⭐ Y esto NO toca a ROBINSON_PlusPlus

`Derives₀` es un objeto **NUEVO**, no un reemplazo. El puente de este módulo va en **una**
dirección:

    derives0_to_derives : Γ ⊢₀ f → Γ ⊢ f

🏁 Desde el 2026‑10‑02 está también la otra, en `FOL/Inconsistencia.lean` (en el build):
`derives_to_derives0 : Γ ⊢ f → Γ ⊢₀ f`, porque `gen_rule` es admisible con una constante fresca.
Sin las meta‑reglas, los dos cálculos derivan exactamente lo mismo.

Al entrar `Derives₀` (2026‑09‑14), RPP no tuvo que tocar ni una cita de `Derives` ni de sus
meta‑reglas —`gen` 323 usos, los cuatro axiomas 320, los constructores `Derives.*` 164 (censo
del 2026‑09‑12)—. 🗑️ El 2026‑10‑02 RPP retiró su capa `⊢` (27 módulos, 633 declaraciones) y FOL
borró `FOL/MetaRules.lean`: desde entonces la librería de RPP (lo que compila `lake build`) no
usa `Derives`; sólo lo usan sondeos fuera del build (`MetaReglasRefutables.lean`,
`DerivesSinMetaReglas.lean`) (medido ese día). Este módulo entra por el barrel `FOL`, que RPP
**no importa**.

⇒ Fue mucho más barato que la «reparación de fondo» de `cuarentena/README.md` §8 (partir
`Derives`/`DerivesW`), y dio lo mismo para lo que hacía falta: un cálculo sobre el que M‑11 no
aplicaba. La reparación de fondo acabó siendo otra: retirar las meta‑reglas (ADR‑115 de RPP), y
desde entonces M‑11 tampoco aplica a `Derives`.

## 🏁 Lo que venía después — **los TRES, hechos**

1. 🏁 **`derives0_soundness`** — `FOL.Metamath.Soundness0` (ADR‑034).
2. 🏁 El lema de **renombrado** — `FOL.Rename`, más el paso de eigenvariable
   (`FOL.Eigenvariable.derives0_gen_fresh`), que era la mitad que faltaba.
3. 🏁 Portada la completitud a `Derives₀` — `FOL.Canonical0.completeness₀`, y con ella
   `derives0_complete_iff`, compacidad y Löwenheim–Skolem descendente.
-/

/-- **Deducción natural clásica de FOL⁼, finitaria y sin habitantes‑axioma.**
Los 21 constructores de `Derives` menos la ω‑regla `gen_rule`. ⇒ **se puede inducir sobre él**. -/
inductive Derives₀ {Sym : Type} : List (FormulaG Sym) → FormulaG Sym → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives₀ Γ f

  -- Reglas estándar de Deducción Natural
  | intro_impl : ∀ Γ A B, Derives₀ (A :: Γ) B → Derives₀ Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives₀ Γ (.impl A B) → Derives₀ Γ A → Derives₀ Γ B

  -- Conjunción
  | intro_and  : ∀ Γ A B, Derives₀ Γ A → Derives₀ Γ B → Derives₀ Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives₀ Γ (.and A B) → Derives₀ Γ A
  | elim_and_r : ∀ Γ A B, Derives₀ Γ (.and A B) → Derives₀ Γ B

  -- Disyunción
  | intro_or_l : ∀ Γ A B, Derives₀ Γ A → Derives₀ Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives₀ Γ B → Derives₀ Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives₀ Γ (.or A B) → Derives₀ (A :: Γ) C → Derives₀ (B :: Γ) C →
      Derives₀ Γ C

  -- Cuantificadores. ⚠️ `intro_forall` ES la regla de la eigenvariable: el contexto se LEVANTA,
  -- y eso es lo que hace las veces de «constante fresca» sin ampliar el lenguaje.
  | intro_forall : ∀ Γ A, Derives₀ (Γ.map (liftFormula 0)) A → Derives₀ Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives₀ Γ (.forall A) → Derives₀ Γ (substFormula 0 t A)
  | intro_ex : ∀ Γ A t, Derives₀ Γ (substFormula 0 t A) → Derives₀ Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives₀ Γ (.ex A) →
      Derives₀ (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives₀ Γ B

  -- Ex falso quodlibet
  | bot_elim : ∀ Γ A, Derives₀ Γ ⊥ → Derives₀ Γ A

  -- Debilitamiento
  | weakening : ∀ Γ Γ' f, Derives₀ Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives₀ Γ' f

  -- Reescritura en subexpresión exacta
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derives₀ Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derives₀ Γ f'

  -- Clásica. ⚠️ `gen_rule` NO está: su premisa es infinitaria (ω‑regla).
  | dne_rule : ∀ Γ A, Derives₀ Γ (neg (neg A)) → Derives₀ Γ A
  | dne_schema : ∀ Γ A, Derives₀ Γ (.impl (neg (neg A)) A)
  | forall_not_ex_not : ∀ Γ A, Derives₀ Γ (.impl (neg (.forall A)) (.ex (neg A)))

  -- Igualdad
  | refl  : ∀ Γ t, Derives₀ Γ (.eq t t)
  | subst : ∀ Γ t₁ t₂ f, Derives₀ Γ (.eq t₁ t₂) → Derives₀ Γ (substFormula 0 t₁ f) →
      Derives₀ Γ (substFormula 0 t₂ f)

infix:50 " ⊢₀ " => Derives₀

/-- **El encaje**: todo lo que `Derives₀` deriva, `Derives` lo deriva.

⭐ **Y esta prueba es la demostración de que el Paso 0 funciona**: es una **inducción sobre
`Derives₀`**. Cada caso es su constructor homónimo. (El 2026‑09‑14 se añadía que sobre `Derives`
esa inducción sería ilegítima por M‑11; desde ADR‑115 de RPP no lo es: ningún axioma lo habita.)

🏁 **La recíproca está demostrada desde el 2026‑10‑02**: `FOL.Inconsistencia.derives_to_derives0`,
por inducción sobre `Derives`, con `gen_rule` admisible por una constante fresca. Aquí se decía
que «NO vale, y a propósito»; era falso también entonces: la inducción no ve los axiomas, la
misma prueba compilaba con `FOL/MetaRules.lean` importado, y junto a `raa` daba `False`. La
metateoría sigue viviendo de este lado: `Derives₀` es el cálculo finitario. -/
theorem derives0_to_derives : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢₀ f) → (Γ ⊢ f) := by
  intro Γ f h
  induction h with
  | hyp Γ f hmem => exact Derives.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives.weakening Γ Γ' f ih hsub
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact Derives.rewrite_at Γ f f' p sub sub' ih hget hrule heq
  | dne_rule Γ A _ ih => exact Derives.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives.forall_not_ex_not Γ A
  | refl Γ t => exact Derives.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives.subst Γ t₁ t₂ f ih1 ih2

/-- Las versiones OBJETO de las meta‑reglas que en `Derives` eran axiomas (🗑️ borrados con
`FOL/MetaRules.lean`, ADR‑115 de RPP: eran refutables). Aquí son teoremas de una línea, y por eso
`Derives₀` no pierde ninguna REGLA: sólo pierde la fuerza **meta** (la premisa‑función), que era
exactamente la patología, y era falsa (`FOL.Inconsistencia.raa_refutable`). -/
theorem derives0_raa {Γ : List Formula} {A : Formula}
    (h : Derives₀ (A :: Γ) Formula.bottom) : Γ ⊢₀ neg A :=
  Derives₀.intro_impl Γ A Formula.bottom h

-- ⚠️ CRITERIO DE ACEPTACIÓN del Paso 0 (`PLAN-COMPLETITUD-FINITISTA.md` §9): el recursor no
-- puede depender de ningún axioma del proyecto. Se imprime en el build, a la vista.
#print axioms Derives₀.rec
#print axioms derives0_to_derives
#print axioms derives0_raa
