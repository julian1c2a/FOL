/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Lift0
-- @axiom_system: classical
-- @importance: high

import FOL.Lift0

/-!
# `FOL.Henkin0` — **el paso de Henkin**: añadir un testigo preserva la consistencia

⭐⭐ El corazón del ensamblaje de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2.

    henkin_step_consistent₀ :
        IsConsistent₀ S  →  (c fresca en S y en A)  →
        IsConsistent₀ (S ∪ { (∃A) → A[c] })

Es **donde paga** `derives0_gen_fresh` (ADR‑036). Todo lo demás del ensamblaje —la iteración ω, el
suministro de constantes— es bookkeeping alrededor de este teorema.

⭐ Desde el 2026‑09‑27 el paso se demuestra **en positivo**: `henkin_step_derives` TRANSFORMA una
derivación de `⊥` desde `S ∪ {H}` en una desde `S`, y `henkin_step_consistent₀` es su corolario de
una línea. La forma positiva es la que consume `Skolem0.henkin_conservative₀` (la vía sintáctica).

## La prueba, en seis pasos

1. Si `S ∪ {H}` fuera inconsistente, hay un `Γ` **finito** con `Γ ⊢₀ ⊥`. Se saca `H` fuera
   (`ctx_split`, sin decidir ninguna igualdad): `Γ' ⊆ S` y `H :: Γ' ⊢₀ ⊥`.
2. `intro_impl` —que aquí **es** el teorema de deducción, porque es un **constructor**— da
   `Γ' ⊢₀ ¬H`.
3. Clásicamente, de `¬(P → Q)` salen `P` y `¬Q` (`neg_impl_left` / `neg_impl_right`, con
   `dne_rule`). ⚠️ Lo clásico es del **cálculo** (`dne_rule` es un constructor de `Derives₀`), no
   del metanivel: los dos lemas no dependen de ningún axioma de Lean.
4. ⭐ `c` es fresca en `Γ'` **porque `Γ' ⊆ S`** — y aquí está el punto fino: `derives0_gen_fresh`
   sólo pide frescura en el **contexto finito**, que es justo lo que `DerivesSet₀` entrega.
5. `derives0_gen_fresh` sobre `Γ' ⊢₀ ¬A[c]` da `Γ' ⊢₀ ∀(¬A)`, porque
   `absFormula c 0 (¬A[c]) = ¬A` — ahí se juntan `absFormula_subst`, `absFormula_eq_lift`
   (`c` no aparece en `A`) y `substFormula_lift_var`.
6. `∃A` y `∀¬A` se contradicen (`derives0_ex_forall_neg_absurd`, que es lo que obligó a tener
   `derives0_lift`).

## 📏 Footprint

⭐ **Ninguna constante de `FOL.Henkin0` lleva `Classical.choice`** (auditoría de constructividad,
2026‑09‑27, medido sobre el entorno compilado: `auditoria/constructividad-2026-09-27/despues/`):

* **ningún axioma**: `DerivesSet₀`, `IsConsistent₀`, `henkinAx`, `neg_impl_left`,
  `neg_impl_right` y ⭐ `ctx_split`;
* `[propext, Quot.sound]`: `abs_neg_witness`, `henkin_step_derives` y `henkin_step_consistent₀`.

**Cero axiomas del proyecto.** Hasta el 2026‑09‑27 `henkin_step_consistent₀` llevaba
`Classical.choice`, y era suyo: el `filter` del paso 1, bajo `open Classical`, decidía
`x = henkinAx c A` con `Classical.propDecidable`. `ctx_split` parte el contexto con la disyunción
que la hipótesis ya entrega, sin decidir nada.

## 🏁 Lo que ESTE módulo no hace — y dónde está ya hecho (2026‑09‑16, ADR‑039)

Este módulo da el **paso**. La **extensión completa** está construida en los dos módulos que
vienen encima:

* `FOL.Fresh0` — el **suministro de constantes frescas** (`shiftTheory`, `cst`, `exists_fresh`);
* `FOL.HenkinLimit0` — la **iteración ω** y el límite: consistente si `S` lo es, y con un testigo
  para cada fórmula.

⚠️⚠️ **Y aquí decía algo que la medición refutó.** El texto anterior era:

> ⚠️ **No construye la extensión completa.** Da el **paso**; falta la iteración ω y, sobre todo,
> el **suministro de constantes frescas** para un `S` arbitrario, que exige meter la teoría en un
> sublenguaje (`FOL.Rename`) y **eso** pasa por descomponer cadenas ⇒ `Classical.choice` por la
> vía del `String` del núcleo.
>
> 🔑 La parte **matemática** está aquí y es finitaria; lo que falta es **combinatoria de nombres**.

Lo del sublenguaje era correcto. Lo de **descomponer cadenas, a medias**: la construcción no descompone
ninguna — la conservatividad del renombrado se obtiene **mapeando con la inversa** (`invOf`,
retirada: ver abajo), y el
`Classical.choice` que aparece viene de ahí, de `Exists.choose`, del tercio excluso de
`cst_bound_sym` y de los lemas de `String` del núcleo tras `shift_inj`/`cst_inj`
(`String.append_right_inj`; `FOL.Fresh0` §Footprint, ADR‑069 §4). Y no era
«combinatoria de nombres»: son **dos** propiedades de `cst` (inyectividad y estar fuera de la
imagen del desplazamiento), de tres a cinco líneas cada una.

⚠️⚠️ **Rectificación, 2026‑09‑27** (auditoría de constructividad, medido). El párrafo anterior
tampoco acertaba con el `Classical.choice`: **ninguna** de las fuentes que enumera era necesaria, y
le faltaban dos.

* `String.append_right_inj` y `shift_inj` nunca lo llevaron (`[propext, Quot.sound]`). Lo de
  `String` venía de la `ReflBEq String` que `not_eq_of_beq_eq_false` sintetizaba a través de
  `String.instOrd`, que decodifica UTF‑8, en `cst_zero_ne`/`cst_ne_shift`. Hoy van por
  `of_decide_eq_false` con `String.decEq`: `[propext]`.
* `Exists.choose` (la cota `bnd` de `FOL.HenkinLimit0`) → cota **calculada**.
* El tercio excluso de `cst_bound_sym` → la cota `s.utf8ByteSize`.
* `invOf` → `Fresh0.unshift`, inversa GLOBAL de `shift` calculada sobre bytes. `invOf` se retiró.
* Faltaba una **aquí mismo**: el `filter` del paso 1, bajo `open Classical`. Hoy lo hace
  `ctx_split`, sin ningún axioma.
* Y faltaba la sobreyectividad de `FOL.Enumeration` (la usa `HenkinLimit0.henLimit_witness`), que
  decodificaba con `String.toList`. Hoy va por `String.exists_eq_ofList` (`[propext]`) y mide
  `[propext, Quot.sound]`.

⚠️ Y «la construcción no descompone ninguna [cadena]» ya no es cierto: `unshift` descompone
`shift s` para devolver `s`. Pero lo hace por **bytes**, y la capa de bytes no lleva
`Classical.choice`; en v4.31 lo trae **decodificar** UTF‑8, no descomponer. Hoy ninguna constante de
`FOL.Henkin0`, `FOL.Fresh0`, `FOL.HenkinLimit0` ni `FOL.Rename` lleva `Classical.choice`.
-/

namespace FOL.Henkin0

open FOL.Eigenvariable
open FOL.Lift0

/-- Derivabilidad desde un CONJUNTO: existe un contexto **finito** dentro de `S` que lo deriva.
⭐ La compacidad sintáctica está metida en la definición, y es lo que hace que la frescura sólo
haga falta en un contexto finito. -/
def DerivesSet₀ (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ Γ : List Formula, (∀ g, g ∈ Γ → S g) ∧ (Γ ⊢₀ f)

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

def IsConsistent₀ (S : Formula → Prop) : Prop := Not (S ⊢₀* Formula.bottom)

/-- El axioma de Henkin para `A` con testigo la constante `c`. -/
def henkinAx (c : String) (A : Formula) : Formula :=
  Formula.impl (Formula.ex A) (substFormula 0 (Term.func c []) A)

-- ============================================================
-- §1 · Dos pasos clásicos sobre `¬(P → Q)`
-- ============================================================

theorem neg_impl_left {Γ : List Formula} {P Q : Formula}
    (h : Γ ⊢₀ neg (Formula.impl P Q)) : Γ ⊢₀ P := by
  refine Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_)
  have hH : (neg P :: Γ) ⊢₀ Formula.impl P Q := by
    refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
    exact Derives₀.elim_impl _ P Formula.bottom
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ _ Formula.bottom
    (Derives₀.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)) hH

theorem neg_impl_right {Γ : List Formula} {P Q : Formula}
    (h : Γ ⊢₀ neg (Formula.impl P Q)) : Γ ⊢₀ neg Q := by
  refine Derives₀.intro_impl _ _ _ ?_
  have hH : (Q :: Γ) ⊢₀ Formula.impl P Q :=
    Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  exact Derives₀.elim_impl _ _ Formula.bottom
    (Derives₀.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)) hH

-- ============================================================
-- §2 · ⭐ La ecuación que hace funcionar el paso
-- ============================================================

/-- ⭐⭐ **Abstraer `c` en `¬A[c]` devuelve `¬A`.** Es el punto exacto donde encajan las tres
piezas: `absFormula_subst` (conmutación), `absFormula_eq_lift` (`c` no aparece en `A`) y
`substFormula_lift_var` (el lift se deshace). -/
theorem abs_neg_witness (c : String) (A : Formula) (hcA : Not (occursFormula c A)) :
    absFormula c 0 (neg (substFormula 0 (Term.func c []) A)) = neg A := by
  show neg (absFormula c 0 (substFormula 0 (Term.func c []) A)) = neg A
  rw [absFormula_subst c A 0 0 (Nat.le_refl 0), absFormula_eq_lift c A 1 hcA]
  have hc : absTerm c 0 (Term.func c []) = Term.var 0 := by simp [absTerm]
  rw [hc, substFormula_lift_var A 0]

/-- ⭐ **Partir un contexto finito sin decidir la igualdad.** Si cada `g ∈ Γ` está en `S` o es `H`,
hay un `Γ' ⊆ S` con `Γ ⊆ H :: Γ'`: por inducción sobre `Γ`, eliminando la disyunción que la
hipótesis ya entrega. **Ningún axioma**. (Hasta el 2026‑09‑27 esto se hacía con un `filter` bajo
`open Classical`, que decidía `x = H` con `Classical.propDecidable`: la auditoría de
constructividad lo midió innecesario.) -/
theorem ctx_split {S : Formula → Prop} {H : Formula} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → Or (S g) (g = H)) →
    ∃ Γ' : List Formula, And (∀ g, g ∈ Γ' → S g) (∀ x, x ∈ Γ → x ∈ H :: Γ')
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨Γ', hS, hsub⟩ := ctx_split Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      cases hΓ g (List.Mem.head _) with
      | inl hg =>
        refine ⟨g :: Γ', ?_, ?_⟩
        · intro x hx
          cases hx with
          | head => exact hg
          | tail _ hx => exact hS x hx
        · intro x hx
          cases hx with
          | head => exact List.Mem.tail _ (List.Mem.head _)
          | tail _ hx =>
            cases hsub x hx with
            | head => exact List.Mem.head _
            | tail _ h => exact List.Mem.tail _ (List.Mem.tail _ h)
      | inr hg =>
        refine ⟨Γ', hS, ?_⟩
        intro x hx
        cases hx with
        | head => rw [hg]; exact List.Mem.head _
        | tail _ hx => exact hsub x hx

-- ============================================================
-- §3 · ⭐⭐ EL PASO DE HENKIN
-- ============================================================

/-- ⭐ **El paso de Henkin, en POSITIVO**: una derivación de `⊥` desde `S ∪ {H}` se TRANSFORMA en una
desde `S`. Es la forma que necesita la conservatividad sintáctica (`Skolem0.henkin_conservative₀`):
el enunciado negativo (`IsConsistent₀`) sólo daría la contrapositiva doblemente negada.

⚠️ La frescura se pide sobre `S` y sobre `A`, que es lo que la construcción puede garantizar. Y
⭐ basta con eso porque `DerivesSet₀` entrega un contexto **finito**: `derives0_gen_fresh` sólo
necesita frescura ahí. -/
theorem henkin_step_derives {S : Formula → Prop} (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A))
    (hbot : (fun x => Or (S x) (x = henkinAx c A)) ⊢₀* Formula.bottom) :
    S ⊢₀* Formula.bottom := by
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  -- paso 1 · sacar `H` del contexto, sin decidir ninguna igualdad
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := henkinAx c A) Γ hΓ
  -- paso 2 · `intro_impl` ES el teorema de deducción: es un constructor
  have hnH : Γ' ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  -- paso 3 · las dos mitades clásicas (del cálculo: `dne_rule`, no del metanivel)
  have hex : Γ' ⊢₀ Formula.ex A := neg_impl_left hnH
  have hnq : Γ' ⊢₀ neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  -- paso 4 · frescura en el contexto FINITO
  have hfresh : ∀ g, g ∈ Γ' → Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  -- paso 5 · eigenvariable
  have hall : Γ' ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  -- paso 6 · `∃A` contra `∀¬A`
  exact ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

/-- **Añadir el testigo de Henkin para `A` con una constante fresca preserva la consistencia.** -/
theorem henkin_step_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) :=
  fun hbot => hCons (henkin_step_derives c A hcS hcA hbot)

end FOL.Henkin0

#print axioms FOL.Henkin0.henkin_step_consistent₀
