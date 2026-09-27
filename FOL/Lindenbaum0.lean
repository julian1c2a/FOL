/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.HenkinLimit0
-- @axiom_system: classical
-- @importance: high

import FOL.HenkinLimit0

/-!
# `FOL.Lindenbaum0` — **Lindenbaum sobre `Derives₀`**, y el ensamblaje de Henkin cerrado

Pieza (3) del ensamblaje de
`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4. Con ella el **ensamblaje
completo** queda demostrado en un solo enunciado:

    henkin_completion₀ : IsConsistent₀ S →
      ∃ T, IsMaximalConsistent₀ T ∧ IsHenkin T ∧ (∀ f, shiftTheory S f → T f)

*Toda teoría consistente se extiende a una **maximal consistente** que además **tiene testigo para
cada existencial**.* Es exactamente la hipótesis que el modelo canónico consume.

## Qué hay aquí

1. **§1** — las cuatro propiedades estructurales de `⊢₀*`. ⭐ `derivesSet0_intro_impl` es
   **el teorema de deducción**, y sobre `Derives₀` **no hay que demostrarlo**: `intro_impl` es un
   **constructor**. La versión de `cuarentena/Completeness.lean` (borrado el 2026‑09‑23)
   invocaba `FOL.Metamath.Deduction.deduction_theorem`.
2. **§2** — Lindenbaum: la etapa `LindenbaumStep` (⭐ impredicativa desde el 2026‑09‑27: no decide
   nada), el límite, su consistencia, su maximalidad y su **cierre por derivación**
   (`lindenbaum_limit_consistent`, `lindenbaum_limit_max`, `lindenbaum_limit_closed`), y
   `lindenbaum_lemma₀`.
3. **§3** — lo mínimo sobre un maximal consistente **ARBITRARIO**: `max_cons_bot`,
   `max_cons_contains` y `max_cons_impl`. ⚠️ Desde el 2026‑09‑27 el ensamblaje de §4 ya no los usa
   (usa `lindenbaum_limit_closed`, sobre el límite CONCRETO); los consume el lema de la verdad de
   `FOL.Canonical0`. 🏁 El resto de la familia (`and`, `or`, `ex`, `forall`) fue con el modelo
   canónico, como aquí se predijo: está en `FOL.Canonical0` §1 y §5.
4. **§4** — ⭐⭐ `henkin_completion₀`, sin `Classical.choice` desde el 2026‑09‑27.

## ⛔ Dónde está, y dónde NO está, lo clásico de la completitud

⚠️⚠️ **Hasta el 2026‑09‑27 esta sección sostenía una tesis que la medición refutó.** Decía:

> Aquí. En una línea: `if IsConsistent₀ (Sₙ ∪ {φₙ}) then … else …`. Esa condición es **Π⁰₁** y
> se decide con `Classical.propDecidable`. **Ahí cabe toda la no‑finitud del teorema de
> completitud** — es el WKL del que habla `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`
> §6.3, y por eso el entregable de la vía W **no es un footprint limpio** sino un
> `Classical.choice` **explicado**.

(Es la tesis de ADR‑040 §2 y ADR‑041 §4, en `../ROBINSON_PlusPlus/DECISIONS.md`.)
⛔ **En Lean es FALSA** (auditoría de
constructividad, 2026‑09‑27, medido). `Prop` es impredicativo: la etapa se define con la condición
DENTRO, como conjunción, y no hay que decidirla:

    LindenbaumStep S (n+1) x := LindenbaumStep S n x ∨ (x = φₙ ∧ IsConsistent₀ (Sₙ ∪ {φₙ}))

Todo lo demás sale sin tercio excluso: la consistencia de cada etapa (la meta es una NEGACIÓN, y
basta `¬¬(C ∨ ¬C)`, `not_not_em`), la maximalidad del límite y su cierre por derivación
(`lindenbaum_limit_closed`). ⇒ `lindenbaum_lemma₀` y `henkin_completion₀`, con los mismos
enunciados, miden `[propext, Quot.sound]`. El `if` era cosa de la PRESENTACIÓN, no del teorema.

⭐ **Dónde SÍ está lo clásico de `completeness₀`** (la frontera medida de la auditoría):

* en el **lema de la verdad sobre un maximal ARBITRARIO**, que tiene que casar la pertenencia a
  `S` con la semántica de Tarski en `Prop`: `max_cons_contains` (§3) y, en `FOL.Canonical0`,
  `max_cons_impl_iff`, `max_cons_or`, `max_cons_complete` y `max_cons_forall`. Con `S` arbitrario,
  los enunciados de las cinco **implican `¬¬P → P`** (compilado, en
  `auditoria/constructividad-2026-09-27/experimentos/`: las cuatro primeras en
  `exp-esencial/E3_MaxCons.lean`; `max_cons_forall`, con un testigo Henkin, en
  `exp-esceptico/Esc2.lean`, según el informe del escéptico); con `[DecidablePred S]` las cinco
  salen en `[propext]`;
* en el `byContradiction` final de `Canonical0.completeness₀` (forma de Markov), esencial sólo
  como hipótesis.

🔑 **El WKL sigue nombrando la FUERZA lógica de la completitud, no un sitio del código.** Sobre
RCA₀, completitud ⇔ WKL₀ (Simpson IV.3.3), y WKL₀ es Π⁰₂‑conservativo sobre PRA; pero ahí la
teoría maximal tiene que EXISTIR como conjunto definible, y en Lean existe gratis como predicado
impredicativo. ⇒ Ningún `Classical.choice` de este árbol «es el WKL».

⚠️ Los demás `Classical.choice` que llegaban aquí, desde abajo o de este mismo módulo
(`Exists.choose` en `HenkinLimit0.bnd`, el tercio excluso de `Fresh0.cst_bound_sym`,
`Rename.invOf`, el `filter` bajo `open Classical` de `henkin_step_consistent₀` y de
`derivesSet0_intro_impl`, la `ReflBEq String` de `Fresh0.cst_zero_ne`/`cst_ne_shift`, la
sobreyectividad de `FOL.Enumeration`) **tampoco eran necesarios**, y se retiraron el mismo día.

🔑 *Un `Classical.choice` explicado vale más que uno escondido; uno retirado, más que uno explicado.*

## 📏 Footprint

Medido el 2026‑09‑27 sobre el entorno compilado (`auditoria/constructividad-2026-09-27/despues/`):

* **ningún axioma**: `derivesSet0_hyp`, `derivesSet0_weakening`, `derivesSet0_intro_impl`,
  `not_not_em`, `max_cons_bot` (y las definiciones `IsMaximalConsistent₀`, `IsHenkin`);
* `[propext]`: `derivesSet0_elim_impl`;
* `[propext, Quot.sound]`: `LindenbaumStep`, `LindenbaumLimit`, los `lindenbaum_step_*` y
  `lindenbaum_limit_*`, ⭐ `lindenbaum_lemma₀` y ⭐⭐ `henkin_completion₀`;
* `[propext, Classical.choice, Quot.sound]`: **sólo** `max_cons_contains` —su
  `Classical.byContradiction` es la única entrada de `Classical.choice` del módulo, y es esencial
  (ver arriba)— y `max_cons_impl`, que lo hereda.

**Cero axiomas del proyecto**, y ninguna declaración `noncomputable` (hasta el 2026‑09‑27 lo era
`LindenbaumStep`).
-/

namespace FOL.Lindenbaum0

open FOL.Henkin0
open FOL.Fresh0
open FOL.HenkinLimit0
open FOL.Metamath.Enumeration

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- §1 · Las cuatro propiedades estructurales de `⊢₀*`
-- ============================================================

theorem derivesSet0_hyp {S : Formula → Prop} {f : Formula} (h : S f) : S ⊢₀* f :=
  ⟨[f],
   fun g hg => by
     cases hg with
     | head => exact h
     | tail _ ht => exact absurd ht List.not_mem_nil,
   Derives₀.hyp _ _ (List.Mem.head _)⟩

theorem derivesSet0_weakening {S S' : Formula → Prop} {f : Formula}
    (h : S ⊢₀* f) (hSub : ∀ x, S x → S' x) : S' ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  exact ⟨Γ, fun g hg => hSub g (hΓ g hg), hD⟩

/-- ⭐ **El teorema de deducción**, y sobre `Derives₀` **no hay que demostrarlo**: `intro_impl` es
un **constructor**. Todo el trabajo es sacar `A` del contexto finito, y eso lo hace
`Henkin0.ctx_split` sin decidir ninguna igualdad: **ningún axioma**. (Hasta el 2026‑09‑27 se hacía
con un `filter` bajo `open Classical`, que metía `Classical.choice` sin necesidad.) -/
theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := A) Γ hΓ
  exact ⟨Γ', hΓ', Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)⟩

theorem derivesSet0_elim_impl {S : Formula → Prop} {A B : Formula}
    (hI : S ⊢₀* Formula.impl A B) (hA : S ⊢₀* A) : S ⊢₀* B := by
  obtain ⟨Γ1, h1, d1⟩ := hI
  obtain ⟨Γ2, h2, d2⟩ := hA
  refine ⟨Γ1 ++ Γ2, fun g hg => (List.mem_append.mp hg).elim (h1 g) (h2 g), ?_⟩
  exact Derives₀.elim_impl _ A B
    (Derives₀.weakening _ _ _ d1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
    (Derives₀.weakening _ _ _ d2 (fun x hx => List.mem_append.mpr (Or.inr hx)))

-- ============================================================
-- §2 · Lindenbaum
-- ============================================================

/-- Consistente, y **no ampliable**: añadir cualquier fórmula que no esté ya lo rompe. -/
def IsMaximalConsistent₀ (S : Formula → Prop) : Prop :=
  And (IsConsistent₀ S) (∀ f, Not (S f) → Not (IsConsistent₀ (fun x => Or (S x) (x = f))))

/-- ⭐⭐ **La etapa de Lindenbaum, IMPREDICATIVA**: `φₙ` entra en la etapa `n+1` si **es consistente**
añadirla, y esa condición va DENTRO del predicado, como conjunción — no se DECIDE. `Prop` es
impredicativo, así que la etapa es un predicado legítimo sin saber si la condición se cumple.
(Hasta el 2026‑09‑27 era un `if IsConsistent₀ … then … else …` decidido con
`Classical.propDecidable`: la «no‑finitud» que la cabecera atribuía aquí era de la PRESENTACIÓN.) -/
def LindenbaumStep (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 => fun x => Or (LindenbaumStep S n x)
      (And (x = natToFormula n)
        (IsConsistent₀ (fun y => Or (LindenbaumStep S n y) (y = natToFormula n))))

def LindenbaumLimit (S : Formula → Prop) (f : Formula) : Prop := ∃ n, LindenbaumStep S n f

/-- El tercio excluso, DOBLEMENTE NEGADO, es intuicionista. -/
theorem not_not_em (C : Prop) : Not (Not (Or C (Not C))) :=
  fun h => h (Or.inr (fun c => h (Or.inl c)))

/-- ⭐ Cada etapa es consistente. La meta es una NEGACIÓN (`IsConsistent₀ X` es `X ⊬ ⊥`), así que
basta el tercio excluso doblemente negado para distinguir si `φₙ` entró: **sin tercio excluso**.
Mide `[propext, Quot.sound]`, lo mismo que la propia etapa (que los trae de `natToFormula`); la
prueba no añade ningún axioma. -/
theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (LindenbaumStep S n)
  | 0 => hCons
  | n + 1 => by
      intro hbot
      apply not_not_em (IsConsistent₀ (fun y => Or (LindenbaumStep S n y) (y = natToFormula n)))
      intro hem
      cases hem with
      | inl hC =>
        exact hC (derivesSet0_weakening hbot (fun x hx => hx.elim Or.inl (fun h => Or.inr h.1)))
      | inr hNC =>
        exact lindenbaum_step_consistent hCons n
          (derivesSet0_weakening hbot (fun x hx => hx.elim id (fun h => absurd h.2 hNC)))

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := Or.inl h

theorem lindenbaum_step_mono {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : LindenbaumStep S n x) : LindenbaumStep S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact lindenbaum_step_subset _ ih

/-- ⭐ Otra vez: un contexto **finito** dentro del límite vive ya en una etapa. -/
theorem lindenbaum_limit_bound {S : Formula → Prop} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → LindenbaumLimit S g) → ∃ N, ∀ g, g ∈ Γ → LindenbaumStep S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨ng, hng⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := lindenbaum_limit_bound Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max ng N, fun x hx => ?_⟩
      cases hx with
      | head => exact lindenbaum_step_mono (Nat.le_max_left _ _) hng
      | tail _ hx' => exact lindenbaum_step_mono (Nat.le_max_right _ _) (hN x hx')

theorem lindenbaum_limit_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (LindenbaumLimit S) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
  exact lindenbaum_step_consistent hCons N ⟨Γ, hN, hD⟩

/-- El límite es MAXIMAL: si `φ = φₙ` no rompe la consistencia del límite, tampoco la de la etapa
`n`, y la conjunción de la etapa `n+1` la mete. -/
theorem lindenbaum_limit_max {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsMaximalConsistent₀ (LindenbaumLimit S) := by
  refine ⟨lindenbaum_limit_consistent hCons, ?_⟩
  intro f hNot hExt
  obtain ⟨n, hn⟩ := natToFormula_surj f
  have hConsN : IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n)) := by
    intro hbot
    refine hExt (derivesSet0_weakening hbot ?_)
    intro x hx
    cases hx with
    | inl hS => exact Or.inl ⟨n, hS⟩
    | inr hE => exact Or.inr (hE.trans hn)
  exact hNot ⟨n + 1, Or.inr ⟨hn.symm, hConsN⟩⟩

/-- ⭐⭐ **El límite de Lindenbaum está CERRADO por derivación**, sin tercio excluso. Para un maximal
ARBITRARIO eso es `max_cons_contains`, que sí lo necesita (su enunciado implica `¬¬P → P`); para
ESTE límite, no: si `f = φₙ` se deriva, añadirla a la etapa `n` es consistente, y entra. -/
theorem lindenbaum_limit_closed {S : Formula → Prop} (hCons : IsConsistent₀ S) {f : Formula}
    (hD : LindenbaumLimit S ⊢₀* f) : LindenbaumLimit S f := by
  obtain ⟨n, hn⟩ := natToFormula_surj f
  have hConsN : IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n)) := by
    intro hbot
    have hI : LindenbaumStep S n ⊢₀* Formula.impl (natToFormula n) Formula.bottom :=
      derivesSet0_intro_impl hbot
    have hI' : LindenbaumLimit S ⊢₀* Formula.impl (natToFormula n) Formula.bottom :=
      derivesSet0_weakening hI (fun x hx => ⟨n, hx⟩)
    rw [hn] at hI'
    exact lindenbaum_limit_consistent hCons (derivesSet0_elim_impl hI' hD)
  exact ⟨n + 1, Or.inr ⟨hn.symm, hConsN⟩⟩

/-- ⭐⭐ **Toda teoría consistente se extiende a una maximal consistente.** Sin `Classical.choice`
desde el 2026‑09‑27 (etapa impredicativa). -/
theorem lindenbaum_lemma₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T) (∀ f, S f → T f) :=
  ⟨LindenbaumLimit S, lindenbaum_limit_max hCons, fun _ hf => ⟨0, hf⟩⟩

-- ============================================================
-- §3 · Lo mínimo sobre un maximal consistente
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) :
    Not (S Formula.bottom) := fun h => hMax.1 (derivesSet0_hyp h)

/-- ⭐ **Un maximal consistente está CERRADO por derivación.** ⚠️ Sin Mathlib no hay `by_contra`:
se usa `Classical.byContradiction`.

⛔ Y aquí el tercio excluso es **ESENCIAL**: con `S` arbitrario, este enunciado implica `¬¬P → P`
(auditoría de constructividad, 2026‑09‑27, compilado). Es la única entrada de `Classical.choice`
del módulo. Para el límite CONCRETO de §2 no hace falta: `lindenbaum_limit_closed`. -/
theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : S f :=
  Classical.byContradiction (fun hNot =>
    hMax.2 f hNot (fun hInc => hMax.1 (derivesSet0_elim_impl (derivesSet0_intro_impl hInc) h)))

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {A B : Formula}
    (hI : S (Formula.impl A B)) (hA : S A) : S B :=
  max_cons_contains hMax (derivesSet0_elim_impl (derivesSet0_hyp hI) (derivesSet0_hyp hA))

-- ============================================================
-- §4 · ⭐⭐ EL ENSAMBLAJE
-- ============================================================

/-- Un conjunto tiene la propiedad de Henkin si **contiene testigos para sus existenciales**. -/
def IsHenkin (S : Formula → Prop) : Prop :=
  ∀ f, S (Formula.ex f) → ∃ t : Term, S (substFormula 0 t f)

/-- ⭐⭐⭐ **EL ENSAMBLAJE DE HENKIN, CERRADO.** Toda teoría consistente se extiende a una
**maximal consistente** que además **tiene testigo para cada existencial**.

⭐ El paso de `henLimit` a `IsHenkin` es de dos líneas: el axioma de Henkin `(∃A) → A[c]` está en
`T := LindenbaumLimit (henLimit S)` porque `T ⊇ henLimit S`, y ese límite está **cerrado por
derivación** sin tercio excluso (`lindenbaum_limit_closed`). *El trabajo estaba en construir
`henLimit`, no en usarlo.* (Hasta el 2026‑09‑27 se cerraba con `max_cons_impl` sobre el `T` que
devolvía `lindenbaum_lemma₀`; ése pasa por `max_cons_contains`, clásico. Hoy el enunciado mide
`[propext, Quot.sound]`.)

⚠️ La conclusión es sobre `shiftTheory S`, no sobre `S`: la extensión vive en el **sublenguaje**.
Es conservativa —`derivesSet0_shift_inv` (`FOL.Fresh0`)—, así que no se pierde nada; pero el
enunciado tiene que decirlo. -/
theorem henkin_completion₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T)
      (And (IsHenkin T) (∀ f, shiftTheory S f → T f)) := by
  have hH := henLimit_consistent₀ hCons
  refine ⟨LindenbaumLimit (henLimit S), lindenbaum_limit_max hH, ?_,
    fun f hf => ⟨0, shiftTheory_sub_henLimit S f hf⟩⟩
  intro A hEx
  obtain ⟨c, hc⟩ := henLimit_witness S A
  -- ⭐ el límite CONCRETO está cerrado por modus ponens sin tercio excluso (`lindenbaum_limit_closed`);
  -- `max_cons_impl`, sobre un maximal arbitrario, pasaría por `max_cons_contains` (clásico).
  exact ⟨Term.func c [], lindenbaum_limit_closed hH
    (derivesSet0_elim_impl (derivesSet0_hyp (S := LindenbaumLimit (henLimit S)) (f := henkinAx c A) ⟨0, hc⟩)
      (derivesSet0_hyp hEx))⟩

end FOL.Lindenbaum0

#print axioms FOL.Lindenbaum0.derivesSet0_intro_impl
#print axioms FOL.Lindenbaum0.lindenbaum_lemma₀
#print axioms FOL.Lindenbaum0.max_cons_contains
#print axioms FOL.Lindenbaum0.henkin_completion₀
