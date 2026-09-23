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

Pieza (3) del ensamblaje de `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4. Con ella el **ensamblaje
completo** queda demostrado en un solo enunciado:

    henkin_completion : IsConsistent₀ S →
      ∃ T, IsMaximalConsistent₀ T ∧ IsHenkin₀ T ∧ (∀ f, shiftTheory S f → T f)

*Toda teoría consistente se extiende a una **maximal consistente** que además **tiene testigo para
cada existencial**.* Es exactamente la hipótesis que el modelo canónico consume.

## Qué hay aquí

1. **§1** — las cuatro propiedades estructurales de `⊢₀*`. ⭐ `derivesSet0_intro_impl` es
   **el teorema de deducción**, y sobre `Derives₀` **no hay que demostrarlo**: `intro_impl` es un
   **constructor**. La versión de `cuarentena/Completeness.lean` invocaba
   `FOL.Metamath.Deduction.deduction_theorem`.
2. **§2** — Lindenbaum: la cadena `LindenbaumStep`, el límite, y `lindenbaum_lemma`.
3. **§3** — lo mínimo sobre un maximal consistente que el ensamblaje necesita: `max_cons_bot`,
   `max_cons_contains` y `max_cons_impl`. 🏁 El resto de la familia (`and`, `or`, `ex`, `forall`)
   fue con el modelo canónico, como aquí se predijo: está en `FOL.Canonical0` §1 y §5.
4. **§4** — ⭐⭐ `henkin_completion`.

## ⛔ Dónde está, y dónde NO está, la no‑finitud

Aquí. En una línea:

    if IsConsistent₀ (Sₙ ∪ {φₙ}) then … else …

Esa condición es **Π⁰₁** y se decide con `Classical.propDecidable`. **Ahí cabe toda la no‑finitud
del teorema de completitud** — es el WKL del que habla `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.3,
y por eso el entregable de la vía W **no es un footprint limpio** sino un `Classical.choice`
**explicado**: ≡ completitud sobre RCA₀, y WKL₀ es Π⁰₂‑conservativo sobre PRA.

⚠️ Los `Classical.choice` de `FOL.Fresh0` y `FOL.HenkinLimit0` **no eran** éste: eran
`Exists.choose` y `String`. Éste sí.

🔑 **Un `Classical.choice` explicado vale más que un `Classical.choice` escondido.**

## 📏 Footprint

`[propext, Classical.choice, Quot.sound]`, **cero axiomas del proyecto**.
-/

namespace FOL.Lindenbaum0

open FOL.Henkin0
open FOL.Fresh0
open FOL.HenkinLimit0
open FOL.Metamath.Enumeration

-- ⚠️ `open Classical` para el `if IsConsistent₀ …` (que es el punto de §6.3) y para el `filter`
-- de `derivesSet0_intro_impl`. Va DENTRO del namespace a propósito: así los `#print axioms` del
-- final imprimen `Classical.choice` con su nombre completo, que es lo que el control compara.
open Classical

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
un **constructor**. Todo el trabajo es sacar `A` del contexto finito con un `filter`. -/
theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ.filter (fun y => decide (Not (y = A))), ?_, ?_⟩
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  · refine Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD ?_)
    intro x hx
    by_cases heq : x = A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)

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

/-- ⛔ **Aquí está toda la no‑finitud del teorema**: la condición del `if` es **Π⁰₁** y se decide
con `Classical.propDecidable`. Ver la cabecera del módulo. -/
noncomputable def LindenbaumStep (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 =>
    if IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n)) then
      fun x => Or (LindenbaumStep S n x) (x = natToFormula n)
    else LindenbaumStep S n

def LindenbaumLimit (S : Formula → Prop) (f : Formula) : Prop := ∃ n, LindenbaumStep S n f

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (LindenbaumStep S n)
  | 0 => hCons
  | n + 1 => by
      simp only [LindenbaumStep]
      by_cases h : IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n))
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact lindenbaum_step_consistent hCons n

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  simp only [LindenbaumStep]
  by_cases hC : IsConsistent₀ (fun y => Or (LindenbaumStep S n y) (y = natToFormula n))
  · rw [if_pos hC]; exact Or.inl h
  · rw [if_neg hC]; exact h

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

/-- ⭐⭐ **Toda teoría consistente se extiende a una maximal consistente.** -/
theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T) (∀ f, S f → T f) := by
  refine ⟨LindenbaumLimit S, ⟨?_, ?_⟩, fun f hf => ⟨0, hf⟩⟩
  · intro hbot
    obtain ⟨Γ, hΓ, hD⟩ := hbot
    obtain ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
    exact lindenbaum_step_consistent hCons N ⟨Γ, hN, hD⟩
  · intro f hNot hExt
    obtain ⟨n, hn⟩ := natToFormula_surj f
    have hConsN : IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n)) := by
      intro hbot
      refine hExt (derivesSet0_weakening hbot ?_)
      intro x hx
      cases hx with
      | inl hS => exact Or.inl ⟨n, hS⟩
      | inr hE => exact Or.inr (by rw [← hn]; exact hE)
    refine hNot ⟨n + 1, ?_⟩
    simp only [LindenbaumStep]
    rw [if_pos hConsN]
    exact Or.inr hn.symm

-- ============================================================
-- §3 · Lo mínimo sobre un maximal consistente
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) :
    Not (S Formula.bottom) := fun h => hMax.1 (derivesSet0_hyp h)

/-- ⭐ **Un maximal consistente está CERRADO por derivación.** ⚠️ Sin Mathlib no hay `by_contra`:
se usa `Classical.byContradiction` (trampa §13). -/
theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {f : Formula}
    (h : S ⊢₀* f) : S f := by
  refine Classical.byContradiction (fun hNot => ?_)
  have hInc : (fun x => Or (S x) (x = f)) ⊢₀* Formula.bottom :=
    Classical.byContradiction (fun hC => hMax.2 f hNot hC)
  exact hMax.1 (derivesSet0_elim_impl (derivesSet0_intro_impl hInc) h)

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S) {A B : Formula}
    (hI : S (Formula.impl A B)) (hA : S A) : S B :=
  max_cons_contains hMax (derivesSet0_elim_impl (derivesSet0_hyp hI) (derivesSet0_hyp hA))

-- ============================================================
-- §4 · ⭐⭐ EL ENSAMBLAJE
-- ============================================================

/-- Un conjunto tiene la propiedad de Henkin si **contiene testigos para sus existenciales**. -/
def IsHenkin₀ (S : Formula → Prop) : Prop :=
  ∀ f, S (Formula.ex f) → ∃ t : Term, S (substFormula 0 t f)

/-- ⭐⭐⭐ **EL ENSAMBLAJE DE HENKIN, CERRADO.** Toda teoría consistente se extiende a una
**maximal consistente** que además **tiene testigo para cada existencial**.

⭐ El paso de `henLimit` a `IsHenkin₀` es de dos líneas: el axioma de Henkin `(∃A) → A[c]` está en
`T` porque `T ⊇ henLimit S`, y un maximal consistente está **cerrado por modus ponens**
(`max_cons_impl`). *El trabajo estaba en construir `henLimit`, no en usarlo.*

⚠️ La conclusión es sobre `shiftTheory S`, no sobre `S`: la extensión vive en el **sublenguaje**.
Es conservativa —`derivesSet0_shift_inv` (`FOL.Fresh0`)—, así que no se pierde nada; pero el
enunciado tiene que decirlo. -/
theorem henkin_completion {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T)
      (And (IsHenkin₀ T) (∀ f, shiftTheory S f → T f)) := by
  obtain ⟨T, hMax, hSub⟩ := lindenbaum_lemma (henLimit_consistent hCons)
  refine ⟨T, hMax, ?_, fun f hf => hSub f (shiftTheory_sub_henLimit S f hf)⟩
  intro A hEx
  obtain ⟨c, hc⟩ := henLimit_witness S A
  exact ⟨Term.func c [], max_cons_impl hMax (hSub _ hc) hEx⟩

end FOL.Lindenbaum0

#print axioms FOL.Lindenbaum0.derivesSet0_intro_impl
#print axioms FOL.Lindenbaum0.lindenbaum_lemma
#print axioms FOL.Lindenbaum0.max_cons_contains
#print axioms FOL.Lindenbaum0.henkin_completion
