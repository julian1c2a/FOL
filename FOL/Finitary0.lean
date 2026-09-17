/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Hauptsatz0
-- @axiom_system: classical
-- @importance: high

import FOL.Hauptsatz0

/-!
# `FOL.Finitary0` — 🏁 la CONSISTENCIA de `Derives₀`, **sin `Classical.choice`**

⭐⭐ **El dividendo que justifica el precio del Hauptsatz.** El mismo enunciado que
`FOL.Metamath.Soundness0.derives0_consistent`, con footprint **estrictamente menor**:

| teorema | ruta | footprint |
|---|---|---|
| `derives0_consistent` (ADR‑034) | semántica: `derives0_soundness` + el modelo `Mtrue` | `[propext, Classical.choice, Quot.sound]` |
| ⭐ `derives0_consistent_fin` (aquí) | **sintáctica**: `ndToLK` + `cut_elimination` + `lk0_tval` | **`[propext, Quot.sound]`** |

🔑 Es el mismo patrón que `derives0_em`/`derives0_peirce`, demostrados dos veces —por completitud y
por Kalmár— con footprint estrictamente menor por la vía H. *Mismo enunciado, menos supuestos.*

## ⚠️ De dónde venía el `Classical.choice`, MEDIDO

No del modelo: `derives0_consistent` **ya** usa un modelo de un punto (`Mtrue : Model Unit`,
`FOL/Soundness0.lean`). Venía de `derives0_soundness`, cuya prueba usa **cuatro
`Classical.byContradiction`** (`FOL/Soundness0.lean:172‑182) — porque `eval` devuelve `Prop` y la
semántica de Tarski es clásica. *El modelo era finitario; la solidez no.*

## ⭐ La salida: evaluar a `Bool`, no a `Prop`

`tval a : Formula → Bool` es el modelo de un punto **calculado**: `⊥ ↦ false`, las igualdades
`↦ true`, los átomos `↦ a`, y los cuantificadores **desaparecen** (dominio de un elemento ⇒
`tval (∀f) = tval (∃f) = tval f`, y `tval` no mira los términos, luego ignora `lift` y `subst`).

⭐ Y **por eso no hace falta el tercio excluido**: el caso `implR` —«o vale `A ⇒ B`, o vale algo de
`Δ`»— se resuelve con `cases h : tval a A`, que es análisis de casos sobre un `Bool`. La misma
disyunción, sobre `Prop`, exige `em`.

## ⭐ Y los cinco axiomas de la igualdad valen `true` GRATIS

`tval_eqInstance` **no depende de ningún axioma**: los cinco (`eqReflAx`, `eqSymmAx`, `eqTransAx`,
`eqFuncAx`, `eqAtomAx`) son `eq`‑ o `impl`‑shaped, y con las igualdades a `true` salen por `rfl`.
⚠️ Salvo `eqAtomAx`, que da `!a || a` y necesita `cases a` — no es `rfl` con `a` variable.
⇒ la regla `eqAx` de `LK₀` (el theory‑cut, ADR‑049) **no cuesta nada aquí**.

## ⭐⭐ Dónde paga el Hauptsatz, exactamente

`LK₀` ya era cut‑free, así que `lk0_tval` **no necesita** el Hauptsatz. Lo que sí lo necesita es el
puente desde la deducción natural: `ndToLK` produce `LKc` —**con** corte—, y `cut_elimination` es lo
único que lleva de ahí a `LK₀`. La cadena entera:

    Derives₀ [] ⊥  →  Derives₂ [] ⊥  →  LKc [] [⊥]  →  LK₀ [] [⊥]  →  False
                    (derives0_iff_derives2)  (ndToLK)  (cut_elimination)  (lk0_tval)

## 📏 Footprint

`tval_eqInstance` **sin ningún axioma**; el resto, `[propext, Quot.sound]`.
**Ni un `Classical.choice`.**
-/

namespace FOL.Finitary0

open FOL.Herbrand0
open FOL.Sequent0
open FOL.Hauptsatz0

def tval (a : Bool) : Formula → Bool
  | .bottom => false
  | .atom _ _ => a
  | .eq _ _ => true
  | .impl f g => (!tval a f) || tval a g
  | .and f g => tval a f && tval a g
  | .or f g => tval a f || tval a g
  | .forall f => tval a f
  | .ex f => tval a f

-- ⚠️ `And`/`Or` explícitos: `∧`/`∨` se parsean como `Formula.and`/`Formula.or` (trampa §12).
def allTrue (a : Bool) (Γ : List Formula) : Prop := ∀ x, x ∈ Γ → tval a x = true
def someTrue (a : Bool) (Δ : List Formula) : Prop := ∃ x, And (x ∈ Δ) (tval a x = true)

-- ── el valor no ve los TÉRMINOS, luego ignora lift y subst ───────────────────
theorem tval_lift (a : Bool) : ∀ (f : Formula) (k : Nat), tval a (liftFormula k f) = tval a f := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro _; rfl
  | eq t u => intro _; rfl
  | impl x y ihx ihy => intro k; simp only [liftFormula, tval, ihx, ihy]
  | and x y ihx ihy => intro k; simp only [liftFormula, tval, ihx, ihy]
  | or x y ihx ihy => intro k; simp only [liftFormula, tval, ihx, ihy]
  | «forall» x ih => intro k; simp only [liftFormula, tval, ih]
  | ex x ih => intro k; simp only [liftFormula, tval, ih]

theorem tval_subst (a : Bool) :
    ∀ (f : Formula) (k : Nat) (t : Term), tval a (substFormula k t f) = tval a f := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro _ _; rfl
  | eq t u => intro _ _; rfl
  | impl x y ihx ihy => intro k t; simp only [substFormula, tval, ihx, ihy]
  | and x y ihx ihy => intro k t; simp only [substFormula, tval, ihx, ihy]
  | or x y ihx ihy => intro k t; simp only [substFormula, tval, ihx, ihy]
  | «forall» x ih => intro k t; simp only [substFormula, tval, ih]
  | ex x ih => intro k t; simp only [substFormula, tval, ih]

-- ⭐ TODO axioma de la igualdad vale `true`: los cinco son `eq`- o `impl`-shaped.
theorem tval_eqInstance (a : Bool) {g : Formula} (hg : EqInstance g) : tval a g = true := by
  cases hg with
  | refl t => rfl
  | symm t u => rfl
  | trans t u w => rfl
  | func f pre post x y => rfl
  | atom p pre post x y => cases a <;> rfl

-- ── aritmética de `allTrue` / `someTrue` ────────────────────────────────────
theorem allTrue_cons {a : Bool} {b : Formula} {Γ : List Formula}
    (hb : tval a b = true) (h : allTrue a Γ) : allTrue a (b :: Γ) := by
  intro x hx
  cases hx with
  | head => exact hb
  | tail _ hm => exact h x hm

theorem allTrue_tl {a : Bool} {b : Formula} {Γ : List Formula}
    (h : allTrue a (b :: Γ)) : allTrue a Γ := fun x hx => h x (List.Mem.tail _ hx)

theorem allTrue_hd {a : Bool} {b : Formula} {Γ : List Formula}
    (h : allTrue a (b :: Γ)) : tval a b = true := h b (List.Mem.head _)

theorem allTrue_sub {a : Bool} {Γ Γ' : List Formula}
    (hs : ∀ x, x ∈ Γ → x ∈ Γ') (h : allTrue a Γ') : allTrue a Γ :=
  fun x hx => h x (hs x hx)

theorem allTrue_lift {a : Bool} {Γ : List Formula} (h : allTrue a Γ) :
    allTrue a (Γ.map (liftFormula 0)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rw [tval_lift]
  exact h y hy

theorem someTrue_sub {a : Bool} {Δ Δ' : List Formula}
    (hs : ∀ x, x ∈ Δ → x ∈ Δ') (h : someTrue a Δ) : someTrue a Δ' :=
  h.elim (fun x hx => ⟨x, hs x hx.1, hx.2⟩)

theorem someTrue_unlift {a : Bool} {Δ : List Formula}
    (h : someTrue a (Δ.map (liftFormula 0))) : someTrue a Δ := by
  obtain ⟨x, hx, hv⟩ := h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact ⟨y, hy, by rwa [tval_lift] at hv⟩

theorem someTrue_nil (a : Bool) (h : someTrue a []) : False :=
  h.elim (fun _ hx => absurd hx.1 (List.not_mem_nil))

-- ── ⭐⭐⭐ SOLIDEZ BOOLEANA de `LK₀` en el modelo de un punto ─────────────────
theorem lk0_tval : ∀ {Γ Δ : List Formula}, LK₀ Γ Δ → ∀ (a : Bool),
    allTrue a Γ → someTrue a Δ := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A h1 h2 => intro a hΓ; exact ⟨A, h2, hΓ A h1⟩
  | botL Γ Δ h1 =>
      intro a hΓ
      have := hΓ Formula.bottom h1
      exact absurd this (by simp [tval])
  | struct Γ Γ' Δ Δ' _ s1 s2 ih =>
      intro a hΓ; exact someTrue_sub s2 (ih a (allTrue_sub s1 hΓ))
  | implR Γ Δ A B _ ih =>
      intro a hΓ
      cases hA : tval a A with
      | false => exact ⟨Formula.impl A B, List.Mem.head _, by simp [tval, hA]⟩
      | true =>
          rcases ih a (allTrue_cons hA hΓ) with ⟨x, hx, hv⟩
          cases hx with
          | head => exact ⟨Formula.impl A B, List.Mem.head _, by simp [tval, hv]⟩
          | tail _ hm => exact ⟨x, List.Mem.tail _ hm, hv⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro a hΓ
      have hAB : tval a (Formula.impl A B) = true := allTrue_hd hΓ
      have hΓ' : allTrue a Γ := allTrue_tl hΓ
      cases hA : tval a A with
      | false =>
          rcases ih1 a hΓ' with ⟨x, hx, hv⟩
          cases hx with
          | head => exact absurd (hA ▸ hv) (by simp)
          | tail _ hm => exact ⟨x, hm, hv⟩
      | true =>
          have hB : tval a B = true := by
            simp only [tval, hA] at hAB; simpa using hAB
          exact ih2 a (allTrue_cons hB hΓ')
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro a hΓ
      rcases ih1 a hΓ with ⟨x, hx, hv⟩
      cases hx with
      | tail _ hm => exact ⟨x, List.Mem.tail _ hm, hv⟩
      | head =>
          rcases ih2 a hΓ with ⟨y, hy, hw⟩
          cases hy with
          | tail _ hm => exact ⟨y, List.Mem.tail _ hm, hw⟩
          | head => exact ⟨Formula.and A B, List.Mem.head _, by simp [tval, hv, hw]⟩
  | andL Γ Δ A B _ ih =>
      intro a hΓ
      have hAB : tval a (Formula.and A B) = true := allTrue_hd hΓ
      simp only [tval, Bool.and_eq_true] at hAB
      exact ih a (allTrue_cons hAB.1 (allTrue_cons hAB.2 (allTrue_tl hΓ)))
  | orR Γ Δ A B _ ih =>
      intro a hΓ
      rcases ih a hΓ with ⟨x, hx, hv⟩
      cases hx with
      | head => exact ⟨Formula.or A B, List.Mem.head _, by simp [tval, hv]⟩
      | tail _ hm =>
          cases hm with
          | head => exact ⟨Formula.or A B, List.Mem.head _, by simp [tval, hv]⟩
          | tail _ hm2 => exact ⟨x, List.Mem.tail _ hm2, hv⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro a hΓ
      have hAB : tval a (Formula.or A B) = true := allTrue_hd hΓ
      simp only [tval, Bool.or_eq_true] at hAB
      have hΓ' : allTrue a Γ := allTrue_tl hΓ
      rcases hAB with hA | hB
      · exact ih1 a (allTrue_cons hA hΓ')
      · exact ih2 a (allTrue_cons hB hΓ')
  | allR Γ Δ A _ ih =>
      intro a hΓ
      rcases ih a (allTrue_lift hΓ) with ⟨x, hx, hv⟩
      cases hx with
      | head => exact ⟨Formula.forall A, List.Mem.head _, hv⟩
      | tail _ hm => exact someTrue_sub (fun y hy => List.Mem.tail _ hy) (someTrue_unlift ⟨x, hm, hv⟩)
  | allL Γ Δ A t _ ih =>
      intro a hΓ
      have hA : tval a (Formula.forall A) = true := allTrue_hd hΓ
      refine ih a (allTrue_cons ?_ (allTrue_tl hΓ))
      rw [tval_subst]; exact hA
  | exR Γ Δ A t _ ih =>
      intro a hΓ
      rcases ih a hΓ with ⟨x, hx, hv⟩
      cases hx with
      | head =>
          refine ⟨Formula.ex A, List.Mem.head _, ?_⟩
          rw [tval_subst] at hv; exact hv
      | tail _ hm => exact ⟨x, List.Mem.tail _ hm, hv⟩
  | exL Γ Δ A _ ih =>
      intro a hΓ
      have hA : tval a (Formula.ex A) = true := allTrue_hd hΓ
      exact someTrue_unlift (ih a (allTrue_cons hA (allTrue_lift (allTrue_tl hΓ))))
  | eqAx Γ Δ g hg _ ih =>
      intro a hΓ
      exact ih a (allTrue_cons (tval_eqInstance a hg) hΓ)

-- ── 🏁 LOS COROLARIOS, y todos SIN `Classical.choice` ───────────────────────
theorem lk0_empty : Not (LK₀ [] []) := fun h => someTrue_nil true (lk0_tval h true (by intro _ hx; exact absurd hx (List.not_mem_nil)))

theorem lk0_no_bot : Not (LK₀ [] [Formula.bottom]) := by
  intro h
  rcases lk0_tval h true (by intro _ hx; exact absurd hx (List.not_mem_nil)) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [tval])
  | tail _ hm => exact absurd hm (List.not_mem_nil)

/-- ⭐⭐⭐ **CONSISTENCIA FINITARIA de `Derives₀`**: el mismo enunciado que
`derives0_consistent`, pero por la vía SINTÁCTICA — y aquí es donde paga el Hauptsatz. -/
theorem derives0_consistent_fin : Not (([] : List Formula) ⊢₀ Formula.bottom) := by
  intro h
  have h2 := FOL.Derives2.derives0_iff_derives2.mp h
  have hc := FOL.NDtoLK0.ndToLK h2
  exact lk0_no_bot (cut_elimination [] [Formula.bottom] hc)

/-- ⭐ Y con la valuación `false`, que `Derives₀` tampoco prueba un átomo. -/
theorem derives0_not_P_fin : Not (([] : List Formula) ⊢₀ Formula.atom "P" []) := by
  intro h
  have h2 := FOL.Derives2.derives0_iff_derives2.mp h
  have hc := FOL.NDtoLK0.ndToLK h2
  rcases lk0_tval (cut_elimination [] [Formula.atom "P" []] hc) false
    (by intro _ hx; exact absurd hx (List.not_mem_nil)) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [tval])
  | tail _ hm => exact absurd hm (List.not_mem_nil)

end FOL.Finitary0

#print axioms FOL.Finitary0.tval_eqInstance
#print axioms FOL.Finitary0.lk0_tval
#print axioms FOL.Finitary0.lk0_empty
#print axioms FOL.Finitary0.lk0_no_bot
#print axioms FOL.Finitary0.derives0_consistent_fin
#print axioms FOL.Finitary0.derives0_not_P_fin
