/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Sequent0, FOL.Canonical0
-- @axiom_system: classical
-- @importance: high

import FOL.Sequent0
import FOL.Canonical0

/-!
# `FOL.SequentSound0` — **el molde no prueba de más**: solidez de `LK₀` y `LKc`

La comprobación que ADR‑046 §5 dejó declarada como **no hecha**:

    lkc_sound       : LKc Γ Δ → ∀ M v, (todo Γ vale) → algún elemento de Δ vale
    lk0_sound       : ídem para `LK₀`, por el encaje
    lk0_to_derives0 : LK₀ Γ Δ → Γ ⊢₀ disjOf Δ        -- ⭐ el corolario sintáctico
    lk0_not_empty   : ¬ LK₀ [] []                     -- ⭐ y la consistencia del molde

⚠️ **Por qué importa y no es adorno**: `LK₀` es el cálculo sobre el que se va a enunciar y
demostrar el Hauptsatz. Si fuera **demasiado fuerte**, `CutElim` podría ser cierto y no servir —o
peor, se perseguiría un teorema falso durante las mil líneas del Hauptsatz—. Esto lo cierra
**antes** de pagar esa pieza.

## ⭐ La ruta SEMÁNTICA es mucho más barata que la sintáctica

ADR‑046 §5 estimó `LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)` en ~250 l. con riesgo en `allR`: exigía sacar
una disyunción de dentro de un cuantificador. **Por la semántica ese caso es rutina**, y el
resultado sintáctico cae **como corolario** vía `completeness₀` (ADR‑041) y
`derives0_iff_derives2` (ADR‑045).

🔑 *Cuando las dos direcciones están demostradas, un resultado sintáctico se puede comprar por la
semántica.* Es la primera vez que este repo cobra ese dividendo, y sólo se puede desde ADR‑041.

## ⭐ Una sola inducción para los dos cálculos

Se prueba sobre **`LKc`** —el que **tiene** corte, 14 casos— y `lk0_sound` sale aplicando
`lk0_to_lkc`. Hacerlo al revés habría costado dos inducciones.

⭐⭐ **Y el caso `cut` es semánticamente TRIVIAL**: si algún elemento de `A :: Δ` vale y, suponiendo
`A`, algún elemento de `Δ` vale, entonces algún elemento de `Δ` vale. Tres líneas.

🔑 **Ahí está el contraste que explica todo el frente H3**: el corte es **gratis para la verdad** y
**carísimo para la demostración**. `lk0_herbrand` (ADR‑046) no puede con él —su fórmula de corte
no aparece en la conclusión, así que las hipótesis de la inducción no se heredan—, y eliminarlo es
el Hauptsatz. *La semántica no distingue lo que la sintaxis paga.*

## ⭐ Dónde está el trabajo de verdad: `allR` y `exL`

Son los dos casos que **cambian el entorno**. `allR` necesita, clásicamente, que o bien `∀A` vale
—y ya está— o bien hay un `d` donde falla, y entonces la hipótesis de inducción se aplica en el
entorno `shiftEnv v d`, con el contexto levantado. Las dos piezas son

    contextSatisfies_lift_zero   -- el contexto levantado vale en el entorno desplazado
    eval_liftFormula_zero        -- y lo levantado se lee abajo

⭐ y **las dos acaban de quedar limpias** gracias a la corrección de PeanoRF (ADR‑047): antes
arrastraban `Classical.choice` por un `omega` sobre una meta no aritmética. Sin ese arreglo este
módulo habría heredado ese `Classical.choice` **sin que se distinguiera del legítimo**.

## 📏 Footprint, y por qué es legítimo

`[propext, Classical.choice, Quot.sound]` — y aquí el `Classical.choice` **es matemático**: la
solidez de un cálculo de secuentes **multiconclusión** es clásica de raíz. `implR` decide si `A`
vale, `allR` decide si `∀A` vale: sin tercio excluso no hay teorema. ⚠️ Compárese con
`FOL.Sequent0`, donde `lk0_herbrand` mide **`[propext]`**: *la extracción es constructiva, la
solidez no*. Los dos viven en módulos distintos a propósito.
-/

namespace FOL.SequentSound0

open FOL.Metamath.Semantics
open FOL.Sequent0
open Classical

-- ⭐ Se prueba para `LKc` (14 casos) y `LK₀` sale por el encaje: una sola inducción.
theorem lkc_sound : ∀ {Γ Δ : List Formula}, LKc Γ Δ →
    ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hΓ hΔ => intro D M v hv; exact ⟨A, hΔ, hv A hΓ⟩
  | botL Γ Δ hbot => intro D M v hv; exact absurd (hv _ hbot) (fun hx => hx)
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro D M v hv
      obtain ⟨d, hd, hval⟩ := ih M v (fun g hg => hv g (hsΓ g hg))
      exact ⟨d, hsΔ d hd, hval⟩
  | implR Γ Δ A B _ ih =>
      intro D M v hv
      by_cases hA : evalFormula M v A
      · obtain ⟨d, hd, hval⟩ := ih M v (fun g hg => by
          cases hg with
          | head => exact hA
          | tail _ h' => exact hv g h')
        cases hd with
        | head => exact ⟨Formula.impl A B, List.Mem.head _, fun _ => hval⟩
        | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hval⟩
      · exact ⟨Formula.impl A B, List.Mem.head _, fun hx => absurd hx hA⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro D M v hv
      have hAB : evalFormula M v A → evalFormula M v B := hv _ (List.Mem.head _)
      have hvt : ∀ g, g ∈ Γ → evalFormula M v g := fun g hg => hv g (List.Mem.tail _ hg)
      obtain ⟨d, hd, hval⟩ := ih1 M v hvt
      cases hd with
      | head =>
          exact ih2 M v (fun g hg => by
            cases hg with
            | head => exact hAB hval
            | tail _ h' => exact hvt g h')
      | tail _ hd' => exact ⟨d, hd', hval⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro D M v hv
      obtain ⟨d1, hd1, hval1⟩ := ih1 M v hv
      cases hd1 with
      | tail _ hd1' => exact ⟨d1, List.Mem.tail _ hd1', hval1⟩
      | head =>
          obtain ⟨d2, hd2, hval2⟩ := ih2 M v hv
          cases hd2 with
          | tail _ hd2' => exact ⟨d2, List.Mem.tail _ hd2', hval2⟩
          | head => exact ⟨Formula.and A B, List.Mem.head _, And.intro hval1 hval2⟩
  | andL Γ Δ A B _ ih =>
      intro D M v hv
      have hAB : And (evalFormula M v A) (evalFormula M v B) := hv _ (List.Mem.head _)
      exact ih M v (fun g hg => by
        cases hg with
        | head => exact hAB.1
        | tail _ h' =>
            cases h' with
            | head => exact hAB.2
            | tail _ h'' => exact hv g (List.Mem.tail _ h''))
  | orR Γ Δ A B _ ih =>
      intro D M v hv
      obtain ⟨d, hd, hval⟩ := ih M v hv
      cases hd with
      | head => exact ⟨Formula.or A B, List.Mem.head _, Or.inl hval⟩
      | tail _ hd' =>
          cases hd' with
          | head => exact ⟨Formula.or A B, List.Mem.head _, Or.inr hval⟩
          | tail _ hd'' => exact ⟨d, List.Mem.tail _ hd'', hval⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro D M v hv
      have hAB : Or (evalFormula M v A) (evalFormula M v B) := hv _ (List.Mem.head _)
      have hvt : ∀ g, g ∈ Γ → evalFormula M v g := fun g hg => hv g (List.Mem.tail _ hg)
      cases hAB with
      | inl hA =>
          exact ih1 M v (fun g hg => by
            cases hg with
            | head => exact hA
            | tail _ h' => exact hvt g h')
      | inr hB =>
          exact ih2 M v (fun g hg => by
            cases hg with
            | head => exact hB
            | tail _ h' => exact hvt g h')
  -- ⭐ el caso caro: la eigenvariable a la derecha
  | allR Γ Δ A _ ih =>
      intro D M v hv
      by_cases hall : ∀ d : D, evalFormula M (shiftEnv v d) A
      · exact ⟨Formula.forall A, List.Mem.head _, hall⟩
      · obtain ⟨d0, hd0⟩ : ∃ d : D, Not (evalFormula M (shiftEnv v d) A) :=
          Classical.byContradiction (fun hc =>
            hall (fun d => Classical.byContradiction (fun hx => hc ⟨d, hx⟩)))
        have hlift := (contextSatisfies_lift_zero M v d0 (Γ := Γ)).mpr hv
        obtain ⟨e, he, hval⟩ := ih M (shiftEnv v d0) hlift
        cases he with
        | head => exact absurd hval hd0
        | tail _ he' =>
            obtain ⟨e0, he0, heq⟩ := List.mem_map.mp he'
            refine ⟨e0, List.Mem.tail _ he0, ?_⟩
            rw [← heq] at hval
            exact (eval_liftFormula_zero M v d0 e0).mp hval
  | allL Γ Δ A t _ ih =>
      intro D M v hv
      have hall : ∀ d : D, evalFormula M (shiftEnv v d) A := hv _ (List.Mem.head _)
      have hinst : evalFormula M v (substFormula 0 t A) :=
        (eval_substFormula_zero M v t A).mpr (hall (evalTerm M v t))
      exact ih M v (fun g hg => by
        cases hg with
        | head => exact hinst
        | tail _ hg' => exact hv g (List.Mem.tail _ hg'))
  | exR Γ Δ A t _ ih =>
      intro D M v hv
      obtain ⟨d, hd, hval⟩ := ih M v hv
      cases hd with
      | head =>
          exact ⟨Formula.ex A, List.Mem.head _,
            ⟨evalTerm M v t, (eval_substFormula_zero M v t A).mp hval⟩⟩
      | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hval⟩
  | exL Γ Δ A _ ih =>
      intro D M v hv
      obtain ⟨d0, hd0⟩ : ∃ d : D, evalFormula M (shiftEnv v d) A := hv _ (List.Mem.head _)
      have hctx : ∀ g, g ∈ A :: Γ.map (liftFormula 0) → evalFormula M (shiftEnv v d0) g := by
        intro g hg
        cases hg with
        | head => exact hd0
        | tail _ hg' =>
            exact (contextSatisfies_lift_zero M v d0 (Γ := Γ)).mpr
              (fun x hx => hv x (List.Mem.tail _ hx)) g hg'
      obtain ⟨e, he, hval⟩ := ih M (shiftEnv v d0) hctx
      obtain ⟨e0, he0, heq⟩ := List.mem_map.mp he
      refine ⟨e0, he0, ?_⟩
      rw [← heq] at hval
      exact (eval_liftFormula_zero M v d0 e0).mp hval
  -- ⭐ el CORTE: semánticamente trivial — y ahí está el contraste con la sintaxis
  | cut Γ Δ A _ _ ih1 ih2 =>
      intro D M v hv
      obtain ⟨d, hd, hval⟩ := ih1 M v hv
      cases hd with
      | head =>
          exact ih2 M v (fun g hg => by
            cases hg with
            | head => exact hval
            | tail _ h' => exact hv g h')
      | tail _ hd' => exact ⟨d, hd', hval⟩

theorem lk0_sound {Γ Δ : List Formula} (h : LK₀ Γ Δ) :
    ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d) :=
  lkc_sound (lk0_to_lkc h)

-- ── de «algún elemento de Δ» a «la disyunción» ──────────────────────────────
theorem eval_disjOf_of_mem {D : Type} (M : Model D) (v : Nat → D) :
    ∀ (Δ : List Formula) (d : Formula), d ∈ Δ → evalFormula M v d →
      evalFormula M v (FOL.Herbrand0.disjOf Δ)
  | [], _, hd, _ => absurd hd List.not_mem_nil
  | e :: Δ, d, hd, hval => by
      show Or (evalFormula M v e) (evalFormula M v (FOL.Herbrand0.disjOf Δ))
      cases hd with
      | head => exact Or.inl hval
      | tail _ hd' => exact Or.inr (eval_disjOf_of_mem M v Δ d hd' hval)

-- ⭐⭐ EL COROLARIO que cierra la comprobación: `LK₀` no prueba de más
theorem lk0_to_derives0 {Γ Δ : List Formula} (h : LK₀ Γ Δ) :
    Γ ⊢₀ FOL.Herbrand0.disjOf Δ :=
  FOL.Canonical0.completeness₀ (fun D M v hctx => by
    obtain ⟨d, hd, hval⟩ := lk0_sound h M v hctx
    exact eval_disjOf_of_mem M v Δ d hd hval)

theorem lk0_to_derives2 {Γ Δ : List Formula} (h : LK₀ Γ Δ) :
    Γ ⊢₂ FOL.Herbrand0.disjOf Δ :=
  FOL.Derives2.derives0_iff_derives2.mp (lk0_to_derives0 h)

/-- ⭐ Y la consistencia del molde: `LK₀` NO prueba el secuente vacío. -/
theorem lk0_not_empty : Not (LK₀ [] []) := by
  intro h
  have hbot : ([] : List Formula) ⊢₀ Formula.bottom := lk0_to_derives0 h
  exact FOL.Metamath.Soundness0.derives0_consistent hbot

end FOL.SequentSound0

#print axioms FOL.SequentSound0.lkc_sound
#print axioms FOL.SequentSound0.lk0_sound
#print axioms FOL.SequentSound0.lk0_to_derives0
#print axioms FOL.SequentSound0.lk0_to_derives2
#print axioms FOL.SequentSound0.lk0_not_empty
