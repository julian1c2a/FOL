/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.HerbrandBlock0, FOL.Hauptsatz0
-- @axiom_system: classical
-- @importance: high

import FOL.HerbrandBlock0
import FOL.Hauptsatz0

/-!
# `FOL.BlockExtraction0` — 🏁 la mitad ⟹ de HERBRAND DE BLOQUE, pagada

    herbrand_extraction_block : HerbrandExtractionBlock
    herbrand_block : ([] ⊢₀ exBlock n φ) ↔ ∃ tss E, HerbrandCertBlock n φ tss E

📏 `[propext, Quot.sound]` en todo el módulo: **ni un `Classical.choice`** — como toda la vía H.

## ⭐⭐ La medición que cambió el coste: **`instB` YA ERA la función de resto parcial**

ADR‑055 dejó esta mitad enunciada como `Prop` y midió la obstrucción así: *«hay que llevar además
la TUPLA PARCIAL acumulada ⇒ es un rediseño del enunciado, no una envoltura: ~350–450 l., riesgo
alto»*. ✅ **La cifra ACERTÓ** (≈400 l. medidas, dentro del rango). Lo que falló fue el QUÉ de la
pieza cara: no hubo que definir nada.

El caso que parecía basura de `instB` **no lo es**:

    instB (n+1) [] φ = exBlock (n+1) φ        -- el bloque que queda PENDIENTE
    instB 2 [t] φ    = exBlock 1 (φ[1 := t])  -- resto tras consumir UNA componente

⇒ `instB n us φ` con `us` **más corta que `n`** ya es el resto parcial, y la tupla parcial **es**
`us`. No hubo que definir ninguna función nueva: el invariante del consecuente es

    BlockInv n φ d := QuantFree d  ∨  ∃ us, us.length ≤ n ∧ d = instB n us φ

🔑 *Antes de construir el dato que falta, mirar si una función que ya existe lo devuelve en su caso
degenerado.* Van ocho de «antes de construir, buscar».

## ⭐ La pieza de riesgo, y era una sola

`instB_snoc`: alargar la tupla parcial por la derecha es **exactamente** lo que hace `exR` — pelar
un `∃` y sustituir:

    us.length < n  →  ∃ A, instB n us φ = ∃A  ∧  instB n (us ++ [t]) φ = A[0 := t]

Con ella, el caso `exR` de la inducción de 14 casos se cierra solo, y los otros trece son el calco
de `FOL.Sequent0.lk0_herbrand`.

## ⭐ Y el testigo pide `QuantFree`, no «distinto del existencial»

`lk0_herbrand` exige del testigo `Not (d = Formula.ex φ)`. Aquí se pide **`QuantFree d`**, que es
más fuerte y hace el trabajo solo en el subcaso de `exR` en que **queda bloque**: el testigo no
puede ser la cabeza porque la cabeza sigue siendo un `∃`.
🔑 *Un invariante más fuerte puede salir MÁS BARATO: descarta casos en vez de obligar a tratarlos.*

## ⚠️ El caso `n = 0`, que no es decorativo

`exBlock 0 φ = φ` **sí** es sin cuantificadores, luego en `n = 0` el testigo de la inducción es
legítimo y no hay contradicción que explotar. El ensamblaje distingue: para `n = 0` mete la **tupla
vacía** en el certificado, y entonces la hipótesis «todas las instancias falsas» contradice al
testigo. Sin ese `cases`, el teorema no sale.

## ⚠️ Lo que esto NO cambia

No toca `Derives`, ni `axioms ⊢`, ni el frente gödeliano. Es la vía H: sintáctica y finitaria.
-/

namespace FOL.BlockExtraction0

open FOL.Herbrand0
open FOL.HerbrandBlock0
open FOL.Sequent0
open FOL.Propositional0

theorem instB_nil : ∀ (n : Nat) (φ : Formula), instB n [] φ = exBlock n φ
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem instB_snoc : ∀ (n : Nat) (us : List Term) (φ : Formula) (t : Term), us.length < n →
    ∃ A, And (instB n us φ = Formula.ex A)
             (instB n (us ++ [t]) φ = substFormula 0 t A)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, [], φ, t, _ => by
      refine ⟨exBlock m φ, rfl, ?_⟩
      show instB m [] (substFormula m (liftN m t) φ) = substFormula 0 t (exBlock m φ)
      rw [subst_exBlock m φ 0 t, instB_nil m (substFormula m (liftN m t) φ)]
      rfl
  | m + 1, u :: us, φ, t, h => by
      have h' : us.length < m := Nat.lt_of_succ_lt_succ h
      obtain ⟨A, hA1, hA2⟩ := instB_snoc m us (substFormula m (liftN m u) φ) t h'
      exact ⟨A, hA1, hA2⟩

-- ══════════════════════════════════════════════════════════════════════════
-- El invariante y la salida
-- ══════════════════════════════════════════════════════════════════════════

/-- Cada fórmula del consecuente es sin cuantificadores, o es un RESTO del bloque: `instB n us φ`
con `us` una tupla **parcial**. ⭐ No hace falta ninguna función nueva: `instB` con la lista corta
ya devuelve el bloque pendiente. -/
def BlockInv (n : Nat) (φ : Formula) (d : Formula) : Prop :=
  Or (QuantFree d) (∃ us : List Term, And (us.length ≤ n) (d = instB n us φ))

/-- ⭐ Un resto que no es un `∃` es una instancia COMPLETA, y por tanto sin cuantificadores. -/
theorem quantFree_of_blockInv {n : Nat} {φ : Formula} (hφ : QuantFree φ) :
    ∀ {d : Formula}, BlockInv n φ d → (∀ A, Not (d = Formula.ex A)) → QuantFree d := by
  intro d hd hne
  cases hd with
  | inl h => exact h
  | inr h =>
      obtain ⟨us, hle, he⟩ := h
      rcases Nat.lt_or_ge us.length n with hlt | hge
      · obtain ⟨A, hA1, _⟩ := instB_snoc n us φ (Term.var 0) hlt
        exact absurd (he.trans hA1) (hne A)
      · have hlen : us.length = n := Nat.le_antisymm hle hge
        exact he ▸ quantFree_instB n us φ hlen hφ

def HerbrandOutB (n : Nat) (φ : Formula) (Γ Δ : List Formula)
    (tss : List (List Term)) (E : List Formula) : Prop :=
  ∀ v : PVal,
    (∀ g, g ∈ Γ → peval v g = true) →
    (∀ g, g ∈ E → peval v g = true) →
    (∀ ts, ts ∈ tss → peval v (instB n ts φ) = false) →
    ∃ d, And (d ∈ Δ) (And (QuantFree d) (peval v d = true))

private theorem nilEq : ∀ g, g ∈ ([] : List Formula) → EqInstance g :=
  fun _ hg => absurd hg List.not_mem_nil

private theorem appEq {E1 E2 : List Formula}
    (h1 : ∀ g, g ∈ E1 → EqInstance g) (h2 : ∀ g, g ∈ E2 → EqInstance g) :
    ∀ g, g ∈ E1 ++ E2 → EqInstance g :=
  fun g hg => (List.mem_append.mp hg).elim (h1 g) (h2 g)

private theorem nilLen (n : Nat) : ∀ ts, ts ∈ ([] : List (List Term)) → ts.length = n :=
  fun _ hg => absurd hg List.not_mem_nil

private theorem appLen {n : Nat} {T1 T2 : List (List Term)}
    (h1 : ∀ ts, ts ∈ T1 → ts.length = n) (h2 : ∀ ts, ts ∈ T2 → ts.length = n) :
    ∀ ts, ts ∈ T1 ++ T2 → ts.length = n :=
  fun ts hts => (List.mem_append.mp hts).elim (h1 ts) (h2 ts)

-- ══════════════════════════════════════════════════════════════════════════
-- 🏁 LA EXTRACCION DE HERBRAND PARA BLOQUES, sobre `LK₀`
-- ══════════════════════════════════════════════════════════════════════════

theorem lk0_herbrand_block {n : Nat} {φ : Formula} (hφ : QuantFree φ) :
    ∀ {Γ Δ : List Formula}, LK₀ Γ Δ →
    (∀ g, g ∈ Γ → QuantFree g) →
    (∀ d, d ∈ Δ → BlockInv n φ d) →
    ∃ (tss : List (List Term)) (E : List Formula),
      And (∀ ts, ts ∈ tss → ts.length = n)
        (And (∀ g, g ∈ E → EqInstance g) (HerbrandOutB n φ Γ Δ tss E)) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hΓ hΔ =>
      intro hqΓ _
      exact ⟨[], [], nilLen n, nilEq, fun v hv _ _ => ⟨A, hΔ, hqΓ A hΓ, hv A hΓ⟩⟩
  | botL Γ Δ hbot =>
      intro _ _
      refine ⟨[], [], nilLen n, nilEq, fun v hv _ _ => ?_⟩
      exact absurd (hv _ hbot) (by simp [peval])
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro hqΓ' hqΔ'
      obtain ⟨tss, E, hL, hE, hts⟩ := ih (fun g hg => hqΓ' g (hsΓ g hg))
        (fun d hd => hqΔ' d (hsΔ d hd))
      refine ⟨tss, E, hL, hE, fun v hv hEv hf => ?_⟩
      obtain ⟨d, hd, hq, hval⟩ := hts v (fun g hg => hv g (hsΓ g hg)) hEv hf
      exact ⟨d, hsΔ d hd, hq, hval⟩
  | implR Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) :=
        quantFree_of_blockInv hφ (hqΔ _ (List.Mem.head _)) (fun _ he => Formula.noConfusion he)
      obtain ⟨tss, E, hL, hE, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g h')
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨tss, E, hL, hE, fun v hv hEv hf => ?_⟩
      cases hA : peval v A with
      | false =>
          refine ⟨Formula.impl A B, List.Mem.head _, hAB, ?_⟩
          show ((!(peval v A)) || peval v B) = true
          simp [hA]
      | true =>
          obtain ⟨d, hd, hq, hval⟩ := hts v
            (fun g hg => by cases hg with
                            | head => exact hA
                            | tail _ h' => exact hv g h') hEv hf
          cases hd with
          | head =>
              refine ⟨Formula.impl A B, List.Mem.head _, hAB, ?_⟩
              show ((!(peval v A)) || peval v B) = true
              simp [hval]
          | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hq, hval⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨T1, E1, hL1, hE1, h1⟩ := ih1 (fun g hg => hqΓ g (List.Mem.tail _ hg))
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d h')
      obtain ⟨T2, E2, hL2, hE2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h'))
        hqΔ
      refine ⟨T1 ++ T2, E1 ++ E2, appLen hL1 hL2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ ts, ts ∈ T1 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ ts, ts ∈ T2 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hEl : ∀ g, g ∈ E1 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inl hg))
      have hEr : ∀ g, g ∈ E2 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inr hg))
      have hvt : ∀ g, g ∈ Γ → peval v g = true := fun g hg => hv g (List.Mem.tail _ hg)
      obtain ⟨d, hd, hq, hval⟩ := h1 v hvt hEl hfl
      cases hd with
      | head =>
          have hABv : peval v (Formula.impl A B) = true := hv _ (List.Mem.head _)
          have hBv : peval v B = true := by
            have hx : ((!(peval v A)) || peval v B) = true := hABv
            rw [hval] at hx
            simpa using hx
          exact h2 v (fun g hg => by cases hg with
                                     | head => exact hBv
                                     | tail _ h' => exact hvt g h') hEr hfr
      | tail _ hd' => exact ⟨d, hd', hq, hval⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) :=
        quantFree_of_blockInv hφ (hqΔ _ (List.Mem.head _)) (fun _ he => Formula.noConfusion he)
      obtain ⟨T1, E1, hL1, hE1, h1⟩ := ih1 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      obtain ⟨T2, E2, hL2, hE2, h2⟩ := ih2 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨T1 ++ T2, E1 ++ E2, appLen hL1 hL2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ ts, ts ∈ T1 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ ts, ts ∈ T2 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hEl : ∀ g, g ∈ E1 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inl hg))
      have hEr : ∀ g, g ∈ E2 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inr hg))
      obtain ⟨d1, hd1, hq1, hval1⟩ := h1 v hv hEl hfl
      cases hd1 with
      | tail _ hd1' => exact ⟨d1, List.Mem.tail _ hd1', hq1, hval1⟩
      | head =>
          obtain ⟨d2, hd2, hq2, hval2⟩ := h2 v hv hEr hfr
          cases hd2 with
          | tail _ hd2' => exact ⟨d2, List.Mem.tail _ hd2', hq2, hval2⟩
          | head =>
              refine ⟨Formula.and A B, List.Mem.head _, hAB, ?_⟩
              show (peval v A && peval v B) = true
              simp [hval1, hval2]
  | andL Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨tss, E, hL, hE, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact hAB.2
                                       | tail _ h'' => exact hqΓ g (List.Mem.tail _ h''))
        hqΔ
      refine ⟨tss, E, hL, hE, fun v hv hEv hf => ?_⟩
      have hABv : peval v (Formula.and A B) = true := hv _ (List.Mem.head _)
      have hAv : peval v A = true := by
        have hx : (peval v A && peval v B) = true := hABv
        cases hy : peval v A with
        | true => rfl
        | false => simp [hy] at hx
      have hBv : peval v B = true := by
        have hx : (peval v A && peval v B) = true := hABv
        cases hy : peval v B with
        | true => rfl
        | false => simp [hy] at hx
      exact hts v (fun g hg => by
        cases hg with
        | head => exact hAv
        | tail _ h' => cases h' with
                       | head => exact hBv
                       | tail _ h'' => exact hv g (List.Mem.tail _ h'')) hEv hf
  | orR Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.or A B) :=
        quantFree_of_blockInv hφ (hqΔ _ (List.Mem.head _)) (fun _ he => Formula.noConfusion he)
      obtain ⟨tss, E, hL, hE, hts⟩ := ih hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact Or.inl hAB.2
                                       | tail _ h'' => exact hqΔ d (List.Mem.tail _ h''))
      refine ⟨tss, E, hL, hE, fun v hv hEv hf => ?_⟩
      obtain ⟨d, hd, hq, hval⟩ := hts v hv hEv hf
      cases hd with
      | head =>
          refine ⟨Formula.or A B, List.Mem.head _, hAB, ?_⟩
          show (peval v A || peval v B) = true
          simp [hval]
      | tail _ hd' =>
          cases hd' with
          | head =>
              refine ⟨Formula.or A B, List.Mem.head _, hAB, ?_⟩
              show (peval v A || peval v B) = true
              simp [hval]
          | tail _ hd'' => exact ⟨d, List.Mem.tail _ hd'', hq, hval⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.or A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨T1, E1, hL1, hE1, h1⟩ := ih1
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      obtain ⟨T2, E2, hL2, hE2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      refine ⟨T1 ++ T2, E1 ++ E2, appLen hL1 hL2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ ts, ts ∈ T1 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ ts, ts ∈ T2 → peval v (instB n ts φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hEl : ∀ g, g ∈ E1 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inl hg))
      have hEr : ∀ g, g ∈ E2 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inr hg))
      have hABv : peval v (Formula.or A B) = true := hv _ (List.Mem.head _)
      have hx : (peval v A || peval v B) = true := hABv
      have hvt : ∀ g, g ∈ Γ → peval v g = true := fun g hg => hv g (List.Mem.tail _ hg)
      cases hA : peval v A with
      | true =>
          exact h1 v (fun g hg => by cases hg with
                                     | head => exact hA
                                     | tail _ h' => exact hvt g h') hEl hfl
      | false =>
          have hB : peval v B = true := by rw [hA] at hx; simpa using hx
          exact h2 v (fun g hg => by cases hg with
                                     | head => exact hB
                                     | tail _ h' => exact hvt g h') hEr hfr
  -- ⛔ los tres casos IMPOSIBLES
  | allR Γ Δ A _ _ =>
      intro _ hqΔ
      exact (not_quantFree_all A
        (quantFree_of_blockInv hφ (hqΔ _ (List.Mem.head _))
          (fun _ he => Formula.noConfusion he))).elim
  | allL Γ Δ A t _ _ =>
      intro hqΓ _; exact (not_quantFree_all A (hqΓ _ (List.Mem.head _))).elim
  | exL Γ Δ A _ _ =>
      intro hqΓ _; exact (not_quantFree_ex A (hqΓ _ (List.Mem.head _))).elim
  -- ⭐⭐ EL CASO QUE ALARGA LA TUPLA PARCIAL
  | exR Γ Δ A t _ ih =>
      intro hqΓ hqΔ
      -- la principal es un RESTO con tupla parcial ESTRICTAMENTE corta
      obtain ⟨us, hle, heq⟩ : ∃ us : List Term,
          And (us.length ≤ n) (Formula.ex A = instB n us φ) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact (not_quantFree_ex A hx).elim
        | inr hx => exact hx
      have hlt : us.length < n := by
        rcases Nat.lt_or_ge us.length n with h1 | h1
        · exact h1
        · have hlen : us.length = n := Nat.le_antisymm hle h1
          exact absurd (heq ▸ quantFree_instB n us φ hlen hφ) (not_quantFree_ex A)
      obtain ⟨A', hA1, hA2⟩ := instB_snoc n us φ t hlt
      have hAA' : A = A' := Formula.ex.inj (heq.trans hA1)
      subst hAA'
      -- la premisa lleva el resto alargado
      have hprem : substFormula 0 t A = instB n (us ++ [t]) φ := hA2.symm
      have hlen' : (us ++ [t]).length = us.length + 1 := by simp
      obtain ⟨tss, E, hL, hE, hts⟩ := ih hqΓ
        (fun d hd => by
          cases hd with
          | head => exact Or.inr ⟨us ++ [t], by omega, hprem⟩
          | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      rcases Nat.lt_or_ge (us.length + 1) n with hshort | hfull
      · -- queda bloque: el testigo no puede ser la cabeza, porque NO es sin cuantificadores
        refine ⟨tss, E, hL, hE, fun v hv hEv hf => ?_⟩
        obtain ⟨d, hd, hq, hval⟩ := hts v hv hEv hf
        cases hd with
        | head =>
            obtain ⟨A'', hA''1, _⟩ := instB_snoc n (us ++ [t]) φ (Term.var 0) (by omega)
            exact absurd (hprem.trans hA''1 ▸ hq : QuantFree (Formula.ex A''))
              (not_quantFree_ex A'')
        | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hq, hval⟩
      · -- la tupla se COMPLETA: entra en `tss`
        have hn : (us ++ [t]).length = n := by omega
        refine ⟨(us ++ [t]) :: tss, E, ?_, hE, fun v hv hEv hf => ?_⟩
        · intro ts hts2
          cases hts2 with
          | head => exact hn
          | tail _ h' => exact hL ts h'
        · obtain ⟨d, hd, hq, hval⟩ := hts v hv hEv
            (fun s hs => hf s (List.Mem.tail _ hs))
          cases hd with
          | head =>
              rw [hprem, hf (us ++ [t]) (List.Mem.head _)] at hval
              exact Bool.noConfusion hval
          | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hq, hval⟩
  | eqAx Γ Δ g hg _ ih =>
      intro hqΓ hqΔ
      obtain ⟨tss, E, hL, hE, hts⟩ := ih
        (fun x hx => by
          cases hx with
          | head => exact quantFree_of_eqInstance hg
          | tail _ h' => exact hqΓ x h')
        hqΔ
      refine ⟨tss, g :: E, hL, ?_, fun v hv hEv hf => ?_⟩
      · intro x hx
        cases hx with
        | head => exact hg
        | tail _ h' => exact hE x h'
      · exact hts v
          (fun x hx => by
            cases hx with
            | head => exact hEv g (List.Mem.head _)
            | tail _ h' => exact hv x h')
          (fun x hx => hEv x (List.Mem.tail _ hx)) hf

-- ── o la disyuncion de tuplas es verdadera, o TODAS las instancias son falsas ──
theorem disjB_or_allFalse (v : PVal) (n : Nat) (φ : Formula) : ∀ tss : List (List Term),
    Or (peval v (herbrandDisjBlock n φ tss) = true)
       (∀ ts, ts ∈ tss → peval v (instB n ts φ) = false)
  | [] => Or.inr (fun _ h => absurd h List.not_mem_nil)
  | ts :: rest => by
      cases ht : peval v (instB n ts φ) with
      | true =>
          refine Or.inl ?_
          show (peval v (instB n ts φ) || peval v (herbrandDisjBlock n φ rest)) = true
          simp [ht]
      | false =>
          cases disjB_or_allFalse v n φ rest with
          | inl hd =>
              refine Or.inl ?_
              show (peval v (instB n ts φ) || peval v (herbrandDisjBlock n φ rest)) = true
              simp [hd]
          | inr hall =>
              refine Or.inr (fun s hs => ?_)
              cases hs with
              | head => exact ht
              | tail _ h' => exact hall s h'

/-- ⚠️ El bloque de altura 0 ES su cuerpo, y por tanto SIN cuantificadores. Por eso el
ensamblaje tiene que distinguir `n = 0`: ahí el testigo del lema de inducción es legítimo y
hay que excluirlo metiendo la tupla vacía en el certificado. -/
theorem herbrandExtractionBlock_of (hcut : CutElim) (htr : NDtoLK) :
    HerbrandExtractionBlock := by
  intro n φ hqf hd
  have hlk : LKc [] [exBlock n φ] :=
    htr [] (exBlock n φ) (FOL.Derives2.derives0_iff_derives2.mp hd)
  have hlk0 : LK₀ [] [exBlock n φ] := hcut _ _ hlk
  obtain ⟨tss, E, hL, hE, hts⟩ := lk0_herbrand_block (n := n) (φ := φ) hqf hlk0
    (fun g hg => absurd hg List.not_mem_nil)
    (fun d hd2 => by
      cases hd2 with
      | head => exact Or.inr ⟨[], Nat.zero_le n, (instB_nil n φ).symm⟩
      | tail _ h2 => exact absurd h2 List.not_mem_nil)
  cases n with
  | succ m =>
      refine ⟨tss, E, hL, hE, fun v hv => ?_⟩
      cases disjB_or_allFalse v (m + 1) φ tss with
      | inl hok => exact hok
      | inr hall =>
          obtain ⟨d, hdmem, hq, _⟩ := hts v (fun g hg => absurd hg List.not_mem_nil) hv hall
          cases hdmem with
          | head => exact absurd hq (not_quantFree_ex (exBlock m φ))
          | tail _ h2 => exact absurd h2 List.not_mem_nil
  | zero =>
      refine ⟨[] :: tss, E, ?_, hE, fun v hv => ?_⟩
      · intro ts hts2
        cases hts2 with
        | head => rfl
        | tail _ h' => exact hL ts h'
      · cases disjB_or_allFalse v 0 φ ([] :: tss) with
        | inl hok => exact hok
        | inr hall =>
            obtain ⟨d, hdmem, _, hval⟩ := hts v (fun g hg => absurd hg List.not_mem_nil) hv
              (fun s hs => hall s (List.Mem.tail _ hs))
            cases hdmem with
            | head =>
                -- ⚠️ `instB 0 [] φ` y `exBlock 0 φ` son AMBOS `φ`, pero `rw` casa por sintaxis:
                -- hay que pedir la forma común con dos `have` tipados.
                have hfalse : peval v φ = false := hall [] (List.Mem.head _)
                have htrue : peval v φ = true := hval
                rw [hfalse] at htrue
                exact Bool.noConfusion htrue
            | tail _ h2 => exact absurd h2 List.not_mem_nil

/-- 🏁🏁 **LA MITAD ⟹ DE E, PAGADA.** -/
theorem herbrand_extraction_block : HerbrandExtractionBlock :=
  herbrandExtractionBlock_of FOL.Hauptsatz0.cut_elimination FOL.NDtoLK0.ndToLK_prop

/-- 🏁🏁🏁 **HERBRAND DE BLOQUE, YA INCONDICIONAL.** -/
theorem herbrand_block {n : Nat} {φ : Formula} (hqf : QuantFree φ) :
    Iff ([] ⊢₀ exBlock n φ) (∃ tss E, HerbrandCertBlock n φ tss E) :=
  herbrand_block_iff herbrand_extraction_block hqf

end FOL.BlockExtraction0

#print axioms FOL.BlockExtraction0.instB_nil
#print axioms FOL.BlockExtraction0.instB_snoc
#print axioms FOL.BlockExtraction0.quantFree_of_blockInv
#print axioms FOL.BlockExtraction0.lk0_herbrand_block
#print axioms FOL.BlockExtraction0.herbrandExtractionBlock_of
#print axioms FOL.BlockExtraction0.herbrand_extraction_block
#print axioms FOL.BlockExtraction0.herbrand_block
