/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives2, FOL.Herbrand0
-- @axiom_system: classical
-- @importance: high

import FOL.Derives2
import FOL.Herbrand0

/-!
# `FOL.Sequent0` — **el cálculo de secuentes**, y H3 reducida a DOS obligaciones

Tercera pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.7). ADR‑044 y ADR‑045 dejaron el
cálculo en forma de libro; **aquí se pone en la forma en la que el Hauptsatz se ENUNCIA**, y se
demuestra lo único que valida esa forma: **que de una prueba sin corte salen los testigos**.

    LK₀                    -- secuentes clásicos de dos lados, SIN corte
    LKc                    -- lo mismo MÁS la regla de corte
    lk0_herbrand           -- ⭐⭐ la EXTRACCIÓN: de `LK₀ E ⟹ ∃xφ` salen los términos
    CutElim, NDtoLK        -- ⬜ las DOS obligaciones que quedan, enunciadas como `Prop`
    herbrandExtraction_of  -- ⭐⭐⭐ y con las dos, H3

## ⭐ Por qué el orden es éste, y no al revés

ADR‑043 §3 decidió **no** construir `LK₀` mientras no hubiera consumidor: *la guarda se copia del
CONSUMIDOR, no del molde*. El consumidor apareció en ADR‑043 (`HerbrandCert`) y el cálculo quedó
en forma estándar en ADR‑045. Sólo entonces tiene sentido el molde — y **lo primero que se hace con
él es probar el consumidor**, `lk0_herbrand`. Si esa prueba no hubiera salido, `LK₀` estaría mal
diseñado y no lo sabríamos hasta el Hauptsatz.

## ⭐⭐ `lk0_herbrand`: cómo se leen los testigos

El enunciado es, en contrapositiva —que es la forma en que la inducción cierra—:

> si `Γ` es **sin cuantificadores**, y `Δ` lo es salvo apariciones de `∃φ`, entonces hay una lista
> finita `ts` tal que, para toda valuación: si `Γ` es verdadero y **todas** las instancias
> `φ(t)` con `t ∈ ts` son falsas, entonces algún elemento de `Δ` **distinto de `∃φ`** es verdadero.

Con `Δ = [∃φ]` el consecuente es imposible, así que queda: *`Γ` verdadero ⇒ alguna instancia
verdadera* — que es exactamente la segunda componente de `HerbrandCert`.

La inducción tiene **13** casos y se reparten en tres grupos:

| grupo | casos | qué pasa |
|---|---|---|
| **producen el testigo** | `exR` | ⭐ `∃A` en el sucedente sólo puede ser `∃φ`, y el término de la regla **es** un testigo: `ts := t :: ts'` |
| ⛔ **imposibles** | `allR`, `allL`, `exL` | meten un cuantificador donde la hipótesis dice que no lo hay ⇒ el caso se cierra por absurdo |
| **proposicionales** | los **nueve** restantes | bookkeeping sobre `peval`, sin sorpresas |

🔑 **Y ahí se ve para qué sirve el Hauptsatz**: la regla de **corte** tendría una fórmula `A`
arbitraria —posiblemente cuantificada— que no aparece en la conclusión, así que **las hipótesis de
la inducción no se heredan**. *El corte es exactamente lo que rompe esta lectura.*

## ⬜ Las dos obligaciones que quedan — enunciadas, no postuladas

    CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ                       -- el HAUPTSATZ
    NDtoLK  : ∀ Γ f, Derives₂ Γ f →
                ∃ E, (∀ g ∈ E, EqInstance g) ∧ LKc (E ++ Γ) [f]

y **el consumidor está escrito**: `herbrandExtraction_of (hcut) (htr) : HerbrandExtraction`. ⇒
con esas dos, H3 y la vía H quedan cerradas.

⚠️ **`NDtoLK` no es rutina, y su dificultad está localizada**: el caso `intro_forall` levanta el
contexto, así que la lista `E` de instancias de igualdad recogida por la hipótesis de inducción
vive en el contexto **levantado**, y hay que producirla desde el de abajo. Las instancias con
`Term.var 0` no son el levantamiento de ninguna. ⬜ Medido como problema, no como coste.

## ⬜ Y una comprobación que NO está hecha

`LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)` —que `LK₀` no es **demasiado fuerte**— ⬜ no se ha demostrado.
⚠️ El obstáculo está identificado y es el caso `allR`: exige sacar una disyunción de dentro de un
cuantificador (`∀x(A ∨ C) → (∀x A) ∨ C` con `C` sin `x`), que es clásico pero pide su propia capa
de lemas sobre el levantamiento. **No está en el camino crítico de H3** —las dos obligaciones de
arriba no pasan por ella—, pero sí es lo que certificaría que el molde no prueba de más.

## 📏 Footprint

`lk0_herbrand` mide **`[propext]`** y `lk0_to_lkc` **ningún axioma**; la cadena,
`[propext, Quot.sound]`. **Ni un `Classical.choice` en todo el módulo.**
-/

-- ── LK₀ : secuentes clásicos de dos lados, SIN corte y SIN igualdad ─────────
inductive LK₀ : List Formula → List Formula → Prop where
  | ax : ∀ Γ Δ A, A ∈ Γ → A ∈ Δ → LK₀ Γ Δ
  | botL : ∀ Γ Δ, Formula.bottom ∈ Γ → LK₀ Γ Δ
  | struct : ∀ Γ Γ' Δ Δ', LK₀ Γ Δ → (∀ x, x ∈ Γ → x ∈ Γ') → (∀ x, x ∈ Δ → x ∈ Δ') → LK₀ Γ' Δ'
  | implR : ∀ Γ Δ A B, LK₀ (A :: Γ) (B :: Δ) → LK₀ Γ (Formula.impl A B :: Δ)
  | implL : ∀ Γ Δ A B, LK₀ Γ (A :: Δ) → LK₀ (B :: Γ) Δ → LK₀ (Formula.impl A B :: Γ) Δ
  | andR : ∀ Γ Δ A B, LK₀ Γ (A :: Δ) → LK₀ Γ (B :: Δ) → LK₀ Γ (Formula.and A B :: Δ)
  | andL : ∀ Γ Δ A B, LK₀ (A :: B :: Γ) Δ → LK₀ (Formula.and A B :: Γ) Δ
  | orR : ∀ Γ Δ A B, LK₀ Γ (A :: B :: Δ) → LK₀ Γ (Formula.or A B :: Δ)
  | orL : ∀ Γ Δ A B, LK₀ (A :: Γ) Δ → LK₀ (B :: Γ) Δ → LK₀ (Formula.or A B :: Γ) Δ
  | allR : ∀ Γ Δ A, LK₀ (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) →
      LK₀ Γ (Formula.forall A :: Δ)
  | allL : ∀ Γ Δ A t, LK₀ (substFormula 0 t A :: Γ) Δ → LK₀ (Formula.forall A :: Γ) Δ
  | exR : ∀ Γ Δ A t, LK₀ Γ (substFormula 0 t A :: Δ) → LK₀ Γ (Formula.ex A :: Δ)
  | exL : ∀ Γ Δ A, LK₀ (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) →
      LK₀ (Formula.ex A :: Γ) Δ

-- ── LKc : LK₀ MAS la regla de CORTE ────────────────────────────────────────
inductive LKc : List Formula → List Formula → Prop where
  | ax : ∀ G D A, A ∈ G → A ∈ D → LKc G D
  | botL : ∀ G D, Formula.bottom ∈ G → LKc G D
  | struct : ∀ G G2 D D2, LKc G D → (∀ x, x ∈ G → x ∈ G2) ->
      (∀ x, x ∈ D → x ∈ D2) → LKc G2 D2
  | implR : ∀ G D A B, LKc (A :: G) (B :: D) → LKc G (Formula.impl A B :: D)
  | implL : ∀ G D A B, LKc G (A :: D) → LKc (B :: G) D → LKc (Formula.impl A B :: G) D
  | andR : ∀ G D A B, LKc G (A :: D) → LKc G (B :: D) → LKc G (Formula.and A B :: D)
  | andL : ∀ G D A B, LKc (A :: B :: G) D → LKc (Formula.and A B :: G) D
  | orR : ∀ G D A B, LKc G (A :: B :: D) → LKc G (Formula.or A B :: D)
  | orL : ∀ G D A B, LKc (A :: G) D → LKc (B :: G) D → LKc (Formula.or A B :: G) D
  | allR : ∀ G D A, LKc (G.map (liftFormula 0)) (A :: D.map (liftFormula 0)) ->
      LKc G (Formula.forall A :: D)
  | allL : ∀ G D A t, LKc (substFormula 0 t A :: G) D → LKc (Formula.forall A :: G) D
  | exR : ∀ G D A t, LKc G (substFormula 0 t A :: D) → LKc G (Formula.ex A :: D)
  | exL : ∀ G D A, LKc (A :: G.map (liftFormula 0)) (D.map (liftFormula 0)) ->
      LKc (Formula.ex A :: G) D
  | cut : ∀ G D A, LKc G (A :: D) → LKc (A :: G) D → LKc G D

namespace FOL.Sequent0

open FOL.Propositional0
open FOL.Herbrand0

-- ============================================================
-- §1 · Lemas de `QuantFree`
-- ============================================================

-- ── `QuantFree` se conserva por sustitución ─────────────────────────────────
theorem quantFree_subst : ∀ (f : Formula) (v : Nat) (t : Term),
    QuantFree f → QuantFree (substFormula v t f) := by
  intro f
  induction f with
  | bottom => intro _ _ _; trivial
  | atom _ _ => intro _ _ _; trivial
  | eq _ _ => intro _ _ _; trivial
  | impl A B ihA ihB => intro v t h; exact ⟨ihA v t h.1, ihB v t h.2⟩
  | and A B ihA ihB => intro v t h; exact ⟨ihA v t h.1, ihB v t h.2⟩
  | or A B ihA ihB => intro v t h; exact ⟨ihA v t h.1, ihB v t h.2⟩
  | «forall» _ _ => intro _ _ h; exact h.elim
  | ex _ _ => intro _ _ h; exact h.elim

theorem not_quantFree_ex (A : Formula) : Not (QuantFree (Formula.ex A)) := fun h => h
theorem not_quantFree_all (A : Formula) : Not (QuantFree (Formula.forall A)) := fun h => h

-- ⭐⭐ LA EXTRACCIÓN: de una prueba SIN CORTE salen los testigos
theorem lk0_herbrand {φ : Formula} (hφ : QuantFree φ) :
    ∀ {Γ Δ : List Formula}, LK₀ Γ Δ →
    (∀ g, g ∈ Γ → QuantFree g) →
    (∀ d, d ∈ Δ → Or (QuantFree d) (d = Formula.ex φ)) →
    ∃ ts : List Term, ∀ v : PVal,
      (∀ g, g ∈ Γ → peval v g = true) →
      (∀ t, t ∈ ts → peval v (substFormula 0 t φ) = false) →
      ∃ d, And (d ∈ Δ) (And (Not (d = Formula.ex φ)) (peval v d = true)) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hΓ hΔ =>
      intro hqΓ _
      refine ⟨[], fun v hv _ => ⟨A, hΔ, ?_, hv A hΓ⟩⟩
      intro he; exact not_quantFree_ex φ (he ▸ hqΓ A hΓ)
  | botL Γ Δ hbot =>
      intro _ _
      refine ⟨[], fun v hv _ => ?_⟩
      exact absurd (hv _ hbot) (by simp [peval])
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro hqΓ' hqΔ'
      obtain ⟨ts, hts⟩ := ih (fun g hg => hqΓ' g (hsΓ g hg)) (fun d hd => hqΔ' d (hsΔ d hd))
      refine ⟨ts, fun v hv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v (fun g hg => hv g (hsΓ g hg)) hf
      exact ⟨d, hsΔ d hd, hne, hval⟩
  | implR Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g h')
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨ts, fun v hv hf => ?_⟩
      cases hA : peval v A with
      | false =>
          refine ⟨Formula.impl A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
          show ((!(peval v A)) || peval v B) = true
          simp [hA]
      | true =>
          obtain ⟨d, hd, hne, hval⟩ := hts v
            (fun g hg => by cases hg with
                            | head => exact hA
                            | tail _ h' => exact hv g h') hf
          cases hd with
          | head =>
              refine ⟨Formula.impl A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
              show ((!(peval v A)) || peval v B) = true
              simp [hval]
          | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hne, hval⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨ts1, h1⟩ := ih1 (fun g hg => hqΓ g (List.Mem.tail _ hg))
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d h')
      obtain ⟨ts2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h'))
        hqΔ
      refine ⟨ts1 ++ ts2, fun v hv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hvt : ∀ g, g ∈ Γ → peval v g = true := fun g hg => hv g (List.Mem.tail _ hg)
      obtain ⟨d, hd, hne, hval⟩ := h1 v hvt hfl
      cases hd with
      | head =>
          -- `A` es verdadera; con `A → B` en el antecedente, `B` también
          have hABv : peval v (Formula.impl A B) = true := hv _ (List.Mem.head _)
          have hBv : peval v B = true := by
            have : ((!(peval v A)) || peval v B) = true := hABv
            rw [hval] at this
            simpa using this
          exact h2 v (fun g hg => by cases hg with
                                     | head => exact hBv
                                     | tail _ h' => exact hvt g h') hfr
      | tail _ hd' => exact ⟨d, hd', hne, hval⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts1, h1⟩ := ih1 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      obtain ⟨ts2, h2⟩ := ih2 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨ts1 ++ ts2, fun v hv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      obtain ⟨d1, hd1, hne1, hval1⟩ := h1 v hv hfl
      cases hd1 with
      | tail _ hd1' => exact ⟨d1, List.Mem.tail _ hd1', hne1, hval1⟩
      | head =>
          obtain ⟨d2, hd2, hne2, hval2⟩ := h2 v hv hfr
          cases hd2 with
          | tail _ hd2' => exact ⟨d2, List.Mem.tail _ hd2', hne2, hval2⟩
          | head =>
              refine ⟨Formula.and A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
              show (peval v A && peval v B) = true
              simp [hval1, hval2]
  | andL Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨ts, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact hAB.2
                                       | tail _ h'' => exact hqΓ g (List.Mem.tail _ h''))
        hqΔ
      refine ⟨ts, fun v hv hf => ?_⟩
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
                       | tail _ h'' => exact hv g (List.Mem.tail _ h'')) hf
  | orR Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.or A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts, hts⟩ := ih hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact Or.inl hAB.2
                                       | tail _ h'' => exact hqΔ d (List.Mem.tail _ h''))
      refine ⟨ts, fun v hv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v hv hf
      cases hd with
      | head =>
          refine ⟨Formula.or A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
          show (peval v A || peval v B) = true
          simp [hval]
      | tail _ hd' =>
          cases hd' with
          | head =>
              refine ⟨Formula.or A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
              show (peval v A || peval v B) = true
              simp [hval]
          | tail _ hd'' => exact ⟨d, List.Mem.tail _ hd'', hne, hval⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.or A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨ts1, h1⟩ := ih1
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      obtain ⟨ts2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      refine ⟨ts1 ++ ts2, fun v hv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hABv : peval v (Formula.or A B) = true := hv _ (List.Mem.head _)
      have hx : (peval v A || peval v B) = true := hABv
      have hvt : ∀ g, g ∈ Γ → peval v g = true := fun g hg => hv g (List.Mem.tail _ hg)
      cases hA : peval v A with
      | true =>
          exact h1 v (fun g hg => by cases hg with
                                     | head => exact hA
                                     | tail _ h' => exact hvt g h') hfl
      | false =>
          have hB : peval v B = true := by rw [hA] at hx; simpa using hx
          exact h2 v (fun g hg => by cases hg with
                                     | head => exact hB
                                     | tail _ h' => exact hvt g h') hfr
  -- ⛔ los tres casos IMPOSIBLES: meten un cuantificador donde no puede haberlo
  | allR Γ Δ A _ _ =>
      intro _ hqΔ
      cases hqΔ _ (List.Mem.head _) with
      | inl hx => exact (not_quantFree_all A hx).elim
      | inr hx => exact Formula.noConfusion hx
  | allL Γ Δ A t _ _ =>
      intro hqΓ _; exact (not_quantFree_all A (hqΓ _ (List.Mem.head _))).elim
  | exL Γ Δ A _ _ =>
      intro hqΓ _; exact (not_quantFree_ex A (hqΓ _ (List.Mem.head _))).elim
  -- ⭐⭐ EL CASO QUE PRODUCE UN TESTIGO
  | exR Γ Δ A t _ ih =>
      intro hqΓ hqΔ
      have hA : Formula.ex A = Formula.ex φ := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact (not_quantFree_ex A hx).elim
        | inr hx => exact hx
      have hAφ : A = φ := Formula.ex.inj hA
      subst hAφ
      obtain ⟨ts, hts⟩ := ih hqΓ
        (fun d hd => by
          cases hd with
          | head => exact Or.inl (quantFree_subst _ 0 t hφ)
          | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨t :: ts, fun v hv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v hv (fun s hs => hf s (List.Mem.tail _ hs))
      cases hd with
      | head =>
          rw [hf t (List.Mem.head _)] at hval
          exact Bool.noConfusion hval
      | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hne, hval⟩



-- ── toda instancia de la igualdad es SIN CUANTIFICADORES ────────────────────
theorem quantFree_of_eqInstance {g : Formula} (h : EqInstance g) : QuantFree g := by
  cases h with
  | refl t => trivial
  | symm t u => exact And.intro trivial trivial
  | trans t u w => exact And.intro trivial (And.intro trivial trivial)
  | func p pre post a b => exact And.intro trivial trivial
  | atom p pre post a b => exact And.intro trivial (And.intro trivial trivial)

-- ── o la disyuncion es verdadera, o TODAS las instancias son falsas ─────────
theorem disj_or_allFalse (v : PVal) (φ : Formula) : ∀ ts : List Term,
    Or (peval v (herbrandDisj φ ts) = true)
       (∀ t, t ∈ ts → peval v (substFormula 0 t φ) = false)
  | [] => Or.inr (fun _ h => absurd h List.not_mem_nil)
  | t :: ts => by
      cases ht : peval v (substFormula 0 t φ) with
      | true =>
          refine Or.inl ?_
          show (peval v (substFormula 0 t φ) || peval v (herbrandDisj φ ts)) = true
          simp [ht]
      | false =>
          cases disj_or_allFalse v φ ts with
          | inl hd =>
              refine Or.inl ?_
              show (peval v (substFormula 0 t φ) || peval v (herbrandDisj φ ts)) = true
              simp [hd]
          | inr hall =>
              refine Or.inr (fun s hs => ?_)
              cases hs with
              | head => exact ht
              | tail _ h2 => exact hall s h2

-- ============================================================
-- §2 · El encaje y las DOS obligaciones
-- ============================================================

theorem lk0_to_lkc {G D : List Formula} (h : LK₀ G D) : LKc G D := by
  induction h with
  | ax G D A h1 h2 => exact LKc.ax G D A h1 h2
  | botL G D h1 => exact LKc.botL G D h1
  | struct G G2 D D2 _ h1 h2 ih => exact LKc.struct G G2 D D2 ih h1 h2
  | implR G D A B _ ih => exact LKc.implR G D A B ih
  | implL G D A B _ _ ih1 ih2 => exact LKc.implL G D A B ih1 ih2
  | andR G D A B _ _ ih1 ih2 => exact LKc.andR G D A B ih1 ih2
  | andL G D A B _ ih => exact LKc.andL G D A B ih
  | orR G D A B _ ih => exact LKc.orR G D A B ih
  | orL G D A B _ _ ih1 ih2 => exact LKc.orL G D A B ih1 ih2
  | allR G D A _ ih => exact LKc.allR G D A ih
  | allL G D A t _ ih => exact LKc.allL G D A t ih
  | exR G D A t _ ih => exact LKc.exR G D A t ih
  | exL G D A _ ih => exact LKc.exL G D A ih

/-- LA DEUDA 1: el HAUPTSATZ. -/
def CutElim : Prop := ∀ G D, LKc G D → LK₀ G D

/-- LA DEUDA 2: la traduccion de deduccion natural a secuentes CON corte,
recogiendo las instancias de la igualdad en el antecedente. -/
def NDtoLK : Prop := ∀ (G : List Formula) (f : Formula), Derives₂ G f ->
    Exists (fun E => And (∀ g, g ∈ E → EqInstance g) (LKc (E ++ G) [f]))

/-- LA CADENA: con las dos deudas, H3. -/
theorem herbrandExtraction_of (hcut : CutElim) (htr : NDtoLK) : HerbrandExtraction := by
  intro φ hqf hd
  obtain ⟨E, hE, hlk⟩ := htr [] φ.ex (FOL.Derives2.derives0_iff_derives2.mp hd)
  have hlk0 : LK₀ (E ++ []) [Formula.ex φ] := hcut _ _ hlk
  obtain ⟨ts, hts⟩ := lk0_herbrand (φ := φ) hqf hlk0
    (fun g hg => quantFree_of_eqInstance (hE g (by simpa using hg)))
    (fun d hd2 => by cases hd2 with
                     | head => exact Or.inr rfl
                     | tail _ h2 => exact absurd h2 List.not_mem_nil)
  refine ⟨ts, E, hE, fun v hv => ?_⟩
  cases disj_or_allFalse v φ ts with
  | inl hok => exact hok
  | inr hall =>
      obtain ⟨d, hdmem, hdne, _⟩ := hts v
        (fun g hg => hv g (by simpa using hg)) hall
      cases hdmem with
      | head => exact absurd rfl hdne
      | tail _ h2 => exact absurd h2 List.not_mem_nil

end FOL.Sequent0

#print axioms LK₀.rec
#print axioms FOL.Sequent0.lk0_herbrand
#print axioms FOL.Sequent0.lk0_to_lkc
#print axioms FOL.Sequent0.herbrandExtraction_of
