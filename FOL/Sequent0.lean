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
# `FOL.Sequent0` — **el cálculo de secuentes**, y H3 reducida a UNA obligación

Tercera pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.7). ADR‑044 y ADR‑045 dejaron el
cálculo en forma de libro; **aquí se pone en la forma en la que el Hauptsatz se ENUNCIA**, y se
demuestra lo único que valida esa forma: **que de una prueba sin corte salen los testigos**.

    LK₀                    -- secuentes clásicos de dos lados, SIN corte (14 ctors)
    LKc                    -- lo mismo MÁS la regla de corte (15)
    lk0_herbrand           -- ⭐⭐ la EXTRACCIÓN: de `LK₀ ⟹ ∃xφ` salen los términos Y las
                           --    instancias de igualdad que la derivación usa
    CutElim                -- ⬜ LA ÚNICA DEUDA QUE QUEDA: el Hauptsatz
    herbrandExtraction_of  -- ⭐⭐⭐ CutElim + NDtoLK ⇒ H3

## ⭐ Por qué el orden es éste, y no al revés

ADR‑043 §3 decidió **no** construir `LK₀` mientras no hubiera consumidor: *la guarda se copia del
CONSUMIDOR, no del molde*. El consumidor apareció en ADR‑043 (`HerbrandCert`) y el cálculo quedó
en forma estándar en ADR‑045. Sólo entonces tiene sentido el molde — y **lo primero que se hace con
él es probar el consumidor**, `lk0_herbrand`. Si esa prueba no hubiera salido, `LK₀` estaría mal
diseñado y no lo sabríamos hasta el Hauptsatz.

## ⭐⭐ `eqAx`: la regla que faltaba, y por qué

⚠️ **Revisión de diseño (ADR‑049).** La primera versión de este módulo no tenía `eqAx` y dejaba la
lista `E` de instancias de igualdad **en el antecedente**, recogida por la traducción `NDtoLK`.
**Medido: eso BLOQUEA `NDtoLK`** — el caso `intro_forall` **levanta el contexto**, así que la `E`
que devuelve la hipótesis de inducción vive arriba y hay que producirla abajo; y una instancia con
`Term.var 0` **no es el levantamiento de ninguna**. No hay manera.

⭐ La regla que lo desbloquea es el **corte contra un axioma de la teoría**:

    eqAx : EqInstance g → LK Γ' Δ  con  Γ' = g :: Γ   ⟹   LK Γ Δ

Es el *theory‑cut* estándar, y con él:

| | antes | ahora |
|---|---|---|
| `NDtoLK` | ⛔ bloqueado por el levantamiento | ✅ **demostrado** (`FOL.NDtoLK0`), traducción estructural sin `E` |
| `lk0_herbrand` | devolvía sólo `ts` | ⭐ devuelve `ts` **y** la `E` que la derivación usó |
| `CutElim` | estándar | estándar: los axiomas son **sin cuantificadores**, así que permutan como cualquier regla izquierda |

🔑 *Cuando una obligación se bloquea por bookkeeping, a veces lo que falta no es esfuerzo sino una
regla.*

⚠️ Y `eqAx` **no puede ser una regla derecha de igualdad** (`⟹ t ≐ t`): `peval` trata `t ≐ t` como
un **átomo**, y bajo una valuación arbitraria es falso. El certificado sólo puede decir *«la
disyunción se sigue de E»*, así que la `E` tiene que existir. **El diseño está forzado por la forma
de `HerbrandCert`, no elegido.**

## ⭐⭐ `lk0_herbrand`: cómo se leen los testigos

El enunciado es, en contrapositiva —que es la forma en que la inducción cierra—:

> si `Γ` es **sin cuantificadores**, y `Δ` lo es salvo apariciones de `∃φ`, entonces hay listas
> finitas `ts` y `E` (de instancias de igualdad) tales que, para toda valuación: si `Γ` y `E` son
> verdaderos y **todas** las instancias `φ(t)` con `t ∈ ts` son falsas, entonces algún elemento de
> `Δ` **distinto de `∃φ`** es verdadero.

Con `Γ = []` y `Δ = [∃φ]` el consecuente es imposible, así que queda: *`E` verdadero ⇒ alguna
instancia verdadera* — que es exactamente la segunda componente de `HerbrandCert`.

La inducción tiene **14** casos en tres grupos:

| grupo | casos | qué pasa |
|---|---|---|
| **producen el testigo** | `exR` | ⭐ `∃A` en el sucedente sólo puede ser `∃φ`, y el término de la regla **es** un testigo: `ts := t :: ts'` |
| **produce una instancia** | ⭐ `eqAx` | el axioma se recoge: `E := g :: E'` |
| ⛔ **imposibles** | `allR`, `allL`, `exL` | meten un cuantificador donde la hipótesis dice que no lo hay ⇒ el caso se cierra por absurdo |
| **proposicionales** | los nueve restantes | bookkeeping sobre `peval`, sin sorpresas |

🔑 **Y ahí se ve para qué sirve el Hauptsatz**: la regla de **corte** tendría una fórmula `A`
arbitraria —posiblemente cuantificada— que no aparece en la conclusión, así que **las hipótesis de
la inducción no se heredan**. *El corte es exactamente lo que rompe esta lectura.* ⚠️ Compárese con
`FOL.SequentSound0`, donde el corte es **semánticamente trivial**: *el corte es gratis para la
verdad y carísimo para la demostración.*

## ⬜ La obligación que queda — enunciada, no postulada

    CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ                       -- el HAUPTSATZ

y **el consumidor está escrito**: `herbrandExtraction_of (hcut) (htr) : HerbrandExtraction`, con
`htr` ya **demostrado** en `FOL.NDtoLK0`. ⇒ con `CutElim`, H3 y la vía H quedan cerradas.

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
  | eqAx : ∀ Γ Δ g, FOL.Herbrand0.EqInstance g → LK₀ (g :: Γ) Δ → LK₀ Γ Δ

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
  | eqAx : ∀ Γ Δ g, FOL.Herbrand0.EqInstance g → LKc (g :: Γ) Δ → LKc Γ Δ

namespace FOL.Sequent0

open FOL.Propositional0
open FOL.Herbrand0

-- ============================================================
-- §1 · Lemas de `QuantFree` y el tipo de salida
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

-- ── toda instancia de la igualdad es SIN CUANTIFICADORES ────────────────────
theorem quantFree_of_eqInstance {g : Formula} (h : EqInstance g) : QuantFree g := by
  cases h with
  | refl t => trivial
  | symm t u => exact And.intro trivial trivial
  | trans t u w => exact And.intro trivial (And.intro trivial trivial)
  | func p pre post a b => exact And.intro trivial trivial
  | atom p pre post a b => exact And.intro trivial (And.intro trivial trivial)


/-- Lo que la extracción devuelve: los términos **y** las instancias de igualdad que usa. -/
def HerbrandOut (φ : Formula) (Γ Δ : List Formula) (ts : List Term) (E : List Formula) : Prop :=
  ∀ v : PVal,
    (∀ g, g ∈ Γ → peval v g = true) →
    (∀ g, g ∈ E → peval v g = true) →
    (∀ t, t ∈ ts → peval v (substFormula 0 t φ) = false) →
    ∃ d, And (d ∈ Δ) (And (Not (d = Formula.ex φ)) (peval v d = true))

private theorem nilEq : ∀ g, g ∈ ([] : List Formula) → EqInstance g :=
  fun _ hg => absurd hg List.not_mem_nil

private theorem appEq {E1 E2 : List Formula}
    (h1 : ∀ g, g ∈ E1 → EqInstance g) (h2 : ∀ g, g ∈ E2 → EqInstance g) :
    ∀ g, g ∈ E1 ++ E2 → EqInstance g :=
  fun g hg => (List.mem_append.mp hg).elim (h1 g) (h2 g)

theorem lk0_herbrand {φ : Formula} (hφ : QuantFree φ) :
    ∀ {Γ Δ : List Formula}, LK₀ Γ Δ →
    (∀ g, g ∈ Γ → QuantFree g) →
    (∀ d, d ∈ Δ → Or (QuantFree d) (d = Formula.ex φ)) →
    ∃ (ts : List Term) (E : List Formula),
      And (∀ g, g ∈ E → EqInstance g) (HerbrandOut φ Γ Δ ts E) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hΓ hΔ =>
      intro hqΓ _
      refine ⟨[], [], nilEq, fun v hv _ _ => ⟨A, hΔ, ?_, hv A hΓ⟩⟩
      intro he; exact not_quantFree_ex φ (he ▸ hqΓ A hΓ)
  | botL Γ Δ hbot =>
      intro _ _
      refine ⟨[], [], nilEq, fun v hv _ _ => ?_⟩
      exact absurd (hv _ hbot) (by simp [peval])
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro hqΓ' hqΔ'
      obtain ⟨ts, E, hE, hts⟩ := ih (fun g hg => hqΓ' g (hsΓ g hg)) (fun d hd => hqΔ' d (hsΔ d hd))
      refine ⟨ts, E, hE, fun v hv hEv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v (fun g hg => hv g (hsΓ g hg)) hEv hf
      exact ⟨d, hsΔ d hd, hne, hval⟩
  | implR Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts, E, hE, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g h')
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨ts, E, hE, fun v hv hEv hf => ?_⟩
      cases hA : peval v A with
      | false =>
          refine ⟨Formula.impl A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
          show ((!(peval v A)) || peval v B) = true
          simp [hA]
      | true =>
          obtain ⟨d, hd, hne, hval⟩ := hts v
            (fun g hg => by cases hg with
                            | head => exact hA
                            | tail _ h' => exact hv g h') hEv hf
          cases hd with
          | head =>
              refine ⟨Formula.impl A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
              show ((!(peval v A)) || peval v B) = true
              simp [hval]
          | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hne, hval⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.impl A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨ts1, E1, hE1, h1⟩ := ih1 (fun g hg => hqΓ g (List.Mem.tail _ hg))
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d h')
      obtain ⟨ts2, E2, hE2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h'))
        hqΔ
      refine ⟨ts1 ++ ts2, E1 ++ E2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hEl : ∀ g, g ∈ E1 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inl hg))
      have hEr : ∀ g, g ∈ E2 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inr hg))
      have hvt : ∀ g, g ∈ Γ → peval v g = true := fun g hg => hv g (List.Mem.tail _ hg)
      obtain ⟨d, hd, hne, hval⟩ := h1 v hvt hEl hfl
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
                                     | tail _ h' => exact hvt g h') hEr hfr
      | tail _ hd' => exact ⟨d, hd', hne, hval⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts1, E1, hE1, h1⟩ := ih1 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      obtain ⟨ts2, E2, hE2, h2⟩ := ih2 hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.2
                        | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨ts1 ++ ts2, E1 ++ E2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inr ht))
      have hEl : ∀ g, g ∈ E1 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inl hg))
      have hEr : ∀ g, g ∈ E2 → peval v g = true :=
        fun g hg => hEv g (List.mem_append.mpr (Or.inr hg))
      obtain ⟨d1, hd1, hne1, hval1⟩ := h1 v hv hEl hfl
      cases hd1 with
      | tail _ hd1' => exact ⟨d1, List.Mem.tail _ hd1', hne1, hval1⟩
      | head =>
          obtain ⟨d2, hd2, hne2, hval2⟩ := h2 v hv hEr hfr
          cases hd2 with
          | tail _ hd2' => exact ⟨d2, List.Mem.tail _ hd2', hne2, hval2⟩
          | head =>
              refine ⟨Formula.and A B, List.Mem.head _, fun he => Formula.noConfusion he, ?_⟩
              show (peval v A && peval v B) = true
              simp [hval1, hval2]
  | andL Γ Δ A B _ ih =>
      intro hqΓ hqΔ
      have hAB : QuantFree (Formula.and A B) := hqΓ _ (List.Mem.head _)
      obtain ⟨ts, E, hE, hts⟩ := ih
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact hAB.2
                                       | tail _ h'' => exact hqΓ g (List.Mem.tail _ h''))
        hqΔ
      refine ⟨ts, E, hE, fun v hv hEv hf => ?_⟩
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
      have hAB : QuantFree (Formula.or A B) := by
        cases hqΔ _ (List.Mem.head _) with
        | inl hx => exact hx
        | inr hx => exact Formula.noConfusion hx
      obtain ⟨ts, E, hE, hts⟩ := ih hqΓ
        (fun d hd => by cases hd with
                        | head => exact Or.inl hAB.1
                        | tail _ h' => cases h' with
                                       | head => exact Or.inl hAB.2
                                       | tail _ h'' => exact hqΔ d (List.Mem.tail _ h''))
      refine ⟨ts, E, hE, fun v hv hEv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v hv hEv hf
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
      obtain ⟨ts1, E1, hE1, h1⟩ := ih1
        (fun g hg => by cases hg with
                        | head => exact hAB.1
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      obtain ⟨ts2, E2, hE2, h2⟩ := ih2
        (fun g hg => by cases hg with
                        | head => exact hAB.2
                        | tail _ h' => exact hqΓ g (List.Mem.tail _ h')) hqΔ
      refine ⟨ts1 ++ ts2, E1 ++ E2, appEq hE1 hE2, fun v hv hEv hf => ?_⟩
      have hfl : ∀ t, t ∈ ts1 → peval v (substFormula 0 t φ) = false :=
        fun t ht => hf t (List.mem_append.mpr (Or.inl ht))
      have hfr : ∀ t, t ∈ ts2 → peval v (substFormula 0 t φ) = false :=
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
      obtain ⟨ts, E, hE, hts⟩ := ih hqΓ
        (fun d hd => by
          cases hd with
          | head => exact Or.inl (quantFree_subst _ 0 t hφ)
          | tail _ h' => exact hqΔ d (List.Mem.tail _ h'))
      refine ⟨t :: ts, E, hE, fun v hv hEv hf => ?_⟩
      obtain ⟨d, hd, hne, hval⟩ := hts v hv hEv (fun s hs => hf s (List.Mem.tail _ hs))
      cases hd with
      | head =>
          rw [hf t (List.Mem.head _)] at hval
          exact Bool.noConfusion hval
      | tail _ hd' => exact ⟨d, List.Mem.tail _ hd', hne, hval⟩

  -- ⭐ EL CASO NUEVO: el corte contra un axioma de la igualdad LO RECOGE
  | eqAx Γ Δ g hg _ ih =>
      intro hqΓ hqΔ
      obtain ⟨ts, E, hE, hts⟩ := ih
        (fun x hx => by
          cases hx with
          | head => exact quantFree_of_eqInstance hg
          | tail _ h' => exact hqΓ x h')
        hqΔ
      refine ⟨ts, g :: E, ?_, fun v hv hEv hf => ?_⟩
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
  | eqAx G D g hg _ ih => exact LKc.eqAx G D g hg ih


/-- ⬜ LA ÚNICA DEUDA QUE QUEDA: el HAUPTSATZ. -/
def CutElim : Prop := ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ

/-- La traducción ND → secuentes con corte. ⭐ Ya NO lleva `E`: las instancias de igualdad
las mete `eqAx` dentro de la derivación, y la extracción las recoge. -/
def NDtoLK : Prop := ∀ (Γ : List Formula) (f : Formula), Derives₂ Γ f → LKc Γ [f]

theorem herbrandExtraction_of (hcut : CutElim) (htr : NDtoLK) : HerbrandExtraction := by
  intro φ hqf hd
  have hlk : LKc [] [Formula.ex φ] :=
    htr [] (Formula.ex φ) (FOL.Derives2.derives0_iff_derives2.mp hd)
  have hlk0 : LK₀ [] [Formula.ex φ] := hcut _ _ hlk
  obtain ⟨ts, E, hE, hts⟩ := lk0_herbrand (φ := φ) hqf hlk0
    (fun g hg => absurd hg List.not_mem_nil)
    (fun d hd2 => by
      cases hd2 with
      | head => exact Or.inr rfl
      | tail _ h2 => exact absurd h2 List.not_mem_nil)
  refine ⟨ts, E, hE, fun v hv => ?_⟩
  cases disj_or_allFalse v φ ts with
  | inl hok => exact hok
  | inr hall =>
      obtain ⟨d, hdmem, hdne, _⟩ := hts v (fun g hg => absurd hg List.not_mem_nil) hv hall
      cases hdmem with
      | head => exact absurd rfl hdne
      | tail _ h2 => exact absurd h2 List.not_mem_nil

end FOL.Sequent0

#print axioms LK₀.rec
#print axioms FOL.Sequent0.lk0_herbrand
#print axioms FOL.Sequent0.lk0_to_lkc
#print axioms FOL.Sequent0.herbrandExtraction_of
