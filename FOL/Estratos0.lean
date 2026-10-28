/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Inconsistencia, FOL.Canonical0, FOL.Derives2, FOL.SequentSound0, FOL.NDtoLK0,
--   FOL.Hauptsatz0, FOL.Interpolation0
-- @axiom_system: classical
-- @importance: medium

import FOL.Inconsistencia
import FOL.Canonical0
import FOL.Derives2
import FOL.SequentSound0
import FOL.NDtoLK0
import FOL.Hauptsatz0
import FOL.Interpolation0
import FOL.Calculus.DerivesI

/-!
# `FOL.Estratos0` — la solidez y la completitud de CADA cálculo de FOL, por sus puentes (T46, ADR‑194 de RPP)

FOL tiene ocho nociones de derivabilidad (el censo de estratos, `check-estratos.bash` de RPP, y REFERENCE §0bis de
RPP), y hasta el 2026‑10‑27 sólo `Derives₀` tenía una completitud con nombre; `LK₀` y `LKc` tenían su solidez en el
build sin que el censo la contara, y `LKp` no estaba censado. Este módulo‑HOJA (nadie lo importa salvo el barril; no
está congelado) pone, para cada cálculo, su solidez y su completitud con nombre, cada una en UNA línea: la composición
de la solidez o la completitud de `Derives₀` con los puentes que ya estaban demostrados.

| cálculo | solidez | completitud | puente |
|---|---|---|---|
| `Derives` (`⊢`) | `derives_soundness` (`FOL.Inconsistencia`) | `derives_semantic_complete` | `derives_to_derives0` · `derives0_to_derives` |
| `Derives₁` | `derives1_soundness` | `derives1_complete` | `derives1_to_derives0` · `derives0_to_derives1` |
| `Derives₂` | `derives2_soundness` | `derives2_complete` | `derives2_to_derives1` · `derives1_to_derives2` |
| `LKc` | `lkc_sound` (`FOL.SequentSound0`) | `lkc_complete` | `ndToLK` (desde `Derives₂`) |
| `LK₀` | `lk0_sound` (`FOL.SequentSound0`) | `lk0_complete` | `cut_elimination₀` (desde `LKc`) |
| `LKh` | `lkh_sound` | `lkh_complete` (con su altura) | `lkh_to_lk0` · `lk0_to_lkh` |
| `LKp` | `lkp_sound` | `lkp_complete` (con las instancias de igualdad delante) | `lkp_to_lk0` · `lk0_to_lkp` |

⚠️ **Lo que NO dice.** La completitud pasa por `completeness₀`, y con ella por su `Classical.choice` (esencial como
hipótesis: Markov; `AXIOMS.md` §4.2): las siete completitudes lo llevan. Las solideces de `Derives₁`, `Derives₂`,
`LKh` y `LKp` pasan por `derives0_soundness` o `lkc_sound`, que también lo llevan (esenciales: la semántica de Tarski
en `Prop`). Son corolarios, no pruebas nuevas: la vía sin choice, donde la hay, está en `FOL.Finitary0`. ✏️ 2026‑10‑28
(R3‑4‑03 de la ronda 3, ADR‑213 de RPP): decía «de RUTA»; no lo son en el sentido de `AXIOMS.md` §4.3 (con variante sin
choice medida): las cuatro solideces tienen un enunciado que implica un principio clásico (E1 de `FOL.Esencialidad0`).
`LKp` es completo sólo con las instancias de igualdad que usa puestas delante del antecedente (`lk0_to_lkp`): no tiene
regla de igualdad, y ésa es su forma de completitud.
-/

namespace FOL.Estratos0

open FOL.Metamath.Semantics FOL.Sequent0 FOL.Hauptsatz0 FOL.Craig0 FOL.Interpolation0

-- ── las nociones de deducción natural: `Derives`, `Derives₁`, `Derives₂` ──────────────────────────────────────

/-- `Derives` (`⊢`) es completo: lo válido se deriva en `Derives₀`, y `Derives₀` está dentro de `Derives`. -/
theorem derives_semantic_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : Γ ⊢ f :=
  derives0_to_derives (FOL.Canonical0.completeness₀ h)

/-- `Derivesᵢ` (`⊢ᵢ`, el intuicionista de X1, `FOL/Calculus/DerivesI.lean`; T51, ADR‑218 de RPP) es sólido para la
semántica de Tarski: está dentro de `Derives₀`. (Su completitud no la tiene: con esta semántica es falsa —el tercero
excluido es válido y `⊢ᵢ` no lo deriva, `FOL.Calculus.derivesI_ne_derives0`—.) -/
theorem derivesI_soundness {Γ : List Formula} {f : Formula} (h : FOL.Calculus.Derivesᵢ Γ f) : satisfies Γ f :=
  FOL.Metamath.Soundness0.derives0_soundness (FOL.Calculus.derivesI_to_derives0 h)

theorem derives1_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢₁ f) : satisfies Γ f :=
  FOL.Metamath.Soundness0.derives0_soundness (FOL.Derives1.derives1_to_derives0 h)

theorem derives1_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : Γ ⊢₁ f :=
  FOL.Derives1.derives0_to_derives1 (FOL.Canonical0.completeness₀ h)

theorem derives2_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢₂ f) : satisfies Γ f :=
  derives1_soundness (FOL.Derives2.derives2_to_derives1 h)

theorem derives2_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : Γ ⊢₂ f :=
  FOL.Derives2.derives1_to_derives2 (derives1_complete h)

-- ── los secuentes: `LKc`, `LK₀`, `LKh`, `LKp` ─────────────────────────────────────────────────────────────────

/-- `LKc` es completo (en un secuente de una sola conclusión): lo válido se deriva en `Derives₂`, y `ndToLK` lo
lleva a `LKc`. -/
theorem lkc_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : LKc Γ [f] :=
  FOL.NDtoLK0.ndToLK (derives2_complete h)

/-- `LK₀` es completo: el de `LKc`, sin el corte (`cut_elimination₀`). -/
theorem lk0_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : LK₀ Γ [f] :=
  cut_elimination₀ _ _ (lkc_complete h)

theorem lkh_sound {n : Nat} {Γ Δ : List Formula} (h : LKh n Γ Δ) :
    ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d) :=
  FOL.SequentSound0.lk0_sound (lkh_to_lk0 h)

/-- `LKh` es completo, con la altura de la derivación como testigo. -/
theorem lkh_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) : ∃ n, LKh n Γ [f] :=
  lk0_to_lkh (lk0_complete h)

theorem lkp_sound {Γ Δ : List Formula} (h : LKp Γ Δ) :
    ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d) :=
  FOL.SequentSound0.lk0_sound (lkp_to_lk0 h)

/-- `LKp` es completo con las instancias de igualdad que usa —cerradas con `∀`— delante del antecedente: no tiene
regla de igualdad (`lk0_to_lkp`). -/
theorem lkp_complete {Γ : List Formula} {f : Formula} (h : satisfies Γ f) :
    ∃ E : List Formula, And (∀ e, e ∈ E → EqGen e) (LKp (E ++ Γ) [f]) :=
  lk0_to_lkp (lk0_complete h)

end FOL.Estratos0

#print axioms FOL.Estratos0.derives_semantic_complete
#print axioms FOL.Estratos0.derivesI_soundness
#print axioms FOL.Estratos0.derives1_soundness
#print axioms FOL.Estratos0.derives1_complete
#print axioms FOL.Estratos0.derives2_soundness
#print axioms FOL.Estratos0.derives2_complete
#print axioms FOL.Estratos0.lkc_complete
#print axioms FOL.Estratos0.lk0_complete
#print axioms FOL.Estratos0.lkh_sound
#print axioms FOL.Estratos0.lkh_complete
#print axioms FOL.Estratos0.lkp_sound
#print axioms FOL.Estratos0.lkp_complete
