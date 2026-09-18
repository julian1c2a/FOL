/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Sequent0, FOL.Lift0
-- @axiom_system: classical
-- @importance: high

import FOL.Sequent0
import FOL.Lift0

/-!
# `FOL.Craig0` — 🏁 el lema de MAEHARA y la INTERPOLACIÓN DE CRAIG para `LKp`

    LKp                     -- el fragmento PURO: `LK₀` sin `eqAx` (13 constructores: los 14 de LK0 menos eqAx)
    maehara : LKp Γ Δ → ∀ particiones, ∃ C interpolante con su condición de lenguaje
    craig   : LKp [A] [B] → ∃ C, LKp [A] [C] ∧ LKp [C] [B] ∧ PredSub C [A] ∧ PredSub C [B]

📏 **`[propext, Quot.sound]` en todo el módulo: ni un `Classical.choice`, ni un axioma del
proyecto.** `lkp_to_lk0`, `predF_lift` y `predF_subst`, **sin ningún axioma**.

## ⛔ Por qué `LKp` y no `LK₀` — la obstrucción, que está CONFIRMADA

`LK₀.eqAx` mete en el antécedente una instancia de igualdad `g` **arbitraria**: sus símbolos no
tienen por qué estar en el secuente. Las derivaciones del paso sí salen —basta meter `g` siempre
en el lado 1— pero la **condición de lenguaje** se rompe, porque el interpolante puede heredar
símbolos de `g`. ⇒ lo entregable es la interpolación para un cálculo **distinto**, `LKp`, que
**no es el que el proyecto usa** (ADR‑056 §1 ya lo dejó medido; esto es su «Nivel 1»).

## ⛔⛔ Y la condición va sobre los símbolos de RELACIÓN, no sobre los de FUNCIÓN

Con los símbolos de función dentro, el paso `allL` de Maehara es **FALSO**. Contraejemplo mínimo,
desarrollado a mano y después comprobado:

    ∀x P(x)  ⊢  P(f(c))          -- por `allL` con t = f(c), y arriba `ax`

La premisa es `P(f(c)), ∀xP(x) ⊢ P(f(c))`, cuyo interpolante (caso `ax`, izquierda‑derecha) es
`P(f(c))`; pero tras la regla el lado 1 sólo tiene `∀xP(x)`, cuyos símbolos son `{P}`. El
interpolante mete `f` y `c` ⇒ la condición se rompe.
⭐ Y el teorema **no** es falso: el interpolante correcto es `∀xP(x)`. Lo falso es el PASO ingenuo.

⇒ `predF` cuenta **sólo predicados**, que es como Craig se enuncia en la mayoría de los textos.
Y entonces los dos lemas que los cuatro casos de cuantificador necesitan —`predF_lift` y
`predF_subst`— son **triviales y net‑0**, porque levantar y sustituir sólo tocan **términos**.
🔑 *La condición que hace demostrable un teorema no siempre es la que uno escribiría primero: aquí
la correcta se descubre desarrollando el caso que falla, no leyendo el enunciado.*

## ⭐⭐ La partición va por PERTENENCIA, y es lo que hace posible el análisis de casos

    def Split (Γ Γ₁ Γ₂ : List Formula) : Prop := ∀ x, x ∈ Γ → Or (x ∈ Γ₁) (x ∈ Γ₂)

Con `Γ = Γ₁ ++ Γ₂` el análisis de casos es **imposible**: cada regla pone la fórmula principal en
la CABEZA, y de `Γ₁ ++ Γ₂ = A :: Γ'` no se sigue en cuál de los dos cayó `A`. Por pertenencia, en
cambio, basta preguntarle a la hipótesis dónde fue la fórmula principal — dos casos por regla.
⭐ Lo que lo autoriza es `struct`: reordena, contrae y debilita **por pertenencia**, así que el
secuente se comporta como un CONJUNTO. Y es también lo que permite **absorber** la fórmula
principal al final de cada caso (`sub_drop`), que es el paso que cierra los 26.

## ⭐⭐⭐ Los cuatro casos de eigenvariable NO necesitan des‑levantar nada

En `allR`/`exL` el interpolante de la hipótesis de inducción vive en el mundo LEVANTADO
(`Γ.map (liftFormula 0)`). La ruta obvia pide des‑levantar una derivación, que en `LK₀` sólo se
tiene vía `lk0_subst` — y ése pasa por `LKh` y por `lkh_subst`, **la pieza cara de ADR‑051**: para
`LKp` habría que reprobarla entera.

No hace falta. El interpolante se **cuantifica con el mismo binder que la regla introduce**, y
entonces las dos mitades salen de los CONSTRUCTORES más `substFormula_lift_var`:

| regla | lado 1 | interpolante | cómo sale |
|---|---|---|---|
| `allR` | `∀A ∈ Δ₁` | `∃C` | `exR` con `t = x₀`, reordenar, `allR` |
| `allR` | `∀A ∈ Δ₂` | `∀C` | `allR` directo / `allL` con `t = x₀` + `allR` |
| `exL` | `∃A ∈ Γ₁` | `∃C` | `exR` con `t = x₀` + `exL` |
| `exL` | `∃A ∈ Γ₂` | `∀C` | `allL` con `t = x₀`, reordenar, `exL` |

🔑 *La condición de eigenvariable es GRATIS en De Bruijn: el contexto llega literalmente como
`Γ.map lift`, y eso ES la frescura.*

## ⚠️ Lo que este módulo NO da

* ⛔ **No hay puente HACIA `LKp`.** `ndToLK` produce `LK₀` y usa `eqAx`; para consumir `craig` hay
  que exhibir una derivación de `LKp` a mano. ⬜ No medido.
* ⛔ **No es interpolación para FOLᐟ.** `LKp` no tiene los axiomas de la igualdad.
* ⚠️ **No incluye la condición sobre VARIABLES LIBRES** de la interpolación de Craig clásica, sólo
  la de símbolos de relación. Para **sentencias** (fórmulas cerradas) esa condición es vacua y el
  enunciado de aquí es el completo; para fórmulas abiertas, es estrictamente más débil, y se dice.
* ⚠️ `Formula.eq` se cuenta como símbolo **lógico** (no aporta predicado). En `LKp` no hay `eqAx`,
  así que `=` no tiene axiomas; contarlo fuera **debilita** el enunciado, no lo falsea.
-/

namespace FOL.Craig0

open FOL.Sequent0

-- ══════════════════════════════════════════════════════════════════════════
-- §1 · LKp, el fragmento PURO
-- ══════════════════════════════════════════════════════════════════════════

inductive LKp : List Formula → List Formula → Prop where
  | ax : ∀ Γ Δ A, A ∈ Γ → A ∈ Δ → LKp Γ Δ
  | botL : ∀ Γ Δ, Formula.bottom ∈ Γ → LKp Γ Δ
  | struct : ∀ Γ Γ' Δ Δ', LKp Γ Δ → (∀ x, x ∈ Γ → x ∈ Γ') → (∀ x, x ∈ Δ → x ∈ Δ') → LKp Γ' Δ'
  | implR : ∀ Γ Δ A B, LKp (A :: Γ) (B :: Δ) → LKp Γ (Formula.impl A B :: Δ)
  | implL : ∀ Γ Δ A B, LKp Γ (A :: Δ) → LKp (B :: Γ) Δ → LKp (Formula.impl A B :: Γ) Δ
  | andR : ∀ Γ Δ A B, LKp Γ (A :: Δ) → LKp Γ (B :: Δ) → LKp Γ (Formula.and A B :: Δ)
  | andL : ∀ Γ Δ A B, LKp (A :: B :: Γ) Δ → LKp (Formula.and A B :: Γ) Δ
  | orR : ∀ Γ Δ A B, LKp Γ (A :: B :: Δ) → LKp Γ (Formula.or A B :: Δ)
  | orL : ∀ Γ Δ A B, LKp (A :: Γ) Δ → LKp (B :: Γ) Δ → LKp (Formula.or A B :: Γ) Δ
  | allR : ∀ Γ Δ A, LKp (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) →
      LKp Γ (Formula.forall A :: Δ)
  | allL : ∀ Γ Δ A t, LKp (substFormula 0 t A :: Γ) Δ → LKp (Formula.forall A :: Γ) Δ
  | exR : ∀ Γ Δ A t, LKp Γ (substFormula 0 t A :: Δ) → LKp Γ (Formula.ex A :: Δ)
  | exL : ∀ Γ Δ A, LKp (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) →
      LKp (Formula.ex A :: Γ) Δ

theorem lkp_to_lk0 : ∀ {Γ Δ : List Formula}, LKp Γ Δ → LK₀ Γ Δ := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A h1 h2 => exact LK₀.ax Γ Δ A h1 h2
  | botL Γ Δ h => exact LK₀.botL Γ Δ h
  | struct Γ Γ' Δ Δ' _ h1 h2 ih => exact LK₀.struct Γ Γ' Δ Δ' ih h1 h2
  | implR Γ Δ A B _ ih => exact LK₀.implR Γ Δ A B ih
  | implL Γ Δ A B _ _ ih1 ih2 => exact LK₀.implL Γ Δ A B ih1 ih2
  | andR Γ Δ A B _ _ ih1 ih2 => exact LK₀.andR Γ Δ A B ih1 ih2
  | andL Γ Δ A B _ ih => exact LK₀.andL Γ Δ A B ih
  | orR Γ Δ A B _ ih => exact LK₀.orR Γ Δ A B ih
  | orL Γ Δ A B _ _ ih1 ih2 => exact LK₀.orL Γ Δ A B ih1 ih2
  | allR Γ Δ A _ ih => exact LK₀.allR Γ Δ A ih
  | allL Γ Δ A t _ ih => exact LK₀.allL Γ Δ A t ih
  | exR Γ Δ A t _ ih => exact LK₀.exR Γ Δ A t ih
  | exL Γ Δ A _ ih => exact LK₀.exL Γ Δ A ih

-- ══════════════════════════════════════════════════════════════════════════
-- §2 · auxiliares de listas y de PARTICIÓN
-- ══════════════════════════════════════════════════════════════════════════

theorem sub_refl (Γ : List Formula) : ∀ x, x ∈ Γ → x ∈ Γ := fun _ h => h

theorem sub_wk {Γ Γ' : List Formula} (b : Formula) (h : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ Γ → x ∈ b :: Γ' := fun x hx => List.Mem.tail _ (h x hx)

theorem sub_cons {Γ Γ' : List Formula} (b : Formula) (h : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ b :: Γ → x ∈ b :: Γ' := by
  intro x hx
  cases hx with
  | head => exact List.Mem.head _
  | tail _ hm => exact List.Mem.tail _ (h x hm)

theorem sub_drop {Δ : List Formula} {b : Formula} (h : b ∈ Δ) : ∀ x, x ∈ b :: Δ → x ∈ Δ := by
  intro x hx
  cases hx with
  | head => exact h
  | tail _ hm => exact hm

theorem swap_cons (a b : Formula) (Γ : List Formula) : ∀ x, x ∈ a :: b :: Γ → x ∈ b :: a :: Γ := by
  intro x hx
  cases hx with
  | head => exact List.Mem.tail _ (List.Mem.head _)
  | tail _ hm =>
      cases hm with
      | head => exact List.Mem.head _
      | tail _ hm2 => exact List.Mem.tail _ (List.Mem.tail _ hm2)

/-- La partición se da POR PERTENENCIA, no por concatenación: como `struct` reordena, contrae y
debilita por pertenencia, el secuente se comporta como un CONJUNTO. ⭐ Es lo que permite el
análisis de casos cuando la regla pone la fórmula principal en la CABEZA. -/
def Split (Γ Γ₁ Γ₂ : List Formula) : Prop := ∀ x, x ∈ Γ → Or (x ∈ Γ₁) (x ∈ Γ₂)

theorem split_consL {Γ Γ₁ Γ₂ : List Formula} (A : Formula) (h : Split Γ Γ₁ Γ₂) :
    Split (A :: Γ) (A :: Γ₁) Γ₂ := by
  intro x hx
  cases hx with
  | head => exact Or.inl (List.Mem.head _)
  | tail _ hm => exact (h x hm).elim (fun hh => Or.inl (List.Mem.tail _ hh)) Or.inr

theorem split_consR {Γ Γ₁ Γ₂ : List Formula} (A : Formula) (h : Split Γ Γ₁ Γ₂) :
    Split (A :: Γ) Γ₁ (A :: Γ₂) := by
  intro x hx
  cases hx with
  | head => exact Or.inr (List.Mem.head _)
  | tail _ hm => exact (h x hm).elim Or.inl (fun hh => Or.inr (List.Mem.tail _ hh))

theorem split_tail {Γ Γ₁ Γ₂ : List Formula} {A : Formula} (h : Split (A :: Γ) Γ₁ Γ₂) :
    Split Γ Γ₁ Γ₂ := fun x hx => h x (List.Mem.tail _ hx)

theorem split_map {Γ Γ₁ Γ₂ : List Formula} (k : Nat) (h : Split Γ Γ₁ Γ₂) :
    Split (Γ.map (liftFormula k)) (Γ₁.map (liftFormula k)) (Γ₂.map (liftFormula k)) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨g, hg, he⟩
  subst he
  exact (h g hg).elim
    (fun hh => Or.inl (List.mem_map_of_mem hh))
    (fun hh => Or.inr (List.mem_map_of_mem hh))

-- ══════════════════════════════════════════════════════════════════════════
-- §3 · los símbolos de RELACIÓN
-- ══════════════════════════════════════════════════════════════════════════

def predF (p : String) : Formula → Prop
  | .bottom => False
  | .atom q _ => q = p
  | .eq _ _ => False
  | .impl a b => Or (predF p a) (predF p b)
  | .and a b => Or (predF p a) (predF p b)
  | .or a b => Or (predF p a) (predF p b)
  | .forall a => predF p a
  | .ex a => predF p a

theorem predF_lift (p : String) : ∀ (f : Formula) (k : Nat),
    Iff (predF p (liftFormula k f)) (predF p f)
  | .bottom, _ => Iff.rfl
  | .atom _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .impl a b, k => or_congr (predF_lift p a k) (predF_lift p b k)
  | .and a b, k => or_congr (predF_lift p a k) (predF_lift p b k)
  | .or a b, k => or_congr (predF_lift p a k) (predF_lift p b k)
  | .forall a, k => predF_lift p a (k + 1)
  | .ex a, k => predF_lift p a (k + 1)

theorem predF_subst (p : String) : ∀ (f : Formula) (k : Nat) (t : Term),
    Iff (predF p (substFormula k t f)) (predF p f)
  | .bottom, _, _ => Iff.rfl
  | .atom _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .impl a b, k, t => or_congr (predF_subst p a k t) (predF_subst p b k t)
  | .and a b, k, t => or_congr (predF_subst p a k t) (predF_subst p b k t)
  | .or a b, k, t => or_congr (predF_subst p a k t) (predF_subst p b k t)
  | .forall a, k, t => predF_subst p a (k + 1) (liftTerm 0 t)
  | .ex a, k, t => predF_subst p a (k + 1) (liftTerm 0 t)

-- ⚠️ Trampa §12: `∧` se parsea como `Formula.and`. Va `And` de Lean, explícito.
def PredSub (C : Formula) (L : List Formula) : Prop :=
  ∀ p, predF p C → ∃ g, And (g ∈ L) (predF p g)

/-- `Cov L L'`: todo símbolo de relación de `L` está ya en `L'`. Es el combinador con el que se
descarga la condición de Craig en cada caso. -/
def Cov (L L' : List Formula) : Prop :=
  ∀ g, g ∈ L → ∀ p, predF p g → ∃ g', And (g' ∈ L') (predF p g')

theorem predSub_of_cov {C : Formula} {L L' : List Formula}
    (h : PredSub C L) (hc : Cov L L') : PredSub C L' := by
  intro p hp
  obtain ⟨g, hg, hpg⟩ := h p hp
  exact hc g hg p hpg

theorem cov_sub {L L' : List Formula} (hs : ∀ x, x ∈ L → x ∈ L') : Cov L L' :=
  fun g hg _ hp => ⟨g, hs g hg, hp⟩

theorem cov_append {L₁ L₂ L : List Formula} (h₁ : Cov L₁ L) (h₂ : Cov L₂ L) :
    Cov (L₁ ++ L₂) L := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h₁ g h
  · exact h₂ g h

theorem cov_cons {A : Formula} {L L' : List Formula}
    (hA : ∀ p, predF p A → ∃ g', And (g' ∈ L') (predF p g')) (hL : Cov L L') :
    Cov (A :: L) L' := by
  intro g hg
  cases hg with
  | head => exact hA
  | tail _ hm => exact hL g hm

/-- ⭐ El levantamiento no mueve predicados: por eso los casos de eigenvariable no cuestan nada
en el recuento. -/
theorem cov_unlift {L L' : List Formula} (k : Nat) (hs : ∀ x, x ∈ L → x ∈ L') :
    Cov (L.map (liftFormula k)) L' := by
  intro g hg p hp
  rcases List.mem_map.mp hg with ⟨g0, hg0, he⟩
  subst he
  exact ⟨g0, hs g0 hg0, (predF_lift p g0 k).mp hp⟩

/-- Un miembro que cubre a otro: `A` está cubierta por `g ∈ L'` si todo predicado de `A` lo es. -/
theorem cov_one {A : Formula} {L' : List Formula} {g : Formula}
    (hg : g ∈ L') (h : ∀ p, predF p A → predF p g) :
    ∀ p, predF p A → ∃ g', And (g' ∈ L') (predF p g') := fun p hp => ⟨g, hg, h p hp⟩

theorem cov_nil {L' : List Formula} : Cov [] L' := by
  intro g hg
  exact absurd hg (List.not_mem_nil)


theorem sub_rot3 (a b c : Formula) (Γ : List Formula) :
    ∀ x, x ∈ a :: b :: c :: Γ → x ∈ b :: c :: a :: Γ := by
  intro x hx
  cases hx with
  | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | tail _ h1 =>
      cases h1 with
      | head => exact List.Mem.head _
      | tail _ h2 =>
          cases h2 with
          | head => exact List.Mem.tail _ (List.Mem.head _)
          | tail _ h3 => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ h3))

theorem sub_rot3' (a b c : Formula) (Γ : List Formula) :
    ∀ x, x ∈ a :: b :: c :: Γ → x ∈ c :: a :: b :: Γ := by
  intro x hx
  cases hx with
  | head => exact List.Mem.tail _ (List.Mem.head _)
  | tail _ h1 =>
      cases h1 with
      | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      | tail _ h2 =>
          cases h2 with
          | head => exact List.Mem.head _
          | tail _ h3 => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ h3))

-- ══════════════════════════════════════════════════════════════════════════
-- §4 · 🏁 EL LEMA DE MAEHARA
-- ══════════════════════════════════════════════════════════════════════════

theorem maehara : ∀ {Γ Δ : List Formula}, LKp Γ Δ →
    ∀ (Γ₁ Γ₂ Δ₁ Δ₂ : List Formula), Split Γ Γ₁ Γ₂ → Split Δ Δ₁ Δ₂ →
      ∃ C, And (LKp Γ₁ (C :: Δ₁)) (And (LKp (C :: Γ₂) Δ₂)
           (And (PredSub C (Γ₁ ++ Δ₁)) (PredSub C (Γ₂ ++ Δ₂)))) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A hA hA' =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ A hA with h1 | h1
      · rcases hΔ A hA' with h2 | h2
        · exact ⟨Formula.bottom, LKp.ax _ _ A h1 (List.Mem.tail _ h2),
            LKp.botL _ _ (List.Mem.head _), fun _ hp => hp.elim, fun _ hp => hp.elim⟩
        · exact ⟨A, LKp.ax _ _ A h1 (List.Mem.head _), LKp.ax _ _ A (List.Mem.head _) h2,
            fun p hp => ⟨A, List.mem_append.mpr (Or.inl h1), hp⟩,
            fun p hp => ⟨A, List.mem_append.mpr (Or.inr h2), hp⟩⟩
      · rcases hΔ A hA' with h2 | h2
        · refine ⟨neg A, ?_, ?_, ?_, ?_⟩
          · exact LKp.implR _ _ A Formula.bottom
              (LKp.ax _ _ A (List.Mem.head _) (List.Mem.tail _ h2))
          · exact LKp.implL _ _ A Formula.bottom
              (LKp.ax _ _ A h1 (List.Mem.head _)) (LKp.botL _ _ (List.Mem.head _))
          · intro p hp
            exact ⟨A, List.mem_append.mpr (Or.inr h2), hp.elim (fun x => x) (fun c => c.elim)⟩
          · intro p hp
            exact ⟨A, List.mem_append.mpr (Or.inl h1), hp.elim (fun x => x) (fun c => c.elim)⟩
        · refine ⟨top, ?_, LKp.ax _ _ A (List.Mem.tail _ h1) h2, ?_, ?_⟩
          · exact LKp.implR _ _ Formula.bottom Formula.bottom (LKp.botL _ _ (List.Mem.head _))
          · intro _ hp; exact hp.elim (fun c => c.elim) (fun c => c.elim)
          · intro _ hp; exact hp.elim (fun c => c.elim) (fun c => c.elim)
  | botL Γ Δ hb =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ _
      rcases hΓ Formula.bottom hb with h1 | h1
      · exact ⟨Formula.bottom, LKp.botL _ _ h1, LKp.botL _ _ (List.Mem.head _),
          fun _ hp => hp.elim, fun _ hp => hp.elim⟩
      · refine ⟨top, LKp.implR _ _ Formula.bottom Formula.bottom
            (LKp.botL _ _ (List.Mem.head _)), LKp.botL _ _ (List.Mem.tail _ h1), ?_, ?_⟩
        · intro _ hp; exact hp.elim (fun c => c.elim) (fun c => c.elim)
        · intro _ hp; exact hp.elim (fun c => c.elim) (fun c => c.elim)
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      exact ih Γ₁ Γ₂ Δ₁ Δ₂ (fun x hx => hΓ x (hsΓ x hx)) (fun x hx => hΔ x (hsΔ x hx))
  | implR Γ Δ A B _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΔ (Formula.impl A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (A :: Γ₁) Γ₂ (B :: Δ₁) Δ₂ (split_consL A hΓ) (split_consL B (split_tail hΔ))
        refine ⟨C, ?_, hC2, ?_, hS2⟩
        · have h1 : LKp (A :: Γ₁) (B :: C :: Δ₁) :=
            LKp.struct _ _ _ _ hC1 (sub_refl _) (swap_cons C B Δ₁)
          have h2 : LKp Γ₁ (Formula.impl A B :: C :: Δ₁) := LKp.implR Γ₁ (C :: Δ₁) A B h1
          exact LKp.struct _ _ _ _ h2 (sub_refl _) (sub_drop (List.Mem.tail _ hpr))
        · refine predSub_of_cov hS1 (cov_append ?_ ?_)
          · exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inl hp))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
          · exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inr hp))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ (A :: Γ₂) Δ₁ (B :: Δ₂) (split_consR A hΓ) (split_consR B (split_tail hΔ))
        refine ⟨C, hC1, ?_, hS1, ?_⟩
        · have h1 : LKp (A :: C :: Γ₂) (B :: Δ₂) :=
            LKp.struct _ _ _ _ hC2 (swap_cons C A Γ₂) (sub_refl _)
          have h2 : LKp (C :: Γ₂) (Formula.impl A B :: Δ₂) := LKp.implR (C :: Γ₂) Δ₂ A B h1
          exact LKp.struct _ _ _ _ h2 (sub_refl _) (sub_drop hpr)
        · refine predSub_of_cov hS2 (cov_append ?_ ?_)
          · exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inl hp))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
          · exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inr hp))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))
  | andL Γ Δ A B _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ (Formula.and A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (A :: B :: Γ₁) Γ₂ Δ₁ Δ₂ (split_consL A (split_consL B (split_tail hΓ))) hΔ
        refine ⟨C, ?_, hC2, ?_, hS2⟩
        · have h2 : LKp (Formula.and A B :: Γ₁) (C :: Δ₁) := LKp.andL Γ₁ (C :: Δ₁) A B hC1
          exact LKp.struct _ _ _ _ h2 (sub_drop hpr) (sub_refl _)
        · refine predSub_of_cov hS1 (cov_append ?_ (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))
          refine cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hp => Or.inl hp)) ?_
          exact cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hp => Or.inr hp))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ (A :: B :: Γ₂) Δ₁ Δ₂ (split_consR A (split_consR B (split_tail hΓ))) hΔ
        refine ⟨C, hC1, ?_, hS1, ?_⟩
        · have h1 : LKp (A :: B :: C :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ hC2 (sub_rot3 C A B Γ₂) (sub_refl _)
          have h2 : LKp (Formula.and A B :: C :: Γ₂) Δ₂ := LKp.andL (C :: Γ₂) Δ₂ A B h1
          exact LKp.struct _ _ _ _ h2 (sub_drop (List.Mem.tail _ hpr)) (sub_refl _)
        · refine predSub_of_cov hS2 (cov_append ?_ (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))
          refine cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hp => Or.inl hp)) ?_
          exact cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hp => Or.inr hp))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
  | orR Γ Δ A B _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΔ (Formula.or A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ Γ₂ (A :: B :: Δ₁) Δ₂ hΓ (split_consL A (split_consL B (split_tail hΔ)))
        refine ⟨C, ?_, hC2, ?_, hS2⟩
        · have h1 : LKp Γ₁ (A :: B :: C :: Δ₁) :=
            LKp.struct _ _ _ _ hC1 (sub_refl _) (sub_rot3 C A B Δ₁)
          have h2 : LKp Γ₁ (Formula.or A B :: C :: Δ₁) := LKp.orR Γ₁ (C :: Δ₁) A B h1
          exact LKp.struct _ _ _ _ h2 (sub_refl _) (sub_drop (List.Mem.tail _ hpr))
        · refine predSub_of_cov hS1 (cov_append (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))) ?_)
          refine cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inl hp)) ?_
          exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inr hp))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ Γ₂ Δ₁ (A :: B :: Δ₂) hΓ (split_consR A (split_consR B (split_tail hΔ)))
        refine ⟨C, hC1, ?_, hS1, ?_⟩
        · have h2 : LKp (C :: Γ₂) (Formula.or A B :: Δ₂) := LKp.orR (C :: Γ₂) Δ₂ A B hC2
          exact LKp.struct _ _ _ _ h2 (sub_refl _) (sub_drop hpr)
        · refine predSub_of_cov hS2 (cov_append (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))) ?_)
          refine cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inl hp)) ?_
          exact cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hp => Or.inr hp))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΔ (Formula.and A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 Γ₁ Γ₂ (A :: Δ₁) Δ₂ hΓ (split_consL A (split_tail hΔ))
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 Γ₁ Γ₂ (B :: Δ₁) Δ₂ hΓ (split_consL B (split_tail hΔ))
        refine ⟨Formula.or C1 C2, ?_, LKp.orL Γ₂ Δ₂ C1 C2 hA2 hB2, ?_, ?_⟩
        · have e1 : LKp Γ₁ (C1 :: C2 :: A :: Δ₁) :=
            LKp.struct _ _ _ _ hA1 (sub_refl _) (by
              intro x hx
              cases hx with
              | head => exact List.Mem.head _
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm))
          have e1'' : LKp Γ₁ (A :: Formula.or C1 C2 :: Δ₁) :=
            LKp.struct _ _ _ _ (LKp.orR Γ₁ (A :: Δ₁) C1 C2 e1) (sub_refl _) (swap_cons _ _ _)
          have e2 : LKp Γ₁ (C1 :: C2 :: B :: Δ₁) :=
            LKp.struct _ _ _ _ hB1 (sub_refl _) (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.head _)
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm))
          have e2'' : LKp Γ₁ (B :: Formula.or C1 C2 :: Δ₁) :=
            LKp.struct _ _ _ _ (LKp.orR Γ₁ (B :: Δ₁) C1 C2 e2) (sub_refl _) (swap_cons _ _ _)
          exact LKp.struct _ _ _ _ (LKp.andR Γ₁ (Formula.or C1 C2 :: Δ₁) A B e1'' e2'')
            (sub_refl _) (sub_drop (List.Mem.tail _ hpr))
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS1 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
          · exact predSub_of_cov hBS1 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
        · intro p hp
          rcases hp with hq | hq
          · exact hAS2 p hq
          · exact hBS2 p hq
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 Γ₁ Γ₂ Δ₁ (A :: Δ₂) hΓ (split_consR A (split_tail hΔ))
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 Γ₁ Γ₂ Δ₁ (B :: Δ₂) hΓ (split_consR B (split_tail hΔ))
        refine ⟨Formula.and C1 C2, LKp.andR Γ₁ Δ₁ C1 C2 hA1 hB1, ?_, ?_, ?_⟩
        · have e1 : LKp (C1 :: C2 :: Γ₂) (A :: Δ₂) :=
            LKp.struct _ _ _ _ hA2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.head _
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)) (sub_refl _)
          have e2 : LKp (C1 :: C2 :: Γ₂) (B :: Δ₂) :=
            LKp.struct _ _ _ _ hB2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.head _)
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)) (sub_refl _)
          have e3 : LKp (C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ (LKp.andR (C1 :: C2 :: Γ₂) Δ₂ A B e1 e2)
              (sub_refl _) (sub_drop hpr)
          exact LKp.andL Γ₂ Δ₂ C1 C2 e3
        · intro p hp
          rcases hp with hq | hq
          · exact hAS1 p hq
          · exact hBS1 p hq
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS2 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
          · exact predSub_of_cov hBS2 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ (Formula.or A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 (A :: Γ₁) Γ₂ Δ₁ Δ₂ (split_consL A (split_tail hΓ)) hΔ
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 (B :: Γ₁) Γ₂ Δ₁ Δ₂ (split_consL B (split_tail hΓ)) hΔ
        refine ⟨Formula.or C1 C2, ?_, LKp.orL Γ₂ Δ₂ C1 C2 hA2 hB2, ?_, ?_⟩
        · have e1 : LKp (A :: Γ₁) (Formula.or C1 C2 :: Δ₁) :=
            LKp.orR (A :: Γ₁) Δ₁ C1 C2 (LKp.struct _ _ _ _ hA1 (sub_refl _) (by
              intro x hx
              cases hx with
              | head => exact List.Mem.head _
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)))
          have e2 : LKp (B :: Γ₁) (Formula.or C1 C2 :: Δ₁) :=
            LKp.orR (B :: Γ₁) Δ₁ C1 C2 (LKp.struct _ _ _ _ hB1 (sub_refl _) (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.head _)
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)))
          exact LKp.struct _ _ _ _ (LKp.orL Γ₁ (Formula.or C1 C2 :: Δ₁) A B e1 e2)
            (sub_drop hpr) (sub_refl _)
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS1 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
          · exact predSub_of_cov hBS1 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
        · intro p hp
          rcases hp with hq | hq
          · exact hAS2 p hq
          · exact hBS2 p hq
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 Γ₁ (A :: Γ₂) Δ₁ Δ₂ (split_consR A (split_tail hΓ)) hΔ
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 Γ₁ (B :: Γ₂) Δ₁ Δ₂ (split_consR B (split_tail hΓ)) hΔ
        refine ⟨Formula.and C1 C2, LKp.andR Γ₁ Δ₁ C1 C2 hA1 hB1, ?_, ?_, ?_⟩
        · have e1 : LKp (A :: C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ hA2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.head _)
              | tail _ hm =>
                  cases hm with
                  | head => exact List.Mem.head _
                  | tail _ hm2 => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hm2)))
              (sub_refl _)
          have e2 : LKp (B :: C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ hB2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
              | tail _ hm =>
                  cases hm with
                  | head => exact List.Mem.head _
                  | tail _ hm2 => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hm2)))
              (sub_refl _)
          have e3 : LKp (C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ (LKp.orL (C1 :: C2 :: Γ₂) Δ₂ A B e1 e2)
              (sub_drop (List.Mem.tail _ (List.Mem.tail _ hpr))) (sub_refl _)
          exact LKp.andL Γ₂ Δ₂ C1 C2 e3
        · intro p hp
          rcases hp with hq | hq
          · exact hAS1 p hq
          · exact hBS1 p hq
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS2 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
          · exact predSub_of_cov hBS2 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ (Formula.impl A B) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 Γ₁ Γ₂ (A :: Δ₁) Δ₂ (split_tail hΓ) (split_consL A hΔ)
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 (B :: Γ₁) Γ₂ Δ₁ Δ₂ (split_consL B (split_tail hΓ)) hΔ
        refine ⟨Formula.or C1 C2, ?_, LKp.orL Γ₂ Δ₂ C1 C2 hA2 hB2, ?_, ?_⟩
        · have e1 : LKp Γ₁ (A :: Formula.or C1 C2 :: Δ₁) :=
            LKp.struct _ _ _ _
              (LKp.orR Γ₁ (A :: Δ₁) C1 C2 (LKp.struct _ _ _ _ hA1 (sub_refl _) (by
                intro x hx
                cases hx with
                | head => exact List.Mem.head _
                | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm))))
              (sub_refl _) (swap_cons _ _ _)
          have e2 : LKp (B :: Γ₁) (Formula.or C1 C2 :: Δ₁) :=
            LKp.orR (B :: Γ₁) Δ₁ C1 C2 (LKp.struct _ _ _ _ hB1 (sub_refl _) (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.head _)
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)))
          exact LKp.struct _ _ _ _ (LKp.implL Γ₁ (Formula.or C1 C2 :: Δ₁) A B e1 e2)
            (sub_drop hpr) (sub_refl _)
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS1 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
          · exact predSub_of_cov hBS1 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
        · intro p hp
          rcases hp with hq | hq
          · exact hAS2 p hq
          · exact hBS2 p hq
      · obtain ⟨C1, hA1, hA2, hAS1, hAS2⟩ :=
          ih1 Γ₁ Γ₂ Δ₁ (A :: Δ₂) (split_tail hΓ) (split_consR A hΔ)
        obtain ⟨C2, hB1, hB2, hBS1, hBS2⟩ :=
          ih2 Γ₁ (B :: Γ₂) Δ₁ Δ₂ (split_consR B (split_tail hΓ)) hΔ
        refine ⟨Formula.and C1 C2, LKp.andR Γ₁ Δ₁ C1 C2 hA1 hB1, ?_, ?_, ?_⟩
        · have e1 : LKp (C1 :: C2 :: Γ₂) (A :: Δ₂) :=
            LKp.struct _ _ _ _ hA2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.head _
              | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ hm)) (sub_refl _)
          have e2 : LKp (B :: C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ hB2 (by
              intro x hx
              cases hx with
              | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
              | tail _ hm =>
                  cases hm with
                  | head => exact List.Mem.head _
                  | tail _ hm2 => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hm2)))
              (sub_refl _)
          have e3 : LKp (C1 :: C2 :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ (LKp.implL (C1 :: C2 :: Γ₂) Δ₂ A B e1 e2)
              (sub_drop (List.Mem.tail _ (List.Mem.tail _ hpr))) (sub_refl _)
          exact LKp.andL Γ₂ Δ₂ C1 C2 e3
        · intro p hp
          rcases hp with hq | hq
          · exact hAS1 p hq
          · exact hBS1 p hq
        · intro p hp
          rcases hp with hq | hq
          · exact predSub_of_cov hAS2 (cov_append
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inl hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))) p hq
          · exact predSub_of_cov hBS2 (cov_append
              (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => Or.inr hr))
                (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))) p hq
  | allR Γ Δ A _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΔ (Formula.forall A) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (Γ₁.map (liftFormula 0)) (Γ₂.map (liftFormula 0))
             (A :: Δ₁.map (liftFormula 0)) (Δ₂.map (liftFormula 0))
             (split_map 0 hΓ) (split_consL A (split_map 0 (split_tail hΔ)))
        refine ⟨Formula.ex C, ?_, LKp.exL Γ₂ Δ₂ C hC2, ?_, ?_⟩
        · have h1 : LKp (Γ₁.map (liftFormula 0))
              (substFormula 0 (Term.var 0) (liftFormula 1 C) :: A :: Δ₁.map (liftFormula 0)) := by
            rwa [FOL.Lift0.substFormula_lift_var C 0]
          have h2 := LKp.exR _ _ (liftFormula 1 C) (Term.var 0) h1
          have h3 : LKp (Γ₁.map (liftFormula 0)) (A :: (Formula.ex C :: Δ₁).map (liftFormula 0)) :=
            LKp.struct _ _ _ _ h2 (sub_refl _) (swap_cons _ _ _)
          exact LKp.struct _ _ _ _ (LKp.allR Γ₁ (Formula.ex C :: Δ₁) A h3)
            (sub_refl _) (sub_drop (List.Mem.tail _ hpr))
        · exact predSub_of_cov hS1 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => hr))
              (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx)))))
        · exact predSub_of_cov hS2 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (Γ₁.map (liftFormula 0)) (Γ₂.map (liftFormula 0))
             (Δ₁.map (liftFormula 0)) (A :: Δ₂.map (liftFormula 0))
             (split_map 0 hΓ) (split_consR A (split_map 0 (split_tail hΔ)))
        refine ⟨Formula.forall C, LKp.allR Γ₁ Δ₁ C hC1, ?_, ?_, ?_⟩
        · have h1 : LKp (substFormula 0 (Term.var 0) (liftFormula 1 C) :: Γ₂.map (liftFormula 0))
              (A :: Δ₂.map (liftFormula 0)) := by
            rwa [FOL.Lift0.substFormula_lift_var C 0]
          have h2 := LKp.allL _ _ (liftFormula 1 C) (Term.var 0) h1
          exact LKp.struct _ _ _ _ (LKp.allR (Formula.forall C :: Γ₂) Δ₂ A h2)
            (sub_refl _) (sub_drop hpr)
        · exact predSub_of_cov hS1 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
        · exact predSub_of_cov hS2 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr)) (fun _ hr => hr))
              (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx)))))
  | exL Γ Δ A _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ (Formula.ex A) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (A :: Γ₁.map (liftFormula 0)) (Γ₂.map (liftFormula 0))
             (Δ₁.map (liftFormula 0)) (Δ₂.map (liftFormula 0))
             (split_consL A (split_map 0 (split_tail hΓ))) (split_map 0 hΔ)
        refine ⟨Formula.ex C, ?_, LKp.exL Γ₂ Δ₂ C hC2, ?_, ?_⟩
        · have h1 : LKp (A :: Γ₁.map (liftFormula 0))
              (substFormula 0 (Term.var 0) (liftFormula 1 C) :: Δ₁.map (liftFormula 0)) := by
            rwa [FOL.Lift0.substFormula_lift_var C 0]
          have h2 := LKp.exR _ _ (liftFormula 1 C) (Term.var 0) h1
          exact LKp.struct _ _ _ _ (LKp.exL Γ₁ (Formula.ex C :: Δ₁) A h2)
            (sub_drop hpr) (sub_refl _)
        · exact predSub_of_cov hS1 (cov_append
            (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => hr))
              (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx))))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
        · exact predSub_of_cov hS2 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (Γ₁.map (liftFormula 0)) (A :: Γ₂.map (liftFormula 0))
             (Δ₁.map (liftFormula 0)) (Δ₂.map (liftFormula 0))
             (split_consR A (split_map 0 (split_tail hΓ))) (split_map 0 hΔ)
        refine ⟨Formula.forall C, LKp.allR Γ₁ Δ₁ C hC1, ?_, ?_, ?_⟩
        · have h1 : LKp (substFormula 0 (Term.var 0) (liftFormula 1 C)
              :: A :: Γ₂.map (liftFormula 0)) (Δ₂.map (liftFormula 0)) := by
            rwa [FOL.Lift0.substFormula_lift_var C 0]
          have h2 := LKp.allL _ _ (liftFormula 1 C) (Term.var 0) h1
          have h3 : LKp (A :: (Formula.forall C :: Γ₂).map (liftFormula 0))
              (Δ₂.map (liftFormula 0)) :=
            LKp.struct _ _ _ _ h2 (swap_cons _ _ _) (sub_refl _)
          exact LKp.struct _ _ _ _ (LKp.exL (Formula.forall C :: Γ₂) Δ₂ A h3)
            (sub_drop (List.Mem.tail _ hpr)) (sub_refl _)
        · exact predSub_of_cov hS1 (cov_append
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
        · exact predSub_of_cov hS2 (cov_append
            (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr)) (fun _ hr => hr))
              (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inl hx))))
            (cov_unlift 0 (fun x hx => List.mem_append.mpr (Or.inr hx))))
  | allL Γ Δ A t _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΓ (Formula.forall A) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih (substFormula 0 t A :: Γ₁) Γ₂ Δ₁ Δ₂
             (split_consL (substFormula 0 t A) (split_tail hΓ)) hΔ
        refine ⟨C, ?_, hC2, ?_, hS2⟩
        · exact LKp.struct _ _ _ _ (LKp.allL Γ₁ (C :: Δ₁) A t hC1) (sub_drop hpr) (sub_refl _)
        · exact predSub_of_cov hS1 (cov_append
            (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr))
              (fun p hr => (predF_subst p A 0 t).mp hr))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ (substFormula 0 t A :: Γ₂) Δ₁ Δ₂
             (split_consR (substFormula 0 t A) (split_tail hΓ)) hΔ
        refine ⟨C, hC1, ?_, hS1, ?_⟩
        · have h1 : LKp (substFormula 0 t A :: C :: Γ₂) Δ₂ :=
            LKp.struct _ _ _ _ hC2 (swap_cons _ _ _) (sub_refl _)
          exact LKp.struct _ _ _ _ (LKp.allL (C :: Γ₂) Δ₂ A t h1)
            (sub_drop (List.Mem.tail _ hpr)) (sub_refl _)
        · exact predSub_of_cov hS2 (cov_append
            (cov_cons (cov_one (List.mem_append.mpr (Or.inl hpr))
              (fun p hr => (predF_subst p A 0 t).mp hr))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx))))
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx))))
  | exR Γ Δ A t _ ih =>
      intro Γ₁ Γ₂ Δ₁ Δ₂ hΓ hΔ
      rcases hΔ (Formula.ex A) (List.Mem.head _) with hpr | hpr
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ Γ₂ (substFormula 0 t A :: Δ₁) Δ₂ hΓ
             (split_consL (substFormula 0 t A) (split_tail hΔ))
        refine ⟨C, ?_, hC2, ?_, hS2⟩
        · have h1 : LKp Γ₁ (substFormula 0 t A :: C :: Δ₁) :=
            LKp.struct _ _ _ _ hC1 (sub_refl _) (swap_cons _ _ _)
          exact LKp.struct _ _ _ _ (LKp.exR Γ₁ (C :: Δ₁) A t h1)
            (sub_refl _) (sub_drop (List.Mem.tail _ hpr))
        · exact predSub_of_cov hS1 (cov_append
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr))
              (fun p hr => (predF_subst p A 0 t).mp hr))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))))
      · obtain ⟨C, hC1, hC2, hS1, hS2⟩ :=
          ih Γ₁ Γ₂ Δ₁ (substFormula 0 t A :: Δ₂) hΓ
             (split_consR (substFormula 0 t A) (split_tail hΔ))
        refine ⟨C, hC1, ?_, hS1, ?_⟩
        · exact LKp.struct _ _ _ _ (LKp.exR (C :: Γ₂) Δ₂ A t hC2) (sub_refl _) (sub_drop hpr)
        · exact predSub_of_cov hS2 (cov_append
            (cov_sub (fun x hx => List.mem_append.mpr (Or.inl hx)))
            (cov_cons (cov_one (List.mem_append.mpr (Or.inr hpr))
              (fun p hr => (predF_subst p A 0 t).mp hr))
              (cov_sub (fun x hx => List.mem_append.mpr (Or.inr hx)))))

/-- 🏁🏁 **LA INTERPOLACIÓN DE CRAIG** para el fragmento puro, como corolario de Maehara con la
partición `Γ₁ = [A]`, `Δ₂ = [B]`. -/
theorem craig {A B : Formula} (h : LKp [A] [B]) :
    ∃ C, And (LKp [A] [C]) (And (LKp [C] [B])
         (And (PredSub C [A]) (PredSub C [B]))) := by
  obtain ⟨C, h1, h2, hS1, hS2⟩ := maehara h [A] [] [] [B]
    (fun x hx => Or.inl hx) (fun x hx => Or.inr hx)
  exact ⟨C, h1, h2, predSub_of_cov hS1 (cov_append (cov_sub (fun _ hx => hx)) cov_nil),
    predSub_of_cov hS2 (cov_append cov_nil (cov_sub (fun _ hx => hx)))⟩


-- ═══════════════════════════════════════════════════════════════════════════
-- §5 · ⭐ CONTROLES DE NO VACUIDAD — sin ellos el teorema podría ser cierto y no decir nada
-- ═══════════════════════════════════════════════════════════════════════════

/-- `LKp` demuestra algo: `P ∧ Q ⊢ P ∨ R`. -/
theorem lkp_example :
    LKp [Formula.and (Formula.atom "P" []) (Formula.atom "Q" [])]
        [Formula.or (Formula.atom "P" []) (Formula.atom "R" [])] :=
  LKp.andL [] _ (Formula.atom "P" []) (Formula.atom "Q" [])
    (LKp.orR _ [] (Formula.atom "P" []) (Formula.atom "R" [])
      (LKp.ax _ _ (Formula.atom "P" []) (List.Mem.head _) (List.Mem.head _)))

/-- ⭐ Y `craig` se aplica a ello: hay interpolante para `P ∧ Q ⊢ P ∨ R`, y su único predicado
posible es `P` — el común a los dos lados. -/
theorem craig_example :
    ∃ C, And (LKp [Formula.and (Formula.atom "P" []) (Formula.atom "Q" [])] [C])
         (And (LKp [C] [Formula.or (Formula.atom "P" []) (Formula.atom "R" [])])
         (And (PredSub C [Formula.and (Formula.atom "P" []) (Formula.atom "Q" [])])
              (PredSub C [Formula.or (Formula.atom "P" []) (Formula.atom "R" [])]))) :=
  craig lkp_example

/-- 🏁 **La forma reconocible de Craig**: de `A ⊢ B` salen `⊢ A ⇒ C` y `⊢ C ⇒ B`. -/
theorem craig_impl {A B : Formula} (h : LKp [A] [B]) :
    ∃ C, And (LKp [] [Formula.impl A C]) (And (LKp [] [Formula.impl C B])
         (And (PredSub C [A]) (PredSub C [B]))) := by
  obtain ⟨C, h1, h2, hS1, hS2⟩ := craig h
  exact ⟨C, LKp.implR [] [] A C (LKp.struct _ _ _ _ h1 (sub_refl _) (sub_refl _)),
    LKp.implR [] [] C B (LKp.struct _ _ _ _ h2 (sub_refl _) (sub_refl _)), hS1, hS2⟩

end FOL.Craig0

#print axioms FOL.Craig0.lkp_to_lk0
#print axioms FOL.Craig0.predF_lift
#print axioms FOL.Craig0.predF_subst
#print axioms FOL.Craig0.maehara
#print axioms FOL.Craig0.craig
#print axioms FOL.Craig0.craig_impl
#print axioms FOL.Craig0.lkp_example
