/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Craig0, FOL.Hauptsatz0
-- @axiom_system: classical
-- @importance: high

import FOL.Craig0
import FOL.Hauptsatz0

/-!
# `FOL.Interpolation0` — 🏁 la INTERPOLACIÓN DE CRAIG para `Derives₀`, CON IGUALDAD

    craig₀              : [A] ⊢₀ B → ∃ C, [A] ⊢₀ C ∧ [C] ⊢₀ B ∧ PredSub C [A] ∧ PredSub C [B]
    craig_ctx₀          : Γ ⊢₀ B   → ∃ C, Γ ⊢₀ C ∧ [C] ⊢₀ B ∧ PredSub C Γ ∧ PredSub C [B]
    lk0_to_lkp          : LK₀ Γ Δ → ∃ E, (∀ e ∈ E, EqGen e) ∧ LKp (E ++ Γ) Δ     -- el PUENTE
    lk0_to_derives0_fin : LK₀ Γ Δ → Γ ⊢₀ disjOf Δ                                -- sin completitud

Paga la deuda que `FOL.Craig0` declaraba ABIERTA (D3a, 2026‑09‑26): `craig` valía para `LKp`, el
fragmento SIN `eqAx`, y no había puente desde lo que el proyecto deriva. 📏 **`[propext, Quot.sound]`**
en todos los titulares: **ni un `Classical.choice`**.

## ⭐ El puente: la igualdad, al ANTECEDENTE y cerrada con `∀`

`LK₀.eqAx` mete una instancia de igualdad `g` en el antecedente; `lk0_to_lkp` la **deja ahí**: una
derivación de `LK₀` de `Γ ⟹ Δ` da una de `LKp` de `E, Γ ⟹ Δ`, con `E` las instancias usadas. El
único cuidado son `allR`/`exL`, cuyo contexto llega LEVANTADO: la `E` de la premisa puede mencionar
la eigenvariable `#0`. Se sustituye por `E.map ∀`, porque `lift₀ (∀e) = ∀ (lift₁ e)` y `allL` en `#0`
devuelve `e` (`substFormula_lift_var`). Por eso `EqGen` son las instancias **cerradas con `∀ʲ`**.

## ⭐⭐ Por qué NO hace falta borrar los predicados ajenos

Cada `EqGen` menciona **a lo sumo un** símbolo de relación (el de `eqAtomAx`). Se reparte `E` en
`E₁` (predicados del lenguaje de `Γ`) y `E₂` (predicados ajenos a `Γ`), y se llama a `maehara` con
`Γ₁ = E₁ ++ Γ`, `Γ₂ = E₂`. Maehara da `preds C ⊆ preds(E₁ ∪ Γ) = preds Γ` **y**
`preds C ⊆ preds(E₂ ∪ {B})`; como ningún predicado de `E₂` está en `Γ`, los de `C` están en `B`.
🔑 *La intersección de los dos lenguajes ya excluye lo ajeno: no hay que quitarlo, basta ponerlo en
el lado donde no puede sobrevivir.*

## ⭐ El dividendo: `LK₀ → ⊢₀` sin completitud

La única traducción `LK₀ → ⊢₀` del árbol era `SequentSound0.lk0_to_derives0`, que ES
`completeness₀` (el WKL, `Classical.choice`). `lk0_refute` la da SINTÁCTICAMENTE, leyendo `Γ ⟹ Δ`
como «`Γ` y las negaciones de `Δ` son contradictorias» con la lista por pertenencia; de ahí
`lk0_to_derives0_fin`, mismo enunciado, `[propext, Quot.sound]`.

## ⚠️ Alcance, dicho con sus palabras

* La condición de lenguaje es **sólo sobre SÍMBOLOS DE RELACIÓN** (`predF`); `≐` es lógico. No hay
  condición sobre símbolos de función ni sobre variables libres: para fórmulas abiertas es más débil
  que el Craig clásico; para sentencias, la de variables es vacua.
* El control `craig₀_example` usa lenguajes INCOMPARABLES y una igualdad necesaria (`P(c)`,
  `c ≐ d` ⊢ `P(d)`): el interpolante sólo puede mencionar `P`. No prueba el contenido de `craig₀` (un
  interpolante se da a mano); prueba que la hipótesis se cumple en un caso NO degenerado.

⚠️ Higiene contra `Classical.choice`: nada de `by_cases` sobre `predF`/pertenencia (la macro de core
hace `open Classical in`; se usan `predF_em`/`predL_em`), nada de `simp` sobre negaciones, y nada de
`open FOL.Hauptsatz0` (redefine `sub_refl`/`sub_cons`/`sub_wk`/`sub_drop`/`swap_cons`).
-/

namespace FOL.Interpolation0

open FOL.Herbrand0
open FOL.Craig0

-- ══════════════════════════════════════════════════════════════════════════
-- §1 · LA VUELTA, SINTÁCTICA: LK₀ → ⊢₀ (forma de refutación, por pertenencia)
-- ══════════════════════════════════════════════════════════════════════════

theorem derives0_by_contra {L : List Formula} {X : Formula}
    (h : (neg X :: L) ⊢₀ Formula.bottom) : L ⊢₀ X :=
  Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ h)

theorem derives0_cut {L : List Formula} {X ψ : Formula} (h1 : (X :: L) ⊢₀ ψ) (h2 : L ⊢₀ X) :
    L ⊢₀ ψ :=
  Derives₀.elim_impl _ _ _ (Derives₀.intro_impl _ _ _ h1) h2

/-- ⭐ `LK₀` (con `eqAx`) se traduce a `⊢₀` SIN completitud: `Γ ⟹ Δ` se lee «`Γ` y las
negaciones de `Δ` son contradictorias», con la lista dada POR PERTENENCIA. -/
theorem lk0_refute : ∀ {Γ Δ : List Formula}, LK₀ Γ Δ → ∀ L : List Formula,
    (∀ x, x ∈ Γ → x ∈ L) → (∀ d, d ∈ Δ → neg d ∈ L) → L ⊢₀ Formula.bottom := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A h1 h2 =>
      intro L hΓ hΔ
      exact Derives₀.elim_impl _ A Formula.bottom (Derives₀.hyp _ _ (hΔ A h2))
        (Derives₀.hyp _ _ (hΓ A h1))
  | botL Γ Δ h1 =>
      intro L hΓ _
      exact Derives₀.hyp _ _ (hΓ _ h1)
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      intro L hΓ hΔ
      exact ih L (fun x hx => hΓ x (hsΓ x hx)) (fun d hd => hΔ d (hsΔ d hd))
  | implR Γ Δ A B _ ih =>
      intro L hΓ hΔ
      have h1 : (neg B :: A :: L) ⊢₀ Formula.bottom :=
        ih (neg B :: A :: L)
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.tail _ (List.Mem.head _)
            | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ (hΓ x hm)))
          (fun d hd => by
            cases hd with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (List.Mem.tail _ (hΔ d (List.Mem.tail _ hm))))
      exact Derives₀.elim_impl _ (Formula.impl A B) Formula.bottom
        (Derives₀.hyp _ _ (hΔ _ (List.Mem.head _))) (Derives₀.intro_impl _ _ _ (derives0_by_contra h1))
  | implL Γ Δ A B _ _ ih1 ih2 =>
      intro L hΓ hΔ
      have hA : L ⊢₀ A := derives0_by_contra (ih1 (neg A :: L)
          (fun x hx => List.Mem.tail _ (hΓ x (List.Mem.tail _ hx)))
          (fun d hd => by
            cases hd with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (hΔ d hm)))
      have hB : L ⊢₀ B :=
        Derives₀.elim_impl _ A B (Derives₀.hyp _ _ (hΓ _ (List.Mem.head _))) hA
      exact derives0_cut (ih2 (B :: L)
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (hΓ x (List.Mem.tail _ hm)))
          (fun d hd => List.Mem.tail _ (hΔ d hd))) hB
  | andR Γ Δ A B _ _ ih1 ih2 =>
      intro L hΓ hΔ
      have side : ∀ X, ∀ d, d ∈ X :: Δ → neg d ∈ neg X :: L := fun X d hd => by
        cases hd with
        | head => exact List.Mem.head _
        | tail _ hm => exact List.Mem.tail _ (hΔ d (List.Mem.tail _ hm))
      have hA : L ⊢₀ A :=
        derives0_by_contra (ih1 (neg A :: L) (fun x hx => List.Mem.tail _ (hΓ x hx)) (side A))
      have hB : L ⊢₀ B :=
        derives0_by_contra (ih2 (neg B :: L) (fun x hx => List.Mem.tail _ (hΓ x hx)) (side B))
      exact Derives₀.elim_impl _ (Formula.and A B) Formula.bottom
        (Derives₀.hyp _ _ (hΔ _ (List.Mem.head _))) (Derives₀.intro_and _ _ _ hA hB)
  | andL Γ Δ A B _ ih =>
      intro L hΓ hΔ
      have hAB : L ⊢₀ Formula.and A B := Derives₀.hyp _ _ (hΓ _ (List.Mem.head _))
      have h0 : (A :: B :: L) ⊢₀ Formula.bottom := ih (A :: B :: L)
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.head _
            | tail _ hm =>
                cases hm with
                | head => exact List.Mem.tail _ (List.Mem.head _)
                | tail _ hm2 =>
                    exact List.Mem.tail _ (List.Mem.tail _ (hΓ x (List.Mem.tail _ hm2))))
          (fun d hd => List.Mem.tail _ (List.Mem.tail _ (hΔ d hd)))
      have h1 : (B :: L) ⊢₀ Formula.bottom := derives0_cut h0
        (Derives₀.elim_and_l _ A B (Derives₀.weakening _ _ _ hAB (fun x hx => List.Mem.tail _ hx)))
      exact derives0_cut h1 (Derives₀.elim_and_r _ A B hAB)
  | orR Γ Δ A B _ ih =>
      intro L hΓ hΔ
      have hn : neg (Formula.or A B) ∈ L := hΔ _ (List.Mem.head _)
      have h0 : (neg A :: neg B :: L) ⊢₀ Formula.bottom := ih (neg A :: neg B :: L)
          (fun x hx => List.Mem.tail _ (List.Mem.tail _ (hΓ x hx)))
          (fun d hd => by
            cases hd with
            | head => exact List.Mem.head _
            | tail _ hm =>
                cases hm with
                | head => exact List.Mem.tail _ (List.Mem.head _)
                | tail _ hm2 =>
                    exact List.Mem.tail _ (List.Mem.tail _ (hΔ d (List.Mem.tail _ hm2))))
      have hnA : (neg B :: L) ⊢₀ neg A := Derives₀.intro_impl _ _ _
        (Derives₀.elim_impl _ (Formula.or A B) Formula.bottom
          (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ hn)))
          (Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))))
      have hnB : L ⊢₀ neg B := Derives₀.intro_impl _ _ _
        (Derives₀.elim_impl _ (Formula.or A B) Formula.bottom
          (Derives₀.hyp _ _ (List.Mem.tail _ hn))
          (Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))))
      exact derives0_cut (derives0_cut h0 hnA) hnB
  | orL Γ Δ A B _ _ ih1 ih2 =>
      intro L hΓ hΔ
      have sub : ∀ X, ∀ x, x ∈ X :: Γ → x ∈ X :: L := fun X x hx => by
        cases hx with
        | head => exact List.Mem.head _
        | tail _ hm => exact List.Mem.tail _ (hΓ x (List.Mem.tail _ hm))
      exact Derives₀.elim_or _ A B _ (Derives₀.hyp _ _ (hΓ _ (List.Mem.head _)))
        (ih1 (A :: L) (sub A) (fun d hd => List.Mem.tail _ (hΔ d hd)))
        (ih2 (B :: L) (sub B) (fun d hd => List.Mem.tail _ (hΔ d hd)))
  | allR Γ Δ A _ ih =>
      intro L hΓ hΔ
      have h0 : (neg A :: L.map (liftFormula 0)) ⊢₀ Formula.bottom :=
        ih (neg A :: L.map (liftFormula 0))
          (fun x hx => by
            obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
            exact List.Mem.tail _ (List.mem_map_of_mem (hΓ g hg)))
          (fun d hd => by
            cases hd with
            | head => exact List.Mem.head _
            | tail _ hm =>
                obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hm
                -- liftFormula 0 (neg d0) ≡ neg (liftFormula 0 d0)  (rfl)
                exact List.Mem.tail _
                  (List.mem_map_of_mem (f := liftFormula 0) (hΔ d0 (List.Mem.tail _ hd0))))
      exact Derives₀.elim_impl _ (Formula.forall A) Formula.bottom
        (Derives₀.hyp _ _ (hΔ _ (List.Mem.head _)))
        (Derives₀.intro_forall _ _ (derives0_by_contra h0))
  | allL Γ Δ A t _ ih =>
      intro L hΓ hΔ
      exact derives0_cut (ih (substFormula 0 t A :: L)
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (hΓ x (List.Mem.tail _ hm)))
          (fun d hd => List.Mem.tail _ (hΔ d hd)))
        (Derives₀.elim_forall _ A t (Derives₀.hyp _ _ (hΓ _ (List.Mem.head _))))
  | exR Γ Δ A t _ ih =>
      intro L hΓ hΔ
      have hn : L ⊢₀ neg (substFormula 0 t A) := Derives₀.intro_impl _ _ _
        (Derives₀.elim_impl _ (Formula.ex A) Formula.bottom
          (Derives₀.hyp _ _ (List.Mem.tail _ (hΔ _ (List.Mem.head _))))
          (Derives₀.intro_ex _ A t (Derives₀.hyp _ _ (List.Mem.head _))))
      exact derives0_cut (ih (neg (substFormula 0 t A) :: L) (fun x hx => List.Mem.tail _ (hΓ x hx))
          (fun d hd => by
            cases hd with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (hΔ d (List.Mem.tail _ hm)))) hn
  | exL Γ Δ A _ ih =>
      intro L hΓ hΔ
      refine Derives₀.elim_ex _ A Formula.bottom (Derives₀.hyp _ _ (hΓ _ (List.Mem.head _))) ?_
      -- meta: (A :: L.map (liftFormula 0)) ⊢₀ liftFormula 0 ⊥, y liftFormula 0 ⊥ ≡ ⊥
      exact ih (A :: L.map (liftFormula 0))
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.head _
            | tail _ hm =>
                obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
                exact List.Mem.tail _ (List.mem_map_of_mem (hΓ g (List.Mem.tail _ hg))))
          (fun d hd => by
            obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
            exact List.Mem.tail _ (List.mem_map_of_mem (f := liftFormula 0) (hΔ d0 hd0)))
  | eqAx Γ Δ g hg _ ih =>
      intro L hΓ hΔ
      exact derives0_cut (ih (g :: L)
          (fun x hx => by
            cases hx with
            | head => exact List.Mem.head _
            | tail _ hm => exact List.Mem.tail _ (hΓ x hm))
          (fun d hd => List.Mem.tail _ (hΔ d hd)))
        (Derives₀.weakening _ _ _ (derives0_of_eqInstance hg)
          (fun x hx => absurd hx List.not_mem_nil))


/-- De la refutación con las negaciones del sucedente DELANTE, a la disyunción. -/
theorem derives0_disjOf_of_refute : ∀ (Δ Γ : List Formula),
    ((Δ.map neg ++ Γ) ⊢₀ Formula.bottom) → Γ ⊢₀ disjOf Δ
  | [], _, h => h
  | d :: Δ, Γ, h => by
      have h0 : (neg d :: (Δ.map neg ++ Γ)) ⊢₀ Formula.bottom := h
      have h1 : (Δ.map neg ++ neg d :: Γ) ⊢₀ Formula.bottom :=
        Derives₀.weakening _ _ _ h0 (fun x hx => by
          cases hx with
          | head => exact List.mem_append_right _ (List.Mem.head _)
          | tail _ hm =>
              rcases List.mem_append.mp hm with h' | h'
              · exact List.mem_append_left _ h'
              · exact List.mem_append_right _ (List.Mem.tail _ h'))
      exact FOL.Propositional0.derives0_cases (A := d)
        (Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)))
        (Derives₀.intro_or_r _ _ _ (derives0_disjOf_of_refute Δ (neg d :: Γ) h1))

/-- ⭐ Dividendo: el MISMO enunciado que `SequentSound0.lk0_to_derives0`, que es
`completeness₀` (`Classical.choice`); éste no. Sufijo `_fin` como `Finitary0.lk0_not_empty_fin`. -/
theorem lk0_to_derives0_fin {Γ Δ : List Formula} (h : LK₀ Γ Δ) : Γ ⊢₀ disjOf Δ :=
  derives0_disjOf_of_refute Δ Γ (lk0_refute h (Δ.map neg ++ Γ)
    (fun _ hx => List.mem_append_right _ hx)
    (fun _ hd => List.mem_append_left _ (List.mem_map_of_mem (f := neg) hd)))

theorem derives0_of_disjOf_single {Γ : List Formula} {X : Formula} (h : Γ ⊢₀ disjOf [X]) :
    Γ ⊢₀ X :=
  Derives₀.elim_or Γ X Formula.bottom X h (Derives₀.hyp _ _ (List.Mem.head _))
    (Derives₀.bot_elim _ _ (Derives₀.hyp _ _ (List.Mem.head _)))

/-- `Herbrand0.derives0_discharge` (Herbrand0:188) con contexto. -/
theorem derives0_discharge_ctx : ∀ (E Γ : List Formula) (ψ : Formula),
    ((E ++ Γ) ⊢₀ ψ) → (∀ g, g ∈ E → ([] ⊢₀ g)) → Γ ⊢₀ ψ
  | [], _, _, h, _ => h
  | g :: E, Γ, ψ, h, hE => by
      refine derives0_discharge_ctx E Γ ψ ?_ (fun x hx => hE x (List.Mem.tail _ hx))
      exact Derives₀.elim_impl _ g ψ (Derives₀.intro_impl _ _ _ h)
        (Derives₀.weakening _ _ _ (hE g (List.Mem.head _)) (fun x hx => absurd hx List.not_mem_nil))

-- ══════════════════════════════════════════════════════════════════════════
-- §2 · Las instancias de igualdad CERRADAS con ∀, y la aritmética de pertenencia
-- ══════════════════════════════════════════════════════════════════════════

/-- `EqGen e`: `e = ∀ⁿ g` con `EqInstance g`. (Equivale a `∃ j g, EqInstance g ∧ e = allBlock j g`,
pero `allBlock` vive en `SkolemN0`, que arrastra `Canonical0`: no se importa por esto.) -/
inductive EqGen : Formula → Prop where
  | inst : ∀ g, EqInstance g → EqGen g
  | all : ∀ e, EqGen e → EqGen (Formula.forall e)

theorem gen_nil : ∀ e, e ∈ ([] : List Formula) → EqGen e :=
  fun _ h => absurd h List.not_mem_nil

theorem gen_app {E1 E2 : List Formula} (h1 : ∀ e, e ∈ E1 → EqGen e)
    (h2 : ∀ e, e ∈ E2 → EqGen e) : ∀ e, e ∈ E1 ++ E2 → EqGen e :=
  fun e he => (List.mem_append.mp he).elim (h1 e) (h2 e)

theorem gen_map_all {E : List Formula} (hE : ∀ e, e ∈ E → EqGen e) :
    ∀ e, e ∈ E.map (fun e => Formula.forall e) → EqGen e := by
  intro e he
  rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
  exact EqGen.all e0 (hE e0 he0)

/-- ⭐ Toda `EqGen` es DERIVABLE: la instancia por `derives0_of_eqInstance`, cada `∀` por
`intro_forall` sobre el contexto vacío (`[].map lift = []`). -/
theorem derives0_of_eqGen {e : Formula} (he : EqGen e) : [] ⊢₀ e := by
  induction he with
  | inst g hg => exact derives0_of_eqInstance hg
  | all e _ ih => exact Derives₀.intro_forall [] e ih

-- ══════════════════════════════════════════════════════════════════════════
-- §2b · Aritmética de pertenencia con la `E` delante
-- ══════════════════════════════════════════════════════════════════════════

theorem sub_front {E Γ : List Formula} {a : Formula} :
    ∀ x, x ∈ E ++ a :: Γ → x ∈ a :: (E ++ Γ) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.Mem.tail _ (List.mem_append_left _ h)
  · cases h with
    | head => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (List.mem_append_right _ h')

theorem sub_front' {E Γ : List Formula} {a : Formula} :
    ∀ x, x ∈ a :: (E ++ Γ) → x ∈ E ++ a :: Γ := by
  intro x hx
  cases hx with
  | head => exact List.mem_append_right _ (List.Mem.head _)
  | tail _ h =>
      rcases List.mem_append.mp h with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.Mem.tail _ h')

theorem sub_app {E Γ Γ' : List Formula} (h : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ E ++ Γ → x ∈ E ++ Γ' := by
  intro x hx
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (h x h')

theorem sub_catL {E1 E2 Γ : List Formula} : ∀ x, x ∈ E1 ++ Γ → x ∈ (E1 ++ E2) ++ Γ := by
  intro x hx
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ (List.mem_append_left _ h')
  · exact List.mem_append_right _ h'

theorem sub_catR {E1 E2 Γ : List Formula} : ∀ x, x ∈ E2 ++ Γ → x ∈ (E1 ++ E2) ++ Γ := by
  intro x hx
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ (List.mem_append_right _ h')
  · exact List.mem_append_right _ h'

-- ══════════════════════════════════════════════════════════════════════════
-- §3 · EL PUENTE LK0 -> LKp, con la igualdad en el antecedente
-- ══════════════════════════════════════════════════════════════════════════

/-- ⭐ `allL` ITERADO: cada hipótesis `e` de `L` se puede sustituir por `∀ (lift₁ e)`, que es
`lift₀ (∀ e)`. Por `substFormula_lift_var`, instanciar en `x₀` la devuelve.
⚠️ El resultado se enuncia como `(L.map ∀).map lift₀` a propósito: es literalmente lo que `allR`
y `exL` piden para `E.map ∀`, y así el caso sólo necesita `List.map_append`. -/
theorem lkp_allL_list (Δ : List Formula) : ∀ (L Γ : List Formula),
    LKp (L ++ Γ) Δ → LKp ((L.map (fun e => Formula.forall e)).map (liftFormula 0) ++ Γ) Δ
  | [], _, h => h
  | e :: L, Γ, h => by
      have h1 : LKp (L ++ e :: Γ) Δ :=
        LKp.struct _ _ _ _ h (sub_front' (E := L) (Γ := Γ) (a := e)) (sub_refl _)
      have h2 : LKp ((L.map (fun e => Formula.forall e)).map (liftFormula 0) ++ e :: Γ) Δ :=
        lkp_allL_list Δ L (e :: Γ) h1
      have h3 : LKp (e :: ((L.map (fun e => Formula.forall e)).map (liftFormula 0) ++ Γ)) Δ :=
        LKp.struct _ _ _ _ h2
          (sub_front (E := (L.map (fun e => Formula.forall e)).map (liftFormula 0)) (Γ := Γ)
            (a := e)) (sub_refl _)
      have h4 : LKp (substFormula 0 (Term.var 0) (liftFormula 1 e)
          :: ((L.map (fun e => Formula.forall e)).map (liftFormula 0) ++ Γ)) Δ := by
        rw [FOL.Lift0.substFormula_lift_var e 0]; exact h3
      -- `liftFormula 0 (∀ e)` ES `∀ (liftFormula 1 e)` por definición
      exact LKp.allL _ Δ (liftFormula 1 e) (Term.var 0) h4

/-- ⭐⭐ **EL PUENTE.** Toda derivación de `LK₀` es una de `LKp` con las instancias de igualdad
que usa —cerradas con `∀`— puestas delante del antecedente. -/
theorem lk0_to_lkp : ∀ {Γ Δ : List Formula}, LK₀ Γ Δ →
    ∃ E : List Formula, And (∀ e, e ∈ E → EqGen e) (LKp (E ++ Γ) Δ) := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A h1 h2 => exact ⟨[], gen_nil, LKp.ax _ _ A (List.mem_append_right [] h1) h2⟩
  | botL Γ Δ hb => exact ⟨[], gen_nil, LKp.botL _ _ (List.mem_append_right [] hb)⟩
  | struct Γ Γ' Δ Δ' _ hsΓ hsΔ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      exact ⟨E, hE, LKp.struct _ _ _ _ hd (sub_app hsΓ) hsΔ⟩
  | implR Γ Δ A B _ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      have h1 : LKp (A :: (E ++ Γ)) (B :: Δ) := LKp.struct _ _ _ _ hd sub_front (sub_refl _)
      exact ⟨E, hE, LKp.implR _ _ A B h1⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨E1, hE1, hd1⟩ := ih1
      obtain ⟨E2, hE2, hd2⟩ := ih2
      have p1 : LKp ((E1 ++ E2) ++ Γ) (A :: Δ) := LKp.struct _ _ _ _ hd1 sub_catL (sub_refl _)
      have p2 : LKp (B :: ((E1 ++ E2) ++ Γ)) Δ :=
        LKp.struct _ _ _ _ hd2
          (fun x hx => sub_cons B (sub_catR (E1 := E1) (E2 := E2) (Γ := Γ)) x (sub_front x hx))
          (sub_refl _)
      exact ⟨E1 ++ E2, gen_app hE1 hE2,
        LKp.struct _ _ _ _ (LKp.implL _ _ A B p1 p2) sub_front' (sub_refl _)⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨E1, hE1, hd1⟩ := ih1
      obtain ⟨E2, hE2, hd2⟩ := ih2
      have p1 : LKp ((E1 ++ E2) ++ Γ) (A :: Δ) := LKp.struct _ _ _ _ hd1 sub_catL (sub_refl _)
      have p2 : LKp ((E1 ++ E2) ++ Γ) (B :: Δ) := LKp.struct _ _ _ _ hd2 sub_catR (sub_refl _)
      exact ⟨E1 ++ E2, gen_app hE1 hE2, LKp.andR _ _ A B p1 p2⟩
  | andL Γ Δ A B _ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      have h1 : LKp (A :: B :: (E ++ Γ)) Δ :=
        LKp.struct _ _ _ _ hd
          (fun x hx => sub_cons A (sub_front (E := E) (Γ := Γ) (a := B)) x (sub_front x hx))
          (sub_refl _)
      exact ⟨E, hE, LKp.struct _ _ _ _ (LKp.andL _ _ A B h1) sub_front' (sub_refl _)⟩
  | orR Γ Δ A B _ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      exact ⟨E, hE, LKp.orR _ _ A B hd⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨E1, hE1, hd1⟩ := ih1
      obtain ⟨E2, hE2, hd2⟩ := ih2
      have p1 : LKp (A :: ((E1 ++ E2) ++ Γ)) Δ :=
        LKp.struct _ _ _ _ hd1
          (fun x hx => sub_cons A (sub_catL (E1 := E1) (E2 := E2) (Γ := Γ)) x (sub_front x hx))
          (sub_refl _)
      have p2 : LKp (B :: ((E1 ++ E2) ++ Γ)) Δ :=
        LKp.struct _ _ _ _ hd2
          (fun x hx => sub_cons B (sub_catR (E1 := E1) (E2 := E2) (Γ := Γ)) x (sub_front x hx))
          (sub_refl _)
      exact ⟨E1 ++ E2, gen_app hE1 hE2,
        LKp.struct _ _ _ _ (LKp.orL _ _ A B p1 p2) sub_front' (sub_refl _)⟩
  | allR Γ Δ A _ ih =>
      -- ih : LKp (E ++ Γ.map lift₀) (A :: Δ.map lift₀); la `E` puede mencionar x₀
      obtain ⟨E, hE, hd⟩ := ih
      have h2 : LKp ((E.map (fun e => Formula.forall e)).map (liftFormula 0)
          ++ Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) :=
        lkp_allL_list (A :: Δ.map (liftFormula 0)) E (Γ.map (liftFormula 0)) hd
      have h3 : LKp ((E.map (fun e => Formula.forall e) ++ Γ).map (liftFormula 0))
          (A :: Δ.map (liftFormula 0)) := by
        rw [List.map_append]; exact h2
      exact ⟨E.map (fun e => Formula.forall e), gen_map_all hE, LKp.allR _ Δ A h3⟩
  | allL Γ Δ A t _ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      have h1 : LKp (substFormula 0 t A :: (E ++ Γ)) Δ :=
        LKp.struct _ _ _ _ hd sub_front (sub_refl _)
      exact ⟨E, hE, LKp.struct _ _ _ _ (LKp.allL _ _ A t h1) sub_front' (sub_refl _)⟩
  | exR Γ Δ A t _ ih =>
      obtain ⟨E, hE, hd⟩ := ih
      exact ⟨E, hE, LKp.exR _ _ A t hd⟩
  | exL Γ Δ A _ ih =>
      -- ih : LKp (E ++ A :: Γ.map lift₀) (Δ.map lift₀)
      obtain ⟨E, hE, hd⟩ := ih
      have h2 : LKp ((E.map (fun e => Formula.forall e)).map (liftFormula 0)
          ++ A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) :=
        lkp_allL_list (Δ.map (liftFormula 0)) E (A :: Γ.map (liftFormula 0)) hd
      have h3 : LKp (A :: ((E.map (fun e => Formula.forall e)).map (liftFormula 0)
          ++ Γ.map (liftFormula 0))) (Δ.map (liftFormula 0)) :=
        LKp.struct _ _ _ _ h2 sub_front (sub_refl _)
      have h4 : LKp (A :: (E.map (fun e => Formula.forall e) ++ Γ).map (liftFormula 0))
          (Δ.map (liftFormula 0)) := by
        rw [List.map_append]; exact h3
      exact ⟨E.map (fun e => Formula.forall e), gen_map_all hE,
        LKp.struct _ _ _ _ (LKp.exL _ Δ A h4) sub_front' (sub_refl _)⟩
  | eqAx Γ Δ g hg _ ih =>
      -- ⭐ el único caso que CRECE la lista: `g` entra con `j = 0`
      obtain ⟨E, hE, hd⟩ := ih
      refine ⟨g :: E, ?_, LKp.struct _ _ _ _ hd sub_front (sub_refl _)⟩
      intro x hx
      cases hx with
      | head => exact EqGen.inst _ hg
      | tail _ h' => exact hE x h'

-- ══════════════════════════════════════════════════════════════════════════
-- §4 · LA PARTICION POR LENGUAJE, sin Classical y SIN borrado
-- ══════════════════════════════════════════════════════════════════════════

theorem em_or2 {P Q : Prop} (hP : Or P (Not P)) (hQ : Or Q (Not Q)) :
    Or (Or P Q) (Not (Or P Q)) :=
  hP.elim (fun h => Or.inl (Or.inl h))
    (fun hnP => hQ.elim (fun h => Or.inl (Or.inr h))
      (fun hnQ => Or.inr (fun h => h.elim hnP hnQ)))

/-- `predF p f` es DECIDIBLE, sin `Classical`: `String` tiene `DecidableEq`. -/
theorem predF_em (p : String) : ∀ (f : Formula), Or (predF p f) (Not (predF p f))
  | .bottom => Or.inr (fun h => h)
  | .atom q _ => Decidable.em (q = p)
  | .eq _ _ => Or.inr (fun h => h)
  | .impl a b => em_or2 (predF_em p a) (predF_em p b)
  | .and a b => em_or2 (predF_em p a) (predF_em p b)
  | .or a b => em_or2 (predF_em p a) (predF_em p b)
  | .forall a => predF_em p a
  | .ex a => predF_em p a

/-- «`P` está en el lenguaje de `Γ`», decidido. -/
theorem predL_em (P : String) : ∀ (Γ : List Formula),
    Or (∃ g, And (g ∈ Γ) (predF P g)) (Not (∃ g, And (g ∈ Γ) (predF P g)))
  | [] => Or.inr (fun hx => by
      obtain ⟨_, hg, _⟩ := hx
      exact absurd hg List.not_mem_nil)
  | g :: Γ => by
      rcases predF_em P g with h | hn
      · exact Or.inl ⟨g, List.Mem.head _, h⟩
      · rcases predL_em P Γ with ⟨g', hg', h'⟩ | hn'
        · exact Or.inl ⟨g', List.Mem.tail _ hg', h'⟩
        · refine Or.inr (fun hx => ?_)
          obtain ⟨x, hxm, hpx⟩ := hx
          cases hxm with
          | head => exact hn hpx
          | tail _ hm => exact hn' ⟨x, hm, hpx⟩

/-- ⭐⭐ **El dato que hace innecesario el borrado**: una `EqGen` tiene sus predicados TODOS en el
lenguaje de `Γ`, o NINGUNO — porque menciona a lo sumo uno (`p` si es `eqAtomAx p …`). -/
theorem eqGen_side (Γ : List Formula) {e : Formula} (he : EqGen e) :
    Or (∀ p, predF p e → ∃ g, And (g ∈ Γ) (predF p g))
       (∀ p, predF p e → Not (∃ g, And (g ∈ Γ) (predF p g))) := by
  induction he with
  | inst g hg =>
      cases hg with
      | refl t => exact Or.inl (fun p hp => (hp : False).elim)
      | symm t u =>
          exact Or.inl (fun p hp => (hp : Or False False).elim False.elim False.elim)
      | trans t u w =>
          exact Or.inl (fun p hp => (hp : Or False (Or False False)).elim False.elim
            (fun h => h.elim False.elim False.elim))
      | func f pre post a b =>
          exact Or.inl (fun p hp => (hp : Or False False).elim False.elim False.elim)
      | atom P pre post a b =>
          have key : ∀ p, predF p (eqAtomAx P pre post a b) → P = p := fun p hp =>
            (hp : Or False (Or (P = p) (P = p))).elim False.elim (fun h => h.elim id id)
          rcases predL_em P Γ with hA | hA
          · exact Or.inl (fun p hp => key p hp ▸ hA)
          · exact Or.inr (fun p hp => key p hp ▸ hA)
  | all e _ ih => exact ih

theorem split_exists {P Q : Formula → Prop} : ∀ (E : List Formula),
    (∀ e, e ∈ E → Or (P e) (Q e)) →
    ∃ E₁ E₂, And (Split E E₁ E₂)
      (And (∀ e, e ∈ E₁ → And (e ∈ E) (P e)) (∀ e, e ∈ E₂ → And (e ∈ E) (Q e)))
  | [], _ => ⟨[], [], fun _ hx => absurd hx List.not_mem_nil,
      fun _ he => absurd he List.not_mem_nil, fun _ he => absurd he List.not_mem_nil⟩
  | e :: E, h => by
      obtain ⟨E₁, E₂, hs, h1, h2⟩ :=
        split_exists (P := P) (Q := Q) E (fun x hx => h x (List.Mem.tail _ hx))
      rcases h e (List.Mem.head _) with hp | hq
      · refine ⟨e :: E₁, E₂, split_consL e hs, ?_, fun x hx =>
          ⟨List.Mem.tail _ (h2 x hx).1, (h2 x hx).2⟩⟩
        intro x hx
        cases hx with
        | head => exact ⟨List.Mem.head _, hp⟩
        | tail _ hm => exact ⟨List.Mem.tail _ (h1 x hm).1, (h1 x hm).2⟩
      · refine ⟨E₁, e :: E₂, split_consR e hs, fun x hx =>
          ⟨List.Mem.tail _ (h1 x hx).1, (h1 x hx).2⟩, ?_⟩
        intro x hx
        cases hx with
        | head => exact ⟨List.Mem.head _, hq⟩
        | tail _ hm => exact ⟨List.Mem.tail _ (h2 x hm).1, (h2 x hm).2⟩

-- ══════════════════════════════════════════════════════════════════════════
-- §5 · CRAIG PARA `Derives₀`, CON IGUALDAD
-- ══════════════════════════════════════════════════════════════════════════

/-- **Interpolación de Craig para `⊢₀`, con contexto.** `Derives₀ → Derives₂ → LKc → LK₀`
(Hauptsatz) `→ LKp` con `E` delante (§3) `→` partición por el lenguaje de `Γ` (§4) `→` Maehara
`→` vuelta sintáctica (§1) `→` descarga de `E`. -/
theorem craig_ctx₀ {Γ : List Formula} {B : Formula} (h : Γ ⊢₀ B) :
    ∃ C, And (Γ ⊢₀ C) (And ([C] ⊢₀ B) (And (PredSub C Γ) (PredSub C [B]))) := by
  have hlk : LK₀ Γ [B] :=
    FOL.Hauptsatz0.cut_elimination _ _
      (FOL.NDtoLK0.ndToLK (FOL.Derives2.derives0_iff_derives2.mp h))
  obtain ⟨E, hE, hp⟩ := lk0_to_lkp hlk
  obtain ⟨E₁, E₂, hs, h1, h2⟩ :=
    split_exists (P := fun e => ∀ p, predF p e → ∃ g, And (g ∈ Γ) (predF p g))
      (Q := fun e => ∀ p, predF p e → Not (∃ g, And (g ∈ Γ) (predF p g)))
      E (fun e he => eqGen_side Γ (hE e he))
  obtain ⟨C, hC1, hC2, hS1, hS2⟩ := maehara hp (E₁ ++ Γ) E₂ [] [B]
    (fun x hx => by
      rcases List.mem_append.mp hx with hx' | hx'
      · exact (hs x hx').elim (fun h' => Or.inl (List.mem_append_left _ h')) Or.inr
      · exact Or.inl (List.mem_append_right _ hx'))
    (fun x hx => Or.inr hx)
  -- lenguaje, lado 1: los predicados de E₁ están en Γ
  have hA : PredSub C Γ := by
    intro p hp'
    obtain ⟨g, hg, hpg⟩ := hS1 p hp'
    rcases List.mem_append.mp hg with hg' | hg'
    · rcases List.mem_append.mp hg' with hg'' | hg''
      · exact (h1 g hg'').2 p hpg
      · exact ⟨g, hg'', hpg⟩
    · exact absurd hg' List.not_mem_nil
  -- lenguaje, lado 2: un predicado de E₂ NO está en Γ, y los de C sí ⇒ es de B
  have hB : PredSub C [B] := by
    intro p hp'
    obtain ⟨g, hg, hpg⟩ := hS2 p hp'
    rcases List.mem_append.mp hg with hg' | hg'
    · exact absurd (hA p hp') ((h2 g hg').2 p hpg)
    · exact ⟨g, hg', hpg⟩
  have d1 : (E₁ ++ Γ) ⊢₀ C :=
    derives0_of_disjOf_single (lk0_to_derives0_fin (lkp_to_lk0 hC1))
  have d2 : (E₂ ++ [C]) ⊢₀ B :=
    Derives₀.weakening _ _ _ (derives0_of_disjOf_single (lk0_to_derives0_fin (lkp_to_lk0 hC2)))
      (fun x hx => by
        cases hx with
        | head => exact List.mem_append_right _ (List.Mem.head _)
        | tail _ h' => exact List.mem_append_left _ h')
  exact ⟨C,
    derives0_discharge_ctx E₁ Γ C d1 (fun e he => derives0_of_eqGen (hE e (h1 e he).1)),
    derives0_discharge_ctx E₂ [C] B d2 (fun e he => derives0_of_eqGen (hE e (h2 e he).1)),
    hA, hB⟩

/-- 🏁 **LA INTERPOLACIÓN DE CRAIG para `⊢₀`**, con la igualdad como símbolo lógico. -/
theorem craig₀ {A B : Formula} (h : [A] ⊢₀ B) :
    ∃ C, And ([A] ⊢₀ C) (And ([C] ⊢₀ B) (And (PredSub C [A]) (PredSub C [B]))) :=
  craig_ctx₀ h

theorem craig_impl₀ {A B : Formula} (h : [A] ⊢₀ B) :
    ∃ C, And ([] ⊢₀ Formula.impl A C) (And ([] ⊢₀ Formula.impl C B)
      (And (PredSub C [A]) (PredSub C [B]))) := by
  obtain ⟨C, h1, h2, hS1, hS2⟩ := craig₀ h
  exact ⟨C, Derives₀.intro_impl [] A C h1, Derives₀.intro_impl [] C B h2, hS1, hS2⟩

-- ══════════════════════════════════════════════════════════════════════════
-- §6 · CONTROL — lenguajes INCOMPARABLES y la igualdad trabajando
-- ══════════════════════════════════════════════════════════════════════════

/-- `P(c) ∧ ((c ≐ d) ∧ Q) ⊢₀ P(d) ∨ R`: el interpolante sólo puede mencionar `P`, así que los
testigos triviales `A` (tiene `Q`) y `B` (tiene `R`) quedan EXCLUIDOS.
⚠️ No prueba «contenido» de `craig₀` (`C := P(d)` se da a mano): comprueba que la hipótesis se
cumple en un caso no degenerado. ⛔ NO usar como control `A := ⊤` ni un `B` sin predicados:
ahí `C := ⊤` / `C := B` satisfacen la conclusión SIN `craig₀`. -/
theorem craig₀_example :
    ∃ C, And ([Formula.and (Formula.atom "P" [Term.func "c" []])
                (Formula.and (Formula.eq (Term.func "c" []) (Term.func "d" []))
                  (Formula.atom "Q" []))] ⊢₀ C)
      (And ([C] ⊢₀ Formula.or (Formula.atom "P" [Term.func "d" []]) (Formula.atom "R" []))
           (∀ p, predF p C → p = "P")) := by
  have hd : [Formula.and (Formula.atom "P" [Term.func "c" []])
              (Formula.and (Formula.eq (Term.func "c" []) (Term.func "d" []))
                (Formula.atom "Q" []))]
      ⊢₀ Formula.or (Formula.atom "P" [Term.func "d" []]) (Formula.atom "R" []) := by
    have hA := Derives₀.hyp
      [Formula.and (Formula.atom "P" [Term.func "c" []])
        (Formula.and (Formula.eq (Term.func "c" []) (Term.func "d" [])) (Formula.atom "Q" []))]
      _ (List.Mem.head _)
    have hPc := Derives₀.elim_and_l _ _ _ hA
    have hcd := Derives₀.elim_and_l _ _ _ (Derives₀.elim_and_r _ _ _ hA)
    exact Derives₀.intro_or_l _ _ _ (FOL.Eq0.derives0_atom_congr "P" [] [] hcd hPc)
  obtain ⟨C, h1, h2, hS1, hS2⟩ := craig₀ hd
  refine ⟨C, h1, h2, fun p hp => ?_⟩
  obtain ⟨g, hg, hpg⟩ := hS1 p hp
  obtain ⟨g', hg', hpg'⟩ := hS2 p hp
  cases hg with
  | tail _ hm => exact absurd hm List.not_mem_nil
  | head =>
      cases hg' with
      | tail _ hm => exact absurd hm List.not_mem_nil
      | head =>
          -- hpg : "P" = p ∨ (False ∨ "Q" = p) ;  hpg' : "P" = p ∨ "R" = p
          rcases hpg with e | e | e
          · exact e.symm
          · exact e.elim
          · rcases hpg' with e' | e'
            · exact e'.symm
            · exact absurd (e.trans e'.symm) (by decide)

end FOL.Interpolation0

#print axioms FOL.Interpolation0.lk0_refute
#print axioms FOL.Interpolation0.lk0_to_derives0_fin
#print axioms FOL.Interpolation0.lk0_to_lkp
#print axioms FOL.Interpolation0.predF_em
#print axioms FOL.Interpolation0.eqGen_side
#print axioms FOL.Interpolation0.craig_ctx₀
#print axioms FOL.Interpolation0.craig₀
#print axioms FOL.Interpolation0.craig_impl₀
#print axioms FOL.Interpolation0.craig₀_example
