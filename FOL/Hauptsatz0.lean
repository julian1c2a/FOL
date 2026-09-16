/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Sequent0
-- @axiom_system: classical
-- @importance: high

import FOL.Sequent0

/-!
# `FOL.Hauptsatz0` — el andamiaje del **Hauptsatz**, y H3 reducida al CORTE ÚNICO

Quinta pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.9). ⛔ **El Hauptsatz NO está**:
esto es lo que hay que tener **antes** de intentarlo, construido y verificado por partes.

    CutAdm               -- el corte ÚNICO, que es lo que un Hauptsatz demuestra de verdad
    cutElim_of           -- ⭐ CutAdm ⇒ CutElim, DEMOSTRADO
    LKh                  -- el cálculo INDEXADO POR ALTURA
    lkh_mono, lkh_to_lk0, lk0_to_lkh
    liftFormula_subst_le -- ⭐ la conmutación De Bruijn que faltaba en el repo

## ⭐ Lo primero: separar el corte ÚNICO de su clausura

`CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ` es la **clausura** sobre derivaciones. Lo que un Hauptsatz
demuestra es el **corte único**:

    CutAdm : ∀ Γ Δ A, LK₀ Γ (A :: Δ) → LK₀ (A :: Γ) Δ → LK₀ Γ Δ

y `cutElim_of : CutAdm → CutElim` es una inducción de quince líneas sobre `LKc`. ⇒ **H3 se
enuncia ahora sobre el corte único**, que es el objeto sobre el que la literatura razona.

## ⚠️⚠️ Por qué hace falta un cálculo INDEXADO POR ALTURA

La demostración de Gentzen es una **inducción doble**: por fuera sobre el **grado** de la fórmula
de corte, por dentro sobre la **suma de las alturas** de las dos subderivaciones.

⛔ **Y la altura no se puede definir sobre `LK₀`**: vive en `Prop`, así que no hay eliminación
grande y no existe `altura : LK₀ Γ Δ → Nat`. ⇒ hay que **indexarla en el propio inductivo**.

⭐ **Y `struct` se declara PRESERVANDO la altura.** Eso da **debilitamiento, contracción e
intercambio gratis dentro de la inducción**, que es exactamente lo que en la presentación clásica
obliga a pasar por la regla **MIX** en vez del corte. *Una decisión de diseño del inductivo se
come una complicación entera de la prueba clásica.*

## ⭐ La conmutación que faltaba, y está MEDIDO que faltaba

El caso `allR` del lema de sustitución necesita

    liftFormula 0 (substFormula v s f) = substFormula (v+1) (liftTerm 0 s) (liftFormula 0 f)

y, al recurrir bajo el binder, su versión general con `k ≤ v`. El repo tenía **las otras dos
mitades de la familia** y no ésta:

| lema | condición | dónde |
|---|---|---|
| `substFormula_lift_comm` | `k = v` | `FOL/Theorems/Eq.lean` |
| `liftFormula_subst` | `v ≤ k` | `FOL/Lift0.lean` |
| ⭐ `liftFormula_subst_le` | **`k ≤ v`** | **aquí** — faltaba |

⚠️ Vive en este módulo y no en `Theorems/Eq.lean` sólo para no mover un fichero ya medido; es de
la familia de aquél y ahí debería acabar.

## ⬜ Lo que falta para `CutAdm`, con su obstáculo MEDIDO

1. ⬜ **La segunda conmutación**: la forma general de Barendregt
   `substFormula v s (substFormula 0 u f) = substFormula 0 (substTerm v s u) (substFormula (v+1) (liftTerm 0 s) f)`.
   ⛔ **Medido que tampoco está**: `subst_subst_comm_succ` (`Theorems/Eq.lean`) sólo cubre índices
   **adyacentes** (`j+1`/`j`), y el caso `allL` necesita `v` arbitrario. ~90 l., riesgo bajo —
   es gemela de `liftFormula_subst_le`.
2. ⬜ **`lkh_subst`** — el cálculo es cerrado por sustitución, preservando altura. ~150 l.
3. ⬜ **La inducción doble** de `CutAdm`. ~400–600 l., **riesgo alto**. Es la pieza grande.

⚠️ **Y una advertencia sobre el atajo semántico, para que no se intente**: `CutAdm` **no** sale de
`lkc_sound` + `completeness₀`. `completeness₀` devuelve una derivación de **`Derives₀`**, no de
`LK₀`; convertirla exigiría `Derives₀ → LK₀` **sin corte**, que *es* el Hauptsatz. **El círculo se
cierra y no hay atajo.**

## 📏 Footprint

`cutElim_of`, `lkh_mono` y `lkh_to_lk0` **no dependen de ningún axioma**; el resto,
`[propext, Quot.sound]`. **Ni un `Classical.choice`.**
-/

namespace FOL.Hauptsatz0

open FOL.Herbrand0
open FOL.Sequent0

-- ── §1 · El corte ÚNICO, y su clausura ──────────────────────────────────────
def CutAdm : Prop := ∀ (Γ Δ : List Formula) (A : Formula),
  LK₀ Γ (A :: Δ) → LK₀ (A :: Γ) Δ → LK₀ Γ Δ

theorem cutElim_of (h : CutAdm) : CutElim := by
  intro Γ Δ hd
  induction hd with
  | ax Γ Δ A h1 h2 => exact LK₀.ax Γ Δ A h1 h2
  | botL Γ Δ h1 => exact LK₀.botL Γ Δ h1
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
  | eqAx Γ Δ g hg _ ih => exact LK₀.eqAx Γ Δ g hg ih
  | cut Γ Δ A _ _ ih1 ih2 => exact h Γ Δ A ih1 ih2

end FOL.Hauptsatz0

-- ── §2 · El cálculo INDEXADO POR ALTURA ─────────────────────────────────────
-- ⚠️ `LK₀` vive en `Prop`, así que NO se le puede definir una función de altura
-- (no hay eliminación grande). La inducción doble del Hauptsatz necesita la
-- altura ⇒ hay que indexarla en el propio inductivo.
-- ⭐ Y `struct` se declara PRESERVANDO la altura: es lo que da debilitamiento,
-- contracción e intercambio «gratis» dentro de la inducción.
inductive LKh : Nat → List Formula → List Formula → Prop where
  | ax : ∀ n Γ Δ A, A ∈ Γ → A ∈ Δ → LKh n Γ Δ
  | botL : ∀ n Γ Δ, Formula.bottom ∈ Γ → LKh n Γ Δ
  | struct : ∀ n Γ Γ' Δ Δ', LKh n Γ Δ → (∀ x, x ∈ Γ → x ∈ Γ') → (∀ x, x ∈ Δ → x ∈ Δ') →
      LKh n Γ' Δ'
  | implR : ∀ n Γ Δ A B, LKh n (A :: Γ) (B :: Δ) → LKh (n+1) Γ (Formula.impl A B :: Δ)
  | implL : ∀ n Γ Δ A B, LKh n Γ (A :: Δ) → LKh n (B :: Γ) Δ →
      LKh (n+1) (Formula.impl A B :: Γ) Δ
  | andR : ∀ n Γ Δ A B, LKh n Γ (A :: Δ) → LKh n Γ (B :: Δ) → LKh (n+1) Γ (Formula.and A B :: Δ)
  | andL : ∀ n Γ Δ A B, LKh n (A :: B :: Γ) Δ → LKh (n+1) (Formula.and A B :: Γ) Δ
  | orR : ∀ n Γ Δ A B, LKh n Γ (A :: B :: Δ) → LKh (n+1) Γ (Formula.or A B :: Δ)
  | orL : ∀ n Γ Δ A B, LKh n (A :: Γ) Δ → LKh n (B :: Γ) Δ → LKh (n+1) (Formula.or A B :: Γ) Δ
  | allR : ∀ n Γ Δ A, LKh n (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) →
      LKh (n+1) Γ (Formula.forall A :: Δ)
  | allL : ∀ n Γ Δ A t, LKh n (substFormula 0 t A :: Γ) Δ → LKh (n+1) (Formula.forall A :: Γ) Δ
  | exR : ∀ n Γ Δ A t, LKh n Γ (substFormula 0 t A :: Δ) → LKh (n+1) Γ (Formula.ex A :: Δ)
  | exL : ∀ n Γ Δ A, LKh n (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) →
      LKh (n+1) (Formula.ex A :: Γ) Δ
  | eqAx : ∀ n Γ Δ g, FOL.Herbrand0.EqInstance g → LKh n (g :: Γ) Δ → LKh (n+1) Γ Δ

namespace FOL.Hauptsatz0

-- ============================================================
-- §3 · Altura: monotonia y los dos encajes
-- ============================================================

/-- La altura se puede inflar. -/
theorem lkh_mono : ∀ {n : Nat} {Γ Δ : List Formula}, LKh n Γ Δ → ∀ m, n ≤ m → LKh m Γ Δ := by
  intro n Γ Δ h
  induction h with
  | ax n Γ Δ A h1 h2 => intro m _; exact LKh.ax m Γ Δ A h1 h2
  | botL n Γ Δ h1 => intro m _; exact LKh.botL m Γ Δ h1
  | struct n Γ Γ' Δ Δ' _ h1 h2 ih => intro m hm; exact LKh.struct m Γ Γ' Δ Δ' (ih m hm) h1 h2
  | implR n Γ Δ A B _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.implR k Γ Δ A B (ih k (Nat.le_of_succ_le_succ hm))
  | implL n Γ Δ A B _ _ ih1 ih2 =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k =>
          exact LKh.implL k Γ Δ A B (ih1 k (Nat.le_of_succ_le_succ hm))
            (ih2 k (Nat.le_of_succ_le_succ hm))
  | andR n Γ Δ A B _ _ ih1 ih2 =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k =>
          exact LKh.andR k Γ Δ A B (ih1 k (Nat.le_of_succ_le_succ hm))
            (ih2 k (Nat.le_of_succ_le_succ hm))
  | andL n Γ Δ A B _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.andL k Γ Δ A B (ih k (Nat.le_of_succ_le_succ hm))
  | orR n Γ Δ A B _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.orR k Γ Δ A B (ih k (Nat.le_of_succ_le_succ hm))
  | orL n Γ Δ A B _ _ ih1 ih2 =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k =>
          exact LKh.orL k Γ Δ A B (ih1 k (Nat.le_of_succ_le_succ hm))
            (ih2 k (Nat.le_of_succ_le_succ hm))
  | allR n Γ Δ A _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.allR k Γ Δ A (ih k (Nat.le_of_succ_le_succ hm))
  | allL n Γ Δ A t _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.allL k Γ Δ A t (ih k (Nat.le_of_succ_le_succ hm))
  | exR n Γ Δ A t _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.exR k Γ Δ A t (ih k (Nat.le_of_succ_le_succ hm))
  | exL n Γ Δ A _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.exL k Γ Δ A (ih k (Nat.le_of_succ_le_succ hm))
  | eqAx n Γ Δ g hg _ ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.eqAx k Γ Δ g hg (ih k (Nat.le_of_succ_le_succ hm))

theorem lkh_to_lk0 : ∀ {n : Nat} {Γ Δ : List Formula}, LKh n Γ Δ → LK₀ Γ Δ := by
  intro n Γ Δ h
  induction h with
  | ax n Γ Δ A h1 h2 => exact LK₀.ax Γ Δ A h1 h2
  | botL n Γ Δ h1 => exact LK₀.botL Γ Δ h1
  | struct n Γ Γ' Δ Δ' _ h1 h2 ih => exact LK₀.struct Γ Γ' Δ Δ' ih h1 h2
  | implR n Γ Δ A B _ ih => exact LK₀.implR Γ Δ A B ih
  | implL n Γ Δ A B _ _ ih1 ih2 => exact LK₀.implL Γ Δ A B ih1 ih2
  | andR n Γ Δ A B _ _ ih1 ih2 => exact LK₀.andR Γ Δ A B ih1 ih2
  | andL n Γ Δ A B _ ih => exact LK₀.andL Γ Δ A B ih
  | orR n Γ Δ A B _ ih => exact LK₀.orR Γ Δ A B ih
  | orL n Γ Δ A B _ _ ih1 ih2 => exact LK₀.orL Γ Δ A B ih1 ih2
  | allR n Γ Δ A _ ih => exact LK₀.allR Γ Δ A ih
  | allL n Γ Δ A t _ ih => exact LK₀.allL Γ Δ A t ih
  | exR n Γ Δ A t _ ih => exact LK₀.exR Γ Δ A t ih
  | exL n Γ Δ A _ ih => exact LK₀.exL Γ Δ A ih
  | eqAx n Γ Δ g hg _ ih => exact LK₀.eqAx Γ Δ g hg ih

theorem lk0_to_lkh : ∀ {Γ Δ : List Formula}, LK₀ Γ Δ → ∃ n, LKh n Γ Δ := by
  intro Γ Δ h
  induction h with
  | ax Γ Δ A h1 h2 => exact ⟨0, LKh.ax 0 Γ Δ A h1 h2⟩
  | botL Γ Δ h1 => exact ⟨0, LKh.botL 0 Γ Δ h1⟩
  | struct Γ Γ' Δ Δ' _ h1 h2 ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n, LKh.struct n Γ Γ' Δ Δ' hn h1 h2⟩
  | implR Γ Δ A B _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.implR n Γ Δ A B hn⟩
  | implL Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
      exact ⟨max n1 n2 + 1, LKh.implL _ Γ Δ A B
        (lkh_mono h1 _ (Nat.le_max_left _ _)) (lkh_mono h2 _ (Nat.le_max_right _ _))⟩
  | andR Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
      exact ⟨max n1 n2 + 1, LKh.andR _ Γ Δ A B
        (lkh_mono h1 _ (Nat.le_max_left _ _)) (lkh_mono h2 _ (Nat.le_max_right _ _))⟩
  | andL Γ Δ A B _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.andL n Γ Δ A B hn⟩
  | orR Γ Δ A B _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.orR n Γ Δ A B hn⟩
  | orL Γ Δ A B _ _ ih1 ih2 =>
      obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
      exact ⟨max n1 n2 + 1, LKh.orL _ Γ Δ A B
        (lkh_mono h1 _ (Nat.le_max_left _ _)) (lkh_mono h2 _ (Nat.le_max_right _ _))⟩
  | allR Γ Δ A _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.allR n Γ Δ A hn⟩
  | allL Γ Δ A t _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.allL n Γ Δ A t hn⟩
  | exR Γ Δ A t _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.exR n Γ Δ A t hn⟩
  | exL Γ Δ A _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.exL n Γ Δ A hn⟩
  | eqAx Γ Δ g hg _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.eqAx n Γ Δ g hg hn⟩

-- ============================================================
-- §4 · La conmutacion De Bruijn que faltaba
-- ============================================================

-- ⛔ MEDIDO: `FOL/Theorems/Eq.lean` tiene la mitad `v ≤ k` (`liftFormula_subst`) y el caso
-- `k = v` (`substFormula_lift_comm`), pero NO la mitad `k ≤ v`, que es la que el Hauptsatz
-- necesita: el caso `allR` del lema de sustitución recurre con `k+1 ≤ v+1` desde `k = 0`.
mutual
theorem liftTerm_subst_le : ∀ (u : Term) (k v : Nat), k ≤ v → ∀ (s : Term),
    liftTerm k (substTerm v s u) = substTerm (v + 1) (liftTerm k s) (liftTerm k u)
  | .var n, k, v, h, s => by
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · by_cases hk : n < k
        · simp [substTerm, liftTerm, hk,
            show ¬ n = v from by omega, show ¬ n > v from by omega,
            show ¬ n = v + 1 from by omega, show ¬ n > v + 1 from by omega]
        · simp [substTerm, liftTerm, hk,
            show ¬ n = v from by omega, show ¬ n > v from by omega,
            show ¬ n + 1 > v + 1 from by omega]
      · subst heq
        simp [substTerm, liftTerm, show ¬ n < k from by omega]
      · simp [substTerm, liftTerm,
          show ¬ n = v from by omega, show n > v from hgt,
          show ¬ n - 1 < k from by omega, show ¬ n < k from by omega,
          show n + 1 > v + 1 from by omega,
          show n - 1 + 1 = n from by omega]
  | .func f ts, k, v, h, s => by
      show Term.func f (liftTerms k (substTerms v s ts))
            = Term.func f (substTerms (v + 1) (liftTerm k s) (liftTerms k ts))
      rw [liftTerms_subst_le ts k v h s]

theorem liftTerms_subst_le : ∀ (us : List Term) (k v : Nat), k ≤ v → ∀ (s : Term),
    liftTerms k (substTerms v s us) = substTerms (v + 1) (liftTerm k s) (liftTerms k us)
  | [], _, _, _, _ => rfl
  | u :: us, k, v, h, s => by
      show liftTerm k (substTerm v s u) :: liftTerms k (substTerms v s us)
            = substTerm (v + 1) (liftTerm k s) (liftTerm k u)
              :: substTerms (v + 1) (liftTerm k s) (liftTerms k us)
      rw [liftTerm_subst_le u k v h s, liftTerms_subst_le us k v h s]
end

theorem liftFormula_subst_le : ∀ (f : Formula) (k v : Nat), k ≤ v → ∀ (s : Term),
    liftFormula k (substFormula v s f) = substFormula (v + 1) (liftTerm k s) (liftFormula k f) := by
  intro f
  induction f with
  | bottom => intro _ _ _ _; rfl
  | atom p ts => intro k v h s; simp only [liftFormula, substFormula, liftTerms_subst_le ts k v h s]
  | eq t u => intro k v h s; simp only [liftFormula, substFormula, liftTerm_subst_le _ k v h s]
  | impl a b iha ihb =>
      intro k v h s; simp only [liftFormula, substFormula, iha k v h s, ihb k v h s]
  | and a b iha ihb =>
      intro k v h s; simp only [liftFormula, substFormula, iha k v h s, ihb k v h s]
  | or a b iha ihb =>
      intro k v h s; simp only [liftFormula, substFormula, iha k v h s, ihb k v h s]
  | «forall» a ih =>
      intro k v h s
      simp only [liftFormula, substFormula]
      rw [ih (k + 1) (v + 1) (Nat.succ_le_succ h) (liftTerm 0 s),
          liftTerm_comm_zero s k]
  | ex a ih =>
      intro k v h s
      simp only [liftFormula, substFormula]
      rw [ih (k + 1) (v + 1) (Nat.succ_le_succ h) (liftTerm 0 s),
          liftTerm_comm_zero s k]

end FOL.Hauptsatz0

#print axioms FOL.Hauptsatz0.cutElim_of
#print axioms LKh.rec
#print axioms FOL.Hauptsatz0.lkh_mono
#print axioms FOL.Hauptsatz0.lkh_to_lk0
#print axioms FOL.Hauptsatz0.lk0_to_lkh
#print axioms FOL.Hauptsatz0.liftFormula_subst_le
