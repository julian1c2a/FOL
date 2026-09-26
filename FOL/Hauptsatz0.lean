/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Sequent0, FOL.NDtoLK0
-- @axiom_system: classical
-- @importance: high

import FOL.Sequent0
import FOL.NDtoLK0

/-!
# `FOL.Hauptsatz0` — 🏁🏁🏁 **EL HAUPTSATZ**, y con él **H3**

Sexta y última pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.9‑§5.11).
⭐ **El corte es ADMISIBLE en `LK₀`**, y de ahí `CutElim`, la extracción de Herbrand y el
**teorema de Herbrand incondicional**.

    §1  CutAdm · cutElim_of    -- el corte ÚNICO, y CutAdm ⇒ CutElim
    §2  LKh                    -- el cálculo INDEXADO POR ALTURA (14 ctors)
    §3  lkh_mono · lkh_to_lk0 · lk0_to_lkh
    §4  liftFormula_subst_le   -- conmutación De Bruijn `k ≤ v`
    §5  substFormula_subst_le  -- Barendregt general `w ≤ v`
    §6  lkh_subst              -- cerrado por SUSTITUCIÓN, preservando altura
    §7  deg · lkh_lift         -- el GRADO, y cerrado por LEVANTAMIENTO
    §8  ⭐⭐⭐ hauptsatz · cut_elimination · herbrand_extraction · herbrand
    §9  ⭐ EqPropCert · derives0_qf_iff  -- el fragmento SIN CUANTIFICADORES, caracterizado

## ⭐ §9: lo que el fragmento sin cuantificadores ES (y lo que no)

Es FALSO que el fragmento sin cuantificadores de `Derives₀` sea «decidible por tabla de verdad»:
`[] ⊢₀ c ≐ c` por `refl`, y `peval` trata `≐` como un átomo. Lo CIERTO es `derives0_qf_iff`:
un secuente sin cuantificadores es derivable **sii** su conclusión es consecuencia proposicional
del contexto más una lista finita `E` de instancias de la igualdad. La ⟹ es `lk0_herbrand` con
`φ := ⊥` sobre la derivación SIN CORTE; la ⟸ no necesita ni la hipótesis `QuantFree`.
⚠️ **Caracteriza, NO decide**: `E` no tiene cota. Y la `E` sin cota **no vuelve vacuo** el
enunciado (el precedente es el Maehara relativizado a `E` de RPP‑067, que NO está en ningún árbol;
su contraejemplo es `../ROBINSON_PlusPlus/sondeos/CraigEqVacuo.lean`): la valuación constante `true` satisface toda
`EqInstance` (`peval_true_eqInstance`), luego `EqPropCert [] ⊥ E` es falso para toda `E` — hay un
`example` que lo compila, y otro que saca de ahí `Not ([] ⊢₀ ⊥)`.

## ⛔⛔ La corrección de diseño: `struct` TIENE que subir la altura

ADR‑050 declaró `struct` **preservando** la altura, y ahí mismo dejó escrito que *«si la inducción
doble no cierra, el primer sospechoso es `struct`»*. **Lo era**: con la altura preservada, el caso
`struct` recurre sobre una premisa de la **misma** altura ⇒ la medida no decrece y la inducción no
está bien fundada. Y no hay salida por inducción estructural, porque la prueba también recurre
sobre el lado **derecho**, que no es subderivación del izquierdo.

⭐ **Y no se pierde nada**: el debilitamiento/contracción/intercambio «gratis» que evita la regla
**MIX** no venía de la altura de `struct`, sino de que el enunciado del corte pide **PERTENENCIA**
(`Or (x = A) (x ∈ Δ)`) en vez de la forma `A :: Δ`. 🔑 *Lo que mata a MIX es el enunciado, no el
constructor.* El cambio costó **tres ediciones** y `lkh_subst` no se movió.

## ⭐⭐⭐ La arquitectura: `LeftPrin`, y por qué NO hace falta la inducción doble

La presentación clásica es una inducción doble —grado × **suma** de alturas— con un análisis de
casos sobre las dos últimas reglas: 5 conectivas × 14 casos de la otra derivación.

Aquí se hace en **dos pasadas independientes de 14 casos**:

* **`cutPrinAux` (§8.5)** analiza `D2` **una sola vez**, induciendo sobre `n`. Lo que necesita del
  lado izquierdo es un dato **uniforme**, `LeftPrin A Γ Δ`: las premisas de la regla derecha
  principal de `A`, empaquetadas por conectiva. Con `leftPrin_mono` y `leftPrin_lift` ese dato
  viaja a los contextos nuevos que cada permutación de `D2` crea.
* **`cutLeftAux` (§8.6)** analiza `D1`, induciendo sobre `m`. Sus únicos casos que tocan el lado
  derecho son los principales, y ésos los delega en `cutPrinAux`.

⇒ **la inducción sobre `m + n` no aparece**: basta `m` por fuera y `n` dentro de `cutPrinAux`.
🔑 *Cuando dos análisis de casos se cruzan, lo que los desacopla es encontrar el DATO que uno le
pasa al otro.*

⭐ Y hay un dividendo: en cada regla derecha de `D1` **la misma llamada recursiva sirve para las dos
ramas** — es `LeftPrin A Γ Δ` si la fórmula principal es `A`, y la premisa de la regla si no lo es.

⛔ `LeftPrin` es `False` para `⊥`, átomos e igualdades — no hay regla derecha que las introduzca —,
y eso **cierra gratis** el caso `botL` de `D2` con `A = ⊥`, que en otras presentaciones hay que
argumentar aparte.

## ⭐ Las conmutaciones De Bruijn, y dónde paga cada una

| lema | condición | dónde |
|---|---|---|
| `substFormula_lift_comm` | `k = v` | `FOL/Theorems/Eq.lean` |
| `subst_subst_comm_succ` | índices **adyacentes** | `FOL/Theorems/Eq.lean` |
| `liftFormula_subst` | `v ≤ k` | `FOL/Lift0.lean` |
| ⭐ `liftFormula_subst_le` | **`k ≤ v`** | **§4** — faltaba |
| ⭐ `substFormula_subst_le` | **`w ≤ v`**, general | **§5** — faltaba |

`lkh_subst` (§6) paga en `allL`/`exR` del corte principal sobre `∀`/`∃`; `lkh_lift` (§7) paga cada
vez que una regla `allR`/`exL` **del otro lado** obliga a levantar la derivación entera y la propia
fórmula de corte.

⚠️ **Y el atajo semántico seguía sin existir**, como estaba escrito: `completeness₀` devuelve
`Derives₀`, no `LK₀` sin corte. Esto se ha pagado **sintácticamente**, que era la única vía.

## 📏 Footprint

De lo que este módulo imprime: `cutElim_of`, `LKh.rec`, `lkh_mono`, `lkh_to_lk0`,
`eqInstance_subst`, `eqInstance_lift` y `peval_true_eqInstance` **sin ningún axioma**; `lk0_to_lkh`
sólo `[propext]`; el resto —incluidos **`hauptsatz`**, `cut_elimination`, `herbrand_extraction`,
**`herbrand`** y **`derives0_qf_iff`**— `[propext, Quot.sound]`. **Ni un `Classical.choice`, ni un
axioma del proyecto.** (Lo que no lleva `#print axioms` no tiene footprint afirmado aquí.)
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
-- ⛔⛔ CORREGIDO (ADR-052): `struct` SUBE la altura. En ADR-050 se declaró
-- PRESERVÁNDOLA, y ahí mismo quedó escrito que «si la inducción doble no cierra,
-- el primer sospechoso es struct». Lo era: con la altura preservada, el caso
-- `struct` de la inducción interna recurre sobre una premisa de la MISMA altura
-- ⇒ `m + n` no decrece y la inducción NO está bien fundada.
-- ⭐ Y no se pierde nada: el debilitamiento/contracción/intercambio «gratis» que
-- evita la regla MIX no venía de la altura de `struct`, sino de que el enunciado
-- del corte pide PERTENENCIA (`x = A ∨ x ∈ Δ`) y no la forma `A :: Δ`. §7.
inductive LKh : Nat → List Formula → List Formula → Prop where
  | ax : ∀ n Γ Δ A, A ∈ Γ → A ∈ Δ → LKh n Γ Δ
  | botL : ∀ n Γ Δ, Formula.bottom ∈ Γ → LKh n Γ Δ
  | struct : ∀ n Γ Γ' Δ Δ', LKh n Γ Δ → (∀ x, x ∈ Γ → x ∈ Γ') → (∀ x, x ∈ Δ → x ∈ Δ') →
      LKh (n+1) Γ' Δ'
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

open FOL.Herbrand0
open FOL.Sequent0

-- ============================================================
-- §3 · Altura: monotonia y los dos encajes
-- ============================================================

/-- La altura se puede inflar. -/
theorem lkh_mono : ∀ {n : Nat} {Γ Δ : List Formula}, LKh n Γ Δ → ∀ m, n ≤ m → LKh m Γ Δ := by
  intro n Γ Δ h
  induction h with
  | ax n Γ Δ A h1 h2 => intro m _; exact LKh.ax m Γ Δ A h1 h2
  | botL n Γ Δ h1 => intro m _; exact LKh.botL m Γ Δ h1
  | struct n Γ Γ' Δ Δ' _ h1 h2 ih =>
      intro m hm
      cases m with
      | zero => exact absurd hm (Nat.not_succ_le_zero n)
      | succ k => exact LKh.struct k Γ Γ' Δ Δ' (ih k (Nat.le_of_succ_le_succ hm)) h1 h2
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
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, LKh.struct n Γ Γ' Δ Δ' hn h1 h2⟩
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

-- ============================================================
-- §5 · Barendregt general: la SEGUNDA conmutacion que faltaba
-- ============================================================

-- ⛔ MEDIDO en ADR-050: `subst_subst_comm_succ` sólo cubre índices ADYACENTES (`j+1`/`j`).
-- El caso `allL` del lema de sustitución necesita `v` arbitrario con `w ≤ v`.
mutual
theorem substTerm_subst_le : ∀ (t : Term) (w v : Nat), w ≤ v → ∀ (s u : Term),
    substTerm v s (substTerm w u t)
      = substTerm w (substTerm v s u) (substTerm (v + 1) (liftTerm w s) t)
  | .var n, w, v, h, s, u => by
      rcases Nat.lt_trichotomy n w with hlt | heq | hgt
      · simp [substTerm,
          show ¬ n = w from by omega, show ¬ n > w from by omega,
          show ¬ n = v from by omega, show ¬ n > v from by omega,
          show ¬ n = v + 1 from by omega, show ¬ n > v + 1 from by omega]
      · subst heq
        simp [substTerm,
          show ¬ n = v + 1 from by omega, show ¬ n > v + 1 from by omega]
      · rcases Nat.lt_trichotomy (n - 1) v with h2 | h2 | h2
        · simp [substTerm,
            show ¬ n = w from by omega, show n > w from hgt,
            show ¬ n - 1 = v from by omega, show ¬ n - 1 > v from by omega,
            show ¬ n = v + 1 from by omega, show ¬ n > v + 1 from by omega]
        · have hn : n = v + 1 := by omega
          subst hn
          simp only [substTerm,
            if_neg (show ¬ v + 1 = w from by omega),
            if_pos (show v + 1 > w from by omega)]
          simp only [show v + 1 - 1 = v from by omega]
          exact (substTerm_liftTerm s w (substTerm v s u)).symm
        · simp [substTerm,
            show ¬ n = w from by omega, show n > w from hgt,
            show ¬ n - 1 = v from by omega, show n - 1 > v from h2,
            show ¬ n = v + 1 from by omega, show n > v + 1 from by omega,
            show ¬ n - 1 = w from by omega, show n - 1 > w from by omega]
  | .func f ts, w, v, h, s, u => by
      show Term.func f (substTerms v s (substTerms w u ts))
            = Term.func f (substTerms w (substTerm v s u) (substTerms (v + 1) (liftTerm w s) ts))
      rw [substTerms_subst_le ts w v h s u]

theorem substTerms_subst_le : ∀ (ts : List Term) (w v : Nat), w ≤ v → ∀ (s u : Term),
    substTerms v s (substTerms w u ts)
      = substTerms w (substTerm v s u) (substTerms (v + 1) (liftTerm w s) ts)
  | [], _, _, _, _, _ => rfl
  | t :: ts, w, v, h, s, u => by
      show substTerm v s (substTerm w u t) :: substTerms v s (substTerms w u ts)
            = substTerm w (substTerm v s u) (substTerm (v + 1) (liftTerm w s) t)
              :: substTerms w (substTerm v s u) (substTerms (v + 1) (liftTerm w s) ts)
      rw [substTerm_subst_le t w v h s u, substTerms_subst_le ts w v h s u]
end

/-- ⭐ **El lema de sustitución de Barendregt, en su forma general** (`w ≤ v`). -/
theorem substFormula_subst_le : ∀ (f : Formula) (w v : Nat), w ≤ v → ∀ (s u : Term),
    substFormula v s (substFormula w u f)
      = substFormula w (substTerm v s u) (substFormula (v + 1) (liftTerm w s) f) := by
  intro f
  induction f with
  | bottom => intro _ _ _ _ _; rfl
  | atom p ts =>
      intro w v h s u; simp only [substFormula, substTerms_subst_le ts w v h s u]
  | eq t1 t2 =>
      intro w v h s u; simp only [substFormula, substTerm_subst_le _ w v h s u]
  | impl a b iha ihb =>
      intro w v h s u; simp only [substFormula, iha w v h s u, ihb w v h s u]
  | and a b iha ihb =>
      intro w v h s u; simp only [substFormula, iha w v h s u, ihb w v h s u]
  | or a b iha ihb =>
      intro w v h s u; simp only [substFormula, iha w v h s u, ihb w v h s u]
  | «forall» a ih =>
      intro w v h s u
      simp only [substFormula]
      rw [ih (w + 1) (v + 1) (Nat.succ_le_succ h) (liftTerm 0 s) (liftTerm 0 u),
          ← liftTerm_subst_le u 0 v (Nat.zero_le _) s,
          liftTerm_comm_zero s w]
  | ex a ih =>
      intro w v h s u
      simp only [substFormula]
      rw [ih (w + 1) (v + 1) (Nat.succ_le_succ h) (liftTerm 0 s) (liftTerm 0 u),
          ← liftTerm_subst_le u 0 v (Nat.zero_le _) s,
          liftTerm_comm_zero s w]

-- ============================================================
-- §6 · ⭐⭐ El calculo es CERRADO POR SUSTITUCION, preservando altura
-- ============================================================

-- ── las instancias de igualdad son cerradas por sustitución ─────────────────
theorem eqInstance_subst {g : Formula} (hg : EqInstance g) (v : Nat) (t : Term) :
    EqInstance (substFormula v t g) := by
  cases hg with
  | refl s => exact EqInstance.refl (substTerm v t s)
  | symm a b => exact EqInstance.symm (substTerm v t a) (substTerm v t b)
  | trans a b c => exact EqInstance.trans (substTerm v t a) (substTerm v t b) (substTerm v t c)
  | func p pre post a b =>
      simp only [eqFuncAx, substFormula, substTerm, substTerms_append]
      exact EqInstance.func p (substTerms v t pre) (substTerms v t post)
        (substTerm v t a) (substTerm v t b)
  | atom p pre post a b =>
      simp only [eqAtomAx, substFormula, substTerms_append]
      exact EqInstance.atom p (substTerms v t pre) (substTerms v t post)
        (substTerm v t a) (substTerm v t b)

-- ── el levantamiento conmuta con la sustitución, a nivel de LISTA ───────────
theorem map_lift_subst (v : Nat) (t : Term) : ∀ Γ : List Formula,
    (Γ.map (liftFormula 0)).map (substFormula (v + 1) (liftTerm 0 t))
      = (Γ.map (substFormula v t)).map (liftFormula 0)
  | [] => rfl
  | g :: Γ => by
      show substFormula (v + 1) (liftTerm 0 t) (liftFormula 0 g)
             :: (Γ.map (liftFormula 0)).map (substFormula (v + 1) (liftTerm 0 t))
           = liftFormula 0 (substFormula v t g) :: (Γ.map (substFormula v t)).map (liftFormula 0)
      rw [← liftFormula_subst_le g 0 v (Nat.zero_le _) t, map_lift_subst v t Γ]

theorem map_sub {Γ Γ' : List Formula} (σ : Formula → Formula) (hs : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ Γ.map σ → x ∈ Γ'.map σ := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
  exact heq ▸ List.mem_map_of_mem (hs y hy)

-- ── ⭐⭐ EL CÁLCULO ES CERRADO POR SUSTITUCIÓN, PRESERVANDO ALTURA ───────────
theorem lkh_subst : ∀ {n : Nat} {Γ Δ : List Formula}, LKh n Γ Δ → ∀ (v : Nat) (t : Term),
    LKh n (Γ.map (substFormula v t)) (Δ.map (substFormula v t)) := by
  intro n Γ Δ h
  induction h with
  | ax n Γ Δ A h1 h2 =>
      intro v t
      exact LKh.ax n _ _ (substFormula v t A) (List.mem_map_of_mem h1) (List.mem_map_of_mem h2)
  | botL n Γ Δ h1 =>
      intro v t
      refine LKh.botL n _ _ ?_
      have hx := List.mem_map_of_mem (f := substFormula v t) h1
      simpa only [substFormula] using hx
  | struct n Γ Γ' Δ Δ' _ hs1 hs2 ih =>
      intro v t
      exact LKh.struct n _ _ _ _ (ih v t) (map_sub _ hs1) (map_sub _ hs2)
  | implR n Γ Δ A B _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.implR n _ _ _ _ (by simpa only [List.map_cons] using ih v t)
  | implL n Γ Δ A B _ _ ih1 ih2 =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.implL n _ _ _ _ (by simpa only [List.map_cons] using ih1 v t)
        (by simpa only [List.map_cons] using ih2 v t)
  | andR n Γ Δ A B _ _ ih1 ih2 =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.andR n _ _ _ _ (by simpa only [List.map_cons] using ih1 v t)
        (by simpa only [List.map_cons] using ih2 v t)
  | andL n Γ Δ A B _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.andL n _ _ _ _ (by simpa only [List.map_cons] using ih v t)
  | orR n Γ Δ A B _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.orR n _ _ _ _ (by simpa only [List.map_cons] using ih v t)
  | orL n Γ Δ A B _ _ ih1 ih2 =>
      intro v t
      simp only [List.map_cons, substFormula]
      exact LKh.orL n _ _ _ _ (by simpa only [List.map_cons] using ih1 v t)
        (by simpa only [List.map_cons] using ih2 v t)
  -- ⭐ los dos casos que CAMBIAN EL ENTORNO
  | allR n Γ Δ A _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      refine LKh.allR n _ _ _ ?_
      have hx := ih (v + 1) (liftTerm 0 t)
      simp only [List.map_cons] at hx
      rw [map_lift_subst v t Γ, map_lift_subst v t Δ] at hx
      exact hx
  | exL n Γ Δ A _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      refine LKh.exL n _ _ _ ?_
      have hx := ih (v + 1) (liftTerm 0 t)
      simp only [List.map_cons] at hx
      rw [map_lift_subst v t Γ, map_lift_subst v t Δ] at hx
      exact hx
  -- ⭐ los dos que instancian: aquí paga Barendregt
  | allL n Γ Δ A s _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      refine LKh.allL n _ _ _ (substTerm v t s) ?_
      have hx := ih v t
      simp only [List.map_cons] at hx
      rw [substFormula_subst_le A 0 v (Nat.zero_le _) t s] at hx
      exact hx
  | exR n Γ Δ A s _ ih =>
      intro v t
      simp only [List.map_cons, substFormula]
      refine LKh.exR n _ _ _ (substTerm v t s) ?_
      have hx := ih v t
      simp only [List.map_cons] at hx
      rw [substFormula_subst_le A 0 v (Nat.zero_le _) t s] at hx
      exact hx
  | eqAx n Γ Δ g hg _ ih =>
      intro v t
      refine LKh.eqAx n _ _ (substFormula v t g) (eqInstance_subst hg v t) ?_
      have hx := ih v t
      simp only [List.map_cons] at hx
      exact hx

-- ── §7.1 · el GRADO ─────────────────────────────────────────────────────────
-- ⭐ Con SUMA y no `max`: las tres desigualdades que hace falta salen sin tocar
-- la aritmética de `max`, y cualquier medida monótona sirve.
def deg : Formula → Nat
  | .bottom => 0
  | .atom _ _ => 0
  | .eq _ _ => 0
  | .impl a b => deg a + deg b + 1
  | .and a b => deg a + deg b + 1
  | .or a b => deg a + deg b + 1
  | .forall a => deg a + 1
  | .ex a => deg a + 1

theorem deg_subst : ∀ (f : Formula) (v : Nat) (t : Term), deg (substFormula v t f) = deg f := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro _ _; rfl
  | eq a b => intro _ _; rfl
  | impl a b iha ihb => intro v t; simp only [substFormula, deg, iha, ihb]
  | and a b iha ihb => intro v t; simp only [substFormula, deg, iha, ihb]
  | or a b iha ihb => intro v t; simp only [substFormula, deg, iha, ihb]
  | «forall» a ih => intro v t; simp only [substFormula, deg, ih]
  | ex a ih => intro v t; simp only [substFormula, deg, ih]

theorem deg_lift : ∀ (f : Formula) (k : Nat), deg (liftFormula k f) = deg f := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro _; rfl
  | eq a b => intro _; rfl
  | impl a b iha ihb => intro k; simp only [liftFormula, deg, iha, ihb]
  | and a b iha ihb => intro k; simp only [liftFormula, deg, iha, ihb]
  | or a b iha ihb => intro k; simp only [liftFormula, deg, iha, ihb]
  | «forall» a ih => intro k; simp only [liftFormula, deg, ih]
  | ex a ih => intro k; simp only [liftFormula, deg, ih]

-- ── §7.2 · las instancias de igualdad son cerradas por LEVANTAMIENTO ─────────
theorem eqInstance_lift {g : Formula} (hg : EqInstance g) (k : Nat) :
    EqInstance (liftFormula k g) := by
  cases hg with
  | refl s => exact EqInstance.refl (liftTerm k s)
  | symm a b => exact EqInstance.symm (liftTerm k a) (liftTerm k b)
  | trans a b c => exact EqInstance.trans (liftTerm k a) (liftTerm k b) (liftTerm k c)
  | func p pre post a b =>
      simp only [eqFuncAx, liftFormula, liftTerm, FOL.Derives2.liftTerms_append]
      exact EqInstance.func p (liftTerms k pre) (liftTerms k post) (liftTerm k a) (liftTerm k b)
  | atom p pre post a b =>
      simp only [eqAtomAx, liftFormula, FOL.Derives2.liftTerms_append]
      exact EqInstance.atom p (liftTerms k pre) (liftTerms k post) (liftTerm k a) (liftTerm k b)

-- ── §7.3 · ⭐⭐ EL CÁLCULO ES CERRADO POR LEVANTAMIENTO, PRESERVANDO ALTURA ───
theorem lkh_lift : ∀ {n : Nat} {Γ Δ : List Formula}, LKh n Γ Δ → ∀ (k : Nat),
    LKh n (Γ.map (liftFormula k)) (Δ.map (liftFormula k)) := by
  intro n Γ Δ h
  induction h with
  | ax n Γ Δ A h1 h2 =>
      intro k
      exact LKh.ax n _ _ (liftFormula k A) (List.mem_map_of_mem h1) (List.mem_map_of_mem h2)
  | botL n Γ Δ h1 =>
      intro k
      refine LKh.botL n _ _ ?_
      have hx := List.mem_map_of_mem (f := liftFormula k) h1
      simpa only [liftFormula] using hx
  | struct n Γ Γ' Δ Δ' _ hs1 hs2 ih =>
      intro k
      exact LKh.struct n _ _ _ _ (ih k) (map_sub _ hs1) (map_sub _ hs2)
  | implR n Γ Δ A B _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.implR n _ _ _ _ (by simpa only [List.map_cons] using ih k)
  | implL n Γ Δ A B _ _ ih1 ih2 =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.implL n _ _ _ _ (by simpa only [List.map_cons] using ih1 k)
        (by simpa only [List.map_cons] using ih2 k)
  | andR n Γ Δ A B _ _ ih1 ih2 =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.andR n _ _ _ _ (by simpa only [List.map_cons] using ih1 k)
        (by simpa only [List.map_cons] using ih2 k)
  | andL n Γ Δ A B _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.andL n _ _ _ _ (by simpa only [List.map_cons] using ih k)
  | orR n Γ Δ A B _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.orR n _ _ _ _ (by simpa only [List.map_cons] using ih k)
  | orL n Γ Δ A B _ _ ih1 ih2 =>
      intro k
      simp only [List.map_cons, liftFormula]
      exact LKh.orL n _ _ _ _ (by simpa only [List.map_cons] using ih1 k)
        (by simpa only [List.map_cons] using ih2 k)
  -- ⭐ los dos que CAMBIAN EL ENTORNO: el índice sube a k+1 y hay que conmutar los mapas
  | allR n Γ Δ A _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      refine LKh.allR n _ _ _ ?_
      have hx := ih (k + 1)
      simp only [List.map_cons] at hx
      rw [← FOL.Lift0.map_lift_lift k Γ, ← FOL.Lift0.map_lift_lift k Δ] at hx
      exact hx
  | exL n Γ Δ A _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      refine LKh.exL n _ _ _ ?_
      have hx := ih (k + 1)
      simp only [List.map_cons] at hx
      rw [← FOL.Lift0.map_lift_lift k Γ, ← FOL.Lift0.map_lift_lift k Δ] at hx
      exact hx
  -- ⭐ los dos que INSTANCIAN: aquí paga `liftFormula_subst` (la mitad `v ≤ k`)
  | allL n Γ Δ A t _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      refine LKh.allL n _ _ _ (liftTerm k t) ?_
      have hx := ih k
      simp only [List.map_cons] at hx
      rw [FOL.Lift0.liftFormula_subst A 0 k (Nat.zero_le _) t] at hx
      exact hx
  | exR n Γ Δ A t _ ih =>
      intro k
      simp only [List.map_cons, liftFormula]
      refine LKh.exR n _ _ _ (liftTerm k t) ?_
      have hx := ih k
      simp only [List.map_cons] at hx
      rw [FOL.Lift0.liftFormula_subst A 0 k (Nat.zero_le _) t] at hx
      exact hx
  | eqAx n Γ Δ g hg _ ih =>
      intro k
      refine LKh.eqAx n _ _ (liftFormula k g) (eqInstance_lift hg k) ?_
      have hx := ih k
      simp only [List.map_cons] at hx
      exact hx

-- ── §8.1 · aritmética de pertenencia, que es lo que más se repite ────────────
-- ⚠️ `Or` explícito en todo el fichero: `∨` se parsea como `Formula.or` (trampa §12).
theorem sub_cons {Γ Γ' : List Formula} (b : Formula) (h : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ b :: Γ → x ∈ b :: Γ' := by
  intro x hx
  cases hx with
  | head => exact List.Mem.head _
  | tail _ hm => exact List.Mem.tail _ (h _ hm)

theorem sub_wk {Γ Γ' : List Formula} (b : Formula) (h : ∀ x, x ∈ Γ → x ∈ Γ') :
    ∀ x, x ∈ Γ → x ∈ b :: Γ' := fun x hx => List.Mem.tail _ (h x hx)

theorem sub_drop {Δ : List Formula} {b : Formula} (h : b ∈ Δ) : ∀ x, x ∈ b :: Δ → x ∈ Δ := by
  intro x hx
  cases hx with
  | head => exact h
  | tail _ hm => exact hm

theorem swap_cons (a b : Formula) (Γ : List Formula) : ∀ x, x ∈ a :: b :: Γ → x ∈ b :: a :: Γ := by
  intro x hx
  cases hx with
  | head => exact List.Mem.tail _ (List.Mem.head _)
  | tail _ h =>
      cases h with
      | head => exact List.Mem.head _
      | tail _ h2 => exact List.Mem.tail _ (List.Mem.tail _ h2)

theorem sub_refl (Γ : List Formula) : ∀ x, x ∈ Γ → x ∈ Γ := fun _ h => h

theorem subA_cons {A : Formula} {Δ Δ' : List Formula} (b : Formula)
    (h : ∀ x, x ∈ Δ → Or (x = A) (x ∈ Δ')) :
    ∀ x, x ∈ b :: Δ → Or (x = A) (x ∈ b :: Δ') := by
  intro x hx
  cases hx with
  | head => exact Or.inr (List.Mem.head _)
  | tail _ hm => exact (h _ hm).imp id (List.Mem.tail _)

theorem subA_wk {A : Formula} {Δ Δ' : List Formula} (b : Formula)
    (h : ∀ x, x ∈ Δ → Or (x = A) (x ∈ Δ')) : ∀ x, x ∈ Δ → Or (x = A) (x ∈ b :: Δ') :=
  fun x hx => (h x hx).imp id (List.Mem.tail _)

theorem mem_tl {Γ : List Formula} {b : Formula} {P : Formula → Prop}
    (h : ∀ x, x ∈ b :: Γ → P x) : ∀ x, x ∈ Γ → P x :=
  fun x hx => h x (List.Mem.tail _ hx)

theorem mapA_sub {A : Formula} {Δ Δ' : List Formula} (k : Nat)
    (h : ∀ x, x ∈ Δ → Or (x = A) (x ∈ Δ')) :
    ∀ x, x ∈ Δ.map (liftFormula k) →
      Or (x = liftFormula k A) (x ∈ Δ'.map (liftFormula k)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (h y hy).imp (fun he => by rw [he]) (fun hm => List.mem_map_of_mem hm)

-- ── §8.2 · `LK₀` es cerrado por levantamiento y sustitución ──────────────────
theorem lk0_lift {Γ Δ : List Formula} (h : LK₀ Γ Δ) (k : Nat) :
    LK₀ (Γ.map (liftFormula k)) (Δ.map (liftFormula k)) := by
  obtain ⟨n, hn⟩ := lk0_to_lkh h
  exact lkh_to_lk0 (lkh_lift hn k)

theorem lk0_subst {Γ Δ : List Formula} (h : LK₀ Γ Δ) (v : Nat) (t : Term) :
    LK₀ (Γ.map (substFormula v t)) (Δ.map (substFormula v t)) := by
  obtain ⟨n, hn⟩ := lk0_to_lkh h
  exact lkh_to_lk0 (lkh_subst hn v t)

theorem map_subst_lift (t : Term) : ∀ Γ : List Formula,
    (Γ.map (liftFormula 0)).map (substFormula 0 t) = Γ
  | [] => rfl
  | g :: Γ => by
      show substFormula 0 t (liftFormula 0 g) :: (Γ.map (liftFormula 0)).map (substFormula 0 t)
           = g :: Γ
      rw [FOL.substFormula_liftFormula g 0 t, map_subst_lift t Γ]

-- ── §8.3 · ⭐⭐ `LeftPrin` ────────────────────────────────────────────────────
-- Lo que aporta el lado IZQUIERDO cuando su última regla es la regla DERECHA
-- principal de `A`. ⭐ Empaquetarlo en UN dato uniforme es lo que permite
-- analizar `D2` UNA sola vez en vez de una por conectiva (1 pasada de 14 casos
-- en lugar de 5).
def LeftPrin : Formula → List Formula → List Formula → Prop
  | Formula.impl b c, Γ, Δ => LK₀ (b :: Γ) (c :: Δ)
  | Formula.and b c, Γ, Δ => And (LK₀ Γ (b :: Δ)) (LK₀ Γ (c :: Δ))
  | Formula.or b c, Γ, Δ => LK₀ Γ (b :: c :: Δ)
  | Formula.forall b, Γ, Δ => LK₀ (Γ.map (liftFormula 0)) (b :: Δ.map (liftFormula 0))
  | Formula.ex b, Γ, Δ => ∃ t, LK₀ Γ (substFormula 0 t b :: Δ)
  | _, _, _ => False

theorem leftPrin_close : ∀ (A : Formula) (Γ Δ : List Formula),
    LeftPrin A Γ Δ → LK₀ Γ (A :: Δ)
  | Formula.bottom, _, _, h => h.elim
  | Formula.atom _ _, _, _, h => h.elim
  | Formula.eq _ _, _, _, h => h.elim
  | Formula.impl b c, Γ, Δ, h => LK₀.implR Γ Δ b c h
  | Formula.and b c, Γ, Δ, h => LK₀.andR Γ Δ b c h.1 h.2
  | Formula.or b c, Γ, Δ, h => LK₀.orR Γ Δ b c h
  | Formula.forall b, Γ, Δ, h => LK₀.allR Γ Δ b h
  | Formula.ex b, Γ, Δ, h => h.elim (fun t ht => LK₀.exR Γ Δ b t ht)

theorem leftPrin_mono : ∀ (A : Formula) {Γ Γ' Δ Δ' : List Formula},
    LeftPrin A Γ Δ → (∀ x, x ∈ Γ → x ∈ Γ') → (∀ x, x ∈ Δ → x ∈ Δ') → LeftPrin A Γ' Δ'
  | Formula.bottom, _, _, _, _, h, _, _ => h.elim
  | Formula.atom _ _, _, _, _, _, h, _, _ => h.elim
  | Formula.eq _ _, _, _, _, _, h, _, _ => h.elim
  | Formula.impl b c, Γ, Γ', Δ, Δ', h, s1, s2 =>
      LK₀.struct (b :: Γ) (b :: Γ') (c :: Δ) (c :: Δ') h (sub_cons b s1) (sub_cons c s2)
  | Formula.and b c, Γ, Γ', Δ, Δ', h, s1, s2 =>
      ⟨LK₀.struct Γ Γ' (b :: Δ) (b :: Δ') h.1 s1 (sub_cons b s2),
       LK₀.struct Γ Γ' (c :: Δ) (c :: Δ') h.2 s1 (sub_cons c s2)⟩
  | Formula.or b c, Γ, Γ', Δ, Δ', h, s1, s2 =>
      LK₀.struct Γ Γ' (b :: c :: Δ) (b :: c :: Δ') h s1 (sub_cons b (sub_cons c s2))
  | Formula.forall b, _, _, _, _, h, s1, s2 =>
      LK₀.struct _ _ _ _ h (map_sub _ s1) (sub_cons b (map_sub _ s2))
  | Formula.ex _, Γ, Γ', _, _, h, s1, s2 =>
      h.elim (fun t ht => ⟨t, LK₀.struct Γ Γ' _ _ ht s1 (sub_cons _ s2)⟩)

theorem leftPrin_lift : ∀ (A : Formula) {Γ Δ : List Formula}, LeftPrin A Γ Δ → ∀ (k : Nat),
    LeftPrin (liftFormula k A) (Γ.map (liftFormula k)) (Δ.map (liftFormula k))
  | Formula.bottom, _, _, h, _ => h.elim
  | Formula.atom _ _, _, _, h, _ => h.elim
  | Formula.eq _ _, _, _, h, _ => h.elim
  | Formula.impl b c, Γ, Δ, h, k => by
      show LK₀ (liftFormula k b :: Γ.map (liftFormula k)) (liftFormula k c :: Δ.map (liftFormula k))
      simpa only [List.map_cons] using lk0_lift h k
  | Formula.and b c, _, _, h, k => by
      refine ⟨?_, ?_⟩
      · simpa only [List.map_cons] using lk0_lift h.1 k
      · simpa only [List.map_cons] using lk0_lift h.2 k
  | Formula.or b c, Γ, Δ, h, k => by
      show LK₀ (Γ.map (liftFormula k))
        (liftFormula k b :: liftFormula k c :: Δ.map (liftFormula k))
      simpa only [List.map_cons] using lk0_lift h k
  | Formula.forall b, Γ, Δ, h, k => by
      show LK₀ ((Γ.map (liftFormula k)).map (liftFormula 0))
        (liftFormula (k + 1) b :: (Δ.map (liftFormula k)).map (liftFormula 0))
      rw [FOL.Lift0.map_lift_lift k Γ, FOL.Lift0.map_lift_lift k Δ]
      simpa only [List.map_cons] using lk0_lift h (k + 1)
  | Formula.ex b, _, _, h, k => by
      obtain ⟨t, ht⟩ := h
      refine ⟨liftTerm k t, ?_⟩
      have hx := lk0_lift ht k
      simp only [List.map_cons] at hx
      rwa [FOL.Lift0.liftFormula_subst b 0 k (Nat.zero_le _) t] at hx

-- ── §8.4 · el enunciado GENERALIZADO del corte ──────────────────────────────
-- ⭐ La fórmula de corte se pide por PERTENENCIA (`Or (x = A) (x ∈ Δ)`) y no en
-- la cabeza. Eso absorbe la contracción — que es lo que en la presentación
-- clásica de Gentzen obliga a pasar por la regla MIX.
def CutAt (A : Formula) (m n : Nat) : Prop :=
  ∀ (Γ₁ Δ₁ Γ₂ Δ₂ Γ Δ : List Formula),
    LKh m Γ₁ Δ₁ → LKh n Γ₂ Δ₂ →
    (∀ x, x ∈ Γ₁ → x ∈ Γ) → (∀ x, x ∈ Δ₁ → Or (x = A) (x ∈ Δ)) →
    (∀ x, x ∈ Γ₂ → Or (x = A) (x ∈ Γ)) → (∀ x, x ∈ Δ₂ → x ∈ Δ) →
    LK₀ Γ Δ

/-- Todos los cortes de grado ESTRICTAMENTE menor que `d`. -/
def CutBelow (d : Nat) : Prop := ∀ A, deg A < d → ∀ m n, CutAt A m n

/-- El corte en su forma cómoda: dos `LK₀` y una cota de grado. -/
theorem cutOf {d : Nat} (IHd : CutBelow d) (A : Formula) (hA : deg A < d)
    {Γ Δ : List Formula} (P : LK₀ Γ (A :: Δ)) (Q : LK₀ (A :: Γ) Δ) : LK₀ Γ Δ := by
  obtain ⟨m, hm⟩ := lk0_to_lkh P
  obtain ⟨n, hn⟩ := lk0_to_lkh Q
  refine IHd A hA m n Γ (A :: Δ) (A :: Γ) Δ Γ Δ hm hn (sub_refl Γ) ?_ ?_ (sub_refl Δ)
  · intro x hx
    cases hx with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr h
  · intro x hx
    cases hx with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr h

-- ── §8.5 · ⭐⭐⭐ EL CORTE PRINCIPAL: UNA sola pasada sobre `D2` ──────────────
-- Inducción FUERTE sobre la altura `n` del lado derecho, no estructural: los
-- casos `exL` principal y los de levantamiento consumen `lkh_subst`/`lkh_lift`,
-- que devuelven otra derivación de la MISMA altura, no una subderivación.
theorem cutPrinAux {d : Nat} (IHd : CutBelow d) :
    ∀ (k n : Nat), n < k → ∀ (Γ₂ Δ₂ : List Formula), LKh n Γ₂ Δ₂ →
      ∀ (A : Formula), deg A = d → ∀ (Γ Δ : List Formula),
        (∀ x, x ∈ Γ₂ → Or (x = A) (x ∈ Γ)) → (∀ x, x ∈ Δ₂ → x ∈ Δ) →
        LeftPrin A Γ Δ → LK₀ Γ Δ := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k IH =>
    intro n hn Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
    cases D2 with
    | ax n₀ Ga Da P hP1 hP2 =>
        rcases h3 P hP1 with he | hm
        · exact LK₀.struct Γ Γ (A :: Δ) Δ (leftPrin_close A Γ Δ hLP) (sub_refl Γ)
            (sub_drop (he ▸ h4 P hP2))
        · exact LK₀.ax Γ Δ P hm (h4 P hP2)
    | botL n₀ Ga Da hP =>
        rcases h3 Formula.bottom hP with he | hm
        · subst he; exact hLP.elim
        · exact LK₀.botL Γ Δ hm
    | struct n₀ Ga Gb Da Db E s1 s2 =>
        exact IH n₀ (by omega) Ga Da E A hdA Γ Δ
          (fun x hx => h3 x (s1 x hx)) (fun x hx => h4 x (s2 x hx)) hLP
    -- ── reglas DERECHAS de D2: nunca principales sobre A, siempre permutan ────
    | implR n₀ Γ₂ Da b c F =>
        have hmem : Formula.impl b c ∈ Δ := h4 _ (List.Mem.head _)
        have H : LK₀ (b :: Γ) (c :: Δ) :=
          IH n₀ (by omega) (b :: Γ₂) (c :: Da) F A hdA (b :: Γ) (c :: Δ)
            (subA_cons b h3) (sub_cons c (mem_tl h4))
            (leftPrin_mono A hLP (sub_wk b (sub_refl Γ)) (sub_wk c (sub_refl Δ)))
        exact LK₀.struct Γ Γ (Formula.impl b c :: Δ) Δ (LK₀.implR Γ Δ b c H)
          (sub_refl Γ) (sub_drop hmem)
    | andR n₀ Γ₂ Da b c F1 F2 =>
        have hmem : Formula.and b c ∈ Δ := h4 _ (List.Mem.head _)
        have H1 : LK₀ Γ (b :: Δ) :=
          IH n₀ (by omega) Γ₂ (b :: Da) F1 A hdA Γ (b :: Δ)
            h3 (sub_cons b (mem_tl h4)) (leftPrin_mono A hLP (sub_refl Γ) (sub_wk b (sub_refl Δ)))
        have H2 : LK₀ Γ (c :: Δ) :=
          IH n₀ (by omega) Γ₂ (c :: Da) F2 A hdA Γ (c :: Δ)
            h3 (sub_cons c (mem_tl h4)) (leftPrin_mono A hLP (sub_refl Γ) (sub_wk c (sub_refl Δ)))
        exact LK₀.struct Γ Γ (Formula.and b c :: Δ) Δ (LK₀.andR Γ Δ b c H1 H2)
          (sub_refl Γ) (sub_drop hmem)
    | orR n₀ Γ₂ Da b c F =>
        have hmem : Formula.or b c ∈ Δ := h4 _ (List.Mem.head _)
        have H : LK₀ Γ (b :: c :: Δ) :=
          IH n₀ (by omega) Γ₂ (b :: c :: Da) F A hdA Γ (b :: c :: Δ)
            h3 (sub_cons b (sub_cons c (mem_tl h4)))
            (leftPrin_mono A hLP (sub_refl Γ) (sub_wk b (sub_wk c (sub_refl Δ))))
        exact LK₀.struct Γ Γ (Formula.or b c :: Δ) Δ (LK₀.orR Γ Δ b c H)
          (sub_refl Γ) (sub_drop hmem)
    | exR n₀ Γ₂ Da b t F =>
        have hmem : Formula.ex b ∈ Δ := h4 _ (List.Mem.head _)
        have H : LK₀ Γ (substFormula 0 t b :: Δ) :=
          IH n₀ (by omega) Γ₂ (substFormula 0 t b :: Da) F A hdA Γ (substFormula 0 t b :: Δ)
            h3 (sub_cons _ (mem_tl h4)) (leftPrin_mono A hLP (sub_refl Γ) (sub_wk _ (sub_refl Δ)))
        exact LK₀.struct Γ Γ (Formula.ex b :: Δ) Δ (LK₀.exR Γ Δ b t H)
          (sub_refl Γ) (sub_drop hmem)
    -- ⭐ `allR` a la derecha: hay que LEVANTAR el lado izquierdo Y la fórmula de corte
    | allR n₀ Γ₂ Da b F =>
        have hmem : Formula.forall b ∈ Δ := h4 _ (List.Mem.head _)
        have H : LK₀ (Γ.map (liftFormula 0)) (b :: Δ.map (liftFormula 0)) :=
          IH n₀ (by omega) (Γ₂.map (liftFormula 0)) (b :: Da.map (liftFormula 0)) F
            (liftFormula 0 A) (by rw [deg_lift]; exact hdA)
            (Γ.map (liftFormula 0)) (b :: Δ.map (liftFormula 0))
            (mapA_sub 0 h3) (sub_cons b (map_sub _ (mem_tl h4)))
            (leftPrin_mono (liftFormula 0 A) (leftPrin_lift A hLP 0)
              (sub_refl _) (sub_wk b (sub_refl _)))
        exact LK₀.struct Γ Γ (Formula.forall b :: Δ) Δ (LK₀.allR Γ Δ b H)
          (sub_refl Γ) (sub_drop hmem)
    -- ── reglas IZQUIERDAS de D2: aquí vive el caso PRINCIPAL ──────────────────
    | implL n₀ Ga Δ₂ b c F1 F2 =>
        have H1 : LK₀ Γ (b :: Δ) :=
          IH n₀ (by omega) Ga (b :: Δ₂) F1 A hdA Γ (b :: Δ)
            (mem_tl h3) (sub_cons b h4) (leftPrin_mono A hLP (sub_refl Γ) (sub_wk b (sub_refl Δ)))
        have H2 : LK₀ (c :: Γ) Δ :=
          IH n₀ (by omega) (c :: Ga) Δ₂ F2 A hdA (c :: Γ) Δ
            (subA_cons c (mem_tl h3)) h4 (leftPrin_mono A hLP (sub_wk c (sub_refl Γ)) (sub_refl Δ))
        rcases h3 (Formula.impl b c) (List.Mem.head _) with he | hmem
        · -- ⭐⭐ PRINCIPAL: A = b ⇒ c
          subst he
          have hb : deg b < d := by
            rw [← hdA]; show deg b < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
          have hc : deg c < d := by
            rw [← hdA]; show deg c < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
          have Hc : LK₀ (b :: Γ) Δ :=
            cutOf IHd c hc hLP
              (LK₀.struct (c :: Γ) (c :: b :: Γ) Δ Δ H2 (sub_cons c (sub_wk b (sub_refl Γ)))
                (sub_refl Δ))
          exact cutOf IHd b hb H1 Hc
        · exact LK₀.struct (Formula.impl b c :: Γ) Γ Δ Δ (LK₀.implL Γ Δ b c H1 H2)
            (sub_drop hmem) (sub_refl Δ)
    | andL n₀ Ga Δ₂ b c F =>
        have H : LK₀ (b :: c :: Γ) Δ :=
          IH n₀ (by omega) (b :: c :: Ga) Δ₂ F A hdA (b :: c :: Γ) Δ
            (subA_cons b (subA_cons c (mem_tl h3))) h4
            (leftPrin_mono A hLP (sub_wk b (sub_wk c (sub_refl Γ))) (sub_refl Δ))
        rcases h3 (Formula.and b c) (List.Mem.head _) with he | hmem
        · -- ⭐⭐ PRINCIPAL: A = b ∧ c
          subst he
          have hb : deg b < d := by
            rw [← hdA]; show deg b < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
          have hc : deg c < d := by
            rw [← hdA]; show deg c < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
          have Hc : LK₀ (b :: Γ) Δ :=
            cutOf IHd c hc
              (LK₀.struct Γ (b :: Γ) (c :: Δ) (c :: Δ) hLP.2 (sub_wk b (sub_refl Γ)) (sub_refl _))
              (LK₀.struct (b :: c :: Γ) (c :: b :: Γ) Δ Δ H (swap_cons b c Γ) (sub_refl Δ))
          exact cutOf IHd b hb hLP.1 Hc
        · exact LK₀.struct (Formula.and b c :: Γ) Γ Δ Δ (LK₀.andL Γ Δ b c H)
            (sub_drop hmem) (sub_refl Δ)
    | orL n₀ Ga Δ₂ b c F1 F2 =>
        have H1 : LK₀ (b :: Γ) Δ :=
          IH n₀ (by omega) (b :: Ga) Δ₂ F1 A hdA (b :: Γ) Δ
            (subA_cons b (mem_tl h3)) h4 (leftPrin_mono A hLP (sub_wk b (sub_refl Γ)) (sub_refl Δ))
        have H2 : LK₀ (c :: Γ) Δ :=
          IH n₀ (by omega) (c :: Ga) Δ₂ F2 A hdA (c :: Γ) Δ
            (subA_cons c (mem_tl h3)) h4 (leftPrin_mono A hLP (sub_wk c (sub_refl Γ)) (sub_refl Δ))
        rcases h3 (Formula.or b c) (List.Mem.head _) with he | hmem
        · -- ⭐⭐ PRINCIPAL: A = b ∨ c
          subst he
          have hb : deg b < d := by
            rw [← hdA]; show deg b < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
          have hc : deg c < d := by
            rw [← hdA]; show deg c < deg b + deg c + 1
            exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
          have Hc : LK₀ Γ (b :: Δ) :=
            cutOf IHd c hc
              (LK₀.struct Γ Γ (b :: c :: Δ) (c :: b :: Δ) hLP (sub_refl Γ) (swap_cons b c Δ))
              (LK₀.struct (c :: Γ) (c :: Γ) Δ (b :: Δ) H2 (sub_refl _) (sub_wk b (sub_refl Δ)))
          exact cutOf IHd b hb Hc H1
        · exact LK₀.struct (Formula.or b c :: Γ) Γ Δ Δ (LK₀.orL Γ Δ b c H1 H2)
            (sub_drop hmem) (sub_refl Δ)
    | allL n₀ Ga Δ₂ b t F =>
        have H : LK₀ (substFormula 0 t b :: Γ) Δ :=
          IH n₀ (by omega) (substFormula 0 t b :: Ga) Δ₂ F A hdA (substFormula 0 t b :: Γ) Δ
            (subA_cons _ (mem_tl h3)) h4
            (leftPrin_mono A hLP (sub_wk _ (sub_refl Γ)) (sub_refl Δ))
        rcases h3 (Formula.forall b) (List.Mem.head _) with he | hmem
        · -- ⭐⭐ PRINCIPAL: A = ∀b. Aquí paga `lkh_subst`, vía `lk0_subst`.
          subst he
          have hb : deg (substFormula 0 t b) < d := by
            rw [deg_subst, ← hdA]; show deg b < deg b + 1
            exact Nat.lt_succ_self _
          have Pt : LK₀ Γ (substFormula 0 t b :: Δ) := by
            have hx := lk0_subst hLP 0 t
            simp only [List.map_cons] at hx
            rwa [map_subst_lift t Γ, map_subst_lift t Δ] at hx
          exact cutOf IHd _ hb Pt H
        · exact LK₀.struct (Formula.forall b :: Γ) Γ Δ Δ (LK₀.allL Γ Δ b t H)
            (sub_drop hmem) (sub_refl Δ)
    | exL n₀ Ga Δ₂ b F =>
        rcases h3 (Formula.ex b) (List.Mem.head _) with he | hmem
        · -- ⭐⭐ PRINCIPAL: A = ∃b. El testigo lo pone el LADO IZQUIERDO.
          subst he
          obtain ⟨t, Pt⟩ := hLP
          have hb : deg (substFormula 0 t b) < d := by
            rw [deg_subst, ← hdA]; show deg b < deg b + 1
            exact Nat.lt_succ_self _
          have Fs : LKh n₀ (substFormula 0 t b :: Ga) Δ₂ := by
            have hx := lkh_subst F 0 t
            simp only [List.map_cons] at hx
            rwa [map_subst_lift t Ga, map_subst_lift t Δ₂] at hx
          have H : LK₀ (substFormula 0 t b :: Γ) Δ :=
            IH n₀ (by omega) (substFormula 0 t b :: Ga) Δ₂ Fs (Formula.ex b) hdA
              (substFormula 0 t b :: Γ) Δ
              (subA_cons _ (mem_tl h3)) h4
              (leftPrin_mono (Formula.ex b) (⟨t, Pt⟩ : LeftPrin (Formula.ex b) Γ Δ)
                (sub_wk _ (sub_refl Γ)) (sub_refl Δ))
          exact cutOf IHd _ hb Pt H
        · have H : LK₀ (b :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) :=
            IH n₀ (by omega) (b :: Ga.map (liftFormula 0)) (Δ₂.map (liftFormula 0)) F
              (liftFormula 0 A) (by rw [deg_lift]; exact hdA)
              (b :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0))
              (subA_cons b (mapA_sub 0 (mem_tl h3))) (map_sub _ h4)
              (leftPrin_mono (liftFormula 0 A) (leftPrin_lift A hLP 0)
                (sub_wk b (sub_refl _)) (sub_refl _))
          exact LK₀.struct (Formula.ex b :: Γ) Γ Δ Δ (LK₀.exL Γ Δ b H)
            (sub_drop hmem) (sub_refl Δ)
    | eqAx n₀ Ga Da g hg F =>
        have H : LK₀ (g :: Γ) Δ :=
          IH n₀ (by omega) (g :: Γ₂) Δ₂ F A hdA (g :: Γ) Δ
            (subA_cons g h3) h4 (leftPrin_mono A hLP (sub_wk g (sub_refl Γ)) (sub_refl Δ))
        exact LK₀.eqAx Γ Δ g hg H

-- ── §8.6 · ⭐⭐ LA PASADA IZQUIERDA: inducción sobre la altura `m` de `D1` ────
-- ⭐ Y aquí está la sorpresa de la arquitectura: la «inducción doble» clásica
-- sobre `m + n` NO hace falta. Basta inducir sobre `m` — porque los únicos casos
-- que consumen el lado derecho son los PRINCIPALES, y ésos los absorbe
-- `cutPrinAux`, que induce sobre `n` por su cuenta.
theorem cutLeftAux {d : Nat} (IHd : CutBelow d) :
    ∀ (k m : Nat), m < k → ∀ (A : Formula), deg A = d → ∀ (n : Nat), CutAt A m n := by
  intro k
  induction k with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ k IH =>
    intro m hm A hdA n Γ₁ Δ₁ Γ₂ Δ₂ Γ Δ D1 D2 h1 h2 h3 h4
    cases D1 with
    | ax m₀ Ga Da P hP1 hP2 =>
        rcases h2 P hP2 with he | hmem
        · have hAΓ : P ∈ Γ := h1 P hP1
          refine LK₀.struct Γ₂ Γ Δ₂ Δ (lkh_to_lk0 D2) ?_ h4
          intro x hx
          rcases h3 x hx with hxA | hxΓ
          · rw [hxA, ← he]; exact hAΓ
          · exact hxΓ
        · exact LK₀.ax Γ Δ P (h1 P hP1) hmem
    | botL m₀ Ga Da hP => exact LK₀.botL Γ Δ (h1 _ hP)
    | struct m₀ Ga Gb Da Db E s1 s2 =>
        exact IH m₀ (by omega) A hdA n Ga Da Γ₂ Δ₂ Γ Δ E D2
          (fun x hx => h1 x (s1 x hx)) (fun x hx => h2 x (s2 x hx)) h3 h4
    -- ── reglas IZQUIERDAS de D1: nunca principales sobre A, siempre permutan ──
    | implL m₀ Ga Da b c F1 F2 =>
        have hmem : Formula.impl b c ∈ Γ := h1 _ (List.Mem.head _)
        have G1 : LK₀ Γ (b :: Δ) :=
          IH m₀ (by omega) A hdA n Ga (b :: Δ₁) Γ₂ Δ₂ Γ (b :: Δ) F1 D2
            (mem_tl h1) (subA_cons b h2) h3 (sub_wk b h4)
        have G2 : LK₀ (c :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (c :: Ga) Δ₁ Γ₂ Δ₂ (c :: Γ) Δ F2 D2
            (sub_cons c (mem_tl h1)) h2 (subA_wk c h3) h4
        exact LK₀.struct (Formula.impl b c :: Γ) Γ Δ Δ (LK₀.implL Γ Δ b c G1 G2)
          (sub_drop hmem) (sub_refl Δ)
    | andL m₀ Ga Da b c F =>
        have hmem : Formula.and b c ∈ Γ := h1 _ (List.Mem.head _)
        have G : LK₀ (b :: c :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (b :: c :: Ga) Δ₁ Γ₂ Δ₂ (b :: c :: Γ) Δ F D2
            (sub_cons b (sub_cons c (mem_tl h1))) h2 (subA_wk b (subA_wk c h3)) h4
        exact LK₀.struct (Formula.and b c :: Γ) Γ Δ Δ (LK₀.andL Γ Δ b c G)
          (sub_drop hmem) (sub_refl Δ)
    | orL m₀ Ga Da b c F1 F2 =>
        have hmem : Formula.or b c ∈ Γ := h1 _ (List.Mem.head _)
        have G1 : LK₀ (b :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (b :: Ga) Δ₁ Γ₂ Δ₂ (b :: Γ) Δ F1 D2
            (sub_cons b (mem_tl h1)) h2 (subA_wk b h3) h4
        have G2 : LK₀ (c :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (c :: Ga) Δ₁ Γ₂ Δ₂ (c :: Γ) Δ F2 D2
            (sub_cons c (mem_tl h1)) h2 (subA_wk c h3) h4
        exact LK₀.struct (Formula.or b c :: Γ) Γ Δ Δ (LK₀.orL Γ Δ b c G1 G2)
          (sub_drop hmem) (sub_refl Δ)
    | allL m₀ Ga Da b t F =>
        have hmem : Formula.forall b ∈ Γ := h1 _ (List.Mem.head _)
        have G : LK₀ (substFormula 0 t b :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (substFormula 0 t b :: Ga) Δ₁ Γ₂ Δ₂
            (substFormula 0 t b :: Γ) Δ F D2
            (sub_cons _ (mem_tl h1)) h2 (subA_wk _ h3) h4
        exact LK₀.struct (Formula.forall b :: Γ) Γ Δ Δ (LK₀.allL Γ Δ b t G)
          (sub_drop hmem) (sub_refl Δ)
    | exL m₀ Ga Da b F =>
        have hmem : Formula.ex b ∈ Γ := h1 _ (List.Mem.head _)
        have G : LK₀ (b :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) :=
          IH m₀ (by omega) (liftFormula 0 A) (by rw [deg_lift]; exact hdA) n
            (b :: Ga.map (liftFormula 0)) (Δ₁.map (liftFormula 0))
            (Γ₂.map (liftFormula 0)) (Δ₂.map (liftFormula 0))
            (b :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0))
            F (lkh_lift D2 0)
            (sub_cons b (map_sub _ (mem_tl h1))) (mapA_sub 0 h2)
            (subA_wk b (mapA_sub 0 h3)) (map_sub _ h4)
        exact LK₀.struct (Formula.ex b :: Γ) Γ Δ Δ (LK₀.exL Γ Δ b G)
          (sub_drop hmem) (sub_refl Δ)
    | eqAx m₀ Ga Da g hg F =>
        have G : LK₀ (g :: Γ) Δ :=
          IH m₀ (by omega) A hdA n (g :: Γ₁) Δ₁ Γ₂ Δ₂ (g :: Γ) Δ F D2
            (sub_cons g h1) h2 (subA_wk g h3) h4
        exact LK₀.eqAx Γ Δ g hg G
    -- ── reglas DERECHAS de D1: la MISMA llamada sirve para las dos ramas ──────
    -- ⭐ El resultado de la recursión ES `LeftPrin A Γ Δ` cuando la principal es
    -- `A`, y la premisa de la regla cuando no lo es. Una sola llamada, dos usos.
    | implR m₀ Ga Da b c F =>
        have G : LK₀ (b :: Γ) (c :: Δ) :=
          IH m₀ (by omega) A hdA n (b :: Γ₁) (c :: Da) Γ₂ Δ₂ (b :: Γ) (c :: Δ) F D2
            (sub_cons b h1) (subA_cons c (mem_tl h2)) (subA_wk b h3) (sub_wk c h4)
        by_cases hA : Formula.impl b c = A
        · have hLP : LeftPrin A Γ Δ := by rw [← hA]; exact G
          exact cutPrinAux IHd (n + 1) n (Nat.lt_succ_self n) Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
        · have hmem : Formula.impl b c ∈ Δ := (h2 _ (List.Mem.head _)).resolve_left hA
          exact LK₀.struct Γ Γ (Formula.impl b c :: Δ) Δ (LK₀.implR Γ Δ b c G)
            (sub_refl Γ) (sub_drop hmem)
    | andR m₀ Ga Da b c F1 F2 =>
        have G1 : LK₀ Γ (b :: Δ) :=
          IH m₀ (by omega) A hdA n Γ₁ (b :: Da) Γ₂ Δ₂ Γ (b :: Δ) F1 D2
            h1 (subA_cons b (mem_tl h2)) h3 (sub_wk b h4)
        have G2 : LK₀ Γ (c :: Δ) :=
          IH m₀ (by omega) A hdA n Γ₁ (c :: Da) Γ₂ Δ₂ Γ (c :: Δ) F2 D2
            h1 (subA_cons c (mem_tl h2)) h3 (sub_wk c h4)
        by_cases hA : Formula.and b c = A
        · have hLP : LeftPrin A Γ Δ := by rw [← hA]; exact ⟨G1, G2⟩
          exact cutPrinAux IHd (n + 1) n (Nat.lt_succ_self n) Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
        · have hmem : Formula.and b c ∈ Δ := (h2 _ (List.Mem.head _)).resolve_left hA
          exact LK₀.struct Γ Γ (Formula.and b c :: Δ) Δ (LK₀.andR Γ Δ b c G1 G2)
            (sub_refl Γ) (sub_drop hmem)
    | orR m₀ Ga Da b c F =>
        have G : LK₀ Γ (b :: c :: Δ) :=
          IH m₀ (by omega) A hdA n Γ₁ (b :: c :: Da) Γ₂ Δ₂ Γ (b :: c :: Δ) F D2
            h1 (subA_cons b (subA_cons c (mem_tl h2))) h3 (sub_wk b (sub_wk c h4))
        by_cases hA : Formula.or b c = A
        · have hLP : LeftPrin A Γ Δ := by rw [← hA]; exact G
          exact cutPrinAux IHd (n + 1) n (Nat.lt_succ_self n) Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
        · have hmem : Formula.or b c ∈ Δ := (h2 _ (List.Mem.head _)).resolve_left hA
          exact LK₀.struct Γ Γ (Formula.or b c :: Δ) Δ (LK₀.orR Γ Δ b c G)
            (sub_refl Γ) (sub_drop hmem)
    | exR m₀ Ga Da b t F =>
        have G : LK₀ Γ (substFormula 0 t b :: Δ) :=
          IH m₀ (by omega) A hdA n Γ₁ (substFormula 0 t b :: Da) Γ₂ Δ₂
            Γ (substFormula 0 t b :: Δ) F D2
            h1 (subA_cons _ (mem_tl h2)) h3 (sub_wk _ h4)
        by_cases hA : Formula.ex b = A
        · have hLP : LeftPrin A Γ Δ := by rw [← hA]; exact ⟨t, G⟩
          exact cutPrinAux IHd (n + 1) n (Nat.lt_succ_self n) Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
        · have hmem : Formula.ex b ∈ Δ := (h2 _ (List.Mem.head _)).resolve_left hA
          exact LK₀.struct Γ Γ (Formula.ex b :: Δ) Δ (LK₀.exR Γ Δ b t G)
            (sub_refl Γ) (sub_drop hmem)
    | allR m₀ Ga Da b F =>
        have G : LK₀ (Γ.map (liftFormula 0)) (b :: Δ.map (liftFormula 0)) :=
          IH m₀ (by omega) (liftFormula 0 A) (by rw [deg_lift]; exact hdA) n
            (Γ₁.map (liftFormula 0)) (b :: Da.map (liftFormula 0))
            (Γ₂.map (liftFormula 0)) (Δ₂.map (liftFormula 0))
            (Γ.map (liftFormula 0)) (b :: Δ.map (liftFormula 0))
            F (lkh_lift D2 0)
            (map_sub _ h1) (subA_cons b (mapA_sub 0 (mem_tl h2)))
            (mapA_sub 0 h3) (sub_wk b (map_sub _ h4))
        by_cases hA : Formula.forall b = A
        · have hLP : LeftPrin A Γ Δ := by rw [← hA]; exact G
          exact cutPrinAux IHd (n + 1) n (Nat.lt_succ_self n) Γ₂ Δ₂ D2 A hdA Γ Δ h3 h4 hLP
        · have hmem : Formula.forall b ∈ Δ := (h2 _ (List.Mem.head _)).resolve_left hA
          exact LK₀.struct Γ Γ (Formula.forall b :: Δ) Δ (LK₀.allR Γ Δ b G)
            (sub_refl Γ) (sub_drop hmem)

-- ── §8.7 · la inducción EXTERNA: sobre el GRADO ─────────────────────────────
theorem cutAll : ∀ (d : Nat), CutBelow d := by
  intro d
  induction d with
  | zero => intro A hA; exact absurd hA (Nat.not_lt_zero _)
  | succ d IHd =>
      intro A hA m n
      rcases Nat.lt_or_ge (deg A) d with h | h
      · exact IHd A h m n
      · have hd : deg A = d := by omega
        exact cutLeftAux IHd (m + 1) m (Nat.lt_succ_self m) A hd n

-- ── §8.8 · 🏁🏁🏁 EL HAUPTSATZ ──────────────────────────────────────────────
/-- 🏁🏁🏁 **EL HAUPTSATZ**: el corte ÚNICO es ADMISIBLE en `LK₀`. -/
theorem hauptsatz : CutAdm := by
  intro Γ Δ A P Q
  obtain ⟨m, hm⟩ := lk0_to_lkh P
  obtain ⟨n, hn⟩ := lk0_to_lkh Q
  refine cutAll (deg A + 1) A (Nat.lt_succ_self _) m n Γ (A :: Δ) (A :: Γ) Δ Γ Δ hm hn
    (sub_refl Γ) ?_ ?_ (sub_refl Δ)
  · intro x hx
    cases hx with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr h
  · intro x hx
    cases hx with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr h

/-- 🏁 Y con él, la ELIMINACIÓN DE CORTES. -/
theorem cut_elimination : CutElim := cutElim_of hauptsatz

/-- 🏁🏁 Y con ella, **H3**: la EXTRACCIÓN DE HERBRAND deja de ser una deuda. -/
theorem herbrand_extraction : HerbrandExtraction :=
  FOL.NDtoLK0.herbrandExtraction_of_cutElim cut_elimination

/-- 🏁🏁🏁 **EL TEOREMA DE HERBRAND, YA INCONDICIONAL.** Era un `↔` con hipótesis (`herbrand_iff`,
ADR‑043) y la hipótesis era H3; H3 es ahora un teorema. ⭐ Y el recíproco ya lo era
(`derives0_ex_of_cert`), luego el bicondicional queda **entero y sin deudas**. -/
theorem herbrand {φ : Formula} (hqf : QuantFree φ) :
    ([] ⊢₀ Formula.ex φ) ↔ ∃ ts E, HerbrandCert φ ts E :=
  herbrand_iff herbrand_extraction hqf

-- ============================================================
-- §9 · ⭐ El fragmento SIN CUANTIFICADORES: derivable ⟺ consecuencia PROPOSICIONAL módulo `E`
-- ============================================================

open FOL.Propositional0

/-- El certificado del secuente `Γ ⟹ φ`: una lista `E` de instancias de la igualdad, y la
constancia de que `φ` se sigue PROPOSICIONALMENTE de `Γ` y `E`.
⚠️ `E` NO tiene cota: esto CARACTERIZA el fragmento sin cuantificadores, pero NO lo DECIDE. -/
def EqPropCert (Γ : List Formula) (φ : Formula) (E : List Formula) : Prop :=
  And (∀ g, g ∈ E → EqInstance g)
    (∀ v : PVal, (∀ g, g ∈ Γ → peval v g = true) →
      (∀ g, g ∈ E → peval v g = true) → peval v φ = true)

/-- ⟸, incondicional y SIN hipótesis `QuantFree` (`peval` trata los cuantificadores como átomos).
Calco de `derives0_of_ptaut_ctx` + `derives0_ex_of_cert`: la cadena `implChain` evita un
`derives0_discharge` con contexto. -/
theorem derives0_of_eqPropCert {Γ : List Formula} {φ : Formula} {E : List Formula}
    (h : EqPropCert Γ φ E) : Γ ⊢₀ φ := by
  refine derives0_of_implChain Γ Γ φ ?_ (fun _ hx => hx)
  refine Derives₀.weakening [] Γ _ ?_ (fun _ hx => absurd hx List.not_mem_nil)
  refine derives0_discharge E _ ?_ (fun g hg => derives0_of_eqInstance (h.1 g hg))
  exact derives0_of_ptaut_ctx (fun v hEv => peval_implChain v Γ φ (fun hΓv => h.2 v hΓv hEv))

/-- ⟹: `lk0_herbrand` con `φ := ⊥`. La tercera premisa de `HerbrandOut` se descarga por `rfl`
(`substFormula 0 t ⊥ = ⊥`, `peval v ⊥ = false`).
⭐ En ESTA ruta paga el Hauptsatz: `lk0_herbrand` exige `LK₀`, porque un corte con fórmula
cuantificada rompería su invariante `QuantFree`. ⚠️ Esto NO afirma que el Hauptsatz sea NECESARIO
para este teorema: cf. `Finitary0` §«Dónde NO paga el Hauptsatz». -/
theorem eqPropCert_of_derives0 {Γ : List Formula} {φ : Formula}
    (hΓ : ∀ g, g ∈ Γ → QuantFree g) (hφ : QuantFree φ) (h : Γ ⊢₀ φ) :
    ∃ E, EqPropCert Γ φ E := by
  obtain ⟨_, E, hE, hout⟩ := lk0_herbrand (φ := Formula.bottom) trivial
    (cut_elimination _ _ (FOL.NDtoLK0.ndToLK (FOL.Derives2.derives0_iff_derives2.mp h))) hΓ
    (fun d hd => by
      cases hd with
      | head => exact Or.inl hφ
      | tail _ h2 => exact absurd h2 List.not_mem_nil)
  refine ⟨E, hE, fun v hv hEv => ?_⟩
  obtain ⟨d, hd, _, hval⟩ := hout v hv hEv (fun _ _ => rfl)
  cases hd with
  | head => exact hval
  | tail _ h2 => exact absurd h2 List.not_mem_nil

/-- 🏁 **El fragmento sin cuantificadores, CARACTERIZADO**: un secuente sin cuantificadores es
derivable sii su conclusión es consecuencia PROPOSICIONAL del contexto más una lista finita de
instancias de la igualdad. Es la versión CIERTA de lo que es FALSO decir «decidible por tabla de
verdad» (`c ≐ c` es derivable y no es `PTaut`).
⚠️ Caracteriza, NO decide: el lado derecho es un `∃ E` sin cota (Σ₁ sólo informalmente: en el
árbol no hay instancia `Decidable` ni de `EqInstance` ni de `EqPropCert Γ φ E`). La versión ACOTADA
(Ackermann / cierre de congruencia sobre los subtérminos) NO está probada: la `E` que devuelve
`lk0_herbrand` no sale acotada porque `eqAx` admite instancias con términos ajenos; con este
teorema en la mano, acotarla sería un lema sobre `EqPropCert` (podar `E`), no sobre `LK₀`, y su
coste no está medido. -/
theorem derives0_qf_iff {Γ : List Formula} {φ : Formula}
    (hΓ : ∀ g, g ∈ Γ → QuantFree g) (hφ : QuantFree φ) :
    (Γ ⊢₀ φ) ↔ ∃ E, EqPropCert Γ φ E :=
  ⟨eqPropCert_of_derives0 hΓ hφ, fun ⟨_, hc⟩ => derives0_of_eqPropCert hc⟩

/-- La valuación constante `true` hace verdaderas las CINCO formas de `EqInstance`
(el gemelo `peval` de `FOL.Finitary0.tval_eqInstance`). -/
theorem peval_true_eqInstance {g : Formula} (hg : EqInstance g) :
    peval (fun _ => true) g = true := by
  cases hg <;> rfl

-- ⚠️ CONTROL DE VACUIDAD: la `E` sin cota NO trivializa el lado derecho.
example (E : List Formula) : Not (EqPropCert [] Formula.bottom E) := by
  intro h
  have hf : peval (fun _ => true) Formula.bottom = true :=
    h.2 (fun _ => true) (fun _ hx => absurd hx List.not_mem_nil)
      (fun g hg => peval_true_eqInstance (h.1 g hg))
  exact absurd hf (by simp [peval])

-- ⚠️ CONTROL: la ⟹ no es trivial — junto con el anterior da la consistencia. Ojo: la valuación
-- constante `true` es la de `Finitary0.tval true`, así que esta consistencia ya la da
-- `Finitary0.derives0_consistent_fin` SIN el Hauptsatz; ningún control de aquí separa esta ⟹ de
-- `tval` (haría falta una valuación que distinga igualdades, p. ej. la identidad sintáctica).
example : Not (([] : List Formula) ⊢₀ Formula.bottom) := fun h => by
  obtain ⟨E, hc⟩ := eqPropCert_of_derives0 (Γ := []) (φ := Formula.bottom)
    (fun _ hx => absurd hx List.not_mem_nil) trivial h
  have hf : peval (fun _ => true) Formula.bottom = true :=
    hc.2 (fun _ => true) (fun _ hx => absurd hx List.not_mem_nil)
      (fun g hg => peval_true_eqInstance (hc.1 g hg))
  exact absurd hf (by simp [peval])

end FOL.Hauptsatz0

#print axioms FOL.Hauptsatz0.cutElim_of
#print axioms LKh.rec
#print axioms FOL.Hauptsatz0.lkh_mono
#print axioms FOL.Hauptsatz0.lkh_to_lk0
#print axioms FOL.Hauptsatz0.lk0_to_lkh
#print axioms FOL.Hauptsatz0.liftFormula_subst_le
#print axioms FOL.Hauptsatz0.substFormula_subst_le
#print axioms FOL.Hauptsatz0.eqInstance_subst
#print axioms FOL.Hauptsatz0.lkh_subst
#print axioms FOL.Hauptsatz0.lkh_lift
#print axioms FOL.Hauptsatz0.eqInstance_lift
#print axioms FOL.Hauptsatz0.cutPrinAux
#print axioms FOL.Hauptsatz0.cutLeftAux
#print axioms FOL.Hauptsatz0.hauptsatz
#print axioms FOL.Hauptsatz0.cut_elimination
#print axioms FOL.Hauptsatz0.herbrand_extraction
#print axioms FOL.Hauptsatz0.herbrand
#print axioms FOL.Hauptsatz0.derives0_of_eqPropCert
#print axioms FOL.Hauptsatz0.eqPropCert_of_derives0
#print axioms FOL.Hauptsatz0.derives0_qf_iff
#print axioms FOL.Hauptsatz0.peval_true_eqInstance
