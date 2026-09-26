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
# `FOL.Inversion0` — las reglas invertibles de `LK₀`: las nueve proposicionales, `allR` y `exL`

    inv_implR   : Γ ⟹ (A ⇒ B), Δ      →   A, Γ ⟹ B, Δ
    inv_implL_l : (A ⇒ B), Γ ⟹ Δ      →   Γ ⟹ A, Δ
    inv_implL_r : (A ⇒ B), Γ ⟹ Δ      →   B, Γ ⟹ Δ
    inv_andR_l  : Γ ⟹ (A ∧ B), Δ      →   Γ ⟹ A, Δ
    inv_andR_r  : Γ ⟹ (A ∧ B), Δ      →   Γ ⟹ B, Δ
    inv_andL    : (A ∧ B), Γ ⟹ Δ      →   A, B, Γ ⟹ Δ
    inv_orR     : Γ ⟹ (A ∨ B), Δ      →   Γ ⟹ A, B, Δ
    inv_orL_l   : (A ∨ B), Γ ⟹ Δ      →   A, Γ ⟹ Δ
    inv_orL_r   : (A ∨ B), Γ ⟹ Δ      →   B, Γ ⟹ Δ
    inv_allR    : Γ ⟹ ∀A, Δ           →   Γ↑ ⟹ A, Δ↑        (↑ = `map (liftFormula 0)`)
    inv_exL     : ∃A, Γ ⟹ Δ           →   A, Γ↑ ⟹ Δ↑

## ⭐ Por qué esto es el primer dividendo del Hauptsatz fuera de Herbrand

En un cálculo de secuentes **sin corte**, invertir una regla obliga a una inducción sobre la
derivación, caso por caso. **Con el corte admisible** (`FOL.Hauptsatz0.hauptsatz : CutAdm`) cada
inversión es **un solo corte**: la premisa dada, un secuente auxiliar que la regla **dual**
deriva en un paso, y el corte sobre la fórmula principal.

🔑 *El Hauptsatz no sólo elimina el corte de las derivaciones: lo convierte en una herramienta
para PROBAR cosas sobre ellas.* Hasta hoy el único consumidor de `hauptsatz` era la extracción de
Herbrand.

## La plantilla — las nueve son la misma

Para invertir la regla que introduce `C` a la derecha:

1. **premisa 1**: la dada, `Γ ⟹ C, Δ`, **debilitada** por `struct` hasta el contexto del objetivo;
2. **premisa 2**: `C, Γ' ⟹ Δ'`, derivada con la regla **izquierda** de `C` sobre dos axiomas;
3. **corte** sobre `C`.

Y simétricamente para las reglas izquierdas. Los helpers de pertenencia **ya estaban**
(`sub_cons`, `sub_wk`, `sub_refl`, `FOL/Hauptsatz0.lean` §8.1): no se ha escrito ninguno.

## Los cuantificadores: `allR` y `exL` SÍ, `allL` y `exR` NO

`allL` y `exR` **no** son invertibles en LK: su premisa elige un término `t`, y la conclusión lo
olvida. `allR` y `exL` **sí** lo son, y con la misma plantilla de un corte: se LEVANTA la premisa
(`Hauptsatz0.lk0_lift`) y se corta contra `allL`/`exR` con `t := #0`. La identidad que eso pide,
`substFormula 0 (var 0) (liftFormula 1 A) = A`, **ya existía**: `Lift0.substFormula_lift_var`.
⚠️ Hasta el 2026‑09‑26 esta cabecera decía que la identidad «no se ha medido» y dejaba fuera las
dos inversiones (DIFERIDA en `[G.2]`); estaba escrita, y el diseño de las dos también (journal del
workflow `wf_1c371ba8-efb`). 🔑 *Antes de construir, buscar* — y antes de diferir, también.

## 📏 Footprint

El de `hauptsatz`: `[propext, Quot.sound]`, las once. **Ni un `Classical.choice`.**
-/

namespace FOL.Inversion0

open FOL.Hauptsatz0

/-- Invertir `implR`: de `Γ ⟹ A ⇒ B, Δ` a `A, Γ ⟹ B, Δ`. -/
theorem inv_implR {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ Γ (Formula.impl A B :: Δ)) : LK₀ (A :: Γ) (B :: Δ) := by
  refine hauptsatz (A :: Γ) (B :: Δ) (Formula.impl A B) ?_ ?_
  · exact LK₀.struct _ _ _ _ h (sub_wk A (sub_refl Γ))
      (sub_cons (Formula.impl A B) (sub_wk B (sub_refl Δ)))
  · refine LK₀.implL (A :: Γ) (B :: Δ) A B ?_ ?_
    · exact LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _)
    · exact LK₀.ax _ _ B (List.Mem.head _) (List.Mem.head _)

/-- Invertir `implL`, premisa izquierda: de `A ⇒ B, Γ ⟹ Δ` a `Γ ⟹ A, Δ`. -/
theorem inv_implL_l {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ (Formula.impl A B :: Γ) Δ) : LK₀ Γ (A :: Δ) := by
  refine hauptsatz Γ (A :: Δ) (Formula.impl A B) ?_ ?_
  · exact LK₀.implR Γ (A :: Δ) A B
      (LK₀.ax _ _ A (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  · exact LK₀.struct _ _ _ _ h (sub_refl _) (sub_wk A (sub_refl Δ))

/-- Invertir `implL`, premisa derecha: de `A ⇒ B, Γ ⟹ Δ` a `B, Γ ⟹ Δ`. -/
theorem inv_implL_r {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ (Formula.impl A B :: Γ) Δ) : LK₀ (B :: Γ) Δ := by
  refine hauptsatz (B :: Γ) Δ (Formula.impl A B) ?_ ?_
  · exact LK₀.implR (B :: Γ) Δ A B
      (LK₀.ax _ _ B (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _))
  · exact LK₀.struct _ _ _ _ h (sub_cons (Formula.impl A B) (sub_wk B (sub_refl Γ)))
      (sub_refl Δ)

/-- Invertir `andR`, conjunto izquierdo. -/
theorem inv_andR_l {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ Γ (Formula.and A B :: Δ)) : LK₀ Γ (A :: Δ) := by
  refine hauptsatz Γ (A :: Δ) (Formula.and A B) ?_ ?_
  · exact LK₀.struct _ _ _ _ h (sub_refl Γ)
      (sub_cons (Formula.and A B) (sub_wk A (sub_refl Δ)))
  · exact LK₀.andL Γ (A :: Δ) A B (LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _))

/-- Invertir `andR`, conjunto derecho. -/
theorem inv_andR_r {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ Γ (Formula.and A B :: Δ)) : LK₀ Γ (B :: Δ) := by
  refine hauptsatz Γ (B :: Δ) (Formula.and A B) ?_ ?_
  · exact LK₀.struct _ _ _ _ h (sub_refl Γ)
      (sub_cons (Formula.and A B) (sub_wk B (sub_refl Δ)))
  · exact LK₀.andL Γ (B :: Δ) A B
      (LK₀.ax _ _ B (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _))

/-- Invertir `andL`. -/
theorem inv_andL {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ (Formula.and A B :: Γ) Δ) : LK₀ (A :: B :: Γ) Δ := by
  refine hauptsatz (A :: B :: Γ) Δ (Formula.and A B) ?_ ?_
  · exact LK₀.andR _ _ A B (LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _))
      (LK₀.ax _ _ B (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _))
  · exact LK₀.struct _ _ _ _ h
      (sub_cons (Formula.and A B) (sub_wk A (sub_wk B (sub_refl Γ)))) (sub_refl Δ)

/-- Invertir `orR`. -/
theorem inv_orR {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ Γ (Formula.or A B :: Δ)) : LK₀ Γ (A :: B :: Δ) := by
  refine hauptsatz Γ (A :: B :: Δ) (Formula.or A B) ?_ ?_
  · exact LK₀.struct _ _ _ _ h (sub_refl Γ)
      (sub_cons (Formula.or A B) (sub_wk A (sub_wk B (sub_refl Δ))))
  · exact LK₀.orL Γ (A :: B :: Δ) A B (LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _))
      (LK₀.ax _ _ B (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))

/-- Invertir `orL`, disyunto izquierdo. -/
theorem inv_orL_l {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ (Formula.or A B :: Γ) Δ) : LK₀ (A :: Γ) Δ := by
  refine hauptsatz (A :: Γ) Δ (Formula.or A B) ?_ ?_
  · exact LK₀.orR _ _ A B (LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _))
  · exact LK₀.struct _ _ _ _ h (sub_cons (Formula.or A B) (sub_wk A (sub_refl Γ)))
      (sub_refl Δ)

/-- Invertir `orL`, disyunto derecho. -/
theorem inv_orL_r {Γ Δ : List Formula} {A B : Formula}
    (h : LK₀ (Formula.or A B :: Γ) Δ) : LK₀ (B :: Γ) Δ := by
  refine hauptsatz (B :: Γ) Δ (Formula.or A B) ?_ ?_
  · exact LK₀.orR _ _ A B
      (LK₀.ax _ _ B (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  · exact LK₀.struct _ _ _ _ h (sub_cons (Formula.or A B) (sub_wk B (sub_refl Γ)))
      (sub_refl Δ)

/-- Invertir `allR`, en su forma de EIGENVARIABLE: de `Γ ⟹ ∀A, Δ` a `Γ↑ ⟹ A, Δ↑`. Se levanta la
premisa y se corta contra `∀(A↑¹), Γ↑ ⟹ A, Δ↑`, que es `allL` con `t := #0` más
`substFormula_lift_var`. -/
theorem inv_allR {Γ Δ : List Formula} {A : Formula}
    (h : LK₀ Γ (Formula.forall A :: Δ)) :
    LK₀ (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) := by
  have hA : substFormula 0 (Term.var 0) (liftFormula 1 A) = A :=
    FOL.Lift0.substFormula_lift_var A 0
  have P : LK₀ (Γ.map (liftFormula 0))
      (Formula.forall (liftFormula 1 A) :: Δ.map (liftFormula 0)) := lk0_lift h 0
  refine hauptsatz (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0))
    (Formula.forall (liftFormula 1 A)) ?_ ?_
  · exact LK₀.struct (Γ.map (liftFormula 0)) (Γ.map (liftFormula 0))
      (Formula.forall (liftFormula 1 A) :: Δ.map (liftFormula 0))
      (Formula.forall (liftFormula 1 A) :: A :: Δ.map (liftFormula 0)) P
      (sub_refl _) (sub_cons _ (sub_wk A (sub_refl _)))
  · refine LK₀.allL (Γ.map (liftFormula 0)) (A :: Δ.map (liftFormula 0)) (liftFormula 1 A)
      (Term.var 0) ?_
    rw [hA]
    exact LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _)

/-- Invertir `exL`: de `∃A, Γ ⟹ Δ` a `A, Γ↑ ⟹ Δ↑`, cortando contra `A, Γ↑ ⟹ ∃(A↑¹), Δ↑`
(`exR` con `t := #0`). -/
theorem inv_exL {Γ Δ : List Formula} {A : Formula}
    (h : LK₀ (Formula.ex A :: Γ) Δ) :
    LK₀ (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) := by
  have hA : substFormula 0 (Term.var 0) (liftFormula 1 A) = A :=
    FOL.Lift0.substFormula_lift_var A 0
  have Q : LK₀ (Formula.ex (liftFormula 1 A) :: Γ.map (liftFormula 0))
      (Δ.map (liftFormula 0)) := lk0_lift h 0
  refine hauptsatz (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0))
    (Formula.ex (liftFormula 1 A)) ?_ ?_
  · refine LK₀.exR (A :: Γ.map (liftFormula 0)) (Δ.map (liftFormula 0)) (liftFormula 1 A)
      (Term.var 0) ?_
    rw [hA]
    exact LK₀.ax _ _ A (List.Mem.head _) (List.Mem.head _)
  · exact LK₀.struct (Formula.ex (liftFormula 1 A) :: Γ.map (liftFormula 0))
      (Formula.ex (liftFormula 1 A) :: A :: Γ.map (liftFormula 0))
      (Δ.map (liftFormula 0)) (Δ.map (liftFormula 0)) Q
      (sub_cons _ (sub_wk A (sub_refl _))) (sub_refl _)

end FOL.Inversion0

/-! ## FOOTPRINT -/
#print axioms FOL.Inversion0.inv_implR
#print axioms FOL.Inversion0.inv_implL_l
#print axioms FOL.Inversion0.inv_implL_r
#print axioms FOL.Inversion0.inv_andR_l
#print axioms FOL.Inversion0.inv_andR_r
#print axioms FOL.Inversion0.inv_andL
#print axioms FOL.Inversion0.inv_orR
#print axioms FOL.Inversion0.inv_orL_l
#print axioms FOL.Inversion0.inv_orL_r
#print axioms FOL.Inversion0.inv_allR
#print axioms FOL.Inversion0.inv_exL
