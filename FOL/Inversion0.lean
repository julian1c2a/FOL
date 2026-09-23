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
# `FOL.Inversion0` — las reglas proposicionales de `LK₀` son INVERTIBLES

    inv_implR   : Γ ⟹ (A ⇒ B), Δ      →   A, Γ ⟹ B, Δ
    inv_implL_l : (A ⇒ B), Γ ⟹ Δ      →   Γ ⟹ A, Δ
    inv_implL_r : (A ⇒ B), Γ ⟹ Δ      →   B, Γ ⟹ Δ
    inv_andR_l  : Γ ⟹ (A ∧ B), Δ      →   Γ ⟹ A, Δ
    inv_andR_r  : Γ ⟹ (A ∧ B), Δ      →   Γ ⟹ B, Δ
    inv_andL    : (A ∧ B), Γ ⟹ Δ      →   A, B, Γ ⟹ Δ
    inv_orR     : Γ ⟹ (A ∨ B), Δ      →   Γ ⟹ A, B, Δ
    inv_orL_l   : (A ∨ B), Γ ⟹ Δ      →   A, Γ ⟹ Δ
    inv_orL_r   : (A ∨ B), Γ ⟹ Δ      →   B, Γ ⟹ Δ

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

## ⛔ Lo que NO es invertible, y por qué no está

`allL` y `exR` **no** lo son en LK: su premisa elige un término `t`, y la conclusión lo olvida.
`allR` y `exL` **sí** lo son, pero su inversión pasa por el levantamiento de De Bruijn
(`Γ.map (liftFormula 0)`) y pide una identidad `substFormula 0 (var 0) (liftFormula 1 A) = A`
que aquí no se ha medido: ⬜ **no se incluyen**.

## 📏 Footprint

El de `hauptsatz`: `[propext, Quot.sound]`. **Ni un `Classical.choice`.**
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
