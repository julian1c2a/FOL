/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives0, FOL.Theorems.Eq
-- @axiom_system: classical
-- @importance: high

import FOL.Derives0
import FOL.Theorems.Eq

/-!
# `FOL.Eq0` — las cuatro piezas de la IGUALDAD sobre `Derives₀`

Simetría, transitividad y las dos **congruencias en una posición** de la lista de argumentos, que
es lo que el modelo canónico necesita para que el cociente por `t ≈ u :⇔ S(t ≐ u)` esté bien
definido.

## ⭐ Es un traslado LITERAL, y eso es un dato

Las cuatro son las de `FOL/Theorems/Eq.lean` (ADR‑031) con `Derives` cambiado por `Derives₀`:
**ni una línea de prueba distinta**. Sale así porque `refl` y `subst` son **constructores de los
dos** cálculos, y porque toda la parte difícil —`substTerms_append`, `substTerms_lift_hole`,
`substTerm_liftTerm`— es **sintaxis pura**, ajena al cálculo, y se importa tal cual.

🔑 *Lo que hacía falta para las congruencias no era lógica sino LISTAS* (ADR‑031), y las listas no
distinguen `Derives` de `Derives₀`.

## 📏 Footprint

`[propext, Quot.sound]` las cuatro: **ni un `Classical.choice`**. La igualdad de este cálculo es
enteramente constructiva.
-/

namespace FOL.Eq0

theorem derives0_eq_symm {Γ : List Formula} {t1 t2 : Term} (h : Derives₀ Γ (.eq t1 t2)) :
    Derives₀ Γ (.eq t2 t1) := by
  let f := Formula.eq (.var 0) (liftTerm 0 t1)
  have hSubst1 : substFormula 0 t1 f = Formula.eq t1 t1 := by
    change Formula.eq (substTerm 0 t1 (.var 0)) (substTerm 0 t1 (liftTerm 0 t1)) = Formula.eq t1 t1
    rw [substTerm_liftTerm t1 0 t1]
    rfl
  have hSubst2 : substFormula 0 t2 f = Formula.eq t2 t1 := by
    change Formula.eq (substTerm 0 t2 (.var 0)) (substTerm 0 t2 (liftTerm 0 t1)) = Formula.eq t2 t1
    rw [substTerm_liftTerm t1 0 t2]
    rfl
  have hSubstDer := Derives₀.subst Γ t1 t2 f h
  rw [hSubst1] at hSubstDer
  have hDer2 := hSubstDer (Derives₀.refl Γ t1)
  rw [hSubst2] at hDer2
  exact hDer2

theorem derives0_eq_trans {Γ : List Formula} {t1 t2 t3 : Term}
    (h12 : Derives₀ Γ (.eq t1 t2)) (h23 : Derives₀ Γ (.eq t2 t3)) :
    Derives₀ Γ (.eq t1 t3) := by
  let f := Formula.eq (liftTerm 0 t1) (.var 0)
  have hSubst2 : substFormula 0 t2 f = Formula.eq t1 t2 := by
    change Formula.eq (substTerm 0 t2 (liftTerm 0 t1)) (substTerm 0 t2 (.var 0)) = Formula.eq t1 t2
    rw [substTerm_liftTerm t1 0 t2]
    rfl
  have hSubst3 : substFormula 0 t3 f = Formula.eq t1 t3 := by
    change Formula.eq (substTerm 0 t3 (liftTerm 0 t1)) (substTerm 0 t3 (.var 0)) = Formula.eq t1 t3
    rw [substTerm_liftTerm t1 0 t3]
    rfl
  have hSubstDer := Derives₀.subst Γ t2 t3 f h23
  rw [hSubst2] at hSubstDer
  have hDer3 := hSubstDer h12
  rw [hSubst3] at hDer3
  exact hDer3

/-- Congruencia de `Term.func` en UNA posición de sus argumentos. -/
theorem derives0_eq_func_congr {Γ : List Formula} (p : String) (pre post : List Term)
    {a b : Term} (h : Derives₀ Γ (.eq a b)) :
    Derives₀ Γ (.eq (Term.func p (pre ++ a :: post)) (Term.func p (pre ++ b :: post))) := by
  have key : ∀ x : Term,
      substFormula 0 x
        (Formula.eq (liftTerm 0 (Term.func p (pre ++ a :: post)))
                    (Term.func p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)))
        = Formula.eq (Term.func p (pre ++ a :: post)) (Term.func p (pre ++ x :: post)) := by
    intro x
    show Formula.eq (substTerm 0 x (liftTerm 0 (Term.func p (pre ++ a :: post))))
                    (Term.func p
                      (substTerms 0 x (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)))
         = _
    rw [substTerm_liftTerm, substTerms_lift_hole]
  have hstep := Derives₀.subst Γ a b
      (Formula.eq (liftTerm 0 (Term.func p (pre ++ a :: post)))
                  (Term.func p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post))) h
  rw [key a, key b] at hstep
  exact hstep (Derives₀.refl Γ _)

/-- Congruencia de `Formula.atom` en UNA posición de sus argumentos. -/
theorem derives0_atom_congr {Γ : List Formula} (p : String) (pre post : List Term)
    {a b : Term} (h : Derives₀ Γ (.eq a b))
    (hA : Derives₀ Γ (.atom p (pre ++ a :: post))) :
    Derives₀ Γ (.atom p (pre ++ b :: post)) := by
  have key : ∀ x : Term,
      substFormula 0 x (Formula.atom p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post))
        = Formula.atom p (pre ++ x :: post) := by
    intro x
    show Formula.atom p
          (substTerms 0 x (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)) = _
    rw [substTerms_lift_hole]
  have hstep := Derives₀.subst Γ a b
      (Formula.atom p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)) h
  rw [key a, key b] at hstep
  exact hstep hA

end FOL.Eq0

#print axioms FOL.Eq0.derives0_eq_symm
#print axioms FOL.Eq0.derives0_eq_trans
#print axioms FOL.Eq0.derives0_eq_func_congr
#print axioms FOL.Eq0.derives0_atom_congr
