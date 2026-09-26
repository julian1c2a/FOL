/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: none
-- @importance: medium

import FOL.FOL

/-!
# `FOL.Complexity` — la COMPLEJIDAD de una fórmula, y que sustituir no la cambia

    formulaComplexity      : Formula → Nat
    complexity_substFormula : formulaComplexity (substFormula v t f) = formulaComplexity f

## Por qué existe este módulo, y por qué es TAN pequeño

⭐ Las dos declaraciones vivían en `FOL/Canonical0.lean` §5 — o sea **detrás de `Soundness0` y
de toda la cadena clásica de completitud**— y son **puramente sintácticas**: sólo mencionan
`Formula`, `substFormula`, `Nat` y `max`. Nada de semántica, nada de derivabilidad.

⇒ quien sólo necesite la medida de complejidad tenía que arrastrar la completitud entera.

🔑 *Que una definición esté donde se usó por primera vez no es una razón para que se quede ahí.*

## Procedencia

**Encargo de PeanoRF §3** (`../Peano-from-ROB-n-FOL/doc/ENCARGO-FOL-2026-09-17.md`), aceptado el
2026‑09‑23: *«son puramente sintácticos y no tienen por qué estar ahí. Si bajan a un módulo base,
PeanoRF retira el `fdepth` que hoy tiene duplicado y declarado como deuda»*.

⚠️ **Los nombres y las firmas NO cambian.** `FOL.Canonical0` hace `open FOL.Complexity`, así que
sus quince sitios de uso siguen escritos igual. Es la misma técnica que los `abbrev` de
ADR‑068: *mover una definición no tiene por qué mover sus citas.*

## 📏 Footprint

`complexity_substFormula` — `[propext]` (medido); cero axiomas del proyecto. Es una inducción estructural sobre `Formula`.

## ⚠️ La copia de `cuarentena/`

`cuarentena/Completeness.lean` tenía su propia copia de las dos; se **borró** el 2026‑09‑23 con
el resto del código de `cuarentena/`, así que ya no hay copia.
-/

namespace FOL.Complexity

/-- La **complejidad** de una fórmula: la profundidad de sus conectivas y cuantificadores.
⚠️ Los átomos y las igualdades valen `0` **a propósito**: la inducción que la consume
(`truth_lemma`) no baja por dentro de los términos. -/
def formulaComplexity : Formula → Nat
  | .bottom => 0
  | .atom _ _ => 0
  | .eq _ _ => 0
  | .impl f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .forall f1 => formulaComplexity f1 + 1
  | .and f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .or f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .ex f1 => formulaComplexity f1 + 1

/-- 🔑 **Sustituir no cambia la complejidad** — sin esto, la inducción del lema de la verdad no
cierra, porque el caso `∀` baja a `substFormula 0 t f₁`, que no es subtérmino de `∀f₁`. -/
@[simp]
theorem complexity_substFormula (v : Nat) (t : Term) (f : Formula) :
    formulaComplexity (substFormula v t f) = formulaComplexity f := by
  induction f generalizing v t with
  | bottom => rfl
  | atom _ _ => rfl
  | eq _ _ => rfl
  | impl _ _ ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | and _ _ ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | or _ _ ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | «forall» _ ih => simp only [formulaComplexity, substFormula, ih]
  | ex _ ih => simp only [formulaComplexity, substFormula, ih]

end FOL.Complexity

/-! ## FOOTPRINT -/
#print axioms FOL.Complexity.complexity_substFormula
