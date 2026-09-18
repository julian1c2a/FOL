/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.SkolemNF0, FOL.BlockExtraction0
-- @axiom_system: classical
-- @importance: high

import FOL.SkolemNF0
import FOL.BlockExtraction0

/-!
# `FOL.SkolemHerbrand0` — 🏁 EL ENCHUFE: de la forma normal de Skolem al certificado de Herbrand

    derives0_neg_allBlock_iff : (Γ ⊢₀ ¬∀ᵐψ)  ↔  (Γ ⊢₀ ∃ᵐ¬ψ)
    herbrand_of_skolemNF      : ∃ m ψ, QuantFree ψ ∧
                                 ( [] ⊢₀ ¬(skolemize k (prenex φ))
                                   ↔ ∃ tss E, HerbrandCertBlock m (¬ψ) tss E )

📏 `[propext, Quot.sound]` en todo el módulo: **ni un `Classical.choice`**.

## ⭐ Por qué hacía falta un puente, y no una composición

ADR‑062 §4 midió la juntura y midió bien: `skolemNF_shape` entrega **exactamente** `∀ᵐ ψ` con
`QuantFree ψ`, que es la hipótesis de `herbrand_block`… pero **Herbrand habla de EXISTENCIALES y
Skolem los quita**. Las dos piezas no componen: se encuentran **al otro lado de una negación**.

⇒ el enchufe es la ley de De Morgan **iterada sobre el bloque**:

    ¬(∀ᵐ ψ)  ⊣⊢  ∃ᵐ (¬ψ)

⭐ Y la mitad cara **ya era un constructor**: `Derives₀.forall_not_ex_not` (`Derives0.lean:141`) es
`¬∀A ⇒ ∃¬A`. Iterarla sobre el bloque es `impAll_ex` + `impAll_trans`, tres líneas por dirección.
La recíproca (`∃¬A ⇒ ¬∀A`) es **intuicionista** y se construye con `elim_ex` + `elim_forall`.

🔑 *Dos teoremas que «encajan por el tipo» pueden no componer: hay que mirar si uno habla del
DUAL del otro.*

## ⚠️ Dos trampas del paso intuicionista, las dos conocidas

* Bajo `elim_ex` el contexto llega **levantado**: el `∀A` de la hipótesis es `∀ (lift 1 A)`, y
  recuperar `A` exige `inst_var0` a mano.
* Y ese paso hay que **generalizarlo en el contexto** (`∀ Γ'`): un `have` con `_` no lo infiere
  — es la trampa de siempre.

## ⚠️ Lo que este módulo NO cierra

El enunciado es sobre **`[]`** y sobre la **forma normal ya calculada**. Componerlo con la
conservatividad (`skolem_conservative_nf`) para volver a `φ` y a un `Γ` cualquiera exige mover la
negación a través de la skolemización, y eso **no es lo mismo** que skolemizar la negación:
⬜ **no medido**.
-/

namespace FOL.SkolemHerbrand0

open FOL.SkolemN0
open FOL.SkolemNF0
open FOL.HerbrandBlock0
open FOL.BlockExtraction0
open FOL.PrenexNF0
open FOL.Herbrand0
open FOL.Prenex0

-- ══════════════════════════════════════════════════════════════════════════
-- ⭐ EL PUENTE: negar un bloque de ∀ es un bloque de ∃ negado
-- La mitad ⟹ es `forall_not_ex_not`, que es un CONSTRUCTOR de `Derives₀`.
-- La mitad ⟸ es intuicionista y se construye con `elim_ex` + `elim_forall`.
-- ══════════════════════════════════════════════════════════════════════════

theorem impAll_neg_allBlock : ∀ (m : Nat) (ψ : Formula),
    ImpAll (neg (allBlock m ψ)) (exBlock m (neg ψ))
  | 0, ψ => impAll_refl (neg ψ)
  | m + 1, ψ =>
      impAll_trans (fun Δ => Derives₀.forall_not_ex_not Δ (allBlock m ψ))
        (impAll_ex (impAll_neg_allBlock m ψ))

/-- `∃(¬A) ⇒ ¬(∀A)`, la mitad intuicionista. -/
theorem impAll_ex_neg_not_forall (A : Formula) :
    ImpAll (Formula.ex (neg A)) (neg (Formula.forall A)) := by
  intro Δ
  refine Derives₀.intro_impl _ _ _ ?_
  refine Derives₀.intro_impl _ _ _ ?_
  -- contexto: ∀A, ∃¬A
  refine Derives₀.elim_ex _ (neg A) _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
  -- bajo el ∃: ¬A en cabeza, contexto levantado
  refine Derives₀.elim_impl _ A Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _)) ?_
  -- ⚠️ el `∀A` del contexto llega LEVANTADO: `lift 0 (∀A) = ∀ (lift 1 A)`. Instanciarlo en `x₀`
  -- lo devuelve, pero por `inst_var0`, que hay que aplicar a mano.
  -- ⚠️ Y el paso se GENERALIZA en el contexto: un `have` con `_` no lo infiere.
  have key : ∀ Γ' : List Formula, Formula.forall (liftFormula 1 A) ∈ Γ' → Γ' ⊢₀ A := by
    intro Γ' hmem
    have h2 := Derives₀.elim_forall Γ' (liftFormula 1 A) (Term.var 0) (Derives₀.hyp _ _ hmem)
    rwa [inst_var0] at h2
  exact key _ (List.Mem.tail _ (List.Mem.head _))

theorem impAll_exBlock_neg : ∀ (m : Nat) (ψ : Formula),
    ImpAll (exBlock m (neg ψ)) (neg (allBlock m ψ))
  | 0, ψ => impAll_refl (neg ψ)
  | m + 1, ψ =>
      impAll_trans (impAll_ex (impAll_exBlock_neg m ψ))
        (impAll_ex_neg_not_forall (allBlock m ψ))

/-- 🏁 El puente, en forma de derivabilidad. -/
theorem derives0_neg_allBlock_iff (m : Nat) (ψ : Formula) (Γ : List Formula) :
    Iff (Γ ⊢₀ neg (allBlock m ψ)) (Γ ⊢₀ exBlock m (neg ψ)) :=
  ⟨fun h => Derives₀.elim_impl _ _ _ (impAll_neg_allBlock m ψ Γ) h,
   fun h => Derives₀.elim_impl _ _ _ (impAll_exBlock_neg m ψ Γ) h⟩

/-- `neg` no crea cuantificadores. -/
theorem quantFree_neg {ψ : Formula} (h : QuantFree ψ) : QuantFree (neg ψ) := ⟨h, trivial⟩


/-- 🏁🏁 **EL ENCHUFE**: la forma normal de Skolem de `φ` es REFUTABLE si y sólo si hay un
certificado de Herbrand **de bloque** para la negación de su matriz.

⭐ Las tres piezas encajan porque `skolemNF_shape` entrega exactamente `∀ᵐ ψ` con `QuantFree ψ`,
que es la hipótesis de `herbrand_block`, y el puente convierte `¬∀ᵐψ` en `∃ᵐ¬ψ`. -/
theorem herbrand_of_skolemNF (k : Nat) (φ : Formula) :
    ∃ (m : Nat) (ψ : Formula), And (QuantFree ψ)
      (Iff ([] ⊢₀ neg (skolemize k (prenex φ)))
           (∃ tss E, HerbrandCertBlock m (neg ψ) tss E)) := by
  obtain ⟨m, ψ, heq, hq⟩ := skolemNF_shape k φ
  refine ⟨m, ψ, hq, ?_⟩
  rw [heq]
  exact Iff.trans (derives0_neg_allBlock_iff m ψ []) (herbrand_block (quantFree_neg hq))

end FOL.SkolemHerbrand0

#print axioms FOL.SkolemHerbrand0.impAll_neg_allBlock
#print axioms FOL.SkolemHerbrand0.impAll_ex_neg_not_forall
#print axioms FOL.SkolemHerbrand0.derives0_neg_allBlock_iff
#print axioms FOL.SkolemHerbrand0.herbrand_of_skolemNF
