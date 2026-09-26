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
    herbrand_validity₀        : ([] ⊢₀ φ) ↔ ∃ tss E, HerbrandCertBlock m (¬ψ) tss E,
                                 con skolemize k (prenex ¬φ) = ∀ᵐ ψ          (§3, D3)
    herbrand_validity_ctx₀    : (Γ ⊢₀ φ)  ↔ … la misma, para Γ ⇒ φ            (§3, D3)

📏 §1‑§2: `[propext, Quot.sound]`, **ni un `Classical.choice`**. §3 (volver a `φ`): los titulares
llevan `[propext, Classical.choice, Quot.sound]` — medido —, porque retirar los axiomas de Skolem
(`skolem_conservative_nf`) pasa por la completitud (el WKL). Por la estructura de la prueba entra
sólo en la dirección «certificado ⇒ derivación de `φ`» (la que retira los axiomas de Skolem); la otra
no pasa por la conservatividad. (Las dos mitades no se imprimen por separado.)

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

## 🏁 §3 · Volver a `φ` y a `Γ` (D3, 2026‑09‑26)

Esta cabecera decía que componer con la conservatividad para volver a `φ` y a un `Γ` cualquiera
«exige mover la negación a través de la skolemización», y lo dejaba como deuda sin medir. **No
hace falta moverla**: se skolemiza la fórmula que se quiere **refutar**.

* `derives0_neg_iff_neg_skolemNF`: `⊢₀ ¬φ ⟺ ⊢₀ ¬Sk(prenex φ)`, con las constantes de Skolem
  frescas en `φ`. ⟹ porque la forma normal implica el prenexo; ⟸ porque los axiomas de Skolem dan
  la forma normal desde `φ` y se retiran por conservatividad (`⊥` no los menciona).
* Para la **validez** de `φ` se refuta `¬φ`: la forma de Skolem de `¬φ` **es** la forma de Herbrand
  de `φ`. No hay una `herbrandize` aparte porque no hace falta.
* El contexto entra por la cadena de implicaciones: `Γ ⊢₀ φ ⟺ ⊢₀ Γ ⇒ φ`.

⚠️ La ecuación `skolemize k (prenex …) = allBlock m ψ` va DENTRO de los enunciados: sin ella `ψ`
quedaría suelta y el `↔` no diría nada de `φ`.
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

-- ══════════════════════════════════════════════════════════════════════════
-- §3 · 🏁 HERBRAND PARA `φ` Y `Γ` CUALESQUIERA (D3, 2026-09-26)
-- La negación NO hay que moverla a través de la skolemización: basta skolemizar la fórmula
-- que se quiere REFUTAR. Para la validez de `φ` se refuta `¬φ`, y la forma de Skolem de `¬φ`
-- ES la forma de Herbrand de `φ` (salvo la negación exterior).
-- ══════════════════════════════════════════════════════════════════════════

open FOL.Eigenvariable (occursFormula)
open FOL.Fresh0 (cst)

/-- ⭐ **Refutar `φ` es refutar su forma normal de Skolem.** ⟹ sin hipótesis: la forma normal
IMPLICA el prenexo (`derives0_of_skolemizeF`), y éste equivale a `φ`. ⟸ con las constantes de
Skolem FRESCAS en `φ`: los axiomas de Skolem dan la forma normal desde `φ`, y se retiran por
conservatividad (`skolem_conservative_nf`) porque `⊥` no los menciona. -/
theorem derives0_neg_iff_neg_skolemNF (k : Nat) (φ : Formula)
    (hφ : ∀ m, k ≤ m → Not (occursFormula (cst m) φ)) :
    Iff ([] ⊢₀ neg φ) ([] ⊢₀ neg (skolemize k (prenex φ))) := by
  constructor
  · intro h
    refine Derives₀.intro_impl _ _ _ ?_
    have hS : [skolemize k (prenex φ)] ⊢₀ skolemize k (prenex φ) :=
      Derives₀.hyp _ _ (List.Mem.head _)
    have hP : [skolemize k (prenex φ)] ⊢₀ φ :=
      (derives0_prenex_iff _ φ).mpr (derives0_of_skolemizeF _ _ _ _ _ hS)
    exact Derives₀.elim_impl _ _ _
      (Derives₀.weakening _ _ _ h (fun _ hx => absurd hx List.not_mem_nil)) hP
  · intro h
    refine Derives₀.intro_impl _ _ _ ?_
    refine skolem_conservative_nf k (prenex φ) [φ] Formula.bottom
      (fun m hm g hg => by
        cases hg with
        | head => exact hφ m hm
        | tail _ h2 => exact absurd h2 List.not_mem_nil)
      (fun m hm => not_occurs_prenex (hφ m hm)) (fun _ _ hc => hc) ?_
    have hφ' : (skolemAxioms k (prenex φ) ++ [φ]) ⊢₀ φ :=
      Derives₀.hyp _ _ (List.mem_append_right _ (List.Mem.head _))
    have hSk : (skolemAxioms k (prenex φ) ++ [φ]) ⊢₀ skolemize k (prenex φ) :=
      derives0_skolemize k (prenex φ) _ (fun g hg => List.mem_append_left _ hg)
        ((derives0_prenex_iff _ φ).mp hφ')
    exact Derives₀.elim_impl _ _ _
      (Derives₀.weakening _ _ _ h (fun _ hx => absurd hx List.not_mem_nil)) hSk

/-- 🏁🏁 **HERBRAND, FORMA DE REFUTACIÓN, para `φ` cualquiera**: `φ` es refutable si y sólo si hay
un certificado de Herbrand de bloque para la negación de la matriz de su forma normal de Skolem.
⭐ La ecuación `skolemize k (prenex φ) = allBlock m ψ` va en el enunciado: sin ella, `ψ` quedaría
suelta y el `↔` no diría nada de `φ`. -/
theorem herbrand_refutation₀ (k : Nat) (φ : Formula)
    (hφ : ∀ m, k ≤ m → Not (occursFormula (cst m) φ)) :
    ∃ (m : Nat) (ψ : Formula), And (skolemize k (prenex φ) = allBlock m ψ)
      (And (QuantFree ψ)
        (Iff ([] ⊢₀ neg φ) (∃ tss E, HerbrandCertBlock m (neg ψ) tss E))) := by
  obtain ⟨m, ψ, heq, hq⟩ := skolemNF_shape k φ
  refine ⟨m, ψ, heq, hq, ?_⟩
  refine Iff.trans (derives0_neg_iff_neg_skolemNF k φ hφ) ?_
  rw [heq]
  exact Iff.trans (derives0_neg_allBlock_iff m ψ []) (herbrand_block (quantFree_neg hq))

/-- La doble negación, en las dos direcciones (`dne_rule` es un constructor). -/
theorem derives0_iff_neg_neg (Γ : List Formula) (φ : Formula) :
    Iff (Γ ⊢₀ φ) (Γ ⊢₀ neg (neg φ)) :=
  ⟨fun h => Derives₀.intro_impl _ _ _ (Derives₀.elim_impl _ _ _
      (Derives₀.hyp _ _ (List.Mem.head _))
      (Derives₀.weakening _ _ _ h (fun _ hx => List.Mem.tail _ hx))),
   fun h => Derives₀.dne_rule _ _ h⟩

/-- 🏁🏁🏁 **EL TEOREMA DE HERBRAND, FORMA DE VALIDEZ, para `φ` cualquiera**: `φ` es derivable si
y sólo si hay un certificado de Herbrand de bloque para la matriz de la forma normal de Skolem de
`¬φ` — que es la **forma de Herbrand** de `φ`. No hace falta una `herbrandize` aparte: skolemizar
la negación ES herbrandizar. -/
theorem herbrand_validity₀ (k : Nat) (φ : Formula)
    (hφ : ∀ m, k ≤ m → Not (occursFormula (cst m) φ)) :
    ∃ (m : Nat) (ψ : Formula), And (skolemize k (prenex (neg φ)) = allBlock m ψ)
      (And (QuantFree ψ)
        (Iff ([] ⊢₀ φ) (∃ tss E, HerbrandCertBlock m (neg ψ) tss E))) := by
  obtain ⟨m, ψ, heq, hq, hiff⟩ := herbrand_refutation₀ k (neg φ)
    (fun m hm hc => hc.elim (hφ m hm) (fun hb => hb))
  exact ⟨m, ψ, heq, hq, Iff.trans (derives0_iff_neg_neg [] φ) hiff⟩

/-- La cadena de implicaciones recoge el contexto: `Γ ⊢₀ φ` da `⊢₀ Γ ⇒ φ`. -/
theorem implChain_of_derives0 : ∀ (Γ Δ : List Formula) (φ : Formula),
    ((Γ ++ Δ) ⊢₀ φ) → Δ ⊢₀ FOL.Propositional0.implChain Γ φ
  | [], _, _, h => h
  | g :: Γ', Δ, φ, h => by
      refine Derives₀.intro_impl _ _ _ ?_
      refine implChain_of_derives0 Γ' (g :: Δ) φ ?_
      refine Derives₀.weakening _ _ _ h (fun x hx => ?_)
      cases hx with
      | head => exact List.mem_append_right _ (List.Mem.head _)
      | tail _ h2 =>
          rcases List.mem_append.mp h2 with h3 | h3
          · exact List.mem_append_left _ h3
          · exact List.mem_append_right _ (List.Mem.tail _ h3)

/-- Y la vuelta: `⊢₀ Γ ⇒ φ` da `Γ ⊢₀ φ`. -/
theorem derives0_iff_implChain (Γ : List Formula) (φ : Formula) :
    Iff (Γ ⊢₀ φ) ([] ⊢₀ FOL.Propositional0.implChain Γ φ) :=
  ⟨fun h => implChain_of_derives0 Γ [] φ (by rw [List.append_nil]; exact h),
   fun h => FOL.Propositional0.derives0_of_implChain Γ Γ φ
     (Derives₀.weakening _ _ _ h (fun _ hx => absurd hx List.not_mem_nil)) (fun _ hx => hx)⟩

theorem not_occurs_implChain {c : String} :
    ∀ (Γ : List Formula) (φ : Formula), (∀ g, g ∈ Γ → Not (occursFormula c g)) →
      Not (occursFormula c φ) → Not (occursFormula c (FOL.Propositional0.implChain Γ φ))
  | [], _, _, hφ => hφ
  | g :: Γ', φ, hΓ, hφ => fun hc => hc.elim (hΓ g (List.Mem.head _))
      (not_occurs_implChain Γ' φ (fun x hx => hΓ x (List.Mem.tail _ hx)) hφ)

/-- 🏁🏁🏁 **HERBRAND CON CONTEXTO**: `Γ ⊢₀ φ` si y sólo si hay un certificado de Herbrand para la
forma de Herbrand de `Γ ⇒ φ`. Con esto cae la deuda que esta cabecera declaraba ABIERTA. -/
theorem herbrand_validity_ctx₀ (k : Nat) (Γ : List Formula) (φ : Formula)
    (hΓ : ∀ m, k ≤ m → ∀ g, g ∈ Γ → Not (occursFormula (cst m) g))
    (hφ : ∀ m, k ≤ m → Not (occursFormula (cst m) φ)) :
    ∃ (m : Nat) (ψ : Formula),
      And (skolemize k (prenex (neg (FOL.Propositional0.implChain Γ φ))) = allBlock m ψ)
        (And (QuantFree ψ)
          (Iff (Γ ⊢₀ φ) (∃ tss E, HerbrandCertBlock m (neg ψ) tss E))) := by
  obtain ⟨m, ψ, heq, hq, hiff⟩ := herbrand_validity₀ k (FOL.Propositional0.implChain Γ φ)
    (fun m hm => not_occurs_implChain Γ φ (hΓ m hm) (hφ m hm))
  exact ⟨m, ψ, heq, hq, Iff.trans (derives0_iff_implChain Γ φ) hiff⟩

end FOL.SkolemHerbrand0

#print axioms FOL.SkolemHerbrand0.impAll_neg_allBlock
#print axioms FOL.SkolemHerbrand0.impAll_ex_neg_not_forall
#print axioms FOL.SkolemHerbrand0.derives0_neg_allBlock_iff
#print axioms FOL.SkolemHerbrand0.herbrand_of_skolemNF
#print axioms FOL.SkolemHerbrand0.derives0_neg_iff_neg_skolemNF
#print axioms FOL.SkolemHerbrand0.herbrand_refutation₀
#print axioms FOL.SkolemHerbrand0.derives0_iff_neg_neg
#print axioms FOL.SkolemHerbrand0.herbrand_validity₀
#print axioms FOL.SkolemHerbrand0.implChain_of_derives0
#print axioms FOL.SkolemHerbrand0.derives0_iff_implChain
#print axioms FOL.SkolemHerbrand0.herbrand_validity_ctx₀
