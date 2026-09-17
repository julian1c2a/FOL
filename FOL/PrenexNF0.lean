/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Prenex0, FOL.Derives1
-- @axiom_system: classical
-- @importance: high

import FOL.Prenex0
import FOL.Derives1

/-!
# `FOL.PrenexNF0` — la FORMA NORMAL prenexa, con su corrección

    prenex              : Formula → Formula
    derives0_prenex_iff : (Γ ⊢₀ φ) ↔ (Γ ⊢₀ prenex φ)

## ⭐⭐ La terminación NO hace falta, y eso era lo que se daba por caro

ADR‑057 §4 estimó esta pieza en «~200 l., riesgo **medio**: lo caro es la **medida de
terminación**». **Falso, y lo dice el compilador**: las seis definiciones las acepta Lean por
**recursión estructural**, sin `termination_by` ni `decreasing_by`.

🔑 La razón es una y vale para toda la familia: **se recurre sobre UN argumento y se LEVANTA el
otro**. `mergeAnd (∀A') B = ∀ (mergeAnd A' (liftFormula 0 B))` decrece en el primero, y que el
segundo cambie da igual — no es el argumento de la recursión. *Cuando la recursión y la
transformación van por argumentos distintos, no hay que medir nada.*

## ⭐ Dos fases por conectiva, y por eso son estructurales

Sacar los cuantificadores de `A ∧ B` son dos pasadas: primero los de `A` (recurriendo en `A`),
y cuando `A` ya no tiene prefijo, los de `B` (recurriendo en `B`). De ahí el par
`mergeAnd`/`mergeAndR`, y sus gemelos para `∨` y `→`.

⚠️ **Y a la izquierda de una implicación el cuantificador SE DA LA VUELTA**:
`mergeImpl (∀A') B = ∃ (mergeImpl A' B↑)`. Es la única asimetría de las seis definiciones, y viene
de la equivalencia 5 de `FOL.Prenex0`.

## ⭐ Las congruencias no se escribieron: se ENVOLVIERON

`FOL.Derives1` ya tenía las ocho congruencias, y con la hipótesis **esquemática en el contexto**
(`∀ Δ, Δ ⊢₁ …`) — que es justo lo que hace falta para meterlas bajo un binder, donde el contexto
llega levantado. ⇒ dos líneas de envoltorio cada una, vía `derives0_iff_derives1`, en vez de
noventa de reescritura. *Antes de construir, buscar* — van ocho.

## 📏 Footprint

`[propext, Quot.sound]`. **Ni un `Classical.choice`.** (`iffAll_trans`, sin ningún axioma.)
-/

namespace FOL.PrenexNF0

open FOL.Prenex0
open FOL.Derives1

-- ── las FUSIONES: cada una recurre ESTRUCTURALMENTE sobre UN argumento,
--    y el otro simplemente se levanta (`liftFormula` no cambia el tamaño).
def mergeAndR : Formula → Formula → Formula
  | A, .forall B' => .forall (mergeAndR (liftFormula 0 A) B')
  | A, .ex B' => .ex (mergeAndR (liftFormula 0 A) B')
  | A, B => .and A B

def mergeAnd : Formula → Formula → Formula
  | .forall A', B => .forall (mergeAnd A' (liftFormula 0 B))
  | .ex A', B => .ex (mergeAnd A' (liftFormula 0 B))
  | A, B => mergeAndR A B

def mergeOrR : Formula → Formula → Formula
  | A, .forall B' => .forall (mergeOrR (liftFormula 0 A) B')
  | A, .ex B' => .ex (mergeOrR (liftFormula 0 A) B')
  | A, B => .or A B

def mergeOr : Formula → Formula → Formula
  | .forall A', B => .forall (mergeOr A' (liftFormula 0 B))
  | .ex A', B => .ex (mergeOr A' (liftFormula 0 B))
  | A, B => mergeOrR A B

def mergeImplR : Formula → Formula → Formula
  | A, .forall B' => .forall (mergeImplR (liftFormula 0 A) B')
  | A, .ex B' => .ex (mergeImplR (liftFormula 0 A) B')
  | A, B => .impl A B

-- ⚠️ A la IZQUIERDA de una implicación el cuantificador se DA LA VUELTA.
def mergeImpl : Formula → Formula → Formula
  | .forall A', B => .ex (mergeImpl A' (liftFormula 0 B))
  | .ex A', B => .forall (mergeImpl A' (liftFormula 0 B))
  | A, B => mergeImplR A B

def prenex : Formula → Formula
  | .bottom => .bottom
  | .atom p ts => .atom p ts
  | .eq t u => .eq t u
  | .forall f => .forall (prenex f)
  | .ex f => .ex (prenex f)
  | .and a b => mergeAnd (prenex a) (prenex b)
  | .or a b => mergeOr (prenex a) (prenex b)
  | .impl a b => mergeImpl (prenex a) (prenex b)

-- ── §1 · equivalencia ESQUEMÁTICA en el contexto ────────────────────────────
-- ⚠️ Esquemática (`∀ Δ`) a propósito: es lo que permite meterla bajo un binder,
-- donde el contexto llega LEVANTADO. Es la forma que ya usan las congruencias
-- de `Derives₁`, y por eso encajan sin adaptador.
def ImpAll (X Y : Formula) : Prop := ∀ Δ : List Formula, Δ ⊢₀ Formula.impl X Y
def IffAll (X Y : Formula) : Prop := ∀ Δ : List Formula, Δ ⊢₀ iff X Y

theorem iffL {X Y : Formula} (h : IffAll X Y) : ImpAll X Y :=
  fun Δ => Derives₀.elim_and_l _ _ _ (h Δ)
theorem iffR {X Y : Formula} (h : IffAll X Y) : ImpAll Y X :=
  fun Δ => Derives₀.elim_and_r _ _ _ (h Δ)
theorem mkIff {X Y : Formula} (h1 : ImpAll X Y) (h2 : ImpAll Y X) : IffAll X Y :=
  fun Δ => Derives₀.intro_and _ _ _ (h1 Δ) (h2 Δ)

theorem impAll_refl (X : Formula) : ImpAll X X :=
  fun _ => Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
theorem iffAll_refl (X : Formula) : IffAll X X := mkIff (impAll_refl X) (impAll_refl X)

theorem impAll_trans {X Y Z : Formula} (h1 : ImpAll X Y) (h2 : ImpAll Y Z) : ImpAll X Z :=
  fun _ => Derives₀.intro_impl _ _ _
    (Derives₀.elim_impl _ Y Z (h2 _)
      (Derives₀.elim_impl _ X Y (h1 _) (Derives₀.hyp _ _ (List.Mem.head _))))

theorem iffAll_trans {X Y Z : Formula} (h1 : IffAll X Y) (h2 : IffAll Y Z) : IffAll X Z :=
  mkIff (impAll_trans (iffL h1) (iffL h2)) (impAll_trans (iffR h2) (iffR h1))

theorem iffAll_symm {X Y : Formula} (h : IffAll X Y) : IffAll Y X := mkIff (iffR h) (iffL h)

-- ── §2 · las CONGRUENCIAS, envueltas desde `Derives₁` en dos líneas ─────────
private theorem up {X Y : Formula} (h : ImpAll X Y) : ∀ Δ : List Formula, Δ ⊢₁ Formula.impl X Y :=
  fun Δ => FOL.Derives1.derives0_iff_derives1.mp (h Δ)
private theorem down {X Y : Formula} (h : ∀ Δ : List Formula, Δ ⊢₁ Formula.impl X Y) :
    ImpAll X Y := fun Δ => FOL.Derives1.derives0_iff_derives1.mpr (h Δ)

theorem impAll_forall {X Y : Formula} (h : ImpAll X Y) :
    ImpAll (Formula.forall X) (Formula.forall Y) := down (fun Δ => forall_congr (up h) Δ)
theorem impAll_ex {X Y : Formula} (h : ImpAll X Y) :
    ImpAll (Formula.ex X) (Formula.ex Y) := down (fun Δ => ex_congr (up h) Δ)
theorem impAll_and_l {X Y : Formula} (Z : Formula) (h : ImpAll X Y) :
    ImpAll (Formula.and X Z) (Formula.and Y Z) := down (fun Δ => and_congr_l Z (up h) Δ)
theorem impAll_and_r {X Y : Formula} (Z : Formula) (h : ImpAll X Y) :
    ImpAll (Formula.and Z X) (Formula.and Z Y) := down (fun Δ => and_congr_r Z (up h) Δ)
theorem impAll_or_l {X Y : Formula} (Z : Formula) (h : ImpAll X Y) :
    ImpAll (Formula.or X Z) (Formula.or Y Z) := down (fun Δ => or_congr_l Z (up h) Δ)
theorem impAll_or_r {X Y : Formula} (Z : Formula) (h : ImpAll X Y) :
    ImpAll (Formula.or Z X) (Formula.or Z Y) := down (fun Δ => or_congr_r Z (up h) Δ)
theorem impAll_impl_l {X Y : Formula} (Z : Formula) (h : ImpAll Y X) :
    ImpAll (Formula.impl X Z) (Formula.impl Y Z) := down (fun Δ => impl_congr_l Z (up h) Δ)
theorem impAll_impl_r {X Y : Formula} (Z : Formula) (h : ImpAll X Y) :
    ImpAll (Formula.impl Z X) (Formula.impl Z Y) := down (fun Δ => impl_congr_r Z (up h) Δ)

theorem iffAll_forall {X Y : Formula} (h : IffAll X Y) :
    IffAll (Formula.forall X) (Formula.forall Y) :=
  mkIff (impAll_forall (iffL h)) (impAll_forall (iffR h))
theorem iffAll_ex {X Y : Formula} (h : IffAll X Y) : IffAll (Formula.ex X) (Formula.ex Y) :=
  mkIff (impAll_ex (iffL h)) (impAll_ex (iffR h))
theorem iffAll_and {X Y Z W : Formula} (h1 : IffAll X Y) (h2 : IffAll Z W) :
    IffAll (Formula.and X Z) (Formula.and Y W) :=
  mkIff (impAll_trans (impAll_and_l Z (iffL h1)) (impAll_and_r Y (iffL h2)))
        (impAll_trans (impAll_and_l W (iffR h1)) (impAll_and_r X (iffR h2)))
theorem iffAll_or {X Y Z W : Formula} (h1 : IffAll X Y) (h2 : IffAll Z W) :
    IffAll (Formula.or X Z) (Formula.or Y W) :=
  mkIff (impAll_trans (impAll_or_l Z (iffL h1)) (impAll_or_r Y (iffL h2)))
        (impAll_trans (impAll_or_l W (iffR h1)) (impAll_or_r X (iffR h2)))
theorem iffAll_impl {X Y Z W : Formula} (h1 : IffAll X Y) (h2 : IffAll Z W) :
    IffAll (Formula.impl X Z) (Formula.impl Y W) :=
  mkIff (impAll_trans (impAll_impl_l Z (iffR h1)) (impAll_impl_r Y (iffL h2)))
        (impAll_trans (impAll_impl_l W (iffL h1)) (impAll_impl_r X (iffR h2)))

-- ── §3 · conmutatividad, y las cuatro versiones POR LA DERECHA ─────────────
theorem and_commA (X Y : Formula) : IffAll (Formula.and X Y) (Formula.and Y X) := by
  refine mkIff (fun _ => Derives₀.intro_impl _ _ _ ?_) (fun _ => Derives₀.intro_impl _ _ _ ?_) <;>
    exact Derives₀.intro_and _ _ _
      (Derives₀.elim_and_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)))
      (Derives₀.elim_and_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)))

theorem or_commA (X Y : Formula) : IffAll (Formula.or X Y) (Formula.or Y X) := by
  refine mkIff (fun _ => Derives₀.intro_impl _ _ _ ?_) (fun _ => Derives₀.intro_impl _ _ _ ?_) <;>
    exact Derives₀.elim_or _ _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
      (Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)))
      (Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)))

theorem and_forall_r (B A : Formula) :
    IffAll (Formula.and B (Formula.forall A)) (Formula.forall (Formula.and (liftFormula 0 B) A)) :=
  iffAll_trans (and_commA B (Formula.forall A))
    (iffAll_trans (fun Δ => and_forall Δ A B)
      (iffAll_forall (and_commA A (liftFormula 0 B))))

theorem and_ex_r (B A : Formula) :
    IffAll (Formula.and B (Formula.ex A)) (Formula.ex (Formula.and (liftFormula 0 B) A)) :=
  iffAll_trans (and_commA B (Formula.ex A))
    (iffAll_trans (fun Δ => and_ex Δ A B)
      (iffAll_ex (and_commA A (liftFormula 0 B))))

theorem or_forall_r (B A : Formula) :
    IffAll (Formula.or B (Formula.forall A)) (Formula.forall (Formula.or (liftFormula 0 B) A)) :=
  iffAll_trans (or_commA B (Formula.forall A))
    (iffAll_trans (fun Δ => or_forall Δ A B)
      (iffAll_forall (or_commA A (liftFormula 0 B))))

theorem or_ex_r (B A : Formula) :
    IffAll (Formula.or B (Formula.ex A)) (Formula.ex (Formula.or (liftFormula 0 B) A)) :=
  iffAll_trans (or_commA B (Formula.ex A))
    (iffAll_trans (fun Δ => or_ex Δ A B)
      (iffAll_ex (or_commA A (liftFormula 0 B))))

-- ── §4 · las FUSIONES son correctas ────────────────────────────────────────
theorem mergeAndR_iff : ∀ (A B : Formula), IffAll (Formula.and A B) (mergeAndR A B)
  | A, .forall B' =>
      iffAll_trans (and_forall_r A B') (iffAll_forall (mergeAndR_iff (liftFormula 0 A) B'))
  | A, .ex B' =>
      iffAll_trans (and_ex_r A B') (iffAll_ex (mergeAndR_iff (liftFormula 0 A) B'))
  | _, .bottom => iffAll_refl _
  | _, .atom _ _ => iffAll_refl _
  | _, .eq _ _ => iffAll_refl _
  | _, .impl _ _ => iffAll_refl _
  | _, .and _ _ => iffAll_refl _
  | _, .or _ _ => iffAll_refl _

theorem mergeAnd_iff : ∀ (A B : Formula), IffAll (Formula.and A B) (mergeAnd A B)
  | .forall A', B =>
      iffAll_trans (fun Δ => and_forall Δ A' B) (iffAll_forall (mergeAnd_iff A' (liftFormula 0 B)))
  | .ex A', B =>
      iffAll_trans (fun Δ => and_ex Δ A' B) (iffAll_ex (mergeAnd_iff A' (liftFormula 0 B)))
  | .bottom, B => mergeAndR_iff _ B
  | .atom _ _, B => mergeAndR_iff _ B
  | .eq _ _, B => mergeAndR_iff _ B
  | .impl _ _, B => mergeAndR_iff _ B
  | .and _ _, B => mergeAndR_iff _ B
  | .or _ _, B => mergeAndR_iff _ B

theorem mergeOrR_iff : ∀ (A B : Formula), IffAll (Formula.or A B) (mergeOrR A B)
  | A, .forall B' =>
      iffAll_trans (or_forall_r A B') (iffAll_forall (mergeOrR_iff (liftFormula 0 A) B'))
  | A, .ex B' =>
      iffAll_trans (or_ex_r A B') (iffAll_ex (mergeOrR_iff (liftFormula 0 A) B'))
  | _, .bottom => iffAll_refl _
  | _, .atom _ _ => iffAll_refl _
  | _, .eq _ _ => iffAll_refl _
  | _, .impl _ _ => iffAll_refl _
  | _, .and _ _ => iffAll_refl _
  | _, .or _ _ => iffAll_refl _

theorem mergeOr_iff : ∀ (A B : Formula), IffAll (Formula.or A B) (mergeOr A B)
  | .forall A', B =>
      iffAll_trans (fun Δ => or_forall Δ A' B) (iffAll_forall (mergeOr_iff A' (liftFormula 0 B)))
  | .ex A', B =>
      iffAll_trans (fun Δ => or_ex Δ A' B) (iffAll_ex (mergeOr_iff A' (liftFormula 0 B)))
  | .bottom, B => mergeOrR_iff _ B
  | .atom _ _, B => mergeOrR_iff _ B
  | .eq _ _, B => mergeOrR_iff _ B
  | .impl _ _, B => mergeOrR_iff _ B
  | .and _ _, B => mergeOrR_iff _ B
  | .or _ _, B => mergeOrR_iff _ B

theorem mergeImplR_iff : ∀ (A B : Formula), IffAll (Formula.impl A B) (mergeImplR A B)
  | A, .forall B' =>
      iffAll_trans (fun Δ => impl_forall_right Δ B' A)
        (iffAll_forall (mergeImplR_iff (liftFormula 0 A) B'))
  | A, .ex B' =>
      iffAll_trans (fun Δ => impl_ex_right Δ B' A)
        (iffAll_ex (mergeImplR_iff (liftFormula 0 A) B'))
  | _, .bottom => iffAll_refl _
  | _, .atom _ _ => iffAll_refl _
  | _, .eq _ _ => iffAll_refl _
  | _, .impl _ _ => iffAll_refl _
  | _, .and _ _ => iffAll_refl _
  | _, .or _ _ => iffAll_refl _

-- ⚠️ A la izquierda de `→` el cuantificador SE DA LA VUELTA.
theorem mergeImpl_iff : ∀ (A B : Formula), IffAll (Formula.impl A B) (mergeImpl A B)
  | .forall A', B =>
      iffAll_trans (fun Δ => impl_forall_left Δ A' B)
        (iffAll_ex (mergeImpl_iff A' (liftFormula 0 B)))
  | .ex A', B =>
      iffAll_trans (fun Δ => impl_ex_left Δ A' B)
        (iffAll_forall (mergeImpl_iff A' (liftFormula 0 B)))
  | .bottom, B => mergeImplR_iff _ B
  | .atom _ _, B => mergeImplR_iff _ B
  | .eq _ _, B => mergeImplR_iff _ B
  | .impl _ _, B => mergeImplR_iff _ B
  | .and _ _, B => mergeImplR_iff _ B
  | .or _ _, B => mergeImplR_iff _ B

-- ── §5 · 🏁 LA CORRECCIÓN DE LA FORMA NORMAL ───────────────────────────────
theorem prenex_iff : ∀ (f : Formula), IffAll f (prenex f)
  | .bottom => iffAll_refl _
  | .atom _ _ => iffAll_refl _
  | .eq _ _ => iffAll_refl _
  | .forall f => iffAll_forall (prenex_iff f)
  | .ex f => iffAll_ex (prenex_iff f)
  | .and a b => iffAll_trans (iffAll_and (prenex_iff a) (prenex_iff b)) (mergeAnd_iff _ _)
  | .or a b => iffAll_trans (iffAll_or (prenex_iff a) (prenex_iff b)) (mergeOr_iff _ _)
  | .impl a b => iffAll_trans (iffAll_impl (prenex_iff a) (prenex_iff b)) (mergeImpl_iff _ _)

/-- 🏁🏁 **La forma normal prenexa es DEMOSTRABLEMENTE equivalente al original.** -/
theorem derives0_prenex_iff (Γ : List Formula) (f : Formula) : Iff (Γ ⊢₀ f) (Γ ⊢₀ prenex f) :=
  ⟨fun h => Derives₀.elim_impl _ _ _ (iffL (prenex_iff f) Γ) h,
   fun h => Derives₀.elim_impl _ _ _ (iffR (prenex_iff f) Γ) h⟩

end FOL.PrenexNF0

#print axioms FOL.PrenexNF0.mergeAnd_iff
#print axioms FOL.PrenexNF0.mergeImpl_iff
#print axioms FOL.PrenexNF0.prenex_iff
#print axioms FOL.PrenexNF0.derives0_prenex_iff
