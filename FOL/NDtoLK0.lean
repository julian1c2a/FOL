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
# `FOL.NDtoLK0` — **`NDtoLK` DEMOSTRADA**: H3 se queda con una sola deuda

Cuarta pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.8).

    ndToLK : Derives₂ Γ f → LKc Γ [f]
    herbrandExtraction_of_cutElim : CutElim → HerbrandExtraction

⇒ **De las dos obligaciones que ADR‑046 dejó, queda UNA**: el Hauptsatz.

## ⭐⭐ Lo que desbloqueó la traducción: una regla, no más esfuerzo

ADR‑046 §4 midió el bloqueo y lo midió bien: con las instancias de igualdad **en el antecedente**,
el caso `intro_forall` **levanta el contexto**, la `E` de la hipótesis de inducción vive arriba, y
una instancia con `Term.var 0` **no es el levantamiento de ninguna**. No hay forma de producirla
desde abajo.

⭐ La salida no fue pelear el bookkeeping sino **añadir la regla que faltaba**: `eqAx`, el corte
contra un axioma de la teoría (ADR‑049). Con ella la traducción es **estructural y sin `E`**: cada
constructor de igualdad de `Derives₂` mete su axioma **localmente**, donde se usa, y el contexto
no tiene que arrastrar nada.

🔑 *Cuando una obligación se bloquea por bookkeeping, a veces lo que falta no es esfuerzo sino una
regla.*

## Cómo se traduce cada grupo

| grupo | herramienta |
|---|---|
| introducciones (`intro_impl`, `intro_and`, `intro_or_*`, `intro_forall`, `intro_ex`) | ⭐ la regla **derecha** correspondiente, **directa** — `intro_forall` es literalmente `allR` |
| eliminaciones (`elim_impl`, `elim_and_*`, `elim_or`, `elim_forall`, `elim_ex`, `bot_elim`) | **corte** sobre la fórmula mayor, y luego la regla **izquierda** |
| clásicas (`dne_rule`, `dne_schema`, `forall_not_ex_not`) | dos lemas: `dneL` y `fnenL` |
| igualdad (`refl`, las tres congruencias) | ⭐ `eqAx` + modus ponens |

⭐ **`intro_forall` y `elim_ex` salen DIRECTOS**, sin corte: `LKc.allR` y `LKc.exL` levantan el
contexto exactamente igual que los constructores de `Derives₂`. *Los dos cálculos tienen la misma
regla de eigenvariable, escrita de dos maneras.*

⚠️ **El caso con más trabajo es `forall_not_ex_not`** (`¬∀A ⟹ ∃¬A`): hay que bajar por `allR`,
subir el `∃` con `exR` usando `Term.var 0` como testigo y cerrar con `substFormula_lift_var` — el
mismo lema del paso de eigenvariable de Henkin (ADR‑036), por tercera vez.

## 📏 Footprint

`[propext, Quot.sound]`. **Ni un `Classical.choice`** — y `mpLK`/`viaEqImpl` **no dependen de
ningún axioma**.
-/

namespace FOL.NDtoLK0

open FOL.Herbrand0
open FOL.Sequent0

-- ── atajos ──────────────────────────────────────────────────────────────────
theorem wkL {Γ Γ' Δ : List Formula} (h : LKc Γ Δ) (hs : ∀ x, x ∈ Γ → x ∈ Γ') : LKc Γ' Δ :=
  LKc.struct _ _ _ _ h hs (fun _ hx => hx)

theorem wkR {Γ Δ Δ' : List Formula} (h : LKc Γ Δ) (hs : ∀ x, x ∈ Δ → x ∈ Δ') : LKc Γ Δ' :=
  LKc.struct _ _ _ _ h (fun _ hx => hx) hs

theorem axH (Γ : List Formula) (A : Formula) (Δ : List Formula) (hΔ : A ∈ Δ) :
    LKc (A :: Γ) Δ := LKc.ax _ _ A (List.Mem.head _) hΔ

/-- `¬¬A ⟹ A`, que es lo que necesitan `dne_rule` y `dne_schema`. -/
theorem dneL (Γ : List Formula) (A : Formula) : LKc (neg (neg A) :: Γ) [A] := by
  refine LKc.implL Γ [A] (neg A) Formula.bottom ?_ (LKc.botL _ _ (List.Mem.head _))
  refine LKc.implR Γ [A] A Formula.bottom ?_
  exact LKc.ax _ _ A (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))

/-- `¬∀A ⟹ ∃¬A`. -/
theorem fnenL (Γ : List Formula) (A : Formula) :
    LKc (neg (Formula.forall A) :: Γ) [Formula.ex (neg A)] := by
  refine LKc.implL Γ [Formula.ex (neg A)] (Formula.forall A) Formula.bottom ?_
    (LKc.botL _ _ (List.Mem.head _))
  -- Γ ⟹ ∀A , ∃¬A
  refine LKc.struct Γ Γ (Formula.forall A :: [Formula.ex (neg A)]) _ ?_ (fun _ hx => hx)
    (fun _ hx => hx)
  refine LKc.allR Γ [Formula.ex (neg A)] A ?_
  -- Γ↑ ⟹ A , (∃¬A)↑
  show LKc (Γ.map (liftFormula 0)) (A :: [Formula.ex (neg (liftFormula 1 A))])
  refine LKc.struct _ _ (Formula.ex (neg (liftFormula 1 A)) :: [A]) _ ?_ (fun _ hx => hx)
    (fun x hx => by
      cases hx with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ h' => cases h' with
                     | head => exact List.Mem.head _
                     | tail _ h'' => exact absurd h'' List.not_mem_nil)
  refine LKc.exR _ [A] (neg (liftFormula 1 A)) (Term.var 0) ?_
  rw [show substFormula 0 (Term.var 0) (neg (liftFormula 1 A)) = neg A from by
        show Formula.impl (substFormula 0 (Term.var 0) (liftFormula 1 A)) Formula.bottom = _
        rw [FOL.Lift0.substFormula_lift_var A 0]; rfl]
  refine LKc.implR _ [A] A Formula.bottom ?_
  exact LKc.ax _ _ A (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))


-- ── modus ponens en LKc, que es tambien el caso `elim_impl` ─────────────────
theorem mpLK {G : List Formula} (X Y : Formula)
    (hXY : LKc G [Formula.impl X Y]) (hX : LKc G [X]) : LKc G [Y] := by
  refine LKc.cut G [Y] (Formula.impl X Y) (wkR hXY (fun x hx => by
    cases hx with
    | head => exact List.Mem.head _
    | tail _ h2 => exact absurd h2 List.not_mem_nil)) ?_
  refine LKc.implL G [Y] X Y (wkR hX (fun x hx => by
    cases hx with
    | head => exact List.Mem.head _
    | tail _ h2 => exact absurd h2 List.not_mem_nil)) ?_
  exact LKc.ax _ _ Y (List.Mem.head _) (List.Mem.head _)

/-- ⭐ El patron de las tres congruencias: meter el axioma con `eqAx` y consumirlo. -/
theorem viaEqImpl {G : List Formula} (X Y : Formula)
    (hg : EqInstance (Formula.impl X Y)) (hX : LKc G [X]) : LKc G [Y] :=
  LKc.eqAx G [Y] (Formula.impl X Y) hg
    (mpLK X Y (LKc.ax _ _ _ (List.Mem.head _) (List.Mem.head _))
      (wkL hX (fun _ hx => List.Mem.tail _ hx)))

-- ── corte contra una premisa ya derivada ───────────────────────────────────
theorem cutOn {G : List Formula} (A : Formula) {D : List Formula}
    (hA : LKc G [A]) (hrest : LKc (A :: G) D) : LKc G D := by
  refine LKc.cut G D A ?_ hrest
  exact wkR hA (fun x hx => by
    cases hx with
    | head => exact List.Mem.head _
    | tail _ h2 => exact absurd h2 List.not_mem_nil)

-- ── ⭐⭐ LA TRADUCCION ───────────────────────────────────────────────────────
theorem ndToLK {G : List Formula} {f : Formula} (h : G ⊢₂ f) : LKc G [f] := by
  induction h with
  | hyp G f hmem => exact LKc.ax G [f] f hmem (List.Mem.head _)
  | intro_impl G A B _ ih => exact LKc.implR G [] A B ih
  | elim_impl G A B _ _ ih1 ih2 => exact mpLK A B ih1 ih2
  | intro_and G A B _ _ ih1 ih2 => exact LKc.andR G [] A B ih1 ih2
  | elim_and_l G A B _ ih =>
      refine cutOn (Formula.and A B) ih ?_
      exact LKc.andL G [A] A B (LKc.ax _ _ A (List.Mem.head _) (List.Mem.head _))
  | elim_and_r G A B _ ih =>
      refine cutOn (Formula.and A B) ih ?_
      exact LKc.andL G [B] A B
        (LKc.ax _ _ B (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _))
  | intro_or_l G A B _ ih =>
      refine LKc.orR G [] A B ?_
      exact wkR ih (fun x hx => by
        cases hx with
        | head => exact List.Mem.head _
        | tail _ h2 => exact absurd h2 List.not_mem_nil)
  | intro_or_r G A B _ ih =>
      refine LKc.orR G [] A B ?_
      exact wkR ih (fun x hx => by
        cases hx with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ h2 => exact absurd h2 List.not_mem_nil)
  | elim_or G A B C _ _ _ ih1 ih2 ih3 =>
      exact cutOn (Formula.or A B) ih1 (LKc.orL G [C] A B ih2 ih3)
  | intro_forall G A _ ih => exact LKc.allR G [] A ih
  | elim_forall G A t _ ih =>
      refine cutOn (Formula.forall A) ih ?_
      exact LKc.allL G [substFormula 0 t A] A t
        (LKc.ax _ _ _ (List.Mem.head _) (List.Mem.head _))
  | intro_ex G A t _ ih => exact LKc.exR G [] A t ih
  | elim_ex G A B _ _ ih1 ih2 =>
      exact cutOn (Formula.ex A) ih1 (LKc.exL G [B] A ih2)
  | bot_elim G A _ ih => exact cutOn Formula.bottom ih (LKc.botL _ _ (List.Mem.head _))
  | weakening G G2 f _ hsub ih => exact wkL ih hsub
  | dne_rule G A _ ih => exact cutOn (neg (neg A)) ih (dneL G A)
  | dne_schema G A => exact LKc.implR G [] (neg (neg A)) A (dneL G A)
  | forall_not_ex_not G A =>
      exact LKc.implR G [] (neg (Formula.forall A)) (Formula.ex (neg A)) (fnenL G A)
  -- ⭐ los cuatro de la IGUALDAD: `eqAx` y a consumir
  | refl G t =>
      exact LKc.eqAx G [Formula.eq t t] (eqReflAx t) (EqInstance.refl t)
        (LKc.ax _ _ _ (List.Mem.head _) (List.Mem.head _))
  | eq_func_congr G p pre post a b _ ih =>
      exact viaEqImpl (Formula.eq a b) _ (EqInstance.func p pre post a b) ih
  | eq_atom_congr G p pre post a b _ _ ih1 ih2 =>
      exact mpLK _ _ (viaEqImpl (Formula.eq a b) _ (EqInstance.atom p pre post a b) ih1) ih2
  | eq_eq_congr G a b c _ _ ih1 ih2 =>
      have hba : LKc G [Formula.eq b a] :=
        viaEqImpl (Formula.eq a b) (Formula.eq b a) (EqInstance.symm a b) ih1
      exact mpLK _ _ (viaEqImpl (Formula.eq b a) _ (EqInstance.trans b a c) hba) ih2


/-- ⭐⭐⭐ `NDtoLK`, la obligación de ADR‑046, **demostrada**. -/
theorem ndToLK_prop : NDtoLK := fun _ _ h => ndToLK h

/-- ⭐⭐⭐⭐ **Y con ella, H3 se queda con UNA sola deuda: el Hauptsatz.** -/
theorem herbrandExtraction_of_cutElim (hcut : CutElim) : HerbrandExtraction :=
  herbrandExtraction_of hcut ndToLK_prop

end FOL.NDtoLK0

#print axioms FOL.NDtoLK0.mpLK
#print axioms FOL.NDtoLK0.viaEqImpl
#print axioms FOL.NDtoLK0.ndToLK
#print axioms FOL.NDtoLK0.herbrandExtraction_of_cutElim
