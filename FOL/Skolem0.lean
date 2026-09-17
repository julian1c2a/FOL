/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Canonical0
-- @axiom_system: classical
-- @importance: high

import FOL.Canonical0

/-!
# `FOL.Skolem0` — 🏁 el axioma de SKOLEM/HENKIN es **CONSERVATIVO**

    henkin_conservative : c fresco para Γ, A y φ →
                          (henkinAx c A :: Γ) ⊢₀ φ  →  Γ ⊢₀ φ

## ⭐⭐ El puente que NO existía, y era el bloqueo medido

Una medición externa señaló el bloqueo de Skolem, y acertó: **no había ningún lema que conectara
`occursFormula` (sintáctico, `FOL/Eigenvariable.lean:366`) con `evalFormula` (semántico,
`FOL/Semantics.lean:54`)**. Sin él, la frescura de un símbolo no dice **nada** semánticamente: se
puede decir «`c` no aparece en `f`» y no poder concluir que reinterpretar `c` no cambia el valor
de `f`. Ésa es la pieza:

    evalFormula_updateFunc : ¬ occursFormula c f →
      (evalFormula (updateFunc M c F) v f ↔ evalFormula M v f)

📏 **No depende de ningún axioma.** Setenta líneas, net‑0, y es reutilizable por cualquier
argumento de frescura que quiera decir algo semántico — no sólo por Skolem.

## ⭐ Y el axioma de Skolem YA ESTABA ESCRITO: es `henkinAx`

    henkinAx c A = (∃A) ⇒ A[c]            -- FOL/Henkin0.lean:90

Es literalmente el axioma de Skolem para un existencial cuyo cuerpo no tiene más variables libres.
⇒ no hay que definir nada nuevo: *antes de construir, buscar*.
⚠️ Lo que el proyecto tenía sobre él era `henkin_step_consistent` (ADR‑037): que el paso **preserva
la CONSISTENCIA**. La conservatividad es **estrictamente más fuerte** y es lo que hace falta para
decir que skolemizar no inventa teoremas.

## ⭐ La ruta, y dónde paga cada pieza

    (henkinAx c A :: Γ) ⊢₀ φ
      --[ derives0_soundness ]-->  vale en TODO modelo del contexto ampliado
      --[ se EXPANDE M en `c` con un testigo ]-->  ese modelo existe
      --[ evalFormula_updateFunc, dos veces ]-->  Γ ⊨ φ         (c fresco para Γ y para φ)
      --[ completeness₀ ]-->  Γ ⊢₀ φ

⚠️ El testigo se elige con `by_cases` sobre si `∃A` vale en `M`, y en la rama negativa el axioma se
cumple **vacuamente** — por el propio lema de coincidencia. *La frescura se usa tres veces y cada
una hace un trabajo distinto: en Γ para transportar el contexto, en A para elegir el testigo, y en
φ para traer la conclusión de vuelta.*

## 📏 Footprint

`updateFunc`, `evalTerm_updateFunc` y `evalFormula_updateFunc` **sin ningún axioma**.
`henkin_conservative`, `[propext, Classical.choice, Quot.sound]` — el `Classical.choice` es el de
`completeness₀`, el **WKL** de siempre (plan §6.3), más la elección del testigo. ⛔ Vía W, no vía H.
-/

namespace FOL.Skolem0

open FOL.Metamath.Semantics
open FOL.Eigenvariable
open FOL.Henkin0

/-- Reinterpretar UN símbolo de función, dejando todo lo demás igual.
⚠️ El `if f = c` usa `String.decEq`, que **no** trae `Classical.choice`: lo que lo trae es
DESCOMPONER un `String`, no compararlo (plan §7). -/
def updateFunc {D : Type} (M : Model D) (c : String) (F : List D → D) : Model D where
  func := fun f ds => if f = c then F ds else M.func f ds
  rel := M.rel

-- ── ⭐⭐ EL LEMA DE COINCIDENCIA ─────────────────────────────────────────────
mutual
theorem evalTerm_updateFunc {D : Type} (M : Model D) (c : String) (F : List D → D) :
    ∀ (t : Term) (v : Nat → D), Not (occursTerm c t) →
      evalTerm (updateFunc M c F) v t = evalTerm M v t
  | .var _, _, _ => rfl
  | .func s ts, v, h => by
      have hs : Not (s = c) := fun he => h (Or.inl he)
      show (if s = c then F (evalTerms (updateFunc M c F) v ts)
            else M.func s (evalTerms (updateFunc M c F) v ts)) = M.func s (evalTerms M v ts)
      rw [if_neg hs, evalTerms_updateFunc M c F ts v (fun ht => h (Or.inr ht))]

theorem evalTerms_updateFunc {D : Type} (M : Model D) (c : String) (F : List D → D) :
    ∀ (ts : List Term) (v : Nat → D), Not (occursTerms c ts) →
      evalTerms (updateFunc M c F) v ts = evalTerms M v ts
  | [], _, _ => rfl
  | t :: ts, v, h => by
      show evalTerm (updateFunc M c F) v t :: evalTerms (updateFunc M c F) v ts
           = evalTerm M v t :: evalTerms M v ts
      rw [evalTerm_updateFunc M c F t v (fun ht => h (Or.inl ht)),
          evalTerms_updateFunc M c F ts v (fun ht => h (Or.inr ht))]
end

theorem evalFormula_updateFunc {D : Type} (M : Model D) (c : String) (F : List D → D) :
    ∀ (f : Formula) (v : Nat → D), Not (occursFormula c f) →
      Iff (evalFormula (updateFunc M c F) v f) (evalFormula M v f) := by
  intro f
  induction f with
  | bottom => intro _ _; exact Iff.rfl
  | atom p ts =>
      intro v h
      show Iff (M.rel p (evalTerms (updateFunc M c F) v ts)) (M.rel p (evalTerms M v ts))
      rw [evalTerms_updateFunc M c F ts v h]
  | eq t u =>
      intro v h
      show Iff (evalTerm (updateFunc M c F) v t = evalTerm (updateFunc M c F) v u)
               (evalTerm M v t = evalTerm M v u)
      rw [evalTerm_updateFunc M c F t v (fun ht => h (Or.inl ht)),
          evalTerm_updateFunc M c F u v (fun ht => h (Or.inr ht))]
  | impl a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx hy => (ihb v (fun ht => h (Or.inr ht))).mp
          (hx ((iha v (fun ht => h (Or.inl ht))).mpr hy)))
        (fun hx hy => (ihb v (fun ht => h (Or.inr ht))).mpr
          (hx ((iha v (fun ht => h (Or.inl ht))).mp hy)))
  | and a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx => ⟨(iha v (fun ht => h (Or.inl ht))).mp hx.1,
                    (ihb v (fun ht => h (Or.inr ht))).mp hx.2⟩)
        (fun hx => ⟨(iha v (fun ht => h (Or.inl ht))).mpr hx.1,
                    (ihb v (fun ht => h (Or.inr ht))).mpr hx.2⟩)
  | or a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx => hx.imp (iha v (fun ht => h (Or.inl ht))).mp
                          (ihb v (fun ht => h (Or.inr ht))).mp)
        (fun hx => hx.imp (iha v (fun ht => h (Or.inl ht))).mpr
                          (ihb v (fun ht => h (Or.inr ht))).mpr)
  | «forall» a ih =>
      intro v h
      exact Iff.intro
        (fun hx d => (ih (shiftEnv v d) h).mp (hx d))
        (fun hx d => (ih (shiftEnv v d) h).mpr (hx d))
  | ex a ih =>
      intro v h
      exact Iff.intro
        (fun hx => hx.elim (fun d hd => ⟨d, (ih (shiftEnv v d) h).mp hd⟩))
        (fun hx => hx.elim (fun d hd => ⟨d, (ih (shiftEnv v d) h).mpr hd⟩))

/-- El símbolo nuevo se interpreta como el testigo elegido. -/
theorem evalTerm_new {D : Type} (M : Model D) (c : String) (w : D) (v : Nat → D) :
    evalTerm (updateFunc M c (fun _ => w)) v (Term.func c []) = w := by
  show (if c = c then w else M.func c (evalTerms (updateFunc M c (fun _ => w)) v [])) = w
  rw [if_pos rfl]

-- ── 🏁 LA CONSERVATIVIDAD ───────────────────────────────────────────────────

/-- 🏁🏁 **El axioma de Skolem/Henkin no inventa teoremas.** Si `c` es fresco para el contexto,
para el cuerpo y para la conclusión, todo lo que se demuestra con él se demuestra sin él. -/
theorem henkin_conservative {c : String} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (henkinAx c A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ := by
  refine FOL.Canonical0.completeness₀ ?_
  intro D M v hctx
  -- ⭐ el núcleo: con CUALQUIER testigo que haga válido el axioma, la conclusión vuelve
  have step : ∀ (w : D), evalFormula (updateFunc M c (fun _ => w)) v (henkinAx c A) →
      evalFormula M v φ := by
    intro w hax
    have hM' : ∀ g, g ∈ (henkinAx c A :: Γ) →
        evalFormula (updateFunc M c (fun _ => w)) v g := by
      intro g hg
      cases hg with
      | head => exact hax
      | tail _ hm => exact (evalFormula_updateFunc M c _ g v (hΓ g hm)).mpr (hctx g hm)
    exact (evalFormula_updateFunc M c _ φ v hφ).mp
      (FOL.Metamath.Soundness0.derives0_soundness h D (updateFunc M c (fun _ => w)) v hM')
  by_cases hEx : ∃ d, evalFormula M (shiftEnv v d) A
  · -- hay testigo en `M`: se elige, y el axioma vale
    refine step hEx.choose ?_
    intro _
    refine (eval_substFormula_zero _ v (Term.func c []) A).mpr ?_
    rw [evalTerm_new M c hEx.choose v]
    exact (evalFormula_updateFunc M c _ A (shiftEnv v hEx.choose) hA).mpr hEx.choose_spec
  · -- no hay testigo: el axioma vale VACUAMENTE, y eso también lo da la coincidencia
    refine step (v 0) ?_
    intro hex
    exact absurd
      (hex.elim (fun d hd => ⟨d, (evalFormula_updateFunc M c _ A (shiftEnv v d) hA).mp hd⟩)) hEx

end FOL.Skolem0

#print axioms FOL.Skolem0.evalTerm_updateFunc
#print axioms FOL.Skolem0.evalFormula_updateFunc
#print axioms FOL.Skolem0.evalTerm_new
#print axioms FOL.Skolem0.henkin_conservative
