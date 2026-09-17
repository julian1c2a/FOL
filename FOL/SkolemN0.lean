/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Skolem0
-- @axiom_system: classical
-- @importance: high

import FOL.Skolem0

/-!
# `FOL.SkolemN0` — 🏁 el axioma de SKOLEM bajo un PREFIJO `∀ⁿ`, y sigue siendo conservativo

    skolemAxN c n A := ∀x₀ … ∀x_{n-1}. (∃y. A  →  A[y := c(x₀,…,x_{n-1})])

    skolem_conservative_n : c fresco para Γ, A y φ →
                            (skolemAxN c n A :: Γ) ⊢₀ φ  →  Γ ⊢₀ φ

## ⭐ Por qué éste es el caso que faltaba, y no una variante más

`FOL.Skolem0.skolem_conservative` cubre `c(t̄)` con `t̄` **fijo**, y es barato precisamente por eso:
la interpretación del símbolo nuevo puede ser **constante** (`fun _ => w`) y entonces los argumentos
dejan de importar. Aquí, bajo el prefijo, el testigo **depende de las variables ligadas**: la
interpretación tiene que ser una **función de verdad**, `List D → D`, y hay que hacer coincidir la
**lista de argumentos sintáctica** (`vars n`) con la **lista de valores semántica** (el `ds` que el
prefijo ha ido acumulando). Ésa es la única pieza que la versión de argumentos fijos no tenía.

## ⭐⭐ La decisión de diseño: el entorno no se RECONSTRUYE, se CONSTRUYE

`envPush v ds` está definido **por `shiftEnv`** y recurriendo **sólo sobre la lista**. Con eso, las
dos ecuaciones que el paso inductivo necesita son `rfl`:

    envPush v []              = v
    shiftEnv (envPush v ds) d = envPush v (d :: ds)

⇒ `eval_allBlock_envPush` no lleva ni un `rw` en el paso bajo el binder. 🔑 *Cuando una inducción
tiene que atravesar un binder, lo que la abarata es definir el dato acumulado CON el constructor que
el binder va a producir.*

Y por eso `vars` se escribe con `liftTerms 0` (y no con `List.map (liftTerm 0)`): así la conmutación
semántica que hace falta **ya existe** (`eval_liftTerms_ext`), y `evalTerms_vars` va de **lista a
lista**, sin un solo `funext`.

## ⚠️ Tres detalles que NO son cosméticos

* El contador se escribe **`n + ds.length`**, no `ds.length + n`: `Nat.add` recurre sobre el segundo
  argumento, así que con `ds = []` la primera forma reduce sola y la segunda no.
* La guarda `ds.length = n` del lema del bloque es **necesaria**, no decorativa: sin ella el
  enunciado es falso ya para `n = 1` (el término `c(x₀,…,x_{n-1})` tiene `n` argumentos, y el
  entorno acumulado tendría otra longitud).
* `skF` usa `@dite` con `Classical.propDecidable` **explícito**: este fichero no abre `Classical`, y
  con la instancia implícita el binder de `dite` no llega a tipar.
-/

namespace FOL.SkolemN0

open FOL.Metamath.Semantics
open FOL.Eigenvariable
open FOL.Skolem0

-- ═══════════════════════════════════════════════════════════════════════════
-- §1 · el entorno acumulado, el prefijo y la lista de variables
-- ═══════════════════════════════════════════════════════════════════════════

/-- `envPush v [d₀, …, d_{k-1}]` empuja los `dᵢ` sobre `v`, el último por fuera.
⭐ Definido **por `shiftEnv`**: las dos ecuaciones que hacen falta son `rfl`. -/
def envPush {D : Type} (v : Nat → D) : List D → Nat → D
  | [] => v
  | d :: ds => shiftEnv (envPush v ds) d

example {D : Type} (v : Nat → D) : envPush v [] = v := rfl
example {D : Type} (v : Nat → D) (d : D) (ds : List D) :
    shiftEnv (envPush v ds) d = envPush v (d :: ds) := rfl

/-- `allBlock n ψ = ∀ⁿ ψ`. -/
def allBlock : Nat → Formula → Formula
  | 0, ψ => ψ
  | n + 1, ψ => Formula.forall (allBlock n ψ)

/-- `vars n = [x₀, x₁, …, x_{n-1}]`, y la **cabeza es la más interna**.
⚠️ Con `liftTerms 0` a propósito: así `eval_liftTerms_ext` aplica directamente. -/
def vars : Nat → List Term
  | 0 => []
  | n + 1 => Term.var 0 :: liftTerms 0 (vars n)

example : vars 3 = [Term.var 0, Term.var 1, Term.var 2] := rfl

/-- Las variables no mencionan ningún símbolo de función. -/
theorem not_occurs_vars (c : String) : ∀ n : Nat, Not (occursTerms c (vars n))
  | 0 => fun h => h
  | n + 1 => by
      intro h
      cases h with
      | inl hv => exact hv
      | inr ht =>
          exact absurd (FOL.HenkinLimit0.occursTerms_lift c 0 (vars n) ht) (not_occurs_vars c n)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2 · el bloque de universales se evalúa EMPUJANDO el entorno
-- ═══════════════════════════════════════════════════════════════════════════

/-- ⭐ Para probar `∀ⁿ ψ` en el entorno `envPush v ds` basta probar `ψ` en **todo** entorno
acumulado de longitud `k`. ⚠️ La guarda `n + ds.length = k` es lo que engancha el prefijo que queda
con la lista que ya se ha acumulado, y se escribe `n + ds.length` para que `ds = []` reduzca. -/
theorem eval_allBlock_envPush {D : Type} (M : Model D) (ψ : Formula) (v : Nat → D) (k : Nat)
    (h : ∀ ds : List D, ds.length = k → evalFormula M (envPush v ds) ψ) :
    ∀ (n : Nat) (ds : List D), n + ds.length = k →
      evalFormula M (envPush v ds) (allBlock n ψ)
  | 0, ds, hlen => h ds (by omega)
  | n + 1, ds, hlen => by
      show ∀ d : D, evalFormula M (shiftEnv (envPush v ds) d) (allBlock n ψ)
      intro d
      refine eval_allBlock_envPush M ψ v k h n (d :: ds) ?_
      show n + (ds.length + 1) = k
      omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3 · ⭐ la coincidencia n‑aria: la lista SINTÁCTICA vale la lista SEMÁNTICA
-- ═══════════════════════════════════════════════════════════════════════════

/-- `eval_liftTerms_ext` está enunciado con `updateEnv 0`; el puente a `shiftEnv` es un `funext`
sobre `updateEnv_zero`, y se paga **una sola vez**, aquí. -/
theorem evalTerms_lift_shift {D : Type} (M : Model D) (v : Nat → D) (d : D) (ts : List Term) :
    evalTerms M (shiftEnv v d) (liftTerms 0 ts) = evalTerms M v ts := by
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [← heq]
  exact eval_liftTerms_ext M v d 0 ts

/-- 🏁 **La pieza central**, y va de **lista a lista**: en el entorno que el prefijo ha acumulado,
las variables `x₀,…,x_{k-1}` valen exactamente los valores acumulados. -/
theorem evalTerms_vars {D : Type} (M : Model D) (v : Nat → D) :
    ∀ ds : List D, evalTerms M (envPush v ds) (vars ds.length) = ds
  | [] => rfl
  | d :: ds => by
      show evalTerm M (shiftEnv (envPush v ds) d) (Term.var 0)
             :: evalTerms M (shiftEnv (envPush v ds) d) (liftTerms 0 (vars ds.length)) = d :: ds
      rw [evalTerms_lift_shift M (envPush v ds) d (vars ds.length), evalTerms_vars M v ds]
      rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §4 · la función de Skolem
-- ═══════════════════════════════════════════════════════════════════════════

/-- La interpretación del símbolo nuevo: un testigo cuando lo hay, y `d0` cuando no.
⚠️ `Classical.propDecidable` va **explícito** — este fichero no abre `Classical`. -/
noncomputable def skF {D : Type} (M : Model D) (A : Formula) (v : Nat → D) (d0 : D) :
    List D → D := fun ds =>
  @dite D (∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A)
    (Classical.propDecidable (∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A))
    (fun h => Exists.choose h) (fun _ => d0)

theorem skF_spec {D : Type} (M : Model D) (A : Formula) (v : Nat → D) (d0 : D) (ds : List D)
    (h : ∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A) :
    evalFormula M (shiftEnv (envPush v ds) (skF M A v d0 ds)) A := by
  show evalFormula M (shiftEnv (envPush v ds)
    (@dite D (∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A)
      (Classical.propDecidable (∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A))
      (fun h => Exists.choose h) (fun _ => d0))) A
  rw [dif_pos h]
  exact h.choose_spec

-- ═══════════════════════════════════════════════════════════════════════════
-- §5 · 🏁 el axioma de Skolem con prefijo, y su conservatividad
-- ═══════════════════════════════════════════════════════════════════════════

/-- `∀x₀ … ∀x_{n-1}. (∃y. A → A[y := c(x₀,…,x_{n-1})])`. -/
def skolemAxN (c : String) (n : Nat) (A : Formula) : Formula :=
  allBlock n (Formula.impl (Formula.ex A) (substFormula 0 (Term.func c (vars n)) A))

/-- El caso `n = 0` es, **por `rfl`**, el axioma de argumentos fijos con lista vacía. -/
example (c : String) (A : Formula) : skolemAxN c 0 A = skolemAxT c [] A := rfl

/-- ⭐ El axioma con prefijo **es válido** en el modelo expandido con `skF`. -/
theorem eval_skolemAxN {D : Type} (M : Model D) (c : String) (n : Nat) (A : Formula)
    (v : Nat → D) (d0 : D) (hA : Not (occursFormula c A)) :
    evalFormula (updateFunc M c (skF M A v d0)) v (skolemAxN c n A) := by
  show evalFormula (updateFunc M c (skF M A v d0)) (envPush v [])
    (allBlock n (Formula.impl (Formula.ex A) (substFormula 0 (Term.func c (vars n)) A)))
  refine eval_allBlock_envPush _ _ v n ?_ n [] rfl
  intro ds hlen hex
  have hexM : ∃ d : D, evalFormula M (shiftEnv (envPush v ds) d) A :=
    hex.elim (fun d hd =>
      ⟨d, (evalFormula_updateFunc M c _ A (shiftEnv (envPush v ds) d) hA).mp hd⟩)
  refine (eval_substFormula_zero _ (envPush v ds) (Term.func c (vars n)) A).mpr ?_
  have hval : evalTerm (updateFunc M c (skF M A v d0)) (envPush v ds)
      (Term.func c (vars n)) = skF M A v d0 ds := by
    show (if c = c then skF M A v d0
            (evalTerms (updateFunc M c (skF M A v d0)) (envPush v ds) (vars n))
          else M.func c (evalTerms (updateFunc M c (skF M A v d0)) (envPush v ds) (vars n)))
         = skF M A v d0 ds
    rw [if_pos rfl,
        evalTerms_updateFunc M c _ (vars n) (envPush v ds) (not_occurs_vars c n),
        show n = ds.length from hlen.symm, evalTerms_vars M v ds]
  rw [hval]
  exact (evalFormula_updateFunc M c _ A (shiftEnv (envPush v ds) _) hA).mpr
    (skF_spec M A v d0 ds hexM)

/-- 🏁🏁 **El axioma de Skolem bajo un prefijo `∀ⁿ` no inventa teoremas.** Si `c` es fresco para el
contexto, el cuerpo y la conclusión, todo lo que se demuestra con él se demuestra sin él.

⚠️ El `Classical.choice` del footprint **no es nuevo**: `completeness₀` ya lo trae (es el WKL). Lo
que `skF` añade es el `Exists.choose` de la elección del testigo, que vive en la misma columna. -/
theorem skolem_conservative_n {c : String} {n : Nat} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (skolemAxN c n A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ := by
  refine FOL.Canonical0.completeness₀ ?_
  intro D M v hctx
  have hM' : ∀ g, g ∈ (skolemAxN c n A :: Γ) →
      evalFormula (updateFunc M c (skF M A v (v 0))) v g := by
    intro g hg
    cases hg with
    | head => exact eval_skolemAxN M c n A v (v 0) hA
    | tail _ hm => exact (evalFormula_updateFunc M c _ g v (hΓ g hm)).mpr (hctx g hm)
  exact (evalFormula_updateFunc M c _ φ v hφ).mp
    (FOL.Metamath.Soundness0.derives0_soundness h D (updateFunc M c (skF M A v (v 0))) v hM')

/-- 🏁 El caso `n = 0` recupera la conservatividad del axioma de argumentos fijos con lista vacía —
y por tanto la de Henkin. -/
theorem skolem_conservative_n_zero {c : String} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (skolemAxT c [] A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ :=
  skolem_conservative_n (n := 0) hΓ hA hφ h

end FOL.SkolemN0

#print axioms FOL.SkolemN0.not_occurs_vars
#print axioms FOL.SkolemN0.eval_allBlock_envPush
#print axioms FOL.SkolemN0.evalTerms_vars
#print axioms FOL.SkolemN0.eval_skolemAxN
#print axioms FOL.SkolemN0.skolem_conservative_n
