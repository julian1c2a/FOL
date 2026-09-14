/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Eigenvariable
-- @axiom_system: none
-- @importance: high

import FOL.Eigenvariable

/-!
# `FOL.Lift0` — `Derives₀` respeta el LEVANTAMIENTO de índices

    derives0_lift : Γ ⊢₀ φ  →  ∀ k, Γ.map (liftFormula k) ⊢₀ liftFormula k φ

## Por qué hace falta, y por qué aparece justo ahora

Es la pieza **estructural** que el ensamblaje de Henkin descubre. El argumento clásico llega a

    Γ' ⊢₀ ∃A      y      Γ' ⊢₀ ∀(¬A)

y quiere `⊥`. En un cálculo **finitario** eso pasa obligatoriamente por `elim_ex`, cuya premisa
lateral vive en el contexto **levantado** `A :: Γ'.map (liftFormula 0)`. Hay que llevar allí el
`∀(¬A)`, y para eso hace falta exactamente este lema.

⭐ Una vez dentro, `elim_forall` en `Term.var 0` lo cierra, porque
`substFormula 0 (var 0) (liftFormula 1 (¬A)) = ¬A` — que es `subst_lift_var`, abajo.

## ⚠️ Nota de ingeniería, escrita a propósito

Este módulo es **casi una copia** de `FOL.Eigenvariable`: `absTerm c k` coincide con `liftTerm k`
en todo salvo en la constante `c`. Un `absTerm'` parametrizado por un **predicado** de símbolos
daría los dos con una sola inducción, y `liftTerm` sería el caso del predicado vacío.

⬜ **No se ha hecho, y la razón es de riesgo, no de gusto**: `FOL.Eigenvariable` ya está compilado
y vigilado por `check-footprints.bash`; refactorizarlo para ahorrar ~150 líneas de enunciados
—no de ideas— se haría **después** de cerrar el ensamblaje, no en medio. Queda anotado para no
perderlo.
-/

namespace FOL.Lift0

open FOL.Eigenvariable (posDepth)

-- ============================================================
-- §1 · Lift contra lift, con `j ≤ k`
-- ============================================================

mutual
theorem liftTerm_lift : ∀ (j k : Nat) (_ : j ≤ k) (t : Term),
    liftTerm j (liftTerm k t) = liftTerm (k + 1) (liftTerm j t) := by
  intro j k hjk t
  cases t with
  | var n =>
      by_cases h1 : n < k
      · by_cases h2 : n < j
        · simp [liftTerm, h1, h2, show n < k + 1 by omega]
        · simp [liftTerm, h1, h2, show n + 1 < k + 1 by omega]
      · have h2 : ¬ n < j := by omega
        simp [liftTerm, h1, h2, show ¬ n + 1 < j by omega, show ¬ n + 1 < k + 1 by omega]
  | func s ts =>
      simp only [liftTerm]
      congr 1
      exact liftTerms_lift j k hjk ts

theorem liftTerms_lift : ∀ (j k : Nat) (_ : j ≤ k) (ts : List Term),
    liftTerms j (liftTerms k ts) = liftTerms (k + 1) (liftTerms j ts) := by
  intro j k hjk ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, List.cons.injEq]
      exact ⟨liftTerm_lift j k hjk t, liftTerms_lift j k hjk ts'⟩
end

theorem liftFormula_lift : ∀ (f : Formula) (j k : Nat), j ≤ k →
    liftFormula j (liftFormula k f) = liftFormula (k + 1) (liftFormula j f) := by
  intro f
  induction f with
  | bottom => intro j k _; rfl
  | atom p ts => intro j k h; simp only [liftFormula, liftTerms_lift j k h]
  | eq t u => intro j k h; simp only [liftFormula, liftTerm_lift j k h]
  | impl a b iha ihb => intro j k h; simp only [liftFormula, iha j k h, ihb j k h]
  | «forall» a ih => intro j k h; simp only [liftFormula, ih (j + 1) (k + 1) (by omega)]
  | and a b iha ihb => intro j k h; simp only [liftFormula, iha j k h, ihb j k h]
  | or a b iha ihb => intro j k h; simp only [liftFormula, iha j k h, ihb j k h]
  | ex a ih => intro j k h; simp only [liftFormula, ih (j + 1) (k + 1) (by omega)]

-- ============================================================
-- §2 · Lift contra sustitución, con `v ≤ k`
-- ============================================================

mutual
theorem liftTerm_subst : ∀ (v k : Nat) (_ : v ≤ k) (s t : Term),
    liftTerm k (substTerm v s t) = substTerm v (liftTerm k s) (liftTerm (k + 1) t) := by
  intro v k hvk s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · subst h1
        simp [liftTerm, substTerm, show n < k + 1 by omega]
      · by_cases h2 : n > v
        · by_cases h3 : n < k + 1
          · have e1 : n - 1 < k := by omega
            simp [liftTerm, substTerm, h1, h2, h3, e1]
          · have e1 : ¬ n - 1 < k := by omega
            have e2 : n + 1 ≠ v := by omega
            have e3 : n + 1 > v := by omega
            simp [liftTerm, substTerm, h1, h2, h3, e1, e2, e3]
            omega
        · have e0 : n < k + 1 := by omega
          have e1 : n < k := by omega
          simp [liftTerm, substTerm, h1, h2, e0, e1]
  | func g ts =>
      simp only [liftTerm, substTerm]
      congr 1
      exact liftTerms_subst v k hvk s ts

theorem liftTerms_subst : ∀ (v k : Nat) (_ : v ≤ k) (s : Term) (ts : List Term),
    liftTerms k (substTerms v s ts) = substTerms v (liftTerm k s) (liftTerms (k + 1) ts) := by
  intro v k hvk s ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨liftTerm_subst v k hvk s t, liftTerms_subst v k hvk s ts'⟩
end

theorem liftFormula_subst : ∀ (f : Formula) (v k : Nat), v ≤ k → ∀ (s : Term),
    liftFormula k (substFormula v s f) = substFormula v (liftTerm k s) (liftFormula (k + 1) f) := by
  intro f
  induction f with
  | bottom => intro v k _ s; rfl
  | atom p ts => intro v k h s; simp only [liftFormula, substFormula, liftTerms_subst v k h s]
  | eq t u => intro v k h s; simp only [liftFormula, substFormula, liftTerm_subst v k h s]
  | impl a b iha ihb => intro v k h s; simp only [liftFormula, substFormula, iha v k h s, ihb v k h s]
  | «forall» a ih =>
      intro v k h s
      simp only [liftFormula, substFormula, ih (v + 1) (k + 1) (by omega) (liftTerm 0 s),
        liftTerm_lift 0 k (by omega)]
  | and a b iha ihb => intro v k h s; simp only [liftFormula, substFormula, iha v k h s, ihb v k h s]
  | or a b iha ihb => intro v k h s; simp only [liftFormula, substFormula, iha v k h s, ihb v k h s]
  | ex a ih =>
      intro v k h s
      simp only [liftFormula, substFormula, ih (v + 1) (k + 1) (by omega) (liftTerm 0 s),
        liftTerm_lift 0 k (by omega)]

-- ============================================================
-- §3 · Navegación
-- ============================================================

theorem lift_getAt? : ∀ (p : Pos) (k : Nat) (f : Formula),
    getAt? (liftFormula k f) p = (getAt? f p).map (liftFormula (k + posDepth p)) := by
  intro p
  induction p with
  | root => intro k f; simp [getAt?, posDepth]
  | left p' ih => intro k f; cases f <;> simp only [getAt?, liftFormula, ih, posDepth] <;> rfl
  | right p' ih => intro k f; cases f <;> simp only [getAt?, liftFormula, ih, posDepth] <;> rfl
  | body p' ih =>
      intro k f
      cases f <;>
        simp only [getAt?, liftFormula, ih, posDepth, Nat.add_assoc, Nat.add_comm 1] <;> rfl

theorem lift_replaceAt : ∀ (p : Pos) (k : Nat) (f newSub : Formula),
    replaceAt (liftFormula k f) p (liftFormula (k + posDepth p) newSub)
      = liftFormula k (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro k f n; simp [replaceAt, posDepth]
  | left p' ih => intro k f n; cases f <;> simp only [replaceAt, liftFormula, ih, posDepth]
  | right p' ih => intro k f n; cases f <;> simp only [replaceAt, liftFormula, ih, posDepth]
  | body p' ih =>
      intro k f n
      have e : k + (posDepth p' + 1) = (k + 1) + posDepth p' := by omega
      cases f <;> simp only [replaceAt, liftFormula, posDepth, e, ih]

theorem lift_localRule (k : Nat) {A B : Formula} (h : LocalRule A B) :
    LocalRule (liftFormula k A) (liftFormula k B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (liftFormula k A) (liftFormula k B) (liftFormula k C)

theorem map_lift_lift (k : Nat) (Γ : List Formula) :
    (Γ.map (liftFormula k)).map (liftFormula 0)
      = (Γ.map (liftFormula 0)).map (liftFormula (k + 1)) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, liftFormula_lift g 0 k (Nat.zero_le _), ih]

-- ============================================================
-- §4 · ⭐ EL LEMA
-- ============================================================

/-- **Debilitamiento bajo levantamiento.** ⚠️ El `∀ k` va **dentro**, como en `absDerives`: en
`intro_forall` y `elim_ex` la hipótesis inductiva se usa a nivel `k + 1`. -/
theorem derives0_lift {Γ : List Formula} {φ : Formula} (h : Γ ⊢₀ φ) :
    ∀ k : Nat, (Γ.map (liftFormula k)) ⊢₀ liftFormula k φ := by
  induction h with
  | hyp Γ' f' hIn => intro k; exact Derives₀.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih => intro k; exact Derives₀.intro_impl _ _ _ (ih k)
  | elim_impl Γ' A B _ _ ih1 ih2 => intro k; exact Derives₀.elim_impl _ _ _ (ih1 k) (ih2 k)
  | intro_and Γ' A B _ _ ih1 ih2 => intro k; exact Derives₀.intro_and _ _ _ (ih1 k) (ih2 k)
  | elim_and_l Γ' A B _ ih => intro k; exact Derives₀.elim_and_l _ _ _ (ih k)
  | elim_and_r Γ' A B _ ih => intro k; exact Derives₀.elim_and_r _ _ _ (ih k)
  | intro_or_l Γ' A B _ ih => intro k; exact Derives₀.intro_or_l _ _ _ (ih k)
  | intro_or_r Γ' A B _ ih => intro k; exact Derives₀.intro_or_r _ _ _ (ih k)
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 =>
      intro k; exact Derives₀.elim_or _ _ _ _ (ih1 k) (ih2 k) (ih3 k)
  | intro_forall Γ' A _ ih =>
      intro k
      refine Derives₀.intro_forall _ _ ?_
      rw [map_lift_lift]
      exact ih (k + 1)
  | elim_forall Γ' A t _ ih =>
      intro k
      have := Derives₀.elim_forall (Γ'.map (liftFormula k)) (liftFormula (k + 1) A)
                (liftTerm k t) (ih k)
      rw [liftFormula_subst A 0 k (Nat.zero_le _)]
      exact this
  | intro_ex Γ' A t _ ih =>
      intro k
      refine Derives₀.intro_ex _ _ (liftTerm k t) ?_
      rw [← liftFormula_subst A 0 k (Nat.zero_le _)]
      exact ih k
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      intro k
      refine Derives₀.elim_ex _ (liftFormula (k + 1) A) _ (ih1 k) ?_
      rw [liftFormula_lift B 0 k (Nat.zero_le _), map_lift_lift]
      exact ih2 (k + 1)
  | bot_elim Γ' A _ ih => intro k; exact Derives₀.bot_elim _ _ (ih k)
  | weakening Γ' Γ'' f' _ hSub ih =>
      intro k
      refine Derives₀.weakening _ _ _ (ih k) ?_
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hSub y hy)
  | rewrite_at Γ' f' f'' p sub sub' _ hget hrule heq ih =>
      intro k
      refine Derives₀.rewrite_at _ _ _ p (liftFormula (k + posDepth p) sub)
        (liftFormula (k + posDepth p) sub') (ih k) ?_ ?_ ?_
      · rw [lift_getAt?, hget]; rfl
      · exact lift_localRule _ hrule
      · rw [heq, ← lift_replaceAt]
  | dne_rule Γ' A _ ih => intro k; exact Derives₀.dne_rule _ _ (ih k)
  | dne_schema Γ' A => intro k; exact Derives₀.dne_schema _ _
  | forall_not_ex_not Γ' A => intro k; exact Derives₀.forall_not_ex_not _ _
  | refl Γ' t => intro k; exact Derives₀.refl _ _
  | subst Γ' t₁ t₂ f' _ _ ih1 ih2 =>
      intro k
      have := Derives₀.subst (Γ'.map (liftFormula k)) (liftTerm k t₁) (liftTerm k t₂)
                (liftFormula (k + 1) f') (ih1 k)
                (by rw [← liftFormula_subst f' 0 k (Nat.zero_le _)]; exact ih2 k)
      rw [liftFormula_subst f' 0 k (Nat.zero_le _)]
      exact this

-- ============================================================
-- §5 · La pieza que cierra el `∃`/`∀`
-- ============================================================

mutual
theorem substTerm_lift_var : ∀ (k : Nat) (t : Term),
    substTerm k (Term.var k) (liftTerm (k + 1) t) = t := by
  intro k t
  cases t with
  | var n =>
      by_cases h1 : n < k + 1
      · by_cases h2 : n = k
        · simp [liftTerm, substTerm, h2]
        · simp [liftTerm, substTerm, h1, h2, show ¬ n > k by omega]
      · have e1 : n + 1 ≠ k := by omega
        have e2 : n + 1 > k := by omega
        simp [liftTerm, substTerm, h1, e1, e2]
  | func s ts =>
      simp only [liftTerm, substTerm]
      congr 1
      exact substTerms_lift_var k ts

theorem substTerms_lift_var : ∀ (k : Nat) (ts : List Term),
    substTerms k (Term.var k) (liftTerms (k + 1) ts) = ts := by
  intro k ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, substTerms, List.cons.injEq]
      exact ⟨substTerm_lift_var k t, substTerms_lift_var k ts'⟩
end

/-- ⭐ **`liftFormula (k+1)` se deshace sustituyendo la variable `k` por sí misma.**
Es lo que convierte `∀(¬A)` levantado en `¬A` dentro del contexto de `elim_ex`. -/
theorem substFormula_lift_var : ∀ (f : Formula) (k : Nat),
    substFormula k (Term.var k) (liftFormula (k + 1) f) = f := by
  intro f
  induction f with
  | bottom => intro k; rfl
  | atom p ts => intro k; simp only [liftFormula, substFormula, substTerms_lift_var]
  | eq t u => intro k; simp only [liftFormula, substFormula, substTerm_lift_var]
  | impl a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | «forall» a ih =>
      intro k
      have e : liftTerm 0 (Term.var k) = Term.var (k + 1) := by simp [liftTerm]
      simp only [liftFormula, substFormula, e]
      exact congrArg Formula.forall (ih (k + 1))
  | and a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | or a b iha ihb => intro k; simp only [liftFormula, substFormula, iha, ihb]
  | ex a ih =>
      intro k
      have e : liftTerm 0 (Term.var k) = Term.var (k + 1) := by simp [liftTerm]
      simp only [liftFormula, substFormula, e]
      exact congrArg Formula.ex (ih (k + 1))

/-- ⭐⭐ **`∃A` y `∀¬A` son contradictorios**, en forma finitaria: es el paso que el ensamblaje de
Henkin necesita y que obliga a tener `derives0_lift`. -/
theorem derives0_ex_forall_neg_absurd {Γ : List Formula} {A : Formula}
    (hex : Γ ⊢₀ Formula.ex A) (hall : Γ ⊢₀ Formula.forall (neg A)) :
    Γ ⊢₀ Formula.bottom := by
  refine Derives₀.elim_ex Γ A Formula.bottom hex ?_
  -- en el contexto levantado, `A` es la hipótesis del testigo
  have hlift : (Γ.map (liftFormula 0)) ⊢₀ liftFormula 0 (Formula.forall (neg A)) :=
    derives0_lift hall 0
  have hall' : (A :: Γ.map (liftFormula 0)) ⊢₀ Formula.forall (liftFormula 1 (neg A)) := by
    refine Derives₀.weakening _ _ _ hlift ?_
    intro x hx
    exact List.Mem.tail _ hx
  have hnegA : (A :: Γ.map (liftFormula 0)) ⊢₀ neg A := by
    have := Derives₀.elim_forall _ (liftFormula 1 (neg A)) (Term.var 0) hall'
    rwa [substFormula_lift_var (neg A) 0] at this
  exact Derives₀.elim_impl _ A Formula.bottom hnegA (Derives₀.hyp _ _ (List.Mem.head _))

end FOL.Lift0

#print axioms FOL.Lift0.derives0_lift
#print axioms FOL.Lift0.derives0_ex_forall_neg_absurd
