/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived

namespace FOL.Theorems.Quantifiers

-- ============================================================
-- Nivel 4: Cuantificadores
-- ============================================================

-- Propiedades de sustitución para variables abstractas (De Bruijn).
--
-- ⚠️ CORRECCIÓN 2026-06-23: `subst_lift_cancel_formula` estaba declarado como
-- `axiom` con un enunciado GENERAL **FALSO**: `substFormula v t (liftFormula (v+1) f) = f`
-- para `t` arbitrario es falso (contraejemplo `f = atom P [#0]`, `v=0`, `t=#5`:
-- `liftFormula 1 (atom P [#0]) = atom P [#0]`, y `substFormula 0 #5 (atom P [#0]) =
-- atom P [#5] ≠ f`). La forma que el código realmente usa (todos los `rw` instancian
-- `t = #v`) es **verdadera y demostrable**: `substFormula v (#v) (liftFormula (v+1) f) = f`
-- (la variable recién insertada en el nivel `v+1` se sustituye por la del nivel `v`).
-- Aquí se prueba de verdad (sin `axiom`), junto con su lema de término.

/- Cancelación lift/subst a nivel término (forma `t = #v`): la variable insertada
   en `v+1` se cancela al sustituir `#v` en el nivel `v`. -/
mutual
theorem substTerm_lift_cancel_var (t : Term) (v : Nat) :
    substTerm v (.var v) (liftTerm (v + 1) t) = t := by
  cases t with
  | var n =>
      by_cases h : n < v + 1
      · rw [show liftTerm (v+1) (.var n) = .var n from by simp [liftTerm, h]]
        by_cases h2 : n = v
        · subst h2; simp [substTerm]
        · simp [substTerm, h2, show ¬ n > v from by omega]
      · rw [show liftTerm (v+1) (.var n) = .var (n+1) from by simp [liftTerm, h]]
        simp [substTerm, show ¬ n + 1 = v from by omega, show n + 1 > v from by omega]
  | func f ts =>
      simp only [liftTerm, substTerm]; congr 1; exact substTerms_lift_cancel_var ts v
theorem substTerms_lift_cancel_var (ts : List Term) (v : Nat) :
    substTerms v (.var v) (liftTerms (v + 1) ts) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, substTerms]
      rw [substTerm_lift_cancel_var, substTerms_lift_cancel_var]
end

/-- **Cancelación lift/subst (nivel fórmula), forma `t = #v`** (antes un `axiom`
    general falso; ahora teorema). Todos los `rw [subst_lift_cancel_formula]` del
    proyecto instancian `t = #0`, cubiertos por esta forma. -/
theorem subst_lift_cancel_formula : ∀ (f : Formula) (v : Nat),
    substFormula v (.var v) (liftFormula (v + 1) f) = f := by
  intro f
  induction f with
  | bottom => intro v; rfl
  | atom p ts => intro v; simp only [liftFormula, substFormula, substTerms_lift_cancel_var]
  | eq t u => intro v; simp only [liftFormula, substFormula, substTerm_lift_cancel_var]
  | impl a b iha ihb => intro v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | «forall» a iha =>
      intro v; simp only [liftFormula, substFormula, liftTerm, if_neg (Nat.not_lt_zero v)]; rw [iha]
  | and a b iha ihb => intro v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | or a b iha ihb => intro v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | ex a iha =>
      intro v; simp only [liftFormula, substFormula, liftTerm, if_neg (Nat.not_lt_zero v)]; rw [iha]

/-- Distributividad de `substFormula` sobre `∧` (definicional; antes `axiom`). -/
theorem subst_distrib_and (A B : Formula) (v : Nat) (t : Term) :
    substFormula v t (.and A B) = .and (substFormula v t A) (substFormula v t B) := rfl
/-- Distributividad de `liftFormula` sobre `∧` (definicional; antes `axiom`). -/
theorem lift_distrib_and (A B : Formula) (c : Nat) :
    liftFormula c (.and A B) = .and (liftFormula c A) (liftFormula c B) := rfl

-- Lema auxiliar: ∀x. A ⇒ ∀x. ¬¬A
theorem forall_dni {Γ A} : Γ ⊢ .impl (.forall A) (.forall (neg (neg A))) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.elim_impl (A := A)
  · exact FOL.Theorems.Neg.double_neg_intro
  · have h : ((.forall A) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
      apply Derives.elim_forall (A := liftFormula 1 A) (t := .var 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    exact h

-- Dualidad ∀/∃ (constructiva): (∃x. ¬A) ⇒ ¬(∀x. A)
theorem exists_not_impl_forall_not {Γ A} : Γ ⊢ .impl (.ex (neg A)) (neg (.forall A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_ex (A := neg A) (B := ⊥)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.head _
    · have h_forall : ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) ⊢ .forall (liftFormula 1 A) := by
        have mem_second : liftFormula 0 (.forall A) ∈ ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) := by
          exact List.Mem.tail _ (List.Mem.head _)
        apply Derives.hyp
        exact mem_second
      have h_elim : ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
        apply Derives.elim_forall (A := liftFormula 1 A) (t := .var 0)
        exact h_forall
      rw [subst_lift_cancel_formula] at h_elim
      exact h_elim

-- Dualidad ∀/∃ (clásica): ¬(∀x. A) ⇒ ∃x. ¬A
-- Dirección clásica; no es derivable intuicionísticamente.
axiom forall_not_impl_exists_not {Γ : List Formula} {A : Formula} :
    Γ ⊢ .impl (neg (.forall A)) (.ex (neg A))

-- 15. Distribución de ∀ sobre ∧: (∀x. A ∧ B) ⇔ (∀x. A) ∧ (∀x. B)

theorem forall_and_impl_and_forall {Γ A B} : Γ ⊢ .impl (.forall (.and A B)) (.and (.forall A) (.forall B)) := by
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.intro_forall
    have h : ((.forall (.and A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (.and A B)) := by
      apply Derives.elim_forall (A := liftFormula 1 (.and A B)) (t := .var 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    apply Derives.elim_and_l (B := B)
    exact h
  · apply Derives.intro_forall
    have h : ((.forall (.and A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (.and A B)) := by
      apply Derives.elim_forall (A := liftFormula 1 (.and A B)) (t := .var 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    apply Derives.elim_and_r (A := A)
    exact h

theorem and_forall_impl_forall_and {Γ A B} : Γ ⊢ .impl (.and (.forall A) (.forall B)) (.forall (.and A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.intro_and
  · have h_ctx : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (.and (.forall A) (.forall B)) := by
      apply Derives.hyp
      exact List.Mem.head _
    rw [lift_distrib_and] at h_ctx
    have h_forall_A : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ .forall (liftFormula 1 A) := by
      apply Derives.elim_and_l (B := liftFormula 0 (.forall B))
      exact h_ctx
    have hA : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
      apply Derives.elim_forall (A := liftFormula 1 A) (t := .var 0)
      exact h_forall_A
    rw [subst_lift_cancel_formula] at hA
    exact hA
  · have h_ctx : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (.and (.forall A) (.forall B)) := by
      apply Derives.hyp
      exact List.Mem.head _
    rw [lift_distrib_and] at h_ctx
    have h_forall_B : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ .forall (liftFormula 1 B) := by
      apply Derives.elim_and_r (A := liftFormula 0 (.forall A))
      exact h_ctx
    have hB : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 B) := by
      apply Derives.elim_forall (A := liftFormula 1 B) (t := .var 0)
      exact h_forall_B
    rw [subst_lift_cancel_formula] at hB
    exact hB

theorem distrib_forall_and {Γ A B} : Γ ⊢ iff (.forall (.and A B)) (.and (.forall A) (.forall B)) := by
  apply Derives.intro_and
  · exact forall_and_impl_and_forall
  · exact and_forall_impl_forall_and

end FOL.Theorems.Quantifiers

export FOL.Theorems.Quantifiers (
  subst_lift_cancel_formula
  subst_distrib_and
  lift_distrib_and
  forall_dni
  exists_not_impl_forall_not
  forall_not_impl_exists_not
  forall_and_impl_and_forall
  and_forall_impl_forall_and
  distrib_forall_and
)
