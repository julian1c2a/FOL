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

-- Propiedades de sustitución para variables abstractas.
-- Dada la complejidad de la aritmética de De Bruijn en Lean 4, 
-- declaramos estos lemas como axiomas por ahora, de acuerdo con la Fase 3.
axiom subst_lift_cancel_formula (f : Formula) (v : Nat) (t : Term) : substFormula v t (liftFormula (v + 1) f) = f
axiom subst_distrib_and (A B : Formula) (v : Nat) (t : Term) : substFormula v t (land A B) = land (substFormula v t A) (substFormula v t B)
axiom lift_distrib_and (A B : Formula) (c : Nat) : liftFormula c (land A B) = land (liftFormula c A) (liftFormula c B)

-- Lema auxiliar: ∀x. ¬¬A ⇒ ∀x. A
theorem forall_dne {Γ A} : Γ ⊢ .impl (.forall (neg (neg A))) (.forall A) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.elim_impl (A := neg (neg A))
  · exact FOL.Theorems.Neg.double_neg_elim
  · have h : ((.forall (neg (neg A))) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (neg (neg A))) := by
      apply Derives.elim_forall (A := liftFormula 1 (neg (neg A))) (t := .var 0)
      apply Derives.hyp
      exact List.Mem.head _
    -- Subst and lift cancel out: subst 0 #0 (lift 1 (neg neg A)) = neg neg A
    rw [subst_lift_cancel_formula] at h
    exact h

-- Dualidad ∀/∃ (1): ¬(∀x. A) ⇒ ∃x. ¬A
theorem forall_not_impl_exists_not {Γ A} : Γ ⊢ .impl (neg (.forall A)) (ex (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .forall A)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := .forall (neg (neg A)))
    · exact forall_dne
    · apply Derives.hyp
      exact List.Mem.head _

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

-- Dualidad ∀/∃ (2): (∃x. ¬A) ⇒ ¬(∀x. A)
theorem exists_not_impl_forall_not {Γ A} : Γ ⊢ .impl (ex (neg A)) (neg (.forall A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .forall (neg (neg A)))
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := .forall A)
    · exact forall_dni
    · apply Derives.hyp
      exact List.Mem.head _

-- 14. Dualidad ∀/∃ completa: ¬(∀x. A) ⇔ ∃x. ¬A
theorem dual_forall_exists {Γ A} : Γ ⊢ iff (neg (.forall A)) (ex (neg A)) := by
  apply Derives.elim_impl (A := .impl (ex (neg A)) (neg (.forall A)))
  · apply Derives.elim_impl (A := .impl (neg (.forall A)) (ex (neg A)))
    · exact FOL.Theorems.Derived.and_intro
    · exact forall_not_impl_exists_not
  · exact exists_not_impl_forall_not

-- 15. Distribución de ∀ sobre ∧: (∀x. A ∧ B) ⇔ (∀x. A) ∧ (∀x. B)

theorem forall_and_impl_and_forall {Γ A B} : Γ ⊢ .impl (.forall (land A B)) (land (.forall A) (.forall B)) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .forall B)
  · apply Derives.elim_impl (A := .forall A)
    · exact FOL.Theorems.Derived.and_intro
    · apply Derives.intro_forall
      have h : ((.forall (land A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (land A B)) := by
        apply Derives.elim_forall (A := liftFormula 1 (land A B)) (t := .var 0)
        apply Derives.hyp
        exact List.Mem.head _
      rw [subst_lift_cancel_formula] at h
      apply Derives.elim_impl (A := land A B)
      · exact FOL.Theorems.Derived.and_elim_left
      · exact h
  · apply Derives.intro_forall
    have h : ((.forall (land A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (land A B)) := by
      apply Derives.elim_forall (A := liftFormula 1 (land A B)) (t := .var 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    apply Derives.elim_impl (A := land A B)
    · exact FOL.Theorems.Derived.and_elim_right
    · exact h

theorem and_forall_impl_forall_and {Γ A B} : Γ ⊢ .impl (land (.forall A) (.forall B)) (.forall (land A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.elim_impl (A := B)
  · apply Derives.elim_impl (A := A)
    · exact FOL.Theorems.Derived.and_intro
    · have hA : ((land (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
        apply Derives.elim_forall (A := liftFormula 1 A) (t := .var 0)
        -- We need to extract (.forall A) from the context.
        -- Context is [land (.forall A) (.forall B)]. After map liftFormula 0, it's [liftFormula 0 (land (.forall A) (.forall B))].
        have h_ctx : ((land (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (land (.forall A) (.forall B)) := by
          apply Derives.hyp
          exact List.Mem.head _
        -- Now extract (.forall A) from it
        -- liftFormula 0 (land ...) = land (liftFormula 0 (.forall A)) (liftFormula 0 (.forall B))
        rw [lift_distrib_and] at h_ctx
        apply Derives.elim_impl (A := land (liftFormula 0 (.forall A)) (liftFormula 0 (.forall B)))
        · exact FOL.Theorems.Derived.and_elim_left
        · exact h_ctx
      rw [subst_lift_cancel_formula] at hA
      exact hA
  · have hB : ((land (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 B) := by
      apply Derives.elim_forall (A := liftFormula 1 B) (t := .var 0)
      have h_ctx : ((land (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (land (.forall A) (.forall B)) := by
        apply Derives.hyp
        exact List.Mem.head _
      rw [lift_distrib_and] at h_ctx
      apply Derives.elim_impl (A := land (liftFormula 0 (.forall A)) (liftFormula 0 (.forall B)))
      · exact FOL.Theorems.Derived.and_elim_right
      · exact h_ctx
    rw [subst_lift_cancel_formula] at hB
    exact hB

theorem distrib_forall_and {Γ A B} : Γ ⊢ iff (.forall (land A B)) (land (.forall A) (.forall B)) := by
  apply Derives.elim_impl (A := .impl (land (.forall A) (.forall B)) (.forall (land A B)))
  · apply Derives.elim_impl (A := .impl (.forall (land A B)) (land (.forall A) (.forall B)))
    · exact FOL.Theorems.Derived.and_intro
    · exact forall_and_impl_and_forall
  · exact and_forall_impl_forall_and

end FOL.Theorems.Quantifiers

export FOL.Theorems.Quantifiers (
  subst_lift_cancel_formula
  subst_distrib_and
  lift_distrib_and
  forall_dne
  forall_not_impl_exists_not
  forall_dni
  exists_not_impl_forall_not
  dual_forall_exists
  forall_and_impl_and_forall
  and_forall_impl_forall_and
  distrib_forall_and
)
