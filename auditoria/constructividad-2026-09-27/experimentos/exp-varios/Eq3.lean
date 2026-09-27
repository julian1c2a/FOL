import FOL.Theorems.Eq
open FOL
set_option linter.unusedSimpArgs false

namespace Exp0

/-! Variante 1: MISMA prueba que `FOL.substTerm_subst_comm_succ`, sólo quitando del
    simp set los dos lemas del núcleo que arrastran `Classical.choice`. -/
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [substTerm, show ¬ k = j from by omega, show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show k > j from hgt,
            show ¬ k = j+2 from by omega, show k > j+2 from h2,
            show ¬ k - 1 = j from by omega, show k - 1 > j from by omega,
            show ¬ k - 1 = j+1 from by omega, show k - 1 > j+1 from by omega]
  | func f ts => simp only [substTerm, liftTerm]; congr 1; exact substTerms_subst_comm_succ ts a b j
theorem substTerms_subst_comm_succ (ts : List Term) (a b : Term) (j : Nat) :
    substTerms (j+1) a (substTerms j b ts)
      = substTerms j (substTerm (j+1) a b) (substTerms (j+2) (liftTerm j a) ts) := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [substTerms]; rw [substTerm_subst_comm_succ, substTerms_subst_comm_succ]
end

theorem subst_subst_comm_succ : ∀ (f : Formula) (a b : Term) (j : Nat),
    substFormula (j+1) a (substFormula j b f)
      = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f) := by
  intro f
  induction f with
  | bottom => intro a b j; rfl
  | atom p ts => intro a b j; simp only [substFormula, substTerms_subst_comm_succ]
  | eq t u => intro a b j; simp only [substFormula, substTerm_subst_comm_succ]
  | impl x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | «forall» g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]
  | and x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | or x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | ex g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]

end Exp0


#print axioms Exp0.substTerm_subst_comm_succ


namespace Exp1

/-! Variante 1: MISMA prueba que `FOL.substTerm_subst_comm_succ`, sólo quitando del
    simp set los dos lemas del núcleo que arrastran `Classical.choice`. -/
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show k > j from hgt,
            show ¬ k = j+2 from by omega, show k > j+2 from h2,
            show ¬ k - 1 = j from by omega, show k - 1 > j from by omega,
            show ¬ k - 1 = j+1 from by omega, show k - 1 > j+1 from by omega]
  | func f ts => simp only [substTerm, liftTerm]; congr 1; exact substTerms_subst_comm_succ ts a b j
theorem substTerms_subst_comm_succ (ts : List Term) (a b : Term) (j : Nat) :
    substTerms (j+1) a (substTerms j b ts)
      = substTerms j (substTerm (j+1) a b) (substTerms (j+2) (liftTerm j a) ts) := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [substTerms]; rw [substTerm_subst_comm_succ, substTerms_subst_comm_succ]
end

theorem subst_subst_comm_succ : ∀ (f : Formula) (a b : Term) (j : Nat),
    substFormula (j+1) a (substFormula j b f)
      = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f) := by
  intro f
  induction f with
  | bottom => intro a b j; rfl
  | atom p ts => intro a b j; simp only [substFormula, substTerms_subst_comm_succ]
  | eq t u => intro a b j; simp only [substFormula, substTerm_subst_comm_succ]
  | impl x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | «forall» g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]
  | and x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | or x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | ex g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]

end Exp1


#print axioms Exp1.substTerm_subst_comm_succ


namespace Exp2

/-! Variante 1: MISMA prueba que `FOL.substTerm_subst_comm_succ`, sólo quitando del
    simp set los dos lemas del núcleo que arrastran `Classical.choice`. -/
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show k > j from hgt,
            show ¬ k = j+2 from by omega, show k > j+2 from h2,
            show ¬ k - 1 = j from by omega, show k - 1 > j from by omega,
            show ¬ k - 1 = j+1 from by omega, show k - 1 > j+1 from by omega]
  | func f ts => simp only [substTerm, liftTerm]; congr 1; exact substTerms_subst_comm_succ ts a b j
theorem substTerms_subst_comm_succ (ts : List Term) (a b : Term) (j : Nat) :
    substTerms (j+1) a (substTerms j b ts)
      = substTerms j (substTerm (j+1) a b) (substTerms (j+2) (liftTerm j a) ts) := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [substTerms]; rw [substTerm_subst_comm_succ, substTerms_subst_comm_succ]
end

theorem subst_subst_comm_succ : ∀ (f : Formula) (a b : Term) (j : Nat),
    substFormula (j+1) a (substFormula j b f)
      = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f) := by
  intro f
  induction f with
  | bottom => intro a b j; rfl
  | atom p ts => intro a b j; simp only [substFormula, substTerms_subst_comm_succ]
  | eq t u => intro a b j; simp only [substFormula, substTerm_subst_comm_succ]
  | impl x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | «forall» g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]
  | and x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | or x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | ex g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]

end Exp2


#print axioms Exp2.substTerm_subst_comm_succ


namespace Exp3

/-! Variante 1: MISMA prueba que `FOL.substTerm_subst_comm_succ`, sólo quitando del
    simp set los dos lemas del núcleo que arrastran `Classical.choice`. -/
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show k > j from hgt,
            show ¬ k = j+2 from by omega, show k > j+2 from h2,
            show ¬ k - 1 = j from by omega, show k - 1 > j from by omega,
            show ¬ k - 1 = j+1 from by omega, show k - 1 > j+1 from by omega]
  | func f ts => simp only [substTerm, liftTerm]; congr 1; exact substTerms_subst_comm_succ ts a b j
theorem substTerms_subst_comm_succ (ts : List Term) (a b : Term) (j : Nat) :
    substTerms (j+1) a (substTerms j b ts)
      = substTerms j (substTerm (j+1) a b) (substTerms (j+2) (liftTerm j a) ts) := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [substTerms]; rw [substTerm_subst_comm_succ, substTerms_subst_comm_succ]
end

theorem subst_subst_comm_succ : ∀ (f : Formula) (a b : Term) (j : Nat),
    substFormula (j+1) a (substFormula j b f)
      = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f) := by
  intro f
  induction f with
  | bottom => intro a b j; rfl
  | atom p ts => intro a b j; simp only [substFormula, substTerms_subst_comm_succ]
  | eq t u => intro a b j; simp only [substFormula, substTerm_subst_comm_succ]
  | impl x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | «forall» g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]
  | and x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | or x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | ex g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]

end Exp3


#print axioms Exp3.substTerm_subst_comm_succ


namespace Exp4

/-! Variante 1: MISMA prueba que `FOL.substTerm_subst_comm_succ`, sólo quitando del
    simp set los dos lemas del núcleo que arrastran `Classical.choice`. -/
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega, show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [substTerm, show ¬ k = j from by omega, show k > j from hgt,
            show ¬ k = j+2 from by omega, show k > j+2 from h2,
            show ¬ k - 1 = j from by omega, show k - 1 > j from by omega,
            show ¬ k - 1 = j+1 from by omega, show k - 1 > j+1 from by omega]
  | func f ts => simp only [substTerm, liftTerm]; congr 1; exact substTerms_subst_comm_succ ts a b j
theorem substTerms_subst_comm_succ (ts : List Term) (a b : Term) (j : Nat) :
    substTerms (j+1) a (substTerms j b ts)
      = substTerms j (substTerm (j+1) a b) (substTerms (j+2) (liftTerm j a) ts) := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [substTerms]; rw [substTerm_subst_comm_succ, substTerms_subst_comm_succ]
end

theorem subst_subst_comm_succ : ∀ (f : Formula) (a b : Term) (j : Nat),
    substFormula (j+1) a (substFormula j b f)
      = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f) := by
  intro f
  induction f with
  | bottom => intro a b j; rfl
  | atom p ts => intro a b j; simp only [substFormula, substTerms_subst_comm_succ]
  | eq t u => intro a b j; simp only [substFormula, substTerm_subst_comm_succ]
  | impl x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | «forall» g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]
  | and x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | or x y ihx ihy => intro a b j; simp only [substFormula]; rw [ihx, ihy]
  | ex g ih =>
      intro a b j; simp only [substFormula]
      rw [ih (liftTerm 0 a) (liftTerm 0 b) (j+1), substTerm_lift_comm_zero, liftTerm_comm_zero]

end Exp4


#print axioms Exp4.substTerm_subst_comm_succ
