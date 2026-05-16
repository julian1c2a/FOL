import FOL.FOL

namespace FOL

mutual
theorem substTerm_liftTerm (t : Term) (c : Nat) (s : Term) :
    substTerm c s (liftTerm c t) = t := by
  cases t with
  | var n =>
    unfold liftTerm
    split
    · next h =>
      unfold substTerm
      split
      · next hEq => omega
      · split
        · next hGt => omega
        · next hNotGt => rfl
    · next h =>
      unfold substTerm
      split
      · next hEq => omega
      · split
        · next hGt =>
          have h1 : n + 1 - 1 = n := by omega
          rw [h1]
        · next hNotGt => omega
  | func f ts =>
    unfold liftTerm
    unfold substTerm
    have ih := substTerms_liftTerms ts c s
    rw [ih]

theorem substTerms_liftTerms (ts : List Term) (c : Nat) (s : Term) :
    substTerms c s (liftTerms c ts) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    unfold liftTerms
    unfold substTerms
    have ih1 := substTerm_liftTerm t c s
    have ih2 := substTerms_liftTerms ts' c s
    rw [ih1, ih2]
end

theorem derive_eq_symm {Γ : List Formula} {t1 t2 : Term} (h : Derives Γ (.eq t1 t2)) :
    Derives Γ (.eq t2 t1) := by
  let f := Formula.eq (.var 0) (liftTerm 0 t1)
  have hSubst1 : substFormula 0 t1 f = Formula.eq t1 t1 := by
    change Formula.eq (substTerm 0 t1 (.var 0)) (substTerm 0 t1 (liftTerm 0 t1)) = Formula.eq t1 t1
    rw [substTerm_liftTerm t1 0 t1]
    rfl
  have hSubst2 : substFormula 0 t2 f = Formula.eq t2 t1 := by
    change Formula.eq (substTerm 0 t2 (.var 0)) (substTerm 0 t2 (liftTerm 0 t1)) = Formula.eq t2 t1
    rw [substTerm_liftTerm t1 0 t2]
    rfl
  have hRefl := Derives.refl Γ t1
  have hSubstDer := Derives.subst Γ t1 t2 f h
  rw [hSubst1] at hSubstDer
  have hDer2 := hSubstDer hRefl
  rw [hSubst2] at hDer2
  exact hDer2

theorem derive_eq_trans {Γ : List Formula} {t1 t2 t3 : Term} 
    (h12 : Derives Γ (.eq t1 t2)) (h23 : Derives Γ (.eq t2 t3)) :
    Derives Γ (.eq t1 t3) := by
  let f := Formula.eq (liftTerm 0 t1) (.var 0)
  have hSubst2 : substFormula 0 t2 f = Formula.eq t1 t2 := by
    change Formula.eq (substTerm 0 t2 (liftTerm 0 t1)) (substTerm 0 t2 (.var 0)) = Formula.eq t1 t2
    rw [substTerm_liftTerm t1 0 t2]
    rfl
  have hSubst3 : substFormula 0 t3 f = Formula.eq t1 t3 := by
    change Formula.eq (substTerm 0 t3 (liftTerm 0 t1)) (substTerm 0 t3 (.var 0)) = Formula.eq t1 t3
    rw [substTerm_liftTerm t1 0 t3]
    rfl
  have hSubstDer := Derives.subst Γ t2 t3 f h23
  rw [hSubst2] at hSubstDer
  have hDer3 := hSubstDer h12
  rw [hSubst3] at hDer3
  exact hDer3

end FOL
