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

-- Lemma: substTerm (c+1) (liftTerm c s) (liftTerm c t) = liftTerm c (substTerm c s t)
-- This is the standard substitution/lift commutation lemma for De Bruijn indices.
mutual
theorem substTerm_lift_comm (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 1) (liftTerm c s) (liftTerm c t) = liftTerm c (substTerm c s t) := by
  cases t with
  | var n =>
    by_cases h1 : n < c
    · have hne : n ≠ c + 1 := by omega
      have hlt : ¬ n > c + 1 := by omega
      have hnec : n ≠ c := by omega
      have hltc : ¬ n > c := by omega
      simp [liftTerm, substTerm, h1, hne, hlt, hnec, hltc]
    · by_cases h2 : n = c
      · subst h2
        simp [liftTerm, substTerm]
      · have hgt : n > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) (Ne.symm h2)
        have hne2 : n + 1 ≠ c + 1 := by omega
        have hgt2 : n + 1 > c + 1 := by omega
        have hge : ¬ n - 1 < c := by omega
        simp [liftTerm, substTerm, show ¬ n < c from h1, h2, hgt, hgt2, hge]
        omega
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_lift_comm ts c s

theorem substTerms_lift_comm (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 1) (liftTerm c s) (liftTerms c ts) = liftTerms c (substTerms c s ts) := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms, List.cons.injEq]
    exact ⟨substTerm_lift_comm t c s, substTerms_lift_comm ts' c s⟩
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

-- Lemma: substTerm (c+1) s (liftTerm c (liftTerm c t)) = liftTerm c t
-- (substituting into a doubly-lifted term at offset c+1 gives back the singly-lifted term)
mutual
theorem substTerm_liftLift (t : Term) (c : Nat) (s : Term) :
    substTerm (c + 1) s (liftTerm c (liftTerm c t)) = liftTerm c t := by
  cases t with
  | var n =>
    by_cases h1 : n < c
    · simp [liftTerm, substTerm, h1, show ¬ n = c + 1 from by omega, show ¬ n > c + 1 from by omega]
    · have hge2 : ¬ n + 1 < c := by omega
      have hgt : n + 1 + 1 > c + 1 := by omega
      simp [liftTerm, substTerm, h1, hge2, hgt]
      omega
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_liftLift ts c s

theorem substTerms_liftLift (ts : List Term) (c : Nat) (s : Term) :
    substTerms (c + 1) s (liftTerms c (liftTerms c ts)) = liftTerms c ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms, List.cons.injEq]
    exact ⟨substTerm_liftLift t c s, substTerms_liftLift ts' c s⟩
end

end FOL
