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

-- Conmutación de `liftTerm 0` con `liftTerm c` (estándar De Bruijn).
mutual
theorem liftTerm_comm_zero (t : Term) (c : Nat) :
    liftTerm 0 (liftTerm c t) = liftTerm (c + 1) (liftTerm 0 t) := by
  cases t with
  | var n =>
      by_cases h : n < c
      · simp [liftTerm, h, show n + 1 < c + 1 from by omega]
      · simp [liftTerm, h, show ¬ n + 1 < c + 1 from by omega]
  | func f ts => simp only [liftTerm]; congr 1; exact liftTerms_comm_zero ts c
theorem liftTerms_comm_zero (ts : List Term) (c : Nat) :
    liftTerms 0 (liftTerms c ts) = liftTerms (c + 1) (liftTerms 0 ts) := by
  cases ts with
  | nil => rfl
  | cons t ts' => simp only [liftTerms]; rw [liftTerm_comm_zero, liftTerms_comm_zero]
end

/-- **Conmutación subst/lift a nivel fórmula** (versión fórmula de `substTerm_lift_comm`):
    `substFormula (c+1) (liftTerm c s) (liftFormula c f) = liftFormula c (substFormula c s f)`.
    Los binders ∀/∃ recurren a `c+1` usando `liftTerm_comm_zero`. -/
theorem substFormula_lift_comm : ∀ (f : Formula) (c : Nat) (s : Term),
    substFormula (c + 1) (liftTerm c s) (liftFormula c f) = liftFormula c (substFormula c s f) := by
  intro f
  induction f with
  | bottom => intro c s; rfl
  | atom p ts => intro c s; simp only [liftFormula, substFormula, substTerms_lift_comm]
  | eq t u => intro c s; simp only [liftFormula, substFormula, substTerm_lift_comm]
  | impl a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | «forall» a iha =>
      intro c s; simp only [liftFormula, substFormula]
      rw [show liftTerm 0 (liftTerm c s) = liftTerm (c+1) (liftTerm 0 s) from liftTerm_comm_zero s c,
          iha (c+1) (liftTerm 0 s)]
  | and a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | or a b iha ihb => intro c s; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | ex a iha =>
      intro c s; simp only [liftFormula, substFormula]
      rw [show liftTerm 0 (liftTerm c s) = liftTerm (c+1) (liftTerm 0 s) from liftTerm_comm_zero s c,
          iha (c+1) (liftTerm 0 s)]

set_option linter.unusedSimpArgs false

-- Conmutación subst/lift con lift en 0 y subst en `v+1` (nivel término).
mutual
theorem substTerm_lift_comm_zero (s : Term) (n : Term) (v : Nat) :
    substTerm (v + 1) (liftTerm 0 n) (liftTerm 0 s) = liftTerm 0 (substTerm v n s) := by
  cases s with
  | var k =>
      rw [show liftTerm 0 (.var k) = .var (k+1) from by simp [liftTerm]]
      by_cases h1 : k = v
      · subst h1; simp [substTerm, liftTerm]
      · by_cases h2 : k > v
        · simp [substTerm, liftTerm, show k + 1 ≠ v + 1 from by omega, show k + 1 > v + 1 from by omega,
            h1, h2, show k - 1 + 1 = k from by omega]
        · simp [substTerm, liftTerm, show k + 1 ≠ v + 1 from by omega, show ¬ k + 1 > v + 1 from by omega,
            h1, h2]
  | func f ts => simp only [liftTerm, substTerm]; congr 1; exact substTerms_lift_comm_zero ts n v
theorem substTerms_lift_comm_zero (ts : List Term) (n : Term) (v : Nat) :
    substTerms (v + 1) (liftTerm 0 n) (liftTerms 0 ts) = liftTerms 0 (substTerms v n ts) := by
  cases ts with
  | nil => rfl
  | cons s ss => simp only [liftTerms, substTerms]; rw [substTerm_lift_comm_zero, substTerms_lift_comm_zero]
end

-- Composición subst-subst-lift generalizada al nivel `v` (nivel término).
mutual
theorem substTerm_subst_lift_gen (u : Term) (n s : Term) (v : Nat) :
    substTerm v n (substTerm v s (liftTerm (v + 1) u)) = substTerm v (substTerm v n s) u := by
  cases u with
  | var k =>
      by_cases h1 : k < v + 1
      · rw [show liftTerm (v+1) (.var k) = .var k from by simp [liftTerm, h1]]
        by_cases h2 : k = v
        · subst h2; simp [substTerm]
        · simp [substTerm, h2, show ¬ k > v from by omega]
      · rw [show liftTerm (v+1) (.var k) = .var (k+1) from by simp [liftTerm, h1]]
        simp [substTerm, show ¬ k + 1 = v from by omega, show k + 1 > v from by omega,
          show ¬ k = v from by omega, show k > v from by omega]
  | func f ts => simp only [liftTerm, substTerm]; congr 1; exact substTerms_subst_lift_gen ts n s v
theorem substTerms_subst_lift_gen (ts : List Term) (n s : Term) (v : Nat) :
    substTerms v n (substTerms v s (liftTerms (v + 1) ts)) = substTerms v (substTerm v n s) ts := by
  cases ts with
  | nil => rfl
  | cons u us => simp only [liftTerms, substTerms]; rw [substTerm_subst_lift_gen, substTerms_subst_lift_gen]
end

/-- **Composición subst-subst-lift a nivel fórmula, generalizada al nivel `v`**:
    `substFormula v n (substFormula v s (liftFormula (v+1) f)) = substFormula v (substTerm v n s) f`.
    Casos ∀/∃ vía `substTerm_lift_comm_zero`; atom/eq vía la versión término. -/
theorem subst_subst_lift_gen : ∀ (f : Formula) (n s : Term) (v : Nat),
    substFormula v n (substFormula v s (liftFormula (v + 1) f)) = substFormula v (substTerm v n s) f := by
  intro f
  induction f with
  | bottom => intro n s v; rfl
  | atom p ts => intro n s v; simp only [liftFormula, substFormula, substTerms_subst_lift_gen]
  | eq t u => intro n s v; simp only [liftFormula, substFormula, substTerm_subst_lift_gen]
  | impl a b iha ihb => intro n s v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | «forall» a iha =>
      intro n s v; simp only [liftFormula, substFormula]
      rw [iha (liftTerm 0 n) (liftTerm 0 s) (v+1), substTerm_lift_comm_zero]
  | and a b iha ihb => intro n s v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | or a b iha ihb => intro n s v; simp only [liftFormula, substFormula]; rw [iha, ihb]
  | ex a iha =>
      intro n s v; simp only [liftFormula, substFormula]
      rw [iha (liftTerm 0 n) (liftTerm 0 s) (v+1), substTerm_lift_comm_zero]

-- Lema de sustitución (Barendregt) para niveles consecutivos `j+1`/`j` (convención
-- decremental): conmuta dos sustituciones anidadas. Casos de binder vía
-- `substTerm_lift_comm_zero` + `liftTerm_comm_zero`.
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
        simp [substTerm, show ¬ k = k+2 from by omega, show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [substTerm, show ¬ j+1 = j from by omega, show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [substTerm, show ¬ j+2 = j from by omega, show j+2 > j from by omega,
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

/-- **Lema de sustitución de Barendregt (nivel fórmula)**, niveles `j+1`/`j`:
    `substFormula (j+1) a (substFormula j b f) = substFormula j (substTerm (j+1) a b) (substFormula (j+2) (liftTerm j a) f)`.
    Casos ∀/∃ vía `substTerm_lift_comm_zero` + `liftTerm_comm_zero`. -/
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

end FOL
