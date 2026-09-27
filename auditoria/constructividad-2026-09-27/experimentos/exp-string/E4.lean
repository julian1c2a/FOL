import FOL.Compacity0

/-! Propagacion MEDIDA: se reconstruyen, sobre las cuatro variantes sin choice, los
titulares que segun el grafo dependen SOLO de las entradas «String». Las pruebas son copia
literal de FOL (Fresh0 §3–§6, Enumeration capas 3–4, Compacity0 §3), cambiando unicamente
el lema de entrada. -/

namespace Exp
open FOL.Fresh0 (cst shift shift_inj shiftTheory)
open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0

-- ===== las cuatro entradas =====
theorem cst_zero_ne (n : Nat) : cst 0 ≠ cst (n + 1) := of_decide_eq_false rfl

theorem cst_ne_shift : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, _ => of_decide_eq_false rfl
  | _ + 1, _ => of_decide_eq_false rfl

theorem cst_inj : ∀ m n : Nat, cst m = cst n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (cst_zero_ne _)
  | _ + 1, 0, h => absurd h.symm (cst_zero_ne _)
  | m + 1, n + 1, h => congrArg (· + 1) (cst_inj m n ((String.append_right_inj "a").mp h))

theorem cst_utf8ByteSize : ∀ m : Nat, (cst m).utf8ByteSize = m + 1
  | 0 => rfl
  | m + 1 => by
      show ("a" ++ cst m).utf8ByteSize = m + 1 + 1
      rw [String.utf8ByteSize_append, cst_utf8ByteSize m]
      show 1 + (m + 1) = m + 1 + 1
      omega

theorem cst_bound_sym (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.utf8ByteSize, fun m hm he => by
    have h := congrArg String.utf8ByteSize he
    rw [cst_utf8ByteSize] at h
    omega⟩

open FOL.Metamath.Enumeration (natToString natToList natToList_surj map_ofNat_toNat) in
theorem natToString_surj (s : String) : ∃ n, natToString n = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  obtain ⟨n, hn⟩ := natToList_surj (l.map Char.toNat)
  exact ⟨n, congrArg String.ofList (by rw [hn, map_ofNat_toNat])⟩

-- ===== Fresh0 §3 =====
mutual
theorem not_occurs_shiftTerm (n : Nat) : ∀ t : Term,
    Not (occursTerm (cst n) (renameTerm shift t))
  | .var _ => fun h => h
  | .func s ts => fun h => by
      cases h with
      | inl he => exact cst_ne_shift n s he.symm
      | inr ht => exact not_occurs_shiftTerms n ts ht

theorem not_occurs_shiftTerms (n : Nat) : ∀ ts : List Term,
    Not (occursTerms (cst n) (renameTerms shift ts))
  | [] => fun h => h
  | t :: ts => fun h => by
      cases h with
      | inl ht => exact not_occurs_shiftTerm n t ht
      | inr hts => exact not_occurs_shiftTerms n ts hts
end

theorem not_occurs_shiftFormula (n : Nat) : ∀ f : Formula,
    Not (occursFormula (cst n) (renameFormula shift f)) := by
  intro f
  induction f with
  | bottom => exact fun h => h
  | atom _ ts => exact not_occurs_shiftTerms n ts
  | eq t u => exact fun h => h.elim (not_occurs_shiftTerm n t) (not_occurs_shiftTerm n u)
  | impl _ _ iha ihb => exact fun h => h.elim iha ihb
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun h => h.elim iha ihb
  | or _ _ iha ihb => exact fun h => h.elim iha ihb
  | ex _ ih => exact ih

-- ===== Fresh0 §4 =====
mutual
theorem cst_bound_term : ∀ t : Term, ∃ N, ∀ m, N ≤ m → Not (occursTerm (cst m) t)
  | .var _ => ⟨0, fun _ _ h => h⟩
  | .func s ts => by
      obtain ⟨N1, h1⟩ := cst_bound_sym s
      obtain ⟨N2, h2⟩ := cst_bound_terms ts
      refine ⟨max N1 N2, fun m hm h => ?_⟩
      cases h with
      | inl he => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm) he.symm
      | inr ht => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) ht

theorem cst_bound_terms : ∀ ts : List Term, ∃ N, ∀ m, N ≤ m → Not (occursTerms (cst m) ts)
  | [] => ⟨0, fun _ _ h => h⟩
  | t :: ts => by
      obtain ⟨N1, h1⟩ := cst_bound_term t
      obtain ⟨N2, h2⟩ := cst_bound_terms ts
      refine ⟨max N1 N2, fun m hm h => ?_⟩
      cases h with
      | inl ht => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm) ht
      | inr hts => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) hts
end

theorem bound_pair {P Q : Nat → Prop} {N1 N2 : Nat}
    (h1 : ∀ m, N1 ≤ m → Not (P m)) (h2 : ∀ m, N2 ≤ m → Not (Q m)) :
    ∀ m, max N1 N2 ≤ m → Not (Or (P m) (Q m)) := fun m hm h =>
  h.elim (h1 m (Nat.le_trans (Nat.le_max_left _ _) hm))
         (h2 m (Nat.le_trans (Nat.le_max_right _ _) hm))

theorem cst_bound_formula : ∀ f : Formula, ∃ N, ∀ m, N ≤ m → Not (occursFormula (cst m) f) := by
  intro f
  induction f with
  | bottom => exact ⟨0, fun _ _ h => h⟩
  | atom _ ts => exact cst_bound_terms ts
  | eq t u =>
      obtain ⟨_, h1⟩ := cst_bound_term t
      obtain ⟨_, h2⟩ := cst_bound_term u
      exact ⟨_, bound_pair h1 h2⟩
  | impl _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | «forall» _ ih => exact ih
  | and _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | or _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | ex _ ih => exact ih

theorem cst_bound_list : ∀ l : List Formula,
    ∃ N, ∀ m, N ≤ m → ∀ f, f ∈ l → Not (occursFormula (cst m) f)
  | [] => ⟨0, fun _ _ _ hf => absurd hf List.not_mem_nil⟩
  | g :: l => by
      obtain ⟨N1, h1⟩ := cst_bound_formula g
      obtain ⟨N2, h2⟩ := cst_bound_list l
      refine ⟨max N1 N2, fun m hm f hf => ?_⟩
      cases hf with
      | head => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm)
      | tail _ hf' => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) f hf'

-- ===== Fresh0 §5–§6 =====
theorem shiftTheory_fresh {S : Formula → Prop} (n : Nat) :
    ∀ g, shiftTheory S g → Not (occursFormula (cst n) g) := by
  intro g hg hocc
  obtain ⟨h, _, he⟩ := hg
  exact not_occurs_shiftFormula n h (he ▸ hocc)

theorem exists_fresh (S : Formula → Prop) (extra : List Formula) (A : Formula) :
    ∃ c : String, And (∀ g, shiftTheory S g → Not (occursFormula c g))
      (And (∀ g, g ∈ extra → Not (occursFormula c g)) (Not (occursFormula c A))) := by
  obtain ⟨N1, h1⟩ := cst_bound_list extra
  obtain ⟨N2, h2⟩ := cst_bound_formula A
  refine ⟨cst (max N1 N2), shiftTheory_fresh _, ?_, ?_⟩
  · exact h1 _ (Nat.le_max_left _ _)
  · exact h2 _ (Nat.le_max_right _ _)

@[reducible] def instFreshSymString : FOL.FreshSym String where
  shift := shift
  cst := cst
  shift_inj := shift_inj
  cst_inj := cst_inj
  cst_ne_shift := cst_ne_shift

-- ===== Enumeration capas 2–4 =====
section Enum
open FOL.Metamath.Enumeration (natToString natToTerm natToTerms termSize termsSize
  natToFormula formulaSize unpair_surj)

@[reducible] def instEnumSymString : FOL.EnumSym String where
  enum := natToString
  enum_surj := natToString_surj

theorem term_surj_aux : ∀ N : Nat,
    (∀ t : Term, termSize t < N → ∃ n, natToTerm n = t) ∧
    (∀ ts : List Term, termsSize ts < N → ∃ n, natToTerms n = ts) := by
  intro N
  induction N with
  | zero =>
      exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih =>
      obtain ⟨ihT, ihTs⟩ := ih
      constructor
      · intro t hlt
        cases t with
        | var k =>
            obtain ⟨m, hm⟩ := unpair_surj 0 k
            exact ⟨m + 1, by simp [natToTerm, hm]⟩
        | func f ts =>
            have hts : termsSize ts < N := by simp only [termSize] at hlt; omega
            obtain ⟨nts, hnts⟩ := ihTs ts hts
            obtain ⟨nf, hnf⟩ := natToString_surj f
            obtain ⟨r, hr⟩ := unpair_surj nf nts
            obtain ⟨m, hm⟩ := unpair_surj 1 r
            exact ⟨m + 1, by simp [natToTerm, hm, hr, hnf, hnts]⟩
      · intro ts hlt
        cases ts with
        | nil => exact ⟨0, by simp [natToTerms]⟩
        | cons t ts' =>
            have h1 : termSize t < N := by simp only [termsSize] at hlt; omega
            have h2 : termsSize ts' < N := by simp only [termsSize] at hlt; omega
            obtain ⟨a, ha⟩ := ihT t h1
            obtain ⟨b, hb⟩ := ihTs ts' h2
            obtain ⟨m, hm⟩ := unpair_surj a b
            exact ⟨m + 1, by simp [natToTerms, hm, ha, hb]⟩

theorem natToTerm_surj (t : Term) : ∃ n, natToTerm n = t :=
  (term_surj_aux (termSize t + 1)).1 t (by omega)

theorem natToTerms_surj (ts : List Term) : ∃ n, natToTerms n = ts :=
  (term_surj_aux (termsSize ts + 1)).2 ts (by omega)

theorem formula_surj_aux :
    ∀ N : Nat, ∀ f : Formula, formulaSize f < N → ∃ n, natToFormula n = f := by
  intro N
  induction N with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro f hlt
      cases f with
      | bottom => exact ⟨0, by simp [natToFormula]⟩
      | atom p ts =>
          obtain ⟨np, hnp⟩ := natToString_surj p
          obtain ⟨nts, hnts⟩ := natToTerms_surj ts
          obtain ⟨r, hr⟩ := unpair_surj np nts
          obtain ⟨m, hm⟩ := unpair_surj 1 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, hnp, hnts]⟩
      | eq t1 t2 =>
          obtain ⟨n1, h1⟩ := natToTerm_surj t1
          obtain ⟨n2, h2⟩ := natToTerm_surj t2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 2 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | impl f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 3 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | «forall» f1 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨m, hm⟩ := unpair_surj 4 n1
          exact ⟨m + 1, by simp [natToFormula, hm, h1]⟩
      | and f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 5 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | or f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 6 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | ex f1 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨m, hm⟩ := unpair_surj 7 n1
          exact ⟨m + 1, by simp [natToFormula, hm, h1]⟩

theorem natToFormula_surj (f : Formula) : ∃ n, natToFormula n = f :=
  formula_surj_aux (formulaSize f + 1) f (by omega)
end Enum

-- ===== Compacity0 §3 =====
section Comp
open FOL.Compacity0 (updateCsts evalFormula_updateCsts HasLargeModels infTheory neqAx)
open FOL.Metamath.Semantics
open FOL.Skolem0
open FOL.Canonical0 (IsSatisfiable)

theorem evalTerm_updateCsts {D : Type} (M : Model D) (e : Nat → D) (v : Nat → D) :
    ∀ n i, i < n → evalTerm (updateCsts M e n) v (Term.func (cst i) []) = e i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
      show (if cst i = cst n then e n else (updateCsts M e n).func (cst i) []) = e i
      by_cases hin : i = n
      · subst hin; rw [if_pos rfl]
      · rw [if_neg (fun h' => hin (cst_inj i n h'))]
        exact evalTerm_updateCsts M e v n i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

theorem infTheory_finSat {S : Formula → Prop}
    (hFresh : ∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) (hLarge : HasLargeModels S) :
    ∀ Γ : List Formula, (∀ f, f ∈ Γ → infTheory S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  intro Γ hΓ
  obtain ⟨N, hN⟩ := cst_bound_list Γ
  obtain ⟨D, M, v, hM, e, he⟩ := hLarge N
  refine ⟨D, updateCsts M e N, v, fun f hf => ?_⟩
  rcases hΓ f hf with hS | ⟨i, j, hij, rfl⟩
  · exact (evalFormula_updateCsts M e f v (hFresh f hS) N).mpr (hM f hS)
  · have hiN : i < N := Nat.lt_of_not_le (fun hle =>
      hN i hle (neqAx i j) hf (Or.inl (Or.inl (Or.inl rfl))))
    have hjN : j < N := Nat.lt_of_not_le (fun hle =>
      hN j hle (neqAx i j) hf (Or.inl (Or.inr (Or.inl rfl))))
    show evalTerm (updateCsts M e N) v (Term.func (cst i) [])
        = evalTerm (updateCsts M e N) v (Term.func (cst j) []) → False
    intro hEq
    exact hij (he i j hiN hjN ((evalTerm_updateCsts M e v N i hiN).symm.trans
      (hEq.trans (evalTerm_updateCsts M e v N j hjN))))
end Comp

end Exp

-- los 9 titulares que el grafo predice libres
#print axioms Exp.evalTerm_updateCsts
#print axioms Exp.infTheory_finSat
#print axioms Exp.cst_bound_formula
#print axioms Exp.cst_bound_sym
#print axioms Exp.exists_fresh
#print axioms Exp.instFreshSymString
#print axioms Exp.instEnumSymString
#print axioms Exp.natToFormula_surj
#print axioms Exp.natToString_surj
-- intermedios
#print axioms Exp.cst_inj
#print axioms Exp.cst_bound_list
#print axioms Exp.shiftTheory_fresh
#print axioms Exp.natToTerms_surj
-- las piezas de FOL que se reutilizan tal cual (control: deben ser sin choice)
#print axioms FOL.Fresh0.cst
#print axioms FOL.Fresh0.shift
#print axioms FOL.Metamath.Enumeration.natToFormula
#print axioms FOL.Compacity0.evalFormula_updateCsts
#print axioms FOL.Compacity0.updateCsts
-- los originales, para contraste
#print axioms FOL.Fresh0.exists_fresh
#print axioms FOL.Metamath.Enumeration.natToFormula_surj
#print axioms FOL.Compacity0.infTheory_finSat
