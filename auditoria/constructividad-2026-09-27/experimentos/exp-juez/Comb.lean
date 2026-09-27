import FOL.Compacity0
/-! JUEZ · Combinación MEDIDA: variantes String (exp-string/E4, ns ExpS) + ctx_split (exp-deceq/E4, ns ExpD)
  + cota calculada y locInv (exp-bnd-invOf/ExpAll) + Lindenbaum impredicativo (exp-esencial/E4, ns ExpL).
  Objetivo: medir los MISMOS enunciados de henLimit_consistent₀, henLimit_witness, lindenbaum_lemma₀ y
  henkin_completion₀ con todo lo eliminable a la vez. -/

/-! Propagacion MEDIDA: se reconstruyen, sobre las cuatro variantes sin choice, los
titulares que segun el grafo dependen SOLO de las entradas «String». Las pruebas son copia
literal de FOL (Fresh0 §3–§6, Enumeration capas 3–4, Compacity0 §3), cambiando unicamente
el lema de entrada. -/

namespace ExpS
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

end ExpS

/-! E4 · SIN `FOL.DecEq` y SIN `open Classical`: no se decide ninguna igualdad. La hipótesis ya
da, para cada `g ∈ Γ`, la disyunción `S g ∨ g = H`; como la meta es una `Prop` (`False` o un
`∃`), se parte el contexto por inducción sobre `Γ` eliminando esa `Or`. -/

namespace ExpD
open FOL.Eigenvariable
open FOL.Lift0
open FOL.Henkin0
open FOL.Lindenbaum0

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

/-- Partir un contexto finito sin decidir la igualdad. -/
theorem ctx_split {S : Formula → Prop} {H : Formula} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → Or (S g) (g = H)) →
    ∃ Γ' : List Formula, And (∀ g, g ∈ Γ' → S g) (∀ x, x ∈ Γ → x ∈ H :: Γ')
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨Γ', hS, hsub⟩ := ctx_split Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      cases hΓ g (List.Mem.head _) with
      | inl hg =>
        refine ⟨g :: Γ', ?_, ?_⟩
        · intro x hx
          cases hx with
          | head => exact hg
          | tail _ hx => exact hS x hx
        · intro x hx
          cases hx with
          | head => exact List.Mem.tail _ (List.Mem.head _)
          | tail _ hx =>
            cases hsub x hx with
            | head => exact List.Mem.head _
            | tail _ h => exact List.Mem.tail _ (List.Mem.tail _ h)
      | inr hg =>
        refine ⟨Γ', hS, ?_⟩
        intro x hx
        cases hx with
        | head => rw [hg]; exact List.Mem.head _
        | tail _ hx => exact hsub x hx

theorem henkin_step_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := henkinAx c A) Γ hΓ
  have hnH : Γ' ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  have hex : Γ' ⊢₀ Formula.ex A := neg_impl_left hnH
  have hnq : Γ' ⊢₀ neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  have hfresh : ∀ g, g ∈ Γ' → Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  have hall : Γ' ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  exact hCons ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => Or (S x) (x = A)) ⊢₀* B) : S ⊢₀* Formula.impl A B := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hΓ', hsub⟩ := ctx_split (H := A) Γ hΓ
  exact ⟨Γ', hΓ', Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)⟩

end ExpD


/-! Combinado: (a) bndC + (b2) locInv + anexo Fresh0 (cst_ne_shift', cst_inj'). -/

namespace ExpF

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0

theorem cst_size : ∀ n : Nat, (cst n).utf8ByteSize = n + 1
  | 0 => rfl
  | n + 1 => by
      show ("a" ++ cst n).utf8ByteSize = n + 1 + 1
      rw [String.utf8ByteSize_append, cst_size n]
      show 1 + (n + 1) = n + 1 + 1
      rw [Nat.add_comm]

/-- `cst_zero_ne` contando bytes (sin `String.instOrd`). -/
theorem cst_zero_ne' (n : Nat) : cst 0 ≠ cst (n + 1) := fun h =>
  absurd ((cst_size 0).symm.trans ((congrArg String.utf8ByteSize h).trans (cst_size (n + 1))))
    (fun h' => Nat.succ_ne_zero n (Nat.succ.inj h').symm)

/-- Dos cadenas de 1 byte distintas no pueden empezar igual. -/
theorem ne_of_head {a b x y : String} (ha : a.toByteArray.size = b.toByteArray.size)
    (hab : a ≠ b) : a ++ x ≠ b ++ y := fun h => by
  have hb : a.toByteArray ++ x.toByteArray = b.toByteArray ++ y.toByteArray := by
    rw [← String.toByteArray_append, ← String.toByteArray_append, h]
  exact hab (String.toByteArray_inj.mp (ByteArray.append_inj_left hb ha))

theorem g_eq : "g" = "g" ++ "" := by decide

/-- ⭐ `cst_ne_shift` sin `not_eq_of_beq_eq_false` (sin `String.instOrd`). -/
theorem cst_ne_shift' : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, s => by
      show "g" ≠ "f" ++ s
      rw [g_eq]
      exact ne_of_head rfl (by decide)
  | n + 1, s => by
      show "a" ++ cst n ≠ "f" ++ s
      exact ne_of_head rfl (by decide)

mutual
theorem not_occurs_shiftTerm' (n : Nat) : ∀ t : Term,
    Not (occursTerm (cst n) (renameTerm shift t))
  | .var _ => fun h => h
  | .func s ts => fun h => by
      cases h with
      | inl he => exact cst_ne_shift' n s he.symm
      | inr ht => exact not_occurs_shiftTerms' n ts ht

theorem not_occurs_shiftTerms' (n : Nat) : ∀ ts : List Term,
    Not (occursTerms (cst n) (renameTerms shift ts))
  | [] => fun h => h
  | t :: ts => fun h => by
      cases h with
      | inl ht => exact not_occurs_shiftTerm' n t ht
      | inr hts => exact not_occurs_shiftTerms' n ts hts
end

theorem not_occurs_shiftFormula' (n : Nat) : ∀ f : Formula,
    Not (occursFormula (cst n) (renameFormula shift f)) := by
  intro f
  induction f with
  | bottom => exact fun h => h
  | atom _ ts => exact not_occurs_shiftTerms' n ts
  | eq t u => exact fun h => h.elim (not_occurs_shiftTerm' n t) (not_occurs_shiftTerm' n u)
  | impl _ _ iha ihb => exact fun h => h.elim iha ihb
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun h => h.elim iha ihb
  | or _ _ iha ihb => exact fun h => h.elim iha ihb
  | ex _ ih => exact ih

theorem shiftTheory_fresh' {S : Formula → Prop} (n : Nat) :
    ∀ g, shiftTheory S g → Not (occursFormula (cst n) g) := by
  intro g hg hocc
  obtain ⟨h, _, he⟩ := hg
  exact not_occurs_shiftFormula' n h (he ▸ hocc)

end ExpF

namespace ExpAll

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0
open FOL.HenkinLimit0
open FOL.Metamath.Enumeration

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- (a) · La cota, calculada
-- ============================================================

/-- ⭐ `cst n` ocupa exactamente `n + 1` bytes. -/
theorem cst_size : ∀ n : Nat, (cst n).utf8ByteSize = n + 1
  | 0 => rfl
  | n + 1 => by
      show ("a" ++ cst n).utf8ByteSize = n + 1 + 1
      rw [String.utf8ByteSize_append, cst_size n]
      show 1 + (n + 1) = n + 1 + 1
      rw [Nat.add_comm]

/-- Una cadena de `k` bytes no es `cst m` para ningún `m ≥ k`. Sin tercio excluso, sin
`cst_inj`: sólo contar bytes. -/
theorem cst_ne_of_size {s : String} {m : Nat} (hm : s.utf8ByteSize ≤ m) : cst m ≠ s := by
  intro h
  have h1 : m + 1 = s.utf8ByteSize := (cst_size m).symm.trans (congrArg String.utf8ByteSize h)
  exact Nat.not_succ_le_self m (Nat.le_trans (Nat.le_of_eq h1) hm)

mutual
def bT : Term → Nat
  | .var _ => 0
  | .func s ts => max s.utf8ByteSize (bTs ts)

def bTs : List Term → Nat
  | [] => 0
  | t :: ts => max (bT t) (bTs ts)
end

/-- ⭐ La cota de §2 de `HenkinLimit0`, **calculada**: el mayor tamaño en bytes de un símbolo de
función de la fórmula. -/
def bndC : Formula → Nat
  | .bottom => 0
  | .atom _ ts => bTs ts
  | .eq t u => max (bT t) (bT u)
  | .impl a b => max (bndC a) (bndC b)
  | .forall a => bndC a
  | .and a b => max (bndC a) (bndC b)
  | .or a b => max (bndC a) (bndC b)
  | .ex a => bndC a

mutual
theorem bT_spec : ∀ (t : Term) (m : Nat), bT t ≤ m → Not (occursTerm (cst m) t)
  | .var _, _, _ => fun h => h
  | .func s ts, m, hm => fun h => by
      cases h with
      | inl he => exact cst_ne_of_size (Nat.le_trans (Nat.le_max_left _ _) hm) he.symm
      | inr ht => exact bTs_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) ht

theorem bTs_spec : ∀ (ts : List Term) (m : Nat), bTs ts ≤ m → Not (occursTerms (cst m) ts)
  | [], _, _ => fun h => h
  | t :: ts, m, hm => fun h => by
      cases h with
      | inl ht => exact bT_spec t m (Nat.le_trans (Nat.le_max_left _ _) hm) ht
      | inr hts => exact bTs_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) hts
end

private theorem pair {P Q : Prop} {a b m : Nat} (h1 : a ≤ m → Not P) (h2 : b ≤ m → Not Q)
    (hm : max a b ≤ m) : Not (Or P Q) := fun h =>
  h.elim (h1 (Nat.le_trans (Nat.le_max_left _ _) hm)) (h2 (Nat.le_trans (Nat.le_max_right _ _) hm))

/-- ⭐⭐ El sustituto de `bnd_spec`, con la cota calculada. -/
theorem bndC_spec : ∀ (f : Formula) (m : Nat), bndC f ≤ m → Not (occursFormula (cst m) f) := by
  intro f
  induction f with
  | bottom => exact fun _ _ h => h
  | atom _ ts => exact bTs_spec ts
  | eq t u => exact fun m hm => pair (bT_spec t m) (bT_spec u m) hm
  | impl _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | or _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | ex _ ih => exact ih

/-- De regalo: `cst_bound_sym` (la entrada de `Fresh0`) sin `by_cases`: la cota es el tamaño. -/
theorem cst_bound_sym' (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.utf8ByteSize, fun _ hm => cst_ne_of_size hm⟩

/-- Y `cst_inj` sin `cst_zero_ne` (sin `String.instOrd`): contar bytes. -/
theorem cst_inj' (m n : Nat) (h : cst m = cst n) : m = n :=
  Nat.succ.inj ((cst_size m).symm.trans ((congrArg String.utf8ByteSize h).trans (cst_size n)))

/-- El índice del testigo, ahora **computable** (sin `noncomputable`). -/
def hidxC : Nat → Nat
  | 0 => bndC (natToFormula 0)
  | n + 1 => max (hidxC n + 1) (bndC (natToFormula (n + 1)))

-- Control de que es de verdad un programa: se evalúa.


-- ============================================================
-- (b2) · La inversa LOCAL de un renombrado inyectivo
-- ============================================================

mutual
def symsT : Term → List String
  | .var _ => []
  | .func s ts => s :: symsTs ts

def symsTs : List Term → List String
  | [] => []
  | t :: ts => symsT t ++ symsTs ts
end

def symsF : Formula → List String
  | .bottom => []
  | .atom _ ts => symsTs ts
  | .eq t u => symsT t ++ symsT u
  | .impl a b => symsF a ++ symsF b
  | .forall a => symsF a
  | .and a b => symsF a ++ symsF b
  | .or a b => symsF a ++ symsF b
  | .ex a => symsF a

def symsL : List Formula → List String
  | [] => []
  | g :: l => symsF g ++ symsL l

theorem symsL_mem : ∀ {l : List Formula} {g : Formula} {s : String},
    g ∈ l → s ∈ symsF g → s ∈ symsL l
  | _ :: _, _, _, .head _, hs => List.mem_append_left _ hs
  | _ :: _, _, _, .tail _ hg, hs => List.mem_append_right _ (symsL_mem hg hs)

/-- La inversa local: busca en la lista FINITA `L` una preimagen por `ρ`. Sólo usa la
igualdad decidible de `String`, que no depende de ningún axioma. -/
def locInv (ρ : String → String) : List String → String → String
  | [], x => x
  | t :: L, x => if ρ t = x then t else locInv ρ L x

theorem locInv_spec {ρ : String → String} (hinj : ∀ s t, ρ s = ρ t → s = t) :
    ∀ {L : List String} {s : String}, s ∈ L → locInv ρ L (ρ s) = s
  | t :: L, s, hs => by
      show (if ρ t = ρ s then t else locInv ρ L (ρ s)) = s
      by_cases h : ρ t = ρ s
      · rw [if_pos h]; exact hinj t s h
      · rw [if_neg h]
        cases hs with
        | head => exact absurd rfl h
        | tail _ hs' => exact locInv_spec hinj hs'

-- La cancelación, LOCAL: basta con que `σ ∘ ρ = id` sobre los símbolos que aparecen.
mutual
theorem rr_term {ρ σ : String → String} : ∀ t : Term,
    (∀ s, s ∈ symsT t → σ (ρ s) = s) → renameTerm σ (renameTerm ρ t) = t
  | .var _, _ => rfl
  | .func s ts, h => by
      show TermG.func (σ (ρ s)) (renameTerms σ (renameTerms ρ ts)) = TermG.func s ts
      rw [h s (List.Mem.head _), rr_terms ts (fun x hx => h x (List.Mem.tail _ hx))]

theorem rr_terms {ρ σ : String → String} : ∀ ts : List Term,
    (∀ s, s ∈ symsTs ts → σ (ρ s) = s) → renameTerms σ (renameTerms ρ ts) = ts
  | [], _ => rfl
  | t :: ts, h => by
      show renameTerm σ (renameTerm ρ t) :: renameTerms σ (renameTerms ρ ts) = t :: ts
      rw [rr_term t (fun x hx => h x (List.mem_append_left _ hx)),
        rr_terms ts (fun x hx => h x (List.mem_append_right _ hx))]
end

theorem rr_formula {ρ σ : String → String} : ∀ f : Formula,
    (∀ s, s ∈ symsF f → σ (ρ s) = s) → renameFormula σ (renameFormula ρ f) = f := by
  intro f
  induction f with
  | bottom => exact fun _ => rfl
  | atom p ts =>
      intro h
      show FormulaG.atom p (renameTerms σ (renameTerms ρ ts)) = FormulaG.atom p ts
      rw [rr_terms ts h]
  | eq t u =>
      intro h
      show FormulaG.eq (renameTerm σ (renameTerm ρ t)) (renameTerm σ (renameTerm ρ u)) = _
      rw [rr_term t (fun x hx => h x (List.mem_append_left _ hx)),
        rr_term u (fun x hx => h x (List.mem_append_right _ hx))]
  | impl a b iha ihb =>
      intro h
      show FormulaG.impl (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | «forall» a ih =>
      intro h
      show FormulaG.forall (renameFormula σ (renameFormula ρ a)) = _
      rw [ih h]
  | and a b iha ihb =>
      intro h
      show FormulaG.and (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | or a b iha ihb =>
      intro h
      show FormulaG.or (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | ex a ih =>
      intro h
      show FormulaG.ex (renameFormula σ (renameFormula ρ a)) = _
      rw [ih h]

theorem map_rr {ρ σ : String → String} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → renameFormula σ (renameFormula ρ g) = g) →
    (Γ.map (renameFormula ρ)).map (renameFormula σ) = Γ
  | [], _ => rfl
  | g :: Γ, h => by
      show renameFormula σ (renameFormula ρ g) :: (Γ.map (renameFormula ρ)).map (renameFormula σ)
        = g :: Γ
      rw [h g (List.Mem.head _), map_rr Γ (fun x hx => h x (List.Mem.tail _ hx))]

/-- ⭐⭐ `derives0_rename_conservative` **sin elección**: la inversa sólo tiene que valer sobre
los símbolos de `Γ` y `f`, que son finitos. -/
theorem derives0_rename_conservative' {ρ : String → String} (hinj : ∀ s t, ρ s = ρ t → s = t)
    {Γ : List Formula} {f : Formula}
    (h : (Γ.map (renameFormula ρ)) ⊢₀ renameFormula ρ f) : Γ ⊢₀ f := by
  have hc : ∀ g, g ∈ f :: Γ → renameFormula (locInv ρ (symsL (f :: Γ))) (renameFormula ρ g) = g :=
    fun g hg => rr_formula g (fun _ hs => locInv_spec hinj (symsL_mem hg hs))
  have h' := derives0_rename (locInv ρ (symsL (f :: Γ))) h
  rwa [map_rr Γ (fun g hg => hc g (List.Mem.tail _ hg)), hc f (List.Mem.head _)] at h'

/-- Las preimágenes de un contexto finito de `shiftTheory S` (eliminación de `∃` en `Prop`,
constructiva). -/
theorem shift_preimages {S : Formula → Prop} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → shiftTheory S g) →
    ∃ Γ' : List Formula, And (∀ y, y ∈ Γ' → S y) (Γ = Γ'.map (renameFormula shift))
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | g :: Γ, h => by
      obtain ⟨y, hy, rfl⟩ := h g (List.Mem.head _)
      obtain ⟨Γ', h1, rfl⟩ := shift_preimages Γ (fun x hx => h x (List.Mem.tail _ hx))
      refine ⟨y :: Γ', fun z hz => ?_, rfl⟩
      cases hz with
      | head => exact hy
      | tail _ hz' => exact h1 z hz'

/-- ⭐⭐ `derivesSet0_shift_inv` **sin `invOf`**. -/
theorem derivesSet0_shift_inv' {S : Formula → Prop} {f : Formula}
    (h : shiftTheory S ⊢₀* renameFormula shift f) : S ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hS, rfl⟩ := shift_preimages Γ hΓ
  exact ⟨Γ', hS, derives0_rename_conservative' shift_inj hD⟩

theorem shiftTheory_consistent₀' {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (shiftTheory S) := fun hbot => hCons (derivesSet0_shift_inv' hbot)

-- ============================================================
-- (a)+(b2) · La iteración ω con las dos variantes
-- ============================================================

theorem hidxC_ge : ∀ n, bndC (natToFormula n) ≤ hidxC n
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

theorem hidxC_step (n : Nat) : hidxC n < hidxC (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)

theorem hidxC_mono : ∀ {i n : Nat}, i < n → hidxC i < hidxC n
  | i, 0, h => absurd h (Nat.not_lt_zero i)
  | i, n + 1, h => by
      cases Nat.lt_or_ge i n with
      | inl hlt => exact Nat.lt_trans (hidxC_mono hlt) (hidxC_step n)
      | inr hge => exact (Nat.le_antisymm (Nat.le_of_lt_succ h) hge) ▸ hidxC_step n

theorem hidxC_ge_of_le {i n : Nat} (h : i ≤ n) : bndC (natToFormula i) ≤ hidxC n := by
  cases Nat.lt_or_ge i n with
  | inl hlt => exact Nat.le_trans (hidxC_ge i) (Nat.le_of_lt (hidxC_mono hlt))
  | inr hge => exact (Nat.le_antisymm h hge) ▸ hidxC_ge i

/-- La cadena, ya **sin `noncomputable`**. -/
def henC (S : Formula → Prop) : Nat → Formula → Prop
  | 0 => shiftTheory S
  | n + 1 => fun x => Or (henC S n x) (x = henkinAx (cst (hidxC n)) (natToFormula n))

theorem henC_mono (S : Formula → Prop) : ∀ {i n : Nat}, i ≤ n → ∀ x, henC S i x → henC S n x
  | _, 0, h, _, hx => (Nat.le_zero.mp h) ▸ hx
  | i, n + 1, h, x, hx => by
      cases Nat.lt_or_ge i (n + 1) with
      | inl hlt => exact Or.inl (henC_mono S (Nat.le_of_lt_succ hlt) x hx)
      | inr hge => exact (Nat.le_antisymm h hge) ▸ hx

theorem henC_fresh (S : Formula → Prop) (m : Nat) : ∀ (n : Nat),
    (∀ i, i < n → m ≠ hidxC i) →
    (∀ i, i < n → Not (occursFormula (cst m) (natToFormula i))) →
    ∀ g, henC S n g → Not (occursFormula (cst m) g)
  | 0, _, _, g, hg => ExpF.shiftTheory_fresh' m g hg
  | n + 1, hne, hfr, g, hg => by
      cases hg with
      | inl h =>
          exact henC_fresh S m n (fun i hi => hne i (Nat.lt_succ_of_lt hi))
            (fun i hi => hfr i (Nat.lt_succ_of_lt hi)) g h
      | inr he =>
          subst he
          refine not_occurs_henkinAx ?_ (hfr n (Nat.lt_succ_self n))
          intro hc
          exact hne n (Nat.lt_succ_self n) (cst_inj' m (hidxC n) hc)

theorem henC_fresh_at (S : Formula → Prop) (n : Nat) :
    ∀ g, henC S n g → Not (occursFormula (cst (hidxC n)) g) :=
  henC_fresh S (hidxC n) n
    (fun _ hi => Nat.ne_of_gt (hidxC_mono hi))
    (fun i hi => bndC_spec (natToFormula i) (hidxC n) (hidxC_ge_of_le (Nat.le_of_lt hi)))

theorem henC_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (henC S n)
  | 0 => shiftTheory_consistent₀' hCons
  | n + 1 =>
      ExpD.henkin_step_consistent₀ (henC_consistent hCons n) (cst (hidxC n)) (natToFormula n)
        (henC_fresh_at S n) (bndC_spec (natToFormula n) (hidxC n) (hidxC_ge n))

def henLimitC (S : Formula → Prop) : Formula → Prop := fun x => ∃ n, henC S n x

theorem henLimitC_finite (S : Formula → Prop) : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → henLimitC S g) → ∃ N, ∀ g, g ∈ Γ → henC S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨n, hn⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := henLimitC_finite S Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max n N, fun x hx => ?_⟩
      cases hx with
      | head => exact henC_mono S (Nat.le_max_left _ _) g hn
      | tail _ hx' => exact henC_mono S (Nat.le_max_right _ _) x (hN x hx')

theorem henLimitC_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (henLimitC S) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨N, hN⟩ := henLimitC_finite S Γ hΓ
  exact henC_consistent hCons N ⟨Γ, hN, hD⟩

theorem henLimitC_witness (S : Formula → Prop) (A : Formula) :
    ∃ c : String, henLimitC S (henkinAx c A) := by
  obtain ⟨n, hn⟩ := ExpS.natToFormula_surj A
  exact ⟨cst (hidxC n), n + 1, Or.inr (by rw [hn])⟩

end ExpAll

namespace ExpL

open FOL.Henkin0 (DerivesSet₀ IsConsistent₀ henkinAx)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ IsHenkin derivesSet0_weakening derivesSet0_elim_impl derivesSet0_hyp)
open FOL.Fresh0 (shiftTheory)

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ── Lindenbaum impredicativo (copia literal de exp-esencial/E4_Lindenbaum.lean) ──────────
def Step (e : Nat → Formula) (S : Formula → Prop) : Nat → Formula → Prop
  | 0 => S
  | n + 1 => fun x => Or (Step e S n x)
      (And (x = e n) (IsConsistent₀ (fun y => Or (Step e S n y) (y = e n))))

def Limit (e : Nat → Formula) (S : Formula → Prop) (f : Formula) : Prop := ∃ n, Step e S n f

theorem nn_em (C : Prop) : Not (Not (Or C (Not C))) := fun h => h (Or.inr (fun c => h (Or.inl c)))

theorem step_consistent {e : Nat → Formula} {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (Step e S n)
  | 0 => hCons
  | n + 1 => by
      intro hbot
      apply nn_em (IsConsistent₀ (fun y => Or (Step e S n y) (y = e n)))
      intro hem
      cases hem with
      | inl hC =>
        exact hC (derivesSet0_weakening hbot (fun x hx => hx.elim Or.inl (fun h => Or.inr h.1)))
      | inr hNC =>
        exact step_consistent hCons n
          (derivesSet0_weakening hbot (fun x hx => hx.elim id (fun h => absurd h.2 hNC)))

theorem step_mono {e : Nat → Formula} {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : Step e S n x) : Step e S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact Or.inl ih

theorem limit_bound {e : Nat → Formula} {S : Formula → Prop} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → Limit e S g) → ∃ N, ∀ g, g ∈ Γ → Step e S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨ng, hng⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := limit_bound Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max ng N, fun x hx => ?_⟩
      cases hx with
      | head => exact step_mono (Nat.le_max_left _ _) hng
      | tail _ hx' => exact step_mono (Nat.le_max_right _ _) (hN x hx')

theorem limit_consistent {e : Nat → Formula} {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (Limit e S) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨N, hN⟩ := limit_bound Γ hΓ
  exact step_consistent hCons N ⟨Γ, hN, hD⟩

theorem limit_max (e : Nat → Formula) (he : ∀ f, ∃ n, e n = f)
    {S : Formula → Prop} (hCons : IsConsistent₀ S) : IsMaximalConsistent₀ (Limit e S) := by
  refine ⟨limit_consistent hCons, ?_⟩
  intro f hNot hExt
  obtain ⟨n, hn⟩ := he f
  have hConsN : IsConsistent₀ (fun x => Or (Step e S n x) (x = e n)) := by
    intro hbot
    refine hExt (derivesSet0_weakening hbot ?_)
    intro x hx
    cases hx with
    | inl hS => exact Or.inl ⟨n, hS⟩
    | inr hE => exact Or.inr (hE.trans hn)
  exact hNot ⟨n + 1, Or.inr ⟨hn.symm, hConsN⟩⟩

/-- ⭐ NUEVO (juez): el límite de Lindenbaum está CERRADO por deducción SIN tercio excluso.
(Para un maximal ARBITRARIO esto es `max_cons_contains`, esencial: E3; para ESTE límite, no.) -/
theorem limit_closed (e : Nat → Formula) (he : ∀ f, ∃ n, e n = f)
    {S : Formula → Prop} (hCons : IsConsistent₀ S) {f : Formula} (hD : Limit e S ⊢₀* f) :
    Limit e S f := by
  obtain ⟨n, hn⟩ := he f
  have hConsN : IsConsistent₀ (fun x => Or (Step e S n x) (x = e n)) := by
    intro hbot
    have hI : Step e S n ⊢₀* Formula.impl (e n) Formula.bottom := ExpD.derivesSet0_intro_impl hbot
    have hI' : Limit e S ⊢₀* Formula.impl (e n) Formula.bottom :=
      derivesSet0_weakening hI (fun x hx => ⟨n, hx⟩)
    rw [hn] at hI'
    exact limit_consistent hCons (derivesSet0_elim_impl hI' hD)
  exact ⟨n + 1, Or.inr ⟨hn.symm, hConsN⟩⟩

open FOL.Metamath.Enumeration (natToFormula)

/-- MISMO enunciado que `FOL.Lindenbaum0.lindenbaum_lemma₀`. -/
theorem lindenbaum_lemma_nc {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T) (∀ f, S f → T f) :=
  ⟨Limit natToFormula S, limit_max natToFormula ExpS.natToFormula_surj hCons, fun _ hf => ⟨0, hf⟩⟩

/-- MISMO enunciado que `FOL.Lindenbaum0.henkin_completion₀`. -/
theorem henkin_completion_nc {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∃ T : Formula → Prop, And (IsMaximalConsistent₀ T)
      (And (IsHenkin T) (∀ f, shiftTheory S f → T f)) := by
  have hH := ExpAll.henLimitC_consistent₀ hCons
  refine ⟨Limit natToFormula (ExpAll.henLimitC S),
    limit_max natToFormula ExpS.natToFormula_surj hH, ?_, fun f hf => ⟨0, ⟨0, hf⟩⟩⟩
  intro A hEx
  obtain ⟨c, hc⟩ := ExpAll.henLimitC_witness S A
  refine ⟨Term.func c [], limit_closed natToFormula ExpS.natToFormula_surj hH ?_⟩
  exact derivesSet0_elim_impl (derivesSet0_hyp (S := Limit natToFormula (ExpAll.henLimitC S))
    (f := henkinAx c A) ⟨0, hc⟩) (derivesSet0_hyp hEx)

end ExpL

-- Comprobación de que los enunciados son los MISMOS (por tipo):
example : @ExpL.lindenbaum_lemma_nc = @FOL.Lindenbaum0.lindenbaum_lemma₀ := rfl
example : ∀ {S : Formula → Prop}, FOL.Henkin0.IsConsistent₀ S → ∃ T : Formula → Prop,
    And (FOL.Lindenbaum0.IsMaximalConsistent₀ T)
      (And (FOL.Lindenbaum0.IsHenkin T) (∀ f, FOL.Fresh0.shiftTheory S f → T f)) :=
  @FOL.Lindenbaum0.henkin_completion₀
example : ∀ {S : Formula → Prop}, FOL.Henkin0.IsConsistent₀ S → ∃ T : Formula → Prop,
    And (FOL.Lindenbaum0.IsMaximalConsistent₀ T)
      (And (FOL.Lindenbaum0.IsHenkin T) (∀ f, FOL.Fresh0.shiftTheory S f → T f)) :=
  @ExpL.henkin_completion_nc

#print axioms ExpD.henkin_step_consistent₀
#print axioms ExpD.derivesSet0_intro_impl
#print axioms ExpS.natToFormula_surj
#print axioms ExpAll.henC_fresh_at
#print axioms ExpAll.henC_consistent
#print axioms ExpAll.henLimitC_consistent₀
#print axioms ExpAll.henLimitC_witness
#print axioms ExpAll.shiftTheory_consistent₀'
#print axioms ExpAll.derives0_rename_conservative'
#print axioms ExpL.step_consistent
#print axioms ExpL.limit_max
#print axioms ExpL.limit_closed
#print axioms ExpL.lindenbaum_lemma_nc
#print axioms ExpL.henkin_completion_nc
#print axioms FOL.Lindenbaum0.lindenbaum_lemma₀
#print axioms FOL.Lindenbaum0.henkin_completion₀
#print axioms FOL.HenkinLimit0.henLimit_consistent₀
#print axioms FOL.HenkinLimit0.henLimit_witness
