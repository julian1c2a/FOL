/-
E5 · (c) ¿Hace falta `quotientOut` (Classical.choose de un representante) para el modelo canónico?
Variante: `func`/`rel` se definen con `Quot.lift` sobre `listQuot : List (Quotient s) → Quot (Pw s.r)`,
que se construye por recursión sobre la lista (elección FINITA, sin axioma). Se reprueba
`evalTerm_canonical` y el LEMA DE LA VERDAD entero con el modelo nuevo.
-/
import FOL.Canonical0

namespace Exp

open FOL.Metamath.Semantics

-- ═══ §1 · Genérico: levantar funciones n‑arias a un cociente, sin elegir ═══════════════
inductive Pw {α : Type} (r : α → α → Prop) : List α → List α → Prop
  | nil : Pw r [] []
  | cons {a b : α} {as bs : List α} : r a b → Pw r as bs → Pw r (a :: as) (b :: bs)

theorem Pw.rfl' {α : Type} {r : α → α → Prop} (hr : ∀ a, r a a) : ∀ l : List α, Pw r l l
  | [] => Pw.nil
  | a :: l => Pw.cons (hr a) (Pw.rfl' hr l)

def consQ {α : Type} (s : Setoid α) (a : α) : Quot (Pw s.r) → Quot (Pw s.r) :=
  Quot.lift (fun as => Quot.mk (Pw s.r) (a :: as))
    (fun _ _ h => Quot.sound (Pw.cons (Setoid.refl a) h))

theorem consQ_resp {α : Type} (s : Setoid α) (a b : α) (hab : s.r a b) (L : Quot (Pw s.r)) :
    consQ s a L = consQ s b L :=
  Quot.ind (β := fun L => consQ s a L = consQ s b L)
    (fun as => Quot.sound (Pw.cons hab (Pw.rfl' (fun x => Setoid.refl x) as))) L

def listQuot {α : Type} (s : Setoid α) : List (Quotient s) → Quot (Pw s.r)
  | [] => Quot.mk _ []
  | q :: qs => Quotient.lift (fun a => consQ s a (listQuot s qs))
      (fun a b hab => consQ_resp s a b hab _) q

theorem listQuot_mk {α : Type} (s : Setoid α) : ∀ ts : List α,
    listQuot s (ts.map (Quotient.mk s)) = Quot.mk _ ts
  | [] => rfl
  | t :: ts => by
      show consQ s t (listQuot s (ts.map (Quotient.mk s))) = _
      rw [listQuot_mk s ts]
      rfl

-- ═══ §2 · El modelo de términos sobre un setoide congruente cualquiera ═══════════════════
section Gen
variable (s : Setoid Term)
  (hF : ∀ (f : String) (a b : List Term), Pw s.r a b → s.r (Term.func f a) (Term.func f b))
  (R : String → List Term → Prop)
  (hR : ∀ (p : String) (a b : List Term), Pw s.r a b → (R p a ↔ R p b))

def canonG : Model (Quotient s) where
  func := fun f qs => Quot.lift (fun ts => Quotient.mk s (Term.func f ts))
    (fun a b h => Quotient.sound (hF f a b h)) (listQuot s qs)
  rel := fun p qs => Quot.lift (R p) (fun a b h => propext (hR p a b h)) (listQuot s qs)

def envG : Nat → Quotient s := fun n => Quotient.mk s (Term.var n)

mutual
theorem evalTerm_G (t : Term) : evalTerm (canonG s hF R hR) (envG s) t = Quotient.mk s t := by
  cases t with
  | var n => rfl
  | func f ts =>
    show Quot.lift _ _ (listQuot s (evalTerms (canonG s hF R hR) (envG s) ts)) = _
    rw [evalTerms_G ts, listQuot_mk]
theorem evalTerms_G (ts : List Term) :
    evalTerms (canonG s hF R hR) (envG s) ts = ts.map (Quotient.mk s) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    show evalTerm _ _ t :: evalTerms _ _ ts' = _
    rw [evalTerm_G t, evalTerms_G ts']
    rfl
end

theorem evalAtom_G (p : String) (ts : List Term) :
    evalFormula (canonG s hF R hR) (envG s) (Formula.atom p ts) ↔ R p ts := by
  show Quot.lift _ _ (listQuot s (evalTerms (canonG s hF R hR) (envG s) ts)) ↔ _
  rw [evalTerms_G, listQuot_mk]
end Gen

-- ═══ §3 · Instanciado en el setoide REAL de `Canonical0`, y el lema de la verdad ═══════════
open FOL.Henkin0 (IsConsistent₀)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ IsHenkin max_cons_bot)
open FOL.Canonical0
open FOL.Complexity

theorem pw_pointwise {S : Formula → Prop} {hMax : IsMaximalConsistent₀ S} {a b : List Term}
    (h : Pw (termSetoid S hMax).r a b) : PointwiseEqv S a b := by
  induction h with
  | nil => exact PointwiseEqv.nil
  | cons hab _ ih => exact PointwiseEqv.cons hab ih

/-- ⭐ El modelo canónico SIN `quotientOut`, y ⚠️ sin `noncomputable`. -/
def canonicalModel' (S : Formula → Prop) (hMax : IsMaximalConsistent₀ S) :
    Model (Quotient (termSetoid S hMax)) :=
  canonG (termSetoid S hMax) (fun f _ _ h => termEqv_func_congr hMax f (pw_pointwise h))
    (fun p ts => S (Formula.atom p ts)) (fun p _ _ h => termEqv_rel_congr hMax p (pw_pointwise h))

theorem truth_lemma_lt' {S : Formula → Prop} (hMax : IsMaximalConsistent₀ S)
    (hHenkin : IsHenkin S) (n : Nat) : ∀ f, formulaComplexity f < n →
    (evalFormula (canonicalModel' S hMax) (envG (termSetoid S hMax)) f ↔ S f) := by
  have hT : ∀ t, evalTerm (canonicalModel' S hMax) (envG (termSetoid S hMax)) t
      = Quotient.mk (termSetoid S hMax) t := evalTerm_G (termSetoid S hMax)
    (fun f _ _ h => termEqv_func_congr hMax f (pw_pointwise h))
    (fun p ts => S (Formula.atom p ts)) (fun p _ _ h => termEqv_rel_congr hMax p (pw_pointwise h))
  have hA : ∀ p ts, evalFormula (canonicalModel' S hMax) (envG (termSetoid S hMax))
      (Formula.atom p ts) ↔ S (Formula.atom p ts) := evalAtom_G (termSetoid S hMax)
    (fun f _ _ h => termEqv_func_congr hMax f (pw_pointwise h))
    (fun p ts => S (Formula.atom p ts)) (fun p _ _ h => termEqv_rel_congr hMax p (pw_pointwise h))
  induction n with
  | zero => intro f hLt; exact absurd hLt (Nat.not_lt_zero _)
  | succ n_ih ih =>
    intro f hLt
    cases f with
    | bottom =>
      simp only [evalFormula]
      exact ⟨fun h => h.elim, max_cons_bot hMax⟩
    | atom p ts => exact hA p ts
    | eq t1 t2 =>
      show evalTerm _ _ t1 = evalTerm _ _ t2 ↔ _
      rw [hT t1, hT t2]
      exact ⟨Quotient.exact (s := termSetoid S hMax), Quotient.sound (s := termSetoid S hMax)⟩
    | impl f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_impl_iff hMax).symm
    | and f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have hLt1 : formulaComplexity f1 < n_ih := by simp only [formulaComplexity] at hLt; omega
      have hLt2 : formulaComplexity f2 < n_ih := by simp only [formulaComplexity] at hLt; omega
      simp only [evalFormula]
      rw [ih f1 hLt1, ih f2 hLt2]
      exact (max_cons_or hMax).symm
    | «forall» f1 =>
      simp only [evalFormula]
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      have h_eq : (∀ d : Quotient (termSetoid S hMax),
            evalFormula (canonicalModel' S hMax) (shiftEnv (envG (termSetoid S hMax)) d) f1)
          ↔ (∀ d : Term, S (substFormula 0 d f1)) := by
        constructor
        · intro h d
          have hSubst := eval_substFormula_zero (canonicalModel' S hMax) (envG (termSetoid S hMax)) d f1
          rw [hT d] at hSubst
          exact (ih (substFormula 0 d f1) (hLtSub d)).mp
            (hSubst.symm.mp (h (Quotient.mk (termSetoid S hMax) d)))
        · intro h d
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel' S hMax) (envG (termSetoid S hMax)) t f1
          rw [hT t] at hSubst
          exact hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr (h t))
      rw [h_eq]
      exact (max_cons_forall hMax hHenkin).symm
    | ex f1 =>
      simp only [evalFormula]
      have hLtSub : ∀ d : Term, formulaComplexity (substFormula 0 d f1) < n_ih := by
        intro d
        rw [complexity_substFormula]
        simp only [formulaComplexity] at hLt
        omega
      have h_eq : (∃ d : Quotient (termSetoid S hMax),
            evalFormula (canonicalModel' S hMax) (shiftEnv (envG (termSetoid S hMax)) d) f1)
          ↔ (∃ t, S (substFormula 0 t f1)) := by
        constructor
        · intro h
          obtain ⟨d, hd⟩ := h
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel' S hMax) (envG (termSetoid S hMax)) t f1
          rw [hT t] at hSubst
          exact ⟨t, (ih (substFormula 0 t f1) (hLtSub t)).mp (hSubst.symm.mp hd)⟩
        · intro h
          obtain ⟨t, ht⟩ := h
          have hSubst := eval_substFormula_zero (canonicalModel' S hMax) (envG (termSetoid S hMax)) t f1
          rw [hT t] at hSubst
          exact ⟨Quotient.mk (termSetoid S hMax) t,
                 hSubst.mp ((ih (substFormula 0 t f1) (hLtSub t)).mpr ht)⟩
      rw [h_eq]
      exact (max_cons_ex hMax hHenkin).symm

end Exp

#print axioms Exp.listQuot
#print axioms Exp.listQuot_mk
#print axioms Exp.canonG
#print axioms Exp.evalTerm_G
#print axioms Exp.evalAtom_G
#print axioms Exp.canonicalModel'
#print axioms Exp.truth_lemma_lt'
