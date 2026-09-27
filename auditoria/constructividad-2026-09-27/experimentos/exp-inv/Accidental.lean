import FOL.Henkin0
import FOL.DecEq
import FOL.Theorems.Eq
import FOL.Fresh0
import FOL.Canonical0

/-! Experimento de auditoría (SOLO LECTURA sobre FOL): ¿qué `Classical.choice` de FOL es
ACCIDENTAL? Cada variante reproduce un enunciado del árbol con otra prueba, en `namespace Exp`. -/

-- ── 0 · las fuentes externas, medidas
#print axioms String.toList
#print axioms String.ofList_toList
#print axioms String.instOrd
#print axioms String.instLawfulEqOrd
#print axioms String.append_right_inj
#print axioms String.length_append
#print axioms Nat.left_eq_add
#print axioms Nat.add_eq_left
#print axioms Classical.propDecidable
#print axioms Exists.choose

namespace Exp
open FOL FOL.Henkin0 FOL.Eigenvariable FOL.Lift0

-- ── 1 · `Canonical0.derives0_em`, por CONSTRUCTORES (el árbol la saca de `completeness₀`)
theorem derives0_em (A : Formula) : [] ⊢₀ Formula.or A (neg A) := by
  let E := Formula.or A (neg A)
  have h1 : [A, neg E] ⊢₀ E := Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
  have h2 : [A, neg E] ⊢₀ neg E := Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have h3 : [A, neg E] ⊢₀ Formula.bottom := Derives₀.elim_impl _ _ _ h2 h1
  have h4 : [neg E] ⊢₀ neg A := Derives₀.intro_impl _ _ _ h3
  have h5 : [neg E] ⊢₀ E := Derives₀.intro_or_r _ _ _ h4
  have h6 : [neg E] ⊢₀ Formula.bottom :=
    Derives₀.elim_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)) h5
  exact Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ h6)

-- ── 2 · `Henkin0.henkin_step_consistent₀` con el `DecidableEq Formula` de `FOL.DecEq`
--       (misma prueba, SIN `open Classical`)
theorem henkin_step_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S)
    (c : String) (A : Formula)
    (hcS : ∀ g, S g → Not (occursFormula c g)) (hcA : Not (occursFormula c A)) :
    IsConsistent₀ (fun x => Or (S x) (x = henkinAx c A)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  have hΓ' : ∀ g, g ∈ Γ.filter (fun x => decide (Not (x = henkinAx c A))) → S g := by
    intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  have hsub : ∀ x, x ∈ Γ → x ∈ henkinAx c A :: Γ.filter (fun y => decide (Not (y = henkinAx c A))) := by
    intro x hx
    by_cases heq : x = henkinAx c A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)
  have hnH : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ neg (henkinAx c A) :=
    Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  have hex : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.ex A :=
    neg_impl_left hnH
  have hnq : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀
      neg (substFormula 0 (Term.func c []) A) := neg_impl_right hnH
  have hfresh : ∀ g, g ∈ Γ.filter (fun y => decide (Not (y = henkinAx c A))) →
      Not (occursFormula c g) := fun g hg => hcS g (hΓ' g hg)
  have hall : (Γ.filter (fun y => decide (Not (y = henkinAx c A)))) ⊢₀ Formula.forall (neg A) := by
    have h := derives0_gen_fresh c hfresh hnq
    rwa [abs_neg_witness c A hcA] at h
  exact hCons ⟨_, hΓ', derives0_ex_forall_neg_absurd hex hall⟩

-- ── 3 · `Lindenbaum0.derivesSet0_intro_impl` con el mismo `DecidableEq`
theorem derivesSet0_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : DerivesSet₀ (fun x => Or (S x) (x = A)) B) : DerivesSet₀ S (Formula.impl A B) := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ.filter (fun y => decide (Not (y = A))), ?_, ?_⟩
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  · refine Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD ?_)
    intro x hx
    by_cases heq : x = A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)

-- ── 4 · `Theorems.Eq.substTerm_subst_comm_succ` sin los lemas `simp` aritméticos del núcleo
mutual
theorem substTerm_subst_comm_succ (u : Term) (a b : Term) (j : Nat) :
    substTerm (j+1) a (substTerm j b u)
      = substTerm j (substTerm (j+1) a b) (substTerm (j+2) (liftTerm j a) u) := by
  cases u with
  | var k =>
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega,
          show ¬ k > j from by omega,
          show ¬ k = j+1 from by omega, show ¬ k > j+1 from by omega,
          show ¬ k = j+2 from by omega, show ¬ k > j+2 from by omega]
      · subst heq
        simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = k+2 from by omega,
          show ¬ k > k+2 from by omega]
      · rcases Nat.lt_trichotomy k (j+2) with h2 | h2 | h2
        · have hk : k = j+1 := by omega
          subst hk
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+1 = j from by omega,
            show j+1 > j from by omega,
            show ¬ j+1 = j+2 from by omega, show ¬ j+1 > j+2 from by omega,
            show ¬ j = j+1 from by omega, show ¬ j > j+1 from by omega]
        · subst h2
          simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ j+2 = j from by omega,
            show j+2 > j from by omega,
            show j+2 = j+2 from rfl, substTerm_liftTerm]
        · simp [-Nat.left_eq_add, -Nat.add_eq_left, substTerm, show ¬ k = j from by omega,
            show k > j from hgt,
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

-- ── 5 · `Fresh0.cst_zero_ne` por LONGITUD, sin `LawfulBEq String`
theorem cst_zero_ne (n : Nat) : FOL.Fresh0.cst 0 ≠ FOL.Fresh0.cst (n + 1) := by
  intro h
  have hl := congrArg String.length h
  simp only [FOL.Fresh0.cst, String.length_append] at hl
  have : (FOL.Fresh0.cst n).length + 1 ≥ 1 := Nat.le_add_left 1 _
  revert hl
  generalize (FOL.Fresh0.cst n).length = m
  intro hl
  have h1 : "g".length = 1 := rfl
  have h2 : "a".length = 1 := rfl
  rw [h1, h2] at hl
  omega

end Exp

#print axioms Exp.derives0_em
#print axioms FOL.Canonical0.derives0_em
#print axioms Exp.henkin_step_consistent₀
#print axioms FOL.Henkin0.henkin_step_consistent₀
#print axioms Exp.derivesSet0_intro_impl
#print axioms FOL.Lindenbaum0.derivesSet0_intro_impl
#print axioms Exp.substTerm_subst_comm_succ
#print axioms FOL.substTerm_subst_comm_succ
#print axioms Exp.cst_zero_ne
#print axioms FOL.Fresh0.cst_zero_ne
