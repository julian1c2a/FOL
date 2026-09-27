import FOL.Lindenbaum0

/-! E5 · ¿El `Classical.choice` de `lindenbaum_step_subset` / `lindenbaum_step_consistent` es SÓLO
el de `LindenbaumStep`? Variante con la decisión de `IsConsistent₀` como PARÁMETRO (oráculo
`[∀ T, Decidable (IsConsistent₀ T)]`), sin `open Classical`, y las mismas pruebas. -/

namespace Exp
open FOL.Henkin0
open FOL.Lindenbaum0
open FOL.Metamath.Enumeration

variable [dec : ∀ T : Formula → Prop, Decidable (IsConsistent₀ T)]

def LindenbaumStepO (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 =>
    if IsConsistent₀ (fun x => Or (LindenbaumStepO S n x) (x = natToFormula n)) then
      fun x => Or (LindenbaumStepO S n x) (x = natToFormula n)
    else LindenbaumStepO S n

theorem lindenbaum_step_consistentO {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (LindenbaumStepO S n)
  | 0 => hCons
  | n + 1 => by
      simp only [LindenbaumStepO]
      by_cases h : IsConsistent₀ (fun x => Or (LindenbaumStepO S n x) (x = natToFormula n))
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact lindenbaum_step_consistentO hCons n

theorem lindenbaum_step_subsetO {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStepO S n x) : LindenbaumStepO S (n + 1) x := by
  simp only [LindenbaumStepO]
  by_cases hC : IsConsistent₀ (fun y => Or (LindenbaumStepO S n y) (y = natToFormula n))
  · rw [if_pos hC]; exact Or.inl h
  · rw [if_neg hC]; exact h

end Exp

#print axioms FOL.Lindenbaum0.LindenbaumStep
#print axioms FOL.Lindenbaum0.lindenbaum_step_subset
#print axioms FOL.Lindenbaum0.lindenbaum_step_consistent
#print axioms Exp.LindenbaumStepO
#print axioms Exp.lindenbaum_step_subsetO
#print axioms Exp.lindenbaum_step_consistentO
-- el oráculo instanciado con la decisión clásica: vuelve el choice
open FOL.Metamath.Enumeration in
theorem Exp.subset_classical {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : @Exp.LindenbaumStepO (fun _ => Classical.propDecidable _) S n x) :
    @Exp.LindenbaumStepO (fun _ => Classical.propDecidable _) S (n + 1) x :=
  @Exp.lindenbaum_step_subsetO (fun _ => Classical.propDecidable _) S n x h
#print axioms Exp.subset_classical
