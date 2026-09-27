import FOL.Canonical0
open FOL

/-! (3) `derives0_em` / `derives0_peirce` SIN completitud, en el contexto de `FOL.Canonical0`
    (sin importar `FOL.Propositional0`): pruebas sintácticas en Derives₀ puro. -/
namespace Exp

theorem derives0_em (A : Formula) : [] ⊢₀ Formula.or A (neg A) := by
  refine Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_)
  have hn : [neg (Formula.or A (neg A))] ⊢₀ neg A := by
    refine Derives₀.intro_impl _ _ _ ?_
    refine Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom ?_ ?_
    · exact Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    · exact Derives₀.intro_or_l _ A (neg A) (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom
    (Derives₀.hyp _ _ (List.Mem.head _))
    (Derives₀.intro_or_r _ A (neg A) hn)

theorem derives0_peirce (A B : Formula) :
    [] ⊢₀ Formula.impl (Formula.impl (Formula.impl A B) A) A := by
  refine Derives₀.intro_impl _ _ _ (Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_))
  have hA : (neg A :: [Formula.impl (Formula.impl A B) A]) ⊢₀ A := by
    refine Derives₀.elim_impl _ (Formula.impl A B) A
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
    refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
    exact Derives₀.elim_impl _ A Formula.bottom
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ A Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _)) hA

/-- Mismo enunciado que `FOL.Canonical0.derives0_em`: comprobación de tipos. -/
example : @Exp.derives0_em = @FOL.Canonical0.derives0_em := rfl
example : @Exp.derives0_peirce = @FOL.Canonical0.derives0_peirce := rfl

end Exp

#print axioms FOL.Canonical0.derives0_em
#print axioms FOL.Canonical0.derives0_peirce
#print axioms FOL.Canonical0.completeness₀
#print axioms Exp.derives0_em
#print axioms Exp.derives0_peirce
