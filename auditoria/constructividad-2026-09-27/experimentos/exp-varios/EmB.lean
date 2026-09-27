import FOL.Canonical0
import FOL.Propositional0
open FOL
namespace ExpB
theorem derives0_em (A : Formula) : [] ⊢₀ Formula.or A (neg A) := FOL.Propositional0.derives0_em_ctx [] A
theorem derives0_peirce (A B : Formula) :
    [] ⊢₀ Formula.impl (Formula.impl (Formula.impl A B) A) A := FOL.Propositional0.derives0_peirce_prop A B
end ExpB
#print axioms FOL.Propositional0.derives0_em_ctx
#print axioms FOL.Propositional0.derives0_em_prop
#print axioms FOL.Propositional0.derives0_peirce_prop
#print axioms ExpB.derives0_em
#print axioms ExpB.derives0_peirce
