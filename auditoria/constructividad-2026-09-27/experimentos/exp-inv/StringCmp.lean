import FOL.Fresh0
set_option pp.explicit true in
#print FOL.Fresh0.cst_zero_ne
def Exp.lb : LawfulBEq String := inferInstance
#print axioms Exp.lb
#print axioms String.decEq
#print axioms String.instTransOrd
#print axioms FOL.Fresh0.shift_inj
#print axioms FOL.Fresh0.cst_bound_sym
