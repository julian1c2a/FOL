import FOL.Fresh0

#print axioms String.append_right_inj
#print axioms String.utf8ByteSize
#print axioms String.utf8ByteSize_append
#print axioms String.length
#print axioms String.length_append
#print axioms String.toList
#print axioms String.drop
#print axioms String.startsWith
#print axioms String.fromUTF8?
#print axioms ByteArray.extract
#print axioms FOL.Fresh0.shift_inj
#print axioms FOL.Fresh0.cst_inj
#print axioms FOL.Fresh0.cst_zero_ne
#print axioms FOL.Fresh0.cst_ne_shift
#print axioms FOL.Fresh0.not_occurs_shiftFormula
#print axioms FOL.Fresh0.shiftTheory_fresh
#print axioms FOL.Fresh0.cst_bound_sym
#print axioms FOL.Fresh0.cst_bound_formula
#print axioms FOL.Rename.derives0_rename
#print axioms FOL.Rename.derives0_rename_inv
#print axioms FOL.Rename.rename_rename_formula
#print axioms List.find?
#print axioms List.find?_some
#print axioms List.mem_of_find?_eq_some
#print axioms List.find?_eq_none
#check @String.utf8ByteSize_append
#check @String.length_append
example : "g".utf8ByteSize = 1 := rfl
example : "a".utf8ByteSize = 1 := by decide
