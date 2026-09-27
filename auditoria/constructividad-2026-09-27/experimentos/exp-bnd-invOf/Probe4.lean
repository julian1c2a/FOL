import FOL.Fresh0
#print axioms ByteArray.extract_append_eq_right
#print axioms ByteArray.extract_append_eq_left
#print axioms ByteArray.extract_append_size_add'
#print axioms ByteArray.extract_zero_size
#print axioms ByteArray.extract_eq_extract_append_extract
#print axioms ByteArray.append_right_inj
#print axioms ByteArray.append_inj_left
#print axioms ByteArray.isValidUTF8_utf8Encode_singleton_append_iff
#print axioms ByteArray.validateUTF8_eq_true_iff
#print axioms ByteArray.validateUTF8
#print axioms ByteArray.instDecidableIsValidUTF8
#print axioms String.size_toByteArray
#print axioms String.toByteArray_inj
#check @String.toByteArray_inj
#print axioms ByteArray.size_append
#print axioms ByteArray.ext
example (b : ByteArray) : Decidable b.IsValidUTF8 := inferInstance
#synth (∀ b : ByteArray, Decidable b.IsValidUTF8)
