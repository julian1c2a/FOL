import FOL.Fresh0
open String in
#check @String.bytes
#print axioms String.bytes_append
#check @String.bytes_append
#print axioms String.extract
#print axioms String.dropPrefix?
#print axioms String.stripPrefix
#print axioms String.front
#print axioms String.ofList
#print axioms String.fromUTF8
#check @String.fromUTF8
#print axioms String.Slice
#print axioms String.toSlice
#print axioms String.drop
#print axioms String.Slice.drop
#print axioms String.Slice.toString
#print axioms String.Slice.copy
#print axioms instDecidableEqString
#print axioms String.decEq
#print axioms String.ext
#print axioms String.bytes_inj
#print axioms ByteArray.extract_append
#print axioms ByteArray.append
#print axioms String.isValidUTF8
#print axioms String.dropWhile
#print axioms String.pushn
#print axioms String.utf8EncodeChar
#print axioms String.Pos.Raw
#print axioms String.Internal.extract
