import FOL.Fresh0
namespace ExpU2
def u1 (x : String) : String := (x.drop 1).copy
def u2 (x : String) : String := (x.sliceFrom (x.startPos.next?.getD x.startPos)).copy
end ExpU2
#print axioms String.drop
#print axioms String.Slice.copy
#print axioms ExpU2.u1
#print axioms String.dropPrefix?
#print axioms String.startsWith
#print axioms String.Pos.next
#print axioms String.front
#print axioms String.get
#print axioms String.extract
#print axioms ByteArray.extract
#print axioms String.toByteArray_append
#print axioms ByteArray.append_inj_left
#print axioms String.toByteArray_inj
#print axioms String.ofByteArray
#print axioms ByteArray.IsValidUTF8
#print axioms String.singleton_append_inj
#print axioms String.ofList_cons
#print axioms String.length_ofList
