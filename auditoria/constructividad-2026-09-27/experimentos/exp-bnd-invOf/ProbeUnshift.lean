import FOL.Fresh0

/-! (b1) Una `unshift` explícita con la API de `String` de v4.31. Sólo se mide la DEFINICIÓN:
si la definición ya lleva choice, todo enunciado que la mencione lo lleva. -/

namespace ExpU

/-- Por `String.drop` (devuelve un `Slice`) y `copy`. -/
def unshiftDrop (x : String) : String :=
  if "f".isPrefixOf x then (x.drop 1).copy else x

/-- Por `dropPrefix?`. -/
def unshiftPrefix (x : String) : String :=
  match x.dropPrefix? "f" with
  | some t => t.copy
  | none => x

/-- Por bytes: `ByteArray.extract` (sin axiomas) + validez decidida con `validateUTF8`. -/
def unshiftBytes (x : String) : String :=
  let b := x.toByteArray.extract 1 x.toByteArray.size
  if h : b.IsValidUTF8 then
    let t := String.ofByteArray b h
    if "f" ++ t = x then t else x
  else x

/-- Por `String.fromUTF8?`. -/
def unshiftUTF8 (x : String) : String :=
  match String.fromUTF8? (x.toByteArray.extract 1 x.toByteArray.size) with
  | some t => if "f" ++ t = x then t else x
  | none => x

end ExpU

#print axioms String.isPrefixOf
#print axioms ExpU.unshiftDrop
#print axioms ExpU.unshiftPrefix
#print axioms ExpU.unshiftBytes
#print axioms ExpU.unshiftUTF8
#print axioms instDecidableIsValidUTF8
