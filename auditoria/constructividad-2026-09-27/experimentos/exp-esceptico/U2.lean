import FOL.Compacity0
/-! ESCEPTICO · Una inversa GLOBAL de `shift` sin `Classical.choice` (contra «una unshift sin choice
no es viable con la API de v4.31»). Se trabaja en bytes: `String.ofByteArray` y `ByteArray` no llevan
axiomas; la validez UTF‑8 de la cola se PRUEBA (no se decide) a partir de la de la cadena, porque el
primer byte es ASCII (102 = 'f'). -/

namespace ExpUS
open FOL.Fresh0 (shift shift_inj)

theorem valid_tail {x : String} (h : x.toByteArray.data.toList.head? = some 102) :
    ByteArray.IsValidUTF8 ⟨x.toByteArray.data.toList.tail.toArray⟩ := by
  obtain ⟨m, hm⟩ := x.isValidUTF8
  have hl : x.toByteArray.data.toList = m.flatMap String.utf8EncodeChar := by
    rw [hm, List.utf8Encode, List.toList_data_toByteArray]
  rw [hl] at h ⊢
  cases m with
  | nil => exact absurd h (fun h' => by cases h')
  | cons c m' =>
    rw [List.flatMap_cons] at h ⊢
    have hv : c.val.toNat ≤ 0x7f := by
      apply Nat.le_of_not_lt
      intro hlt
      have hlt' : Not (c.val.toNat ≤ 0x7f) := Nat.not_le_of_lt hlt
      simp only [String.utf8EncodeChar, if_neg hlt'] at h
      by_cases h2 : c.val.toNat ≤ 0x7ff
      · rw [if_pos h2] at h
        have h3 := congrArg UInt8.toNat (Option.some.inj h)
        rw [UInt8.toNat_ofNat'] at h3
        exact absurd h3 (by show Not (_ = 102); omega)
      · rw [if_neg h2] at h
        by_cases h4 : c.val.toNat ≤ 0xffff
        · rw [if_pos h4] at h
          have h3 := congrArg UInt8.toNat (Option.some.inj h)
          rw [UInt8.toNat_ofNat'] at h3
          exact absurd h3 (by show Not (_ = 102); omega)
        · rw [if_neg h4] at h
          have h3 := congrArg UInt8.toNat (Option.some.inj h)
          rw [UInt8.toNat_ofNat'] at h3
          exact absurd h3 (by show Not (_ = 102); omega)
    simp only [String.utf8EncodeChar, if_pos hv]
    have e : (m'.flatMap String.utf8EncodeChar).toByteArray.data =
        (m'.flatMap String.utf8EncodeChar).toArray := List.data_toByteArray
    exact ⟨m', by rw [List.utf8Encode]; exact congrArg ByteArray.mk e.symm⟩

/-- ⭐ La inversa global de `shift`, SIN elección. -/
def unshiftC (x : String) : String :=
  if h : x.toByteArray.data.toList.head? = some 102 then
    String.ofByteArray ⟨x.toByteArray.data.toList.tail.toArray⟩ (valid_tail h)
  else x

theorem shift_bytes (s : String) :
    (shift s).toByteArray.data.toList = 102 :: s.toByteArray.data.toList := by
  show ("f" ++ s).toByteArray.data.toList = _
  rw [String.toByteArray_append, ByteArray.toList_data_append]
  rfl

theorem unshiftC_shift (s : String) : unshiftC (shift s) = s := by
  apply String.toByteArray_inj.mp
  unfold unshiftC
  split
  · show ByteArray.mk (shift s).toByteArray.data.toList.tail.toArray = s.toByteArray
    rw [shift_bytes]
    show ByteArray.mk s.toByteArray.data.toList.toArray = s.toByteArray
    rw [Array.toArray_toList]
  · rename_i hne
    exact absurd (by rw [shift_bytes]; rfl) hne

-- ═══ Consecuencias: las de Fresh0 y Compacity0, con la inversa GLOBAL sin choice ═══
open FOL.Rename
open FOL.Fresh0
open FOL.Henkin0 (DerivesSet₀ IsConsistent₀)
open FOL.Compacity0 (HasLargeModels)
open FOL.Canonical0 (pullback eval_pullback_formula)
open FOL.Metamath.Semantics

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

/-- `hasLargeModels_shift`, la prueba de FOL cambiando SÓLO `invOf shift` por `unshiftC`. -/
theorem hasLargeModels_shift' {S : Formula → Prop} (h : HasLargeModels S) :
    HasLargeModels (shiftTheory S) := by
  intro n
  obtain ⟨D, M, v, hM, he⟩ := h n
  refine ⟨D, pullback M unshiftC, v, fun x hx => ?_, he⟩
  obtain ⟨g, hg, rfl⟩ := hx
  refine (eval_pullback_formula M unshiftC (renameFormula shift g) v).mpr ?_
  rw [rename_rename_formula unshiftC_shift g]
  exact hM g hg

/-- `derivesSet0_shift_inv`, la prueba de FOL cambiando SÓLO `invOf shift` por `unshiftC`
(no toca `FOL.Rename`). -/
theorem derivesSet0_shift_inv'' {S : Formula → Prop} {f : Formula}
    (h : shiftTheory S ⊢₀* renameFormula shift f) : S ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  have hcancel := rename_rename_formula unshiftC_shift
  refine ⟨Γ.map (renameFormula unshiftC), ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, hex⟩ := List.mem_map.mp hg
    obtain ⟨y, hSy, hey⟩ := hΓ x hx
    rw [← hex, hey, hcancel]
    exact hSy
  · have hr := derives0_rename unshiftC hD
    rwa [hcancel f] at hr

theorem shiftTheory_consistent₀'' {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (shiftTheory S) := fun hbot => hCons (derivesSet0_shift_inv'' hbot)

end ExpUS

example : @ExpUS.hasLargeModels_shift' = @FOL.Compacity0.hasLargeModels_shift := rfl

example : @ExpUS.derivesSet0_shift_inv'' = @FOL.Fresh0.derivesSet0_shift_inv := rfl
example : @ExpUS.shiftTheory_consistent₀'' = @FOL.Fresh0.shiftTheory_consistent₀ := rfl
#print axioms ExpUS.derivesSet0_shift_inv''
#print axioms ExpUS.shiftTheory_consistent₀''
#print axioms ExpUS.valid_tail
#print axioms ExpUS.unshiftC
#print axioms ExpUS.unshiftC_shift
#print axioms ExpUS.hasLargeModels_shift'
#print axioms FOL.Compacity0.hasLargeModels_shift
#print axioms FOL.Rename.rename_rename_formula
#print axioms FOL.Canonical0.eval_pullback_formula
