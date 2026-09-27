import FOL.SequentSound0
import FOL.Finitary0
import FOL.Interpolation0

/-! JUEZ · Titulares cuyo choice es de RUTA (se prueban por completitud o solidez a propósito) y que
tienen gemelo finitario con el MISMO enunciado; y la esencialidad del enunciado de `lk0_sound`. -/
namespace ExpT
open FOL.Metamath.Semantics

def MP (P : Prop) : Model Unit := ⟨fun _ _ => (), fun _ _ => P⟩
def Q : Formula := Formula.atom "Q" []

/-- El ENUNCIADO de `lk0_sound` implica el tercio excluso (mismo testigo que `lkc_sound`). -/
theorem lk0_stmt_implies_em
    (hS : ∀ {Γ Δ : List Formula}, LK₀ Γ Δ → ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d)) :
    ∀ P : Prop, Or P (Not P) := by
  intro P
  have hd : LK₀ [] [neg Q, Q] :=
    LK₀.implR [] [Q] Q Formula.bottom
      (LK₀.ax [Q] [Formula.bottom, Q] Q (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  obtain ⟨d, hmem, hval⟩ := hS hd (MP P) (fun _ => ()) (fun _ h => absurd h List.not_mem_nil)
  cases hmem with
  | head => exact Or.inr hval
  | tail _ h' =>
    cases h' with
    | head => exact Or.inl hval
    | tail _ h'' => exact absurd h'' List.not_mem_nil

example : ∀ P : Prop, Or P (Not P) := lk0_stmt_implies_em (fun h => FOL.SequentSound0.lk0_sound h)

theorem lk0_to_derives0' {Γ Δ : List Formula} (h : LK₀ Γ Δ) : Γ ⊢₀ FOL.Herbrand0.disjOf Δ :=
  FOL.Interpolation0.lk0_to_derives0_fin h
theorem lk0_to_derives2' {Γ Δ : List Formula} (h : LK₀ Γ Δ) : Γ ⊢₂ FOL.Herbrand0.disjOf Δ :=
  FOL.Derives2.derives0_iff_derives2.mp (FOL.Interpolation0.lk0_to_derives0_fin h)
theorem lk0_not_empty' : Not (LK₀ [] []) := FOL.Finitary0.lk0_not_empty_fin
theorem derives0_consistent' : ¬ (([] : List Formula) ⊢₀ Formula.bottom) :=
  FOL.Finitary0.derives0_consistent_fin

end ExpT

example : @ExpT.lk0_to_derives0' = @FOL.SequentSound0.lk0_to_derives0 := rfl
example : @ExpT.lk0_to_derives2' = @FOL.SequentSound0.lk0_to_derives2 := rfl
example : @ExpT.lk0_not_empty' = @FOL.SequentSound0.lk0_not_empty := rfl
example : @ExpT.derives0_consistent' = @FOL.Metamath.Soundness0.derives0_consistent := rfl

#print axioms ExpT.lk0_stmt_implies_em
#print axioms ExpT.lk0_to_derives0'
#print axioms ExpT.lk0_to_derives2'
#print axioms ExpT.lk0_not_empty'
#print axioms ExpT.derives0_consistent'
#print axioms FOL.SequentSound0.lk0_to_derives2
#print axioms FOL.SequentSound0.lk0_not_empty
#print axioms FOL.Metamath.Soundness0.derives0_consistent
