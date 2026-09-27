/-
E1 · (a) ¿Es ESENCIAL el Classical.choice de derives0_soundness y lkc_sound para el ENUNCIADO?
Se toma el ENUNCIADO como hipótesis (no el teorema) y se deriva de él un principio clásico sobre
un `P : Prop` ARBITRARIO. Si el footprint de la implicación no trae Classical.choice, el enunciado
implica ese principio en la teoría base de Lean ⇒ ninguna prueba del enunciado puede evitar choice.
-/
import FOL.Soundness0
import FOL.SequentSound0

namespace Exp

open FOL.Metamath.Semantics

/-- Modelo de un punto donde TODA relación vale `P`. -/
def MP (P : Prop) : Model Unit := ⟨fun _ _ => (), fun _ _ => P⟩

def Q : Formula := Formula.atom "Q" []

/-- El ENUNCIADO de `derives0_soundness` implica la doble negación para todo `P : Prop`. -/
theorem soundness_stmt_implies_dne
    (hS : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢₀ f) → satisfies Γ f) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have h := hS (Derives₀.dne_schema [] Q) Unit (MP P) (fun _ => ())
    (fun _ hf => absurd hf List.not_mem_nil)
  exact h hnn

/-- El ENUNCIADO de `lkc_sound` implica el tercio excluso para todo `P : Prop`. -/
theorem lkc_stmt_implies_em
    (hS : ∀ {Γ Δ : List Formula}, LKc Γ Δ → ∀ {D : Type} (M : Model D) (v : Nat → D),
      (∀ g, g ∈ Γ → evalFormula M v g) → ∃ d, And (d ∈ Δ) (evalFormula M v d)) :
    ∀ P : Prop, Or P (Not P) := by
  intro P
  have hd : LKc [] [neg Q, Q] :=
    LKc.implR [] [Q] Q Formula.bottom
      (LKc.ax [Q] [Formula.bottom, Q] Q (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  obtain ⟨d, hmem, hval⟩ := hS hd (MP P) (fun _ => ()) (fun _ h => absurd h List.not_mem_nil)
  cases hmem with
  | head => exact Or.inr hval
  | tail _ h' =>
    cases h' with
    | head => exact Or.inl hval
    | tail _ h'' => exact absurd h'' List.not_mem_nil

/-- Control: los teoremas reales cumplen las hipótesis (así las hipótesis no son vacías). -/
example : ∀ P : Prop, Not (Not P) → P :=
  soundness_stmt_implies_dne (fun h => FOL.Metamath.Soundness0.derives0_soundness h)
example : ∀ P : Prop, Or P (Not P) :=
  lkc_stmt_implies_em (fun h => FOL.SequentSound0.lkc_sound h)

end Exp

#print axioms Exp.soundness_stmt_implies_dne
#print axioms Exp.lkc_stmt_implies_em
