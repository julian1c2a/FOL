import TheoryFramework
import FOL.Canonical0

/-! Experimento de auditoría: la opción (a) de `TheoryFramework/Instances/FOL.lean` (las dos
DIFERIDA de `[G.2]`): `LogicSystem Formula` sobre `Derives₀`, con `SoundLogic` y `CompleteLogic`
pagadas por `derives0_soundness` y `completeness₀`. ¿Compila, y cuánto cuesta? -/

namespace Exp
open TheoryFramework FOL.Metamath.Semantics

@[reducible] def fol0System : LogicSystem Formula where
  derives         := fun Γ f => Γ ⊢₀ f
  bottom          := Formula.bottom
  neg             := neg
  semanticEntails := fun Γ f => satisfies Γ f

attribute [local instance] fol0System

theorem fol0Sound : SoundLogic Formula :=
  ⟨fun h => FOL.Metamath.Soundness0.derives0_soundness h⟩

theorem fol0Complete : CompleteLogic Formula :=
  ⟨fun h => FOL.Canonical0.completeness₀ h⟩

attribute [local instance] fol0Sound fol0Complete

theorem fol0_proves_iff_models (T : Theory Formula) (f : Formula) : T.proves f ↔ T.models f :=
  TheoryFramework.proves_iff_models T f

end Exp

#print axioms Exp.fol0System
#print axioms Exp.fol0Sound
#print axioms Exp.fol0Complete
#print axioms Exp.fol0_proves_iff_models
