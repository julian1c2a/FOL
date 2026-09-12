/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOLPure.lean
-- LogicSystem instance for pure first-order logic (without equality).

import TheoryFramework.Logic
import FOLPure

namespace TheoryFramework.Instances

open FOLPure
open FOLPure.Metamath.Semantics
open FOLPure.Metamath.Soundness
open FOLPure.Metamath.Completeness

-- Formula, Derives, neg are defined at root level in FOLPure/FOL.lean
instance folPureSystem : LogicSystem Formula where
  derives         := fun Γ f => Derives Γ f
  bottom          := .bottom
  neg             := neg
  semanticEntails := FOLPure.Metamath.Semantics.satisfies
  sound           := @FOLPure.Metamath.Soundness.soundness
  complete        := @FOLPure.Metamath.Completeness.completeness

end TheoryFramework.Instances
