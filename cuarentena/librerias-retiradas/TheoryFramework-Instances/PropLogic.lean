/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/PropLogic.lean
-- LogicSystem instance for propositional logic.

import TheoryFramework.Logic
import PropLogic

namespace TheoryFramework.Instances

open PropLogic
open PropLogic.Metamath.Semantics
open PropLogic.Metamath.Soundness
open PropLogic.Metamath.Completeness

instance propLogicSystem : LogicSystem PropLogic.Formula where
  derives         := fun Γ f => PropLogic.Derives Γ f
  bottom          := .bottom
  neg             := PropLogic.neg
  semanticEntails := PropLogic.Metamath.Semantics.satisfies
  sound           := @PropLogic.Metamath.Soundness.soundness
  complete        := @PropLogic.Metamath.Completeness.completeness

end TheoryFramework.Instances
