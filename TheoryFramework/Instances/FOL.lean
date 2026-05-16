/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOL.lean
-- LogicSystem instance for first-order logic with equality (FOL^=).
--
-- NOTE: FOL.Completeness contains one `sorry` (the equality/Henkin case).
-- This sorry is encapsulated here; the rest of the framework is sorry-free.

import TheoryFramework.Logic
import FOL

namespace TheoryFramework.Instances

open FOL
open FOL.Metamath.Semantics
open FOL.Metamath.Soundness
open FOL.Metamath.Completeness

-- Formula, Derives, neg are defined at root level in FOL/FOL.lean
instance folSystem : LogicSystem Formula where
  derives         := fun Γ f => Derives Γ f
  bottom          := .bottom
  neg             := neg
  semanticEntails := FOL.Metamath.Semantics.satisfies
  sound           := @FOL.Metamath.Soundness.soundness
  complete        := @FOL.Metamath.Completeness.completeness

end TheoryFramework.Instances
