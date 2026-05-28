/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Root module for TheoryFramework.
-- Generic framework for evaluating theories over any LogicSystem.

import TheoryFramework.Logic
import TheoryFramework.Theory
import TheoryFramework.Properties
import TheoryFramework.Relations
import TheoryFramework.MetaTheorems
-- Instances are NOT imported here: FOLPure and FOL both define `Formula`
-- at root level, causing a conflict when imported together.
-- Users import whichever instance they need:
--   import TheoryFramework.Instances.PropLogic
--   import TheoryFramework.Instances.FOLPure
--   import TheoryFramework.Instances.FOL
