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
-- La instancia NO se importa aquí: `TheoryFramework.Instances.FOL` (la de `Derives₀`, declarada
-- el 2026-09-27) importa `FOL.Canonical0`, toda la capa clásica, y el marco no la necesita. Quien
-- la quiera: `import TheoryFramework.Instances.FOL` (la compila el `globs` del lakefile).
-- (Las instancias `PropLogic` y `FOLPure` que se citaban aquí se retiraron el 2026-09-12.)
