import Lake
open Lake DSL

package «FOL» where
  moreServerArgs := #["-DautoImplicit=false"]

@[default_target]
lean_lib «FOL» where

lean_lib «FOLPure» where

lean_lib «PropLogic» where

lean_lib «TheoryFramework» where

lean_lib «FOL_poli» where
