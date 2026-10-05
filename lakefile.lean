import Lake
open Lake DSL

package «FOL» where
  -- `autoImplicit` desactivado en el EDITOR y en `lake build` (ADR‑128 de RPP, 2026‑10‑05). Antes era
  -- `moreServerArgs := #["-DautoImplicit=false"]`, que sólo llega al servidor del editor: `lake build`
  -- aceptaba variables implícitas automáticas (medido con un módulo sonda). `leanOptions` vale para los
  -- dos; activarlo no rompió ningún módulo (build completo desde cero, medido).
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «FOL» where

-- ⚠️ `TheoryFramework` SÍ entra en el build desde el 2026‑09‑12 (A‑5): antes estaba
-- declarada pero sin `@[default_target]`, así que **nunca se compilaba** y su
-- `Instances/FOL.lean` llevaba meses roto sin que nada lo dijera. Ahora rompe si rompe.
@[default_target]
lean_lib «TheoryFramework» where
  -- ⚠️ `globs` EXPLÍCITO (2026‑09‑12, A‑5): sin él la `lean_lib` sólo compila lo que el
  -- barrel alcanza, y `TheoryFramework/Instances/FOL.lean` era HUÉRFANO — roto desde hacía
  -- meses, autodescribiéndose «fully complete and verified», y sin que nada lo dijera.
  -- Con `.submodules` entra TODO el directorio: si algo rompe, el build lo dice.
  globs := #[.submodules `TheoryFramework]

-- 🗑️ **RETIRADAS el 2026‑09‑12** (D‑1): `FOLPure`, `PropLogic` y `FOL_poli` están en
-- `cuarentena/librerias-retiradas/`. Medido: cero consumidores, cero artefactos de
-- compilación, y `FOL_poli/FOL.lean` era **byte‑idéntico** a `FOL/FOL.lean`.
-- ⛔ Estaban en el PEOR estado posible: declaradas (⇒ su salida en el `LEAN_PATH` de
-- ROBINSON_PlusPlus), con 15 de los 28 axiomas del repo, y **nunca compiladas** — que es
-- la causa raíz de que un `axiom` FALSO sobreviviera ahí 80 días.
-- Ver `cuarentena/README.md` §7.
