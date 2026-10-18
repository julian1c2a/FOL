/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL
import TheoryFramework.Instances.FOL

/-! `scripts/VolcarEntorno.lean` — el entorno de Lean de FOL, para `[B]` de `check-doc-sync.bash` (T04 y ADR‑166 de RPP).

Escribe en la salida estándar, una por línea, cada constante no interna del entorno de `import FOL` y de la instancia de
TheoryFramework (con «P» si su módulo es de FOL o de TheoryFramework, y «L» si no) y cada opción registrada (con «O»).
No está en el build: necesita el build hecho. ⛔ M‑3: en local se ejecuta desde la raíz de RPP
(`lake env lean ../FOL/scripts/VolcarEntorno.lean`), que es donde se construye FOL; en la CI de FOL, desde FOL. -/

open Lean Elab Command

elab "#volcar_entorno" : command => do
  let env ← getEnv
  -- a un FICHERO, el de la variable VOLCADO: en Windows, la salida estándar de Lean tarda más de dos minutos con
  -- 130 000 líneas, y el fichero, siete segundos (medido el 2026-10-18)
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    unless n.isInternal do
      let m := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]?).getD Name.anonymous
        | none => Name.anonymous
      let proy := (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m
      out := out.push s!"{n}\t{if proy then "P" else "L"}"
  for (n, _) in (← getOptionDecls).toList do
    out := out.push s!"{n}\tO"
  let texto := "\n".intercalate out.toList ++ "\n"
  match (← IO.getEnv "VOLCADO") with
  | some ruta => IO.FS.writeFile ruta texto
  | none => IO.print texto

#volcar_entorno
