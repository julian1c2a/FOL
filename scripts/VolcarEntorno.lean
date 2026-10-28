/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL
import TheoryFramework.Instances.FOL
-- ✏️ 2026-10-28 (T58, ADR-217 de RPP): y la de los modelos, que trae `Semantics` y `Conservativity`; sin ella, `[B]`
-- daba por muertas las citas de sus declaraciones (lo vio en su primera ejecución).
import TheoryFramework.Instances.FOLModels

/-! `scripts/VolcarEntorno.lean` — el entorno de Lean de FOL, para `[B]` de `check-doc-sync.bash` (T04 y ADR‑166 de RPP).

Escribe en el fichero de la variable `VOLCADO` (sin ella, en la salida estándar), una por línea, cada constante no
interna del entorno de `import FOL` y de las instancias de TheoryFramework (con el marco entero) (con «P» si su módulo es de FOL o de
TheoryFramework, y «L» si no), cada opción registrada (con «O»), cada módulo importado (con «M») y cada orden, un token
del analizador que empieza por «#» (con «T»).
No está en el build: necesita el build hecho. ⛔ M‑3: en local se ejecuta desde la raíz de RPP
(`lake env lean ../FOL/scripts/VolcarEntorno.lean`), que es donde se construye FOL; en la CI de FOL, desde FOL. -/

open Lean Elab Command

elab "#volcar_entorno" : command => do
  let env ← getEnv
  -- a un FICHERO, el de la variable VOLCADO: en Windows, la salida estándar de Lean tarda más de dos minutos con
  -- 130 000 líneas, y el fichero, siete segundos (medido el 2026-10-18)
  let mut out : Array String := #[]
  let proyecto (n : Name) : Bool :=
    let m := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]?).getD Name.anonymous
      | none => Name.anonymous
    (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m
  -- los ALIAS del proyecto: con `abbrev Formula := FormulaG (List Char)`, Lean resuelve `Formula.atom` como
  -- `FormulaG.atom`, y los documentos lo citan así. Van con un tercer campo, «A»: valen enteros, pero sus componentes
  -- no absuelven nombres sueltos (un `abbrev N := Nat` no revive `add_comm`; ADR‑167 de RPP)
  let mut alias : NameMap (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .defnInfo d := ci then
      if proyecto n then
        if let .reducible ← getReducibilityStatus n then
          let mut v := d.value
          while v.isLambda do v := v.bindingBody!
          if let .const h _ := v.getAppFn then
            if let some (.inductInfo _) := env.find? h then
              alias := alias.insert h (((alias.find? h).getD #[]).push n)
  for (n, _) in env.constants.toList do
    unless n.isInternal do
      out := out.push s!"{n}\t{if proyecto n then "P" else "L"}"
      let mut p := n.getPrefix
      while !p.isAnonymous do
        for a in (alias.find? p).getD #[] do
          out := out.push s!"{n.replacePrefix p a}\tP\tA"
        p := p.getPrefix
  for (n, _) in (← getOptionDecls).toList do
    out := out.push s!"{n}\tO"
  -- y los módulos importados (`Init.Classical`): se citan y no son constantes
  for m in env.header.moduleNames do
    out := out.push s!"{m}\tM"
  -- y las ÓRDENES (`#print`, `#eval`): los tokens del analizador que empiezan por «#»
  for t in Lean.Data.Trie.values (Lean.Parser.getTokenTable env) do
    if t.startsWith "#" then
      out := out.push s!"{t}\tT"
  let texto := "\n".intercalate out.toList ++ "\n"
  match (← IO.getEnv "VOLCADO") with
  | some ruta => IO.FS.writeFile ruta texto
  | none => IO.print texto

#volcar_entorno
