/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-!
# `FOL/SymLit.lean` — los literales de SÍMBOLO, `sym!"…"` (D7, ADR‑129 de RPP; en FOL desde T51, ADR‑218 de RPP)

🏁 2026‑10‑28 (T51, ADR‑218 de RPP): la macro nació en RPP (`Minimal/SymLit.lean`) y baja a FOL, que es de quien son
los símbolos: así la usan RPP, la entrega X1 y cualquier consumidor. RPP la importa de aquí.

Desde D7 los símbolos de FOL son `List Char` (antes `String`). `sym!"substfc"` es el símbolo
`['s', 'u', 'b', 's', 't', 'f', 'c'] : List Char`, y `sym!""` es `([] : List Char)`. Vale en TÉRMINO y en
PATRÓN (en RPP, el despacho del modelo, `Meta/ModeloEstandar.lean`, casa por `| sym!"σ", [a] => …`).

**Sin `String` en el resultado**: la macro lee la cadena al ELABORAR y construye la cadena de `List.cons`
de literales de carácter; el término sólo nombra `List.cons`, `List.nil`, `Char` y `Char.ofNat`. Ni
`String.toList` ni `String.decEq` llegan al núcleo. `String` sólo queda en el CÓDIGO de este fichero (la
macro y su `unexpander`, que corren al elaborar) y, en RPP, en `termToString` (su `Minimal/Axioms.lean`, impresión): ningún
teorema los nombra.

* `syntax:max`: sin él `.func sym!"σ" [t]` no se leería como argumento (la precedencia por defecto de una
  sintaxis que no acaba en átomo es `leadPrec`).
* Construye `List.cons` directamente, no `[…]`: la macro de listas de Lean cambia de forma a partir de
  ocho elementos (introduce un `let`, que un patrón no admite).
* Las comillas dobles (``List.cons``) resuelven el nombre al DEFINIR la macro: el `cons` del lenguaje
  objeto de RPP (su `Minimal/Axioms.lean`) no puede capturarlo.
* El `unexpander` imprime de vuelta `sym!"…"` en los objetivos (toda lista de literales de carácter).

Diseño: `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §7.2 y la exploración de D7 (ADR‑129 de RPP).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FOL.SymLit

/-- `sym!"abc"` es el símbolo `['a', 'b', 'c'] : List Char`; `sym!""` es `([] : List Char)`. -/
syntax:max (name := symLit) "sym!" str : term

macro_rules (kind := symLit)
  | `(sym! $s:str) => do
    let mut acc : Lean.Term ← ``(List.nil)
    for c in s.getString.toList.reverse do
      let lit : Lean.Term := Lean.Syntax.mkCharLit c
      acc ← ``(List.cons $lit $acc)
    ``(($acc : List Char))

/-- Imprime de vuelta como `sym!"…"` una cadena de `List.cons` de literales de carácter que acaba en `[]`.
Los `unexpander` actúan de abajo arriba: la cola ya es `[]` o `sym!"…"`. -/
@[app_unexpander List.cons]
def unexpandSymLit : Lean.PrettyPrinter.Unexpander
  | `($(_) $c:char $tail) =>
    match tail with
    | `([])          => `(sym! $(Lean.Syntax.mkStrLit c.getChar.toString))
    | `(sym! $s:str) => `(sym! $(Lean.Syntax.mkStrLit (c.getChar.toString ++ s.getString)))
    | _              => throw ()
  | _ => throw ()

/-! ### Autocontroles -/

example : sym!"substfc" = ['s', 'u', 'b', 's', 't', 'f', 'c'] := rfl
example : sym!"" = ([] : List Char) := rfl
example : sym!"Π_p" = ['Π', '_', 'p'] := rfl
example : sym!"σ" ≠ sym!"τ" := by decide

/-- El despacho por patrones: `sym!` en posición de patrón, con comodín. -/
def symMatchProbe : List Char → List Nat → Nat
  | sym!"σ", [a] => a + 1
  | sym!"Π_p", [l] => l
  | sym!"", [] => 7
  | _, _ => 0

example : symMatchProbe sym!"σ" [4] = 5 := rfl
example : symMatchProbe sym!"τ" [4] = 0 := rfl
example : symMatchProbe sym!"" [] = 7 := rfl

/-- Guarda de footprint: una expansión que pasara por `String` (`"…".toList`) llevaría `Classical.choice`. -/
def symProbe : List Char := sym!"axiomsCodeT"

end FOL.SymLit


#print axioms FOL.SymLit.symProbe
