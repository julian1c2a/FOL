/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: constructive
-- @importance: medium

import FOL.FOL

/-!
# `FOL.DecEq` — `DecidableEq` **de verdad** para `Term` y `Formula`

`Term` y `Formula` derivan `BEq`, que **no basta**: de `BEq` no sale `Decidable (a = b)` sin una
instancia `LawfulBEq`. Hasta ahora, cada vez que hacía falta decidir una igualdad de fórmulas
—el `filter` de `FOL.Henkin0`, el de `FOL.Lindenbaum0`— se resolvía con `open Classical`, y eso
mete `Classical.choice` en el footprint **por una razón que no es matemática**.
(⚠️ 2026‑09‑27: esos dos `filter` ya no existen. No los sustituyó esta instancia sino algo mejor,
`Henkin0.ctx_split`, que parte el contexto **sin decidir ninguna igualdad**; ver la rectificación
del final.)

Aquí está la instancia real, y es **net‑0 pura**: `#print axioms` no imprime nada.

## ⚠️ Por qué está escrita a mano

⛔ **`deriving instance DecidableEq for Term` NO funciona** (medido): `Term.func : String → List
Term → Term` es un inductivo **anidado**, y ninguno de los *deriving handlers* de v4.31 se le
aplica. Hay que escribir la recursión mutua `Term` / `List Term`.

⭐ En cambio **`Formula` sí se deriva**, una vez existe la de `Term`: sus ocurrencias recursivas
son directas y la única anidada es `List Term`, que ya tiene instancia.

## ⚠️⚠️ CORRECCIÓN (2026‑09‑16): aquí decía que NO reduce, y es FALSO

El texto anterior era:

> No **reduce** en el kernel: `decEqTerm` se compila por recursión bien fundada, así que
> `by decide` sobre una igualdad concreta de fórmulas **se atasca**.

**Medido de nuevo, y sale al revés**: los tres controles compilan **por `rfl`**:

    decide (Term.var 1 = Term.var 1) = true
    decide (Formula.atom "P" [#0] = Formula.atom "P" [#0]) = true
    decide (Formula.atom "P" [#0] = Formula.atom "Q" [#0]) = false

⇒ **la instancia SÍ reduce**, y por eso `FOL.Herbrand0.ptautCheck` —que la usa a través de
`upd`— se evalúa en el kernel y un certificado de Herbrand se comprueba con `by rfl`.

🔑 El fallo original era **del control, no del código**: probé `decide (X = Y) = true` con
`by decide`, es decir, un `decide` envolviendo a otro, y lo que se atascaba era el de fuera.
*Un control mal montado mide su propio montaje.*

## ⛔ Y por qué NO se retrofita a los módulos ya escritos

`FOL.Henkin0` y `FOL.Lindenbaum0` no importan este módulo, así que su elaboración **no cambia**:
sus `Decidable` siguen resolviéndose por `Classical.propDecidable`. Cambiarlo movería el footprint
de teoremas ya publicados y medidos, y el `Classical.choice` de `FOL.Lindenbaum0` **tiene que
seguir ahí** por otra razón —el `if IsConsistent₀ …`, que es Π⁰₁ (ADR‑040 §2)—, así que no se
ganaría nada y se perdería la trazabilidad.

## ⚠️⚠️ RECTIFICACIÓN (2026‑09‑27): la conclusión se mantiene, las razones no

* «sus `Decidable` siguen resolviéndose por `Classical.propDecidable`»: ya no queda ninguno. En la
  frontera medida (`auditoria/constructividad-2026-09-27/despues/frontera.txt`) ni `FOL.Henkin0`
  ni `FOL.Lindenbaum0` usan `Classical.propDecidable`; `max_cons_contains` usa
  `Classical.byContradiction` directamente.
* «el `Classical.choice` de `FOL.Lindenbaum0` tiene que seguir ahí por el `if IsConsistent₀ …`»:
  **FALSO**. La etapa de Lindenbaum ya no decide nada: la condición va DENTRO del predicado y
  no se decide. `lindenbaum_lemma₀` y `henkin_completion₀` miden `[propext, Quot.sound]`. Lo único
  clásico que queda en `FOL.Lindenbaum0` es `max_cons_contains` (y `max_cons_impl`, que lo usa), y
  no por decidir igualdades: es el `¬¬P → P` de un maximal arbitrario.
* «cambiarlo movería el footprint de teoremas ya publicados»: se movió, a la baja y a propósito
  (decisión D1 del propietario tras la auditoría de constructividad, 2026‑09‑27).

La conclusión —no importar este módulo en `FOL.Henkin0` ni en `FOL.Lindenbaum0`— sigue en pie, por
una razón nueva: **no les hace falta**. La auditoría midió las dos vías
(`…/experimentos/exp-deceq/`). Con `import FOL.DecEq`, `henkin_step_consistent₀` y
`derivesSet0_intro_impl` pierden el `Classical.choice`. Con `ctx_split` también, sin la instancia, y
además `derivesSet0_intro_impl` queda sin NINGÚN axioma. Ninguno de los dos módulos abre ya
`Classical`. 🔑 *Decidir una igualdad para partir una lista es un rodeo cuando la hipótesis ya dice
de qué lado cae cada elemento.*
-/

namespace FOL.DecEq

mutual
def decEqTerm {S : Type} [DecidableEq S] : (a b : TermG S) → Decidable (a = b)
  | .var n, .var m =>
      if h : n = m then isTrue (by rw [h]) else isFalse (fun he => h (by injection he))
  | .var _, .func _ _ => isFalse (by intro h; cases h)
  | .func _ _, .var _ => isFalse (by intro h; cases h)
  | .func s ts, .func u us =>
      if hs : s = u then
        match decEqTerms ts us with
        | isTrue ht => isTrue (by rw [hs, ht])
        | isFalse ht => isFalse (fun h => ht (by cases h; rfl))
      else isFalse (fun h => hs (by cases h; rfl))

def decEqTerms {S : Type} [DecidableEq S] : (a b : List (TermG S)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | t :: ts, u :: us =>
      match decEqTerm t u with
      | isTrue h1 =>
        match decEqTerms ts us with
        | isTrue h2 => isTrue (by rw [h1, h2])
        | isFalse h2 => isFalse (fun h => h2 (by cases h; rfl))
      | isFalse h1 => isFalse (fun h => h1 (by cases h; rfl))
end

instance instDecidableEqTermG {S : Type} [DecidableEq S] : DecidableEq (TermG S) := decEqTerm

abbrev instDecidableEqTerm : DecidableEq Term := instDecidableEqTermG

end FOL.DecEq

-- ⭐ Ésta SÍ se deriva, una vez existe la de `TermG`.
deriving instance DecidableEq for FormulaG

abbrev instDecidableEqFormula : DecidableEq Formula := instDecidableEqFormulaG

#print axioms FOL.DecEq.instDecidableEqTerm
#print axioms instDecidableEqFormula
