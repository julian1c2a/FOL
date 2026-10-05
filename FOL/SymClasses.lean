import FOL.FOL

/-!
# `FOL.SymClasses` — lo que hay que saber del tipo de los SÍMBOLOS

**Last updated:** 2026-10-05 — D7 ejecutada (ADR‑129 de RPP): los símbolos son `List Char`, la
instancia de MEDIDA de `FreshSym` se retira y la instancia es la de `FOL.Fresh0`. Antes, 2026-09-27.

ADR-068 metió el parámetro (`TermG Sym` / `FormulaG Sym`) y ADR-069 generificó la capa de
operaciones. Falta lo que **no** es sintaxis: la metateoría de FOL⁼ le pide al tipo de símbolos
exactamente **dos** cosas, y este módulo las declara.

## ⭐ Las dos clases, y por qué son éstas y no otras

| clase | quién la pide | qué le pide | medido en |
|---|---|---|---|
| `FreshSym` | `FOL.Fresh0` | fabricar constantes nuevas, y que no colisionen | `Fresh0.shift`, `cst`, `shift_inj`, `cst_inj`, `cst_ne_shift` |
| `EnumSym` | `FOL.Metamath.Enumeration` | una **sobreyección** `Nat → Sym` | `Enumeration.natToSym_surj` (hasta D7, `natToString_surj`) |

⭐ **`FreshSym` tiene exactamente tres propiedades, ni una más.** Se midió leyendo el único
consumidor no trivial: `Fresh0.cst_bound_sym` se demostraba con `by_cases`
sobre `∃ k, cst k = s` más `cst_inj`, y **no tocaba la estructura de `String`**. De ahí salen
`cst_bound_term`, `cst_bound_formula` y `cst_bound_list` sin pedir nada nuevo.

⚠️ **RECTIFICACIÓN (2026‑09‑27).** La medida sigue siendo cierta **con tercio excluso**, pero el
consumidor ya no es así. `Fresh0.cst_bound_sym` se prueba ahora con una cota CALCULADA,
`s.utf8ByteSize`, porque `cst m` ocupa `m + 1` bytes (`Fresh0.cst_utf8ByteSize`): sin `by_cases`,
sin `cst_inj` y sin `Classical.choice`, mirando la capa de bytes de `String`. ⇒ Para un `Sym`
genérico, la prueba con las tres propiedades es la de antes, clásica; la de `String` usa algo que
la clase no tiene: una cota de tamaño. La instancia de `List Char` de abajo también la tendría
(`cst n` mide `n + 1`). A 2026‑09‑27 la clase no se amplía: es una MEDIDA, y ningún módulo la
consume. ✏️ 2026‑10‑05 (D7, ADR‑129 de RPP): la cota es hoy `s.length` (`Fresh0.cst_length`;
`cst_utf8ByteSize`, retirado), y la instancia de abajo se retiró: la de la clase es
`FOL.Fresh0.instFreshSymListChar`. La clase sigue sin ampliarse y sin consumidores.

⭐ **`EnumSym` pide una sobreyección y nada más**: ni biyección, ni decidibilidad, ni orden, ni
inyectividad. Medido sobre `Enumeration.lean`: los `if` de `natToTerm`/`natToFormula` son todos
sobre `(unpair n).1 = k : Nat`, el caso base es `.var 0`, y `natToSym_surj` (hasta D7,
`natToString_surj`) se consume sólo en la dirección `∃ n`.

## ⚠️ Por qué el parámetro se llama `Sym` y no `S`

`S` está **ocupado por la TEORÍA** (`S : Formula → Prop`) en `Henkin0`, `Fresh0`, `HenkinLimit0`,
`Lindenbaum0` y `Canonical0`, donde además es el binder de la `local notation … ⊢₀* …`. Ponerle
`S` al tipo de símbolos habría chocado en cinco módulos, y el choque se ve **tarde**.

## ⛔ Y lo que este módulo NO hace

⛔ **Y la vía de instanciarlas en la cadena de completitud queda CERRADA** (2026‑09‑23, ver
`FOL/FOL.lean`): su única justificación escrita era LS ascendente, y `EnumSym` —esta misma clase,
líneas abajo— es falsa para los tipos no numerables que LS↑ necesita. Y el cierre es
**DEFINITIVO** (decisión del propietario del 2026-09-26): no hay receta para reabrirla.

⭐ Las clases **se quedan**, como MEDIDA y no como capa en uso: dicen exactamente qué le pediría
esa cadena al tipo de símbolos, y **ningún** módulo las consume (ninguna firma del árbol lleva
`[FreshSym _]` ni `[EnumSym _]`). `Fresh0`, `Enumeration` y la cadena de completitud son `List Char`
por dentro (desde D7, 2026‑10‑05; hasta entonces `String`), concretos y no genéricos. Para que la
medida no sea *cierta y vacua*, cada clase tiene su instancia en `List Char` junto a su prueba:
`FOL.Fresh0.instFreshSymListChar` y `FOL.Metamath.Enumeration.instEnumSymListChar`. (Hasta D7 aquí
iba una instancia `FreshSym (List Char)` de MEDIDA —`'c' :: replicate n 'i'`, construida sin pasar
por `String`—, y `Enumeration.lean` tenía además una `EnumSym String`: D7 retiró las dos.)
Y la migración `String`→`List Char` del plan §7.3 de RPP quedó **ABANDONADA en FOL** el 2026-09-26
(D7): la parte de FOL estaba hecha como parámetro, y terminarla no movería ningún
footprint titular de FOL (su `Classical.choice` es el WKL). ✏️ 2026‑10‑05: D7 EJECUTADA (ADR‑129 de
RPP), por decisión del propietario: los `abbrev` de `FOL/FOL.lean` son `List Char`.

⚠️ **RECTIFICACIÓN (2026‑09‑27) de esa razón.** «Su `Classical.choice` es el WKL» era falso como
localización (ver la cabecera de `FOL/Canonical0.lean`). La conclusión se mantenía, y con mejor
fundamento: la migración **no hacía falta**. Lo que en v4.31 trae `Classical.choice` a `String` es
DECODIFICAR UTF‑8 (`toList`, `ofList_toList`, `String.instOrd`), no `String` en sí; la capa de bytes
está limpia. La auditoría de constructividad retiró esos usos sin migrar: `Fresh0` comparaba con
`String.decEq` y acotaba con `utf8ByteSize`, y `natToString_surj` (hoy retirado) usaba
`String.exists_eq_ofList`.
Los 34 titulares de FOL que conservaban `Classical.choice` (2026‑09‑27) lo llevan por la semántica
de Tarski, por el lema de la verdad sobre un maximal arbitrario, por el `byContradiction` final de
`completeness₀` o por las funciones de Skolem, directamente o por ruta. `List Char` no cambiaría
ninguno.
✏️ 2026‑10‑05: el propietario reabrió la migración y D7 está EJECUTADA (ADR‑129 de RPP); `Fresh0`
compara con la igualdad decidible de `List Char` y acota con `List.length`, y la sobreyección es
`natToSym_surj`. Y «`List Char` no cambiaría ninguno» se midió: las 39 filas de FOL y
`TheoryFramework` con `Classical.choice` (`../ROBINSON_PlusPlus/check-footprints.bash`) lo conservan.
-/

namespace FOL

universe u

/-- Lo que `FOL.Fresh0` necesita del tipo de símbolos: una familia infinita de constantes
nuevas (`cst`) y un desplazamiento inyectivo (`shift`) cuya imagen no las toca. -/
class FreshSym (Sym : Type u) where
  /-- Renombra un símbolo de función para dejar libre el espacio de las constantes nuevas. -/
  shift        : Sym → Sym
  /-- La familia infinita de constantes nuevas. -/
  cst          : Nat → Sym
  shift_inj    : ∀ s t, shift s = shift t → s = t
  cst_inj      : ∀ m n, cst m = cst n → m = n
  /-- ⭐⭐ **Ninguna constante nueva está en la imagen del desplazamiento.** Es lo único que hay
  que saber de los nombres: todo lo demás se deduce. -/
  cst_ne_shift : ∀ n s, cst n ≠ shift s

/-- Lo que `FOL.Metamath.Enumeration` necesita: una **sobreyección** `Nat → Sym`.
⚠️ Con `Sym` genérico esto **no es demostrable** —hay tipos no numerables—, así que es una
hipótesis, y ésta es su forma mínima. -/
class EnumSym (Sym : Type u) where
  enum      : Nat → Sym
  enum_surj : ∀ s, ∃ n, enum n = s

-- D7 (2026‑10‑05): aquí iba una instancia `FreshSym (List Char)` de MEDIDA (`'c' :: replicate n 'i'`).
-- Desde que los símbolos son `List Char`, la instancia es la de `FOL.Fresh0` —hecha con la `cst` y el `shift`
-- que la cadena de completitud usa desnudos; la cadena no consume la instancia—, y dos instancias para el
-- mismo tipo harían que la `cst` dependiera de los `import`.

end FOL
