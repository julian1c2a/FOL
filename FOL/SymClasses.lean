import FOL.FOL

/-!
# `FOL.SymClasses` — lo que hay que saber del tipo de los SÍMBOLOS

**Last updated:** 2026-09-18

ADR-068 metió el parámetro (`TermG Sym` / `FormulaG Sym`) y ADR-069 generificó la capa de
operaciones. Falta lo que **no** es sintaxis: la metateoría de FOL⁼ le pide al tipo de símbolos
exactamente **dos** cosas, y este módulo las declara.

## ⭐ Las dos clases, y por qué son éstas y no otras

| clase | quién la pide | qué le pide | medido en |
|---|---|---|---|
| `FreshSym` | `FOL.Fresh0` | fabricar constantes nuevas, y que no colisionen | `Fresh0.lean:79‑110` |
| `EnumSym` | `FOL.Metamath.Enumeration` | una **sobreyección** `Nat → Sym` | `Enumeration.lean:186` |

⭐ **`FreshSym` tiene exactamente tres propiedades, ni una más.** Se midió leyendo el único
consumidor no trivial: `Fresh0.cst_bound_sym` (`Fresh0.lean:155`) se demuestra con `by_cases`
sobre `∃ k, cst k = s` más `cst_inj`, y **no toca la estructura de `String`**. De ahí salen
`cst_bound_term`, `cst_bound_formula` y `cst_bound_list` sin pedir nada nuevo.

⭐ **`EnumSym` pide una sobreyección y nada más**: ni biyección, ni decidibilidad, ni orden, ni
inyectividad. Medido sobre `Enumeration.lean`: los `if` de `natToTerm`/`natToFormula` son todos
sobre `(unpair n).1 = k : Nat`, el caso base es `.var 0`, y `natToString_surj` se consume sólo en
la dirección `∃ n`.

## ⚠️ Por qué el parámetro se llama `Sym` y no `S`

`S` está **ocupado por la TEORÍA** (`S : Formula → Prop`) en `Henkin0`, `Fresh0`, `HenkinLimit0`,
`Lindenbaum0` y `Canonical0`, donde además es el binder de la `local notation … ⊢₀* …`. Ponerle
`S` al tipo de símbolos habría chocado en cinco módulos, y el choque se ve **tarde**.

## ⛔ Y lo que este módulo NO hace

Declarar las clases **no** permite todavía instanciar `Sym := List Char` en la metateoría:
`Fresh0` y `Enumeration` siguen siendo `String` por dentro. Para que esto no sea una capa
*cierta y vacua*, aquí va ya la instancia de `List Char` de `FreshSym` — **construida sin pasar
por `String`** —, y las de `EnumSym` van en `Enumeration.lean`, donde vive su prueba.
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

/-- ⭐ `List Char` satisface `FreshSym` **sin pasar por `String`**: `'f' :: s` y
`'c' :: replicate n 'i'`. Es el testigo de que la clase no se quedó corta ni se pasó de larga, y
de que el parámetro tiene al menos **dos** habitantes en el árbol compilado. -/
instance : FreshSym (List Char) where
  shift s := 'f' :: s
  cst n := 'c' :: List.replicate n 'i'
  shift_inj := by
    intro s t h
    injection h
  cst_inj := by
    intro m n h
    injection h with _ h2
    have hl := congrArg List.length h2
    simpa using hl
  cst_ne_shift := by
    intro n s h
    injection h with h1 _
    exact absurd h1 (by decide)

end FOL
