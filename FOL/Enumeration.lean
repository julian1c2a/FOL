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
-- @axiom_system: none
-- @importance: medium

import FOL.FOL
import FOL.SymClasses

/-!
# `FOL.Enumeration` — las fórmulas son ENUMERABLES, y aquí está la sobreyección

⭐ **Este módulo existe para RETIRAR DOS AXIOMAS** de los cinco de `cuarentena/Completeness.lean`.
(Los otros dos baratos —`termEqv_func_congr` y `termEqv_rel_congr`— cayeron el mismo día por otra
vía, en `FOL/Theorems/Eq.lean`; el módulo quedó en **un solo** postulado.)

`cuarentena/Completeness.lean` postulaba

    axiom formula_enum      : Nat → Formula
    axiom formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f

con el comentario «asumimos la enumerabilidad de las fórmulas». No hace falta asumirla: se
construye. Aquí está construida, y **compilada dentro del build** — no en `cuarentena/`, que
no se compila, que es exactamente donde un `axiom` falso sobrevivió ochenta días.

## El plan, en cinco capas

| capa | función | sobreyección |
|---|---|---|
| 0 | `unpair : Nat → Nat × Nat` | `unpair_surj` |
| 1 | `natToList : Nat → List Nat` | `natToList_surj` |
| 2 | `natToString : Nat → String` | `natToString_surj` |
| 3 | `natToTerm` / `natToTerms` | `natToTerm_surj` / `natToTerms_surj` |
| 4 | `natToFormula : Nat → Formula` | `natToFormula_surj` |

⭐ **La capa 0 evita la aritmética de los números triangulares.** El par de Cantor habitual
(`n ↦ (a,b)` con `n = (a+b)(a+b+1)/2 + b`) obliga a probar identidades con división entera,
que sin Mathlib es caro. En vez de eso `unpair` **camina la diagonal** paso a paso:

    (0,0) (1,0) (0,1) (2,0) (1,1) (0,2) (3,0) …

y entonces la sobreyectividad es una inducción doble sobre `(suma, segundo)`, sin una sola
división. Es la misma función matemática, con la recursión puesta donde la prueba la quiere.

⚠️ **Las capas 1, 3 y 4 son recursión BIEN FUNDADA, no estructural**: `natToList (n+1)` llama a
`natToList (unpair n).2`, y `(unpair n).2` no es un subtérmino de `n+1`. La cota que lo salva es
`unpair_sum_le : (unpair n).1 + (unpair n).2 ≤ n` — la única propiedad cuantitativa de `unpair`
que este fichero necesita.

⚠️ **Las sobreyectividades de las capas 3 y 4 NO son inducción sobre `Term`/`Formula`**, sino
sobre un TAMAÑO (`termSize`/`formulaSize`), con el patrón `∀ N, ∀ t, size t < N → …` que ya usa
`truth_lemma_lt`. Así se esquiva el recursor del inductivo ANIDADO (`Term` contiene `List Term`)
sin construir a mano un principio de inducción mutua.

## Footprint

Cero axiomas del proyecto. Todo lo que se usa de fuera es núcleo de Lean:
`Char.ofNat_toNat` y `String.ofList_toList`.

## ⚠️ Hay una SEGUNDA ruta, también compilada, y más corta

`../ROBINSON_PlusPlus/sondeos/EnumFormulaPorInyeccion.lean` hace lo contrario: define un
codificador **inyectivo** `codeNat : Formula → Nat` y obtiene la enumeración como
`noncomputable def formula_enum n := if h : ∃ f, codeNat f = n then h.choose else ⊥`. **102
líneas** en vez de ~330, mismo footprint.

Se adoptó ésta, y la razón conviene que quede escrita: aquélla da una sobreyección **semántica**
—`formula_enum` no computa nada—, y ésta da una **efectiva**, que es la que un proyecto sobre
representabilidad y conjuntos r.e. quiere tener. `#eval (List.range 12).map natToFormula` funciona.
El precio son 230 líneas. ⬜ Si el propietario prefiere la corta, el cambio es de una línea en
`cuarentena/Completeness.lean`.
-/

namespace FOL.Metamath.Enumeration

-- ============================================================
-- Capa 0 · el par de Cantor, recorrido estructuralmente
-- ============================================================

/-- Inversa del par de Cantor, definida como un PASEO por la diagonal: cada paso baja el
primer componente y sube el segundo, y al agotarse la diagonal salta a la siguiente.
Produce `(0,0) (1,0) (0,1) (2,0) (1,1) (0,2) (3,0) …` -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    match unpair n with
    | (a + 1, b) => (a, b + 1)
    | (0, b)     => (b + 1, 0)

theorem unpair_step_down {n a b : Nat} (h : unpair n = (a + 1, b)) :
    unpair (n + 1) = (a, b + 1) := by simp [unpair, h]

theorem unpair_step_next {n b : Nat} (h : unpair n = (0, b)) :
    unpair (n + 1) = (b + 1, 0) := by simp [unpair, h]

/-- El paseo alcanza toda la diagonal `s`, de arriba abajo. Inducción doble: sobre la suma
`s` y, dentro, sobre el segundo componente `b`. -/
theorem unpair_reach : ∀ s b : Nat, b ≤ s → ∃ n, unpair n = (s - b, b) := by
  intro s
  induction s with
  | zero => intro b hb; have : b = 0 := Nat.le_zero.mp hb; subst this; exact ⟨0, rfl⟩
  | succ s ih =>
      intro b
      induction b with
      | zero =>
          intro _
          obtain ⟨m, hm⟩ := ih s (Nat.le_refl s)
          rw [Nat.sub_self] at hm
          exact ⟨m + 1, by simpa using unpair_step_next hm⟩
      | succ b ihb =>
          intro hb
          obtain ⟨n, hn⟩ := ihb (by omega)
          have e : s + 1 - b = (s - b) + 1 := by omega
          rw [e] at hn
          exact ⟨n + 1, by simpa using unpair_step_down hn⟩

theorem unpair_surj (a b : Nat) : ∃ n, unpair n = (a, b) := by
  obtain ⟨n, hn⟩ := unpair_reach (a + b) b (by omega)
  have h : a + b - b = a := by omega
  rw [h] at hn
  exact ⟨n, hn⟩

/-- La ÚNICA propiedad cuantitativa de `unpair` que hace falta: es lo que permite la recursión
bien fundada de las capas 1, 3 y 4. -/
theorem unpair_sum_le : ∀ n : Nat, (unpair n).1 + (unpair n).2 ≤ n := by
  intro n
  induction n with
  | zero => simp [unpair]
  | succ n ih =>
      cases h : unpair n with
      | mk a b =>
        simp only [h] at ih
        cases a with
        | zero =>
            rw [unpair_step_next h]
            omega
        | succ k =>
            rw [unpair_step_down h]
            omega

theorem unpair_fst_le (n : Nat) : (unpair n).1 ≤ n := by
  have := unpair_sum_le n; omega

theorem unpair_snd_le (n : Nat) : (unpair n).2 ≤ n := by
  have := unpair_sum_le n; omega

-- ============================================================
-- Capa 1 · listas de naturales
-- ============================================================

def natToList : Nat → List Nat
  | 0 => []
  | n + 1 => (unpair n).1 :: natToList (unpair n).2
  termination_by n => n
  decreasing_by
    have := unpair_snd_le n; omega

theorem natToList_surj : ∀ L : List Nat, ∃ n, natToList n = L := by
  intro L
  induction L with
  | nil => exact ⟨0, by simp [natToList]⟩
  | cons a L' ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨k, hk⟩ := unpair_surj a m
      exact ⟨k + 1, by simp [natToList, hk, hm]⟩

-- ============================================================
-- Capa 2 · caracteres y cadenas
-- ============================================================

theorem map_ofNat_toNat : ∀ L : List Char, (L.map Char.toNat).map Char.ofNat = L := by
  intro L
  induction L with
  | nil => rfl
  | cons c L' ih => simp [ih, Char.ofNat_toNat]

def natToString (n : Nat) : String := String.ofList ((natToList n).map Char.ofNat)

theorem natToString_surj (s : String) : ∃ n, natToString n = s := by
  obtain ⟨n, hn⟩ := natToList_surj (s.toList.map Char.toNat)
  refine ⟨n, ?_⟩
  simp only [natToString, hn, map_ofNat_toNat, String.ofList_toList]

/-- ⭐ `String` satisface `FOL.EnumSym` con lo que esta capa ya tiene probado (ADR-069). -/
instance : FOL.EnumSym String where
  enum := natToString
  enum_surj := natToString_surj

/-- ⭐⭐ Y `List Char` la satisface **más barato**, saliendo de la **capa 1**
(`natToList_surj`, sobre `List Nat`) más `map_ofNat_toNat`: **no toca `String` en absoluto**.
⇒ el día que la metateoría se instancie en `List Char`, el `Classical.choice` que hoy entra por
DESCOMPONER un `String` no entra por esta puerta. Contéjese con la instancia de arriba:
`#print axioms` las separa. -/
instance : FOL.EnumSym (List Char) where
  enum n := (natToList n).map Char.ofNat
  enum_surj := by
    intro s
    obtain ⟨n, hn⟩ := natToList_surj (s.map Char.toNat)
    refine ⟨n, ?_⟩
    rw [hn]
    exact map_ofNat_toNat s

-- ============================================================
-- Capa 3 · términos
-- ============================================================

mutual
def natToTerm : Nat → Term
  | 0 => .var 0
  | n + 1 =>
      if (unpair n).1 = 0 then
        .var (unpair n).2
      else
        .func (natToString (unpair (unpair n).2).1) (natToTerms (unpair (unpair n).2).2)
  termination_by n => n
  decreasing_by
    all_goals
      (have a2 := unpair_snd_le n
       have _a3 := unpair_fst_le (unpair n).2
       have a4 := unpair_snd_le (unpair n).2
       omega)

def natToTerms : Nat → List Term
  | 0 => []
  | n + 1 => natToTerm (unpair n).1 :: natToTerms (unpair n).2
  termination_by n => n
  decreasing_by
    all_goals
      (have a1 := unpair_fst_le n
       have a2 := unpair_snd_le n
       omega)
end

mutual
def termSize : Term → Nat
  | .var _ => 0
  | .func _ ts => termsSize ts + 1

def termsSize : List Term → Nat
  | [] => 0
  | t :: ts => termSize t + termsSize ts + 1
end

/-- Sobreyectividad de las capas de términos, por INDUCCIÓN SOBRE UNA COTA de tamaño.
⚠️ No es inducción sobre `Term`: `Term` es un inductivo ANIDADO (contiene `List Term`) y
haría falta un principio de inducción mutua escrito a mano. La cota lo evita. -/
theorem term_surj_aux : ∀ N : Nat,
    (∀ t : Term, termSize t < N → ∃ n, natToTerm n = t) ∧
    (∀ ts : List Term, termsSize ts < N → ∃ n, natToTerms n = ts) := by
  intro N
  induction N with
  | zero =>
      exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih =>
      obtain ⟨ihT, ihTs⟩ := ih
      constructor
      · intro t hlt
        cases t with
        | var k =>
            obtain ⟨m, hm⟩ := unpair_surj 0 k
            exact ⟨m + 1, by simp [natToTerm, hm]⟩
        | func f ts =>
            have hts : termsSize ts < N := by simp only [termSize] at hlt; omega
            obtain ⟨nts, hnts⟩ := ihTs ts hts
            obtain ⟨nf, hnf⟩ := natToString_surj f
            obtain ⟨r, hr⟩ := unpair_surj nf nts
            obtain ⟨m, hm⟩ := unpair_surj 1 r
            exact ⟨m + 1, by simp [natToTerm, hm, hr, hnf, hnts]⟩
      · intro ts hlt
        cases ts with
        | nil => exact ⟨0, by simp [natToTerms]⟩
        | cons t ts' =>
            have h1 : termSize t < N := by simp only [termsSize] at hlt; omega
            have h2 : termsSize ts' < N := by simp only [termsSize] at hlt; omega
            obtain ⟨a, ha⟩ := ihT t h1
            obtain ⟨b, hb⟩ := ihTs ts' h2
            obtain ⟨m, hm⟩ := unpair_surj a b
            exact ⟨m + 1, by simp [natToTerms, hm, ha, hb]⟩

theorem natToTerm_surj (t : Term) : ∃ n, natToTerm n = t :=
  (term_surj_aux (termSize t + 1)).1 t (by omega)

theorem natToTerms_surj (ts : List Term) : ∃ n, natToTerms n = ts :=
  (term_surj_aux (termsSize ts + 1)).2 ts (by omega)

-- ============================================================
-- Capa 4 · fórmulas
-- ============================================================

def formulaSize : Formula → Nat
  | .bottom => 0
  | .atom _ _ => 0
  | .eq _ _ => 0
  | .impl f1 f2 => max (formulaSize f1) (formulaSize f2) + 1
  | .forall f1 => formulaSize f1 + 1
  | .and f1 f2 => max (formulaSize f1) (formulaSize f2) + 1
  | .or f1 f2 => max (formulaSize f1) (formulaSize f2) + 1
  | .ex f1 => formulaSize f1 + 1

/-- La enumeración de fórmulas. El primer componente de `unpair n` es la ETIQUETA del
constructor (0…7) y el segundo lleva los argumentos, repartidos otra vez con `unpair`
cuando el constructor es binario. -/
def natToFormula : Nat → Formula
  | 0 => .bottom
  | n + 1 =>
      if (unpair n).1 = 0 then .bottom
      else if (unpair n).1 = 1 then
        .atom (natToString (unpair (unpair n).2).1) (natToTerms (unpair (unpair n).2).2)
      else if (unpair n).1 = 2 then
        .eq (natToTerm (unpair (unpair n).2).1) (natToTerm (unpair (unpair n).2).2)
      else if (unpair n).1 = 3 then
        .impl (natToFormula (unpair (unpair n).2).1) (natToFormula (unpair (unpair n).2).2)
      else if (unpair n).1 = 4 then
        .forall (natToFormula (unpair n).2)
      else if (unpair n).1 = 5 then
        .and (natToFormula (unpair (unpair n).2).1) (natToFormula (unpair (unpair n).2).2)
      else if (unpair n).1 = 6 then
        .or (natToFormula (unpair (unpair n).2).1) (natToFormula (unpair (unpair n).2).2)
      else
        .ex (natToFormula (unpair n).2)
  termination_by n => n
  decreasing_by
    all_goals
      (have a2 := unpair_snd_le n
       have a3 := unpair_fst_le (unpair n).2
       have a4 := unpair_snd_le (unpair n).2
       omega)

theorem formula_surj_aux :
    ∀ N : Nat, ∀ f : Formula, formulaSize f < N → ∃ n, natToFormula n = f := by
  intro N
  induction N with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro f hlt
      cases f with
      | bottom => exact ⟨0, by simp [natToFormula]⟩
      | atom p ts =>
          obtain ⟨np, hnp⟩ := natToString_surj p
          obtain ⟨nts, hnts⟩ := natToTerms_surj ts
          obtain ⟨r, hr⟩ := unpair_surj np nts
          obtain ⟨m, hm⟩ := unpair_surj 1 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, hnp, hnts]⟩
      | eq t1 t2 =>
          obtain ⟨n1, h1⟩ := natToTerm_surj t1
          obtain ⟨n2, h2⟩ := natToTerm_surj t2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 2 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | impl f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 3 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | «forall» f1 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨m, hm⟩ := unpair_surj 4 n1
          exact ⟨m + 1, by simp [natToFormula, hm, h1]⟩
      | and f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 5 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | or f1 f2 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          have e2 : formulaSize f2 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨n2, h2⟩ := ih f2 e2
          obtain ⟨r, hr⟩ := unpair_surj n1 n2
          obtain ⟨m, hm⟩ := unpair_surj 6 r
          exact ⟨m + 1, by simp [natToFormula, hm, hr, h1, h2]⟩
      | ex f1 =>
          have e1 : formulaSize f1 < N := by simp only [formulaSize] at hlt; omega
          obtain ⟨n1, h1⟩ := ih f1 e1
          obtain ⟨m, hm⟩ := unpair_surj 7 n1
          exact ⟨m + 1, by simp [natToFormula, hm, h1]⟩

/-- ⭐ **El teorema que retira los dos axiomas**: toda fórmula aparece en la enumeración. -/
theorem natToFormula_surj (f : Formula) : ∃ n, natToFormula n = f :=
  formula_surj_aux (formulaSize f + 1) f (by omega)

end FOL.Metamath.Enumeration
