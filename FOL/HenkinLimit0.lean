/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Fresh0, FOL.Enumeration
-- @axiom_system: classical
-- @importance: high

import FOL.Fresh0
import FOL.Enumeration

/-!
# `FOL.HenkinLimit0` — **la iteración ω**: la extensión de Henkin, entera

Pieza (2) del ensamblaje de
`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4, y con ella la extensión de
Henkin queda **construida y consistente**:

    henLimit_consistent₀ : IsConsistent₀ S → IsConsistent₀ (henLimit S)
    henLimit_witness    : ∀ A, ∃ c, henLimit S (henkinAx c A)

Es decir: toda teoría consistente se extiende a una consistente **con testigo para cada fórmula**.
Lo que faltaba para la vía W —Lindenbaum y el modelo canónico— está en `FOL.Lindenbaum0`/`FOL.Canonical0`.

## La construcción

`hen S 0 := shiftTheory S` (la teoría metida en el sublenguaje, `FOL.Fresh0`), y

    hen S (n+1) := hen S n ∪ { henkinAx (cst (hidx n)) (natToFormula n) }

recorriendo **todas** las fórmulas por la enumeración de `FOL.Enumeration`. El límite es la unión.

## ⭐ El punto que §6.4 marcaba en rojo, y cómo se resolvió

El plan daba a esta pieza **riesgo medio**: `cₙ` tiene que ser fresca para `φₙ`, y `φₙ` recorre
todas las fórmulas, así que puede mencionar cualquier `cst m` — «no vale `cₙ := cst n`». Cierto.
La solución prevista era una función `Formula → Nat` («mayor índice usado»), ~40 líneas.

⭐ **No ha hecho falta.** `cst_bound_formula` (`FOL.Fresh0` §4) da, para cada fórmula, un índice a
partir del cual **todas** las constantes son frescas; eso es un `∃`, y `Exists.choose` lo convertía
(hasta el 2026‑09‑27: ver la rectificación de abajo)
en la función `bnd`. El índice del turno es entonces

    hidx 0 := bnd (natToFormula 0)     hidx (n+1) := max (hidx n + 1) (bnd (natToFormula (n+1)))

que es **estrictamente creciente** —de ahí `cₙ ≠ cᵢ` para `i < n`, por `cst_inj`— y **domina las
cotas de todas las fórmulas anteriores** —de ahí la frescura en `φᵢ` para `i ≤ n`—. Dos
propiedades, una definición, sin invertir `cst`.

🔑 *El enunciado correcto no era «el máximo índice usado» sino «a partir de cierto índice, todas
valen». El primero obliga a leer los nombres; el segundo, no.*

⚠️ **Rectificación, 2026‑09‑27** (auditoría de constructividad). `bnd` ya no es `Exists.choose`: se
CALCULA por recursión sobre la fórmula —el mayor `utf8ByteSize` de sus símbolos de función—, y
`bnd_spec` sale de contar bytes (`cst m` ocupa `m + 1`). (✏️ 2026‑10‑05, D7: hoy la mayor LONGITUD, y
`bnd_spec` cuenta caracteres: `Fresh0.cst_length`.) O sea: la función `Formula → Nat` acabó
escribiéndose, pero por otra razón —quitar el `Classical.choice`—, y con el enunciado de COTA, no de
índice. El 🔑 de arriba sigue en pie: `bnd` **mide** los nombres, no los **lee** (no invierte `cst`
ni averigua qué `cst m` aparece).

## Qué hace cada sección

1. **§1** — las dos conmutaciones de `occursFormula` que faltaban: el **lift** no cambia los
   símbolos, y la **sustitución** sólo puede meter los del término sustituido. De ahí
   `not_occurs_henkinAx`: una constante distinta del testigo, y fresca en `A`, es fresca en
   `henkinAx d A`. ⭐ **Net‑0 puro** — no depende de ningún axioma.
2. **§2** — la cota `bnd`, **calculada** por recursión (`bndTerm`, `bndTerms`: la mayor longitud
   de un símbolo de función; hasta D7, el mayor `utf8ByteSize`), su especificación `bnd_spec` (vía
   `cst_ne_of_size`: un símbolo de `k` caracteres no es `cst m` para ningún `m ≥ k`), y `hidx`, con
   las dos propiedades.
   ⭐ Desde el 2026‑09‑27 `bnd`, `hidx` y `hen` son **computables** (hasta entonces
   `noncomputable`): `hidx 5` se evalúa con `#eval`.
3. **§3** — la cadena, su monotonía, su frescura y su **consistencia**, que es `henkin_step_consistent₀`
   (ADR‑037) aplicado `n` veces.
4. **§4** — el límite. ⭐ Su consistencia sale **de la definición de `DerivesSet₀`**: una derivación
   usa un contexto **finito**, luego vive en algún `hen S N`. *La compacidad sintáctica metida en la
   definición vuelve a pagar.*

## 📏 Footprint

⭐ **Ninguna constante de `FOL.HenkinLimit0` lleva `Classical.choice`, y ninguna es
`noncomputable`** (auditoría de constructividad, 2026‑09‑27, medido sobre el entorno compilado:
`auditoria/constructividad-2026-09-27/despues/`):

* **ningún axioma**: §1 entero (`occursTerm_lift`, `occursTerms_lift`, `not_occurs_substTerm`,
  `not_occurs_substTerms`, `not_occurs_substFormula`, `not_occurs_henkinAx`) y la cota `bndTerm`,
  `bndTerms`, `bnd`;
* `[propext, Quot.sound]`: todo lo demás salvo el auxiliar privado `bnd_pair` (`[propext]`)
  —`cst_ne_of_size`, `bndTerm_spec`, `bndTerms_spec`,
  `bnd_spec`, `hidx` y sus lemas, `hen`, `hen_mono`, `hen_fresh`, `hen_fresh_at`, `hen_consistent`,
  `henLimit`, `shiftTheory_sub_henLimit`, `henLimit_finite`, `henLimit_consistent₀`,
  `henLimit_witness`—.

**Cero axiomas del proyecto.**

✏️ 2026‑10‑05: esa medición es la de `String`. Tras D7 (ADR‑129 de RPP) se midieron de nuevo las
filas de `../ROBINSON_PlusPlus/check-footprints.bash`: `not_occurs_henkinAx`, ningún axioma;
`hen_consistent`, `henLimit_consistent₀` y `henLimit_witness`, `[propext, Quot.sound]`. Sin
`Classical.choice`, como antes. Lo que no tiene fila lleva la cifra del 2026‑09‑27, sin volver a
medirla con `List Char`.

⚠️⚠️ **Hasta el 2026‑09‑27 esta sección decía** `[propext, Classical.choice, Quot.sound]`, con el
`Classical.choice` entrando «por `Exists.choose` en `bnd` (§2), por `String` (§7 del plan) y por lo
que ya traen `shiftTheory_consistent₀` (`Rename.invOf`) y `henkin_step_consistent₀`», y que «no es
el de la completitud — ése es el `if IsConsistent …` de Lindenbaum». Ninguna de esas vías era
necesaria, y se retiraron: `bnd` calculada (§2); `Fresh0.unshift` en lugar de `invOf`; el
`ctx_split` de `FOL.Henkin0` en lugar del `filter` bajo `open Classical`; `of_decide_eq_false` en
`Fresh0.cst_zero_ne`/`cst_ne_shift` y `String.exists_eq_ofList` en la sobreyectividad de
`FOL.Enumeration` (lo de `String` era DECODIFICAR UTF‑8; ✏️ 2026‑10‑05: desde D7 no hay `String`, y
la sobreyectividad es `natToSym_surj`). Y la segunda mitad también era falsa: la
etapa de Lindenbaum ya no decide nada — ver `FOL.Lindenbaum0`.
-/

namespace FOL.HenkinLimit0

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0
open FOL.Metamath.Enumeration

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- §1 · `occursFormula` frente a `lift` y `subst`
-- ============================================================

-- ⭐ El lift mueve **índices**, no **símbolos**.
mutual
theorem occursTerm_lift (c : List Char) : ∀ (k : Nat) (t : Term),
    occursTerm c (liftTerm k t) → occursTerm c t
  | _, .var _ => by
      simp only [liftTerm]
      split <;> exact fun h => h.elim
  | k, .func _ ts => fun h =>
      h.elim Or.inl (fun ht => Or.inr (occursTerms_lift c k ts ht))

theorem occursTerms_lift (c : List Char) : ∀ (k : Nat) (ts : List Term),
    occursTerms c (liftTerms k ts) → occursTerms c ts
  | _, [] => fun h => h
  | k, t :: ts => fun h =>
      h.elim (fun ht => Or.inl (occursTerm_lift c k t ht))
             (fun hts => Or.inr (occursTerms_lift c k ts hts))
end

-- ⭐ Sustituir sólo puede introducir los símbolos del término que se sustituye.
mutual
theorem not_occurs_substTerm (c : List Char) : ∀ (v : Nat) (s t : Term),
    Not (occursTerm c s) → Not (occursTerm c t) → Not (occursTerm c (substTerm v s t))
  | _, _, .var _ => by
      intro hs _
      simp only [substTerm]
      split
      · exact hs
      · split <;> exact fun h => h.elim
  | v, s, .func _ ts => by
      intro hs ht h
      cases h with
      | inl he => exact ht (Or.inl he)
      | inr hts => exact not_occurs_substTerms c v s ts hs (fun k => ht (Or.inr k)) hts

theorem not_occurs_substTerms (c : List Char) : ∀ (v : Nat) (s : Term) (ts : List Term),
    Not (occursTerm c s) → Not (occursTerms c ts) → Not (occursTerms c (substTerms v s ts))
  | _, _, [] => fun _ _ h => h
  | v, s, t :: ts => by
      intro hs hts h
      cases h with
      | inl h1 => exact not_occurs_substTerm c v s t hs (fun k => hts (Or.inl k)) h1
      | inr h2 => exact not_occurs_substTerms c v s ts hs (fun k => hts (Or.inr k)) h2
end

theorem not_occurs_substFormula (c : List Char) : ∀ (f : Formula) (v : Nat) (s : Term),
    Not (occursTerm c s) → Not (occursFormula c f) →
    Not (occursFormula c (substFormula v s f)) := by
  intro f
  induction f with
  | bottom => intro _ _ _ _ h; exact h
  | atom _ ts => intro v s hs hf; exact not_occurs_substTerms c v s ts hs hf
  | eq t u =>
      intro v s hs hf h
      exact h.elim (not_occurs_substTerm c v s t hs (fun k => hf (Or.inl k)))
                   (not_occurs_substTerm c v s u hs (fun k => hf (Or.inr k)))
  | impl _ _ iha ihb =>
      intro v s hs hf h
      exact h.elim (iha v s hs (fun k => hf (Or.inl k))) (ihb v s hs (fun k => hf (Or.inr k)))
  | «forall» _ ih =>
      intro v s hs hf
      exact ih (v + 1) (liftTerm 0 s) (fun k => hs (occursTerm_lift c 0 s k)) hf
  | and _ _ iha ihb =>
      intro v s hs hf h
      exact h.elim (iha v s hs (fun k => hf (Or.inl k))) (ihb v s hs (fun k => hf (Or.inr k)))
  | or _ _ iha ihb =>
      intro v s hs hf h
      exact h.elim (iha v s hs (fun k => hf (Or.inl k))) (ihb v s hs (fun k => hf (Or.inr k)))
  | ex _ ih =>
      intro v s hs hf
      exact ih (v + 1) (liftTerm 0 s) (fun k => hs (occursTerm_lift c 0 s k)) hf

/-- ⭐ **Lo que la cadena necesita de los axiomas ya añadidos**: una constante distinta del
testigo y fresca en `A` es fresca en `henkinAx d A`. **Net‑0 puro.** -/
theorem not_occurs_henkinAx {c d : List Char} {A : Formula}
    (hcd : c ≠ d) (hA : Not (occursFormula c A)) : Not (occursFormula c (henkinAx d A)) := by
  intro h
  cases h with
  | inl hex => exact hA hex
  | inr hsub =>
      refine not_occurs_substFormula c A 0 (Term.func d []) ?_ hA hsub
      intro hc
      cases hc with
      | inl he => exact hcd he.symm
      | inr hz => exact hz

-- ============================================================
-- §2 · El índice del testigo de cada turno
-- ============================================================

/-- Un símbolo de `k` caracteres no es `cst m` para ningún `m ≥ k`: sólo contar caracteres
(`Fresh0.cst_length`; hasta D7, 2026‑10‑05, bytes). -/
theorem cst_ne_of_size {s : List Char} {m : Nat} (hm : s.length ≤ m) : cst m ≠ s := by
  intro h
  have h1 : m + 1 = s.length :=
    (cst_length m).symm.trans (congrArg List.length h)
  exact Nat.not_succ_le_self m (Nat.le_trans (Nat.le_of_eq h1) hm)

mutual
/-- La mayor longitud de un símbolo de función del término (hasta D7, en bytes). -/
def bndTerm : Term → Nat
  | .var _ => 0
  | .func s ts => max s.length (bndTerms ts)

def bndTerms : List Term → Nat
  | [] => 0
  | t :: ts => max (bndTerm t) (bndTerms ts)
end

/-- ⭐ **La cota, CALCULADA**: la mayor longitud de un símbolo de función de la fórmula (hasta D7,
2026‑10‑05, el mayor tamaño en bytes). A
partir de ahí ninguna `cst m` aparece (`bnd_spec`). Hasta el 2026‑09‑27 era
`(cst_bound_formula f).choose`, `noncomputable` y con `Classical.choice`; su docstring decía que
«no es evitable con este enunciado»: lo era (auditoría de constructividad). -/
def bnd : Formula → Nat
  | .bottom => 0
  | .atom _ ts => bndTerms ts
  | .eq t u => max (bndTerm t) (bndTerm u)
  | .impl a b => max (bnd a) (bnd b)
  | .forall a => bnd a
  | .and a b => max (bnd a) (bnd b)
  | .or a b => max (bnd a) (bnd b)
  | .ex a => bnd a

mutual
theorem bndTerm_spec : ∀ (t : Term) (m : Nat), bndTerm t ≤ m → Not (occursTerm (cst m) t)
  | .var _, _, _ => fun h => h
  | .func s ts, m, hm => fun h => by
      cases h with
      | inl he => exact cst_ne_of_size (Nat.le_trans (Nat.le_max_left _ _) hm) he.symm
      | inr ht => exact bndTerms_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) ht

theorem bndTerms_spec : ∀ (ts : List Term) (m : Nat), bndTerms ts ≤ m →
    Not (occursTerms (cst m) ts)
  | [], _, _ => fun h => h
  | t :: ts, m, hm => fun h => by
      cases h with
      | inl ht => exact bndTerm_spec t m (Nat.le_trans (Nat.le_max_left _ _) hm) ht
      | inr hts => exact bndTerms_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) hts
end

private theorem bnd_pair {P Q : Prop} {a b m : Nat} (h1 : a ≤ m → Not P) (h2 : b ≤ m → Not Q)
    (hm : max a b ≤ m) : Not (Or P Q) := fun h =>
  h.elim (h1 (Nat.le_trans (Nat.le_max_left _ _) hm)) (h2 (Nat.le_trans (Nat.le_max_right _ _) hm))

theorem bnd_spec (f : Formula) : ∀ m, bnd f ≤ m → Not (occursFormula (cst m) f) := by
  induction f with
  | bottom => exact fun _ _ h => h
  | atom _ ts => exact bndTerms_spec ts
  | eq t u => exact fun m hm => bnd_pair (bndTerm_spec t m) (bndTerm_spec u m) hm
  | impl _ _ iha ihb => exact fun m hm => bnd_pair (iha m) (ihb m) hm
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun m hm => bnd_pair (iha m) (ihb m) hm
  | or _ _ iha ihb => exact fun m hm => bnd_pair (iha m) (ihb m) hm
  | ex _ ih => exact ih

/-- El índice de la constante que atestigua `natToFormula n`.

⭐ Las dos propiedades que lo definen están en la definición misma: `hidx n + 1` fuerza el
**crecimiento estricto** (⇒ testigos distintos), y `bnd (natToFormula (n+1))` fuerza que **domine
la cota** (⇒ frescura en la fórmula del turno). -/
def hidx : Nat → Nat
  | 0 => bnd (natToFormula 0)
  | n + 1 => max (hidx n + 1) (bnd (natToFormula (n + 1)))

theorem hidx_ge : ∀ n, bnd (natToFormula n) ≤ hidx n
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

theorem hidx_step (n : Nat) : hidx n < hidx (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)

theorem hidx_mono : ∀ {i n : Nat}, i < n → hidx i < hidx n
  | i, 0, h => absurd h (Nat.not_lt_zero i)
  | i, n + 1, h => by
      cases Nat.lt_or_ge i n with
      | inl hlt => exact Nat.lt_trans (hidx_mono hlt) (hidx_step n)
      | inr hge => exact (Nat.le_antisymm (Nat.le_of_lt_succ h) hge) ▸ hidx_step n

theorem hidx_ge_of_le {i n : Nat} (h : i ≤ n) : bnd (natToFormula i) ≤ hidx n := by
  cases Nat.lt_or_ge i n with
  | inl hlt => exact Nat.le_trans (hidx_ge i) (Nat.le_of_lt (hidx_mono hlt))
  | inr hge => exact (Nat.le_antisymm h hge) ▸ hidx_ge i

-- ============================================================
-- §3 · La cadena, y su consistencia
-- ============================================================

/-- `hen S n` es `shiftTheory S` más los `n` primeros axiomas de Henkin. -/
def hen (S : Formula → Prop) : Nat → Formula → Prop
  | 0 => shiftTheory S
  | n + 1 => fun x => Or (hen S n x) (x = henkinAx (cst (hidx n)) (natToFormula n))

theorem hen_mono (S : Formula → Prop) : ∀ {i n : Nat}, i ≤ n → ∀ x, hen S i x → hen S n x
  | _, 0, h, _, hx => (Nat.le_zero.mp h) ▸ hx
  | i, n + 1, h, x, hx => by
      cases Nat.lt_or_ge i (n + 1) with
      | inl hlt => exact Or.inl (hen_mono S (Nat.le_of_lt_succ hlt) x hx)
      | inr hge => exact (Nat.le_antisymm h hge) ▸ hx

/-- Frescura en toda la etapa `n`, con las dos condiciones que la hacen posible: no coincidir con
ningún testigo anterior, y ser fresca en las fórmulas ya atestiguadas.
⭐ Sobre `shiftTheory S` no hace falta ninguna: `shiftTheory_fresh` es incondicional. -/
theorem hen_fresh (S : Formula → Prop) (m : Nat) : ∀ (n : Nat),
    (∀ i, i < n → m ≠ hidx i) →
    (∀ i, i < n → Not (occursFormula (cst m) (natToFormula i))) →
    ∀ g, hen S n g → Not (occursFormula (cst m) g)
  | 0, _, _, g, hg => shiftTheory_fresh m g hg
  | n + 1, hne, hfr, g, hg => by
      cases hg with
      | inl h =>
          exact hen_fresh S m n (fun i hi => hne i (Nat.lt_succ_of_lt hi))
            (fun i hi => hfr i (Nat.lt_succ_of_lt hi)) g h
      | inr he =>
          subst he
          refine not_occurs_henkinAx ?_ (hfr n (Nat.lt_succ_self n))
          intro hc
          exact hne n (Nat.lt_succ_self n) (cst_inj m (hidx n) hc)

/-- ⭐ Y las dos condiciones se descargan **de la definición de `hidx`**: el crecimiento estricto
da la primera, la dominación de cotas la segunda. -/
theorem hen_fresh_at (S : Formula → Prop) (n : Nat) :
    ∀ g, hen S n g → Not (occursFormula (cst (hidx n)) g) :=
  hen_fresh S (hidx n) n
    (fun _ hi => Nat.ne_of_gt (hidx_mono hi))
    (fun i hi => bnd_spec (natToFormula i) (hidx n) (hidx_ge_of_le (Nat.le_of_lt hi)))

/-- ⭐⭐ **Cada etapa es consistente** — `henkin_step_consistent₀` (ADR‑037) aplicado `n` veces. -/
theorem hen_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (hen S n)
  | 0 => shiftTheory_consistent₀ hCons
  | n + 1 =>
      henkin_step_consistent₀ (hen_consistent hCons n) (cst (hidx n)) (natToFormula n)
        (hen_fresh_at S n) (bnd_spec (natToFormula n) (hidx n) (hidx_ge n))

-- ============================================================
-- §4 · ⭐⭐ El límite
-- ============================================================

/-- La unión de la cadena: **la extensión de Henkin** de `S`. -/
def henLimit (S : Formula → Prop) : Formula → Prop := fun x => ∃ n, hen S n x

theorem shiftTheory_sub_henLimit (S : Formula → Prop) : ∀ g, shiftTheory S g → henLimit S g :=
  fun _ h => ⟨0, h⟩

/-- ⭐ Un contexto **finito** dentro del límite vive ya en una etapa. Es la mitad de la
compacidad, y sale por inducción sobre la lista con `max`. -/
theorem henLimit_finite (S : Formula → Prop) : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → henLimit S g) → ∃ N, ∀ g, g ∈ Γ → hen S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨n, hn⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := henLimit_finite S Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max n N, fun x hx => ?_⟩
      cases hx with
      | head => exact hen_mono S (Nat.le_max_left _ _) g hn
      | tail _ hx' => exact hen_mono S (Nat.le_max_right _ _) x (hN x hx')

/-- ⭐⭐ **La extensión de Henkin de una teoría consistente es consistente.**

🔑 La prueba es de tres líneas **porque `DerivesSet₀` lleva la compacidad sintáctica dentro**: una
derivación desde el límite usa un contexto finito, luego ya derivaba desde una etapa. -/
theorem henLimit_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (henLimit S) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨N, hN⟩ := henLimit_finite S Γ hΓ
  exact hen_consistent hCons N ⟨Γ, hN, hD⟩

/-- ⭐⭐ **Y tiene testigo para TODA fórmula** — aquí es donde paga la enumeración construida en
`FOL.Enumeration` (ADR‑030). -/
theorem henLimit_witness (S : Formula → Prop) (A : Formula) :
    ∃ c : List Char, henLimit S (henkinAx c A) := by
  obtain ⟨n, hn⟩ := natToFormula_surj A
  exact ⟨cst (hidx n), n + 1, Or.inr (by rw [hn])⟩

end FOL.HenkinLimit0

#print axioms FOL.HenkinLimit0.not_occurs_henkinAx
#print axioms FOL.HenkinLimit0.hen_consistent
#print axioms FOL.HenkinLimit0.henLimit_consistent₀
#print axioms FOL.HenkinLimit0.henLimit_witness
