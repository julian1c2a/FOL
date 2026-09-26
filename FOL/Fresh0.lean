/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Henkin0, FOL.Rename
-- @axiom_system: classical
-- @importance: high

import FOL.SymClasses
import FOL.Henkin0
import FOL.Rename

/-!
# `FOL.Fresh0` — **el suministro de constantes frescas**

Pieza (1) del ensamblaje de `doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4. `henkin_step_consistent`
(ADR‑037) pide una constante `c` fresca **en la teoría y en la fórmula**; para una teoría
`S : Formula → Prop` **arbitraria** no tiene por qué haber ninguna: `S` puede usar todas las
cadenas. Este módulo fabrica el suministro por el camino clásico.

## La construcción, en dos movimientos

1. **Meter la teoría en un sublenguaje.** `shift s := "f" ++ s` renombra *todos* los símbolos de
   función. `shiftTheory S` es la imagen de `S`, y es **conservativa** en los dos sentidos
   (`derivesSet0_shift` / `derivesSet0_shift_inv`) y **equiconsistente**
   (`shiftTheory_consistent`).
2. **Las constantes nuevas.** `cst 0 = "g"`, `cst (n+1) = "a" ++ cst n` — infinitas, inyectiva, y
   **ninguna está en la imagen de `shift`** ⇒ `cst n` no aparece en ninguna fórmula desplazada.

## ⭐ Y el punto que §6.4 marcaba en rojo

El plan daba a la iteración ω **riesgo medio** por esto: `cₙ` tiene que ser fresca también para
`φₙ`, y `φₙ` recorre **todas** las fórmulas, así que puede mencionar cualquier `cst m`. La
solución prevista era una función `Formula → Nat` («mayor índice usado») con su lema, ~40 líneas.

⭐ **No hace falta esa función.** El enunciado que la iteración consume no es «el máximo índice»
sino «**a partir de cierto índice, todas son frescas**»:

    cst_bound_formula : ∀ f, ∃ N, ∀ m ≥ N, ¬ occursFormula (cst m) f

y eso sale por inducción estructural con `max`, sin invertir `cst` y sin tocar `String.length`.
El único punto clásico está en el **símbolo**: `∃ N, ∀ m ≥ N, cst m ≠ s` se decide por
`Classical.em (∃ k, cst k = s)`, y la inyectividad de `cst` hace el resto.

⇒ `exists_fresh` entrega la constante que el paso de Henkin pide, para la teoría desplazada
**más** cualquier lista finita de axiomas ya añadidos **más** la fórmula del turno.

## 📏 Footprint

`Classical.choice` entra, y **por dos vías distintas que conviene no confundir**:

* la **matemática**: `cst_bound_sym` usa el tercio excluso sobre `∃ k, cst k = s` (§4);
* la **implementación**: en Lean v4.31 comparar dos `String` con `≠` ya arrastra choice — el muro
  de `doc/PLAN-COMPLETITUD-FINITISTA.md` §7, que es deuda del núcleo y no de la lógica.

⚠️ Nada de esto es el `Classical.choice` de la completitud: ése es el `if IsConsistent …` de
Lindenbaum (§6.3), que entra más arriba en la cadena (`FOL.Lindenbaum0`).
-/

namespace FOL.Fresh0

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- §1 · El desplazamiento al sublenguaje
-- ============================================================

/-- Renombra **todo** símbolo de función `s` como `"f" ++ s`. ⚠️ Los símbolos de RELACIÓN no se
tocan (`renameFormula` no los toca): no hacen falta testigos para ellos. -/
def shift (s : String) : String := "f" ++ s

/-- ⭐ Una línea, porque `String.append_right_inj` **existe** en el núcleo. Medido en
`../ROBINSON_PlusPlus/sondeos/NombresFrescosMedicion.lean`. -/
theorem shift_inj : ∀ s t : String, shift s = shift t → s = t :=
  fun _ _ h => (String.append_right_inj "f").mp h

-- ============================================================
-- §2 · La familia infinita de constantes nuevas
-- ============================================================

/-- `"g"`, `"ag"`, `"aag"`, … Infinitas, e **inyectiva**. -/
def cst : Nat → String
  | 0 => "g"
  | n + 1 => "a" ++ cst n

/-- ⚠️ `not_eq_of_beq_eq_false rfl` con variables libres **parece imposible** y no lo es: `beq`
sobre `String` compara byte a byte **cortocircuitando** en el primero que difiere, y aquí ese byte
es el del literal. Verificado con control adversarial (el análogo FALSO **no compila**). -/
theorem cst_zero_ne (n : Nat) : cst 0 ≠ cst (n + 1) := not_eq_of_beq_eq_false rfl

/-- ⭐⭐ **Ninguna constante nueva está en la imagen del desplazamiento.** Es lo único que hay que
saber de los nombres: todo lo demás se deduce. -/
theorem cst_ne_shift : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, _ => not_eq_of_beq_eq_false rfl
  | _ + 1, _ => not_eq_of_beq_eq_false rfl

theorem cst_inj : ∀ m n : Nat, cst m = cst n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (cst_zero_ne _)
  | _ + 1, 0, h => absurd h.symm (cst_zero_ne _)
  | m + 1, n + 1, h => congrArg (· + 1) (cst_inj m n ((String.append_right_inj "a").mp h))

/-- ⭐ **La instancia**: `String` satisface `FOL.FreshSym` con los cinco nombres de arriba
(ADR-069). ⛔ Las seis declaraciones **NO se retiran**: `HenkinLimit0`, `Lindenbaum0` y
`Canonical0` usan `cst`, `shift` y `shiftTheory` **desnudos** en una docena de sitios, y
retirarlas movería contenido bajo teoremas ya publicados. La instancia se añade **al lado**. -/
instance : FOL.FreshSym String where
  shift := shift
  cst := cst
  shift_inj := shift_inj
  cst_inj := cst_inj
  cst_ne_shift := cst_ne_shift

-- ============================================================
-- §3 · Ninguna `cst n` aparece en nada desplazado
-- ============================================================

mutual
theorem not_occurs_shiftTerm (n : Nat) : ∀ t : Term,
    Not (occursTerm (cst n) (renameTerm shift t))
  | .var _ => fun h => h
  | .func s ts => fun h => by
      cases h with
      | inl he => exact cst_ne_shift n s he.symm
      | inr ht => exact not_occurs_shiftTerms n ts ht

theorem not_occurs_shiftTerms (n : Nat) : ∀ ts : List Term,
    Not (occursTerms (cst n) (renameTerms shift ts))
  | [] => fun h => h
  | t :: ts => fun h => by
      cases h with
      | inl ht => exact not_occurs_shiftTerm n t ht
      | inr hts => exact not_occurs_shiftTerms n ts hts
end

theorem not_occurs_shiftFormula (n : Nat) : ∀ f : Formula,
    Not (occursFormula (cst n) (renameFormula shift f)) := by
  intro f
  induction f with
  | bottom => exact fun h => h
  | atom _ ts => exact not_occurs_shiftTerms n ts
  | eq t u => exact fun h => h.elim (not_occurs_shiftTerm n t) (not_occurs_shiftTerm n u)
  | impl _ _ iha ihb => exact fun h => h.elim iha ihb
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun h => h.elim iha ihb
  | or _ _ iha ihb => exact fun h => h.elim iha ihb
  | ex _ ih => exact ih

-- ============================================================
-- §4 · ⭐⭐ A partir de cierto índice, TODAS son frescas
-- ============================================================

/-- El único paso clásico, y está en el **símbolo**: o `s` es alguna `cst k` —y entonces
`cst` inyectiva dice que es la única— o no lo es ninguna.

🔑 Éste es el lema que sustituye a la función `Formula → Nat` que §6.4 daba por necesaria. -/
theorem cst_bound_sym (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s := by
  by_cases h : ∃ k, cst k = s
  · obtain ⟨k, hk⟩ := h
    refine ⟨k + 1, fun m hm he => ?_⟩
    have hmk : m = k := cst_inj m k (he.trans hk.symm)
    exact absurd (hmk ▸ hm) (Nat.not_succ_le_self k)
  · exact ⟨0, fun m _ he => h ⟨m, he⟩⟩

mutual
theorem cst_bound_term : ∀ t : Term, ∃ N, ∀ m, N ≤ m → Not (occursTerm (cst m) t)
  | .var _ => ⟨0, fun _ _ h => h⟩
  | .func s ts => by
      obtain ⟨N1, h1⟩ := cst_bound_sym s
      obtain ⟨N2, h2⟩ := cst_bound_terms ts
      refine ⟨max N1 N2, fun m hm h => ?_⟩
      cases h with
      | inl he => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm) he.symm
      | inr ht => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) ht

theorem cst_bound_terms : ∀ ts : List Term, ∃ N, ∀ m, N ≤ m → Not (occursTerms (cst m) ts)
  | [] => ⟨0, fun _ _ h => h⟩
  | t :: ts => by
      obtain ⟨N1, h1⟩ := cst_bound_term t
      obtain ⟨N2, h2⟩ := cst_bound_terms ts
      refine ⟨max N1 N2, fun m hm h => ?_⟩
      cases h with
      | inl ht => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm) ht
      | inr hts => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) hts
end

/-- El combinador que se repite en cada caso binario: dos cotas dan una. -/
private theorem bound_pair {P Q : Nat → Prop} {N1 N2 : Nat}
    (h1 : ∀ m, N1 ≤ m → Not (P m)) (h2 : ∀ m, N2 ≤ m → Not (Q m)) :
    ∀ m, max N1 N2 ≤ m → Not (Or (P m) (Q m)) := fun m hm h =>
  h.elim (h1 m (Nat.le_trans (Nat.le_max_left _ _) hm))
         (h2 m (Nat.le_trans (Nat.le_max_right _ _) hm))

/-- ⭐⭐ **Para cualquier fórmula, casi todas las constantes nuevas son frescas.** -/
theorem cst_bound_formula : ∀ f : Formula, ∃ N, ∀ m, N ≤ m → Not (occursFormula (cst m) f) := by
  intro f
  induction f with
  | bottom => exact ⟨0, fun _ _ h => h⟩
  | atom _ ts => exact cst_bound_terms ts
  | eq t u =>
      obtain ⟨_, h1⟩ := cst_bound_term t
      obtain ⟨_, h2⟩ := cst_bound_term u
      exact ⟨_, bound_pair h1 h2⟩
  | impl _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | «forall» _ ih => exact ih
  | and _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | or _ _ iha ihb =>
      obtain ⟨_, h1⟩ := iha; obtain ⟨_, h2⟩ := ihb; exact ⟨_, bound_pair h1 h2⟩
  | ex _ ih => exact ih

/-- Y para una lista **finita** de fórmulas — que es lo que la iteración ω acumula. -/
theorem cst_bound_list : ∀ l : List Formula,
    ∃ N, ∀ m, N ≤ m → ∀ f, f ∈ l → Not (occursFormula (cst m) f)
  | [] => ⟨0, fun _ _ _ hf => absurd hf List.not_mem_nil⟩
  | g :: l => by
      obtain ⟨N1, h1⟩ := cst_bound_formula g
      obtain ⟨N2, h2⟩ := cst_bound_list l
      refine ⟨max N1 N2, fun m hm f hf => ?_⟩
      cases hf with
      | head => exact h1 m (Nat.le_trans (Nat.le_max_left _ _) hm)
      | tail _ hf' => exact h2 m (Nat.le_trans (Nat.le_max_right _ _) hm) f hf'

-- ============================================================
-- §5 · La teoría desplazada
-- ============================================================

/-- La imagen de `S` por el desplazamiento. ⚠️ Se enuncia como imagen (`∃ g, S g ∧ …`) y no como
preimagen: así la frescura de `cst n` es inmediata (§3) y la conservatividad se obtiene
**mapeando**, sin tener que elegir preimágenes de una lista. -/
def shiftTheory (S : Formula → Prop) : Formula → Prop :=
  fun x => ∃ g, And (S g) (x = renameFormula shift g)

/-- ⭐ **Todas** las constantes nuevas son frescas en la teoría desplazada, sin hipótesis
ninguna sobre `S`. Es exactamente lo que `henkin_step_consistent` pide de la teoría. -/
theorem shiftTheory_fresh {S : Formula → Prop} (n : Nat) :
    ∀ g, shiftTheory S g → Not (occursFormula (cst n) g) := by
  intro g hg hocc
  obtain ⟨h, _, he⟩ := hg
  exact not_occurs_shiftFormula n h (he ▸ hocc)

/-- Lo derivable viaja al sublenguaje. -/
theorem derivesSet0_shift {S : Formula → Prop} {f : Formula} (h : S ⊢₀* f) :
    shiftTheory S ⊢₀* renameFormula shift f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ.map (renameFormula shift), ?_, derives0_rename shift hD⟩
  intro g hg
  obtain ⟨x, hx, hex⟩ := List.mem_map.mp hg
  exact ⟨x, hΓ x hx, hex.symm⟩

/-- ⭐⭐ **Y vuelve.** El desplazamiento es **conservativo**: nada nuevo del lenguaje viejo se
demuestra por haberse mudado al sublenguaje.

⭐ La prueba no elige preimágenes: **mapea con la inversa**. `invOf shift` existe porque `shift`
es inyectiva, y `rename_rename_formula` la cancela. -/
theorem derivesSet0_shift_inv {S : Formula → Prop} {f : Formula}
    (h : shiftTheory S ⊢₀* renameFormula shift f) : S ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  have hcancel := rename_rename_formula (invOf_spec shift_inj)
  refine ⟨Γ.map (renameFormula (invOf shift)), ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, hex⟩ := List.mem_map.mp hg
    obtain ⟨y, hSy, hey⟩ := hΓ x hx
    rw [← hex, hey, hcancel]
    exact hSy
  · have hr := derives0_rename (invOf shift) hD
    rwa [hcancel f] at hr

/-- ⭐⭐ **Equiconsistencia.** Es lo que la iteración ω necesita para arrancar. -/
theorem shiftTheory_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (shiftTheory S) := fun hbot => hCons (derivesSet0_shift_inv hbot)

-- ============================================================
-- §6 · ⭐⭐ El enunciado que consume la iteración
-- ============================================================

/-- **Hay constante fresca para todo a la vez**: la teoría desplazada, la lista finita de axiomas
de Henkin ya añadidos, y la fórmula del turno.

🔑 Éste es el teorema que cierra la pieza (1) de §6.4 — y con él la iteración ω deja de necesitar
la función «mayor índice usado». -/
theorem exists_fresh (S : Formula → Prop) (extra : List Formula) (A : Formula) :
    ∃ c : String, And (∀ g, shiftTheory S g → Not (occursFormula c g))
      (And (∀ g, g ∈ extra → Not (occursFormula c g)) (Not (occursFormula c A))) := by
  obtain ⟨N1, h1⟩ := cst_bound_list extra
  obtain ⟨N2, h2⟩ := cst_bound_formula A
  refine ⟨cst (max N1 N2), shiftTheory_fresh _, ?_, ?_⟩
  · exact h1 _ (Nat.le_max_left _ _)
  · exact h2 _ (Nat.le_max_right _ _)

end FOL.Fresh0

#print axioms FOL.Fresh0.cst_bound_formula
#print axioms FOL.Fresh0.derivesSet0_shift_inv
#print axioms FOL.Fresh0.shiftTheory_consistent
#print axioms FOL.Fresh0.exists_fresh
