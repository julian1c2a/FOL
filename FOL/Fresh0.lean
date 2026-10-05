/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.SymClasses, FOL.Henkin0, FOL.Rename
-- @axiom_system: classical
-- @importance: high

import FOL.SymClasses
import FOL.Henkin0
import FOL.Rename

/-!
# `FOL.Fresh0` — **el suministro de constantes frescas**

Pieza (1) del ensamblaje de
`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.4. `henkin_step_consistent₀`
(ADR‑037) pide una constante `c` fresca **en la teoría y en la fórmula**; para una teoría
`S : Formula → Prop` **arbitraria** no tiene por qué haber ninguna: `S` puede usar todos los
símbolos. Este módulo fabrica el suministro por el camino de los libros (meter la teoría en un
sublenguaje) y, desde el 2026‑09‑27, **sin `Classical.choice`** (§Footprint).

## La construcción, en dos movimientos

1. **Meter la teoría en un sublenguaje.** `shift s := 'f' :: s` renombra *todos* los símbolos de
   función. `shiftTheory S` es la imagen de `S`, y es **conservativa** en los dos sentidos
   (`derivesSet0_shift` / `derivesSet0_shift_inv`) y **equiconsistente**
   (`shiftTheory_consistent₀`). La vuelta mapea con `unshift`, la inversa GLOBAL de `shift`,
   **calculada**: quita el `'f'` de cabeza (§5; hasta D7, 2026‑10‑05, sobre los bytes de `String`).
2. **Las constantes nuevas.** `cst 0 = ['g']`, `cst (n+1) = 'a' :: cst n` — infinitas, inyectiva, y
   **ninguna está en la imagen de `shift`** ⇒ `cst n` no aparece en ninguna fórmula desplazada.
   (Los nombres de siempre, «g», «ag», «aag»…: con `String`, hasta D7, eran `"g"` y `"a" ++ cst n`.)

## ⭐ Y el punto que §6.4 marcaba en rojo

El plan daba a la iteración ω **riesgo medio** por esto: `cₙ` tiene que ser fresca también para
`φₙ`, y `φₙ` recorre **todas** las fórmulas, así que puede mencionar cualquier `cst m`. La
solución prevista era una función `Formula → Nat` («mayor índice usado») con su lema, ~40 líneas.

⭐ **No hace falta esa función.** El enunciado que la iteración consume no es «el máximo índice»
sino «**a partir de cierto índice, todas son frescas**»:

    cst_bound_formula : ∀ f, ∃ N, ∀ m ≥ N, ¬ occursFormula (cst m) f

y eso sale por inducción estructural con `max`, sin invertir `cst`.
El caso del **símbolo** —`∃ N, ∀ m ≥ N, cst m ≠ s`— se CALCULA: `N := s.length`, porque
`cst m` tiene `m + 1` caracteres (`cst_length`; hasta D7, 2026‑10‑05, `s.utf8ByteSize` y
`cst_utf8ByteSize`, en bytes). (Hasta el 2026‑09‑27 se decidía por
`Classical.em (∃ k, cst k = s)` más la inyectividad de `cst`, y esta cabecera lo llamaba «el único
punto clásico»: no hacía falta.)

⇒ `exists_fresh` entrega la constante que el paso de Henkin pide, para la teoría desplazada
**más** cualquier lista finita de axiomas ya añadidos **más** la fórmula del turno.

⚠️ (2026‑09‑27) `FOL.HenkinLimit0` acabó escribiendo una función `Formula → Nat` —`bnd`, una COTA
calculada, no el «mayor índice usado»—, pero para quitar un `Exists.choose`, no porque la iteración
la necesitara. Desde entonces la iteración consume `HenkinLimit0.bnd_spec` (la misma forma: a partir
de `bnd f`, todas frescas), no `cst_bound_formula`.

## 📏 Footprint

⭐ **Ninguna constante de `FOL.Fresh0` lleva `Classical.choice`** (auditoría de constructividad,
2026‑09‑27, medido sobre el entorno compilado: `auditoria/constructividad-2026-09-27/despues/`).

✏️ **2026‑10‑05, D7 EJECUTADA (ADR‑129 de RPP).** Los símbolos son `List Char`, y la capa de bytes de
`String` se fue con ellos: `valid_tail` y `shift_bytes`, retirados; `cst_utf8ByteSize`, hoy
`cst_length`. Medido de nuevo (filas de `../ROBINSON_PlusPlus/check-footprints.bash`): la instancia
`instFreshSymListChar` **no depende de ningún axioma**, y por tanto tampoco nada de lo que usa
—`shift`, `cst`, `shift_inj`, `cst_inj`, `cst_ne_shift` y `cst_zero_ne`—; `cst_bound_sym`,
`cst_bound_formula`, `derivesSet0_shift_inv`, `shiftTheory_consistent₀` y `exists_fresh`,
`[propext, Quot.sound]`. Ninguna de las medidas lleva `Classical.choice`.

La tabla es la del 2026‑09‑27, con `String`; lo que entonces quedaba era su capa de bytes:

| footprint | constantes |
|---|---|
| `[propext]` | `shift`, `cst`, `cst_zero_ne`, `cst_ne_shift`, `shift_bytes` (retirado), `not_occurs_shiftTerm`/`Terms`/`Formula`, `shiftTheory`, `shiftTheory_fresh` |
| `[propext, Quot.sound]` | `shift_inj`, `cst_inj`, `cst_utf8ByteSize` (retirado; hoy `cst_length`), `cst_bound_sym`/`term`/`terms`/`formula`/`list`, `valid_tail` (retirado), `unshift`, `unshift_shift`, `derivesSet0_shift`, `derivesSet0_shift_inv`, `shiftTheory_consistent₀`, `exists_fresh` y la instancia `FreshSym String` (retirada; hoy `instFreshSymListChar`) |

`propext` entraba ya en `shift` y `cst`, que no usaban más que literales y `++` de `String`: era el
suelo del módulo. Con `List Char` ese suelo no existe (ver arriba). **Cero axiomas del proyecto.**

⚠️⚠️ **Hasta el 2026‑09‑27 esta sección decía** que `Classical.choice` entraba «por tres vías
distintas que conviene no confundir»: `Rename.invOf` en `derivesSet0_shift_inv`; «la matemática», el
tercio excluso de `cst_bound_sym`; y «la implementación de `String`» —«DESCOMPONER un `String`
arrastra choice», el muro de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §7—. Las tres
eran evitables, y se retiraron:

* `Rename.invOf`, la inversa GLOBAL **elegida** → `unshift`, inversa GLOBAL **calculada** sobre los
  bytes (§5; desde D7, un `match` sobre `List Char`). `invOf` ya no existe;
* el tercio excluso de `cst_bound_sym` → la cota `s.utf8ByteSize` (§4; desde D7, `s.length`);
* `String` → el choice no venía de descomponer, sino de DECODIFICAR UTF‑8 (una prueba de
  `BitVec`/`Nat` dentro del decodificador del núcleo, v4.31): aquí, por la `ReflBEq String` que
  `not_eq_of_beq_eq_false` sintetizaba a través de `String.instOrd` en `cst_zero_ne`/`cst_ne_shift`.
  Con `of_decide_eq_false` (`String.decEq`) medían `[propext]`. `String.decEq`,
  `String.append_right_inj` y `shift_inj` nunca lo llevaron, y `unshift` DESCOMPONÍA un `String`
  —por bytes— sin él. (✏️ 2026‑10‑05: desde D7 no hay `String`; `cst_zero_ne`/`cst_ne_shift` siguen
  con `of_decide_eq_false`, sobre `List Char`, y no dependen de ningún axioma.)

⚠️ Y el `Classical.choice` de la completitud tampoco es «el `if IsConsistent …` de Lindenbaum», como
decía esta sección: la etapa ya no decide nada. Ver `FOL.Lindenbaum0`, «Dónde está, y dónde NO está,
lo clásico de la completitud».
-/

namespace FOL.Fresh0

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- §1 · El desplazamiento al sublenguaje
-- ============================================================

/-- Renombra **todo** símbolo de función `s` como `'f' :: s`. ⚠️ Los símbolos de RELACIÓN no se
tocan (`renameFormula` no los toca): no hacen falta testigos para ellos. -/
def shift (s : List Char) : List Char := 'f' :: s

/-- Una línea: `shift` es un `cons`, y los constructores son inyectivos (D7, 2026‑10‑05: antes
`String.append_right_inj`). -/
theorem shift_inj : ∀ s t : List Char, shift s = shift t → s = t :=
  fun _ _ h => (List.cons.inj h).2

-- ============================================================
-- §2 · La familia infinita de constantes nuevas
-- ============================================================

/-- `['g']`, `['a', 'g']`, `['a', 'a', 'g']`, … Infinitas, e **inyectiva**. -/
def cst : Nat → List Char
  | 0 => ['g']
  | n + 1 => 'a' :: cst n

/-- ⚠️ `of_decide_eq_false rfl` con variables libres **parece imposible** y no lo es: la igualdad
decidible de `List Char` compara carácter a carácter **cortocircuitando** en el primero que difiere,
y aquí ese carácter es el del literal. (Con `String`, hasta D7, era byte a byte.) -/
theorem cst_zero_ne (n : Nat) : cst 0 ≠ cst (n + 1) := of_decide_eq_false rfl

/-- ⭐⭐ **Ninguna constante nueva está en la imagen del desplazamiento.** Es lo único que hay que
saber de los nombres: todo lo demás se deduce. -/
theorem cst_ne_shift : ∀ (n : Nat) (s : List Char), cst n ≠ shift s
  | 0, _ => of_decide_eq_false rfl
  | _ + 1, _ => of_decide_eq_false rfl

theorem cst_inj : ∀ m n : Nat, cst m = cst n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (cst_zero_ne _)
  | _ + 1, 0, h => absurd h.symm (cst_zero_ne _)
  | m + 1, n + 1, h => congrArg (· + 1) (cst_inj m n (List.cons.inj h).2)

/-- ⭐ **La instancia**: `List Char` satisface `FOL.FreshSym` con los cinco nombres de arriba
(ADR-069). ⛔ Las seis declaraciones **NO se retiran**: `HenkinLimit0`, `Lindenbaum0` y
`Canonical0` usan `cst`, `shift` y `shiftTheory` **desnudos** en una docena de sitios, y
retirarlas movería contenido bajo teoremas ya publicados. La instancia se añade **al lado**. -/
instance : FOL.FreshSym (List Char) where
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

/-- `cst m` tiene `m + 1` caracteres (D7, 2026‑10‑05: antes `cst_utf8ByteSize`, en bytes). -/
theorem cst_length : ∀ m : Nat, (cst m).length = m + 1
  | 0 => rfl
  | m + 1 => congrArg (· + 1) (cst_length m)

/-- ⭐ **La cota se CALCULA**: a partir de `s.length`, ninguna `cst m` es `s`, porque es más larga.
Antes esto se probaba por tercio excluso sobre `∃ k, cst k = s` («el único paso clásico»); no hacía
falta (auditoría de constructividad, 2026‑09‑27).

🔑 Éste es el lema que sustituyó a la función `Formula → Nat` de §6.4; desde el 2026‑09‑27 la
iteración usa `HenkinLimit0.bnd_spec`. -/
theorem cst_bound_sym (s : List Char) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.length, fun m hm he => by
    have h := congrArg List.length he
    rw [cst_length] at h
    omega⟩

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

-- ── La inversa GLOBAL de `shift` ──────────────────────────────────────────────────────────
-- D7 (2026‑10‑05): con `List Char`, quitar el `'f'` de cabeza es un `match`; la capa de bytes de
-- `String` (`valid_tail`, `shift_bytes`) ya no hace falta y se retira.

/-- ⭐ **La inversa global de `shift`**: quita el `'f'` de cabeza; lo demás lo deja como está. -/
def unshift : List Char → List Char
  | 'f' :: t => t
  | x => x

theorem unshift_shift (s : List Char) : unshift (shift s) = s := rfl

/-- La imagen de `S` por el desplazamiento. ⚠️ Se enuncia como imagen (`∃ g, S g ∧ …`) y no como
preimagen: así la frescura de `cst n` es inmediata (§3) y la conservatividad se obtiene
**mapeando**, sin tener que elegir preimágenes de una lista. -/
def shiftTheory (S : Formula → Prop) : Formula → Prop :=
  fun x => ∃ g, And (S g) (x = renameFormula shift g)

/-- ⭐ **Todas** las constantes nuevas son frescas en la teoría desplazada, sin hipótesis
ninguna sobre `S`. Es exactamente lo que `henkin_step_consistent₀` pide de la teoría. -/
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

⭐ La prueba no elige preimágenes: **mapea con la inversa** `unshift`, calculada, y
`rename_rename_formula` la cancela. (Hasta el 2026‑09‑27 mapeaba con `Rename.invOf shift`, una
inversa ELEGIDA con `Classical.choice`.) -/
theorem derivesSet0_shift_inv {S : Formula → Prop} {f : Formula}
    (h : shiftTheory S ⊢₀* renameFormula shift f) : S ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  have hcancel := rename_rename_formula unshift_shift
  refine ⟨Γ.map (renameFormula unshift), ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, hex⟩ := List.mem_map.mp hg
    obtain ⟨y, hSy, hey⟩ := hΓ x hx
    rw [← hex, hey, hcancel]
    exact hSy
  · have hr := derives0_rename unshift hD
    rwa [hcancel f] at hr

/-- ⭐⭐ **Equiconsistencia**, en la dirección que la iteración ω necesita para arrancar (la otra
sale de `derivesSet0_shift` con `f := ⊥` y no se enuncia). -/
theorem shiftTheory_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (shiftTheory S) := fun hbot => hCons (derivesSet0_shift_inv hbot)

-- ============================================================
-- §6 · ⭐⭐ Una constante fresca para todo a la vez (`exists_fresh`; la iteración de `HenkinLimit0`
-- va por `bnd_spec`)
-- ============================================================

/-- **Hay constante fresca para todo a la vez**: la teoría desplazada, la lista finita de axiomas
de Henkin ya añadidos, y la fórmula del turno.

🔑 Éste es el teorema que cierra la pieza (1) de §6.4. La iteración ω no lo usa (tomó
`cst_bound_formula` y, desde el 2026‑09‑27, `HenkinLimit0.bnd_spec`), y dejó de necesitar
la función «mayor índice usado». -/
theorem exists_fresh (S : Formula → Prop) (extra : List Formula) (A : Formula) :
    ∃ c : List Char, And (∀ g, shiftTheory S g → Not (occursFormula c g))
      (And (∀ g, g ∈ extra → Not (occursFormula c g)) (Not (occursFormula c A))) := by
  obtain ⟨N1, h1⟩ := cst_bound_list extra
  obtain ⟨N2, h2⟩ := cst_bound_formula A
  refine ⟨cst (max N1 N2), shiftTheory_fresh _, ?_, ?_⟩
  · exact h1 _ (Nat.le_max_left _ _)
  · exact h2 _ (Nat.le_max_right _ _)

end FOL.Fresh0

#print axioms FOL.Fresh0.cst_bound_formula
#print axioms FOL.Fresh0.derivesSet0_shift_inv
#print axioms FOL.Fresh0.shiftTheory_consistent₀
#print axioms FOL.Fresh0.exists_fresh
