/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.SkolemN0, FOL.PrenexNF0
-- @axiom_system: classical
-- @importance: high

import FOL.SkolemN0
import FOL.PrenexNF0

/-!
# `FOL.SkolemNF0` — 🏁 la FORMA NORMAL DE SKOLEM

    skolemize k f     : Formula          -- ∀ᵐ ψ, con ψ SIN cuantificadores
    skolemAxioms k f  : List Formula     -- los axiomas de Skolem que consume

    skolemize_shape       : Prenex f → ∃ m ψ, skolemize k f = allBlock m ψ ∧ QuantFree ψ
    skolemizeF_impAll     : la forma normal IMPLICA el original — ⭐ **net‑0**, sin axiomas
    skolem_conservative_nf: el BLOQUE ENTERO de axiomas de Skolem no inventa teoremas
    derives0_of_skolemNF  : 🏁 lo que se demuestra desde la forma normal se demuestra sin ella

## ⭐⭐ La decisión que mata el único riesgo que había: COMBUSTIBLE

La definición natural recurre sobre `substFormula 0 t A`, que **no es subtérmino** de `.ex A`
⇒ Lean la compila por recursión **bien fundada**, y una definición WF **no reduce
definicionalmente**: sólo se abre por sus lemas de ecuación. Tres diseños independientes
tropezaron exactamente ahí, y los dos refutadores de cada uno señalaron el mismo sitio.

Aquí el prefijo se recorre con un **combustible**, y entonces la recursión es **estructural
sobre el primer `Nat`**. El combustible no es una cota arbitraria: es **exactamente** la
longitud del prefijo (`qdepth`), y **sustituir no la cambia** (`qdepth_subst`).

⇒ las tres ecuaciones de `skolemizeF` son **`rfl`**, y la normalización de fórmulas concretas
se comprueba **por cómputo**:

    skolemize 0 (∀∃∀∃ Q(x,y,z,w)) = ∀∀ Q(x₁, c₀(x₁), x₀, c₁(x₀,x₁))      -- `by rfl`

🔑 *Cuando una recursión no es estructural, antes de pagar la recursión bien fundada hay que
mirar si el argumento que decrece se puede PASAR, en vez de MEDIR.*

## ⚠️ Lo que este módulo entrega y lo que NO

Entrega **una** de las dos direcciones, y es la que vale para la conservatividad:

* ⭐ `skolemizeF_impAll` — la forma normal **implica** el original, **sin ningún axioma de
  Skolem** y net‑0: es `intro_ex` bajo el prefijo.
* 🏁 `skolem_conservative_nf` — los axiomas de Skolem **se retiran todos**, iterando
  `FOL.SkolemN0.skolem_conservative_n` sobre la lista con la frescura correcta.

⬜ **No entrega** la dirección `φ → skolemize φ` *con* los axiomas. Esa exige empujar el axioma
de Skolem **bajo el prefijo `∀ⁿ`** (la regla K iterada), y **no está medida**.

## ⚠️ Y un puente que faltaba en el árbol

`occursFormula_lift` **no existía**: había `occursTerm_lift`/`occursTerms_lift`
(`FOL/HenkinLimit0.lean:92,101`) y nada para fórmulas. Sin él no se puede transportar la
frescura a través de `prenex`, y sin eso el teorema final **no es aplicable** por ningún
consumidor. *Una conservatividad cuyas hipótesis nadie puede descargar no es un teorema
utilizable.*
-/

namespace FOL.SkolemNF0

open FOL.Eigenvariable
open FOL.Skolem0
open FOL.SkolemN0
open FOL.Herbrand0
open FOL.Prenex0
open FOL.PrenexNF0
open FOL.Fresh0
open FOL.HenkinLimit0

-- ═══════════════════════════════════════════════════════════════════════════
-- §1 · el combustible, y por qué es EXACTO
-- ═══════════════════════════════════════════════════════════════════════════

/-- La longitud del prefijo de cuantificadores. -/
def qdepth : Formula → Nat
  | .forall A => qdepth A + 1
  | .ex A => qdepth A + 1
  | _ => 0

/-- ⭐ Sustituir no toca el prefijo. Es lo que hace que el combustible sea **exacto** y no una
cota: en el paso `∃` se gasta uno y queda justo el que hace falta. -/
theorem qdepth_subst : ∀ (f : Formula) (k : Nat) (t : Term),
    qdepth (substFormula k t f) = qdepth f
  | .bottom, _, _ => rfl
  | .atom _ _, _, _ => rfl
  | .eq _ _, _, _ => rfl
  | .impl _ _, _, _ => rfl
  | .and _ _, _, _ => rfl
  | .or _ _, _, _ => rfl
  | .forall A, k, t => by
      show qdepth (substFormula (k + 1) (liftTerm 0 t) A) + 1 = qdepth A + 1
      rw [qdepth_subst A (k + 1) (liftTerm 0 t)]
  | .ex A, k, t => by
      show qdepth (substFormula (k + 1) (liftTerm 0 t) A) + 1 = qdepth A + 1
      rw [qdepth_subst A (k + 1) (liftTerm 0 t)]

/-- Prefijo de longitud cero ⇒ no hay cuantificadores.
⭐ Los seis casos no cuantificados salen por **identidad**: `Prenex` y `QuantFree` son
definicionalmente iguales ahí. -/
theorem quantFree_of_qdepth_zero : ∀ (f : Formula), Prenex f → qdepth f = 0 → QuantFree f
  | .bottom, h, _ => h
  | .atom _ _, h, _ => h
  | .eq _ _, h, _ => h
  | .impl _ _, h, _ => h
  | .and _ _, h, _ => h
  | .or _ _, h, _ => h
  | .forall _, _, hz => absurd hz (by intro hc; exact Nat.succ_ne_zero _ hc)
  | .ex _, _, hz => absurd hz (by intro hc; exact Nat.succ_ne_zero _ hc)

/-- Sustituir tampoco crea cuantificadores. -/
theorem quantFree_subst : ∀ (f : Formula) (k : Nat) (t : Term),
    QuantFree f → QuantFree (substFormula k t f)
  | .bottom, _, _, h => h
  | .atom _ _, _, _, h => h
  | .eq _ _, _, _, h => h
  | .impl a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .and a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .or a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .forall _, _, _, h => h.elim
  | .ex _, _, _, h => h.elim

/-- ⭐ Y la forma prenexa se conserva al sustituir: es lo que permite volver a entrar
en el paso `∃`. -/
theorem prenex_subst : ∀ (f : Formula) (k : Nat) (t : Term), Prenex f → Prenex (substFormula k t f)
  | .bottom, _, _, h => h
  | .atom _ _, _, _, h => h
  | .eq _ _, _, _, h => h
  | .impl a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .and a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .or a b, k, t, h => ⟨quantFree_subst a k t h.1, quantFree_subst b k t h.2⟩
  | .forall A, k, t, h => prenex_subst A (k + 1) (liftTerm 0 t) h
  | .ex A, k, t, h => prenex_subst A (k + 1) (liftTerm 0 t) h

-- ═══════════════════════════════════════════════════════════════════════════
-- §2 · la normalización, ESTRUCTURAL sobre el combustible
-- ═══════════════════════════════════════════════════════════════════════════

/-- `skolemizeF fuel k n f`: elimina los `∃` del prefijo de `f` usando los símbolos
`cst k, cst (k+1), …`, sabiendo que ya hay `n` universales por fuera.
⭐ **Estructural sobre `fuel`** ⇒ sus ecuaciones son **definicionales**. -/
def skolemizeF : Nat → Nat → Nat → Formula → Formula
  | 0, _, _, f => f
  | fuel + 1, k, n, .forall A => Formula.forall (skolemizeF fuel k (n + 1) A)
  | fuel + 1, k, n, .ex A =>
      skolemizeF fuel (k + 1) n (substFormula 0 (Term.func (cst k) (vars n)) A)
  | _ + 1, _, _, f => f

/-- La lista de axiomas de Skolem que la normalización consume, en el mismo orden. -/
def skolemAxiomsF : Nat → Nat → Nat → Formula → List Formula
  | 0, _, _, _ => []
  | fuel + 1, k, n, .forall A => skolemAxiomsF fuel k (n + 1) A
  | fuel + 1, k, n, .ex A =>
      skolemAxN (cst k) n A ::
        skolemAxiomsF fuel (k + 1) n (substFormula 0 (Term.func (cst k) (vars n)) A)
  | _ + 1, _, _, _ => []

/-- La forma normal de Skolem de `f`, con símbolos nuevos a partir de `cst k`. -/
def skolemize (k : Nat) (f : Formula) : Formula := skolemizeF (qdepth f) k 0 f

/-- Los axiomas de Skolem de `f`. -/
def skolemAxioms (k : Nat) (f : Formula) : List Formula := skolemAxiomsF (qdepth f) k 0 f

-- ── las tres ecuaciones, y las tres por `rfl` ──────────────────────────────
example (k n : Nat) (f : Formula) : skolemizeF 0 k n f = f := rfl
example (fuel k n : Nat) (A : Formula) :
    skolemizeF (fuel + 1) k n (Formula.forall A)
      = Formula.forall (skolemizeF fuel k (n + 1) A) := rfl
example (fuel k n : Nat) (A : Formula) :
    skolemizeF (fuel + 1) k n (Formula.ex A)
      = skolemizeF fuel (k + 1) n (substFormula 0 (Term.func (cst k) (vars n)) A) := rfl

-- ── ⭐ y por eso la normalización se comprueba POR CÓMPUTO ─────────────────
/-- `∀x ∃y P(x,y)  ↝  ∀x P(x, c₀(x))`. -/
example :
    skolemize 0 (Formula.forall (Formula.ex (Formula.atom "P" [Term.var 1, Term.var 0])))
      = Formula.forall (Formula.atom "P" [Term.var 0, Term.func (cst 0) [Term.var 0]]) := by
  rfl

/-- `∃y ∀x P(x,y)  ↝  ∀x P(x, c₀)` — con el existencial por FUERA, el símbolo es una
constante, y eso lo decide `vars 0 = []`. -/
example :
    skolemize 0 (Formula.ex (Formula.forall (Formula.atom "P" [Term.var 0, Term.var 1])))
      = Formula.forall (Formula.atom "P" [Term.var 0, Term.func (cst 0) []]) := by
  rfl

/-- `∀x ∃y ∀z ∃w Q(x,y,z,w)  ↝  ∀x ∀z Q(x, c₀(x), z, c₁(z,x))`. -/
example :
    skolemize 0 (Formula.forall (Formula.ex (Formula.forall (Formula.ex
      (Formula.atom "Q" [Term.var 3, Term.var 2, Term.var 1, Term.var 0])))))
      = Formula.forall (Formula.forall (Formula.atom "Q"
          [Term.var 1, Term.func (cst 0) [Term.var 1],
           Term.var 0, Term.func (cst 1) [Term.var 0, Term.var 1]])) := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §3 · 🏁 la FORMA de la salida: `∀ᵐ ψ` con `ψ` sin cuantificadores
-- ═══════════════════════════════════════════════════════════════════════════

theorem skolemizeF_shape : ∀ (fuel k n : Nat) (f : Formula), Prenex f → qdepth f ≤ fuel →
    ∃ (m : Nat) (ψ : Formula), And (skolemizeF fuel k n f = allBlock m ψ) (QuantFree ψ)
  | 0, _, _, f, h, hle =>
      ⟨0, f, rfl, quantFree_of_qdepth_zero f h (Nat.le_zero.mp hle)⟩
  | _ + 1, _, _, .bottom, h, _ => ⟨0, Formula.bottom, rfl, h⟩
  | _ + 1, _, _, .atom p ts, h, _ => ⟨0, Formula.atom p ts, rfl, h⟩
  | _ + 1, _, _, .eq t u, h, _ => ⟨0, Formula.eq t u, rfl, h⟩
  | _ + 1, _, _, .impl a b, h, _ => ⟨0, Formula.impl a b, rfl, h⟩
  | _ + 1, _, _, .and a b, h, _ => ⟨0, Formula.and a b, rfl, h⟩
  | _ + 1, _, _, .or a b, h, _ => ⟨0, Formula.or a b, rfl, h⟩
  | fuel + 1, k, n, .forall A, h, hle => by
      have hA : qdepth A ≤ fuel := by
        have h1 : qdepth A + 1 ≤ fuel + 1 := hle
        omega
      obtain ⟨m, ψ, he, hq⟩ := skolemizeF_shape fuel k (n + 1) A h hA
      refine ⟨m + 1, ψ, ?_, hq⟩
      show Formula.forall (skolemizeF fuel k (n + 1) A) = allBlock (m + 1) ψ
      rw [he]
      rfl
  | fuel + 1, k, n, .ex A, h, hle => by
      have hA : qdepth (substFormula 0 (Term.func (cst k) (vars n)) A) ≤ fuel := by
        rw [qdepth_subst]
        have h1 : qdepth A + 1 ≤ fuel + 1 := hle
        omega
      exact skolemizeF_shape fuel (k + 1) n _ (prenex_subst A 0 _ h) hA

/-- 🏁 **La salida es `∀ᵐ ψ` con `ψ` sin cuantificadores** — que es exactamente la hipótesis
que el teorema de Herbrand pide (`FOL.Herbrand0.QuantFree`). -/
theorem skolemize_shape (k : Nat) (f : Formula) (h : Prenex f) :
    ∃ (m : Nat) (ψ : Formula), And (skolemize k f = allBlock m ψ) (QuantFree ψ) :=
  skolemizeF_shape (qdepth f) k 0 f h (Nat.le_refl _)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4 · ⭐ la forma normal IMPLICA el original — net‑0, sin un solo axioma
-- ═══════════════════════════════════════════════════════════════════════════

/-- La introducción del existencial, en forma esquemática: es **un constructor**. -/
theorem impAll_intro_ex (t : Term) (A : Formula) : ImpAll (substFormula 0 t A) (Formula.ex A) :=
  fun _ => Derives₀.intro_impl _ _ _
    (Derives₀.intro_ex _ A t (Derives₀.hyp _ _ (List.Mem.head _)))

/-- 🏁 **La forma normal de Skolem implica el original**, y **sin ningún axioma de Skolem**.
⭐ Es `intro_ex` bajo el prefijo: la dirección barata, y la que la conservatividad consume. -/
theorem skolemizeF_impAll : ∀ (fuel k n : Nat) (f : Formula), ImpAll (skolemizeF fuel k n f) f
  | 0, _, _, f => impAll_refl f
  | _ + 1, _, _, .bottom => impAll_refl _
  | _ + 1, _, _, .atom _ _ => impAll_refl _
  | _ + 1, _, _, .eq _ _ => impAll_refl _
  | _ + 1, _, _, .impl _ _ => impAll_refl _
  | _ + 1, _, _, .and _ _ => impAll_refl _
  | _ + 1, _, _, .or _ _ => impAll_refl _
  | fuel + 1, k, n, .forall A => impAll_forall (skolemizeF_impAll fuel k (n + 1) A)
  | fuel + 1, k, n, .ex A =>
      impAll_trans
        (skolemizeF_impAll fuel (k + 1) n (substFormula 0 (Term.func (cst k) (vars n)) A))
        (impAll_intro_ex (Term.func (cst k) (vars n)) A)

theorem derives0_of_skolemizeF (fuel k n : Nat) (f : Formula) (Γ : List Formula)
    (h : Γ ⊢₀ skolemizeF fuel k n f) : Γ ⊢₀ f :=
  Derives₀.elim_impl _ _ _ (skolemizeF_impAll fuel k n f Γ) h

-- ═══════════════════════════════════════════════════════════════════════════
-- §5 · 🏁 la CONSERVATIVIDAD del bloque entero de axiomas
-- ═══════════════════════════════════════════════════════════════════════════

/-- El bloque `∀ⁿ` no esconde símbolos. -/
theorem occurs_allBlock (c : String) : ∀ (n : Nat) (X : Formula),
    occursFormula c (allBlock n X) → occursFormula c X
  | 0, _, h => h
  | n + 1, X, h => occurs_allBlock c n X h

theorem not_occurs_skolemAxN {c d : String} {n : Nat} {A : Formula}
    (hcd : c ≠ d) (hA : Not (occursFormula c A)) :
    Not (occursFormula c (skolemAxN d n A)) := by
  intro h
  have h1 : occursFormula c
      (Formula.impl (Formula.ex A) (substFormula 0 (Term.func d (vars n)) A)) :=
    occurs_allBlock c n _ h
  have ht : Not (occursTerm c (Term.func d (vars n))) := by
    intro hc
    exact hc.elim (fun he => hcd he.symm) (fun hv => not_occurs_vars c n hv)
  exact h1.elim hA (not_occurs_substFormula c A 0 _ ht hA)

/-- 🏁 **Los axiomas de Skolem de toda la normalización se retiran.** La inducción va sobre el
combustible y, en cada paso `∃`, hace tres cosas: permuta el axioma de ese paso al contexto,
retira por hipótesis de inducción todos los interiores (que usan símbolos `≥ k+1`), y remata
con `FOL.SkolemN0.skolem_conservative_n` sobre el de ese paso. -/
theorem skolem_conservative_listF :
    ∀ (fuel k n : Nat) (f : Formula) (Γ : List Formula) (χ : Formula),
      (∀ m, k ≤ m → ∀ g, g ∈ Γ → Not (occursFormula (cst m) g)) →
      (∀ m, k ≤ m → Not (occursFormula (cst m) f)) →
      (∀ m, k ≤ m → Not (occursFormula (cst m) χ)) →
      ((skolemAxiomsF fuel k n f ++ Γ) ⊢₀ χ) → Γ ⊢₀ χ
  | 0, _, _, _, _, _, _, _, _, h => h
  | _ + 1, _, _, .bottom, _, _, _, _, _, h => h
  | _ + 1, _, _, .atom _ _, _, _, _, _, _, h => h
  | _ + 1, _, _, .eq _ _, _, _, _, _, _, h => h
  | _ + 1, _, _, .impl _ _, _, _, _, _, _, h => h
  | _ + 1, _, _, .and _ _, _, _, _, _, _, h => h
  | _ + 1, _, _, .or _ _, _, _, _, _, _, h => h
  | fuel + 1, k, n, .forall A, Γ, χ, hΓ, hf, hχ, h =>
      skolem_conservative_listF fuel k (n + 1) A Γ χ hΓ hf hχ h
  | fuel + 1, k, n, .ex A, Γ, χ, hΓ, hf, hχ, h => by
      have hAk : ∀ m, k ≤ m → Not (occursFormula (cst m) A) := hf
      -- (1) permutar: el axioma de este paso sale del bloque y entra en el contexto
      have hperm : (skolemAxiomsF fuel (k + 1) n
            (substFormula 0 (Term.func (cst k) (vars n)) A)
            ++ (skolemAxN (cst k) n A :: Γ)) ⊢₀ χ := by
        refine Derives₀.weakening _ _ _ h ?_
        intro x hx
        -- ⚠️ `(a :: L) ++ Γ` es DEFEQ a `a :: (L ++ Γ)`, pero `List.mem_append` parte por el
        -- `++` SIN abrir el `::`: hay que pedir la forma que se quiere con un `have` tipado.
        have hx' : x ∈ skolemAxN (cst k) n A ::
            (skolemAxiomsF fuel (k + 1) n
              (substFormula 0 (Term.func (cst k) (vars n)) A) ++ Γ) := hx
        cases hx' with
        | head => exact List.mem_append.mpr (Or.inr (List.Mem.head _))
        | tail _ hm =>
            rcases List.mem_append.mp hm with hl | hr
            · exact List.mem_append.mpr (Or.inl hl)
            · exact List.mem_append.mpr (Or.inr (List.Mem.tail _ hr))
      -- (2) retirar los axiomas interiores, que usan símbolos `≥ k+1`
      have hne : ∀ m, k + 1 ≤ m → cst m ≠ cst k := by
        intro m hm he
        exact absurd (cst_inj m k he) (by omega)
      have hΓ' : ∀ m, k + 1 ≤ m → ∀ g, g ∈ (skolemAxN (cst k) n A :: Γ) →
          Not (occursFormula (cst m) g) := by
        intro m hm g hg
        cases hg with
        | head => exact not_occurs_skolemAxN (hne m hm) (hAk m (by omega))
        | tail _ hmm => exact hΓ m (by omega) g hmm
      have hsub : ∀ m, k + 1 ≤ m →
          Not (occursFormula (cst m) (substFormula 0 (Term.func (cst k) (vars n)) A)) := by
        intro m hm
        refine not_occurs_substFormula (cst m) A 0 _ ?_ (hAk m (by omega))
        intro hc
        exact hc.elim (fun he => hne m hm he.symm) (fun hv => not_occurs_vars (cst m) n hv)
      have hstep : (skolemAxN (cst k) n A :: Γ) ⊢₀ χ :=
        skolem_conservative_listF fuel (k + 1) n _ _ χ hΓ' hsub
          (fun m hm => hχ m (by omega)) hperm
      -- (3) y el de este paso ya es `skolem_conservative_n`
      exact skolem_conservative_n
        (fun g hg => hΓ k (Nat.le_refl k) g hg) (hAk k (Nat.le_refl k))
        (hχ k (Nat.le_refl k)) hstep

theorem skolem_conservative_nf (k : Nat) (f : Formula) (Γ : List Formula) (χ : Formula)
    (hΓ : ∀ m, k ≤ m → ∀ g, g ∈ Γ → Not (occursFormula (cst m) g))
    (hf : ∀ m, k ≤ m → Not (occursFormula (cst m) f))
    (hχ : ∀ m, k ≤ m → Not (occursFormula (cst m) χ))
    (h : (skolemAxioms k f ++ Γ) ⊢₀ χ) : Γ ⊢₀ χ :=
  skolem_conservative_listF (qdepth f) k 0 f Γ χ hΓ hf hχ h

-- ═══════════════════════════════════════════════════════════════════════════
-- §6 · ⚠️ el puente que FALTABA: la frescura tiene que atravesar `prenex`
-- ═══════════════════════════════════════════════════════════════════════════

/-- ⚠️ **No existía.** El árbol tenía `occursTerm_lift`/`occursTerms_lift` y **nada** para
fórmulas. El levantamiento mueve **índices**, no **símbolos**. -/
theorem occursFormula_lift (c : String) : ∀ (f : Formula) (k : Nat),
    occursFormula c (liftFormula k f) → occursFormula c f
  | .bottom, _, h => h
  | .atom _ ts, k, h => occursTerms_lift c k ts h
  | .eq t u, k, h =>
      h.elim (fun ht => Or.inl (occursTerm_lift c k t ht))
             (fun hu => Or.inr (occursTerm_lift c k u hu))
  | .impl a b, k, h =>
      h.elim (fun ha => Or.inl (occursFormula_lift c a k ha))
             (fun hb => Or.inr (occursFormula_lift c b k hb))
  | .and a b, k, h =>
      h.elim (fun ha => Or.inl (occursFormula_lift c a k ha))
             (fun hb => Or.inr (occursFormula_lift c b k hb))
  | .or a b, k, h =>
      h.elim (fun ha => Or.inl (occursFormula_lift c a k ha))
             (fun hb => Or.inr (occursFormula_lift c b k hb))
  | .forall a, k, h => occursFormula_lift c a (k + 1) h
  | .ex a, k, h => occursFormula_lift c a (k + 1) h

theorem occurs_mergeAndR (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeAndR A B) → Or (occursFormula c A) (occursFormula c B)
  | A, .forall B', h =>
      (occurs_mergeAndR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | A, .ex B', h =>
      (occurs_mergeAndR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | _, .bottom, h => h
  | _, .atom _ _, h => h
  | _, .eq _ _, h => h
  | _, .impl _ _, h => h
  | _, .and _ _, h => h
  | _, .or _ _, h => h

theorem occurs_mergeAnd (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeAnd A B) → Or (occursFormula c A) (occursFormula c B)
  | .forall A', B, h =>
      (occurs_mergeAnd c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .ex A', B, h =>
      (occurs_mergeAnd c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .bottom, B, h => occurs_mergeAndR c _ B h
  | .atom _ _, B, h => occurs_mergeAndR c _ B h
  | .eq _ _, B, h => occurs_mergeAndR c _ B h
  | .impl _ _, B, h => occurs_mergeAndR c _ B h
  | .and _ _, B, h => occurs_mergeAndR c _ B h
  | .or _ _, B, h => occurs_mergeAndR c _ B h

theorem occurs_mergeOrR (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeOrR A B) → Or (occursFormula c A) (occursFormula c B)
  | A, .forall B', h =>
      (occurs_mergeOrR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | A, .ex B', h =>
      (occurs_mergeOrR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | _, .bottom, h => h
  | _, .atom _ _, h => h
  | _, .eq _ _, h => h
  | _, .impl _ _, h => h
  | _, .and _ _, h => h
  | _, .or _ _, h => h

theorem occurs_mergeOr (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeOr A B) → Or (occursFormula c A) (occursFormula c B)
  | .forall A', B, h =>
      (occurs_mergeOr c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .ex A', B, h =>
      (occurs_mergeOr c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .bottom, B, h => occurs_mergeOrR c _ B h
  | .atom _ _, B, h => occurs_mergeOrR c _ B h
  | .eq _ _, B, h => occurs_mergeOrR c _ B h
  | .impl _ _, B, h => occurs_mergeOrR c _ B h
  | .and _ _, B, h => occurs_mergeOrR c _ B h
  | .or _ _, B, h => occurs_mergeOrR c _ B h

theorem occurs_mergeImplR (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeImplR A B) → Or (occursFormula c A) (occursFormula c B)
  | A, .forall B', h =>
      (occurs_mergeImplR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | A, .ex B', h =>
      (occurs_mergeImplR c (liftFormula 0 A) B' h).elim
        (fun ha => Or.inl (occursFormula_lift c A 0 ha)) Or.inr
  | _, .bottom, h => h
  | _, .atom _ _, h => h
  | _, .eq _ _, h => h
  | _, .impl _ _, h => h
  | _, .and _ _, h => h
  | _, .or _ _, h => h

theorem occurs_mergeImpl (c : String) : ∀ (A B : Formula),
    occursFormula c (mergeImpl A B) → Or (occursFormula c A) (occursFormula c B)
  | .forall A', B, h =>
      (occurs_mergeImpl c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .ex A', B, h =>
      (occurs_mergeImpl c A' (liftFormula 0 B) h).elim
        Or.inl (fun hb => Or.inr (occursFormula_lift c B 0 hb))
  | .bottom, B, h => occurs_mergeImplR c _ B h
  | .atom _ _, B, h => occurs_mergeImplR c _ B h
  | .eq _ _, B, h => occurs_mergeImplR c _ B h
  | .impl _ _, B, h => occurs_mergeImplR c _ B h
  | .and _ _, B, h => occurs_mergeImplR c _ B h
  | .or _ _, B, h => occurs_mergeImplR c _ B h

/-- 🏁 **La forma normal prenexa no inventa símbolos** — y por eso la frescura viaja. -/
theorem occurs_prenex (c : String) : ∀ (f : Formula),
    occursFormula c (prenex f) → occursFormula c f
  | .bottom, h => h
  | .atom _ _, h => h
  | .eq _ _, h => h
  | .forall f, h => occurs_prenex c f h
  | .ex f, h => occurs_prenex c f h
  | .and a b, h =>
      (occurs_mergeAnd c _ _ h).elim
        (fun ha => Or.inl (occurs_prenex c a ha)) (fun hb => Or.inr (occurs_prenex c b hb))
  | .or a b, h =>
      (occurs_mergeOr c _ _ h).elim
        (fun ha => Or.inl (occurs_prenex c a ha)) (fun hb => Or.inr (occurs_prenex c b hb))
  | .impl a b, h =>
      (occurs_mergeImpl c _ _ h).elim
        (fun ha => Or.inl (occurs_prenex c a ha)) (fun hb => Or.inr (occurs_prenex c b hb))

theorem not_occurs_prenex {c : String} {f : Formula} (h : Not (occursFormula c f)) :
    Not (occursFormula c (prenex f)) := fun hc => h (occurs_prenex c f hc)

-- ═══════════════════════════════════════════════════════════════════════════
-- §7 · 🏁🏁 EL ENSAMBLAJE
-- ═══════════════════════════════════════════════════════════════════════════

/-- 🏁🏁 **Lo que se demuestra desde la forma normal de Skolem se demuestra sin ella.**

Basta que los símbolos `cst k, cst (k+1), …` sean frescos para el contexto y para la fórmula
—y eso lo entrega `FOL.Fresh0.cst_bound_formula` / `cst_bound_list`—.

⭐ Las tres piezas: la forma normal **implica** el prenexo (net‑0, §4), el prenexo es
**equivalente** al original (`derives0_prenex_iff`, ADR‑058), y los axiomas **se retiran**
(§5). La frescura atraviesa `prenex` por §6. -/
theorem derives0_of_skolemNF (k : Nat) (φ : Formula) (Γ : List Formula)
    (hΓ : ∀ m, k ≤ m → ∀ g, g ∈ Γ → Not (occursFormula (cst m) g))
    (hφ : ∀ m, k ≤ m → Not (occursFormula (cst m) φ))
    (h : (skolemAxioms k (prenex φ) ++ Γ) ⊢₀ skolemize k (prenex φ)) : Γ ⊢₀ φ := by
  have h1 : (skolemAxioms k (prenex φ) ++ Γ) ⊢₀ prenex φ :=
    derives0_of_skolemizeF _ _ _ _ _ h
  have h2 : (skolemAxioms k (prenex φ) ++ Γ) ⊢₀ φ :=
    (derives0_prenex_iff _ φ).mpr h1
  exact skolem_conservative_nf k (prenex φ) Γ φ hΓ
    (fun m hm => not_occurs_prenex (hφ m hm)) hφ h2

/-- 🏁 Y la salida de todo el proceso **es universal con matriz sin cuantificadores**, que es
lo que `FOL.Hauptsatz0.herbrand` pide. -/
theorem skolemNF_shape (k : Nat) (φ : Formula) :
    ∃ (m : Nat) (ψ : Formula),
      And (skolemize k (prenex φ) = allBlock m ψ) (QuantFree ψ) :=
  skolemize_shape k (prenex φ) (prenex_isPrenex φ)

end FOL.SkolemNF0

#print axioms FOL.SkolemNF0.qdepth_subst
#print axioms FOL.SkolemNF0.skolemizeF_shape
#print axioms FOL.SkolemNF0.skolemizeF_impAll
#print axioms FOL.SkolemNF0.occursFormula_lift
#print axioms FOL.SkolemNF0.occurs_prenex
#print axioms FOL.SkolemNF0.skolem_conservative_nf
#print axioms FOL.SkolemNF0.derives0_of_skolemNF
#print axioms FOL.SkolemNF0.skolemNF_shape
