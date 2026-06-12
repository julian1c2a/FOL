/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.FOL

/-!
# Meta-reglas de deducción (capa ω-meta sobre `Derives`)

Reglas de deducción en **formulación meta-función**, distintas de los
constructores de `Derives` (que usan hipótesis-en-contexto, `A :: Γ ⊢ B`).
Aquí las hipótesis son funciones Lean (`Γ ⊢ A → Γ ⊢ B`) y, en `gen`, la
**ω-regla** (`∀ n : Term, Γ ⊢ A[n] → Γ ⊢ ∀A`).

**Estatus**: `imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim` son **axiomas**.
No son derivables de los constructores de `Derives` (la hipótesis meta-función
no se reduce a hipótesis-en-contexto sin inspeccionar el término de prueba).
Junto con la ω-regla `gen`, axiomatizan "demostrabilidad = verdad en el modelo
estándar": el sistema resultante es **sólido y completo relativo a ℕ** (es
ω-lógica, estrictamente más fuerte que FOL= finitaria). Los constructores
finitarios y sólidos para *todo* modelo son `Derives.intro_impl`,
`Derives.elim_or`, `Derives.elim_ex`, `Derives.intro_forall`.

El resto (`mp`, `and_intro`, `and_elim_*`, `or_intro_*`, `false_elim`,
`ex_intro`, `iff_mp`, `iff_mpr`) son **wrappers derivables** de los
constructores de `Derives` (no axiomas).

**Procedencia**: extraídos de `ROBINSON_PlusPlus/Minimal/Axioms.lean`
(2026-06-12) — eran lógica pura de FOL= viviendo en el módulo de axiomas
aritméticos. `Minimal.Axioms` los re-exporta para compatibilidad. Ver ADR-008.
-/

namespace FOL.MetaRules

/-- Modus ponens: from `Γ ⊢ A ⇒ B` and `Γ ⊢ A`, conclude `Γ ⊢ B`. -/
def mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B h1 h2

/-- Implication introduction (meta-función → implicación object).
    **Meta-axioma** ω: sólido relativo al modelo estándar. -/
axiom imp_intro {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)

/-- Generalización universal (**ω-regla**): de `∀ n, Γ ⊢ A[n]` concluye `Γ ⊢ ∀A`.
    **Meta-axioma**: no derivable de `Derives.intro_forall` (que es finitario). -/
axiom gen {Γ : List Formula} {A : Formula} (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) :
    Γ ⊢ Formula.forall A

/-- Reducción al absurdo (clásica): de `Γ ⊢ A → ⊥` concluye `Γ ⊢ ¬A`.
    **Meta-axioma** ω. -/
axiom raa {Γ : List Formula} {A : Formula} (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A

/-- Conjunction introduction (wrapper de `Derives.intro_and`). -/
def and_intro {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ A) (h2 : Γ ⊢ B) : Γ ⊢ (A ∧ B) :=
  Derives.intro_and Γ A B h1 h2

/-- Left conjunction elimination (wrapper de `Derives.elim_and_l`). -/
def and_elim_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ A :=
  Derives.elim_and_l Γ A B h

/-- Right conjunction elimination (wrapper de `Derives.elim_and_r`). -/
def and_elim_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ B :=
  Derives.elim_and_r Γ A B h

/-- Left disjunction introduction (wrapper de `Derives.intro_or_l`). -/
def or_intro_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_l Γ A B h

/-- Right disjunction introduction (wrapper de `Derives.intro_or_r`). -/
def or_intro_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ B) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_r Γ A B h

/-- Disjunction elimination (case split meta-nivel).
    **Meta-axioma** ω: usa hipótesis meta-función `Γ ⊢ A → Γ ⊢ C`. -/
axiom or_elim {Γ : List Formula} {A B C : Formula}
    (h : Γ ⊢ (A ∨ B)) (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C

/-- False elimination / ex falso (wrapper de `Derives.bot_elim`). -/
def false_elim {Γ : List Formula} {A : Formula} (h : Γ ⊢ ⊥) : Γ ⊢ A :=
  Derives.bot_elim Γ A h

/-- Existential introduction (wrapper de `Derives.intro_ex`). -/
def ex_intro {Γ : List Formula} {A : Formula} (t : Term)
    (h : Γ ⊢ substFormula 0 t A) : Γ ⊢ Formula.ex A :=
  Derives.intro_ex Γ A t h

/-- Existential elimination (extracción de testigo meta-nivel).
    **Meta-axioma** ω: usa hipótesis meta-función. -/
axiom ex_elim {Γ : List Formula} {A C : Formula}
    (h : Γ ⊢ Formula.ex A)
    (cont : ∀ t : Term, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C

/-- Forward direction of biconditional (wrapper). -/
def iff_mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B (Derives.elim_and_l Γ (A ⇒ B) (B ⇒ A) h1) h2

/-- Backward direction of biconditional (wrapper). -/
def iff_mpr {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ B) : Γ ⊢ A :=
  Derives.elim_impl Γ B A (Derives.elim_and_r Γ (A ⇒ B) (B ⇒ A) h1) h2

end FOL.MetaRules
