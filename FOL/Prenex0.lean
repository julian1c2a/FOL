/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Herbrand0, FOL.Lift0
-- @axiom_system: classical
-- @importance: high

import FOL.Herbrand0
import FOL.Lift0

/-!
# `FOL.Prenex0` — la CAPA PRENEXA sobre `Derives₀`: las ocho equivalencias de desplazamiento

Las ocho formas de **sacar un cuantificador** de debajo de una conectiva, demostradas sobre
`Derives₀`. Es lo que hace falta para hablar de forma prenexa — y, detrás, de skolemización.

| | equivalencia | ¿clásica? |
|---|---|---|
| 1 | `(∀A) ∧ B  ↔  ∀(A ∧ B↑)` | no |
| 2 | `(∃A) ∧ B  ↔  ∃(A ∧ B↑)` | no |
| 3 | `(∀A) ∨ B  ↔  ∀(A ∨ B↑)` | ⚠️ la vuelta, sí |
| 4 | `(∃A) ∨ B  ↔  ∃(A ∨ B↑)` | no |
| 5 | `(∀A) → B  ↔  ∃(A → B↑)` | ⚠️ la ida, sí |
| 6 | `(∃A) → B  ↔  ∀(A → B↑)` | no |
| 7 | `B → (∀A)  ↔  ∀(B↑ → A)` | no |
| 8 | `B → (∃A)  ↔  ∃(B↑ → A)` | ⚠️ la ida, sí |

## ⭐ «La variable no aparece en `B`» se dice `liftFormula 0 B`

En De Bruijn no hay nombres, así que la condición lateral clásica —*x no libre en B*— no se
enuncia: **se construye**. `B↑` es `liftFormula 0 B`, y por eso `B` no puede mencionar la variable
recién ligada. 🔑 *Una condición lateral que se codifica en el TIPO no hay que comprobarla.*

## ⭐⭐ El truco que hace las ocho pruebas

Bajo un binder, `intro_forall` **levanta el contexto**, así que la hipótesis `∀A` llega como
`∀(A↑¹)`. Se instancia en `Term.var 0` y `substFormula_lift_var` la devuelve **intacta**:

    inst_var0 : substFormula 0 (Term.var 0) (liftFormula 1 A) = A

Esa línea aparece en siete de las ocho. La otra usa `substFormula_liftFormula`, para el caso en que
lo que hay que devolver es el `B` de fuera.

## ⚠️ Y la lógica clásica NO entra por Lean

Las tres direcciones clásicas salen de `derives0_em_ctx` (`FOL.Propositional0`, **sin ningún
axioma**) y del constructor `Derives₀.forall_not_ex_not`. ⇒ footprint `[propext, Quot.sound]`:
**ni un `Classical.choice`**. 🔑 *La fuerza clásica de este cálculo está en sus CONSTRUCTORES, no en
el metanivel* — y por eso se puede usar sin encarecer el footprint.

## ⬜ Lo que falta para la forma normal

Estas ocho son el **motor**. Falta la **función** `prenex : Formula → Formula` con su terminación y
su teorema de corrección (`Γ ⊢₀ φ ↔ Γ ⊢₀ prenex φ`), que es una recursión sobre la estructura con
una medida que decrece. ⬜ Estimado ~200 l., riesgo medio: lo que cuesta no son las equivalencias
—están aquí— sino la **medida de terminación**.

## 📏 Footprint

Las ocho, `[propext, Quot.sound]`. **Ni un `Classical.choice`.**
-/

namespace FOL.Prenex0

open FOL.Lift0
open FOL.Propositional0
open FOL.Herbrand0

/-- ⭐ Bajo un binder, la hipótesis levantada se instancia en `var 0` y vuelve intacta. -/
theorem inst_var0 (A : Formula) : substFormula 0 (Term.var 0) (liftFormula 1 A) = A :=
  substFormula_lift_var A 0

-- ── (1) ∧ / ∀ ───────────────────────────────────────────────────────────────
theorem and_forall (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.and (Formula.forall A) B)
             (Formula.forall (Formula.and A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.intro_forall _ _ ?_
    have hy : (Formula.and (Formula.forall (liftFormula 1 A)) (liftFormula 0 B)
                :: Γ.map (liftFormula 0)) ⊢₀
        Formula.and (Formula.forall (liftFormula 1 A)) (liftFormula 0 B) :=
      Derives₀.hyp _ _ (List.Mem.head _)
    refine Derives₀.intro_and _ _ _ ?_ (Derives₀.elim_and_r _ _ _ hy)
    have h1 := Derives₀.elim_forall _ (liftFormula 1 A) (Term.var 0)
      (Derives₀.elim_and_l _ _ _ hy)
    rwa [inst_var0 A] at h1
  · have hy : (Formula.forall (Formula.and A (liftFormula 0 B)) :: Γ) ⊢₀
        Formula.forall (Formula.and A (liftFormula 0 B)) := Derives₀.hyp _ _ (List.Mem.head _)
    refine Derives₀.intro_and _ _ _ ?_ ?_
    · refine Derives₀.intro_forall _ _ ?_
      have hl := FOL.Lift0.derives0_lift hy 0
      have h1 := Derives₀.elim_forall _ (liftFormula 1 (Formula.and A (liftFormula 0 B)))
        (Term.var 0) hl
      rw [inst_var0 (Formula.and A (liftFormula 0 B))] at h1
      exact Derives₀.elim_and_l _ _ _ h1
    · have h1 := Derives₀.elim_forall _ (Formula.and A (liftFormula 0 B)) (Term.var 0) hy
      have h2 := Derives₀.elim_and_r _ _ _ h1
      rwa [FOL.substFormula_liftFormula B 0 (Term.var 0)] at h2

-- ── (2) → / ∃ a la izquierda ────────────────────────────────────────────────
theorem impl_ex_left (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.impl (Formula.ex A) B)
             (Formula.forall (Formula.impl A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.intro_forall _ _ (Derives₀.intro_impl _ _ _ ?_)
    -- contexto: A :: lift(impl (ex A) B) :: Γ.map lift
    have hy : (A :: Formula.impl (Formula.ex (liftFormula 1 A)) (liftFormula 0 B)
                 :: Γ.map (liftFormula 0)) ⊢₀
        Formula.impl (Formula.ex (liftFormula 1 A)) (liftFormula 0 B) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    refine Derives₀.elim_impl _ _ _ hy ?_
    refine Derives₀.intro_ex _ (liftFormula 1 A) (Term.var 0) ?_
    rw [inst_var0 A]
    exact Derives₀.hyp _ _ (List.Mem.head _)
  · have hy : (Formula.forall (Formula.impl A (liftFormula 0 B)) :: Γ) ⊢₀
        Formula.forall (Formula.impl A (liftFormula 0 B)) := Derives₀.hyp _ _ (List.Mem.head _)
    refine Derives₀.intro_impl _ _ _ ?_
    -- Δ = ex A :: ∀(A → B↑) :: Γ ; se elimina el ∃
    refine Derives₀.elim_ex _ A B (Derives₀.hyp _ _ (List.Mem.head _)) ?_
    -- contexto: A :: (ex A :: ∀(...) :: Γ).map lift ; hay que aplicar la ∀ levantada
    have hl : (A :: (Formula.ex A :: Formula.forall (Formula.impl A (liftFormula 0 B)) :: Γ).map
                (liftFormula 0)) ⊢₀
        Formula.forall (liftFormula 1 (Formula.impl A (liftFormula 0 B))) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have h1 := Derives₀.elim_forall _ (liftFormula 1 (Formula.impl A (liftFormula 0 B)))
      (Term.var 0) hl
    rw [inst_var0 (Formula.impl A (liftFormula 0 B))] at h1
    exact Derives₀.elim_impl _ _ _ h1 (Derives₀.hyp _ _ (List.Mem.head _))

-- ── (2) ∧ / ∃ ───────────────────────────────────────────────────────────────
theorem and_ex (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.and (Formula.ex A) B)
             (Formula.ex (Formula.and A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · have hy : (Formula.and (Formula.ex A) B :: Γ) ⊢₀ Formula.and (Formula.ex A) B :=
      Derives₀.hyp _ _ (List.Mem.head _)
    refine Derives₀.elim_ex _ A _ (Derives₀.elim_and_l _ _ _ hy) ?_
    -- contexto: A :: (and (ex A) B :: Γ).map lift ; objetivo: lift (ex (A ∧ B↑))
    have hB : (A :: (Formula.and (Formula.ex A) B :: Γ).map (liftFormula 0)) ⊢₀ liftFormula 0 B :=
      Derives₀.elim_and_r _ (Formula.ex (liftFormula 1 A)) _
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    refine Derives₀.intro_ex _ (Formula.and (liftFormula 1 A) (liftFormula 1 (liftFormula 0 B)))
      (Term.var 0) ?_
    show _ ⊢₀ Formula.and (substFormula 0 (Term.var 0) (liftFormula 1 A))
                          (substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B)))
    rw [inst_var0 A, inst_var0 (liftFormula 0 B)]
    exact Derives₀.intro_and _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)) hB
  · have hy : (Formula.ex (Formula.and A (liftFormula 0 B)) :: Γ) ⊢₀
        Formula.ex (Formula.and A (liftFormula 0 B)) := Derives₀.hyp _ _ (List.Mem.head _)
    refine Derives₀.elim_ex _ (Formula.and A (liftFormula 0 B)) _ hy ?_
    have hh := Derives₀.hyp
      (Formula.and A (liftFormula 0 B)
         :: (Formula.ex (Formula.and A (liftFormula 0 B)) :: Γ).map (liftFormula 0))
      (Formula.and A (liftFormula 0 B)) (List.Mem.head _)
    refine Derives₀.intro_and _ _ _ ?_ (Derives₀.elim_and_r _ _ _ hh)
    refine Derives₀.intro_ex _ (liftFormula 1 A) (Term.var 0) ?_
    rw [inst_var0 A]
    exact Derives₀.elim_and_l _ _ _ hh

-- ── (4) ∨ / ∃ ───────────────────────────────────────────────────────────────
theorem or_ex (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.or (Formula.ex A) B)
             (Formula.ex (Formula.or A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.elim_or _ (Formula.ex A) B _ (Derives₀.hyp _ _ (List.Mem.head _)) ?_ ?_
    · refine Derives₀.elim_ex _ A _ (Derives₀.hyp _ _ (List.Mem.head _)) ?_
      refine Derives₀.intro_ex _ (Formula.or (liftFormula 1 A) (liftFormula 1 (liftFormula 0 B)))
        (Term.var 0) ?_
      show _ ⊢₀ Formula.or (substFormula 0 (Term.var 0) (liftFormula 1 A))
                           (substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B)))
      rw [inst_var0 A, inst_var0 (liftFormula 0 B)]
      exact Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
    · refine Derives₀.intro_ex _ (Formula.or A (liftFormula 0 B)) (Term.var 0) ?_
      show _ ⊢₀ Formula.or (substFormula 0 (Term.var 0) A)
                           (substFormula 0 (Term.var 0) (liftFormula 0 B))
      rw [FOL.substFormula_liftFormula B 0 (Term.var 0)]
      exact Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
  · refine Derives₀.elim_ex _ (Formula.or A (liftFormula 0 B)) _
      (Derives₀.hyp _ _ (List.Mem.head _)) ?_
    refine Derives₀.elim_or _ A (liftFormula 0 B) _ (Derives₀.hyp _ _ (List.Mem.head _)) ?_ ?_
    · refine Derives₀.intro_or_l _ _ _ ?_
      refine Derives₀.intro_ex _ (liftFormula 1 A) (Term.var 0) ?_
      rw [inst_var0 A]
      exact Derives₀.hyp _ _ (List.Mem.head _)
    · exact Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))

-- ── (7) → / ∀ a la derecha ──────────────────────────────────────────────────
theorem impl_forall_right (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.impl B (Formula.forall A))
             (Formula.forall (Formula.impl (liftFormula 0 B) A)) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.intro_forall _ _ (Derives₀.intro_impl _ _ _ ?_)
    have hy : (liftFormula 0 B :: Formula.impl (liftFormula 0 B)
                 (Formula.forall (liftFormula 1 A)) :: Γ.map (liftFormula 0)) ⊢₀
        Formula.impl (liftFormula 0 B) (Formula.forall (liftFormula 1 A)) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have h1 := Derives₀.elim_impl _ _ _ hy (Derives₀.hyp _ _ (List.Mem.head _))
    have h2 := Derives₀.elim_forall _ (liftFormula 1 A) (Term.var 0) h1
    rwa [inst_var0 A] at h2
  · refine Derives₀.intro_impl _ _ _ (Derives₀.intro_forall _ _ ?_)
    have hy : (B :: Formula.forall (Formula.impl (liftFormula 0 B) A) :: Γ).map
                (liftFormula 0) ⊢₀
        Formula.forall (liftFormula 1 (Formula.impl (liftFormula 0 B) A)) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have h1 := Derives₀.elim_forall _ (liftFormula 1 (Formula.impl (liftFormula 0 B) A))
      (Term.var 0) hy
    rw [inst_var0 (Formula.impl (liftFormula 0 B) A)] at h1
    exact Derives₀.elim_impl _ _ _ h1 (Derives₀.hyp _ _ (List.Mem.head _))

-- ── (3) ∨ / ∀ ─ la vuelta necesita TERCIO EXCLUIDO ──────────────────────────
theorem or_forall (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.or (Formula.forall A) B)
             (Formula.forall (Formula.or A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.elim_or _ (Formula.forall A) B _ (Derives₀.hyp _ _ (List.Mem.head _)) ?_ ?_
    · refine Derives₀.intro_forall _ _ ?_
      have hall : (Formula.forall (liftFormula 1 A)
                     :: (Formula.or (Formula.forall A) B :: Γ).map (liftFormula 0)) ⊢₀
          Formula.forall (liftFormula 1 A) := Derives₀.hyp _ _ (List.Mem.head _)
      have h1 := Derives₀.elim_forall _ (liftFormula 1 A) (Term.var 0) hall
      rw [inst_var0 A] at h1
      exact Derives₀.intro_or_l _ _ _ h1
    · refine Derives₀.intro_forall _ _ ?_
      exact Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ (liftFormula 0 B) (List.Mem.head _))
  · refine Derives₀.elim_or _ B (neg B) _ (derives0_em_ctx _ B) ?_ ?_
    · exact Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))
    · refine Derives₀.intro_or_l _ _ _ (Derives₀.intro_forall _ _ ?_)
      have hall := Derives₀.hyp
        (((neg B) :: Formula.forall (Formula.or A (liftFormula 0 B)) :: Γ).map (liftFormula 0))
        (Formula.forall (liftFormula 1 (Formula.or A (liftFormula 0 B))))
        (List.Mem.tail _ (List.Mem.head _))
      have h1 := Derives₀.elim_forall _ (liftFormula 1 (Formula.or A (liftFormula 0 B)))
        (Term.var 0) hall
      rw [inst_var0 (Formula.or A (liftFormula 0 B))] at h1
      refine Derives₀.elim_or _ A (liftFormula 0 B) _ h1 (Derives₀.hyp _ _ (List.Mem.head _)) ?_
      refine Derives₀.bot_elim _ _ ?_
      exact Derives₀.elim_impl _ (liftFormula 0 B) Formula.bottom
        (Derives₀.hyp _ (neg (liftFormula 0 B)) (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))

-- ── (5) → / ∀ a la izquierda ─ la ida necesita TERCIO EXCLUIDO ──────────────
theorem impl_forall_left (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.impl (Formula.forall A) B)
             (Formula.ex (Formula.impl A (liftFormula 0 B))) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.elim_or _ B (neg B) _ (derives0_em_ctx _ B) ?_ ?_
    · refine Derives₀.intro_ex _ (Formula.impl A (liftFormula 0 B)) (Term.var 0) ?_
      show _ ⊢₀ Formula.impl (substFormula 0 (Term.var 0) A)
                             (substFormula 0 (Term.var 0) (liftFormula 0 B))
      rw [FOL.substFormula_liftFormula B 0 (Term.var 0)]
      exact Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    · -- ¬B ⇒ ¬∀A ⇒ ∃¬A, y de ¬A sale A → B↑
      have hnall : ((neg B) :: Formula.impl (Formula.forall A) B :: Γ) ⊢₀
          neg (Formula.forall A) := by
        refine Derives₀.intro_impl _ _ _ ?_
        exact Derives₀.elim_impl _ B Formula.bottom
          (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
          (Derives₀.elim_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.head _)))) (Derives₀.hyp _ _ (List.Mem.head _)))
      have hex := Derives₀.elim_impl _ _ _ (Derives₀.forall_not_ex_not _ A) hnall
      refine Derives₀.elim_ex _ (neg A) _ hex ?_
      refine Derives₀.intro_ex _ (Formula.impl (liftFormula 1 A) (liftFormula 1 (liftFormula 0 B)))
        (Term.var 0) ?_
      show _ ⊢₀ Formula.impl (substFormula 0 (Term.var 0) (liftFormula 1 A))
                             (substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B)))
      rw [inst_var0 A, inst_var0 (liftFormula 0 B)]
      refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
      exact Derives₀.elim_impl _ A Formula.bottom
        (Derives₀.hyp _ (neg A) (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))
  · refine Derives₀.intro_impl _ _ _ ?_
    refine Derives₀.elim_ex _ (Formula.impl A (liftFormula 0 B)) _
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
    have hall := Derives₀.hyp
      (Formula.impl A (liftFormula 0 B)
         :: (Formula.forall A :: Formula.ex (Formula.impl A (liftFormula 0 B)) :: Γ).map
              (liftFormula 0))
      (Formula.forall (liftFormula 1 A)) (List.Mem.tail _ (List.Mem.head _))
    have h1 := Derives₀.elim_forall _ (liftFormula 1 A) (Term.var 0) hall
    rw [inst_var0 A] at h1
    exact Derives₀.elim_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)) h1

-- ── (8) → / ∃ a la derecha ─ la ida necesita TERCIO EXCLUIDO ────────────────
theorem impl_ex_right (Γ : List Formula) (A B : Formula) :
    Γ ⊢₀ iff (Formula.impl B (Formula.ex A))
             (Formula.ex (Formula.impl (liftFormula 0 B) A)) := by
  refine Derives₀.intro_and _ _ _ (Derives₀.intro_impl _ _ _ ?_) (Derives₀.intro_impl _ _ _ ?_)
  · refine Derives₀.elim_or _ B (neg B) _ (derives0_em_ctx _ B) ?_ ?_
    · have hex : (B :: Formula.impl B (Formula.ex A) :: Γ) ⊢₀ Formula.ex A :=
        Derives₀.elim_impl _ B (Formula.ex A)
          (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
          (Derives₀.hyp _ _ (List.Mem.head _))
      refine Derives₀.elim_ex _ A _ hex ?_
      refine Derives₀.intro_ex _ (Formula.impl (liftFormula 1 (liftFormula 0 B)) (liftFormula 1 A))
        (Term.var 0) ?_
      show _ ⊢₀ Formula.impl (substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B)))
                             (substFormula 0 (Term.var 0) (liftFormula 1 A))
      rw [inst_var0 (liftFormula 0 B), inst_var0 A]
      exact Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    · refine Derives₀.intro_ex _ (Formula.impl (liftFormula 0 B) A) (Term.var 0) ?_
      show _ ⊢₀ Formula.impl (substFormula 0 (Term.var 0) (liftFormula 0 B))
                             (substFormula 0 (Term.var 0) A)
      rw [FOL.substFormula_liftFormula B 0 (Term.var 0)]
      refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
      exact Derives₀.elim_impl _ B Formula.bottom
        (Derives₀.hyp _ (neg B) (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))
  · refine Derives₀.intro_impl _ _ _ ?_
    refine Derives₀.elim_ex _ (Formula.impl (liftFormula 0 B) A) _
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
    have hB := Derives₀.hyp
      (Formula.impl (liftFormula 0 B) A
         :: (B :: Formula.ex (Formula.impl (liftFormula 0 B) A) :: Γ).map (liftFormula 0))
      (liftFormula 0 B) (List.Mem.tail _ (List.Mem.head _))
    have hA := Derives₀.elim_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.head _)) hB
    refine Derives₀.intro_ex _ (liftFormula 1 A) (Term.var 0) ?_
    rw [inst_var0 A]
    exact hA

/-- Forma prenexa: un prefijo de cuantificadores y detrás nada de cuantificadores. -/
def Prenex : Formula → Prop
  | .forall f => Prenex f
  | .ex f => Prenex f
  | .bottom => True
  | .atom _ _ => True
  | .eq _ _ => True
  | .impl a b => And (QuantFree a) (QuantFree b)
  | .and a b => And (QuantFree a) (QuantFree b)
  | .or a b => And (QuantFree a) (QuantFree b)

theorem prenex_of_quantFree : ∀ (f : Formula), QuantFree f → Prenex f
  | .bottom, _ => trivial
  | .atom _ _, _ => trivial
  | .eq _ _, _ => trivial
  | .impl _ _, h => h
  | .and _ _, h => h
  | .or _ _, h => h

end FOL.Prenex0

#print axioms FOL.Prenex0.and_forall
#print axioms FOL.Prenex0.and_ex
#print axioms FOL.Prenex0.or_forall
#print axioms FOL.Prenex0.or_ex
#print axioms FOL.Prenex0.impl_forall_left
#print axioms FOL.Prenex0.impl_ex_left
#print axioms FOL.Prenex0.impl_forall_right
#print axioms FOL.Prenex0.impl_ex_right
