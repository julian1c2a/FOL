/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives1, FOL.Theorems.Eq
-- @axiom_system: classical
-- @importance: high

import FOL.Derives1
import FOL.Theorems.Eq

/-!
# `FOL.Derives2` — **`subst` es ADMISIBLE**: el segundo obstáculo de H3, retirado

Segunda pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.5). ADR‑044 dejó el frente en
**un** obstáculo: `subst`, la regla de Leibniz, que *no elimina la igualdad sino que la convierte
en teoría*. Éste es el módulo que la retira.

    Derives₂               -- `Derives₁` SIN `subst`, con las TRES congruencias primitivas
    eq_substFormula        -- ⭐⭐ Leibniz, DEMOSTRADO a partir de ellas
    derives1_iff_derives2  -- y los dos cálculos derivan EXACTAMENTE lo mismo

⇒ Con ADR‑044 y esto, **`Derives₂` es deducción natural clásica de libro más los axiomas de la
igualdad**, que es exactamente la forma en que la literatura enuncia Herbrand con `=`.
**Los dos obstáculos que ADR‑043 §3 había contado ya no están.**

## Qué sustituye a `subst`

Tres constructores, y son **instancias de los axiomas de la igualdad**, no una regla de inferencia
sobre fórmulas arbitrarias:

| constructor | qué dice |
|---|---|
| `eq_func_congr` | `a ≐ b ⟹ f(…a…) ≐ f(…b…)`, **en UNA posición** |
| `eq_atom_congr` | `a ≐ b ⟹ P(…a…) ⟹ P(…b…)`, **en UNA posición** |
| `eq_eq_congr` | `a ≐ b ⟹ a ≐ c ⟹ b ≐ c` — la congruencia de `≐` en su primer argumento |

⭐ **Simetría y transitividad NO hacen falta como primitivas**: salen de `eq_eq_congr` + `refl` en
una línea cada una. Y `eq_eq_congr` sí hace falta porque `Formula.eq` es un **constructor propio**,
no un `atom`, así que `eq_atom_congr` no lo alcanza.

## ⭐⭐ Por qué la reducción es fina, y no una reorganización

`subst` es Leibniz para **cualquier** fórmula `f`; las tres congruencias son de **una posición** y
**atómicas**. Que la primera se siga de las segundas es el contenido de este módulo, y se demuestra
en dos escalones:

1. **Leibniz de TÉRMINOS** (`eq_substTerm`), por recursión mutua con `eq_substTerms`: en el caso
   `func` hay que subir de igualdades **punto a punto** de la lista de argumentos a la igualdad de
   los dos términos, y eso es `eq_func_pw` — la congruencia de una posición **iterada con un
   prefijo que crece**. 🔑 *Lo que faltaba no era lógica sino LISTAS*, otra vez (ADR‑031).
2. **Leibniz de FÓRMULAS** (`eq_substFormula`), por inducción estructural.

## ⭐ Los tres puntos finos de la inducción de fórmulas

* **`impl` es contravariante** — pero aquí **no hace falta un enunciado bicondicional** (a
  diferencia de ADR‑044): el enunciado ya es simétrico en `t₁`/`t₂`, así que basta aplicar la
  hipótesis de inducción **con los términos intercambiados** y la ecuación simétrica. *Cuando la
  simetría está en los datos, no hay que meterla en el enunciado.*
* **`eq`** se cierra con `eq_eq_congr` en el primer argumento y **transitividad** en el segundo.
* ⛔ **`forall`/`ex` obligan a que la ecuación VIAJE al contexto levantado**, porque
  `substFormula v t (∀A) = ∀ (substFormula (v+1) (liftTerm 0 t) A)`: cambia el índice **y** levanta
  el término. De ahí `derives2_lift`, que es una inducción entera sobre `Derives₂` (22 casos) y
  la mitad del coste del módulo. El cierre es otra vez `substFormula_lift_var`.

## ⚠️ El dato medido que ordenó el trabajo

ADR‑044 §4 midió que las cuatro piezas de `FOL/Eq0.lean` —simetría, transitividad y las dos
congruencias— están **derivadas de `subst`**. ⇒ no se podían conservar como teoremas al quitarlo:
había que **subirlas a constructores**. Este módulo hace eso, y paga la deuda en la otra
dirección: `derives2_to_derives1` demuestra que las tres nuevas **son derivables** en `Derives₁`,
así que `Derives₂` no es más fuerte.

## 📏 Footprint

`[propext, Quot.sound]`. **Ni un `Classical.choice`.** ⭐ Y `Derives₂.rec` **no depende de ningún
axioma**.

## ⬜ Lo que sigue faltando para H3

**El Hauptsatz.** Esto no elimina cortes: pone el cálculo en la forma en que el Hauptsatz se puede
plantear. Siguen siendo «de corte» `elim_impl`, `elim_and_l/r`, `elim_or` y `elim_ex` — los cinco
**estándar**, que es de lo que trata Gentzen.
-/

inductive Derives₂ : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives₂ Γ f
  | intro_impl : ∀ Γ A B, Derives₂ (A :: Γ) B → Derives₂ Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives₂ Γ (.impl A B) → Derives₂ Γ A → Derives₂ Γ B
  | intro_and  : ∀ Γ A B, Derives₂ Γ A → Derives₂ Γ B → Derives₂ Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives₂ Γ (.and A B) → Derives₂ Γ A
  | elim_and_r : ∀ Γ A B, Derives₂ Γ (.and A B) → Derives₂ Γ B
  | intro_or_l : ∀ Γ A B, Derives₂ Γ A → Derives₂ Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives₂ Γ B → Derives₂ Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives₂ Γ (.or A B) → Derives₂ (A :: Γ) C → Derives₂ (B :: Γ) C →
      Derives₂ Γ C
  | intro_forall : ∀ Γ A, Derives₂ (Γ.map (liftFormula 0)) A → Derives₂ Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives₂ Γ (.forall A) → Derives₂ Γ (substFormula 0 t A)
  | intro_ex : ∀ Γ A t, Derives₂ Γ (substFormula 0 t A) → Derives₂ Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives₂ Γ (.ex A) →
      Derives₂ (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives₂ Γ B
  | bot_elim : ∀ Γ A, Derives₂ Γ ⊥ → Derives₂ Γ A
  | weakening : ∀ Γ Γ' f, Derives₂ Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives₂ Γ' f
  | dne_rule : ∀ Γ A, Derives₂ Γ (neg (neg A)) → Derives₂ Γ A
  | dne_schema : ∀ Γ A, Derives₂ Γ (.impl (neg (neg A)) A)
  | forall_not_ex_not : ∀ Γ A, Derives₂ Γ (.impl (neg (.forall A)) (.ex (neg A)))
  | refl  : ∀ Γ t, Derives₂ Γ (.eq t t)
  -- ⭐ las TRES congruencias, en lugar de `subst`
  | eq_func_congr : ∀ Γ (p : String) (pre post : List Term) (a b : Term),
      Derives₂ Γ (.eq a b) →
      Derives₂ Γ (.eq (Term.func p (pre ++ a :: post)) (Term.func p (pre ++ b :: post)))
  | eq_atom_congr : ∀ Γ (p : String) (pre post : List Term) (a b : Term),
      Derives₂ Γ (.eq a b) → Derives₂ Γ (.atom p (pre ++ a :: post)) →
      Derives₂ Γ (.atom p (pre ++ b :: post))
  | eq_eq_congr : ∀ Γ (a b c : Term),
      Derives₂ Γ (.eq a b) → Derives₂ Γ (.eq a c) → Derives₂ Γ (.eq b c)

infix:50 " ⊢₂ " => Derives₂

namespace FOL.Derives2

open FOL.Lift0

-- ── simetría y transitividad, derivadas de `eq_eq_congr` + `refl` ───────────
theorem eq_symm {Γ : List Formula} {a b : Term} (h : Γ ⊢₂ Formula.eq a b) :
    Γ ⊢₂ Formula.eq b a := Derives₂.eq_eq_congr Γ a b a h (Derives₂.refl Γ a)

theorem eq_trans {Γ : List Formula} {a b c : Term}
    (h1 : Γ ⊢₂ Formula.eq a b) (h2 : Γ ⊢₂ Formula.eq b c) : Γ ⊢₂ Formula.eq a c :=
  Derives₂.eq_eq_congr Γ b a c (eq_symm h1) h2

-- ── la conmutación que falta: `liftTerms` con `++` ──────────────────────────
theorem liftTerms_append (k : Nat) : ∀ (l1 l2 : List Term),
    liftTerms k (l1 ++ l2) = liftTerms k l1 ++ liftTerms k l2
  | [], _ => rfl
  | t :: l, l2 => by
      show liftTerm k t :: liftTerms k (l ++ l2)
            = (liftTerm k t :: liftTerms k l) ++ liftTerms k l2
      rw [liftTerms_append k l l2]
      rfl

-- ── §2 · el levantamiento ───────────────────────────────────────────────────
theorem derives2_lift {Γ : List Formula} {φ : Formula} (h : Γ ⊢₂ φ) :
    ∀ k : Nat, (Γ.map (liftFormula k)) ⊢₂ liftFormula k φ := by
  induction h with
  | hyp Γ' f' hIn => intro k; exact Derives₂.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih => intro k; exact Derives₂.intro_impl _ _ _ (ih k)
  | elim_impl Γ' A B _ _ ih1 ih2 => intro k; exact Derives₂.elim_impl _ _ _ (ih1 k) (ih2 k)
  | intro_and Γ' A B _ _ ih1 ih2 => intro k; exact Derives₂.intro_and _ _ _ (ih1 k) (ih2 k)
  | elim_and_l Γ' A B _ ih => intro k; exact Derives₂.elim_and_l _ _ _ (ih k)
  | elim_and_r Γ' A B _ ih => intro k; exact Derives₂.elim_and_r _ _ _ (ih k)
  | intro_or_l Γ' A B _ ih => intro k; exact Derives₂.intro_or_l _ _ _ (ih k)
  | intro_or_r Γ' A B _ ih => intro k; exact Derives₂.intro_or_r _ _ _ (ih k)
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 =>
      intro k; exact Derives₂.elim_or _ _ _ _ (ih1 k) (ih2 k) (ih3 k)
  | intro_forall Γ' A _ ih =>
      intro k
      refine Derives₂.intro_forall _ _ ?_
      rw [map_lift_lift]
      exact ih (k + 1)
  | elim_forall Γ' A t _ ih =>
      intro k
      have hh := Derives₂.elim_forall (Γ'.map (liftFormula k)) (liftFormula (k + 1) A)
                (liftTerm k t) (ih k)
      rw [liftFormula_subst A 0 k (Nat.zero_le _)]
      exact hh
  | intro_ex Γ' A t _ ih =>
      intro k
      refine Derives₂.intro_ex _ _ (liftTerm k t) ?_
      rw [← liftFormula_subst A 0 k (Nat.zero_le _)]
      exact ih k
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      intro k
      refine Derives₂.elim_ex _ (liftFormula (k + 1) A) _ (ih1 k) ?_
      rw [liftFormula_lift B 0 k (Nat.zero_le _), map_lift_lift]
      exact ih2 (k + 1)
  | bot_elim Γ' A _ ih => intro k; exact Derives₂.bot_elim _ _ (ih k)
  | weakening Γ' Γ'' f' _ hSub ih =>
      intro k
      refine Derives₂.weakening _ _ _ (ih k) ?_
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hSub y hy)
  | dne_rule Γ' A _ ih => intro k; exact Derives₂.dne_rule _ _ (ih k)
  | dne_schema Γ' A => intro k; exact Derives₂.dne_schema _ _
  | forall_not_ex_not Γ' A => intro k; exact Derives₂.forall_not_ex_not _ _
  | refl Γ' t => intro k; exact Derives₂.refl _ _
  | eq_func_congr Γ' p pre post a b _ ih =>
      intro k
      show (Γ'.map (liftFormula k)) ⊢₂
        Formula.eq (Term.func p (liftTerms k (pre ++ a :: post)))
                   (Term.func p (liftTerms k (pre ++ b :: post)))
      rw [liftTerms_append, liftTerms_append]
      exact Derives₂.eq_func_congr _ p (liftTerms k pre) (liftTerms k post)
        (liftTerm k a) (liftTerm k b) (ih k)
  | eq_atom_congr Γ' p pre post a b _ _ ih1 ih2 =>
      intro k
      have hpre : liftTerms k (pre ++ a :: post)
          = liftTerms k pre ++ liftTerm k a :: liftTerms k post := liftTerms_append k pre (a :: post)
      have hpost : liftTerms k (pre ++ b :: post)
          = liftTerms k pre ++ liftTerm k b :: liftTerms k post := liftTerms_append k pre (b :: post)
      have h2 : (Γ'.map (liftFormula k)) ⊢₂
          Formula.atom p (liftTerms k pre ++ liftTerm k a :: liftTerms k post) := by
        have hx := ih2 k
        show _ ⊢₂ Formula.atom p _
        rw [← hpre]
        exact hx
      show (Γ'.map (liftFormula k)) ⊢₂ Formula.atom p (liftTerms k (pre ++ b :: post))
      rw [hpost]
      exact Derives₂.eq_atom_congr _ p (liftTerms k pre) (liftTerms k post)
        (liftTerm k a) (liftTerm k b) (ih1 k) h2
  | eq_eq_congr Γ' a b c _ _ ih1 ih2 =>
      intro k
      exact Derives₂.eq_eq_congr _ (liftTerm k a) (liftTerm k b) (liftTerm k c) (ih1 k) (ih2 k)


-- ── §3 · Leibniz a nivel de TERMINO ─────────────────────────────────────────
inductive PwEq (G : List Formula) : List Term → List Term → Prop where
  | nil : PwEq G [] []
  | cons : ∀ {a b l1 l2}, Derives₂ G (Formula.eq a b) → PwEq G l1 l2 ->
      PwEq G (a :: l1) (b :: l2)

theorem eq_func_pw {G : List Formula} (p : String) : ∀ {l1 l2 : List Term},
    PwEq G l1 l2 → ∀ pre : List Term,
    G ⊢₂ Formula.eq (Term.func p (pre ++ l1)) (Term.func p (pre ++ l2)) := by
  intro l1 l2 hpw
  induction hpw with
  | nil => intro pre; simp only [List.append_nil]; exact Derives₂.refl _ _
  | @cons a b r1 r2 hab _ ih =>
      intro pre
      have step1 := Derives₂.eq_func_congr G p pre r1 a b hab
      have step2 := ih (pre ++ [b])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at step2
      exact eq_trans step1 step2

theorem eq_atom_pw {G : List Formula} (p : String) : ∀ {l1 l2 : List Term},
    PwEq G l1 l2 → ∀ pre : List Term,
    (G ⊢₂ Formula.atom p (pre ++ l1)) → G ⊢₂ Formula.atom p (pre ++ l2) := by
  intro l1 l2 hpw
  induction hpw with
  | nil => intro pre hx; exact hx
  | @cons a b r1 r2 hab _ ih =>
      intro pre hx
      have step1 := Derives₂.eq_atom_congr G p pre r1 a b hab hx
      have step2 := ih (pre ++ [b])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at step2
      exact step2 step1

mutual
theorem eq_substTerm {G : List Formula} {t1 t2 : Term} (h : G ⊢₂ Formula.eq t1 t2) (v : Nat) :
    ∀ u : Term, G ⊢₂ Formula.eq (substTerm v t1 u) (substTerm v t2 u)
  | .var n => by
      show G ⊢₂ Formula.eq (substTerm v t1 (Term.var n)) (substTerm v t2 (Term.var n))
      simp only [substTerm]
      by_cases hnv : n = v
      · simp only [if_pos hnv]; exact h
      · simp only [if_neg hnv]
        by_cases hgt : n > v
        · simp only [if_pos hgt]; exact Derives₂.refl _ _
        · simp only [if_neg hgt]; exact Derives₂.refl _ _
  | .func s us => by
      show G ⊢₂ Formula.eq (Term.func s (substTerms v t1 us)) (Term.func s (substTerms v t2 us))
      have hx := eq_func_pw (G := G) s (eq_substTerms h v us) []
      simpa using hx

theorem eq_substTerms {G : List Formula} {t1 t2 : Term} (h : G ⊢₂ Formula.eq t1 t2) (v : Nat) :
    ∀ us : List Term, PwEq G (substTerms v t1 us) (substTerms v t2 us)
  | [] => PwEq.nil
  | u :: us => PwEq.cons (eq_substTerm h v u) (eq_substTerms h v us)
end

-- ── §4 · Leibniz a nivel de FORMULA: `subst` es ADMISIBLE ───────────────────
theorem eq_substFormula : ∀ (f : Formula) (v : Nat) (t1 t2 : Term) (G : List Formula),
    (G ⊢₂ Formula.eq t1 t2) → (G ⊢₂ substFormula v t1 f) → G ⊢₂ substFormula v t2 f := by
  intro f
  induction f with
  | bottom => intro _ _ _ _ _ hd; exact hd
  | atom p ts =>
      intro v t1 t2 G h hd
      show G ⊢₂ Formula.atom p (substTerms v t2 ts)
      have hx := eq_atom_pw (G := G) p (eq_substTerms h v ts) [] hd
      simpa using hx
  | eq a b =>
      intro v t1 t2 G h hd
      have ha := eq_substTerm h v a
      have hb := eq_substTerm h v b
      show G ⊢₂ Formula.eq (substTerm v t2 a) (substTerm v t2 b)
      exact eq_trans (Derives₂.eq_eq_congr G _ _ _ ha hd) hb
  | impl A B ihA ihB =>
      intro v t1 t2 G h hd
      refine Derives₂.intro_impl _ _ _ ?_
      have hw : (substFormula v t2 A :: G) ⊢₂ Formula.eq t1 t2 :=
        Derives₂.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)
      have hws : (substFormula v t2 A :: G) ⊢₂ Formula.eq t2 t1 := eq_symm hw
      have hA1 : (substFormula v t2 A :: G) ⊢₂ substFormula v t1 A :=
        ihA v t2 t1 _ hws (Derives₂.hyp _ _ (List.Mem.head _))
      have hdw : (substFormula v t2 A :: G) ⊢₂ Formula.impl (substFormula v t1 A) (substFormula v t1 B) :=
        Derives₂.weakening _ _ _ hd (fun x hx => List.Mem.tail _ hx)
      exact ihB v t1 t2 _ hw (Derives₂.elim_impl _ _ _ hdw hA1)
  | and A B ihA ihB =>
      intro v t1 t2 G h hd
      exact Derives₂.intro_and _ _ _
        (ihA v t1 t2 G h (Derives₂.elim_and_l _ _ _ hd))
        (ihB v t1 t2 G h (Derives₂.elim_and_r _ _ _ hd))
  | or A B ihA ihB =>
      intro v t1 t2 G h hd
      refine Derives₂.elim_or G (substFormula v t1 A) (substFormula v t1 B) _ hd ?_ ?_
      · refine Derives₂.intro_or_l _ _ _ (ihA v t1 t2 _ ?_ (Derives₂.hyp _ _ (List.Mem.head _)))
        exact Derives₂.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)
      · refine Derives₂.intro_or_r _ _ _ (ihB v t1 t2 _ ?_ (Derives₂.hyp _ _ (List.Mem.head _)))
        exact Derives₂.weakening _ _ _ h (fun x hx => List.Mem.tail _ hx)
  | «forall» A ihA =>
      intro v t1 t2 G h hd
      show G ⊢₂ Formula.forall (substFormula (v + 1) (liftTerm 0 t2) A)
      refine Derives₂.intro_forall _ _ ?_
      have hlift := derives2_lift hd 0
      have hall : (G.map (liftFormula 0)) ⊢₂
          Formula.forall (liftFormula 1 (substFormula (v + 1) (liftTerm 0 t1) A)) := hlift
      have hinst := Derives₂.elim_forall _ (liftFormula 1 (substFormula (v + 1) (liftTerm 0 t1) A))
        (Term.var 0) hall
      rw [substFormula_lift_var] at hinst
      exact ihA (v + 1) (liftTerm 0 t1) (liftTerm 0 t2) _ (derives2_lift h 0) hinst
  | ex A ihA =>
      intro v t1 t2 G h hd
      show G ⊢₂ Formula.ex (substFormula (v + 1) (liftTerm 0 t2) A)
      refine Derives₂.elim_ex G (substFormula (v + 1) (liftTerm 0 t1) A) _ hd ?_
      show (substFormula (v + 1) (liftTerm 0 t1) A :: G.map (liftFormula 0)) ⊢₂
        Formula.ex (liftFormula 1 (substFormula (v + 1) (liftTerm 0 t2) A))
      refine Derives₂.intro_ex _ _ (Term.var 0) ?_
      rw [substFormula_lift_var]
      refine ihA (v + 1) (liftTerm 0 t1) (liftTerm 0 t2) _ ?_ (Derives₂.hyp _ _ (List.Mem.head _))
      exact Derives₂.weakening _ _ _ (derives2_lift h 0) (fun x hx => List.Mem.tail _ hx)


-- ============================================================
-- §5 · Las cuatro piezas de la igualdad, sobre `Derives₁`
-- ============================================================

-- ⚠️ Traslado literal de `FOL.Eq0` (que las prueba sobre `Derives₀`) — y las cuatro pasan por
-- `Derives₁.subst`, que es exactamente el punto medido en ADR‑044 §4: al quitarlo, hay que
-- subirlas a constructores.

theorem derives1_eq_symm {Γ : List Formula} {t1 t2 : Term} (h : Derives₁ Γ (.eq t1 t2)) :
    Derives₁ Γ (.eq t2 t1) := by
  let f := Formula.eq (.var 0) (liftTerm 0 t1)
  have hSubst1 : substFormula 0 t1 f = Formula.eq t1 t1 := by
    change Formula.eq (substTerm 0 t1 (.var 0)) (substTerm 0 t1 (liftTerm 0 t1)) = Formula.eq t1 t1
    rw [substTerm_liftTerm t1 0 t1]; rfl
  have hSubst2 : substFormula 0 t2 f = Formula.eq t2 t1 := by
    change Formula.eq (substTerm 0 t2 (.var 0)) (substTerm 0 t2 (liftTerm 0 t1)) = Formula.eq t2 t1
    rw [substTerm_liftTerm t1 0 t2]; rfl
  have hSubstDer := Derives₁.subst Γ t1 t2 f h
  rw [hSubst1] at hSubstDer
  have hDer2 := hSubstDer (Derives₁.refl Γ t1)
  rw [hSubst2] at hDer2
  exact hDer2

theorem derives1_eq_trans {Γ : List Formula} {t1 t2 t3 : Term}
    (h12 : Derives₁ Γ (.eq t1 t2)) (h23 : Derives₁ Γ (.eq t2 t3)) : Derives₁ Γ (.eq t1 t3) := by
  let f := Formula.eq (liftTerm 0 t1) (.var 0)
  have hSubst2 : substFormula 0 t2 f = Formula.eq t1 t2 := by
    change Formula.eq (substTerm 0 t2 (liftTerm 0 t1)) (substTerm 0 t2 (.var 0)) = Formula.eq t1 t2
    rw [substTerm_liftTerm t1 0 t2]; rfl
  have hSubst3 : substFormula 0 t3 f = Formula.eq t1 t3 := by
    change Formula.eq (substTerm 0 t3 (liftTerm 0 t1)) (substTerm 0 t3 (.var 0)) = Formula.eq t1 t3
    rw [substTerm_liftTerm t1 0 t3]; rfl
  have hSubstDer := Derives₁.subst Γ t2 t3 f h23
  rw [hSubst2] at hSubstDer
  have hDer3 := hSubstDer h12
  rw [hSubst3] at hDer3
  exact hDer3

theorem derives1_eq_func_congr {Γ : List Formula} (p : String) (pre post : List Term)
    {a b : Term} (h : Derives₁ Γ (.eq a b)) :
    Derives₁ Γ (.eq (Term.func p (pre ++ a :: post)) (Term.func p (pre ++ b :: post))) := by
  have key : ∀ x : Term,
      substFormula 0 x
        (Formula.eq (liftTerm 0 (Term.func p (pre ++ a :: post)))
                    (Term.func p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)))
        = Formula.eq (Term.func p (pre ++ a :: post)) (Term.func p (pre ++ x :: post)) := by
    intro x
    show Formula.eq (substTerm 0 x (liftTerm 0 (Term.func p (pre ++ a :: post))))
                    (Term.func p
                      (substTerms 0 x (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)))
         = _
    rw [substTerm_liftTerm, substTerms_lift_hole]
  have hstep := Derives₁.subst Γ a b
      (Formula.eq (liftTerm 0 (Term.func p (pre ++ a :: post)))
                  (Term.func p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post))) h
  rw [key a, key b] at hstep
  exact hstep (Derives₁.refl Γ _)

theorem derives1_atom_congr {Γ : List Formula} (p : String) (pre post : List Term)
    {a b : Term} (h : Derives₁ Γ (.eq a b)) (hA : Derives₁ Γ (.atom p (pre ++ a :: post))) :
    Derives₁ Γ (.atom p (pre ++ b :: post)) := by
  have key : ∀ x : Term,
      substFormula 0 x (Formula.atom p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post))
        = Formula.atom p (pre ++ x :: post) := by
    intro x
    show Formula.atom p
          (substTerms 0 x (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)) = _
    rw [substTerms_lift_hole]
  have hstep := Derives₁.subst Γ a b
      (Formula.atom p (liftTerms 0 pre ++ Term.var 0 :: liftTerms 0 post)) h
  rw [key a, key b] at hstep
  exact hstep hA

-- ============================================================
-- §6 · ⭐⭐ Los dos cálculos derivan LO MISMO
-- ============================================================

/-- `Derives₂` no es más fuerte: sus tres congruencias **son derivables** con `subst`. -/
theorem derives2_to_derives1 {Γ : List Formula} {f : Formula} (h : Γ ⊢₂ f) : Derives₁ Γ f := by
  induction h with
  | hyp Γ f hmem => exact Derives₁.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives₁.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₁.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₁.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₁.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₁.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₁.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₁.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₁.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₁.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₁.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₁.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₁.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₁.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₁.weakening Γ Γ' f ih hsub
  | dne_rule Γ A _ ih => exact Derives₁.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₁.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₁.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₁.refl Γ t
  | eq_func_congr Γ p pre post a b _ ih => exact derives1_eq_func_congr p pre post ih
  | eq_atom_congr Γ p pre post a b _ _ ih1 ih2 => exact derives1_atom_congr p pre post ih1 ih2
  | eq_eq_congr Γ a b c _ _ ih1 ih2 => exact derives1_eq_trans (derives1_eq_symm ih1) ih2

/-- ⭐⭐⭐ **La dirección que importa**: `subst` no hace falta. El único caso con contenido es el
suyo, y lo cierra `eq_substFormula`. -/
theorem derives1_to_derives2 {Γ : List Formula} {f : Formula} (h : Derives₁ Γ f) : Γ ⊢₂ f := by
  induction h with
  | hyp Γ f hmem => exact Derives₂.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives₂.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₂.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₂.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₂.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₂.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₂.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₂.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₂.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₂.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₂.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₂.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₂.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₂.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₂.weakening Γ Γ' f ih hsub
  | dne_rule Γ A _ ih => exact Derives₂.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₂.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₂.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₂.refl Γ t
  -- ⭐ EL ÚNICO CASO CON CONTENIDO
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact eq_substFormula f 0 t₁ t₂ Γ ih1 ih2

/-- ⭐⭐⭐ **`subst` es prescindible.** -/
theorem derives1_iff_derives2 {Γ : List Formula} {f : Formula} : (Derives₁ Γ f) ↔ (Γ ⊢₂ f) :=
  ⟨derives1_to_derives2, derives2_to_derives1⟩

/-- Y con `derives0_iff_derives1` (ADR‑044), el puente hasta el cálculo original: todo lo probado
sobre `Derives₀` —solidez, completitud, Henkin, Herbrand— vale tal cual sobre `Derives₂`. -/
theorem derives0_iff_derives2 {Γ : List Formula} {f : Formula} : (Γ ⊢₀ f) ↔ (Γ ⊢₂ f) :=
  Iff.trans FOL.Derives1.derives0_iff_derives1 derives1_iff_derives2

end FOL.Derives2

#print axioms Derives₂.rec
#print axioms FOL.Derives2.derives2_lift
#print axioms FOL.Derives2.eq_substTerm
#print axioms FOL.Derives2.eq_substFormula
#print axioms FOL.Derives2.derives1_to_derives2
#print axioms FOL.Derives2.derives0_iff_derives2
