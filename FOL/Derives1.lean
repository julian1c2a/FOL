/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Lift0
-- @axiom_system: classical
-- @importance: high

import FOL.Lift0

/-!
# `FOL.Derives1` — **`rewrite_at` es ADMISIBLE**: el primer obstáculo de H3, retirado

Primera pieza de **H3** (`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.4). ADR‑043 §3 dejó el obstáculo
localizado y **contado**: de los 21 constructores de `Derives₀`, siete son «de corte», y **dos**
impiden que la eliminación de cortes sea un Hauptsatz de libro —`subst`, que es Leibniz, y
⛔ **`rewrite_at`, que no tiene análogo en LK**.

**Este módulo retira el segundo.**

    Derives₁               -- los 20 constructores de `Derives₀` MENOS `rewrite_at`
    derives0_iff_derives1  -- y derivan EXACTAMENTE lo mismo

⇒ `Derives₁` es **deducción natural clásica de libro más igualdad**: hipótesis, los conectivos,
los cuantificadores, `bot_elim`, debilitamiento, doble negación y `refl`/`subst`. Nada más.
La única rareza que quedaba se ha ido, y el frente de H3 pasa de **dos** obstáculos a **uno**.

## Cómo se retira

`rewrite_at` reescribe una subfórmula **en una posición exacta** con una `LocalRule`. Y
`LocalRule` tiene **un solo constructor**: `commuteImpl A B C : A → (B → C)  ⟹  B → (A → C)`.

La eliminación es entonces una **congruencia por posiciones**:

    rewrite_equiv : getAt? f p = some sub → LocalRule sub sub' →
        ∀ Γ, (Γ ⊢₁ f → replaceAt f p sub') ∧ (Γ ⊢₁ replaceAt f p sub' → f)

⭐ **Y tiene que ser BICONDICIONAL**, aunque `rewrite_at` sólo pida una dirección: al bajar por el
**antecedente** de una implicación la congruencia se invierte (`impl_congr_l` es
**contravariante**), así que la inducción necesita las dos mitades a la vez.

## ⭐ Los dos casos que de verdad costaban: bajo el cuantificador

`Pos.body` mete la reescritura **dentro de un binder**. Ahí hay que probar
`⊢₁ (∀X) → (∀Y)` a partir de `⊢₁ X → Y`, y el camino pasa por `intro_forall` (que **levanta el
contexto**) y luego `elim_forall` con `Term.var 0`, cerrando con

    substFormula_lift_var : substFormula k (Term.var k) (liftFormula (k+1) f) = f

⭐ Es el mismo lema que sostenía el paso de eigenvariable de Henkin (`FOL.Lift0`, ADR‑036):
*deshacer un lift sustituyendo la variable cero*. Sale gratis porque ya estaba.

⚠️ Nótese que la hipótesis de las congruencias es **`∀ Δ, Δ ⊢₁ X → Y`**, cuantificada sobre
**todos** los contextos, no sobre uno. Es lo que permite instanciarla en el contexto **levantado**
que `intro_forall` fabrica, sin tener que levantar `X` ni `Y`.

## ⚠️ `getAt?` y `replaceAt` NO REDUCEN — medido

Las dos recursiones cambian **los dos** argumentos a la vez (`getAt? f1 p` desde `getAt? f p`), así
que Lean las compila por recursión **bien fundada** y `rfl` no las abre: `getAt? f .root = some f`
**no** es `rfl`. Hay que ir por sus **ecuaciones** (`simp only [getAt?]`). Es primo de la regla
⛔ *los símbolos OBJETO no reducen*, pero por otra causa: aquí el símbolo es de Lean y lo que falla
es el **esquema de recursión**.

## 📏 Footprint

`[propext, Quot.sound]`. **Ni un `Classical.choice`**: la admisibilidad de `rewrite_at` es
enteramente constructiva.

## ⬜ Lo que sigue faltando para H3

`subst` — la regla de Leibniz. La vía estándar es reducirla a **instancias de congruencia**
(`FOL.Herbrand0.EqInstance` ya las tiene, y ya están probadas derivables), dejando el cálculo en
ND puro + axiomas de igualdad, que es la forma en que la literatura enuncia Herbrand con `=`.
Y después, el Hauptsatz.
-/

/-- **`Derives₀` sin `rewrite_at`**: 20 constructores, y es deducción natural clásica de libro
más igualdad. -/
inductive Derives₁ : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives₁ Γ f
  | intro_impl : ∀ Γ A B, Derives₁ (A :: Γ) B → Derives₁ Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives₁ Γ (.impl A B) → Derives₁ Γ A → Derives₁ Γ B
  | intro_and  : ∀ Γ A B, Derives₁ Γ A → Derives₁ Γ B → Derives₁ Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives₁ Γ (.and A B) → Derives₁ Γ A
  | elim_and_r : ∀ Γ A B, Derives₁ Γ (.and A B) → Derives₁ Γ B
  | intro_or_l : ∀ Γ A B, Derives₁ Γ A → Derives₁ Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives₁ Γ B → Derives₁ Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives₁ Γ (.or A B) → Derives₁ (A :: Γ) C → Derives₁ (B :: Γ) C →
      Derives₁ Γ C
  | intro_forall : ∀ Γ A, Derives₁ (Γ.map (liftFormula 0)) A → Derives₁ Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives₁ Γ (.forall A) → Derives₁ Γ (substFormula 0 t A)
  | intro_ex : ∀ Γ A t, Derives₁ Γ (substFormula 0 t A) → Derives₁ Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives₁ Γ (.ex A) →
      Derives₁ (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives₁ Γ B
  | bot_elim : ∀ Γ A, Derives₁ Γ ⊥ → Derives₁ Γ A
  | weakening : ∀ Γ Γ' f, Derives₁ Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives₁ Γ' f
  | dne_rule : ∀ Γ A, Derives₁ Γ (neg (neg A)) → Derives₁ Γ A
  | dne_schema : ∀ Γ A, Derives₁ Γ (.impl (neg (neg A)) A)
  | forall_not_ex_not : ∀ Γ A, Derives₁ Γ (.impl (neg (.forall A)) (.ex (neg A)))
  | refl  : ∀ Γ t, Derives₁ Γ (.eq t t)
  | subst : ∀ Γ t₁ t₂ f, Derives₁ Γ (.eq t₁ t₂) → Derives₁ Γ (substFormula 0 t₁ f) →
      Derives₁ Γ (substFormula 0 t₂ f)

infix:50 " ⊢₁ " => Derives₁

namespace FOL.Derives1

open FOL.Lift0

-- ============================================================
-- §1 · La única `LocalRule`, derivada
-- ============================================================

/-- ⭐ `commuteImpl` en su forma de implicación. Sirve para **las dos** direcciones: la inversa es
esta misma con `A` y `B` intercambiadas. -/
theorem commute_impl_fwd (Γ : List Formula) (A B C : Formula) :
    Γ ⊢₁ Formula.impl (Formula.impl A (Formula.impl B C)) (Formula.impl B (Formula.impl A C)) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_impl _ _ _ (Derives₁.intro_impl _ _ _ ?_))
  refine Derives₁.elim_impl _ B C ?_ (Derives₁.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  exact Derives₁.elim_impl _ A (Formula.impl B C)
    (Derives₁.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    (Derives₁.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §2 · Congruencia, una por conectiva
-- ============================================================

-- ⚠️ La hipótesis va cuantificada sobre TODOS los contextos (`∀ Δ`): es lo que permite
-- instanciarla en el contexto LEVANTADO que `intro_forall` fabrica.

/-- ⚠️ **Contravariante**: en el antecedente la congruencia se da la vuelta. Es la razón de que
`rewrite_equiv` tenga que ser biconditional. -/
theorem impl_congr_l {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl Y X)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.impl X Z) (Formula.impl Y Z) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_impl _ _ _ ?_)
  refine Derives₁.elim_impl _ X Z (Derives₁.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
  exact Derives₁.elim_impl _ Y X (h _) (Derives₁.hyp _ _ (List.Mem.head _))

theorem impl_congr_r {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.impl Z X) (Formula.impl Z Y) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_impl _ _ _ ?_)
  refine Derives₁.elim_impl _ X Y (h _) ?_
  exact Derives₁.elim_impl _ Z X (Derives₁.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    (Derives₁.hyp _ _ (List.Mem.head _))

theorem and_congr_l {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.and X Z) (Formula.and Y Z) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_and _ _ _ ?_ ?_)
  · exact Derives₁.elim_impl _ X Y (h _)
      (Derives₁.elim_and_l _ X Z (Derives₁.hyp _ _ (List.Mem.head _)))
  · exact Derives₁.elim_and_r _ X Z (Derives₁.hyp _ _ (List.Mem.head _))

theorem and_congr_r {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.and Z X) (Formula.and Z Y) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_and _ _ _ ?_ ?_)
  · exact Derives₁.elim_and_l _ Z X (Derives₁.hyp _ _ (List.Mem.head _))
  · exact Derives₁.elim_impl _ X Y (h _)
      (Derives₁.elim_and_r _ Z X (Derives₁.hyp _ _ (List.Mem.head _)))

theorem or_congr_l {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.or X Z) (Formula.or Y Z) := by
  refine Derives₁.intro_impl _ _ _ ?_
  refine Derives₁.elim_or _ X Z _ (Derives₁.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derives₁.intro_or_l _ Y Z
      (Derives₁.elim_impl _ X Y (h _) (Derives₁.hyp _ _ (List.Mem.head _)))
  · exact Derives₁.intro_or_r _ Y Z (Derives₁.hyp _ _ (List.Mem.head _))

theorem or_congr_r {X Y : Formula} (Z : Formula) (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.or Z X) (Formula.or Z Y) := by
  refine Derives₁.intro_impl _ _ _ ?_
  refine Derives₁.elim_or _ Z X _ (Derives₁.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derives₁.intro_or_l _ Z Y (Derives₁.hyp _ _ (List.Mem.head _))
  · exact Derives₁.intro_or_r _ Z Y
      (Derives₁.elim_impl _ X Y (h _) (Derives₁.hyp _ _ (List.Mem.head _)))

/-- ⭐ **Bajo el cuantificador.** `intro_forall` levanta el contexto; `elim_forall` con
`Term.var 0` lo deshace, y el puente es `substFormula_lift_var` — el mismo lema del paso de
eigenvariable de Henkin (ADR‑036). -/
theorem forall_congr {X Y : Formula} (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.forall X) (Formula.forall Y) := by
  refine Derives₁.intro_impl _ _ _ (Derives₁.intro_forall _ _ ?_)
  have hx : (((Formula.forall X) :: Γ).map (liftFormula 0)) ⊢₁ X := by
    have hall : (((Formula.forall X) :: Γ).map (liftFormula 0)) ⊢₁
        Formula.forall (liftFormula 1 X) := Derives₁.hyp _ _ (List.Mem.head _)
    have hinst := Derives₁.elim_forall _ (liftFormula 1 X) (Term.var 0) hall
    rwa [substFormula_lift_var X 0] at hinst
  exact Derives₁.elim_impl _ X Y (h _) hx

theorem ex_congr {X Y : Formula} (h : ∀ Δ, Δ ⊢₁ Formula.impl X Y)
    (Γ : List Formula) : Γ ⊢₁ Formula.impl (Formula.ex X) (Formula.ex Y) := by
  refine Derives₁.intro_impl _ _ _ ?_
  refine Derives₁.elim_ex _ X (Formula.ex Y) (Derives₁.hyp _ _ (List.Mem.head _)) ?_
  show (X :: (((Formula.ex X) :: Γ).map (liftFormula 0))) ⊢₁ Formula.ex (liftFormula 1 Y)
  refine Derives₁.intro_ex _ (liftFormula 1 Y) (Term.var 0) ?_
  rw [substFormula_lift_var Y 0]
  exact Derives₁.elim_impl _ X Y (h _) (Derives₁.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §3 · ⭐⭐ La congruencia por POSICIONES
-- ============================================================

-- ⚠️ `getAt?` y `replaceAt` se compilan por recursión BIEN FUNDADA (sus llamadas recursivas
-- cambian los DOS argumentos), así que **no reducen**: hay que ir por sus ecuaciones.

/-- ⭐⭐ Reescribir en una posición produce una fórmula **equivalente** — y hacen falta las dos
direcciones porque `impl_congr_l` es contravariante. -/
theorem rewrite_equiv : ∀ (p : Pos) (f sub sub' : Formula),
    getAt? f p = some sub → LocalRule sub sub' →
    ∀ Γ : List Formula,
      And (Γ ⊢₁ Formula.impl f (replaceAt f p sub'))
          (Γ ⊢₁ Formula.impl (replaceAt f p sub') f)
  | .root, f, sub, sub', h, hr, Γ => by
      simp only [getAt?] at h
      simp only [replaceAt]
      have hfs : f = sub := Option.some.inj h
      subst hfs
      cases hr with
      | commuteImpl A B C => exact ⟨commute_impl_fwd Γ A B C, commute_impl_fwd Γ B A C⟩
  | .left q, f, sub, sub', h, hr, Γ => by
      cases f with
      | impl f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f1 sub sub' h hr
          exact ⟨impl_congr_l f2 (fun Δ => (ih Δ).2) Γ, impl_congr_l f2 (fun Δ => (ih Δ).1) Γ⟩
      | and f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f1 sub sub' h hr
          exact ⟨and_congr_l f2 (fun Δ => (ih Δ).1) Γ, and_congr_l f2 (fun Δ => (ih Δ).2) Γ⟩
      | or f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f1 sub sub' h hr
          exact ⟨or_congr_l f2 (fun Δ => (ih Δ).1) Γ, or_congr_l f2 (fun Δ => (ih Δ).2) Γ⟩
      | bottom => simp [getAt?] at h
      | atom _ _ => simp [getAt?] at h
      | eq _ _ => simp [getAt?] at h
      | «forall» _ => simp [getAt?] at h
      | ex _ => simp [getAt?] at h
  | .right q, f, sub, sub', h, hr, Γ => by
      cases f with
      | impl f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f2 sub sub' h hr
          exact ⟨impl_congr_r f1 (fun Δ => (ih Δ).1) Γ, impl_congr_r f1 (fun Δ => (ih Δ).2) Γ⟩
      | and f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f2 sub sub' h hr
          exact ⟨and_congr_r f1 (fun Δ => (ih Δ).1) Γ, and_congr_r f1 (fun Δ => (ih Δ).2) Γ⟩
      | or f1 f2 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f2 sub sub' h hr
          exact ⟨or_congr_r f1 (fun Δ => (ih Δ).1) Γ, or_congr_r f1 (fun Δ => (ih Δ).2) Γ⟩
      | bottom => simp [getAt?] at h
      | atom _ _ => simp [getAt?] at h
      | eq _ _ => simp [getAt?] at h
      | «forall» _ => simp [getAt?] at h
      | ex _ => simp [getAt?] at h
  | .body q, f, sub, sub', h, hr, Γ => by
      cases f with
      | «forall» f1 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f1 sub sub' h hr
          exact ⟨forall_congr (fun Δ => (ih Δ).1) Γ, forall_congr (fun Δ => (ih Δ).2) Γ⟩
      | ex f1 =>
          simp only [getAt?] at h; simp only [replaceAt]
          have ih := rewrite_equiv q f1 sub sub' h hr
          exact ⟨ex_congr (fun Δ => (ih Δ).1) Γ, ex_congr (fun Δ => (ih Δ).2) Γ⟩
      | bottom => simp [getAt?] at h
      | atom _ _ => simp [getAt?] at h
      | eq _ _ => simp [getAt?] at h
      | impl _ _ => simp [getAt?] at h
      | and _ _ => simp [getAt?] at h
      | or _ _ => simp [getAt?] at h

/-- ⭐⭐⭐ **`rewrite_at` es ADMISIBLE en `Derives₁`**: no hace falta como regla. -/
theorem rewrite_at_admissible {Γ : List Formula} {f f' sub sub' : Formula} {p : Pos}
    (hd : Γ ⊢₁ f) (hg : getAt? f p = some sub) (hr : LocalRule sub sub')
    (he : f' = replaceAt f p sub') : Γ ⊢₁ f' := by
  subst he
  exact Derives₁.elim_impl _ f _ ((rewrite_equiv p f sub sub' hg hr Γ).1) hd

-- ============================================================
-- §4 · ⭐⭐ Y por tanto los dos cálculos DERIVAN LO MISMO
-- ============================================================

theorem derives1_to_derives0 {Γ : List Formula} {f : Formula} (h : Γ ⊢₁ f) : Γ ⊢₀ f := by
  induction h with
  | hyp Γ f hmem => exact Derives₀.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives₀.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₀.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₀.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₀.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₀.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₀.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₀.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₀.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₀.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₀.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₀.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₀.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₀.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₀.weakening Γ Γ' f ih hsub
  | dne_rule Γ A _ ih => exact Derives₀.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₀.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₀.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₀.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives₀.subst Γ t₁ t₂ f ih1 ih2

/-- ⭐⭐⭐ **La dirección que importa**: todo lo que `Derives₀` deriva con `rewrite_at`, `Derives₁`
lo deriva **sin** ella. El único caso con contenido es el suyo, y lo cierra
`rewrite_at_admissible`. -/
theorem derives0_to_derives1 {Γ : List Formula} {f : Formula} (h : Γ ⊢₀ f) : Γ ⊢₁ f := by
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
  -- ⭐ EL ÚNICO CASO CON CONTENIDO
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact rewrite_at_admissible ih hget hrule heq
  | dne_rule Γ A _ ih => exact Derives₁.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₁.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₁.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₁.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives₁.subst Γ t₁ t₂ f ih1 ih2

/-- ⭐⭐⭐ **Los dos cálculos derivan exactamente lo mismo.** ⇒ todo lo probado sobre `Derives₀`
—solidez, completitud, Henkin, Herbrand— vale tal cual sobre `Derives₁`, que ya **no tiene la
regla sin análogo en LK**. -/
theorem derives0_iff_derives1 {Γ : List Formula} {f : Formula} : (Γ ⊢₀ f) ↔ (Γ ⊢₁ f) :=
  ⟨derives0_to_derives1, derives1_to_derives0⟩

end FOL.Derives1

#print axioms Derives₁.rec
#print axioms FOL.Derives1.rewrite_equiv
#print axioms FOL.Derives1.rewrite_at_admissible
#print axioms FOL.Derives1.derives0_to_derives1
#print axioms FOL.Derives1.derives0_iff_derives1
