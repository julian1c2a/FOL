/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Hauptsatz0
-- @axiom_system: classical
-- @importance: high

import FOL.Hauptsatz0

/-!
# `FOL.QFDecide0` — 🏁 el fragmento SIN CUANTIFICADORES de `Derives₀`, ACOTADO y DECIDIDO

    eqPropCert_prune        : EqPropCert Γ φ E → EqPropCert Γ φ (qfInst Γ φ)     -- LA PODA
    derives0_qf_iff_bounded : Γ, φ sin ∀/∃ → ((Γ ⊢₀ φ) ↔ EqPropCert Γ φ (qfInst Γ φ))
    decideDerives0QF        : Γ, φ sin ∀/∃ → Decidable (Γ ⊢₀ φ)

La OFERTA de `FOL.Hauptsatz0` §9, cotizada en RPP‑106 y aceptada por el propietario el 2026‑09‑27
(RPP‑107).
`derives0_qf_iff` caracterizaba el fragmento («derivable sii consecuencia proposicional de `Γ` más
una lista `E` de instancias de la igualdad») pero no lo decidía: `E` no tenía cota. Aquí la tiene.

## ⛔ La cota INGENUA es FALSA

Acotar `E` a las instancias sobre los SUBTÉRMINOS del secuente no basta, porque `EqInstance.func`
cambia UN argumento cada vez: `[a≐b, c≐d] ⟹ g(a,c) ≐ g(b,d)` es derivable y la cadena pasa por
`g(b,c)` o `g(a,d)`: ninguno es subtérmino. Está compilado abajo (§8): una valuación satisface TODAS las
instancias ingenuas y `Γ`, y refuta `φ`. ⇒ `T` = los subtérminos `S` MÁS las **mezclas de
prefijo** `f(y₁…yᵢ, xᵢ₊₁…xₙ)` de cada par `f(xs)`, `g(ys)` de `S` —un solo paso, no un cierre; `mixT`
no exige `g = f`— (`|T| ≤ |S| + (k+1)|S|²`, con `k` la aridad máxima en `S`: se lee de `qfT`/`mixL`,
no se demuestra); y `E` se
SUSTITUYE por todas las instancias sobre `T` (filtrar una `E` dada tampoco basta).

## ⭐⭐ La poda, por EXTENSIÓN de la valuación

Si `v` satisface `Γ` y las instancias sobre `T`, se construye `ext v`, que satisface TODA
`EqInstance` (con términos arbitrarios) **por construcción** —su igualdad es el núcleo de una
interpretación composicional de los términos— y que coincide con `v` en los átomos del secuente
(`evI_S`, el lema difícil, donde pagan las mezclas). Entonces `ext v ⊨ φ` por el certificado, y
`v ⊨ φ` por `peval_congr`. ⭐ No hace falta ni el Hauptsatz ni `QuantFree` para la poda; sólo para
componerla con `derives0_qf_iff`.

## ⚠️ El decisor es de JUGUETE

`qfCheck` recorre una tabla de verdad sobre los átomos DISTINTOS (`ptautCheck` repite átomos y es
inservible aquí): `2^(átomos)` filas — medido, `[a≐b] ⟹ b≐a` tiene 4 átomos; `g(a,c) ≐ g(b,d)`, 112.
Es completo y calculable en el kernel; no es usable más allá de ejemplos pequeños. Un decisor
práctico (cierre de congruencia con certificado) sería otra cosa.

## 📏 Footprint

`[propext, Quot.sound]` en los titulares (`ext_eqInstance` y `qfCheck_iff`, sólo `[propext]`): **ni un
`Classical.choice`**. Viene de dos borradores
independientes que compilaron en aislado (RPP‑106); éste es el de la ruta «semántica».
-/

namespace FOL.QFDecide0

open FOL.DecEq
open FOL.Propositional0
open FOL.Herbrand0
open FOL.Hauptsatz0

-- ============================================================
-- §1 · Utillaje de listas (propio: `eraseDups`/`∈`-decidable piden `LawfulBEq` —`pick` copia
--      `List.find?`, que no lo pide, con sus lemas a mano—,
--      y el `BEq` derivado de `Term` no lo es)
-- ============================================================

def pick {α : Type} (r : α → Bool) : List α → Option α
  | [] => none
  | s :: l => if r s = true then some s else pick r l

theorem pick_some {α : Type} {r : α → Bool} : ∀ {l : List α} {a : α},
    pick r l = some a → And (a ∈ l) (r a = true)
  | [], _, h => by simp [pick] at h
  | s :: l, a, h => by
      unfold pick at h
      by_cases hs : r s = true
      · rw [if_pos hs] at h
        cases h
        exact ⟨List.Mem.head _, hs⟩
      · rw [if_neg hs] at h
        obtain ⟨h1, h2⟩ := pick_some h
        exact ⟨List.Mem.tail _ h1, h2⟩

theorem pick_exists {α : Type} {r : α → Bool} : ∀ {l : List α} {s : α},
    s ∈ l → r s = true → ∃ a, pick r l = some a
  | [], _, hs, _ => absurd hs List.not_mem_nil
  | x :: l, s, hs, hr => by
      unfold pick
      by_cases hx : r x = true
      · exact ⟨x, if_pos hx⟩
      · rw [if_neg hx]
        cases hs with
        | head => exact absurd hr hx
        | tail _ h => exact pick_exists h hr

theorem pick_congr {α : Type} {r r' : α → Bool} : ∀ {l : List α},
    (∀ x, x ∈ l → r x = r' x) → pick r l = pick r' l
  | [], _ => rfl
  | x :: l, h => by
      unfold pick
      rw [h x (List.Mem.head _), pick_congr (fun y hy => h y (List.Mem.tail _ hy))]

def memB {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || memB x ys

theorem mem_of_memB {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α},
    memB x l = true → x ∈ l
  | [], h => by simp [memB] at h
  | y :: ys, h => by
      have h' : (decide (x = y) || memB x ys) = true := h
      rcases (Bool.or_eq_true _ _).mp h' with h1 | h1
      · rw [of_decide_eq_true h1]; exact List.Mem.head _
      · exact List.Mem.tail _ (mem_of_memB h1)

def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if memB x xs = true then dedup xs else x :: dedup xs

theorem mem_dedup {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ l → x ∈ dedup l
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
      unfold dedup
      by_cases hy : memB y ys = true
      · rw [if_pos hy]
        cases h with
        | head => exact mem_dedup (mem_of_memB hy)
        | tail _ h' => exact mem_dedup h'
      · rw [if_neg hy]
        cases h with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail _ (mem_dedup h')

theorem dedup_sub {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedup l → x ∈ l
  | [], h => h
  | y :: ys, h => by
      unfold dedup at h
      by_cases hy : memB y ys = true
      · rw [if_pos hy] at h; exact List.Mem.tail _ (dedup_sub h)
      · rw [if_neg hy] at h
        cases h with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail _ (dedup_sub h')

/-- Relación punto a punto entre dos listas de términos. -/
inductive Pw (r : Term → Term → Prop) : List Term → List Term → Prop
  | nil : Pw r [] []
  | cons {x y : Term} {xs ys : List Term} : r x y → Pw r xs ys → Pw r (x :: xs) (y :: ys)

theorem peval_mp {v : PVal} {X Y : Formula} (h : peval v (Formula.impl X Y) = true)
    (hx : peval v X = true) : peval v Y = true := by
  have h' : ((!(peval v X)) || peval v Y) = true := h
  rw [hx] at h'
  simpa using h'

-- ============================================================
-- §2 · Los subtérminos, cerrados
-- ============================================================

mutual
def subT : Term → List Term
  | .var n => [.var n]
  | .func f ts => .func f ts :: subTs ts
def subTs : List Term → List Term
  | [] => []
  | t :: ts => subT t ++ subTs ts
end

theorem mem_subT_self : ∀ t : Term, t ∈ subT t
  | .var _ => List.Mem.head _
  | .func _ _ => List.Mem.head _

theorem mem_subTs_of_mem : ∀ {ts : List Term} {t : Term}, t ∈ ts → t ∈ subTs ts
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, t, h => by
      show t ∈ subT x ++ subTs xs
      cases h with
      | head => exact List.mem_append.mpr (Or.inl (mem_subT_self _))
      | tail _ h' => exact List.mem_append.mpr (Or.inr (mem_subTs_of_mem h'))

mutual
theorem subT_closed : ∀ (u : Term) {f : String} {ss : List Term},
    Term.func f ss ∈ subT u → ∀ y, y ∈ ss → y ∈ subT u
  | .var _, _, _, h, _, _ => by
      cases h with
      | tail _ h' => exact absurd h' List.not_mem_nil
  | .func _ us, _, _, h, y, hy => by
      cases h with
      | head => exact List.Mem.tail _ (mem_subTs_of_mem hy)
      | tail _ h' => exact List.Mem.tail _ (subTs_closed us h' y hy)
theorem subTs_closed : ∀ (us : List Term) {f : String} {ss : List Term},
    Term.func f ss ∈ subTs us → ∀ y, y ∈ ss → y ∈ subTs us
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | u :: us, _, _, h, y, hy => by
      cases List.mem_append.mp h with
      | inl h1 => exact List.mem_append.mpr (Or.inl (subT_closed u h1 y hy))
      | inr h2 => exact List.mem_append.mpr (Or.inr (subTs_closed us h2 y hy))
end

/-- Los términos de primer nivel de los átomos del esqueleto de una fórmula. -/
def topT : Formula → List Term
  | .atom _ ts => ts
  | .eq t u => [t, u]
  | .impl a b => topT a ++ topT b
  | .and a b => topT a ++ topT b
  | .or a b => topT a ++ topT b
  | _ => []

/-- Los términos de UN átomo. -/
def atomT : Formula → List Term
  | .atom _ ts => ts
  | .eq t u => [t, u]
  | _ => []

theorem atomT_sub : ∀ (g : Formula) {a : Formula}, a ∈ patoms g →
    ∀ t, t ∈ atomT a → t ∈ topT g := by
  intro g
  induction g with
  | bottom => intro a ha; exact absurd ha List.not_mem_nil
  | atom p ts =>
      intro a ha t ht
      cases ha with
      | head => exact ht
      | tail _ h => exact absurd h List.not_mem_nil
  | eq t u =>
      intro a ha x hx
      cases ha with
      | head => exact hx
      | tail _ h => exact absurd h List.not_mem_nil
  | impl A B ihA ihB =>
      intro a ha t ht
      exact (List.mem_append.mp ha).elim
        (fun h => List.mem_append.mpr (Or.inl (ihA h t ht)))
        (fun h => List.mem_append.mpr (Or.inr (ihB h t ht)))
  | and A B ihA ihB =>
      intro a ha t ht
      exact (List.mem_append.mp ha).elim
        (fun h => List.mem_append.mpr (Or.inl (ihA h t ht)))
        (fun h => List.mem_append.mpr (Or.inr (ihB h t ht)))
  | or A B ihA ihB =>
      intro a ha t ht
      exact (List.mem_append.mp ha).elim
        (fun h => List.mem_append.mpr (Or.inl (ihA h t ht)))
        (fun h => List.mem_append.mpr (Or.inr (ihB h t ht)))
  | «forall» A _ =>
      intro a ha t ht
      cases ha with
      | head => exact absurd ht List.not_mem_nil
      | tail _ h => exact absurd h List.not_mem_nil
  | ex A _ =>
      intro a ha t ht
      cases ha with
      | head => exact absurd ht List.not_mem_nil
      | tail _ h => exact absurd h List.not_mem_nil

/-- `S`: los subtérminos de `Γ ⟹ φ`. -/
def ctxT (Γ : List Formula) (φ : Formula) : List Term := Γ.flatMap topT ++ topT φ
def qfS (Γ : List Formula) (φ : Formula) : List Term := dedup (subTs (ctxT Γ φ))
/-- Los átomos del esqueleto de `Γ ⟹ φ`. -/
def ctxA (Γ : List Formula) (φ : Formula) : List Formula := Γ.flatMap patoms ++ patoms φ

theorem mem_ctxA_left {Γ : List Formula} {φ g a : Formula} (hg : g ∈ Γ) (ha : a ∈ patoms g) :
    a ∈ ctxA Γ φ := List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨g, hg, ha⟩))

theorem mem_ctxA_right {Γ : List Formula} {φ a : Formula} (ha : a ∈ patoms φ) :
    a ∈ ctxA Γ φ := List.mem_append.mpr (Or.inr ha)

theorem atomT_ctx {Γ : List Formula} {φ a : Formula} (ha : a ∈ ctxA Γ φ) :
    ∀ t, t ∈ atomT a → t ∈ ctxT Γ φ := by
  intro t ht
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨g, hg, hag⟩ := List.mem_flatMap.mp h
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨g, hg, atomT_sub g hag t ht⟩))
  · exact List.mem_append.mpr (Or.inr (atomT_sub φ h t ht))

-- ============================================================
-- §3 · ⭐ Las MEZCLAS: sin ellas la cota es FALSA
-- ============================================================

-- ⛔ `EqInstance.func` cambia UN argumento. Para `f(a,c) ≐ f(b,d)` desde `a ≐ b`, `c ≐ d` hace falta
-- pasar por `f(b,c)` o por `f(a,d)`, y ninguno es subtérmino. Contraejemplo a la cota ingenua
-- (instancias con todos sus términos en los subtérminos):
-- `Γ = [a≐b, c≐d]`, `φ = f(a,c) ≐ f(b,d)`. ⇒ `T` = subtérminos
-- MÁS las mezclas de prefijo `f(y₁…yᵢ, xᵢ₊₁…xₙ)` de cada par `f(xs)`, `g(ys)` de `S` (`mixT` no
-- exige `g = f`; un solo paso, no un cierre).

/-- Las mezclas de prefijo de `xs` hacia `ys`: `xs`, `y₁::xs₂…`, …, hasta agotar una de las dos;
acaba en `ys` si tienen la misma longitud (`end_mem_mixL`). -/
def mixL : List Term → List Term → List (List Term)
  | [], _ => [[]]
  | x :: xs, [] => [x :: xs]
  | x :: xs, y :: ys => (x :: xs) :: (mixL xs ys).map (List.cons y)

theorem self_mem_mixL : ∀ (xs ys : List Term), xs ∈ mixL xs ys
  | [], _ => List.Mem.head _
  | _ :: _, [] => List.Mem.head _
  | _ :: _, _ :: _ => List.Mem.head _

theorem end_mem_mixL {r : Term → Term → Prop} {xs ys : List Term} (h : Pw r xs ys) :
    ys ∈ mixL xs ys := by
  induction h with
  | nil => exact List.Mem.head _
  | @cons x y xs ys _ _ ih => exact List.Mem.tail _ (List.mem_map.mpr ⟨ys, ih, rfl⟩)

def mixT : Term → Term → List Term
  | .func f xs, .func _ ys => (mixL xs ys).map (Term.func f)
  | _, _ => []

def mixA : Formula → Formula → List Formula
  | .atom p xs, .atom _ ys => (mixL xs ys).map (Formula.atom p)
  | _, _ => []

/-- `T`: los términos sobre los que se instancian los axiomas. -/
def qfT (S : List Term) : List Term := dedup (S ++ S.flatMap (fun x => S.flatMap (mixT x)))

/-- Los átomos sobre los que se instancia la congruencia de relación. -/
def qfA (A : List Formula) : List Formula := A ++ A.flatMap (fun x => A.flatMap (mixA x))

theorem mem_qfT_of_S {S : List Term} {t : Term} (h : t ∈ S) : t ∈ qfT S :=
  mem_dedup (List.mem_append.mpr (Or.inl h))

theorem mem_qfT_mix {S : List Term} {f g : String} {xs ys zs : List Term}
    (hx : Term.func f xs ∈ S) (hy : Term.func g ys ∈ S) (hz : zs ∈ mixL xs ys) :
    Term.func f zs ∈ qfT S :=
  mem_dedup (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨_, hx,
    List.mem_flatMap.mpr ⟨_, hy, List.mem_map.mpr ⟨zs, hz, rfl⟩⟩⟩)))

theorem mem_qfA_mix {A : List Formula} {p q : String} {xs ys zs : List Term}
    (hx : Formula.atom p xs ∈ A) (hy : Formula.atom q ys ∈ A) (hz : zs ∈ mixL xs ys) :
    Formula.atom p zs ∈ qfA A :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨_, hx,
    List.mem_flatMap.mpr ⟨_, hy, List.mem_map.mpr ⟨zs, hz, rfl⟩⟩⟩))

-- ============================================================
-- §4 · `Inst(S)`: la lista FINITA de instancias
-- ============================================================

def splits : List Term → List (List Term × Term × List Term)
  | [] => []
  | x :: xs => ([], x, xs) :: (splits xs).map (fun q => (x :: q.1, q.2.1, q.2.2))

theorem mem_splits : ∀ (pre : List Term) (a : Term) (post : List Term),
    (pre, a, post) ∈ splits (pre ++ a :: post)
  | [], _, _ => List.Mem.head _
  | _ :: pre, a, post =>
      List.Mem.tail _ (List.mem_map.mpr ⟨(pre, a, post), mem_splits pre a post, rfl⟩)

def funcInsts (T : List Term) : Term → List Formula
  | .func f zs => (splits zs).flatMap (fun q => T.map (eqFuncAx f q.1 q.2.2 q.2.1))
  | .var _ => []

def atomInsts (T : List Term) : Formula → List Formula
  | .atom p zs => (splits zs).flatMap (fun q => T.map (eqAtomAx p q.1 q.2.2 q.2.1))
  | _ => []

def instsOf (T : List Term) (A : List Formula) : List Formula :=
  T.map eqReflAx
  ++ T.flatMap (fun t => T.map (eqSymmAx t))
  ++ T.flatMap (fun t => T.flatMap (fun u => T.map (eqTransAx t u)))
  ++ T.flatMap (funcInsts T)
  ++ A.flatMap (atomInsts T)

/-- ⭐ **`Inst(S)`**, finita y calculable: las instancias sobre `T = qfT S` (no sobre `S`: ésa es
la cota ingenua, FALSA, §8); por eso §7 la llama también `Inst(T)`. -/
def qfInst (Γ : List Formula) (φ : Formula) : List Formula :=
  instsOf (qfT (qfS Γ φ)) (qfA (ctxA Γ φ))

section Mem
variable {T : List Term} {A : List Formula}

private theorem inL {x : Formula} {l1 l2 : List Formula} (h : x ∈ l1) : x ∈ l1 ++ l2 :=
  List.mem_append.mpr (Or.inl h)
private theorem inR {x : Formula} {l1 l2 : List Formula} (h : x ∈ l2) : x ∈ l1 ++ l2 :=
  List.mem_append.mpr (Or.inr h)

theorem refl_mem {t : Term} (ht : t ∈ T) : eqReflAx t ∈ instsOf T A :=
  inL (inL (inL (inL (List.mem_map.mpr ⟨t, ht, rfl⟩))))

theorem symm_mem {t u : Term} (ht : t ∈ T) (hu : u ∈ T) : eqSymmAx t u ∈ instsOf T A :=
  inL (inL (inL (inR (List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨u, hu, rfl⟩⟩))))

theorem trans_mem {t u w : Term} (ht : t ∈ T) (hu : u ∈ T) (hw : w ∈ T) :
    eqTransAx t u w ∈ instsOf T A :=
  inL (inL (inR (List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨u, hu,
    List.mem_map.mpr ⟨w, hw, rfl⟩⟩⟩)))

theorem func_mem {f : String} {pre post : List Term} {a b : Term}
    (hx : Term.func f (pre ++ a :: post) ∈ T) (hb : b ∈ T) : eqFuncAx f pre post a b ∈ instsOf T A :=
  inL (inR (List.mem_flatMap.mpr ⟨_, hx, List.mem_flatMap.mpr ⟨(pre, a, post),
    mem_splits pre a post, List.mem_map.mpr ⟨b, hb, rfl⟩⟩⟩))

theorem atom_mem {p : String} {pre post : List Term} {a b : Term}
    (hx : Formula.atom p (pre ++ a :: post) ∈ A) (hb : b ∈ T) :
    eqAtomAx p pre post a b ∈ instsOf T A :=
  inR (List.mem_flatMap.mpr ⟨_, hx, List.mem_flatMap.mpr ⟨(pre, a, post),
    mem_splits pre a post, List.mem_map.mpr ⟨b, hb, rfl⟩⟩⟩)

/-- Todo lo que hay en `Inst(S)` es una instancia de la igualdad. -/
theorem instsOf_eqInstance : ∀ g, g ∈ instsOf T A → EqInstance g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  rcases List.mem_append.mp h with h | h
  rcases List.mem_append.mp h with h | h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact EqInstance.refl t
  · obtain ⟨t, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
    exact EqInstance.symm t u
  · obtain ⟨t, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨u, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp h
    exact EqInstance.trans t u w
  · obtain ⟨x, _, h⟩ := List.mem_flatMap.mp h
    cases x with
    | var _ => exact absurd h List.not_mem_nil
    | func f zs =>
        obtain ⟨q, _, h⟩ := List.mem_flatMap.mp h
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
        exact EqInstance.func f q.1 q.2.2 q.2.1 b
  · obtain ⟨x, _, h⟩ := List.mem_flatMap.mp h
    cases x with
    | atom p zs =>
        obtain ⟨q, _, h⟩ := List.mem_flatMap.mp h
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
        exact EqInstance.atom p q.1 q.2.2 q.2.1 b
    | _ => exact absurd h List.not_mem_nil
end Mem

-- ============================================================
-- §5 · ⭐⭐ La valuación EXTENDIDA `ext v` — satisface TODA `EqInstance`, sin hipótesis
-- ============================================================

section Ext
variable (v : PVal) (S : List Term) (A : List Formula)

/-- El representante canónico de la clase de `t`: el primer `s ∈ S` con `v (s ≐ t)`. -/
def cls (t : Term) : Term :=
  match pick (fun s => v (Formula.eq s t)) S with
  | some s => s
  | none => t

def headF (f : String) (us : List Term) : Term → Bool
  | .func g ss => decide (g = f) && decide (ss.map (cls v S) = us)
  | .var _ => false

/-- Un nodo `f(us)`: si algún `f(ss) ∈ S` tiene las clases `us`, su clase; si no, él mismo. -/
def node (f : String) (us : List Term) : Term :=
  match pick (headF v S f us) S with
  | some s => cls v S s
  | none => Term.func f us

mutual
/-- ⭐ La interpretación en el modelo de términos: `evI (f ts)` sólo depende de `f` y `evIs ts`. -/
def evI : Term → Term
  | .var n => cls v S (.var n)
  | .func f ts => node v S f (evIs ts)
def evIs : List Term → List Term
  | [] => []
  | t :: ts => evI t :: evIs ts
end

def headA (p : String) (us : List Term) : Formula → Bool
  | .atom q ss => decide (q = p) && decide (ss.map (cls v S) = us)
  | _ => false

def atomVal (p : String) (us : List Term) : Bool :=
  match pick (headA v S p us) A with
  | some a => v a
  | none => false

/-- ⭐⭐ **La valuación extendida.** Igualdad = núcleo de `evI`; un átomo sólo mira las clases
de sus argumentos; el resto (cuantificadores incluidos), como `v`. -/
def ext (g : Formula) : Bool :=
  match g with
  | .eq a b => decide (evI v S a = evI v S b)
  | .atom p ts => atomVal v S A p (evIs v S ts)
  | _ => v g

end Ext

theorem evIs_append (v : PVal) (S : List Term) : ∀ (l1 l2 : List Term),
    evIs v S (l1 ++ l2) = evIs v S l1 ++ evIs v S l2
  | [], _ => rfl
  | t :: l, l2 => by
      show evI v S t :: evIs v S (l ++ l2) = (evI v S t :: evIs v S l) ++ evIs v S l2
      rw [evIs_append v S l l2]
      rfl

theorem evIs_hole (v : PVal) (S : List Term) (pre post : List Term) {a b : Term}
    (h : evI v S a = evI v S b) :
    evIs v S (pre ++ a :: post) = evIs v S (pre ++ b :: post) := by
  rw [evIs_append, evIs_append]
  show evIs v S pre ++ (evI v S a :: evIs v S post) = evIs v S pre ++ (evI v S b :: evIs v S post)
  rw [h]

/-- ⭐⭐ **`ext v` satisface las CINCO formas de `EqInstance`, con términos ARBITRARIOS** — y no
pide nada a `v`: es la forma de `evI`/`ext` la que lo da. -/
theorem ext_eqInstance (v : PVal) (S : List Term) (A : List Formula) {g : Formula}
    (hg : EqInstance g) : peval (ext v S A) g = true := by
  cases hg with
  | refl t => exact decide_eq_true rfl
  | symm t u =>
      show ((!(decide (evI v S t = evI v S u))) || decide (evI v S u = evI v S t)) = true
      by_cases h : evI v S t = evI v S u
      · rw [decide_eq_true h.symm]; simp
      · rw [decide_eq_false h]; rfl
  | trans t u w =>
      show ((!(decide (evI v S t = evI v S u))) ||
        ((!(decide (evI v S u = evI v S w))) || decide (evI v S t = evI v S w))) = true
      by_cases h1 : evI v S t = evI v S u
      · by_cases h2 : evI v S u = evI v S w
        · rw [decide_eq_true (h1.trans h2)]; simp
        · rw [decide_eq_false h2]; simp
      · rw [decide_eq_false h1]; rfl
  | func f pre post a b =>
      show ((!(decide (evI v S a = evI v S b))) ||
        decide (node v S f (evIs v S (pre ++ a :: post)) =
          node v S f (evIs v S (pre ++ b :: post)))) = true
      by_cases h : evI v S a = evI v S b
      · rw [evIs_hole v S pre post h]; simp
      · rw [decide_eq_false h]; rfl
  | atom p pre post a b =>
      show ((!(decide (evI v S a = evI v S b))) ||
        ((!(atomVal v S A p (evIs v S (pre ++ a :: post)))) ||
          atomVal v S A p (evIs v S (pre ++ b :: post)))) = true
      by_cases h : evI v S a = evI v S b
      · rw [evIs_hole v S pre post h]
        cases atomVal v S A p (evIs v S (pre ++ b :: post)) <;> simp
      · rw [decide_eq_false h]; rfl

-- ============================================================
-- §6 · ⭐⭐⭐ La CONSERVATIVIDAD: sobre `S`, `ext v` coincide con `v`
-- ============================================================

/-- Lo que se le pide a `v`: satisfacer `Inst(S)`. Y a `S`, `A`: estar cerrados. -/
structure Good (v : PVal) (S : List Term) (A : List Formula) : Prop where
  closed : ∀ {f : String} {ss : List Term}, Term.func f ss ∈ S → ∀ y, y ∈ ss → y ∈ S
  atoms : ∀ {a : Formula}, a ∈ A → ∀ t, t ∈ atomT a → t ∈ S
  inst : ∀ g, g ∈ instsOf (qfT S) (qfA A) → peval v g = true

section Good
variable {v : PVal} {S : List Term} {A : List Formula}

theorem Good.rfl' (hG : Good v S A) {t : Term} (ht : t ∈ qfT S) :
    v (Formula.eq t t) = true := hG.inst _ (refl_mem ht)

theorem Good.symm (hG : Good v S A) {t u : Term} (ht : t ∈ qfT S) (hu : u ∈ qfT S)
    (h : v (Formula.eq t u) = true) : v (Formula.eq u t) = true :=
  peval_mp (hG.inst _ (symm_mem ht hu)) h

theorem Good.trans (hG : Good v S A) {t u w : Term} (ht : t ∈ qfT S) (hu : u ∈ qfT S)
    (hw : w ∈ qfT S) (h1 : v (Formula.eq t u) = true) (h2 : v (Formula.eq u w) = true) :
    v (Formula.eq t w) = true :=
  peval_mp (peval_mp (hG.inst _ (trans_mem ht hu hw)) h1) h2

theorem Good.func (hG : Good v S A) {f : String} {pre post : List Term} {a b : Term}
    (hx : Term.func f (pre ++ a :: post) ∈ qfT S) (hb : b ∈ qfT S)
    (h : v (Formula.eq a b) = true) :
    v (Formula.eq (Term.func f (pre ++ a :: post)) (Term.func f (pre ++ b :: post))) = true :=
  peval_mp (hG.inst _ (func_mem hx hb)) h

theorem Good.atom (hG : Good v S A) {p : String} {pre post : List Term} {a b : Term}
    (hx : Formula.atom p (pre ++ a :: post) ∈ qfA A) (hb : b ∈ qfT S)
    (h : v (Formula.eq a b) = true) (ha : v (Formula.atom p (pre ++ a :: post)) = true) :
    v (Formula.atom p (pre ++ b :: post)) = true :=
  peval_mp (peval_mp (hG.inst _ (atom_mem hx hb)) h) ha

/-- ⭐ La CADENA de funciones: de `xs ~ ys` punto a punto a `f(pre++xs) ≐ f(pre++ys)`, pasando
por las mezclas (un argumento cada vez: `func` + `trans`). -/
theorem chainF (hG : Good v S A) {f : String} :
    ∀ {xs ys : List Term}, Pw (fun x y => v (Formula.eq x y) = true) xs ys →
    (∀ y, y ∈ ys → y ∈ qfT S) →
    ∀ pre : List Term, (∀ zs, zs ∈ mixL xs ys → Term.func f (pre ++ zs) ∈ qfT S) →
    v (Formula.eq (Term.func f (pre ++ xs)) (Term.func f (pre ++ ys))) = true := by
  intro xs ys hp
  induction hp with
  | nil => intro _ pre hT; exact hG.rfl' (hT [] (List.Mem.head _))
  | @cons x y xs ys hxy hrest ih =>
      intro hys pre hT
      have hA : Term.func f (pre ++ x :: xs) ∈ qfT S := hT _ (List.Mem.head _)
      have hB : Term.func f (pre ++ y :: xs) ∈ qfT S :=
        hT _ (List.Mem.tail _ (List.mem_map.mpr ⟨xs, self_mem_mixL xs ys, rfl⟩))
      have hC : Term.func f (pre ++ y :: ys) ∈ qfT S :=
        hT _ (List.Mem.tail _ (List.mem_map.mpr ⟨ys, end_mem_mixL hrest, rfl⟩))
      have h1 := hG.func hA (hys y (List.Mem.head _)) hxy
      have h2 := ih (fun z hz => hys z (List.Mem.tail _ hz)) (pre ++ [y])
        (fun zs hz => by
          rw [List.append_assoc]
          exact hT _ (List.Mem.tail _ (List.mem_map.mpr ⟨zs, hz, rfl⟩)))
      rw [List.append_assoc, List.append_assoc] at h2
      exact hG.trans hA hB hC h1 h2

/-- La CADENA de relaciones: lo mismo con `atom` (sin `trans`: basta encadenar implicaciones). -/
theorem chainA (hG : Good v S A) {p : String} :
    ∀ {xs ys : List Term}, Pw (fun x y => v (Formula.eq x y) = true) xs ys →
    (∀ y, y ∈ ys → y ∈ qfT S) →
    ∀ pre : List Term, (∀ zs, zs ∈ mixL xs ys → Formula.atom p (pre ++ zs) ∈ qfA A) →
    v (Formula.atom p (pre ++ xs)) = true → v (Formula.atom p (pre ++ ys)) = true := by
  intro xs ys hp
  induction hp with
  | nil => intro _ _ _ h; exact h
  | @cons x y xs ys hxy _ ih =>
      intro hys pre hT hx
      have hA : Formula.atom p (pre ++ x :: xs) ∈ qfA A := hT _ (List.Mem.head _)
      have h1 := hG.atom hA (hys y (List.Mem.head _)) hxy hx
      have h2 := ih (fun z hz => hys z (List.Mem.tail _ hz)) (pre ++ [y])
        (fun zs hz => by
          rw [List.append_assoc]
          exact hT _ (List.Mem.tail _ (List.mem_map.mpr ⟨zs, hz, rfl⟩)))
        (by rw [List.append_assoc]; exact h1)
      rw [List.append_assoc] at h2
      exact h2

theorem cls_spec (hG : Good v S A) {t : Term} (ht : t ∈ S) :
    And (cls v S t ∈ S) (v (Formula.eq (cls v S t) t) = true) := by
  obtain ⟨s, hs⟩ := pick_exists (r := fun s => v (Formula.eq s t)) ht (hG.rfl' (mem_qfT_of_S ht))
  obtain ⟨h1, h2⟩ := pick_some hs
  unfold cls
  rw [hs]
  exact ⟨h1, h2⟩

theorem cls_eq_of (hG : Good v S A) {s t : Term} (hs : s ∈ S) (ht : t ∈ S)
    (h : v (Formula.eq s t) = true) : cls v S s = cls v S t := by
  have hs' := mem_qfT_of_S hs
  have ht' := mem_qfT_of_S ht
  have hc : ∀ x, x ∈ S → v (Formula.eq x s) = v (Formula.eq x t) := by
    intro x hx
    have hx' := mem_qfT_of_S hx
    cases h1 : v (Formula.eq x s) with
    | true => exact (hG.trans hx' hs' ht' h1 h).symm
    | false =>
        cases h2 : v (Formula.eq x t) with
        | false => rfl
        | true =>
            have h3 := hG.trans hx' ht' hs' h2 (hG.symm hs' ht' h)
            rw [h1] at h3
            exact absurd h3 (by decide)
  obtain ⟨a, ha⟩ := pick_exists (r := fun x => v (Formula.eq x t)) ht (hG.rfl' ht')
  unfold cls
  rw [pick_congr hc, ha]

theorem eq_of_cls (hG : Good v S A) {s t : Term} (hs : s ∈ S) (ht : t ∈ S)
    (h : cls v S s = cls v S t) : v (Formula.eq s t) = true := by
  obtain ⟨hcs, h1⟩ := cls_spec hG hs
  obtain ⟨_, h2⟩ := cls_spec hG ht
  rw [h] at h1 hcs
  exact hG.trans (mem_qfT_of_S hs) (mem_qfT_of_S hcs) (mem_qfT_of_S ht)
    (hG.symm (mem_qfT_of_S hcs) (mem_qfT_of_S hs) h1) h2

theorem pw_of_cls (hG : Good v S A) : ∀ {xs ys : List Term},
    (∀ x, x ∈ xs → x ∈ S) → (∀ y, y ∈ ys → y ∈ S) →
    xs.map (cls v S) = ys.map (cls v S) → Pw (fun x y => v (Formula.eq x y) = true) xs ys
  | [], [], _, _, _ => Pw.nil
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
      have h' : cls v S x :: xs.map (cls v S) = cls v S y :: ys.map (cls v S) := h
      injection h' with h1 h2
      exact Pw.cons (eq_of_cls hG (hx x (List.Mem.head _)) (hy y (List.Mem.head _)) h1)
        (pw_of_cls hG (fun z hz => hx z (List.Mem.tail _ hz))
          (fun z hz => hy z (List.Mem.tail _ hz)) h2)

mutual
/-- ⭐⭐⭐ **El lema difícil**: sobre `S`, la interpretación ES la clase. El paso `func` es donde
pagan las mezclas: el `f(ss')` que encuentra la búsqueda tiene las mismas clases que `f(ss)`, y
`chainF` los iguala. -/
theorem evI_S (hG : Good v S A) : ∀ (t : Term), t ∈ S → evI v S t = cls v S t
  | .var _, _ => rfl
  | .func f ss, hs => by
      have hss : ∀ y, y ∈ ss → y ∈ S := hG.closed hs
      show node v S f (evIs v S ss) = cls v S (Term.func f ss)
      rw [evIs_S hG ss hss]
      have hself : headF v S f (ss.map (cls v S)) (Term.func f ss) = true := by
        show (decide (f = f) && decide (ss.map (cls v S) = ss.map (cls v S))) = true
        simp
      obtain ⟨s', hs'⟩ := pick_exists hs hself
      obtain ⟨hmem, hhead⟩ := pick_some hs'
      unfold node
      rw [hs']
      show cls v S s' = cls v S (Term.func f ss)
      cases s' with
      | var _ => simp [headF] at hhead
      | func g ss' =>
          have hh : (decide (g = f) && decide (ss'.map (cls v S) = ss.map (cls v S))) = true :=
            hhead
          obtain ⟨hg, hmap⟩ := (Bool.and_eq_true _ _).mp hh
          have hg' : g = f := of_decide_eq_true hg
          have hmap' := of_decide_eq_true hmap
          subst hg'
          have hss' : ∀ y, y ∈ ss' → y ∈ S := hG.closed hmem
          exact cls_eq_of hG hmem hs (chainF hG (pw_of_cls hG hss' hss hmap')
            (fun y hy => mem_qfT_of_S (hss y hy)) [] (fun zs hz => mem_qfT_mix hmem hs hz))
theorem evIs_S (hG : Good v S A) : ∀ (ts : List Term), (∀ t, t ∈ ts → t ∈ S) →
    evIs v S ts = ts.map (cls v S)
  | [], _ => rfl
  | t :: ts, h => by
      show evI v S t :: evIs v S ts = cls v S t :: ts.map (cls v S)
      rw [evI_S hG t (h t (List.Mem.head _)), evIs_S hG ts (fun x hx => h x (List.Mem.tail _ hx))]
end

/-- La congruencia de relación sobre `A`, por `chainA` en los dos sentidos. -/
theorem atom_congr (hG : Good v S A) {p : String} {xs ys : List Term}
    (hx : Formula.atom p xs ∈ A) (hy : Formula.atom p ys ∈ A)
    (h : xs.map (cls v S) = ys.map (cls v S)) :
    v (Formula.atom p xs) = v (Formula.atom p ys) := by
  have hxs : ∀ t, t ∈ xs → t ∈ S := hG.atoms hx
  have hys : ∀ t, t ∈ ys → t ∈ S := hG.atoms hy
  have d1 := chainA hG (p := p) (pw_of_cls hG hxs hys h)
    (fun y hy' => mem_qfT_of_S (hys y hy')) [] (fun zs hz => mem_qfA_mix hx hy hz)
  have d2 := chainA hG (p := p) (pw_of_cls hG hys hxs h.symm)
    (fun y hy' => mem_qfT_of_S (hxs y hy')) [] (fun zs hz => mem_qfA_mix hy hx hz)
  cases h1 : v (Formula.atom p xs) with
  | true => exact (d1 h1).symm
  | false =>
      cases h2 : v (Formula.atom p ys) with
      | false => rfl
      | true => exact Bool.noConfusion (h1.symm.trans (d2 h2))

/-- ⭐⭐⭐ **CONSERVATIVIDAD**: en los átomos de `Γ ⟹ φ`, `ext v` coincide con `v`. -/
theorem ext_agree (hG : Good v S A) {a : Formula} (ha : a ∈ A) : ext v S A a = v a := by
  cases a with
  | eq t u =>
      have ht : t ∈ S := hG.atoms ha t (List.Mem.head _)
      have hu : u ∈ S := hG.atoms ha u (List.Mem.tail _ (List.Mem.head _))
      show decide (evI v S t = evI v S u) = v (Formula.eq t u)
      rw [evI_S hG t ht, evI_S hG u hu]
      cases hv : v (Formula.eq t u) with
      | true => exact decide_eq_true (cls_eq_of hG ht hu hv)
      | false =>
          exact decide_eq_false (fun hc => Bool.noConfusion (hv.symm.trans (eq_of_cls hG ht hu hc)))
  | atom p ts =>
      have hts : ∀ x, x ∈ ts → x ∈ S := hG.atoms ha
      show atomVal v S A p (evIs v S ts) = v (Formula.atom p ts)
      rw [evIs_S hG ts hts]
      have hself : headA v S p (ts.map (cls v S)) (Formula.atom p ts) = true := by
        show (decide (p = p) && decide (ts.map (cls v S) = ts.map (cls v S))) = true
        simp
      obtain ⟨a0, h0⟩ := pick_exists ha hself
      obtain ⟨hmem, hh⟩ := pick_some h0
      unfold atomVal
      rw [h0]
      show v a0 = v (Formula.atom p ts)
      cases a0 with
      | atom q ss =>
          have hh' : (decide (q = p) && decide (ss.map (cls v S) = ts.map (cls v S))) = true := hh
          obtain ⟨hq, hmap⟩ := (Bool.and_eq_true _ _).mp hh'
          have hq' : q = p := of_decide_eq_true hq
          subst hq'
          exact atom_congr hG hmem ha (of_decide_eq_true hmap)
      | _ => simp [headA] at hh
  | bottom => rfl
  | impl _ _ => rfl
  | and _ _ => rfl
  | or _ _ => rfl
  | «forall» _ => rfl
  | ex _ => rfl

end Good

-- ============================================================
-- §7 · 🏁 La PODA, la versión ACOTADA y el DECISOR
-- ============================================================

theorem good_ctx {Γ : List Formula} {φ : Formula} {v : PVal}
    (hI : ∀ g, g ∈ qfInst Γ φ → peval v g = true) : Good v (qfS Γ φ) (ctxA Γ φ) where
  closed := fun hs y hy => mem_dedup (subTs_closed _ (dedup_sub hs) y hy)
  atoms := fun ha t ht => mem_dedup (mem_subTs_of_mem (atomT_ctx ha t ht))
  inst := hI

/-- 🏁 **LA PODA**: un certificado con `E` arbitraria da uno con `E := Inst(S)`. ⭐ Sin hipótesis
`QuantFree`: `peval` trata los cuantificadores como átomos, y `ext` los deja como `v`. -/
theorem eqPropCert_prune {Γ : List Formula} {φ : Formula} {E : List Formula}
    (h : EqPropCert Γ φ E) : EqPropCert Γ φ (qfInst Γ φ) := by
  refine ⟨instsOf_eqInstance, fun v hΓ hI => ?_⟩
  have hG := good_ctx hI
  have hΓ' : ∀ g, g ∈ Γ → peval (ext v (qfS Γ φ) (ctxA Γ φ)) g = true := fun g hg =>
    (peval_congr g (fun a ha => ext_agree hG (mem_ctxA_left hg ha))).trans (hΓ g hg)
  have hφ := h.2 _ hΓ' (fun g hg => ext_eqInstance v _ _ (h.1 g hg))
  exact (peval_congr φ (fun a ha => (ext_agree hG (mem_ctxA_right ha)).symm)).trans hφ

theorem peval_implChain_inv (v : PVal) : ∀ (Γ : List Formula) (φ : Formula),
    peval v (implChain Γ φ) = true → (∀ g, g ∈ Γ → peval v g = true) → peval v φ = true
  | [], _, h, _ => h
  | g :: Γ', φ, h, hΓ =>
      peval_implChain_inv v Γ' φ (peval_mp h (hΓ g (List.Mem.head _)))
        (fun x hx => hΓ x (List.Mem.tail _ hx))

theorem eqPropCert_iff_ptaut {Γ : List Formula} {φ : Formula} {E : List Formula}
    (hE : ∀ g, g ∈ E → EqInstance g) :
    EqPropCert Γ φ E ↔ PTaut (implChain E (implChain Γ φ)) :=
  ⟨fun h v => peval_implChain v E _ (fun hEv => peval_implChain v Γ φ (fun hΓv => h.2 v hΓv hEv)),
   fun h => ⟨hE, fun v hΓv hEv =>
     peval_implChain_inv v Γ φ (peval_implChain_inv v E _ (h v) hEv) hΓv⟩⟩

/-- El verificador con los átomos SIN REPETIR (`ptautCheck` recorre `patoms` con repeticiones: con
`Inst(S)` dentro, `2^36` filas ya para `[a≐b] ⟹ b≐a`, frente a `2^4`). -/
def qfCheck (X : Formula) : Bool := pcheck (dedup (patoms X)) (fun _ => false) X

theorem qfCheck_iff {X : Formula} : qfCheck X = true ↔ PTaut X :=
  ⟨fun h w => pcheck_sound _ _ X h w (fun _ ha hn => absurd (mem_dedup ha) hn),
   fun h => pcheck_complete _ _ X (fun w _ => h w)⟩

section Decisor

/-- 🏁🏁 **LA VERSIÓN ACOTADA**: derivable ⟺ certificado con `E := Inst(T)`, FIJA y FINITA. -/
theorem derives0_qf_iff_bounded {Γ : List Formula} {φ : Formula}
    (hΓ : ∀ g, g ∈ Γ → QuantFree g) (hφ : QuantFree φ) :
    (Γ ⊢₀ φ) ↔ EqPropCert Γ φ (qfInst Γ φ) :=
  ⟨fun h => ((derives0_qf_iff hΓ hφ).mp h).elim (fun _ hc => eqPropCert_prune hc),
   fun hc => (derives0_qf_iff hΓ hφ).mpr ⟨_, hc⟩⟩

/-- La forma «`∃ E ⊆ Inst(T)`». -/
theorem derives0_qf_iff_sub {Γ : List Formula} {φ : Formula}
    (hΓ : ∀ g, g ∈ Γ → QuantFree g) (hφ : QuantFree φ) :
    (Γ ⊢₀ φ) ↔ ∃ E, And (∀ g, g ∈ E → g ∈ qfInst Γ φ) (EqPropCert Γ φ E) :=
  ⟨fun h => ⟨_, fun _ hg => hg, (derives0_qf_iff_bounded hΓ hφ).mp h⟩,
   fun ⟨_, _, hc⟩ => (derives0_qf_iff hΓ hφ).mpr ⟨_, hc⟩⟩

/-- 🏁🏁🏁 **EL DECISOR** del fragmento sin cuantificadores de `⊢₀`. Un `def` con las hipótesis
`QuantFree`, no un `instance`: la lógica de primer orden NO es decidible. ⚠️ De juguete: recorre una
tabla de verdad de `2^(átomos distintos)` filas. -/
def decideDerives0QF (Γ : List Formula) (φ : Formula)
    (hΓ : ∀ g, g ∈ Γ → QuantFree g) (hφ : QuantFree φ) : Decidable (Γ ⊢₀ φ) :=
  if h : qfCheck (implChain (qfInst Γ φ) (implChain Γ φ)) = true then
    isTrue ((derives0_qf_iff_bounded hΓ hφ).mpr
      ((eqPropCert_iff_ptaut instsOf_eqInstance).mpr (qfCheck_iff.mp h)))
  else
    isFalse (fun hd => h (qfCheck_iff.mpr
      ((eqPropCert_iff_ptaut instsOf_eqInstance).mp ((derives0_qf_iff_bounded hΓ hφ).mp hd))))

end Decisor

-- ============================================================
-- §8 · ⚠️ CONTROLES
-- ============================================================

private def ca : Term := Term.func "a" []
private def cb : Term := Term.func "b" []

-- ⭐ El certificado ACOTADO se comprueba POR CÓMPUTO: `[a≐b] ⟹ b≐a` sí; `[] ⟹ a≐b` no.
example : qfCheck (implChain (qfInst [Formula.eq ca cb] (Formula.eq cb ca))
    (implChain [Formula.eq ca cb] (Formula.eq cb ca))) = true := by decide
example : qfCheck (implChain (qfInst [] (Formula.eq ca cb))
    (implChain [] (Formula.eq ca cb))) = false := by decide

-- ⭐ Y el DECISOR contesta «no» por `rfl`: `¬ ([] ⊢₀ a ≐ b)`, sin semántica de Tarski.
example : Not (([] : List Formula) ⊢₀ Formula.eq ca cb) :=
  @of_decide_eq_false _ (decideDerives0QF [] (Formula.eq ca cb)
    (fun _ h => absurd h List.not_mem_nil) trivial) rfl

-- ⛔ CONTROL: SIN las mezclas la cota es FALSA. `[a≐b, c≐d] ⟹ g(a,c) ≐ g(b,d)` es derivable, y
-- `v0` satisface TODAS las instancias cuyos términos de igualdad están en `S` y refuta `φ`.
private def cc : Term := Term.func "c" []
private def cd : Term := Term.func "d" []
private def Γx : List Formula := [Formula.eq ca cb, Formula.eq cc cd]
private def φx : Formula := Formula.eq (Term.func "g" [ca, cc]) (Term.func "g" [cb, cd])

private def eqTerms (g : Formula) : List Term :=
  (patoms g).flatMap (fun a => match a with | .eq x y => [x, y] | _ => [])
/-- La cota INGENUA: las instancias sobre `S` con todos sus términos de igualdad en `S`. -/
private def naiveInst (Γ : List Formula) (φ : Formula) : List Formula :=
  (instsOf (qfS Γ φ) (ctxA Γ φ)).filter (fun g => (eqTerms g).all (fun t => memB t (qfS Γ φ)))
private def r0 (t : Term) : Term := if t = cb then ca else if t = cd then cc else t
private def v0 : PVal := fun g => match g with
  | .eq x y => decide (r0 x = r0 y)
  | _ => false

set_option maxRecDepth 100000 in
example : (naiveInst Γx φx).all (fun g => peval v0 g) = true := by decide
example : Γx.all (fun g => peval v0 g) = true := by decide
example : peval v0 φx = false := by decide

end FOL.QFDecide0

#print axioms FOL.QFDecide0.instsOf_eqInstance
#print axioms FOL.QFDecide0.ext_eqInstance
#print axioms FOL.QFDecide0.evI_S
#print axioms FOL.QFDecide0.ext_agree
#print axioms FOL.QFDecide0.eqPropCert_prune
#print axioms FOL.QFDecide0.qfCheck_iff
#print axioms FOL.QFDecide0.derives0_qf_iff_bounded
#print axioms FOL.QFDecide0.derives0_qf_iff_sub
#print axioms FOL.QFDecide0.decideDerives0QF
