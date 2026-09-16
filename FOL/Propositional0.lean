/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives0, FOL.DecEq
-- @axiom_system: constructive
-- @importance: high

import FOL.Derives0
import FOL.DecEq

/-!
# `FOL.Propositional0` — **H1 y H2** de la vía H: completitud PROPOSICIONAL, y es FINITARIA

Hitos **H1** y **H2** de `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.2:

    derives0_of_ptaut     : PTaut φ → [] ⊢₀ φ
    derives0_of_ptaut_ctx : (∀ v, (∀ g ∈ Γ, peval v g) → peval v φ) → Γ ⊢₀ φ

⭐⭐ **Y son `[propext, Quot.sound]`: ni un `Classical.choice`.** Ésa es toda la diferencia con la
vía W: aquí no hay König, porque `Γ` es **finito** y la valuación recorre una lista **finita** de
átomos. *Esto es lo que Hilbert llamaría finitario, y lo es de verdad.*

## H1 · La semántica proposicional, y el ⭐ que la hace útil

`peval : (Formula → Bool) → Formula → Bool` evalúa los conectivos y **trata como ÁTOMO todo lo
demás**: `atom`, `eq`, **y también `∀` y `∃`**. Es el *esqueleto proposicional*.

⭐ El plan pedía «semántica proposicional para fórmulas **sin cuantificadores**». Tratar los
cuantificadores como átomos **no cuesta nada y sirve para mucho más**: `derives0_of_ptaut` vale
para **toda** fórmula, así que descarga cualquier tautología proposicional —con subfórmulas
cuantificadas dentro— en **una línea**. La restricción a fórmulas sin cuantificadores no habría
hecho el teorema más fuerte, sólo menos aplicable.

## H2 · La demostración, que es Kalmár

1. **`kalmar`** — bajo el contexto de los literales de una valuación `v`, toda fórmula se decide:
   si `peval v φ = true` se deriva `φ`, y si `= false` se deriva `¬φ`. Inducción estructural.
2. **`elim_atoms`** — se eliminan los átomos uno a uno con `derives0_cases`, que es `elim_or`
   sobre `A ∨ ¬A`.
3. ⭐ **`derives0_em_ctx : Δ ⊢₀ A ∨ ¬A` es NET‑0**: sale de `dne_rule` + `intro_or_*` en diez
   líneas. ⚠️ Compárese con `FOL.Canonical0.derives0_em`, **el mismo teorema** obtenido por
   completitud semántica: ése arrastra `Classical.choice`. *La vía H da los mismos teoremas con
   footprint estrictamente menor* — ver §6.

## ⚠️ Un detalle del paso de eliminación que conviene no perder

Al quitar el átomo `a` de la cabeza, las valuaciones `v[a↦true]` y `v[a↦false]` **no coinciden con
`v` en el resto de la lista** si `a` aparece repetido. ⭐ No hace falta pedir que la lista sea sin
repeticiones: basta **debilitar** (`Derives₀.weakening`), porque el literal discrepante es
justamente `a` (o `¬a`), que es la cabeza del contexto objetivo.

## ⛔ Lo que este módulo NO dice

**No hay recíproca.** `⊢₀ φ` **no** implica `PTaut φ`: `(∀x P(x)) → P(t)` es derivable y su
esqueleto proposicional es `p → q`, que no es tautología. La solidez proposicional es falsa, y
tiene que serlo: el cálculo sabe más que su esqueleto.

⬜ Y falta lo gordo de la vía H: **H3**, la eliminación de cortes / normalización, y **H4**, la
extracción de testigos. Ver §5.2 del plan.
-/

namespace FOL.Propositional0

open FOL.DecEq

-- ============================================================
-- §1 · El tercio excluso FINITARIO, y el análisis de casos
-- ============================================================

/-- ⭐ `A ∨ ¬A` **dentro de `Derives₀`, sin semántica y sin elección.** -/
theorem derives0_em_ctx (Δ : List Formula) (A : Formula) : Δ ⊢₀ Formula.or A (neg A) := by
  refine Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_)
  have hn : (neg (Formula.or A (neg A)) :: Δ) ⊢₀ neg A := by
    refine Derives₀.intro_impl _ _ _ ?_
    refine Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom ?_ ?_
    · exact Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    · exact Derives₀.intro_or_l _ A (neg A) (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom
    (Derives₀.hyp _ _ (List.Mem.head _))
    (Derives₀.intro_or_r _ A (neg A) hn)

/-- **Análisis de casos**: si `φ` se deriva suponiendo `A` y también suponiendo `¬A`, se deriva. -/
theorem derives0_cases {Δ : List Formula} {A φ : Formula}
    (h1 : (A :: Δ) ⊢₀ φ) (h2 : (neg A :: Δ) ⊢₀ φ) : Δ ⊢₀ φ :=
  Derives₀.elim_or Δ A (neg A) φ (derives0_em_ctx Δ A) h1 h2

-- ============================================================
-- §2 · H1 · La semántica proposicional
-- ============================================================

/-- Una valuación proposicional. Sólo se consulta en los **átomos** del esqueleto. -/
abbrev PVal := Formula → Bool

/-- El **esqueleto proposicional**: se evalúan los conectivos y **todo lo demás es un átomo**,
incluidos `∀` y `∃`. -/
def peval (v : PVal) : Formula → Bool
  | .bottom => false
  | .atom p ts => v (.atom p ts)
  | .eq t u => v (.eq t u)
  | .impl a b => (!(peval v a)) || peval v b
  | .and a b => peval v a && peval v b
  | .or a b => peval v a || peval v b
  | .forall a => v (.forall a)
  | .ex a => v (.ex a)

/-- Tautología proposicional. ⚠️ **No** es validez de primer orden. -/
def PTaut (φ : Formula) : Prop := ∀ v : PVal, peval v φ = true

theorem peval_neg (v : PVal) (A : Formula) : peval v (neg A) = !(peval v A) := by
  show ((!(peval v A)) || peval v Formula.bottom) = !(peval v A)
  simp only [peval, Bool.or_false]

/-- Los átomos del esqueleto: lo que la valuación tiene que decidir. -/
def patoms : Formula → List Formula
  | .bottom => []
  | .atom p ts => [.atom p ts]
  | .eq t u => [.eq t u]
  | .impl a b => patoms a ++ patoms b
  | .and a b => patoms a ++ patoms b
  | .or a b => patoms a ++ patoms b
  | .forall a => [.forall a]
  | .ex a => [.ex a]

/-- El literal que `v` asigna al átomo `a`. -/
def lit (v : PVal) (a : Formula) : Formula := if v a = true then a else neg a

-- ============================================================
-- §3 · H2 · Kalmár
-- ============================================================

/-- Los cuatro casos ATÓMICOS de Kalmár son el mismo: el literal está en el contexto. -/
private theorem kalmar_atom {v : PVal} {Δ : List Formula} {A : Formula} (hm : lit v A ∈ Δ) :
    And (v A = true → (Δ ⊢₀ A)) (v A = false → (Δ ⊢₀ neg A)) := by
  constructor
  · intro hv
    have he : lit v A = A := by simp [lit, hv]
    exact Derives₀.hyp _ _ (he ▸ hm)
  · intro hv
    have he : lit v A = neg A := by simp [lit, hv]
    exact Derives₀.hyp _ _ (he ▸ hm)

/-- Debilita un paso: lo derivado en `Δ` vale en `X :: Δ`. -/
private theorem wk1 {Δ : List Formula} {X φ : Formula} (h : Δ ⊢₀ φ) : (X :: Δ) ⊢₀ φ :=
  Derives₀.weakening _ _ _ h (fun _ hx => List.Mem.tail _ hx)

/-- ⭐⭐ **El lema de Kalmár**: bajo el contexto de los literales de `v`, el cálculo **decide**
toda fórmula, y lo hace del lado que `peval` dice. -/
theorem kalmar (v : PVal) (Δ : List Formula) : ∀ φ : Formula,
    (∀ a, a ∈ patoms φ → lit v a ∈ Δ) →
    And (peval v φ = true → (Δ ⊢₀ φ)) (peval v φ = false → (Δ ⊢₀ neg φ)) := by
  intro φ
  induction φ with
  | bottom =>
      intro _
      exact ⟨fun h => Bool.noConfusion h,
             fun _ => Derives₀.intro_impl _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))⟩
  | atom p ts => intro hL; exact kalmar_atom (hL _ (List.Mem.head _))
  | eq t u => intro hL; exact kalmar_atom (hL _ (List.Mem.head _))
  | «forall» a => intro hL; exact kalmar_atom (hL _ (List.Mem.head _))
  | ex a => intro hL; exact kalmar_atom (hL _ (List.Mem.head _))
  | impl A B ihA ihB =>
      intro hL
      have hA := ihA (fun a ha => hL a (List.mem_append.mpr (Or.inl ha)))
      have hB := ihB (fun a ha => hL a (List.mem_append.mpr (Or.inr ha)))
      constructor
      · intro h
        have h' : ((!(peval v A)) || peval v B) = true := h
        cases hb : peval v B with
        | true => exact Derives₀.intro_impl _ _ _ (wk1 (hB.1 hb))
        | false =>
            have ha : peval v A = false := by
              cases hx : peval v A with
              | false => rfl
              | true => simp [hx, hb] at h'
            refine Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ ?_)
            exact Derives₀.elim_impl _ A Formula.bottom (wk1 (hA.2 ha))
              (Derives₀.hyp _ _ (List.Mem.head _))
      · intro h
        have h' : ((!(peval v A)) || peval v B) = false := h
        have ha : peval v A = true := by
          cases hx : peval v A with
          | true => rfl
          | false => simp [hx] at h'
        have hb : peval v B = false := by
          cases hx : peval v B with
          | false => rfl
          | true => simp [hx] at h'
        refine Derives₀.intro_impl _ _ _ ?_
        refine Derives₀.elim_impl _ B Formula.bottom (wk1 (hB.2 hb)) ?_
        exact Derives₀.elim_impl _ A B (Derives₀.hyp _ _ (List.Mem.head _)) (wk1 (hA.1 ha))
  | and A B ihA ihB =>
      intro hL
      have hA := ihA (fun a ha => hL a (List.mem_append.mpr (Or.inl ha)))
      have hB := ihB (fun a ha => hL a (List.mem_append.mpr (Or.inr ha)))
      constructor
      · intro h
        have h' : (peval v A && peval v B) = true := h
        have ha : peval v A = true := by
          cases hx : peval v A with
          | true => rfl
          | false => simp [hx] at h'
        have hb : peval v B = true := by
          cases hx : peval v B with
          | true => rfl
          | false => simp [hx] at h'
        exact Derives₀.intro_and _ _ _ (hA.1 ha) (hB.1 hb)
      · intro h
        have h' : (peval v A && peval v B) = false := h
        refine Derives₀.intro_impl _ _ _ ?_
        cases ha : peval v A with
        | false =>
            refine Derives₀.elim_impl _ A Formula.bottom (wk1 (hA.2 ha)) ?_
            exact Derives₀.elim_and_l _ A B (Derives₀.hyp _ _ (List.Mem.head _))
        | true =>
            have hb : peval v B = false := by
              cases hx : peval v B with
              | false => rfl
              | true => simp [ha, hx] at h'
            refine Derives₀.elim_impl _ B Formula.bottom (wk1 (hB.2 hb)) ?_
            exact Derives₀.elim_and_r _ A B (Derives₀.hyp _ _ (List.Mem.head _))
  | or A B ihA ihB =>
      intro hL
      have hA := ihA (fun a ha => hL a (List.mem_append.mpr (Or.inl ha)))
      have hB := ihB (fun a ha => hL a (List.mem_append.mpr (Or.inr ha)))
      constructor
      · intro h
        have h' : (peval v A || peval v B) = true := h
        cases ha : peval v A with
        | true => exact Derives₀.intro_or_l _ _ _ (hA.1 ha)
        | false =>
            have hb : peval v B = true := by
              cases hx : peval v B with
              | true => rfl
              | false => simp [ha, hx] at h'
            exact Derives₀.intro_or_r _ _ _ (hB.1 hb)
      · intro h
        have h' : (peval v A || peval v B) = false := h
        have ha : peval v A = false := by
          cases hx : peval v A with
          | false => rfl
          | true => simp [hx] at h'
        have hb : peval v B = false := by
          cases hx : peval v B with
          | false => rfl
          | true => simp [hx] at h'
        refine Derives₀.intro_impl _ _ _ ?_
        refine Derives₀.elim_or _ A B Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _)) ?_ ?_
        · exact Derives₀.elim_impl _ A Formula.bottom (wk1 (wk1 (hA.2 ha)))
            (Derives₀.hyp _ _ (List.Mem.head _))
        · exact Derives₀.elim_impl _ B Formula.bottom (wk1 (wk1 (hB.2 hb)))
            (Derives₀.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §4 · La eliminación de átomos
-- ============================================================

/-- Actualiza una valuación en un punto. ⭐ Aquí paga `FOL.DecEq`: sin `DecidableEq Formula` este
`if` necesitaría `open Classical`, y todo el módulo dejaría de ser net‑0. -/
def upd (v : PVal) (a : Formula) (b : Bool) : PVal := fun x => if x = a then b else v x

theorem upd_self (v : PVal) (a : Formula) (b : Bool) : upd v a b a = b := by simp [upd]

theorem upd_other (v : PVal) (a : Formula) (b : Bool) {x : Formula} (h : x ≠ a) :
    upd v a b x = v x := by simp [upd, h]

/-- El paso de membresía del `weakening`, que es donde está todo el trabajo de §4. -/
private theorem elim_step (v : PVal) (a : Formula) (L Δ : List Formula) (b : Bool)
    (hla : lit (upd v a b) a = (if b = true then a else neg a)) :
    ∀ x, x ∈ (a :: L).map (lit (upd v a b)) ++ Δ →
      x ∈ (if b = true then a else neg a) :: (L.map (lit v) ++ Δ) := by
  intro x hx
  cases List.mem_append.mp hx with
  | inr hm => exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hm))
  | inl hm =>
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
      by_cases hya : y = a
      · subst hya
        rw [hla] at hxy
        exact hxy ▸ List.Mem.head _
      · have hyL : y ∈ L := by
          cases hy with
          | head => exact absurd rfl hya
          | tail _ h' => exact h'
        have heq : lit (upd v a b) y = lit v y := by
          simp only [lit, upd_other v a b hya]
        rw [heq] at hxy
        exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨y, hyL, hxy⟩)))

/-- ⭐⭐ **Se eliminan los átomos uno a uno.**

⚠️ El punto fino está en el `weakening`: `upd v a b` **no** coincide con `v` en el resto de la
lista si `a` está repetido — pero el literal que discrepa es exactamente `a` (o `¬a`), que es la
**cabeza** del contexto objetivo. *Debilitar sale más barato que pedir la lista sin repeticiones.* -/
theorem elim_atoms : ∀ (L : List Formula) (φ : Formula) (Δ : List Formula),
    (∀ v : PVal, (L.map (lit v) ++ Δ) ⊢₀ φ) → Δ ⊢₀ φ
  | [], _, _, h => h (fun _ => true)
  | a :: L, φ, Δ, h => by
      refine elim_atoms L φ Δ (fun v => derives0_cases (A := a) ?_ ?_)
      · have hla : lit (upd v a true) a = (if true = true then a else neg a) := by
          simp [lit, upd_self]
        exact Derives₀.weakening _ _ _ (h (upd v a true)) (elim_step v a L Δ true hla)
      · have hla : lit (upd v a false) a = (if false = true then a else neg a) := by
          simp [lit, upd_self]
        exact Derives₀.weakening _ _ _ (h (upd v a false)) (elim_step v a L Δ false hla)

-- ============================================================
-- §5 · ⭐⭐⭐ H2 · COMPLETITUD PROPOSICIONAL
-- ============================================================

/-- ⭐⭐⭐ **Toda tautología proposicional es derivable** — y **sin `Classical.choice`**. -/
theorem derives0_of_ptaut {φ : Formula} (h : PTaut φ) : [] ⊢₀ φ := by
  refine elim_atoms (patoms φ) φ [] (fun v => ?_)
  refine (kalmar v _ φ ?_).1 (h v)
  intro a ha
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩))

/-- La cadena `g₁ → g₂ → … → φ`. -/
def implChain : List Formula → Formula → Formula
  | [], φ => φ
  | g :: Γ, φ => Formula.impl g (implChain Γ φ)

theorem peval_implChain (v : PVal) : ∀ (Γ : List Formula) (φ : Formula),
    ((∀ g, g ∈ Γ → peval v g = true) → peval v φ = true) →
    peval v (implChain Γ φ) = true
  | [], _, h => h (fun _ hg => absurd hg List.not_mem_nil)
  | g :: Γ', φ, h => by
      show ((!(peval v g)) || peval v (implChain Γ' φ)) = true
      cases hg : peval v g with
      | false => simp
      | true =>
          have hrec : peval v (implChain Γ' φ) = true :=
            peval_implChain v Γ' φ (fun hs => h (fun x hx => by
              cases hx with
              | head => exact hg
              | tail _ hx' => exact hs x hx'))
          simp [hrec]

/-- De una cadena de implicaciones al contexto. -/
theorem derives0_of_implChain : ∀ (Γ : List Formula) (Δ : List Formula) (φ : Formula),
    (Δ ⊢₀ implChain Γ φ) → (∀ g, g ∈ Γ → g ∈ Δ) → Δ ⊢₀ φ
  | [], _, _, h, _ => h
  | g :: Γ', Δ, φ, h, hsub => by
      refine derives0_of_implChain Γ' Δ φ ?_ (fun x hx => hsub x (List.Mem.tail _ hx))
      exact Derives₀.elim_impl _ g _ h (Derives₀.hyp _ _ (hsub g (List.Mem.head _)))

/-- ⭐⭐⭐ **H2: completitud proposicional para `Γ` FINITO.** Ni König ni compacidad: la
valuación recorre una lista finita de átomos y se elimina uno a uno. -/
theorem derives0_of_ptaut_ctx {Γ : List Formula} {φ : Formula}
    (h : ∀ v : PVal, (∀ g, g ∈ Γ → peval v g = true) → peval v φ = true) : Γ ⊢₀ φ := by
  refine derives0_of_implChain Γ Γ φ ?_ (fun _ hx => hx)
  refine Derives₀.weakening _ _ _
    (derives0_of_ptaut (fun v => peval_implChain v Γ φ (h v))) ?_
  exact fun _ hx => absurd hx List.not_mem_nil

-- ============================================================
-- §6 · ⚠️ CONTROL: los MISMOS teoremas, con footprint ESTRICTAMENTE MENOR
-- ============================================================

-- ⭐⭐ `FOL.Canonical0` ya demuestra estos dos, pero **por completitud semántica**, y por eso
-- arrastran `Classical.choice`. Aquí salen por la vía H y son **net‑0**. Es la demostración
-- práctica de para qué sirve la vía H: *el mismo teorema, sin el WKL.*

theorem derives0_em_prop (A : Formula) : [] ⊢₀ Formula.or A (neg A) :=
  derives0_of_ptaut (fun v => by
    show (peval v A || peval v (neg A)) = true
    rw [peval_neg]
    cases peval v A <;> rfl)

theorem derives0_peirce_prop (A B : Formula) :
    [] ⊢₀ Formula.impl (Formula.impl (Formula.impl A B) A) A :=
  derives0_of_ptaut (fun v => by
    show ((!((!((!(peval v A)) || peval v B)) || peval v A)) || peval v A) = true
    cases peval v A <;> cases peval v B <;> rfl)

end FOL.Propositional0

#print axioms FOL.Propositional0.derives0_em_ctx
#print axioms FOL.Propositional0.kalmar
#print axioms FOL.Propositional0.elim_atoms
#print axioms FOL.Propositional0.derives0_of_ptaut
#print axioms FOL.Propositional0.derives0_of_ptaut_ctx
#print axioms FOL.Propositional0.derives0_peirce_prop
