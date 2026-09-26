/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Canonical0, FOL.Skolem0
-- @axiom_system: classical
-- @importance: high

import FOL.Canonical0
import FOL.Skolem0

/-!
# `FOL.Compacity0` — 🏁 COMPACIDAD, 🏁 LÖWENHEIM–SKOLEM DESCENDENTE y 🏁 EL MODELO INFINITO NUMERABLE, sobre `Derives₀`

    model_existence_iff   : IsConsistent₀ S ↔ IsSatisfiable S
    compactness₀          : IsSatisfiable S ↔ (todo subconjunto FINITO de S es satisfacible)
    loewenheim_skolem_down: IsSatisfiable S → IsSatisfiableCountable S
    infinite_model_of_large: HasLargeModels S → ∃ modelo NUMERABLE e INFINITO de S     (§3)

## ⭐ Por qué esto repara algo, y no es adorno

`cuarentena/Compacity.lean` estuvo apartado desde el 2026‑09‑11 —y se **borró** el 2026‑09‑23 con
el resto de la cuarentena (RPP‑099 §5)—: su `compactness_theorem` estaba declarado **VACUO** —con
esas palabras— en `cuarentena/README.md` y en el barril `FOL.lean`: *«su prueba pasaba por
`soundness`»*, y la solidez de `Derives` es **falsa** (M‑11).
⇒ `compactness₀` es el mismo teorema con el **SUJETO** cambiado. 🔑 Es el patrón ya escarmentado
del proyecto: *cuando un teorema cae, su prueba suele estar bien — lo que cambia es el sujeto.*

## ⭐⭐ La compacidad SINTÁCTICA ya estaba metida en la definición

`DerivesSet₀ S f := ∃ Γ : List Formula, (∀ g ∈ Γ, S g) ∧ (Γ ⊢₀ f)` (`FOL/Henkin0.lean:82`): la
derivabilidad desde un **conjunto** pide un contexto **finito** por construcción.
⇒ la mitad difícil de la compacidad no hay que demostrarla: **está en el tipo**. Lo único que hay
que hacer es cruzar `derives0_soundness` con `model_existence_lemma₀`, y son dos `obtain`.

## ⭐ Löwenheim–Skolem descendente: la obstrucción era el ENUNCIADO, no la prueba

⚠️ Sin Mathlib no hay `Cardinal` ni `Countable`. Aquí «numerable» se dice con lo único que hay:

    CountableDom D := ∃ e : Nat → D, ∀ d, ∃ n, e n = d

Y entonces la prueba es **componer dos cosas que ya existían**: el dominio del modelo canónico es
`QuotientDomain T hMax = Quotient (termSetoid T hMax)` (`FOL/Canonical0.lean`), y
`natToTerm_surj` (`FOL/Enumeration.lean`) enumera los términos ⇒ `Quotient.mk ∘ natToTerm` enumera
el dominio. 🔑 *El modelo que la completitud construye ya era numerable; lo que faltaba era poder
decirlo.*

⚠️ Y hay un detalle que no es gratis: `IsSatisfiable` esconde el dominio bajo un `∃`, así que la
numerabilidad **no se puede añadir a posteriori** — hay que rehacer `model_existence_lemma₀`
llevándola dentro (`model_existence_countable₀`), y con ella `satisfiable_of_shift`
(`countable_of_shift`). Son ocho líneas, pero son ocho líneas que el enunciado obliga a escribir.

## 🏁 §3 · El modelo infinito: la primera APLICACIÓN de la compacidad y de LS↓

El argumento de libro — añadir constantes `cᵢ` con `cᵢ ≠ cⱼ`, compacidad, y LS↓ para bajar a
numerable — con tres piezas y nada más:

* **«infinito» sin Mathlib**: `InfiniteDom D := ∃ e : Nat → D, inyectiva`; y la hipótesis
  `HasLargeModels S`: para todo `n`, un modelo con `n` elementos distintos. ⚠️ **No pide
  finitud**: la prueba no la usa, y pedirla sólo debilitaría el teorema.
* **la teoría ampliada** `infTheory S = S ∪ {cst i ≠ cst j}`. La frescura de las `cst` en `S` es
  hipótesis REAL de `infinite_model_of_large_fresh` (`cst 0 = "g"`); `infinite_model_of_large`
  la ELIMINA sin construir nada: `shiftTheory` + `pullback`, que ya estaban.
* **la satisfacibilidad finita** con `updateCsts`, el `updateFunc` de `Skolem0` ITERADO sobre
  `Nat`: el lema de coincidencia de UN símbolo basta, aplicado `n` veces.

⚠️ **NO es LS↑**: ningún teorema de §3 sube desde un modelo infinito a uno de cardinal mayor. Con
`Formula = FormulaG String` sólo hay ℵ₀ constantes nuevas; la vía de constantes pediría un tipo de
símbolos no numerable (la 2ª entrega de `ModelG`, `Canonical0` genérico en el símbolo, está
CERRADA: ver `FOL/FOL.lean`) más un Lindenbaum transfinito, y la vía de ultraproductos no está en
el árbol. La conclusión es «numerable e infinito»; la biyección con `Nat` no se construye.
Los cuatro controles (`infiniteDom_nat`, `not_infiniteDom_unit`, `hasLargeModels_empty`,
`not_hasLargeModels_one`) prueban que las dos definiciones DISCRIMINAN: `InfiniteDom` (Nat sí, Unit
no) y `HasLargeModels` (la teoría vacía sí, `∀x∀y. x ≐ y` no). Que la conclusión tampoco es trivial
se sigue de lo segundo, porque la conclusión implica `HasLargeModels S`; ese eslabón no está
compilado.

## 📏 Footprint

Los titulares, `[propext, Classical.choice, Quot.sound]`. ⚠️ **Y el `Classical.choice` es el de
siempre y está explicado**: viene de `completeness₀` a través de `model_existence_lemma₀`, y es el
`if IsConsistent₀` Π⁰₁ de `FOL.Lindenbaum0` — el **WKL** (ADR‑041, plan §6.3). No se añade fuerza
nueva. ⛔ Y por eso esto **no** es finitario, al revés que `FOL.Finitary0`: es vía W, no vía H.
⚠️ **En §3 el `Classical.choice` NO viene sólo de la completitud**: `infTheory_finSat` y
`evalTerm_updateCsts` lo llevan SIN pasar por `model_existence_lemma₀`. Es el de `FOL.Fresh0`
(`cst_bound_list`, `cst_inj`; ver su §Footprint: el tercio excluso de `cst_bound_sym` y la
comparación de `String`).
`infinite_model_of_large` pasa además por `Rename.invOf` (vía `hasLargeModels_shift`). El conjunto
de axiomas es el mismo; las procedencias son varias, y sólo una es el WKL.
Excepciones de §3, medidas: `evalFormula_updateCsts` sólo `[propext]`, y los controles
`hasLargeModels_empty` y `not_hasLargeModels_one`, **ningún axioma**.
-/

namespace FOL.Compacity0

open FOL.Henkin0
open FOL.Canonical0
open FOL.Fresh0
open FOL.Lindenbaum0
open FOL.Metamath.Semantics

-- ── §1 · COMPACIDAD ─────────────────────────────────────────────────────────
theorem consistency_of_satisfiable₀ {S : Formula → Prop} (hSat : IsSatisfiable S) :
    IsConsistent₀ S := by
  intro hBot
  obtain ⟨Γ, hΓ, hDer⟩ := hBot
  obtain ⟨D, M, v, hEval⟩ := hSat
  exact FOL.Metamath.Soundness0.derives0_soundness hDer D M v (fun g hg => hEval g (hΓ g hg))

/-- 🏁 **EL TEOREMA DE EXISTENCIA DE MODELO, bicondicional** — la forma de **Henkin** de la
completitud: una teoría es consistente **si y sólo si** tiene modelo.

⭐ Las dos mitades ya estaban, una en cada módulo: `model_existence_lemma₀` (`Canonical0`, la
difícil) y `consistency_of_satisfiable₀` (aquí, la de solidez). Nadie las había juntado, y es con
esta forma —sobre CONJUNTOS, no sobre contextos finitos como `derives0_complete_iff`— con la que la
teoría de modelos cita la completitud. -/
theorem model_existence_iff {S : Formula → Prop} : IsConsistent₀ S ↔ IsSatisfiable S :=
  ⟨model_existence_lemma₀, consistency_of_satisfiable₀⟩

theorem compactness₀ (S : Formula → Prop) :
    Iff (IsSatisfiable S)
        (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) := by
  constructor
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hEval⟩ := hSat
    exact ⟨D, M, v, fun f hf => hEval f (hSub f hf)⟩
  · intro hFin
    refine model_existence_lemma₀ ?_
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    obtain ⟨D, M, v, hEvalΓ⟩ := hFin Γ hΓ
    exact FOL.Metamath.Soundness0.derives0_soundness hDer D M v hEvalΓ

-- ── §2 · LÖWENHEIM–SKOLEM DESCENDENTE ───────────────────────────────────────
/-- «Numerable» sin Mathlib: hay una enumeración suprayectiva. -/
def CountableDom (D : Type) : Prop := ∃ e : Nat → D, ∀ d, ∃ n, e n = d

def IsSatisfiableCountable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D),
    And (CountableDom D) (∀ f, S f → evalFormula M v f)

theorem countable_of_shift {S : Formula → Prop}
    (h : IsSatisfiableCountable (shiftTheory S)) : IsSatisfiableCountable S := by
  obtain ⟨D, M, v, hC, hM⟩ := h
  exact ⟨D, pullback M shift, v, hC,
    fun f hf => (eval_pullback_formula M shift f v).mpr (hM _ ⟨f, hf, rfl⟩)⟩

theorem model_existence_countable₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsSatisfiableCountable S := by
  obtain ⟨T, hMax, hHenkin, hSub⟩ := henkin_completion hCons
  refine countable_of_shift ⟨QuotientDomain T hMax, canonicalModel T hMax, canonicalEnv T hMax,
    ⟨fun n => Quotient.mk (termSetoid T hMax) (FOL.Metamath.Enumeration.natToTerm n), ?_⟩,
    fun f hf => ?_⟩
  · intro d
    obtain ⟨t, ht⟩ := Quotient.exists_rep d
    obtain ⟨n, hn⟩ := FOL.Metamath.Enumeration.natToTerm_surj t
    refine ⟨n, ?_⟩
    show Quotient.mk (termSetoid T hMax) (FOL.Metamath.Enumeration.natToTerm n) = d
    rw [hn]; exact ht
  · exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)

/-- 🏁 **LÖWENHEIM–SKOLEM DESCENDENTE**: toda teoría satisfacible tiene un modelo NUMERABLE. -/
theorem loewenheim_skolem_down {S : Formula → Prop} (hSat : IsSatisfiable S) :
    IsSatisfiableCountable S :=
  model_existence_countable₀ (consistency_of_satisfiable₀ hSat)

-- ── §3 · 🏁 EL MODELO INFINITO por compacidad (numerable) ───────────────────
section Infinito
open FOL.Skolem0
open FOL.Eigenvariable
open FOL.Rename

/-- «Infinito» sin Mathlib: `Nat` se INYECTA en `D`. -/
def InfiniteDom (D : Type) : Prop := ∃ e : Nat → D, ∀ i j, e i = e j → i = j

/-- Para TODO `n`, un modelo de `S` con al menos `n` elementos distintos.
⚠️ El orden es `∀ n, ∃ modelo`: con `∃ modelo, ∀ n` el teorema NO necesitaría la compacidad.
Bastaría construir una inyección `Nat → D` en ese modelo (palomar + elección), nombrarla con las
`cst` y aplicar LS↓ a la teoría AMPLIADA (LS↓ sola no conserva la infinitud). -/
def HasLargeModels (S : Formula → Prop) : Prop :=
  ∀ n : Nat, ∃ (D : Type) (M : Model D) (v : Nat → D),
    And (∀ f, S f → evalFormula M v f)
        (∃ e : Nat → D, ∀ i j, i < n → j < n → e i = e j → i = j)

/-- `cᵢ ≠ cⱼ`, con `cᵢ := cst i` como CONSTANTE (símbolo de función sin argumentos). -/
def neqAx (i j : Nat) : Formula :=
  neg (Formula.eq (Term.func (cst i) []) (Term.func (cst j) []))

/-- `S ∪ {cᵢ ≠ cⱼ : i ≠ j}`. -/
def infTheory (S : Formula → Prop) : Formula → Prop :=
  fun f => Or (S f) (∃ i j, And (Not (i = j)) (f = neqAx i j))

/-- `updateFunc` ITERADO: `cst 0, …, cst (n-1)` pasan a valer `e 0, …, e (n-1)`. -/
def updateCsts {D : Type} (M : Model D) (e : Nat → D) : Nat → Model D
  | 0 => M
  | n + 1 => updateFunc (updateCsts M e n) (cst n) (fun _ => e n)

/-- Coincidencia ITERADA: una fórmula sin ninguna `cst m` no ve la reinterpretación. -/
theorem evalFormula_updateCsts {D : Type} (M : Model D) (e : Nat → D) (f : Formula)
    (v : Nat → D) (hf : ∀ m, Not (occursFormula (cst m) f)) :
    ∀ n, Iff (evalFormula (updateCsts M e n) v f) (evalFormula M v f)
  | 0 => Iff.rfl
  | n + 1 => (evalFormula_updateFunc (updateCsts M e n) (cst n) (fun _ => e n) f v (hf n)).trans
      (evalFormula_updateCsts M e f v hf n)

/-- Y cada `cst i` con `i < n` vale `e i`. -/
theorem evalTerm_updateCsts {D : Type} (M : Model D) (e : Nat → D) (v : Nat → D) :
    ∀ n i, i < n → evalTerm (updateCsts M e n) v (Term.func (cst i) []) = e i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
      show (if cst i = cst n then e n else (updateCsts M e n).func (cst i) []) = e i
      by_cases hin : i = n
      · subst hin; rw [if_pos rfl]
      · rw [if_neg (fun h' => hin (cst_inj i n h'))]
        exact evalTerm_updateCsts M e v n i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

/-- ⭐ La teoría ampliada es FINITAMENTE satisfacible. -/
theorem infTheory_finSat {S : Formula → Prop}
    (hFresh : ∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) (hLarge : HasLargeModels S) :
    ∀ Γ : List Formula, (∀ f, f ∈ Γ → infTheory S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  intro Γ hΓ
  obtain ⟨N, hN⟩ := cst_bound_list Γ
  obtain ⟨D, M, v, hM, e, he⟩ := hLarge N
  refine ⟨D, updateCsts M e N, v, fun f hf => ?_⟩
  rcases hΓ f hf with hS | ⟨i, j, hij, rfl⟩
  · exact (evalFormula_updateCsts M e f v (hFresh f hS) N).mpr (hM f hS)
  · have hiN : i < N := Nat.lt_of_not_le (fun hle =>
      hN i hle (neqAx i j) hf (Or.inl (Or.inl (Or.inl rfl))))
    have hjN : j < N := Nat.lt_of_not_le (fun hle =>
      hN j hle (neqAx i j) hf (Or.inl (Or.inr (Or.inl rfl))))
    show evalTerm (updateCsts M e N) v (Term.func (cst i) [])
        = evalTerm (updateCsts M e N) v (Term.func (cst j) []) → False
    intro hEq
    exact hij (he i j hiN hjN ((evalTerm_updateCsts M e v N i hiN).symm.trans
      (hEq.trans (evalTerm_updateCsts M e v N j hjN))))

/-- 🏁🏁 El modelo infinito, con la frescura de las `cst` como HIPÓTESIS. -/
theorem infinite_model_of_large_fresh {S : Formula → Prop}
    (hFresh : ∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) (hLarge : HasLargeModels S) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f) := by
  obtain ⟨D, M, v, hC, hM⟩ := loewenheim_skolem_down
    ((compactness₀ (infTheory S)).mpr (infTheory_finSat hFresh hLarge))
  refine ⟨D, M, v, ⟨hC, ⟨fun i => evalTerm M v (Term.func (cst i) []), fun i j hij => ?_⟩⟩,
    fun f hf => hM f (Or.inl hf)⟩
  exact Decidable.byContradiction (fun hne => hM (neqAx i j) (Or.inr ⟨i, j, hne, rfl⟩) hij)

/-- Un modelo de `S` con `≥ n` elementos da uno de `shiftTheory S` con el MISMO dominio. -/
theorem hasLargeModels_shift {S : Formula → Prop} (h : HasLargeModels S) :
    HasLargeModels (shiftTheory S) := by
  intro n
  obtain ⟨D, M, v, hM, he⟩ := h n
  refine ⟨D, pullback M (invOf shift), v, fun x hx => ?_, he⟩
  obtain ⟨g, hg, rfl⟩ := hx
  refine (eval_pullback_formula M (invOf shift) (renameFormula shift g) v).mpr ?_
  rw [rename_rename_formula (invOf_spec shift_inj) g]
  exact hM g hg

/-- 🏁🏁🏁 **Modelos con al menos `n` elementos para TODO `n` ⇒ un modelo NUMERABLE e INFINITO**
(en particular: modelos finitos arbitrariamente grandes ⇒ modelo infinito). SIN hipótesis de
frescura: la teoría se muda al sublenguaje `shiftTheory` y vuelve.
⚠️ NO es LS↑: nada sube de un modelo infinito a uno de cardinal mayor (ver la cabecera, §3). Y la
conclusión es «numerable e infinito»; la biyección con `Nat` no se construye. -/
theorem infinite_model_of_large {S : Formula → Prop} (hLarge : HasLargeModels S) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f) := by
  obtain ⟨D, M, v, hDom, hM⟩ := infinite_model_of_large_fresh (S := shiftTheory S)
    (fun f hf m => shiftTheory_fresh m f hf) (hasLargeModels_shift hLarge)
  exact ⟨D, pullback M shift, v, hDom,
    fun f hf => (eval_pullback_formula M shift f v).mpr (hM _ ⟨f, hf, rfl⟩)⟩

/-- Corolario: si hay un modelo infinito cualquiera, hay uno NUMERABLE e infinito. -/
theorem countable_infinite_of_infinite {S : Formula → Prop}
    (h : ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (InfiniteDom D) (∀ f, S f → evalFormula M v f)) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f) := by
  obtain ⟨D, M, v, ⟨e, he⟩, hM⟩ := h
  exact infinite_model_of_large (fun _ => ⟨D, M, v, hM, e, fun i j _ _ hij => he i j hij⟩)

-- ⚠️ CONTROLES DE NO VACUIDAD: las dos definiciones DISCRIMINAN, en los dos sentidos.
theorem infiniteDom_nat : InfiniteDom Nat := ⟨id, fun _ _ h => h⟩

theorem not_infiniteDom_unit : Not (InfiniteDom Unit) := fun ⟨e, he⟩ =>
  absurd (he 0 1 rfl) (by decide)

/-- La hipótesis PUEDE valer: `Nat` es modelo de la teoría vacía con ≥ n elementos distintos para
todo `n`. ⚠️ Testigo INFINITO: no ejercita el caso de modelos sólo finitos, que es el que necesita
la compacidad. -/
theorem hasLargeModels_empty : HasLargeModels (fun _ => False) :=
  fun _ => ⟨Nat, ⟨fun _ _ => 0, fun _ _ => True⟩, id, fun _ h => False.elim h, id,
    fun _ _ _ _ h => h⟩

/-- `∀x∀y. x ≐ y` sólo tiene modelos de UN elemento ⇒ no tiene modelos grandes. -/
theorem not_hasLargeModels_one :
    Not (HasLargeModels (fun f => f = Formula.forall (Formula.forall
      (Formula.eq (Term.var 0) (Term.var 1))))) := by
  intro h
  obtain ⟨D, M, v, hM, e, he⟩ := h 2
  exact absurd (he 0 1 (by decide) (by decide) (hM _ rfl (e 1) (e 0))) (by decide)

end Infinito

end FOL.Compacity0

#print axioms FOL.Compacity0.consistency_of_satisfiable₀
#print axioms FOL.Compacity0.model_existence_iff
#print axioms FOL.Compacity0.compactness₀
#print axioms FOL.Compacity0.model_existence_countable₀
#print axioms FOL.Compacity0.loewenheim_skolem_down
#print axioms FOL.Compacity0.evalFormula_updateCsts
#print axioms FOL.Compacity0.evalTerm_updateCsts
#print axioms FOL.Compacity0.infTheory_finSat
#print axioms FOL.Compacity0.infinite_model_of_large_fresh
#print axioms FOL.Compacity0.infinite_model_of_large
#print axioms FOL.Compacity0.countable_infinite_of_infinite
#print axioms FOL.Compacity0.hasLargeModels_empty
#print axioms FOL.Compacity0.not_hasLargeModels_one
