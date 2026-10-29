/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Compacity0, FOL.Esencialidad0
-- @axiom_system: intuitionistic (ninguno de sus teoremas lleva axiomas, ni propext: es lo que miden)
-- @importance: medium

import FOL.Compacity0
import FOL.Esencialidad0

/-!
# `FOL.EsencialidadSem0` — la esencialidad del `Classical.choice` de los CINCO SEMÁNTICOS de `Compacity0` (T71, ADR‑221 de RPP)

El método de `FOL.Esencialidad0`: se toma el ENUNCIADO de cada teorema como hipótesis y se deriva de él un principio
no constructivo sobre un `P : Prop` (o una sucesión) ARBITRARIO. Aquí, sin NINGÚN axioma, ni `propext`: ninguna prueba
de esos enunciados puede evitar la lógica clásica. Los cinco, clasificados:

| enunciado | implica, sin axiomas | |
|---|---|---|
| `compactness` (basta su vuelta) | WLEM, `¬P ∨ ¬¬P` | E8 |
| `loewenheim_skolem_down`, `countable_infinite_of_infinite` | KSst (el esquema de Kripke para las `P` ¬¬‑estables) y, de él, WKS | E9 |
| `infinite_model_of_large`, `infinite_model_of_large_fresh` | WLPO para sucesiones decidibles y WKS; juntos, WLEM | E10 |

* **E8** — el testigo de E7, `S_P := {Q ∨ R} ∪ {¬Q | P} ∪ {¬R | ¬P}`. E7 necesitaba su CONSISTENCIA; aquí basta su
  satisfacibilidad FINITA, que sale sin choice, sin solidez y sin la igualdad decidible de `Formula`: una lista trae la
  evidencia de pertenencia de cada miembro. Un modelo de `S_P` da WLEM. ⭐ No es el infinito: basta la vuelta para las
  teorías contenidas en TRES fórmulas fijas (`compactness_mpr_L3_implies_wlem`). Lo clásico es la pertenencia NO
  DECIDIDA: con soporte finito y pertenencia decidida, la vuelta sale sin choice (`sat_of_finSat_of_em`).
* **E9** — lo único que LS↓ añade al modelo de partida, que ya satisface la teoría, es la NUMERABILIDAD. Con
  `S_P := {∀x (q x ∨ ¬q x)} ∪ {∃x q x | P} ∪ {∀x ¬q x | ¬P}` y el modelo infinito `Nat ⊕ PLift P`, la enumeración `e`
  del modelo numerable da una sucesión decidible `β n := q(e n)` con `P → ∃n β n` y `∃n β n → ¬¬P`: KSst. WLEM lo
  implica (`wlem_implies_ksst`), así que E9 queda por debajo de E8 y E10.
* **E10** — `S_β := {r ∨ ¬r} ∪ {r | ∀n ¬β n} ∪ {G k ⇒ ¬r | β k}`, con `G k` «hay al menos `k+1` elementos distintos»,
  tiene modelos FINITOS de todo tamaño. En uno INFINITO valen todas las guardas `G k`, así que `r ∨ ¬r` decide
  `∀n ¬β n` (WLPOp). Con el WKS de la numerabilidad (la extracción de E9), WLEM. ⚠️ El palomar es propio: el del núcleo
  (`List.Nodup.length_le_of_subset`) lleva `Classical.choice`.

⚠️ **Lo que NO está compilado** (ADR‑221 de RPP, con su ámbito):
* que WLEM, KSst y WKS no se demuestren sin choice. Lo dan contramodelos de Kripke: en el poset `{0<1, 0<2}` fallan los
  tres, porque WKS ⟺ WLEM en todo marco de Kripke. Es la misma evidencia que la de E7;
* las cotas por arriba: ninguno de los cinco implica EM (Kripke sobre `{0<1}`), y LS↓ no implica KS (el topos de
  Sierpinski).

El registro de la exploración, con sus medidas: `auditoria/t71-semanticos-2026-10-29/`. Nada de esto lo consume otro
módulo: es la medida, en el build, con su fila de footprint en RPP.
-/

namespace FOL.EsencialidadSem0

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)
open FOL.Compacity0 (CountableDom IsSatisfiableCountable InfiniteDom HasLargeModels)
open FOL.Eigenvariable (occursFormula)
open FOL.Fresh0 (cst)

-- ── Los principios ──────────────────────────────────────────────────────────
/-- El tercio excluso DÉBIL. -/
abbrev WLEM : Prop := ∀ P : Prop, Or (Not P) (Not (Not P))

/-- WLPO para sucesiones decidibles en `Prop` (sin choice, de `∀ n, β n ∨ ¬β n` no sale una `Nat → Bool`). -/
abbrev WLPOp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Or (∀ n, Not (β n)) (Not (∀ n, Not (β n)))

/-- El esquema de Kripke DÉBIL (el KS⁻ de Dragalin), con la sucesión decidible en `Prop`. -/
abbrev WKS : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not P) (∀ n, Not (β n)))

/-- El esquema de Kripke para las proposiciones ¬¬‑ESTABLES. -/
abbrev KSst : Prop :=
  ∀ P : Prop, (Not (Not P) → P) →
    ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff P (∃ n, β n))

-- ── Los cinco ENUNCIADOS, como proposiciones ────────────────────────────────
/-- El enunciado de `FOL.Compacity0.compactness`. -/
abbrev CompactnessStmt : Prop :=
  ∀ S : Formula → Prop, Iff (IsSatisfiable S)
    (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ))

/-- El enunciado de `FOL.Compacity0.loewenheim_skolem_down`. -/
abbrev LsDownStmt : Prop := ∀ {S : Formula → Prop}, IsSatisfiable S → IsSatisfiableCountable S

/-- El enunciado de `FOL.Compacity0.countable_infinite_of_infinite`. -/
abbrev CountableInfStmt : Prop :=
  ∀ {S : Formula → Prop},
    (∃ (D : Type) (M : Model D) (v : Nat → D), And (InfiniteDom D) (∀ f, S f → evalFormula M v f)) →
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)

/-- El enunciado de `FOL.Compacity0.infinite_model_of_large`. -/
abbrev LargeStmt : Prop :=
  ∀ {S : Formula → Prop}, HasLargeModels S →
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)

/-- El enunciado de `FOL.Compacity0.infinite_model_of_large_fresh`. -/
abbrev LargeFreshStmt : Prop :=
  ∀ {S : Formula → Prop}, (∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) → HasLargeModels S →
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)

-- ⚠️ Las hipótesis SON los enunciados reales, no sólo consecuencias suyas: identidad de tipos, reducible.
example : CompactnessStmt = type_of% @FOL.Compacity0.compactness := by with_reducible rfl
example : LsDownStmt = type_of% @FOL.Compacity0.loewenheim_skolem_down := by with_reducible rfl
example : CountableInfStmt = type_of% @FOL.Compacity0.countable_infinite_of_infinite := by with_reducible rfl
example : LargeStmt = type_of% @FOL.Compacity0.infinite_model_of_large := by with_reducible rfl
example : LargeFreshStmt = type_of% @FOL.Compacity0.infinite_model_of_large_fresh := by with_reducible rfl

end FOL.EsencialidadSem0

namespace FOL.EsencialidadSem0.E8

/-
E8 · El ENUNCIADO de `compactness` —basta su VUELTA: finitamente satisfacible ⇒ satisfacible— implica WLEM, con el
testigo de E7. Su satisfacibilidad finita no pide la solidez: por inducción sobre la lista, haciendo casos sobre la
disyunción de pertenencia de cada miembro (la meta es una `Prop`).
-/

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)
open FOL.Esencialidad0.E7 (MB Qf Rf SP)

/-- El invariante: o vale `P`, o todo miembro de `Γ` es `Q ∨ R` o `¬R`. -/
theorem SP_list_split (P : Prop) :
    ∀ Γ : List Formula, (∀ f, f ∈ Γ → SP P f) →
      Or P (∀ f, f ∈ Γ → Or (f = Formula.or Qf Rf) (f = neg Rf))
  | [], _ => Or.inr (fun _ hf => absurd hf List.not_mem_nil)
  | g :: Γ, hΓ => by
    have ih := SP_list_split P Γ (fun f hf => hΓ f (List.Mem.tail g hf))
    rcases hΓ g (List.Mem.head Γ) with hg | ⟨_, hP⟩ | ⟨hg, _⟩
    · rcases ih with hP | hall
      · exact Or.inl hP
      · refine Or.inr (fun f hf => ?_)
        cases hf with
        | head => exact Or.inl hg
        | tail _ h => exact hall f h
    · exact Or.inl hP
    · rcases ih with hP | hall
      · exact Or.inl hP
      · refine Or.inr (fun f hf => ?_)
        cases hf with
        | head => exact Or.inr hg
        | tail _ h => exact hall f h

/-- ⭐ `S_P` es FINITAMENTE satisfacible: sin choice, sin solidez, sin `DecidableEq Formula`. -/
theorem SP_finSat (P : Prop) :
    ∀ Γ : List Formula, (∀ f, f ∈ Γ → SP P f) → IsSatisfiable (fun x => x ∈ Γ) := by
  intro Γ hΓ
  rcases SP_list_split P Γ hΓ with hP | hall
  · -- vale `P`: `Q := False, R := True` (un `¬R` exigiría `¬P`)
    refine ⟨Unit, MB false true, fun _ => (), fun f hf => ?_⟩
    rcases hΓ f hf with h | ⟨h, _⟩ | ⟨_, hn⟩
    · subst h; exact Or.inr rfl
    · subst h; exact fun hq => Bool.noConfusion hq
    · exact absurd hP hn
  · -- ningún miembro es `¬Q`: `Q := True, R := False`
    refine ⟨Unit, MB true false, fun _ => (), fun f hf => ?_⟩
    rcases hall f hf with h | h
    · subst h; exact Or.inl rfl
    · subst h; exact fun hr => Bool.noConfusion hr

/-- De un modelo de `S_P`, WLEM para `P` (el argumento de E7). -/
theorem wlem_of_model (P : Prop) (h : IsSatisfiable (SP P)) : Or (Not P) (Not (Not P)) := by
  obtain ⟨D, M, v, hM⟩ := h
  have hOr : Or (evalFormula M v Qf) (evalFormula M v Rf) := hM (Formula.or Qf Rf) (Or.inl rfl)
  have hPQ : P → Not (evalFormula M v Qf) := fun hP => hM (neg Qf) (Or.inr (Or.inl ⟨rfl, hP⟩))
  have hnPR : Not P → Not (evalFormula M v Rf) :=
    fun hnP => hM (neg Rf) (Or.inr (Or.inr ⟨rfl, hnP⟩))
  cases hOr with
  | inl hq => exact Or.inl (fun hP => hPQ hP hq)
  | inr hr => exact Or.inr (fun hnP => hnPR hnP hr)

/-- 🏁 La VUELTA de la compacidad, sola, implica WLEM. -/
theorem compactness_mpr_stmt_implies_wlem
    (H : ∀ S : Formula → Prop,
      (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) → IsSatisfiable S) :
    WLEM :=
  fun P => wlem_of_model P (H (SP P) (SP_finSat P))

/-- 🏁 El ENUNCIADO de `FOL.Compacity0.compactness` implica WLEM. -/
theorem compactness_stmt_implies_wlem (H : CompactnessStmt) : WLEM :=
  compactness_mpr_stmt_implies_wlem (fun S => (H S).mpr)

/-- Las tres fórmulas del testigo. -/
def L3 : List Formula := [Formula.or Qf Rf, neg Qf, neg Rf]

/-- `S_P` vive dentro de `L3`. -/
theorem SP_support (P : Prop) : ∀ f, SP P f → f ∈ L3 := by
  intro f hf
  rcases hf with h | ⟨h, _⟩ | ⟨h, _⟩
  · subst h; exact List.Mem.head _
  · subst h; exact List.Mem.tail _ (List.Mem.head _)
  · subst h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- ⭐ La vuelta de la compacidad SÓLO para las teorías contenidas en `L3` implica WLEM: lo clásico no está en el
infinito. -/
theorem compactness_mpr_L3_implies_wlem
    (H : ∀ S : Formula → Prop, (∀ f, S f → f ∈ L3) →
      (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) → IsSatisfiable S) :
    WLEM :=
  fun P => wlem_of_model P (H (SP P) (SP_support P) (SP_finSat P))

/-- El CONTRASTE: con soporte finito y pertenencia DECIDIDA (`∀ f, S f ∨ ¬S f`, en `Prop`), la vuelta sale sin
choice: la parte de `L` que está en `S` existe como lista. -/
theorem sat_of_finSat_of_em (L : List Formula) (S : Formula → Prop)
    (hL : ∀ f, S f → f ∈ L) (hem : ∀ f, Or (S f) (Not (S f)))
    (hFin : ∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) :
    IsSatisfiable S := by
  have key : ∀ L' : List Formula, ∃ Γ : List Formula,
      And (∀ f, f ∈ Γ → S f) (∀ f, S f → f ∈ L' → f ∈ Γ) := by
    intro L'
    induction L' with
    | nil =>
      exact ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil⟩
    | cons g L' ih =>
      obtain ⟨Γ, h1, h2⟩ := ih
      rcases hem g with hg | hg
      · refine ⟨g :: Γ, fun f hf => ?_, fun f hf hm => ?_⟩
        · cases hf with
          | head => exact hg
          | tail _ h => exact h1 f h
        · cases hm with
          | head => exact List.Mem.head _
          | tail _ h => exact List.Mem.tail _ (h2 f hf h)
      · refine ⟨Γ, h1, fun f hf hm => ?_⟩
        cases hm with
        | head => exact absurd hf hg
        | tail _ h => exact h2 f hf h
  obtain ⟨Γ, h1, h2⟩ := key L
  obtain ⟨D, M, v, hM⟩ := hFin Γ h1
  exact ⟨D, M, v, fun f hf => hM f (h2 f hf (hL f hf))⟩

/-- Lente de vacuidad del contraste: sus hipótesis caben JUNTAS con una teoría no vacía (`{Q}`, con la igualdad
decidible de `Formula` de `FOL.DecEq`). -/
theorem sat_of_finSat_of_em_noVacuo : IsSatisfiable (fun f => f = Qf) :=
  sat_of_finSat_of_em [Qf] (fun f => f = Qf)
    (fun f h => by subst h; exact List.Mem.head _)
    (fun f => if h : f = Qf then Or.inl h else Or.inr h)
    (fun Γ hΓ => ⟨Unit, MB true true, fun _ => (), fun f hf => by
      have h := hΓ f hf
      subst h
      exact rfl⟩)

-- ⚠️ CONTROLES DE NO VACUIDAD: el teorema REAL cumple las hipótesis (y lleva `Classical.choice`).
example : WLEM := compactness_stmt_implies_wlem FOL.Compacity0.compactness
example : WLEM := compactness_mpr_stmt_implies_wlem (fun _ => (FOL.Compacity0.compactness _).mpr)
example : WLEM := compactness_mpr_L3_implies_wlem (fun _ _ h => (FOL.Compacity0.compactness _).mpr h)

end FOL.EsencialidadSem0.E8

namespace FOL.EsencialidadSem0.E9

/-
E9 · Los ENUNCIADOS de `loewenheim_skolem_down` y de `countable_infinite_of_infinite` implican KSst: toda `P`
¬¬‑estable es Σ⁰₁ con una matriz decidible en `Prop`. La enumeración del modelo numerable convierte el `∃x` de su
dominio en un `∃n`. `P` sólo entra en el ANTECEDENTE de «`S_P f` → el modelo satisface `f`», así que de él sólo salen
hechos NEGADOS sobre `P`: por eso KSst, y no KS.
-/

open FOL.Metamath.Semantics
open FOL.Compacity0 (CountableDom InfiniteDom)

/-- El átomo `q(x₀)`. -/
def qF : Formula := Formula.atom ['q'] [Term.var 0]

/-- `S_P := {∀x (q x ∨ ¬q x)} ∪ {∃x q x | P} ∪ {∀x ¬q x | ¬P}`. -/
def SQ (P : Prop) : Formula → Prop := fun x =>
  Or (x = Formula.forall (Formula.or qF (neg qF)))
    (Or (And (x = Formula.ex qF) P) (And (x = Formula.forall (neg qF)) (Not P)))

def isR {P : Prop} : Sum Nat (PLift P) → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- ⚠️ Patrones DISJUNTOS: con `| [d] => … | _ => False` (solapados), la DEFINICIÓN lleva `propext`. -/
def relQ {P : Prop} : List (Sum Nat (PLift P)) → Prop
  | [] => False
  | d :: _ => isR d

/-- El modelo INFINITO `Nat ⊕ PLift P`: `q` es «estar a la derecha», que tiene un punto si y sólo si `P`. -/
def MQ (P : Prop) : Model (Sum Nat (PLift P)) := ⟨fun _ _ => Sum.inl 0, fun _ ds => relQ ds⟩

/-- `MQ P` es modelo de `S_P`, con cualquier asignación, sin choice. -/
theorem sat_SQ (P : Prop) (v : Nat → Sum Nat (PLift P)) : ∀ f, SQ P f → evalFormula (MQ P) v f := by
  intro f hf
  rcases hf with h | ⟨h, hP⟩ | ⟨h, hnP⟩
  · subst h
    intro d
    cases d with
    | inl _ => exact Or.inr (fun h => h)
    | inr _ => exact Or.inl trivial
  · subst h; exact ⟨Sum.inr ⟨hP⟩, trivial⟩
  · subst h
    intro d hd
    cases d with
    | inl _ => exact hd
    | inr u => exact hnP u.down

theorem infiniteDom_MQ (P : Prop) : InfiniteDom (Sum Nat (PLift P)) :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

/-- ⭐ La extracción: de un modelo NUMERABLE de `S_P`, una sucesión decidible `β n := q(e n)` con `P → ∃n β n` (por la
suprayectividad de `e`) y `∃n β n → ¬¬P` (si `¬P`, nadie cumple `q`). -/
theorem kripke_of_model {P : Prop} {D : Type} (M : Model D) (v : Nat → D) (hC : CountableDom D)
    (hM : ∀ f, SQ P f → evalFormula M v f) :
    ∃ β : Nat → Prop,
      And (∀ n, Or (β n) (Not (β n))) (And (P → ∃ n, β n) ((∃ n, β n) → Not (Not P))) := by
  obtain ⟨e, he⟩ := hC
  have hq : ∀ d, Or (evalFormula M (shiftEnv v d) qF) (Not (evalFormula M (shiftEnv v d) qF)) :=
    hM (Formula.forall (Formula.or qF (neg qF))) (Or.inl rfl)
  refine ⟨fun n => evalFormula M (shiftEnv v (e n)) qF, fun n => hq (e n), fun hP => ?_,
    fun hex hnP => ?_⟩
  · obtain ⟨d, hd⟩ : ∃ d, evalFormula M (shiftEnv v d) qF :=
      hM (Formula.ex qF) (Or.inr (Or.inl ⟨rfl, hP⟩))
    obtain ⟨n, rfl⟩ := he d
    exact ⟨n, hd⟩
  · obtain ⟨n, hn⟩ := hex
    exact hM (Formula.forall (neg qF)) (Or.inr (Or.inr ⟨rfl, hnP⟩)) (e n) hn

/-- El emparedado de `kripke_of_model` da la instancia de WKS para esa `P`. -/
theorem wks_of_kripke {P : Prop} {β : Nat → Prop} (h1 : P → ∃ n, β n) (h2 : (∃ n, β n) → Not (Not P)) :
    Iff (Not P) (∀ n, Not (β n)) :=
  ⟨fun hnP n hn => h2 ⟨n, hn⟩ hnP, fun hall hP => (h1 hP).elim (fun n hn => hall n hn)⟩

/-- 🏁 El ENUNCIADO de `FOL.Compacity0.loewenheim_skolem_down` implica KSst. -/
theorem ls_down_stmt_implies_ksst (H : LsDownStmt) : KSst := by
  intro P hst
  obtain ⟨D, M, v, hC, hM⟩ := H (S := SQ P) ⟨Sum Nat (PLift P), MQ P, fun _ => Sum.inl 0, sat_SQ P _⟩
  obtain ⟨β, hd, h1, h2⟩ := kripke_of_model M v hC hM
  exact ⟨β, hd, h1, fun hex => hst (h2 hex)⟩

/-- 🏁 El ENUNCIADO de `FOL.Compacity0.countable_infinite_of_infinite` implica KSst. -/
theorem countable_infinite_stmt_implies_ksst (H : CountableInfStmt) : KSst := by
  intro P hst
  obtain ⟨D, M, v, ⟨hC, _⟩, hM⟩ :=
    H (S := SQ P) ⟨Sum Nat (PLift P), MQ P, fun _ => Sum.inl 0, infiniteDom_MQ P, sat_SQ P _⟩
  obtain ⟨β, hd, h1, h2⟩ := kripke_of_model M v hC hM
  exact ⟨β, hd, h1, fun hex => hst (h2 hex)⟩

/-- KSst ⟹ WKS (lógica pura): KSst sobre `¬¬P`, que es estable. -/
theorem ksst_implies_wks : KSst → WKS := by
  intro h P
  obtain ⟨β, hd, hiff⟩ := h (Not (Not P)) (fun hnnn hnP => hnnn (fun hnn => hnn hnP))
  refine ⟨β, hd, fun hnP n hn => hiff.mpr ⟨n, hn⟩ hnP, fun hall hP => ?_⟩
  obtain ⟨n, hn⟩ := hiff.mp (fun hnP => hnP hP)
  exact hall n hn

/-- WLEM ⟹ KSst (lógica pura): con `¬P` decidido basta una `β` constante. KSst queda por debajo de WLEM. -/
theorem wlem_implies_ksst : WLEM → KSst := by
  intro h P hst
  cases h P with
  | inl hnP => exact ⟨fun _ => False, fun _ => Or.inr id, fun hP => absurd hP hnP, fun ⟨_, h⟩ => h.elim⟩
  | inr hnnP => exact ⟨fun _ => True, fun _ => Or.inl trivial, fun _ => ⟨0, trivial⟩, fun _ => hst hnnP⟩

/-- El enunciado de LS↓ implica WKS. -/
theorem ls_down_stmt_implies_wks (H : LsDownStmt) : WKS :=
  ksst_implies_wks (ls_down_stmt_implies_ksst H)

/-- El enunciado de `countable_infinite_of_infinite` implica WKS. -/
theorem countable_infinite_stmt_implies_wks (H : CountableInfStmt) : WKS :=
  ksst_implies_wks (countable_infinite_stmt_implies_ksst H)

-- ⚠️ CONTROLES DE NO VACUIDAD: los teoremas REALES cumplen las hipótesis (y llevan `Classical.choice`).
example : KSst := ls_down_stmt_implies_ksst (fun h => FOL.Compacity0.loewenheim_skolem_down h)
example : KSst :=
  countable_infinite_stmt_implies_ksst (fun h => FOL.Compacity0.countable_infinite_of_infinite h)

end FOL.EsencialidadSem0.E9

namespace FOL.EsencialidadSem0.E10

/-
E10 · Los ENUNCIADOS de `infinite_model_of_large` y de `infinite_model_of_large_fresh` implican WLPOp (las guardas
«hay ≥ k+1 elementos», que sólo se activan todas en un modelo infinito) y WKS (la numerabilidad, por la extracción
de E9); juntos, WLEM. Ninguna fórmula de los testigos tiene símbolos de función: la frescura de las `cst` es gratis.
-/

open FOL.Metamath.Semantics
open FOL.Compacity0 (CountableDom InfiniteDom HasLargeModels)
open FOL.Eigenvariable (occursFormula)
open FOL.Fresh0 (cst)
open FOL.EsencialidadSem0.E9 (qF SQ MQ sat_SQ kripke_of_model wks_of_kripke)

-- ── El palomar, sin `Classical` ─────────────────────────────────────────────
/-- ⚠️ El del núcleo (`List.Nodup.length_le_of_subset`) mide `[propext, Classical.choice, Quot.sound]` (v4.35.0,
2026‑10‑29). Éste es una inducción sobre `N` con la igualdad decidible de `Nat`: se cambia el valor `N` por `f m`. -/
theorem pigeon : ∀ (N m : Nat) (f : Nat → Nat), (∀ i, i < m → f i < N) →
    (∀ i j, i < m → j < m → f i = f j → i = j) → m ≤ N
  | _, 0, _, _, _ => Nat.zero_le _
  | 0, m + 1, _, hlt, _ => absurd (hlt 0 (Nat.succ_pos m)) (Nat.not_lt_zero _)
  | N + 1, m + 1, f, hlt, hinj => by
    have hfm : f m < N + 1 := hlt m (Nat.lt_succ_self m)
    refine Nat.succ_le_succ (pigeon N m (fun i => if f i = N then f m else f i) ?_ ?_)
    · intro i hi
      have hi' : i < m + 1 := Nat.lt_succ_of_lt hi
      show (if f i = N then f m else f i) < N
      by_cases h : f i = N
      · rw [ite_eq_left h]
        refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hfm) (fun hmN => ?_)
        have him : i = m := hinj i m hi' (Nat.lt_succ_self m) (h.trans hmN.symm)
        subst him
        exact Nat.lt_irrefl i hi
      · rw [ite_eq_right h]
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hlt i hi')) h
    · intro i j hi hj hij
      have hi' : i < m + 1 := Nat.lt_succ_of_lt hi
      have hj' : j < m + 1 := Nat.lt_succ_of_lt hj
      have hij' : (if f i = N then f m else f i) = (if f j = N then f m else f j) := hij
      by_cases h1 : f i = N <;> by_cases h2 : f j = N
      · exact hinj i j hi' hj' (h1.trans h2.symm)
      · rw [ite_eq_left h1, ite_eq_right h2] at hij'
        have hmj : m = j := hinj m j (Nat.lt_succ_self m) hj' hij'
        subst hmj
        exact absurd hj (Nat.lt_irrefl m)
      · rw [ite_eq_right h1, ite_eq_left h2] at hij'
        have him : i = m := hinj i m hi' (Nat.lt_succ_self m) hij'
        subst him
        exact absurd hi (Nat.lt_irrefl i)
      · rw [ite_eq_right h1, ite_eq_right h2] at hij'
        exact hinj i j hi' hj' hij'

-- ── «Hay al menos k+1 elementos distintos» ──────────────────────────────────
/-- `var 0` es distinto de `var 1, …, var m` (los `m` elegidos antes del `∃` que lo introduce). -/
def distF : Nat → Formula
  | 0 => top
  | m + 1 => Formula.and (distF m) (neg (Formula.eq (Term.var 0) (Term.var (m + 1))))

/-- `HF k m`: hay `k` elementos NUEVOS, distintos entre sí y de los `m` ya elegidos (`var 0, …, var (m-1)`). -/
def HF : Nat → Nat → Formula
  | 0, _ => top
  | k + 1, m => Formula.ex (Formula.and (distF m) (HF k (m + 1)))

/-- `G k`: hay al menos `k + 1` elementos distintos dos a dos. -/
def GF (k : Nat) : Formula := HF (k + 1) 0

theorem distF_of {D : Type} (M : Model D) : ∀ (m : Nat) (w : Nat → D),
    (∀ i, i < m → Not (w 0 = w (i + 1))) → evalFormula M w (distF m)
  | 0, _, _ => fun h => h
  | m + 1, w, h => by
    show And (evalFormula M w (distF m)) (Not (w 0 = w (m + 1)))
    exact ⟨distF_of M m w (fun i hi => h i (Nat.lt_succ_of_lt hi)), h m (Nat.lt_succ_self m)⟩

theorem of_distF {D : Type} (M : Model D) : ∀ (m : Nat) (w : Nat → D),
    evalFormula M w (distF m) → ∀ i, i < m → Not (w 0 = w (i + 1))
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, w, h, i, hi => by
    have h' : And (evalFormula M w (distF m)) (Not (w 0 = w (m + 1))) := h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
    · exact of_distF M m w h'.1 i hlt
    · subst heq; exact h'.2

/-- Con `e : Nat → D` INYECTIVA, `HF k m` vale si los `m` elegidos son valores de `e` en índices `≥ k`: el testigo
nuevo es `e k`. -/
theorem HF_of_inj {D : Type} (M : Model D) (e : Nat → D) (he : ∀ i j, e i = e j → i = j) :
    ∀ (k m : Nat) (w : Nat → D), (∀ i, i < m → ∃ j, And (k ≤ j) (w i = e j)) →
      evalFormula M w (HF k m)
  | 0, _, _, _ => fun h => h
  | k + 1, m, w, hw => by
    show ∃ d, And (evalFormula M (shiftEnv w d) (distF m))
      (evalFormula M (shiftEnv w d) (HF k (m + 1)))
    refine ⟨e k, distF_of M m (shiftEnv w (e k)) ?_, HF_of_inj M e he k (m + 1) (shiftEnv w (e k)) ?_⟩
    · intro i hi heq
      obtain ⟨j, hkj, hj⟩ := hw i hi
      have heq' : e k = w i := heq
      have hkj' : k = j := he k j (heq'.trans hj)
      subst hkj'
      exact absurd hkj (Nat.not_succ_le_self k)
    · intro i hi
      cases i with
      | zero => exact ⟨k, Nat.le_refl k, rfl⟩
      | succ i =>
        obtain ⟨j, hkj, hj⟩ := hw i (Nat.lt_of_succ_lt_succ hi)
        exact ⟨j, Nat.le_of_succ_le hkj, hj⟩

/-- ⭐ En un dominio `Fin N`, `HF k m` con los `m` elegidos distintos obliga a `k + m ≤ N`: el palomar. -/
theorem count_HF {N : Nat} (M : Model (Fin N)) :
    ∀ (k m : Nat) (w : Nat → Fin N), (∀ i j, i < m → j < m → w i = w j → i = j) →
      evalFormula M w (HF k m) → k + m ≤ N
  | 0, m, w, hw, _ => by
    have hp : m ≤ N := pigeon N m (fun i => (w i).val) (fun i _ => (w i).isLt)
      (fun i j hi hj h => hw i j hi hj (Fin.eq_of_val_eq h))
    rw [Nat.zero_add]
    exact hp
  | k + 1, m, w, hw, h => by
    have h' : ∃ d, And (evalFormula M (shiftEnv w d) (distF m))
        (evalFormula M (shiftEnv w d) (HF k (m + 1))) := h
    obtain ⟨x, hx1, hx2⟩ := h'
    have hd := of_distF M m (shiftEnv w x) hx1
    have hc : k + (m + 1) ≤ N := count_HF M k (m + 1) (shiftEnv w x) (fun i j hi hj hij => by
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j => exact absurd hij (hd j (Nat.lt_of_succ_lt_succ hj))
      | succ i =>
        cases j with
        | zero => exact absurd hij.symm (hd i (Nat.lt_of_succ_lt_succ hi))
        | succ j =>
          exact congrArg Nat.succ
            (hw i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hij)) hx2
    rw [Nat.succ_add]
    exact hc

-- ── WLPOp ───────────────────────────────────────────────────────────────────
def rF : Formula := Formula.atom ['r'] []

/-- `S_β := {r ∨ ¬r} ∪ {r | ∀ n, ¬β n} ∪ {G k ⇒ ¬r | β k}`. -/
def Sβ (β : Nat → Prop) : Formula → Prop := fun x =>
  Or (x = Formula.or rF (neg rF))
    (Or (And (x = rF) (∀ n, Not (β n))) (∃ k, And (β k) (x = Formula.impl (GF k) (neg rF))))

/-- `∀ k < N, ¬β k` es decidible si `β` lo es (inducción acotada). -/
theorem bdec (β : Nat → Prop) (hdec : ∀ n, Or (β n) (Not (β n))) :
    ∀ N, Or (∀ k, k < N → Not (β k)) (Not (∀ k, k < N → Not (β k)))
  | 0 => Or.inl (fun k hk => absurd hk (Nat.not_lt_zero k))
  | N + 1 => by
    cases bdec β hdec N with
    | inr h => exact Or.inr (fun hall => h (fun k hk => hall k (Nat.lt_succ_of_lt hk)))
    | inl h =>
      cases hdec N with
      | inl hb => exact Or.inr (fun hall => hall N (Nat.lt_succ_self N) hb)
      | inr hnb =>
        refine Or.inl (fun k hk => ?_)
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
        · exact h k hlt
        · subst heq; exact hnb

/-- El modelo FINITO de tamaño `n + 1`: `r` dice «ningún `β k` con `k ≤ n`». -/
def MF (β : Nat → Prop) (n : Nat) : Model (Fin (n + 1)) :=
  ⟨fun _ _ => ⟨0, Nat.succ_pos n⟩, fun _ _ => ∀ k, k < n + 1 → Not (β k)⟩

/-- La inyección de `{0, …, n}` en `Fin (n + 1)`. ⚠️ Con `dite` y no con `%`: `Nat.mod_eq_of_lt` lleva `propext`. -/
def eF (n : Nat) (i : Nat) : Fin (n + 1) := if h : i < n + 1 then ⟨i, h⟩ else ⟨0, Nat.succ_pos n⟩

theorem eF_val (n i : Nat) (h : i < n + 1) : (eF n i).val = i := by
  show (if h : i < n + 1 then (⟨i, h⟩ : Fin (n + 1)) else ⟨0, Nat.succ_pos n⟩).val = i
  rw [dite_eq_left h]

/-- `S_β` tiene modelos (finitos) de todo tamaño, si `β` es decidible. -/
theorem large_Sβ (β : Nat → Prop) (hdec : ∀ n, Or (β n) (Not (β n))) : HasLargeModels (Sβ β) := by
  intro n
  refine ⟨Fin (n + 1), MF β n, fun _ => ⟨0, Nat.succ_pos n⟩, fun f hf => ?_, eF n,
    fun i j hi hj hij => ?_⟩
  · rcases hf with h | ⟨h, hall⟩ | ⟨k, hk, h⟩
    · subst h; exact bdec β hdec (n + 1)
    · subst h; exact fun k _ => hall k
    · subst h
      intro hG hR
      have hc : k + 1 + 0 ≤ n + 1 := count_HF (MF β n) (k + 1) 0 (fun _ => ⟨0, Nat.succ_pos n⟩)
        (fun i _ hi => absurd hi (Nat.not_lt_zero i)) hG
      exact hR k (Nat.lt_of_succ_le hc) hk
  · have hi' : i < n + 1 := Nat.lt_succ_of_lt hi
    have hj' : j < n + 1 := Nat.lt_succ_of_lt hj
    have h1 : (eF n i).val = (eF n j).val := congrArg Fin.val hij
    rw [eF_val n i hi', eF_val n j hj'] at h1
    exact h1

/-- Desde un modelo INFINITO de `S_β`: todos los `G k` valen, y `r ∨ ¬r` decide `∀ n, ¬β n`. -/
theorem wlpo_of_model (β : Nat → Prop)
    (h : ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, Sβ β f → evalFormula M v f)) :
    Or (∀ n, Not (β n)) (Not (∀ n, Not (β n))) := by
  obtain ⟨D, M, v, ⟨_, e, he⟩, hM⟩ := h
  have hG : ∀ k, evalFormula M v (GF k) := fun k =>
    HF_of_inj M e he (k + 1) 0 v (fun i hi => absurd hi (Nat.not_lt_zero i))
  have hor : Or (evalFormula M v rF) (Not (evalFormula M v rF)) :=
    hM (Formula.or rF (neg rF)) (Or.inl rfl)
  cases hor with
  | inl hr =>
    exact Or.inl (fun k hk =>
      hM (Formula.impl (GF k) (neg rF)) (Or.inr (Or.inr ⟨k, hk, rfl⟩)) (hG k) hr)
  | inr hnr =>
    exact Or.inr (fun hall => hnr (hM rF (Or.inr (Or.inl ⟨rfl, hall⟩))))

/-- 🏁 El ENUNCIADO de `infinite_model_of_large` implica WLPO para sucesiones decidibles. -/
theorem infinite_large_stmt_implies_wlpop (H : LargeStmt) : WLPOp :=
  fun β hdec => wlpo_of_model β (H (large_Sβ β hdec))

-- ── WKS, por la numerabilidad ───────────────────────────────────────────────
/-- `S_P` (el de E9) tiene modelos grandes: `MQ P` es infinito. -/
theorem large_SQ (P : Prop) : HasLargeModels (SQ P) := fun _ =>
  ⟨Sum Nat (PLift P), MQ P, fun _ => Sum.inl 0, sat_SQ P _, Sum.inl, fun _ _ _ _ h => Sum.inl.inj h⟩

/-- De un modelo NUMERABLE de `S_P`, la instancia de WKS para `P` (la extracción de E9). -/
theorem wks_of_model (P : Prop)
    (h : ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, SQ P f → evalFormula M v f)) :
    ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not P) (∀ n, Not (β n))) := by
  obtain ⟨D, M, v, ⟨hC, _⟩, hM⟩ := h
  obtain ⟨β, hd, h1, h2⟩ := kripke_of_model M v hC hM
  exact ⟨β, hd, wks_of_kripke h1 h2⟩

/-- 🏁 El ENUNCIADO de `infinite_model_of_large` implica el esquema de Kripke débil. -/
theorem infinite_large_stmt_implies_wks (H : LargeStmt) : WKS :=
  fun P => wks_of_model P (H (large_SQ P))

-- ── WKS ∧ WLPOp ⟹ WLEM ──────────────────────────────────────────────────────
theorem wks_wlpop_implies_wlem : WKS → WLPOp → WLEM := by
  intro hW hL P
  obtain ⟨β, hdec, hiff⟩ := hW P
  cases hL β hdec with
  | inl h => exact Or.inl (hiff.mpr h)
  | inr h => exact Or.inr (fun hnP => h (hiff.mp hnP))

/-- 🏁 El ENUNCIADO de `infinite_model_of_large` implica el tercio excluso débil. -/
theorem infinite_large_stmt_implies_wlem (H : LargeStmt) : WLEM :=
  wks_wlpop_implies_wlem (infinite_large_stmt_implies_wks H) (infinite_large_stmt_implies_wlpop H)

-- ── Con la frescura: sin símbolos de función, ninguna `cst m` aparece ───────
theorem noOcc_top (c : List Char) : Not (occursFormula c (top : Formula)) := by
  show Not (Or False False)
  intro h; rcases h with h | h <;> exact h

theorem noOcc_distF (c : List Char) : ∀ m, Not (occursFormula c (distF m))
  | 0 => noOcc_top c
  | m + 1 => by
    show Not (Or (occursFormula c (distF m)) (Or (Or False False) False))
    intro h
    rcases h with h | (h | h) | h
    · exact noOcc_distF c m h
    · exact h
    · exact h
    · exact h

theorem noOcc_HF (c : List Char) : ∀ k m, Not (occursFormula c (HF k m))
  | 0, _ => noOcc_top c
  | k + 1, m => by
    show Not (Or (occursFormula c (distF m)) (occursFormula c (HF k (m + 1))))
    intro h
    rcases h with h | h
    · exact noOcc_distF c m h
    · exact noOcc_HF c k (m + 1) h

theorem fresh_Sβ (β : Nat → Prop) : ∀ f, Sβ β f → ∀ m, Not (occursFormula (cst m) f) := by
  intro f hf m
  rcases hf with h | ⟨h, _⟩ | ⟨k, _, h⟩
  · subst h
    show Not (Or False (Or False False))
    intro h; rcases h with h | h | h <;> exact h
  · subst h
    show Not False
    exact fun h => h
  · subst h
    show Not (Or (occursFormula (cst m) (HF (k + 1) 0)) (Or False False))
    intro h; rcases h with h | h | h
    · exact noOcc_HF (cst m) (k + 1) 0 h
    · exact h
    · exact h

theorem fresh_SQ (P : Prop) : ∀ f, SQ P f → ∀ m, Not (occursFormula (cst m) f) := by
  intro f hf m
  rcases hf with h | ⟨h, _⟩ | ⟨h, _⟩
  · subst h
    show Not (Or (Or False False) (Or (Or False False) False))
    intro h; rcases h with (h | h) | (h | h) | h <;> exact h
  · subst h
    show Not (Or False False)
    intro h; rcases h with h | h <;> exact h
  · subst h
    show Not (Or (Or False False) False)
    intro h; rcases h with (h | h) | h <;> exact h

/-- 🏁 El ENUNCIADO de `infinite_model_of_large_fresh` implica el tercio excluso débil. -/
theorem infinite_large_fresh_stmt_implies_wlem (H : LargeFreshStmt) : WLEM :=
  wks_wlpop_implies_wlem (fun P => wks_of_model P (H (fresh_SQ P) (large_SQ P)))
    (fun β hdec => wlpo_of_model β (H (fresh_Sβ β) (large_Sβ β hdec)))

-- ⚠️ CONTROLES DE NO VACUIDAD: los teoremas REALES cumplen las hipótesis (y llevan `Classical.choice`).
example : WLEM := infinite_large_stmt_implies_wlem (fun h => FOL.Compacity0.infinite_model_of_large h)
example : WLEM :=
  infinite_large_fresh_stmt_implies_wlem
    (fun hF hL => FOL.Compacity0.infinite_model_of_large_fresh hF hL)

end FOL.EsencialidadSem0.E10

#print axioms FOL.EsencialidadSem0.E8.SP_finSat
#print axioms FOL.EsencialidadSem0.E8.wlem_of_model
#print axioms FOL.EsencialidadSem0.E8.compactness_mpr_stmt_implies_wlem
#print axioms FOL.EsencialidadSem0.E8.compactness_stmt_implies_wlem
#print axioms FOL.EsencialidadSem0.E8.compactness_mpr_L3_implies_wlem
#print axioms FOL.EsencialidadSem0.E8.sat_of_finSat_of_em
#print axioms FOL.EsencialidadSem0.E8.sat_of_finSat_of_em_noVacuo
#print axioms FOL.EsencialidadSem0.E9.sat_SQ
#print axioms FOL.EsencialidadSem0.E9.kripke_of_model
#print axioms FOL.EsencialidadSem0.E9.ls_down_stmt_implies_ksst
#print axioms FOL.EsencialidadSem0.E9.countable_infinite_stmt_implies_ksst
#print axioms FOL.EsencialidadSem0.E9.ksst_implies_wks
#print axioms FOL.EsencialidadSem0.E9.wlem_implies_ksst
#print axioms FOL.EsencialidadSem0.E9.ls_down_stmt_implies_wks
#print axioms FOL.EsencialidadSem0.E9.countable_infinite_stmt_implies_wks
#print axioms FOL.EsencialidadSem0.E10.pigeon
#print axioms FOL.EsencialidadSem0.E10.count_HF
#print axioms FOL.EsencialidadSem0.E10.HF_of_inj
#print axioms FOL.EsencialidadSem0.E10.large_Sβ
#print axioms FOL.EsencialidadSem0.E10.wlpo_of_model
#print axioms FOL.EsencialidadSem0.E10.infinite_large_stmt_implies_wlpop
#print axioms FOL.EsencialidadSem0.E10.infinite_large_stmt_implies_wks
#print axioms FOL.EsencialidadSem0.E10.wks_wlpop_implies_wlem
#print axioms FOL.EsencialidadSem0.E10.infinite_large_stmt_implies_wlem
#print axioms FOL.EsencialidadSem0.E10.infinite_large_fresh_stmt_implies_wlem
