/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.Semantics

/-!
# `FOL/Sentence.lean` — las sentencias: fórmulas sin variables libres (T72, ADR‑215 de RPP)

FOL no tenía noción de sentencia, y RPP tuvo que definir la suya (`IsSentence φ := liftFormula 0 φ = φ`, en su
`Meta/TarskiPrf.lean`). Aquí, la de libro, y su relación con aquélla:

* `closedAt n φ`: toda variable libre de `φ` es menor que `n` (con índices de De Bruijn, bajo `k` binders la libre `i`
  se escribe `#(i + k)`). Computable, por recursión sobre la sintaxis.
* `IsSentence φ := closedAt 0 φ = true`, DECIDIBLE (`instDecidableIsSentence`).
* `evalFormula_agree`: dos valuaciones que coinciden por debajo de `n` dan el mismo valor a una fórmula con
  `closedAt n`; y `eval_sentence`: el valor de una SENTENCIA no depende de la valuación.
* `liftFormula_eq_iff_closedAt`: `liftFormula c φ = φ` si y sólo si `closedAt c φ`; con `c = 0`,
  `isSentence_iff_lift`: la noción de RPP es ésta.

Sin `Classical.choice`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FOL.Sentence

open FOL.Metamath.Semantics

/-! ## §1 · `closedAt` -/

mutual
/-- Las variables del término son todas menores que `n`. -/
def closedAtTerm {S : Type} (n : Nat) (t : TermG S) : Bool :=
  match t with
  | .var k => decide (k < n)
  | .func _ ts => closedAtTerms n ts

/-- Las variables de los términos son todas menores que `n`. -/
def closedAtTerms {S : Type} (n : Nat) (ts : List (TermG S)) : Bool :=
  match ts with
  | [] => true
  | t :: ts' => closedAtTerm n t && closedAtTerms n ts'
end

/-- Las variables LIBRES de la fórmula son todas menores que `n` (bajo un binder, el umbral sube en uno). -/
def closedAt {S : Type} (n : Nat) (f : FormulaG S) : Bool :=
  match f with
  | .bottom => true
  | .atom _ ts => closedAtTerms n ts
  | .eq t1 t2 => closedAtTerm n t1 && closedAtTerm n t2
  | .impl f1 f2 => closedAt n f1 && closedAt n f2
  | .forall f1 => closedAt (n + 1) f1
  | .and f1 f2 => closedAt n f1 && closedAt n f2
  | .or f1 f2 => closedAt n f1 && closedAt n f2
  | .ex f1 => closedAt (n + 1) f1

/-- Una SENTENCIA: una fórmula sin variables libres. -/
def IsSentence {S : Type} (f : FormulaG S) : Prop := closedAt 0 f = true

instance instDecidableIsSentence {S : Type} (f : FormulaG S) : Decidable (IsSentence f) :=
  inferInstanceAs (Decidable (closedAt 0 f = true))

/-! ## §2 · El valor sólo depende de las variables libres -/

mutual
theorem evalTerm_agree {S D : Type} (M : ModelG S D) (n : Nat) (v w : Nat → D)
    (hvw : ∀ k, k < n → v k = w k) (t : TermG S) (h : closedAtTerm n t = true) :
    evalTerm M v t = evalTerm M w t := by
  match t with
  | .var k =>
    unfold closedAtTerm at h
    unfold evalTerm
    exact hvw k (of_decide_eq_true h)
  | .func f ts =>
    unfold closedAtTerm at h
    unfold evalTerm
    rw [evalTerms_agree M n v w hvw ts h]

theorem evalTerms_agree {S D : Type} (M : ModelG S D) (n : Nat) (v w : Nat → D)
    (hvw : ∀ k, k < n → v k = w k) (ts : List (TermG S)) (h : closedAtTerms n ts = true) :
    evalTerms M v ts = evalTerms M w ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold closedAtTerms at h
    rw [Bool.and_eq_true] at h
    unfold evalTerms
    rw [evalTerm_agree M n v w hvw t h.1, evalTerms_agree M n v w hvw ts' h.2]
end

/-- Bajo un binder: si `v` y `w` coinciden por debajo de `n`, sus desplazamientos coinciden por debajo de `n + 1`. -/
theorem shiftEnv_agree {D : Type} (n : Nat) (v w : Nat → D) (hvw : ∀ k, k < n → v k = w k) (d : D) :
    ∀ k, k < n + 1 → shiftEnv v d k = shiftEnv w d k := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k => exact hvw k (Nat.lt_of_succ_lt_succ hk)

theorem evalFormula_agree {S D : Type} (M : ModelG S D) (f : FormulaG S) :
    ∀ (n : Nat) (v w : Nat → D), (∀ k, k < n → v k = w k) → closedAt n f = true →
      (evalFormula M v f ↔ evalFormula M w f) := by
  induction f with
  | bottom => intro _ _ _ _ _; exact Iff.rfl
  | atom p ts =>
    intro n v w hvw h
    unfold closedAt at h
    unfold evalFormula
    rw [evalTerms_agree M n v w hvw ts h]
  | eq t1 t2 =>
    intro n v w hvw h
    unfold closedAt at h
    rw [Bool.and_eq_true] at h
    unfold evalFormula
    rw [evalTerm_agree M n v w hvw t1 h.1, evalTerm_agree M n v w hvw t2 h.2]
  | impl f1 f2 ih1 ih2 =>
    intro n v w hvw h
    unfold closedAt at h
    rw [Bool.and_eq_true] at h
    unfold evalFormula
    rw [ih1 n v w hvw h.1, ih2 n v w hvw h.2]
  | «forall» f1 ih =>
    intro n v w hvw h
    unfold closedAt at h
    unfold evalFormula
    exact forall_congr' fun d => ih (n + 1) _ _ (shiftEnv_agree n v w hvw d) h
  | and f1 f2 ih1 ih2 =>
    intro n v w hvw h
    unfold closedAt at h
    rw [Bool.and_eq_true] at h
    unfold evalFormula
    rw [ih1 n v w hvw h.1, ih2 n v w hvw h.2]
  | or f1 f2 ih1 ih2 =>
    intro n v w hvw h
    unfold closedAt at h
    rw [Bool.and_eq_true] at h
    unfold evalFormula
    rw [ih1 n v w hvw h.1, ih2 n v w hvw h.2]
  | ex f1 ih =>
    intro n v w hvw h
    unfold closedAt at h
    unfold evalFormula
    exact exists_congr fun d => ih (n + 1) _ _ (shiftEnv_agree n v w hvw d) h

/-- 🏁 **El valor de una sentencia no depende de la valuación.** -/
theorem eval_sentence {S D : Type} (M : ModelG S D) {f : FormulaG S} (h : IsSentence f) (v w : Nat → D) :
    evalFormula M v f ↔ evalFormula M w f :=
  evalFormula_agree M f 0 v w (fun _ hk => absurd hk (Nat.not_lt_zero _)) h

/-! ## §3 · `liftFormula c f = f` es `closedAt c f`: la noción de RPP es ésta -/

mutual
theorem liftTerm_eq_iff_closedAtTerm {S : Type} (c : Nat) (t : TermG S) :
    liftTerm c t = t ↔ closedAtTerm c t = true := by
  match t with
  | .var k =>
    unfold liftTerm closedAtTerm
    by_cases hk : k < c
    · rw [ite_eq_left hk]
      exact ⟨fun _ => decide_eq_true hk, fun _ => rfl⟩
    · rw [ite_eq_right hk]
      constructor
      · intro h; injection h with h'; exact absurd h' (Nat.succ_ne_self k)
      · intro h; exact absurd (of_decide_eq_true h) hk
  | .func f ts =>
    unfold liftTerm closedAtTerm
    rw [← liftTerms_eq_iff_closedAtTerms c ts]
    constructor
    · intro h; injection h
    · intro h; rw [h]

theorem liftTerms_eq_iff_closedAtTerms {S : Type} (c : Nat) (ts : List (TermG S)) :
    liftTerms c ts = ts ↔ closedAtTerms c ts = true := by
  match ts with
  | [] => unfold liftTerms closedAtTerms; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | t :: ts' =>
    unfold liftTerms closedAtTerms
    rw [Bool.and_eq_true, ← liftTerm_eq_iff_closedAtTerm c t, ← liftTerms_eq_iff_closedAtTerms c ts']
    constructor
    · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
    · intro h; rw [h.1, h.2]
end

theorem liftFormula_eq_iff_closedAt {S : Type} (f : FormulaG S) :
    ∀ (c : Nat), liftFormula c f = f ↔ closedAt c f = true := by
  induction f with
  | bottom => intro c; unfold liftFormula closedAt; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | atom p ts =>
    intro c
    unfold liftFormula closedAt
    rw [← liftTerms_eq_iff_closedAtTerms c ts]
    constructor
    · intro h; injection h
    · intro h; rw [h]
  | eq t1 t2 =>
    intro c
    unfold liftFormula closedAt
    rw [Bool.and_eq_true, ← liftTerm_eq_iff_closedAtTerm c t1, ← liftTerm_eq_iff_closedAtTerm c t2]
    constructor
    · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
    · intro h; rw [h.1, h.2]
  | impl f1 f2 ih1 ih2 =>
    intro c
    unfold liftFormula closedAt
    rw [Bool.and_eq_true, ← ih1 c, ← ih2 c]
    constructor
    · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
    · intro h; rw [h.1, h.2]
  | «forall» f1 ih =>
    intro c
    unfold liftFormula closedAt
    rw [← ih (c + 1)]
    constructor
    · intro h; injection h
    · intro h; rw [h]
  | and f1 f2 ih1 ih2 =>
    intro c
    unfold liftFormula closedAt
    rw [Bool.and_eq_true, ← ih1 c, ← ih2 c]
    constructor
    · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
    · intro h; rw [h.1, h.2]
  | or f1 f2 ih1 ih2 =>
    intro c
    unfold liftFormula closedAt
    rw [Bool.and_eq_true, ← ih1 c, ← ih2 c]
    constructor
    · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
    · intro h; rw [h.1, h.2]
  | ex f1 ih =>
    intro c
    unfold liftFormula closedAt
    rw [← ih (c + 1)]
    constructor
    · intro h; injection h
    · intro h; rw [h]

/-- 🏁 **La sentencia de RPP es ésta**: `liftFormula 0 f = f` (la definición de `IsSentence` en su
    `Meta/TarskiPrf.lean`) si y sólo si `f` no tiene variables libres. -/
theorem isSentence_iff_lift {S : Type} (f : FormulaG S) : IsSentence f ↔ liftFormula 0 f = f :=
  (liftFormula_eq_iff_closedAt f 0).symm

-- Controles: la decidibilidad calcula, y no es trivial (una variable libre no es sentencia).
example : IsSentence (FormulaG.forall (FormulaG.eq (TermG.var 0) (TermG.var 0)) : FormulaG (List Char)) := by decide
example : ¬ IsSentence (FormulaG.eq (TermG.var 0) (TermG.var 0) : FormulaG (List Char)) := by decide

end FOL.Sentence

#print axioms FOL.Sentence.evalFormula_agree
#print axioms FOL.Sentence.eval_sentence
#print axioms FOL.Sentence.liftFormula_eq_iff_closedAt
#print axioms FOL.Sentence.isSentence_iff_lift
