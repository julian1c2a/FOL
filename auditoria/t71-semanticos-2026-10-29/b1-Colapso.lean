import FOL.Compacity0

/-!
# T71 · b1 — más allá de WLEM: el COLAPSO de las codificaciones naturales de EM, MP y LPO

Pregunta: ¿implican los enunciados de `compactness`, `infinite_model_of_large` (y `_fresh`) algo
ESTRICTAMENTE más fuerte que WLEM (EM, MP, LPO) sin `Classical.choice`?

Lo que un modelo `M` de `S` dice de `S` es NEGATIVO (`info_negativa`): si `M` hace falsa `f`,
entonces `¬ S f`; y una teoría sin `⊥` ni `→` no restringe nada (`positive_sat`). Las disyunciones y
los `∃` de la evaluación combinan esos hechos negativos. Aquí se COMPILAN, sin `Classical.choice`,
tres artefactos que lo hacen preciso para las tres codificaciones naturales:

* §2 el ARTILUGIO DISYUNTIVO `T c d := {Q ∨ R} ∪ {¬Q | c} ∪ {¬R | d}`:
  `IsSatisfiable (T c d) ↔ ¬c ∨ ¬d` (`sat_T_iff`). La compacidad sólo da ¬(c ∧ d) → ¬c ∨ ¬d
  (De Morgan = WLEM); para EM haría falta `P ↔ ¬c`, es decir `P` estable.
* §3 el ARTILUGIO DEL TESTIGO (Kreisel‑Markov) `SM α`: hay un `A`, `A` y la igualdad son decidibles,
  `¬A(#k)` si `α k = false`, y si `α N = true` todo `A` está entre `#0 … #N`. Tiene un modelo
  NUMERABLE e INFINITO SIN NINGUNA HIPÓTESIS (`colapso_MP`): el dominio es el COCIENTE de
  `Option Nat` que identifica el testigo `none` con el MENOR índice verdadero, si lo hay. Así la
  compacidad, LS↓ y §3 aplicados a `SM α` no dan nada que no fuera ya demostrable. Y en ese modelo
  «el testigo tiene nombre» EQUIVALE a `∃ n, α n = true` (`nombrado_iff`): nombrarlo ES Markov.
* §4 la combinación `SL α := SM α ∪ T (∀n, α n = false) (∃n, α n = true)`, el intento de LPO:
  `IsSatisfiable (SL α) ↔ WLPO α`, y con WLPO hay modelo numerable e infinito (`sat_SL_iff_wlpo`).
-/

set_option autoImplicit false

namespace T71Sem.B1

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)
open FOL.Compacity0 (CountableDom InfiniteDom IsSatisfiableCountable HasLargeModels)

-- ── §0 · Sin `⊥` ni `→` NO hay restricción: el modelo de un punto todo‑verdadero lo cumple ──
-- (toda la información que da un modelo pasa por negaciones: `S f` con `f` falsa ⇒ `¬ S f`)
/-- Fórmula POSITIVA: sin `⊥` ni `→`. -/
def Pos : Formula → Prop
  | .bottom => False
  | .atom _ _ => True
  | .eq _ _ => True
  | .impl _ _ => False
  | .forall a => Pos a
  | .and a b => And (Pos a) (Pos b)
  | .or a b => Or (Pos a) (Pos b)
  | .ex a => Pos a

def Mtop : Model Unit := ⟨fun _ _ => (), fun _ _ => True⟩

theorem eval_pos : ∀ (f : Formula) (v : Nat → Unit), Pos f → evalFormula Mtop v f
  | .bottom, _, h => h.elim
  | .atom _ _, _, _ => trivial
  | .eq _ _, _, _ => rfl
  | .impl _ _, _, h => h.elim
  | .forall a, v, h => fun d => eval_pos a (shiftEnv v d) h
  | .and a b, v, h => ⟨eval_pos a v h.1, eval_pos b v h.2⟩
  | .or a b, v, h => h.elim (fun ha => Or.inl (eval_pos a v ha)) (fun hb => Or.inr (eval_pos b v hb))
  | .ex a, v, h => ⟨(), eval_pos a (shiftEnv v ()) h⟩

/-- Una teoría POSITIVA es satisfacible, sin hipótesis: no transporta información. -/
theorem positive_sat (S : Formula → Prop) (hS : ∀ f, S f → Pos f) : IsSatisfiable S :=
  ⟨Unit, Mtop, fun _ => (), fun f hf => eval_pos f _ (hS f hf)⟩

/-- Y lo que da un modelo de `S` sobre `S` es NEGATIVO: una `f` falsa en él no está en `S`. -/
theorem info_negativa {S : Formula → Prop} {D : Type} (M : Model D) (v : Nat → D)
    (hM : ∀ f, S f → evalFormula M v f) (f : Formula) (hf : Not (evalFormula M v f)) : Not (S f) :=
  fun hS => hf (hM f hS)

-- ── §1 · Sintaxis: UN solo símbolo; las ARIDADES distinguen (no se comparan `List Char`) ──
def sA : List Char := ['A']

/-- `A(t)`, aridad 1. -/
def At (t : Term) : Formula := FormulaG.atom sA [t]
/-- `Q`, aridad 0. -/
def Qf : Formula := FormulaG.atom sA []
/-- `R`, aridad 2 (sobre `#0, #0`). -/
def Rf : Formula := FormulaG.atom sA [TermG.var 0, TermG.var 0]

/-- `∃x A(x)`. -/
def exA : Formula := FormulaG.ex (At (TermG.var 0))
/-- `¬A(#k)`. -/
def notA (k : Nat) : Formula := neg (At (TermG.var k))
/-- Bajo un ligador: `x = #0 ∨ … ∨ x = #N` (`x` es `var 0`; `#k` es `var (k+1)`). -/
def disj : Nat → Formula
  | 0 => FormulaG.eq (TermG.var 0) (TermG.var 1)
  | N + 1 => FormulaG.or (disj N) (FormulaG.eq (TermG.var 0) (TermG.var (N + 2)))
/-- `∀x (A(x) → x = #0 ∨ … ∨ x = #N)`. -/
def bound (N : Nat) : Formula := FormulaG.forall (FormulaG.impl (At (TermG.var 0)) (disj N))
/-- `∀x (A(x) ∨ ¬A(x))`. -/
def decA : Formula := FormulaG.forall (FormulaG.or (At (TermG.var 0)) (neg (At (TermG.var 0))))
/-- `∀x∀y (y = x ∨ ¬ y = x)`. -/
def decEqF : Formula := FormulaG.forall (FormulaG.forall
  (FormulaG.or (FormulaG.eq (TermG.var 0) (TermG.var 1))
    (neg (FormulaG.eq (TermG.var 0) (TermG.var 1)))))

-- ── §1b · El dominio COCIENTE: el testigo `none` es el MENOR índice verdadero, si lo hay ──
/-- `k` es el menor índice con `α k = true`. -/
def least (α : Nat → Bool) (k : Nat) : Prop := And (α k = true) (∀ j, j < k → α j = false)

theorem least_unique (α : Nat → Bool) {i k : Nat} (hi : least α i) (hk : least α k) : i = k := by
  cases Nat.lt_or_ge i k with
  | inl h => exact absurd (hi.1.symm.trans (hk.2 i h)) (fun h' => Bool.noConfusion h')
  | inr h =>
    cases Nat.lt_or_ge k i with
    | inl h' => exact absurd (hk.1.symm.trans (hi.2 k h')) (fun h'' => Bool.noConfusion h'')
    | inr h' => exact Nat.le_antisymm h' h

def Rel (α : Nat → Bool) : Option Nat → Option Nat → Prop
  | none, none => True
  | none, some k => least α k
  | some k, none => least α k
  | some j, some k => j = k

theorem rel_refl (α : Nat → Bool) : ∀ x, Rel α x x
  | none => trivial
  | some _ => rfl

theorem rel_symm (α : Nat → Bool) : ∀ {x y}, Rel α x y → Rel α y x
  | none, none, _ => trivial
  | none, some _, h => h
  | some _, none, h => h
  | some _, some _, h => h.symm

theorem rel_trans (α : Nat → Bool) : ∀ {x y z}, Rel α x y → Rel α y z → Rel α x z
  | none, none, none, _, _ => trivial
  | none, none, some _, _, h => h
  | none, some _, none, _, _ => trivial
  | none, some _, some _, h1, h2 => h2 ▸ h1
  | some _, none, none, h1, _ => h1
  | some _, none, some _, h1, h2 => least_unique α h1 h2
  | some _, some _, none, h1, h2 => h1 ▸ h2
  | some _, some _, some _, h1, h2 => h1.trans h2

def setoidR (α : Nat → Bool) : Setoid (Option Nat) where
  r := Rel α
  iseqv := ⟨rel_refl α, fun h => rel_symm α h, fun h1 h2 => rel_trans α h1 h2⟩

abbrev Dq (α : Nat → Bool) : Type := Quotient (setoidR α)

def cls (α : Nat → Bool) (x : Option Nat) : Dq α := Quotient.mk (setoidR α) x

def decRel (α : Nat → Bool) : (x y : Option Nat) → Decidable (Rel α x y)
  | none, none => isTrue trivial
  | none, some k => inferInstanceAs (Decidable (And (α k = true) (∀ j, j < k → α j = false)))
  | some k, none => inferInstanceAs (Decidable (And (α k = true) (∀ j, j < k → α j = false)))
  | some j, some k => inferInstanceAs (Decidable (j = k))

/-- La igualdad del cociente es DECIDIBLE (en `Prop`), porque `Rel` lo es. -/
theorem eq_or_ne_q (α : Nat → Bool) (a b : Dq α) : Or (a = b) (Not (a = b)) := by
  refine Quotient.inductionOn₂ (motive := fun a b => Or (a = b) (Not (a = b))) a b (fun x y => ?_)
  cases decRel α x y with
  | isTrue h => exact Or.inl (Quotient.sound h)
  | isFalse h => exact Or.inr (fun he => h (Quotient.exact he))

/-- El modelo: `Q := q`, `R := r`, `A(d) := d = [none]`; las funciones, constantes. -/
def relM (α : Nat → Bool) (q r : Prop) : List (Dq α) → Prop
  | [] => q
  | [d] => d = cls α none
  | _ :: _ :: _ => r

def Mq (α : Nat → Bool) (q r : Prop) : Model (Dq α) :=
  ⟨fun _ _ => cls α none, fun _ ds => relM α q r ds⟩

/-- `#k` vale `[some k]`. -/
def vq (α : Nat → Bool) : Nat → Dq α := fun k => cls α (some k)

def decode : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

theorem countable_q (α : Nat → Bool) : CountableDom (Dq α) := by
  refine ⟨fun n => cls α (decode n), fun d => ?_⟩
  refine Quotient.inductionOn (motive := fun d => ∃ n, cls α (decode n) = d) d (fun x => ?_)
  cases x with
  | none => exact ⟨0, rfl⟩
  | some k => exact ⟨k + 1, rfl⟩

theorem infinite_q (α : Nat → Bool) : InfiniteDom (Dq α) :=
  ⟨vq α, fun i j h => (Quotient.exact h : Rel α (some i) (some j))⟩

-- búsqueda ACOTADA: de `α n = true`, el menor índice verdadero (sin `Classical`)
theorem exists_true_lt (α : Nat → Bool) :
    ∀ n, Not (∀ j, j < n → α j = false) → ∃ j, And (j < n) (α j = true)
  | 0, h => absurd (fun j hj => absurd hj (Nat.not_lt_zero j)) h
  | n + 1, h => by
    cases hα : α n with
    | true => exact ⟨n, Nat.lt_succ_self n, hα⟩
    | false =>
      have h' : Not (∀ j, j < n → α j = false) := fun hall => h (fun j hj => by
        cases Nat.lt_or_ge j n with
        | inl hlt => exact hall j hlt
        | inr hge =>
          have hjn : j = n := Nat.le_antisymm (Nat.le_of_lt_succ hj) hge
          subst hjn
          exact hα)
      obtain ⟨j, hj, hjt⟩ := exists_true_lt α n h'
      exact ⟨j, Nat.lt_succ_of_lt hj, hjt⟩

theorem exists_least (α : Nat → Bool) (n : Nat) (hn : α n = true) :
    ∃ k, And (k ≤ n) (least α k) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases (inferInstance : Decidable (∀ j, j < n → α j = false)) with
    | isTrue h => exact ⟨n, Nat.le_refl n, hn, h⟩
    | isFalse h =>
      obtain ⟨j, hj, hjt⟩ := exists_true_lt α n h
      obtain ⟨k, hk, hl⟩ := ih j hj hjt
      exact ⟨k, Nat.le_trans hk (Nat.le_of_lt hj), hl⟩

/-- La disyunción acotada se cumple si `d` es uno de `#0 … #N`. -/
theorem disj_of {D : Type} (M : Model D) (v : Nat → D) (d : D) :
    ∀ N k, k ≤ N → d = v k → evalFormula M (shiftEnv v d) (disj N)
  | 0, k, hk, h => by
    have hk0 : k = 0 := Nat.le_antisymm hk (Nat.zero_le k)
    subst hk0
    exact h
  | N + 1, k, hk, h => by
    cases Nat.lt_or_ge k (N + 1) with
    | inl hlt => exact Or.inl (disj_of M v d N k (Nat.le_of_lt_succ hlt) h)
    | inr hge =>
      have hkN : k = N + 1 := Nat.le_antisymm hk hge
      subst hkN
      exact Or.inr h

-- ── §2 · El ARTILUGIO DISYUNTIVO: Sat ⟺ ¬c ∨ ¬d (sólo información NEGATIVA) ──
def T (c d : Prop) : Formula → Prop := fun f =>
  Or (f = FormulaG.or Qf Rf) (Or (And (f = neg Qf) c) (And (f = neg Rf) d))

/-- Un modelo de `T c d` da `¬c ∨ ¬d`; y `¬c ∨ ¬d` basta para construirlo (`Q := ¬c`, `R := ¬d`). -/
theorem sat_T_iff (c d : Prop) : Iff (IsSatisfiable (T c d)) (Or (Not c) (Not d)) := by
  constructor
  · intro ⟨D, M, v, hM⟩
    have hOr : Or (evalFormula M v Qf) (evalFormula M v Rf) := hM _ (Or.inl rfl)
    cases hOr with
    | inl hq => exact Or.inl (fun hc => hM (neg Qf) (Or.inr (Or.inl ⟨rfl, hc⟩)) hq)
    | inr hr => exact Or.inr (fun hd => hM (neg Rf) (Or.inr (Or.inr ⟨rfl, hd⟩)) hr)
  · intro h
    refine ⟨Dq (fun _ => false), Mq (fun _ => false) (Not c) (Not d), vq (fun _ => false),
      fun f hf => ?_⟩
    rcases hf with hf | ⟨hf, hc⟩ | ⟨hf, hd⟩
    · subst hf; exact h
    · subst hf; exact fun hnc => hnc hc
    · subst hf; exact fun hnd => hnd hd

-- ── §3 · El ARTILUGIO DEL TESTIGO (Kreisel‑Markov): satisfacible SIN hipótesis ──
/-- La teoría que «codifica» Markov para `α`. -/
def SM (α : Nat → Bool) : Formula → Prop := fun f =>
  Or (f = exA) (Or (f = decA) (Or (f = decEqF)
    (Or (∃ k, And (α k = false) (f = notA k)) (∃ N, And (α N = true) (f = bound N)))))

theorem modelo_SM (α : Nat → Bool) (q r : Prop) :
    ∀ f, SM α f → evalFormula (Mq α q r) (vq α) f := by
  intro f hf
  rcases hf with h | h | h | ⟨k, hk, h⟩ | ⟨N, hN, h⟩
  · subst h; exact ⟨cls α none, rfl⟩
  · subst h; intro d; exact eq_or_ne_q α d (cls α none)
  · subst h; intro d₁ d₂; exact eq_or_ne_q α d₂ d₁
  · subst h
    intro he
    have hR : Rel α (some k) none := Quotient.exact he
    exact Bool.noConfusion (hR.1.symm.trans hk)
  · subst h
    intro d hd
    obtain ⟨k, hkN, hl⟩ := exists_least α N hN
    exact disj_of (Mq α q r) (vq α) d N k hkN
      (hd.trans (Quotient.sound (s := setoidR α) (a := none) (b := some k) hl))

/-- 🔑 **COLAPSO**: `SM α` tiene un modelo NUMERABLE e INFINITO, para TODO `α`, sin hipótesis. -/
theorem colapso_MP (α : Nat → Bool) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, SM α f → evalFormula M v f) :=
  ⟨Dq α, Mq α True True, vq α, ⟨countable_q α, infinite_q α⟩, modelo_SM α True True⟩

theorem sat_SM (α : Nat → Bool) : IsSatisfiable (SM α) :=
  ⟨Dq α, Mq α True True, vq α, modelo_SM α True True⟩

theorem large_SM (α : Nat → Bool) : HasLargeModels (SM α) :=
  fun _ => ⟨Dq α, Mq α True True, vq α, modelo_SM α True True, vq α,
    fun i j _ _ h => (Quotient.exact h : Rel α (some i) (some j))⟩

/-- 🔑 En el modelo del colapso, que el testigo `[none]` TENGA NOMBRE (`= #k` para algún `k`)
EQUIVALE a `∃ n, α n = true`: nombrarlo es exactamente el contenido de Markov. -/
theorem nombrado_iff (α : Nat → Bool) :
    Iff (∃ k, cls α none = vq α k) (∃ n, α n = true) := by
  constructor
  · intro ⟨k, hk⟩
    have hR : Rel α none (some k) := Quotient.exact hk
    exact ⟨k, hR.1⟩
  · intro ⟨n, hn⟩
    obtain ⟨k, _, hl⟩ := exists_least α n hn
    exact ⟨k, Quotient.sound (s := setoidR α) (a := none) (b := some k) hl⟩

/-- Control de NO VACUIDAD de la codificación: en CUALQUIER modelo de `SM α`, un testigo de `A`
con nombre `#k` da `α k = true`. Si la lógica de primer orden pudiera obligar a nombrar el testigo,
`SM α` daría Markov; no puede (`colapso_MP`). -/
theorem testigo_nombrado {D : Type} (M : Model D) (v : Nat → D) (α : Nat → Bool)
    (hM : ∀ f, SM α f → evalFormula M v f) (d : D)
    (hd : evalFormula M (shiftEnv v d) (At (TermG.var 0))) (k : Nat) (hk : d = v k) :
    α k = true := by
  cases hα : α k with
  | true => rfl
  | false =>
    have h1 : M.rel sA [d] := hd
    rw [hk] at h1
    exact absurd h1 (hM (notA k) (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hα, rfl⟩)))))

-- ── §4 · El intento de LPO: `SL α` es EXACTAMENTE tan fuerte como WLPO para `α` ──
def SL (α : Nat → Bool) : Formula → Prop := fun f =>
  Or (SM α f) (T (∀ n, α n = false) (∃ n, α n = true) f)

theorem wlpo_of_sat_SL (α : Nat → Bool) (h : IsSatisfiable (SL α)) :
    Or (∀ n, α n = false) (Not (∀ n, α n = false)) := by
  obtain ⟨D, M, v, hM⟩ := h
  have hT : IsSatisfiable (T (∀ n, α n = false) (∃ n, α n = true)) :=
    ⟨D, M, v, fun f hf => hM f (Or.inr hf)⟩
  cases (sat_T_iff _ _).mp hT with
  | inl h1 => exact Or.inr h1
  | inr h2 =>
    refine Or.inl (fun n => ?_)
    cases hα : α n with
    | false => rfl
    | true => exact absurd ⟨n, hα⟩ h2

theorem sat_SL_of_wlpo (α : Nat → Bool) (hw : Or (∀ n, α n = false) (Not (∀ n, α n = false))) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, SL α f → evalFormula M v f) := by
  refine ⟨Dq α, Mq α (Not (∀ n, α n = false)) (∀ n, α n = false), vq α,
    ⟨countable_q α, infinite_q α⟩, fun f hf => ?_⟩
  rcases hf with hf | hf
  · exact modelo_SM α _ _ f hf
  · rcases hf with hf | ⟨hf, hc⟩ | ⟨hf, hd⟩
    · subst hf
      cases hw with
      | inl h => exact Or.inr h
      | inr h => exact Or.inl h
    · subst hf; exact fun hq => hq hc
    · subst hf
      intro hr
      obtain ⟨n, hn⟩ := hd
      exact Bool.noConfusion (hn.symm.trans (hr n))

/-- `Sat (SL α) ⟺ WLPO α`: el intento de LPO no pasa de WLPO; lo que falta es nombrar el testigo
de la rama `Q`, que es Markov (`nombrado_iff`). -/
theorem sat_SL_iff_wlpo (α : Nat → Bool) :
    Iff (IsSatisfiable (SL α)) (Or (∀ n, α n = false) (Not (∀ n, α n = false))) :=
  ⟨wlpo_of_sat_SL α, fun hw =>
    let ⟨D, M, v, _, hM⟩ := sat_SL_of_wlpo α hw
    ⟨D, M, v, hM⟩⟩

-- ── Controles: los teoremas REALES se aplican a estas teorías y no dan más ──
/-- La compacidad real sobre `SM α`: lo que da ya estaba (`sat_SM`, sin choice). -/
theorem ctrl_compacidad_SM (α : Nat → Bool) : IsSatisfiable (SM α) :=
  (FOL.Compacity0.compactness (SM α)).mpr (fun _ hΓ =>
    ⟨Dq α, Mq α True True, vq α, fun f hf => modelo_SM α True True f (hΓ f hf)⟩)

/-- §3 real sobre `SM α`: lo que da ya estaba (`colapso_MP`, sin choice). -/
theorem ctrl_infinito_SM (α : Nat → Bool) :
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, SM α f → evalFormula M v f) :=
  FOL.Compacity0.infinite_model_of_large (large_SM α)

/-- Control: `SM` RESTRINGE (no es positiva): el modelo todo‑verdadero no la cumple. -/
theorem SM_restringe : Not (∀ f, SM (fun _ => false) f → evalFormula Mtop (fun _ => ()) f) :=
  fun h => h (notA 0) (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, rfl, rfl⟩)))) trivial

/-!
## La obstrucción GENERAL — ⚠️ INFERIDA, NO MEDIDA (no hay modelo de Lean dentro de Lean)

Lo de arriba sólo cierra TRES codificaciones. Para TODAS, dos modelos de la teoría de tipos de Lean
sin `Classical.choice` (Prop := Ω), en los que los tres enunciados valen y el principio no:

* **EM** — Kripke sobre la cadena `{0 < 1}` (prehaces). El nodo 1 es clásico y todo valor de verdad
  no nulo lo contiene. `S` interno es `Formula → {0, ½, 1}`; la hipótesis interna en 0 (FinSat o
  HasLargeModels) da, en el nodo 1, que `S_½ := {f | S f ≥ ½}` es finitamente satisfacible
  (resp. con modelos finitos grandes) CLÁSICAMENTE; compacidad clásica (+ LS↓) da un `N` numerable
  (e infinito); el modelo de Kripke CONSTANTE `N` fuerza `S` en el nodo 0. EM falla (`P = ½`);
  MP, LPO y WLEM valen allí.
* **MP y LPO (y EM, KS)** — haces sobre `βℕ` (semántica de pilas para los universos). `βℕ` es
  extremadamente disconexo ⇒ WLEM vale; con `α n := χ_{n}`, `¬¬∃n, α n` vale en todo `βℕ` y
  `∃n, α n` sólo en `ℕ` ⇒ MP y LPO fallan. Compacidad: en cada punto aislado `a` la hipótesis interna
  da que `S_a := {f | a ∈ U_f}` es finitamente satisfacible clásicamente; con `N_a ⊨ S_a`, el
  empuje `j_*(N_a)` tiene semántica de Łoś `⟦f⟧ = cl {a | N_a ⊨ f}` (inducción: `→` y `∀` porque
  los valores son clopen, `∃` con testigos elegidos punto a punto) y `U_f ⊆ cl (U_f ∩ ℕ)`. §3 y
  LS↓: lo mismo con cascos de Skolem UNIFORMES (términos de Skolem sobre los símbolos objeto, las
  funciones de Skolem, constantes `dᵢ` distintas y `w_k` del entorno), dominio `ℕ_Sh / R` con
  `R_{st} := cl {a | N_a ⊨ s = t}`: la enumeración es internamente suprayectiva y `dᵢ` inyectiva.
-/

end T71Sem.B1

#print axioms T71Sem.B1.eval_pos
#print axioms T71Sem.B1.positive_sat
#print axioms T71Sem.B1.info_negativa
#print axioms T71Sem.B1.least_unique
#print axioms T71Sem.B1.eq_or_ne_q
#print axioms T71Sem.B1.countable_q
#print axioms T71Sem.B1.infinite_q
#print axioms T71Sem.B1.exists_least
#print axioms T71Sem.B1.disj_of
#print axioms T71Sem.B1.sat_T_iff
#print axioms T71Sem.B1.modelo_SM
#print axioms T71Sem.B1.colapso_MP
#print axioms T71Sem.B1.sat_SM
#print axioms T71Sem.B1.large_SM
#print axioms T71Sem.B1.nombrado_iff
#print axioms T71Sem.B1.testigo_nombrado
#print axioms T71Sem.B1.wlpo_of_sat_SL
#print axioms T71Sem.B1.sat_SL_of_wlpo
#print axioms T71Sem.B1.sat_SL_iff_wlpo
#print axioms T71Sem.B1.ctrl_compacidad_SM
#print axioms T71Sem.B1.ctrl_infinito_SM
#print axioms T71Sem.B1.SM_restringe

-- ════════ s1 (escéptico): «la satisfacibilidad finita de T c d equivale a ¬(c ∧ d)» ════════
namespace T71Sem.B1

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)

theorem T_split (c d : Prop) : ∀ Γ : List Formula, (∀ f, f ∈ Γ → T c d f) →
    Or c (∀ f, f ∈ Γ → Or (f = FormulaG.or Qf Rf) (f = neg Rf))
  | [], _ => Or.inr (fun _ hf => absurd hf List.not_mem_nil)
  | g :: Γ, hΓ => by
    have ih := T_split c d Γ (fun f hf => hΓ f (List.Mem.tail g hf))
    rcases hΓ g (List.Mem.head Γ) with hg | ⟨_, hc⟩ | ⟨hg, _⟩
    · rcases ih with hc | hall
      · exact Or.inl hc
      · refine Or.inr (fun f hf => ?_)
        cases hf with
        | head => exact Or.inl hg
        | tail _ h => exact hall f h
    · exact Or.inl hc
    · rcases ih with hc | hall
      · exact Or.inl hc
      · refine Or.inr (fun f hf => ?_)
        cases hf with
        | head => exact Or.inr hg
        | tail _ h => exact hall f h

theorem finSat_T_iff (c d : Prop) :
    Iff (∀ Γ : List Formula, (∀ f, f ∈ Γ → T c d f) → IsSatisfiable (fun x => x ∈ Γ))
        (Not (And c d)) := by
  constructor
  · intro hFin hcd
    obtain ⟨D, M, v, hM⟩ := hFin [FormulaG.or Qf Rf, neg Qf, neg Rf] (fun f hf => by
      cases hf with
      | head => exact Or.inl rfl
      | tail _ h =>
        cases h with
        | head => exact Or.inr (Or.inl ⟨rfl, hcd.1⟩)
        | tail _ h =>
          cases h with
          | head => exact Or.inr (Or.inr ⟨rfl, hcd.2⟩)
          | tail _ h => exact absurd h List.not_mem_nil)
    have hOr : Or (evalFormula M v Qf) (evalFormula M v Rf) := hM _ (List.Mem.head _)
    have hnQ : Not (evalFormula M v Qf) := hM (neg Qf) (List.Mem.tail _ (List.Mem.head _))
    have hnR : Not (evalFormula M v Rf) :=
      hM (neg Rf) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    cases hOr with
    | inl h => exact hnQ h
    | inr h => exact hnR h
  · intro hncd Γ hΓ
    rcases T_split c d Γ hΓ with hc | hall
    · refine ⟨Dq (fun _ => false), Mq (fun _ => false) False True, vq (fun _ => false),
        fun f hf => ?_⟩
      rcases hΓ f hf with h | ⟨h, _⟩ | ⟨_, hd⟩
      · subst h; exact Or.inr trivial
      · subst h; exact fun hq => hq
      · exact absurd ⟨hc, hd⟩ hncd
    · refine ⟨Dq (fun _ => false), Mq (fun _ => false) True False, vq (fun _ => false),
        fun f hf => ?_⟩
      rcases hall f hf with h | h
      · subst h; exact Or.inl trivial
      · subst h; exact fun hr => hr

/-- La vuelta de la compacidad sobre `T c d` da EXACTAMENTE De Morgan (⟺ WLEM). -/
theorem deMorgan_of_compactness_mpr
    (H : ∀ S : Formula → Prop,
      (∀ Γ : List Formula, (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ)) → IsSatisfiable S) :
    ∀ c d : Prop, Not (And c d) → Or (Not c) (Not d) :=
  fun c d h => (sat_T_iff c d).mp (H (T c d) ((finSat_T_iff c d).mpr h))

theorem ctl_deMorgan : ∀ c d : Prop, Not (And c d) → Or (Not c) (Not d) :=
  deMorgan_of_compactness_mpr (fun _ => (FOL.Compacity0.compactness _).mpr)

end T71Sem.B1

#print axioms T71Sem.B1.T_split
#print axioms T71Sem.B1.finSat_T_iff
#print axioms T71Sem.B1.deMorgan_of_compactness_mpr
#print axioms T71Sem.B1.ctl_deMorgan
