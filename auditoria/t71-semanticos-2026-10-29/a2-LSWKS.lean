import FOL.Compacity0

/-!
# T71 (mitad semántica) · Löwenheim–Skolem descendente: su ENUNCIADO implica WKS (y algo más)

Método de `FOL.Esencialidad0` (E1, E7): se toma el ENUNCIADO como hipótesis (no el teorema) y se deriva de él un
principio no constructivo sobre un `P : Prop` ARBITRARIO, con footprint dentro de `[propext, Quot.sound]`.

* `ls_down_stmt_implies_wks`, `countable_infinite_stmt_implies_wks`: los enunciados de `loewenheim_skolem_down` y de
  `countable_infinite_of_infinite` implican el esquema de Kripke DÉBIL (WKS).
* De hecho implican `KSdn` (`P → ∃n β n → ¬¬P`, con `β` decidible en `Prop`), que equivale al esquema de Kripke para las
  proposiciones NEGADAS (`KSneg`: `¬R ↔ ∃n β n`); implica WKS y se sigue de WKS + Markov (`MPp`).
* Y la versión UNIFORME (`KSdnSeq`): una sola sucesión doble para toda una familia `P : Nat → Prop` (sin elección
  numerable no se sigue de la puntual).
* `wks_wlpop_implies_wlem`: WKS + WLPOp ⟹ WLEM (lógica pura).

Testigo: `S_P := {∀x (q x ∨ ¬q x)} ∪ {∃x q x | P} ∪ {∀x ¬q x | ¬P}`, con un modelo CONSTRUCTIVO e INFINITO de dominio
`Nat ⊕ {u : Unit // P}`; de un modelo NUMERABLE de `S_P`, con su enumeración `e`, sale `β n := q(e n)`.

📏 Footprint (medido el 2026‑10‑29, Lean v4.35.0, contra FOL `fa0b1f1`): todos los teoremas de este fichero, NINGÚN
axioma; los controles con nombre (`wks_classical`, `wks_classical'`, `ksdnSeq_classical`),
`[propext, Classical.choice, Quot.sound]`, el de los teoremas reales. Dos trampas de `propext`, evitadas (medidas en
`Propext.lean` y `Propext2.lean`): un `match` con patrones SOLAPADOS y `List.length_replicate` del núcleo.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FOL.T71Sem.A2

open FOL.Metamath.Semantics
open FOL.Canonical0 (IsSatisfiable)
open FOL.Compacity0 (CountableDom IsSatisfiableCountable InfiniteDom)

-- ── §0 · Los principios, en la forma literal del contexto ──────────────────
def WLEM : Prop := ∀ P : Prop, Or (Not P) (Not (Not P))

def WLPOp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Or (∀ n, Not (β n)) (Not (∀ n, Not (β n)))

def WKS : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not P) (∀ n, Not (β n)))

/-- Markov para sucesiones decidibles en `Prop`. -/
def MPp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Not (Not (∃ n, β n)) → ∃ n, β n

/-- Lo que de verdad sale: `P` queda ENTRE un Σ⁰₁ decidible y su doble negación. -/
def KSdn : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop,
    And (∀ n, Or (β n) (Not (β n))) (And (P → ∃ n, β n) ((∃ n, β n) → Not (Not P)))

/-- El esquema de Kripke para las proposiciones NEGADAS. -/
def KSneg : Prop :=
  ∀ R : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not R) (∃ n, β n))

/-- `KSdn` UNIFORME: una sola sucesión doble para toda una familia `P : Nat → Prop`. -/
def KSdnSeq : Prop :=
  ∀ P : Nat → Prop, ∃ β : Nat → Nat → Prop,
    And (∀ k n, Or (β k n) (Not (β k n)))
      (∀ k, And (P k → ∃ n, β k n) ((∃ n, β k n) → Not (Not (P k))))

-- ── §1 · La teoría S_P y su modelo constructivo e infinito ─────────────────
/-- El átomo `q(x₀)`. -/
def Aq : Formula := Formula.atom ['q'] [Term.var 0]

/-- `S_P := {∀x (q x ∨ ¬q x)} ∪ {∃x q x | P} ∪ {∀x ¬q x | ¬P}`. -/
def SP (P : Prop) : Formula → Prop := fun x =>
  Or (x = Formula.forall (Formula.or Aq (neg Aq)))
    (Or (And (x = Formula.ex Aq) P) (And (x = Formula.forall (neg Aq)) (Not P)))

/-- El dominio: `Nat` (que lo hace infinito) más un punto que sólo existe si `P`. -/
abbrev D0 (P : Prop) : Type := Sum Nat {_u : Unit // P}

/-- `q` vale exactamente en el punto de `P`. -/
def isR {P : Prop} : D0 P → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- ⚠️ Patrones DISJUNTOS: con `| [d] => … | _ => False` (solapados) el `match` trae `propext` (medido). -/
def relq {P : Prop} : List (D0 P) → Prop
  | [] => False
  | [d] => isR d
  | _ :: _ :: _ => False

def M0 (P : Prop) : Model (D0 P) := ⟨fun _ _ => Sum.inl 0, fun _ ds => relq ds⟩

def v0 (P : Prop) : Nat → D0 P := fun _ => Sum.inl 0

/-- `q(x₀)` en el entorno desplazado por `d` es la relación en `[d]`, por cálculo. -/
theorem eval_Aq {D : Type} (M : Model D) (v : Nat → D) (d : D) :
    evalFormula M (shiftEnv v d) Aq = M.rel ['q'] [d] := rfl

/-- `M0 P ⊨ S_P`, sin lógica clásica: la decidibilidad de `q` es por casos en `Sum`. -/
theorem M0_sat (P : Prop) : ∀ f, SP P f → evalFormula (M0 P) (v0 P) f := by
  intro f hf
  rcases hf with rfl | ⟨rfl, hP⟩ | ⟨rfl, hnP⟩
  · show ∀ d, Or (relq [d]) (relq [d] → False)
    intro d
    cases d with
    | inl _ => exact Or.inr (fun h => h)
    | inr _ => exact Or.inl trivial
  · show ∃ d, relq [d]
    exact ⟨Sum.inr ⟨(), hP⟩, trivial⟩
  · show ∀ d, relq [d] → False
    intro d
    cases d with
    | inl _ => exact fun h => h
    | inr u => exact fun _ => hnP u.property

theorem sat_SP (P : Prop) : IsSatisfiable (SP P) := ⟨D0 P, M0 P, v0 P, M0_sat P⟩

theorem infiniteDom_D0 (P : Prop) : InfiniteDom (D0 P) :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

-- ── §2 · De un modelo NUMERABLE de S_P, la sucesión decidible ──────────────
/-- La extracción: `β n := q(e n)`. Decidible por `∀x (q x ∨ ¬q x)`; `P → ∃n β n` por `∃x q x` y la
suprayectividad de `e`; `∃n β n → ¬¬P` por `¬P → ∀x ¬q x`. -/
theorem extract {P : Prop} {D : Type} (M : Model D) (v : Nat → D) (hC : CountableDom D)
    (hM : ∀ f, SP P f → evalFormula M v f) :
    ∃ β : Nat → Prop,
      And (∀ n, Or (β n) (Not (β n))) (And (P → ∃ n, β n) ((∃ n, β n) → Not (Not P))) := by
  obtain ⟨e, he⟩ := hC
  have hDec : ∀ d, Or (M.rel ['q'] [d]) (Not (M.rel ['q'] [d])) :=
    hM (Formula.forall (Formula.or Aq (neg Aq))) (Or.inl rfl)
  have hEx : P → ∃ d, M.rel ['q'] [d] :=
    fun hP => hM (Formula.ex Aq) (Or.inr (Or.inl ⟨rfl, hP⟩))
  have hNo : Not P → ∀ d, Not (M.rel ['q'] [d]) :=
    fun hnP => hM (Formula.forall (neg Aq)) (Or.inr (Or.inr ⟨rfl, hnP⟩))
  refine ⟨fun n => M.rel ['q'] [e n], fun n => hDec (e n), ?_, ?_⟩
  · intro hP
    obtain ⟨d, hd⟩ := hEx hP
    obtain ⟨n, rfl⟩ := he d
    exact ⟨n, hd⟩
  · intro ⟨n, hn⟩ hnP
    exact hNo hnP (e n) hn

-- ── §3 · Los dos enunciados implican KSdn ──────────────────────────────────
theorem ls_down_stmt_implies_ksdn
    (H : ∀ {S : Formula → Prop}, IsSatisfiable S → IsSatisfiableCountable S) : KSdn := by
  intro P
  obtain ⟨D, M, v, hC, hM⟩ := H (sat_SP P)
  exact extract M v hC hM

theorem countable_infinite_stmt_implies_ksdn
    (H : ∀ {S : Formula → Prop},
      (∃ (D : Type) (M : Model D) (v : Nat → D), And (InfiniteDom D) (∀ f, S f → evalFormula M v f)) →
      ∃ (D : Type) (M : Model D) (v : Nat → D),
        And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)) : KSdn := by
  intro P
  obtain ⟨D, M, v, ⟨hC, _⟩, hM⟩ := H ⟨D0 P, M0 P, v0 P, infiniteDom_D0 P, M0_sat P⟩
  exact extract M v hC hM

-- ── §4 · Lógica pura: KSdn ⟺ KSneg, KSdn ⟹ WKS, WKS + MPp ⟹ KSdn, WKS + WLPOp ⟹ WLEM ──
theorem ksdn_implies_wks : KSdn → WKS := by
  intro h P
  obtain ⟨β, hDec, hPos, hNeg⟩ := h P
  exact ⟨β, hDec, fun hnP n hn => hNeg ⟨n, hn⟩ hnP, fun hAll hP =>
    match hPos hP with
    | ⟨n, hn⟩ => hAll n hn⟩

theorem ksdn_implies_ksneg : KSdn → KSneg := by
  intro h R
  obtain ⟨β, hDec, hPos, hNeg⟩ := h (Not R)
  exact ⟨β, hDec, hPos, fun hEx hR => hNeg hEx (fun hnR => hnR hR)⟩

theorem ksneg_implies_ksdn : KSneg → KSdn := by
  intro h P
  obtain ⟨β, hDec, hIff⟩ := h (Not P)
  exact ⟨β, hDec, fun hP => hIff.mp (fun hnP => hnP hP), hIff.mpr⟩

theorem wks_mpp_implies_ksdn : WKS → MPp → KSdn := by
  intro hW hM P
  obtain ⟨β, hDec, hIff⟩ := hW P
  refine ⟨β, hDec, fun hP => hM β hDec (fun hNo => ?_), fun ⟨n, hn⟩ hnP => hIff.mp hnP n hn⟩
  exact hIff.mpr (fun n hn => hNo ⟨n, hn⟩) hP

/-- WKS + WLPOp ⟹ WLEM. -/
theorem wks_wlpop_implies_wlem : WKS → WLPOp → WLEM := by
  intro hW hL P
  obtain ⟨β, hDec, hIff⟩ := hW P
  cases hL β hDec with
  | inl hAll => exact Or.inl (hIff.mpr hAll)
  | inr hNot => exact Or.inr (fun hnP => hNot (hIff.mp hnP))

-- ── §5 · Los titulares pedidos ─────────────────────────────────────────────
theorem ls_down_stmt_implies_wks
    (H : ∀ {S : Formula → Prop}, IsSatisfiable S → IsSatisfiableCountable S) : WKS :=
  ksdn_implies_wks (ls_down_stmt_implies_ksdn H)

theorem countable_infinite_stmt_implies_wks
    (H : ∀ {S : Formula → Prop},
      (∃ (D : Type) (M : Model D) (v : Nat → D), And (InfiniteDom D) (∀ f, S f → evalFormula M v f)) →
      ∃ (D : Type) (M : Model D) (v : Nat → D),
        And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)) : WKS :=
  ksdn_implies_wks (countable_infinite_stmt_implies_ksdn H)

-- ── §6 · La versión UNIFORME: una familia `P : Nat → Prop` de una vez ──────
/-- El símbolo del predicado `k`‑ésimo: `k` letras `q` (se distinguen por la LONGITUD, sin comparar `List Char`). -/
def symq (k : Nat) : List Char := List.replicate k 'q'

/-- Por inducción propia: `List.length_replicate` del núcleo trae `propext` (medido). -/
theorem symq_length : ∀ k, (symq k).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (symq_length k)

def Aqk (k : Nat) : Formula := Formula.atom (symq k) [Term.var 0]

/-- `S_P := ⋃ₖ {∀x (qₖ x ∨ ¬qₖ x)} ∪ {∃x qₖ x | P k} ∪ {∀x ¬qₖ x | ¬P k}`. -/
def SPs (P : Nat → Prop) : Formula → Prop := fun x =>
  ∃ k, Or (x = Formula.forall (Formula.or (Aqk k) (neg (Aqk k))))
    (Or (And (x = Formula.ex (Aqk k)) (P k)) (And (x = Formula.forall (neg (Aqk k))) (Not (P k))))

abbrev Ds (P : Nat → Prop) : Type := Sum Nat {k : Nat // P k}

/-- `qₛ` vale en el punto `k` de `P` exactamente cuando `s` tiene longitud `k`. -/
def isRs {P : Nat → Prop} (s : List Char) : Ds P → Prop
  | Sum.inl _ => False
  | Sum.inr j => s.length = j.val

def relqs {P : Nat → Prop} (s : List Char) : List (Ds P) → Prop
  | [] => False
  | [d] => isRs s d
  | _ :: _ :: _ => False

def Ms (P : Nat → Prop) : Model (Ds P) := ⟨fun _ _ => Sum.inl 0, fun s ds => relqs s ds⟩

def vs (P : Nat → Prop) : Nat → Ds P := fun _ => Sum.inl 0

theorem Ms_sat (P : Nat → Prop) : ∀ f, SPs P f → evalFormula (Ms P) (vs P) f := by
  intro f ⟨k, hf⟩
  rcases hf with rfl | ⟨rfl, hP⟩ | ⟨rfl, hnP⟩
  · show ∀ d, Or (relqs (symq k) [d]) (relqs (symq k) [d] → False)
    intro d
    cases d with
    | inl _ => exact Or.inr (fun h => h)
    | inr j =>
      show Or ((symq k).length = j.val) ((symq k).length = j.val → False)
      exact match Nat.decEq (symq k).length j.val with
        | isTrue h => Or.inl h
        | isFalse h => Or.inr h
  · show ∃ d, relqs (symq k) [d]
    exact ⟨Sum.inr ⟨k, hP⟩, symq_length k⟩
  · show ∀ d, relqs (symq k) [d] → False
    intro d
    cases d with
    | inl _ => exact fun h => h
    | inr j =>
      intro h
      have hk : k = j.val := (symq_length k).symm.trans h
      exact hnP (hk ▸ j.property)

theorem infiniteDom_Ds (P : Nat → Prop) : InfiniteDom (Ds P) :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

theorem extractSeq {P : Nat → Prop} {D : Type} (M : Model D) (v : Nat → D) (hC : CountableDom D)
    (hM : ∀ f, SPs P f → evalFormula M v f) :
    ∃ β : Nat → Nat → Prop,
      And (∀ k n, Or (β k n) (Not (β k n)))
        (∀ k, And (P k → ∃ n, β k n) ((∃ n, β k n) → Not (Not (P k)))) := by
  obtain ⟨e, he⟩ := hC
  have hDec : ∀ k d, Or (M.rel (symq k) [d]) (Not (M.rel (symq k) [d])) :=
    fun k => hM (Formula.forall (Formula.or (Aqk k) (neg (Aqk k)))) ⟨k, Or.inl rfl⟩
  have hEx : ∀ k, P k → ∃ d, M.rel (symq k) [d] :=
    fun k hP => hM (Formula.ex (Aqk k)) ⟨k, Or.inr (Or.inl ⟨rfl, hP⟩)⟩
  have hNo : ∀ k, Not (P k) → ∀ d, Not (M.rel (symq k) [d]) :=
    fun k hnP => hM (Formula.forall (neg (Aqk k))) ⟨k, Or.inr (Or.inr ⟨rfl, hnP⟩)⟩
  refine ⟨fun k n => M.rel (symq k) [e n], fun k n => hDec k (e n), fun k => ⟨?_, ?_⟩⟩
  · intro hP
    obtain ⟨d, hd⟩ := hEx k hP
    obtain ⟨n, rfl⟩ := he d
    exact ⟨n, hd⟩
  · intro ⟨n, hn⟩ hnP
    exact hNo k hnP (e n) hn

theorem ls_down_stmt_implies_ksdnSeq
    (H : ∀ {S : Formula → Prop}, IsSatisfiable S → IsSatisfiableCountable S) : KSdnSeq := by
  intro P
  obtain ⟨D, M, v, hC, hM⟩ := H (S := SPs P) ⟨Ds P, Ms P, vs P, Ms_sat P⟩
  exact extractSeq M v hC hM

theorem countable_infinite_stmt_implies_ksdnSeq
    (H : ∀ {S : Formula → Prop},
      (∃ (D : Type) (M : Model D) (v : Nat → D), And (InfiniteDom D) (∀ f, S f → evalFormula M v f)) →
      ∃ (D : Type) (M : Model D) (v : Nat → D),
        And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)) : KSdnSeq := by
  intro P
  obtain ⟨D, M, v, ⟨hC, _⟩, hM⟩ := H (S := SPs P) ⟨Ds P, Ms P, vs P, infiniteDom_Ds P, Ms_sat P⟩
  exact extractSeq M v hC hM

theorem ksdnSeq_implies_ksdn : KSdnSeq → KSdn := by
  intro h P
  obtain ⟨β, hDec, hk⟩ := h (fun _ => P)
  exact ⟨β 0, hDec 0, hk 0⟩

-- ── §7 · CONTROLES de no vacuidad: los teoremas reales cumplen las hipótesis ──
example : WKS := ls_down_stmt_implies_wks (fun h => FOL.Compacity0.loewenheim_skolem_down h)
example : WKS :=
  countable_infinite_stmt_implies_wks (fun h => FOL.Compacity0.countable_infinite_of_infinite h)
example : KSdn := ls_down_stmt_implies_ksdn (fun h => FOL.Compacity0.loewenheim_skolem_down h)
example : KSdn :=
  countable_infinite_stmt_implies_ksdn (fun h => FOL.Compacity0.countable_infinite_of_infinite h)
example : KSdnSeq := ls_down_stmt_implies_ksdnSeq (fun h => FOL.Compacity0.loewenheim_skolem_down h)
example : KSdnSeq :=
  countable_infinite_stmt_implies_ksdnSeq (fun h => FOL.Compacity0.countable_infinite_of_infinite h)

/-- Controles con nombre, para MEDIR que sí llevan `Classical.choice` (el de los teoremas reales). -/
theorem wks_classical : WKS :=
  ls_down_stmt_implies_wks (fun h => FOL.Compacity0.loewenheim_skolem_down h)

theorem wks_classical' : WKS :=
  countable_infinite_stmt_implies_wks (fun h => FOL.Compacity0.countable_infinite_of_infinite h)

theorem ksdnSeq_classical : KSdnSeq :=
  ls_down_stmt_implies_ksdnSeq (fun h => FOL.Compacity0.loewenheim_skolem_down h)

end FOL.T71Sem.A2

#print axioms FOL.T71Sem.A2.eval_Aq
#print axioms FOL.T71Sem.A2.M0_sat
#print axioms FOL.T71Sem.A2.sat_SP
#print axioms FOL.T71Sem.A2.infiniteDom_D0
#print axioms FOL.T71Sem.A2.extract
#print axioms FOL.T71Sem.A2.ls_down_stmt_implies_ksdn
#print axioms FOL.T71Sem.A2.countable_infinite_stmt_implies_ksdn
#print axioms FOL.T71Sem.A2.ksdn_implies_wks
#print axioms FOL.T71Sem.A2.ksdn_implies_ksneg
#print axioms FOL.T71Sem.A2.ksneg_implies_ksdn
#print axioms FOL.T71Sem.A2.wks_mpp_implies_ksdn
#print axioms FOL.T71Sem.A2.wks_wlpop_implies_wlem
#print axioms FOL.T71Sem.A2.ls_down_stmt_implies_wks
#print axioms FOL.T71Sem.A2.countable_infinite_stmt_implies_wks
#print axioms FOL.T71Sem.A2.symq_length
#print axioms FOL.T71Sem.A2.Ms_sat
#print axioms FOL.T71Sem.A2.extractSeq
#print axioms FOL.T71Sem.A2.ls_down_stmt_implies_ksdnSeq
#print axioms FOL.T71Sem.A2.countable_infinite_stmt_implies_ksdnSeq
#print axioms FOL.T71Sem.A2.ksdnSeq_implies_ksdn
#print axioms FOL.T71Sem.A2.wks_classical
#print axioms FOL.T71Sem.A2.wks_classical'
#print axioms FOL.T71Sem.A2.ksdnSeq_classical

-- ══ s2: lo que b2 dejó «NO compilado»: KSdnSeq ⟹ KS para ∃k P k con cada P k ¬¬‑estable ══
namespace S2Sigma
open FOL.T71Sem.A2

/-- Búsqueda acotada de una familia decidible. -/
theorem bsearch {δ : Nat → Prop} (hd : ∀ n, Or (δ n) (Not (δ n))) :
    ∀ K, Or (∃ j, And (j < K) (δ j)) (∀ j, j < K → Not (δ j))
  | 0 => Or.inr (fun j hj => absurd hj (Nat.not_lt_zero j))
  | K + 1 =>
    match bsearch hd K with
    | Or.inl ⟨j, hj, h⟩ => Or.inl ⟨j, Nat.lt_succ_of_lt hj, h⟩
    | Or.inr hall =>
      match hd K with
      | Or.inl hK => Or.inl ⟨K, Nat.lt_succ_self K, hK⟩
      | Or.inr hnK => Or.inr (fun j hj hδ =>
          match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
          | Or.inl hlt => hall j hlt hδ
          | Or.inr heq => hnK (heq ▸ hδ))

theorem ksdnSeq_ksSigma (h : KSdnSeq) (P : Nat → Prop) (hst : ∀ k, Not (Not (P k)) → P k) :
    ∃ γ : Nat → Prop, And (∀ m, Or (γ m) (Not (γ m))) (Iff (∃ k, P k) (∃ m, γ m)) := by
  obtain ⟨β, hd, hk⟩ := h P
  -- γ m := ∃ k < m+1, β k (m - k)   (la diagonal m = k + n)
  refine ⟨fun m => ∃ k, And (k < m + 1) (β k (m - k)), fun m => ?_, ?_, ?_⟩
  · cases bsearch (δ := fun k => β k (m - k)) (fun k => hd k (m - k)) (m + 1) with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (fun ⟨k, hk', hb⟩ => h k hk' hb)
  · intro ⟨k, hP⟩
    obtain ⟨n, hn⟩ := (hk k).1 hP
    refine ⟨k + n, k, Nat.lt_succ_of_le (Nat.le_add_right k n), ?_⟩
    have : k + n - k = n := Nat.add_sub_cancel_left k n
    rw [this]; exact hn
  · intro ⟨m, k, _, hb⟩
    exact ⟨k, hst k ((hk k).2 ⟨m - k, hb⟩)⟩

-- control: con el teorema REAL (lleva choice)
theorem ksSigma_classical (P : Nat → Prop) (hst : ∀ k, Not (Not (P k)) → P k) :
    ∃ γ : Nat → Prop, And (∀ m, Or (γ m) (Not (γ m))) (Iff (∃ k, P k) (∃ m, γ m)) :=
  ksdnSeq_ksSigma (ls_down_stmt_implies_ksdnSeq (fun h => FOL.Compacity0.loewenheim_skolem_down h)) P hst
end S2Sigma
#print axioms S2Sigma.bsearch
#print axioms S2Sigma.ksdnSeq_ksSigma
#print axioms S2Sigma.ksSigma_classical
