/-!
# T71 (mitad semántica) · b2 · DÓNDE cae WKS en el retículo de principios (lógica pura, sin FOL)

Complemento de `a2/LSWKS.lean` (que deriva de los enunciados de `loewenheim_skolem_down` y de
`countable_infinite_of_infinite` el principio `KSdn`, equivalente a `KSneg`, y de ahí WKS). Aquí, sin
ningún import, lo que hace falta para leer esa medida:

* §1 · COTAS SUPERIORES: WKS (y `KSneg`) se siguen de WLEM y de KS, dos principios INCOMPARABLES
  (`wlem_implies_ksneg`, `ks_implies_ksneg`, `em_implies_ks`). `KSneg` es exactamente KS para las
  proposiciones ¬¬‑ESTABLES (`ksneg_iff_ksst`), y WKS es «KS salvo doble negación» (`wks_iff_nn`).
* §2 · EL COLAPSO: bajo WKS, `WLEM ⟺ LLPOp ⟺ WLPOp` (`wks_llpop_implies_wlem`, nuevo: la carrera entre
  las dos sucesiones; `wlem_implies_llpop`, `wlem_implies_wlpop`). ⇒ que LS↓ implicase LLPO sería lo
  mismo que implicase WLEM.
* §3 · POR QUÉ NO SE PUEDE SUBIR A KS / BKS⁻: con Markov, BKS⁻ da DNE (Moschovakis 1980) y KS con LPO da
  EM; y las formas `p` (decidibles en `Prop`) implican las de `Bool`, así que refutar la de `Bool` refuta
  la `p`.

📏 Footprint (medido el 2026‑10‑29, Lean v4.35.0, sin imports): ningún teorema lleva `Classical.choice`;
la mayoría, NINGÚN axioma; los que usan `omega` (`wlem_implies_llpop`, `mix_even`, `mix_odd`,
`wks_llpop_implies_wlem`, `wks_collapse`), `[propext, Quot.sound]`. Los controles (`example` y `*_classical`)
instancian las hipótesis con `Classical.em`: comprueban que no son vacías, y SÍ llevan elección.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FOL.T71Sem.B2

-- ── §0 · Los principios, en la forma literal del contexto ──────────────────
def EM : Prop := ∀ P : Prop, Or P (Not P)
def DNE : Prop := ∀ P : Prop, Not (Not P) → P
def WLEM : Prop := ∀ P : Prop, Or (Not P) (Not (Not P))
def MP : Prop := ∀ α : Nat → Bool, Not (Not (∃ n, α n = true)) → ∃ n, α n = true
def LPO : Prop := ∀ α : Nat → Bool, Or (∃ n, α n = true) (∀ n, α n = false)
def WLPO : Prop := ∀ α : Nat → Bool, Or (∀ n, α n = false) (Not (∀ n, α n = false))
def LLPO : Prop := ∀ α : Nat → Bool, (∀ m n, α m = true → α n = true → m = n) →
    Or (∀ n, α (2 * n) = false) (∀ n, α (2 * n + 1) = false)

def WLPOp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Or (∀ n, Not (β n)) (Not (∀ n, Not (β n)))

/-- LLPO para sucesiones decidibles en `Prop` (la forma que sale sin elección). -/
def LLPOp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → (∀ m n, β m → β n → m = n) →
    Or (∀ n, Not (β (2 * n))) (∀ n, Not (β (2 * n + 1)))

def MPp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Not (Not (∃ n, β n)) → ∃ n, β n

def LPOp : Prop :=
  ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) → Or (∃ n, β n) (∀ n, Not (β n))

def WKS : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not P) (∀ n, Not (β n)))

def KS : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff P (∃ n, β n))

/-- KS para las proposiciones NEGADAS (la de `a2`, que equivale a su `KSdn`). -/
def KSneg : Prop :=
  ∀ R : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff (Not R) (∃ n, β n))

/-- KS para las proposiciones ¬¬‑ESTABLES. -/
def KSst : Prop :=
  ∀ P : Prop, (Not (Not P) → P) →
    ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n))) (Iff P (∃ n, β n))

/-- BKS⁻ de van Atten (2018) = el KS de Dragalin: WKS MÁS la cláusula positiva `∃n β n → P`.
(El KS⁻ de Dragalin es sólo el bicondicional: nuestro WKS.) -/
def BKSm : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop,
    And (∀ n, Or (β n) (Not (β n))) (And (Iff (Not P) (∀ n, Not (β n))) ((∃ n, β n) → P))

-- ── §1 · Cotas superiores de WKS: WLEM y KS (incomparables) ────────────────
theorem em_implies_wlem : EM → WLEM := fun h P => h (Not P)

theorem em_implies_ks : EM → KS := by
  intro h P
  cases h P with
  | inl hP => exact ⟨fun _ => True, fun _ => Or.inl trivial, fun _ => ⟨0, trivial⟩, fun _ => hP⟩
  | inr hnP => exact ⟨fun _ => False, fun _ => Or.inr id, fun hP => absurd hP hnP,
      fun ⟨_, h⟩ => h.elim⟩

theorem ks_implies_bksm : KS → BKSm := by
  intro h P
  obtain ⟨β, hd, hiff⟩ := h P
  refine ⟨β, hd, ⟨fun hnP n hn => hnP (hiff.mpr ⟨n, hn⟩), fun hall hP => ?_⟩, hiff.mpr⟩
  obtain ⟨n, hn⟩ := hiff.mp hP
  exact hall n hn

theorem bksm_implies_wks : BKSm → WKS := fun h P =>
  match h P with
  | ⟨β, hd, hiff, _⟩ => ⟨β, hd, hiff⟩

theorem ks_implies_ksneg : KS → KSneg := fun h R => h (Not R)

/-- Con WLEM, `¬R` está DECIDIDA, y una proposición decidida es Σ⁰₁ (constante). -/
theorem wlem_implies_ksneg : WLEM → KSneg := by
  intro h R
  cases h R with
  | inl hnR => exact ⟨fun _ => True, fun _ => Or.inl trivial, fun _ => ⟨0, trivial⟩, fun _ => hnR⟩
  | inr hnnR => exact ⟨fun _ => False, fun _ => Or.inr id, fun hnR => absurd hnR hnnR,
      fun ⟨_, h⟩ => h.elim⟩

theorem ksneg_implies_wks : KSneg → WKS := by
  intro h P
  obtain ⟨β, hd, hiff⟩ := h (Not P)
  refine ⟨β, hd, fun hnP n hn => hiff.mpr ⟨n, hn⟩ hnP, fun hall hP => ?_⟩
  obtain ⟨n, hn⟩ := hiff.mp (fun hnP => hnP hP)
  exact hall n hn

theorem wlem_implies_wks : WLEM → WKS := fun h => ksneg_implies_wks (wlem_implies_ksneg h)

/-- `KSneg` es KS restringido a las proposiciones ¬¬‑estables. -/
theorem ksneg_iff_ksst : Iff KSneg KSst := by
  constructor
  · intro h P hst
    obtain ⟨β, hd, hiff⟩ := h (Not P)
    exact ⟨β, hd, fun hP => hiff.mp (fun hnP => hnP hP), fun hex => hst (hiff.mpr hex)⟩
  · intro h R
    exact h (Not R) (fun hnn hR => hnn (fun hnR => hnR hR))

/-- WKS es KS «salvo doble negación»: `¬¬P ↔ ¬¬∃n β n`. -/
theorem wks_iff_nn : Iff WKS (∀ P : Prop, ∃ β : Nat → Prop,
    And (∀ n, Or (β n) (Not (β n))) (Iff (Not (Not P)) (Not (Not (∃ n, β n))))) := by
  constructor
  · intro h P
    obtain ⟨β, hd, hiff⟩ := h P
    refine ⟨β, hd, fun hnn hno => ?_, fun hnn hnP => ?_⟩
    · exact hnn (hiff.mpr (fun n hn => hno ⟨n, hn⟩))
    · exact hnn (fun ⟨n, hn⟩ => hiff.mp hnP n hn)
  · intro h P
    obtain ⟨β, hd, hiff⟩ := h P
    refine ⟨β, hd, fun hnP n hn => hiff.mpr (fun hno => hno ⟨n, hn⟩) hnP, ?_⟩
    intro hall hP
    exact hiff.mp (fun hnP => hnP hP) (fun ⟨n, hn⟩ => hall n hn)

-- ── §2 · El colapso bajo WKS: WLEM ⟺ LLPOp ⟺ WLPOp ────────────────────────
theorem wlem_implies_wlpop : WLEM → WLPOp := by
  intro h β _
  cases h (∀ n, Not (β n)) with
  | inl hn => exact Or.inr hn
  | inr hnn => exact Or.inl (fun n hb => hnn (fun hall => hall n hb))

theorem wlem_implies_llpop : WLEM → LLPOp := by
  intro h β _ huniq
  cases h (∃ n, β (2 * n)) with
  | inl hno => exact Or.inl (fun n hb => hno ⟨n, hb⟩)
  | inr hnn =>
    refine Or.inr (fun m hb => hnn (fun ⟨n, hn⟩ => ?_))
    have h2 := huniq (2 * n) (2 * m + 1) hn hb
    omega

theorem wks_wlpop_implies_wlem : WKS → WLPOp → WLEM := by
  intro hW hL P
  obtain ⟨β, hd, hiff⟩ := hW P
  cases hL β hd with
  | inl hall => exact Or.inl (hiff.mpr hall)
  | inr hn => exact Or.inr (fun hnP => hn (hiff.mp hnP))

/-- El cuantificador ACOTADO de una sucesión decidible es decidible. -/
theorem bdec {δ : Nat → Prop} (hd : ∀ n, Or (δ n) (Not (δ n))) :
    ∀ k, Or (∃ j, And (j < k) (δ j)) (∀ j, j < k → Not (δ j))
  | 0 => Or.inr (fun j hj => absurd hj (Nat.not_lt_zero j))
  | k + 1 =>
    match bdec hd k with
    | Or.inl ⟨j, hj, hδ⟩ => Or.inl ⟨j, Nat.lt_succ_of_lt hj, hδ⟩
    | Or.inr hall =>
      match hd k with
      | Or.inl hk => Or.inl ⟨k, Nat.lt_succ_self k, hk⟩
      | Or.inr hnk => Or.inr (fun j hj hδj =>
          match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
          | Or.inl hlt => hall j hlt hδj
          | Or.inr heq => hnk (heq ▸ hδj))

/-- El MENOR testigo de una sucesión decidible (por inducción sobre una cota). -/
theorem least {δ : Nat → Prop} (hd : ∀ n, Or (δ n) (Not (δ n))) :
    ∀ N k, k ≤ N → δ k → ∃ m, And (δ m) (∀ j, j < m → Not (δ j))
  | 0, k, hk, hδ => ⟨k, hδ, fun j hj => absurd (Nat.lt_of_lt_of_le hj hk) (Nat.not_lt_zero j)⟩
  | N + 1, k, hk, hδ =>
    match bdec hd k with
    | Or.inl ⟨j, hj, hδj⟩ => least hd N j (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hj hk)) hδj
    | Or.inr hall => ⟨k, hδ, hall⟩

/-- Las dos sucesiones ENTRELAZADAS: `β` en los pares, `γ` en los impares. -/
def mix (β γ : Nat → Prop) (k : Nat) : Prop := if k % 2 = 0 then β (k / 2) else γ (k / 2)

theorem mix_even (β γ : Nat → Prop) (n : Nat) : Iff (mix β γ (2 * n)) (β n) := by
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  unfold mix
  rw [ite_eq_left h1, h2]

theorem mix_odd (β γ : Nat → Prop) (n : Nat) : Iff (mix β γ (2 * n + 1)) (γ n) := by
  have h1 : Not ((2 * n + 1) % 2 = 0) := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  unfold mix
  rw [ite_eq_right h1, h2]

theorem mix_dec {β γ : Nat → Prop} (hb : ∀ n, Or (β n) (Not (β n)))
    (hg : ∀ n, Or (γ n) (Not (γ n))) : ∀ k, Or (mix β γ k) (Not (mix β γ k)) := by
  intro k
  unfold mix
  split
  · exact hb _
  · exact hg _

/-- «`k` es la PRIMERA posición verdadera». -/
def first (δ : Nat → Prop) (k : Nat) : Prop := And (δ k) (∀ j, j < k → Not (δ j))

theorem first_dec {δ : Nat → Prop} (hd : ∀ n, Or (δ n) (Not (δ n))) :
    ∀ k, Or (first δ k) (Not (first δ k)) := fun k =>
  match hd k, bdec hd k with
  | Or.inr hn, _ => Or.inr (fun h => hn h.1)
  | Or.inl _, Or.inl ⟨j, hj, hδj⟩ => Or.inr (fun h => h.2 j hj hδj)
  | Or.inl hk, Or.inr hall => Or.inl ⟨hk, hall⟩

theorem first_uniq {δ : Nat → Prop} : ∀ m n, first δ m → first δ n → m = n := by
  intro m n hm hn
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd hm.1 (hn.2 m h)
  · exact h
  · exact absurd hn.1 (hm.2 n h)

/-- ⭐ WKS + LLPOp ⟹ WLEM. Con WKS en `P` y en `¬P`: `β n → ¬¬P` y `γ n → ¬P`, así que las dos
sucesiones no pueden tener ambas un `true`. Se entrelazan, se queda la PRIMERA posición verdadera
(a lo sumo una), y LLPOp dice en qué paridad NO está: si no está en los pares, `∀n ¬β n`, es decir
`¬P`; si no está en los impares, `∀n ¬γ n`, es decir `¬¬P`. -/
theorem wks_llpop_implies_wlem : WKS → LLPOp → WLEM := by
  intro hW hL P
  obtain ⟨β, hb, hβ⟩ := hW P
  obtain ⟨γ, hg, hγ⟩ := hW (Not P)
  have hβnn : ∀ n, β n → Not (Not P) := fun n hn hnP => hβ.mp hnP n hn
  have hγn : ∀ n, γ n → Not P := fun n hn hP => hγ.mp (fun hnP => hnP hP) n hn
  have hd := mix_dec hb hg
  cases hL (first (mix β γ)) (first_dec hd) first_uniq with
  | inl hEven =>
    refine Or.inl (hβ.mpr (fun n hn => ?_))
    obtain ⟨m, hm, hmin⟩ :=
      least hd (2 * n) (2 * n) (Nat.le_refl _) ((mix_even β γ n).mpr hn)
    have hpar : Or (m % 2 = 0) (m % 2 = 1) := by omega
    cases hpar with
    | inl h0 =>
      have hm' : m = 2 * (m / 2) := by omega
      have hf : first (mix β γ) (2 * (m / 2)) := by rw [← hm']; exact ⟨hm, hmin⟩
      exact hEven (m / 2) hf
    | inr h1 =>
      have hm' : m = 2 * (m / 2) + 1 := by omega
      have hmx : mix β γ (2 * (m / 2) + 1) := by rw [← hm']; exact hm
      exact hβnn n hn (hγn (m / 2) ((mix_odd β γ (m / 2)).mp hmx))
  | inr hOdd =>
    refine Or.inr (hγ.mpr (fun n hn => ?_))
    obtain ⟨m, hm, hmin⟩ :=
      least hd (2 * n + 1) (2 * n + 1) (Nat.le_refl _) ((mix_odd β γ n).mpr hn)
    have hpar : Or (m % 2 = 0) (m % 2 = 1) := by omega
    cases hpar with
    | inl h0 =>
      have hm' : m = 2 * (m / 2) := by omega
      have hmx : mix β γ (2 * (m / 2)) := by rw [← hm']; exact hm
      exact hβnn (m / 2) ((mix_even β γ (m / 2)).mp hmx) (hγn n hn)
    | inr h1 =>
      have hm' : m = 2 * (m / 2) + 1 := by omega
      have hf : first (mix β γ) (2 * (m / 2) + 1) := by rw [← hm']; exact ⟨hm, hmin⟩
      exact hOdd (m / 2) hf

/-- 🏁 Bajo WKS, LLPOp, WLPOp y WLEM son el MISMO principio. -/
theorem wks_collapse (hW : WKS) : And (Iff WLEM LLPOp) (Iff WLEM WLPOp) :=
  ⟨⟨wlem_implies_llpop, wks_llpop_implies_wlem hW⟩,
   ⟨wlem_implies_wlpop, wks_wlpop_implies_wlem hW⟩⟩

-- ── §3 · Por qué no se sube a BKS⁻ / KS, y de `p` a `Bool` ─────────────────
/-- Moschovakis (1980), forma `p`: BKS⁻ + Markov ⟹ DNE. -/
theorem bksm_mpp_implies_dne : BKSm → MPp → DNE := by
  intro hB hM P hnn
  obtain ⟨β, hd, hiff, hpos⟩ := hB P
  exact hpos (hM β hd (fun hno => hnn (hiff.mpr (fun n hn => hno ⟨n, hn⟩))))

theorem ks_lpop_implies_em : KS → LPOp → EM := by
  intro hK hL P
  obtain ⟨β, hd, hiff⟩ := hK P
  cases hL β hd with
  | inl hex => exact Or.inl (hiff.mpr hex)
  | inr hall => exact Or.inr (fun hP => match hiff.mp hP with | ⟨n, hn⟩ => hall n hn)

theorem bool_dec (b : Bool) : Or (b = true) (Not (b = true)) :=
  match b with
  | true => Or.inl rfl
  | false => Or.inr (fun h => Bool.noConfusion h)

theorem bool_false_of_not_true {b : Bool} (h : Not (b = true)) : b = false :=
  match b, h with
  | true, h => absurd rfl h
  | false, _ => rfl

theorem llpop_implies_llpo : LLPOp → LLPO := by
  intro h α huniq
  cases h (fun n => α n = true) (fun n => bool_dec (α n)) huniq with
  | inl hE => exact Or.inl (fun n => bool_false_of_not_true (hE n))
  | inr hO => exact Or.inr (fun n => bool_false_of_not_true (hO n))

theorem wlpop_implies_wlpo : WLPOp → WLPO := by
  intro h α
  cases h (fun n => α n = true) (fun n => bool_dec (α n)) with
  | inl hall => exact Or.inl (fun n => bool_false_of_not_true (hall n))
  | inr hn => exact Or.inr (fun hall => hn (fun n hn' => Bool.noConfusion ((hall n).symm.trans hn')))

theorem mpp_implies_mp : MPp → MP := fun h α => h (fun n => α n = true) (fun n => bool_dec (α n))

-- ── §4 · CONTROLES de no vacuidad: las hipótesis se cumplen (clásicamente) ──
theorem em_classical : EM := Classical.em
theorem wlem_classical : WLEM := em_implies_wlem em_classical
theorem mpp_classical : MPp := fun _ _ hnn => Classical.byContradiction hnn
theorem lpop_classical : LPOp := fun β _ =>
  (Classical.em (∃ n, β n)).elim Or.inl (fun h => Or.inr (fun n hn => h ⟨n, hn⟩))

example : WLEM := wks_llpop_implies_wlem (wlem_implies_wks wlem_classical) (wlem_implies_llpop wlem_classical)
example : WLEM := wks_wlpop_implies_wlem (wlem_implies_wks wlem_classical) (wlem_implies_wlpop wlem_classical)
example : DNE := bksm_mpp_implies_dne (ks_implies_bksm (em_implies_ks em_classical)) mpp_classical
example : EM := ks_lpop_implies_em (em_implies_ks em_classical) lpop_classical
example : KSst := ksneg_iff_ksst.mp (ks_implies_ksneg (em_implies_ks em_classical))
example : LLPO := llpop_implies_llpo (wlem_implies_llpop wlem_classical)
example : MP := mpp_implies_mp mpp_classical

end FOL.T71Sem.B2


#print axioms FOL.T71Sem.B2.em_implies_wlem
#print axioms FOL.T71Sem.B2.em_implies_ks
#print axioms FOL.T71Sem.B2.ks_implies_bksm
#print axioms FOL.T71Sem.B2.bksm_implies_wks
#print axioms FOL.T71Sem.B2.ks_implies_ksneg
#print axioms FOL.T71Sem.B2.wlem_implies_ksneg
#print axioms FOL.T71Sem.B2.ksneg_implies_wks
#print axioms FOL.T71Sem.B2.wlem_implies_wks
#print axioms FOL.T71Sem.B2.ksneg_iff_ksst
#print axioms FOL.T71Sem.B2.wks_iff_nn
#print axioms FOL.T71Sem.B2.wlem_implies_wlpop
#print axioms FOL.T71Sem.B2.wlem_implies_llpop
#print axioms FOL.T71Sem.B2.wks_wlpop_implies_wlem
#print axioms FOL.T71Sem.B2.bdec
#print axioms FOL.T71Sem.B2.least
#print axioms FOL.T71Sem.B2.mix_even
#print axioms FOL.T71Sem.B2.mix_odd
#print axioms FOL.T71Sem.B2.mix_dec
#print axioms FOL.T71Sem.B2.first_dec
#print axioms FOL.T71Sem.B2.first_uniq
#print axioms FOL.T71Sem.B2.wks_llpop_implies_wlem
#print axioms FOL.T71Sem.B2.wks_collapse
#print axioms FOL.T71Sem.B2.bksm_mpp_implies_dne
#print axioms FOL.T71Sem.B2.ks_lpop_implies_em
#print axioms FOL.T71Sem.B2.llpop_implies_llpo
#print axioms FOL.T71Sem.B2.wlpop_implies_wlpo
#print axioms FOL.T71Sem.B2.mpp_implies_mp
#print axioms FOL.T71Sem.B2.wlem_classical
#print axioms FOL.T71Sem.B2.mpp_classical
