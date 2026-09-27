/-
E3 · (b) ¿Es ESENCIAL el tercio excluso de max_cons_contains / max_cons_complete /
max_cons_impl_iff / max_cons_or para sus ENUNCIADOS (con `S` arbitrario)?
  Parte 1: cada ENUNCIADO, tomado como hipótesis, implica ¬¬P → P para todo P : Prop.
           Testigo: S_P := {x | Mtrue ⊨ x} ∩ {x | x = f₀ → P}, que es maximal consistente si ¬¬P.
           (La consistencia de Th(Mtrue) se prueba SIN choice con `sound_stable`, copiado de E2.)
  Parte 2: con `[DecidablePred S]` las cinco versiones salen SIN choice (y sin MP).
-/
import FOL.Canonical0
import FOL.DecEq

namespace Exp

open FOL.Metamath.Semantics

theorem sound_stable {D : Type} (M : Model D)
    (hstab : ∀ (v : Nat → D) (f : Formula), Not (Not (evalFormula M v f)) → evalFormula M v f)
    {Γ : List Formula} {f : Formula} (h : Γ ⊢₀ f) :
    ∀ v, contextSatisfies M v Γ → evalFormula M v f := by
  induction h with
  | hyp Γ' f' hIn => intro v hΓ; exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro v hΓ hA
    apply ih v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A => intro v hΓ; exact (ih_impl v hΓ) (ih_A v hΓ)
  | intro_and Γ' A B _ _ ihA ihB => intro v hΓ; exact ⟨ihA v hΓ, ihB v hΓ⟩
  | elim_and_l Γ' A B _ ih => intro v hΓ; exact (ih v hΓ).left
  | elim_and_r Γ' A B _ ih => intro v hΓ; exact (ih v hΓ).right
  | intro_or_l Γ' A B _ ih => intro v hΓ; exact Or.inl (ih v hΓ)
  | intro_or_r Γ' A B _ ih => intro v hΓ; exact Or.inr (ih v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro v hΓ
    cases ih_or v hΓ with
    | inl hA =>
      apply ih_A v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | intro_forall Γ' A _ ih =>
    intro v hΓ d
    exact ih (shiftEnv v d) ((contextSatisfies_lift_zero M v d).mpr hΓ)
  | elim_forall Γ' A t _ ih =>
    intro v hΓ
    exact (eval_substFormula_zero M v t A).mpr (ih v hΓ (evalTerm M v t))
  | intro_ex Γ' A t _ ih =>
    intro v hΓ
    exact ⟨evalTerm M v t, (eval_substFormula_zero M v t A).mp (ih v hΓ)⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro v hΓ
    obtain ⟨d, hd⟩ := ih_ex v hΓ
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    exact (eval_liftFormula_zero M v d B).mp (ih_B (shiftEnv v d) hCtx)
  | bot_elim Γ' A _ ih => intro v hΓ; exact (ih v hΓ).elim
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro v hΓ
    exact ih v (fun g hg => hΓ g (hSubset g hg))
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro v hΓ
    have hEquiv := replaceAt_soundness M v h_get (fun v' => rule_soundness M h_rule v')
    rw [h_replace]
    exact hEquiv.mp (ih v hΓ)
  -- ⭐ los tres casos clásicos: ESTABILIDAD en vez de Classical.byContradiction
  | dne_rule Γ' A _ ih => intro v hΓ; exact hstab v A (ih v hΓ)
  | dne_schema Γ' A => intro v _ hnn; exact hstab v A hnn
  | forall_not_ex_not Γ' A =>
    intro v _ hnf
    apply hstab v (Formula.ex (neg A))
    intro hne
    apply hnf
    intro d
    apply hstab (shiftEnv v d) A
    intro hnd
    exact hne ⟨d, hnd⟩
  | refl Γ' t => intro v _; rfl
  | subst Γ' t1 t2 f' _ _ ih_eq ih_f =>
    intro v hΓ
    have heq : evalTerm M v t1 = evalTerm M v t2 := ih_eq v hΓ
    have h1 := (eval_substFormula_zero M v t1 f').mp (ih_f v hΓ)
    rw [heq] at h1
    exact (eval_substFormula_zero M v t2 f').mpr h1

/-- Estable ⇐ decidible. -/
theorem stable_of_dec {D : Type} (M : Model D)
    (hdec : ∀ (v : Nat → D) (f : Formula), Decidable (evalFormula M v f)) :
    ∀ (v : Nat → D) (f : Formula), Not (Not (evalFormula M v f)) → evalFormula M v f :=
  fun v f hnn => match hdec v f with
    | isTrue h => h
    | isFalse h => absurd h hnn


open FOL.Henkin0 (DerivesSet₀ IsConsistent₀ neg_impl_left neg_impl_right)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ IsHenkin derivesSet0_hyp derivesSet0_weakening
  derivesSet0_elim_impl)
open FOL.Canonical0 (IsMemComplete derivesSet0_map derivesSet0_map2)
open FOL.Metamath.Soundness0 (Mtrue)

-- ═══ Parte 1 ═══════════════════════════════════════════════════════════════
def decTrue : (v : Nat → Unit) → (f : Formula) → Decidable (evalFormula Mtrue v f)
  | _, .bottom => isFalse (fun h => h)
  | _, .atom _ _ => isTrue trivial
  | _, .eq _ _ => isTrue rfl
  | v, .impl a b =>
    match decTrue v a, decTrue v b with
    | _, isTrue hb => isTrue (fun _ => hb)
    | isFalse ha, _ => isTrue (fun h => absurd h ha)
    | isTrue ha, isFalse hb => isFalse (fun h => hb (h ha))
  | v, .forall a =>
    match decTrue (shiftEnv v ()) a with
    | isTrue h => isTrue (fun _ => h)
    | isFalse h => isFalse (fun hall => h (hall ()))
  | v, .and a b =>
    match decTrue v a, decTrue v b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun h => ha h.1)
    | _, isFalse hb => isFalse (fun h => hb h.2)
  | v, .or a b =>
    match decTrue v a, decTrue v b with
    | isTrue ha, _ => isTrue (Or.inl ha)
    | _, isTrue hb => isTrue (Or.inr hb)
    | isFalse ha, isFalse hb => isFalse (fun h => h.elim ha hb)
  | v, .ex a =>
    match decTrue (shiftEnv v ()) a with
    | isTrue h => isTrue ⟨(), h⟩
    | isFalse h => isFalse (fun ⟨_, hd⟩ => h hd)

/-- La teoría del modelo de un punto con todo verdadero. -/
def T : Formula → Prop := fun x => evalFormula Mtrue (fun _ => ()) x

theorem T_consistent : IsConsistent₀ T := by
  intro ⟨Γ, hΓ, hD⟩
  exact sound_stable Mtrue (stable_of_dec Mtrue decTrue) hD (fun _ => ()) hΓ

def SP (f₀ : Formula) (P : Prop) : Formula → Prop := fun x => And (T x) (x = f₀ → P)

theorem SP_max {f₀ : Formula} {P : Prop} (hf₀ : T f₀) (hneg : ∀ g, Not (neg g = f₀))
    (hnn : Not (Not P)) : IsMaximalConsistent₀ (SP f₀ P) := by
  refine ⟨fun hbot => T_consistent (derivesSet0_weakening hbot (fun x hx => hx.1)), ?_⟩
  intro g hng hcons
  by_cases hg : g = f₀
  · subst hg
    exact hnn (fun hP => hng ⟨hf₀, fun _ => hP⟩)
  · have hTg : Not (T g) := fun hT => hng ⟨hT, fun h => absurd h hg⟩
    have hTng : SP f₀ P (neg g) := ⟨fun hx => hTg hx, fun h => absurd h (hneg g)⟩
    apply hcons
    refine ⟨[neg g, g], ?_, ?_⟩
    · intro x hx
      cases hx with
      | head => exact Or.inl hTng
      | tail _ hx' =>
        cases hx' with
        | head => exact Or.inr rfl
        | tail _ hx'' => exact absurd hx'' List.not_mem_nil
    · exact Derives₀.elim_impl _ g Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _))
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

def f0 : Formula := Formula.eq (Term.var 0) (Term.var 0)
def fI : Formula := Formula.impl f0 f0
def fO : Formula := Formula.or f0 f0

theorem f0_T : T f0 := rfl
theorem fI_T : T fI := fun h => h
theorem fO_T : T fO := Or.inl rfl
theorem f0_notneg : ∀ g, Not (neg g = f0) := fun _ h => by cases h
theorem fI_notneg : ∀ g, Not (neg g = fI) := fun _ h => by cases h
theorem fO_notneg : ∀ g, Not (neg g = fO) := fun _ h => by cases h

theorem contains_stmt_implies_dne
    (hmc : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {f : Formula}, DerivesSet₀ S f → S f) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := f0) (P := P) f0_T f0_notneg hnn
  have h := hmc hMax (f := f0) ⟨[], fun _ h => absurd h List.not_mem_nil, Derives₀.refl [] (Term.var 0)⟩
  exact h.2 rfl

theorem complete_stmt_implies_dne
    (hmc : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → IsMemComplete S) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := f0) (P := P) f0_T f0_notneg hnn
  cases hmc hMax f0 with
  | inl h => exact h.2 rfl
  | inr h => exact absurd f0_T h.1

theorem impl_iff_stmt_implies_dne
    (hmi : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {A B : Formula},
      S (Formula.impl A B) ↔ (S A → S B)) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := fI) (P := P) fI_T fI_notneg hnn
  have hf0 : SP fI P f0 := ⟨f0_T, fun h => by cases h⟩
  exact ((hmi hMax (A := f0) (B := f0)).mpr (fun _ => hf0)).2 rfl

theorem or_stmt_implies_dne
    (hmo : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {A B : Formula},
      S (Formula.or A B) ↔ Or (S A) (S B)) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have hMax := SP_max (f₀ := fO) (P := P) fO_T fO_notneg hnn
  have hf0 : SP fO P f0 := ⟨f0_T, fun h => by cases h⟩
  exact ((hmo hMax (A := f0) (B := f0)).mpr (Or.inl hf0)).2 rfl

-- controles: los teoremas reales cumplen las hipótesis
example : ∀ P : Prop, Not (Not P) → P :=
  contains_stmt_implies_dne (fun hMax _ h => FOL.Lindenbaum0.max_cons_contains hMax h)
example : ∀ P : Prop, Not (Not P) → P :=
  complete_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_complete hMax)
example : ∀ P : Prop, Not (Not P) → P :=
  impl_iff_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_impl_iff hMax)
example : ∀ P : Prop, Not (Not P) → P :=
  or_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_or hMax)

-- ═══ Parte 2 · con S DECIDIBLE ═════════════════════════════════════════════
/-- `derivesSet0_intro_impl` con el `DecidableEq Formula` real (FOL.DecEq), no `propDecidable`. -/
theorem intro_impl' {S : Formula → Prop} {A B : Formula}
    (h : DerivesSet₀ (fun x => Or (S x) (x = A)) B) : DerivesSet₀ S (Formula.impl A B) := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ.filter (fun y => decide (Not (y = A))), ?_, ?_⟩
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have hne := of_decide_eq_true h1.2
    cases hΓ g h1.1 with
    | inl hS => exact hS
    | inr hEq => exact absurd hEq hne
  · refine Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD ?_)
    intro x hx
    by_cases heq : x = A
    · subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)

section Dec
variable {S : Formula → Prop} [DecidablePred S]

theorem contains' (hMax : IsMaximalConsistent₀ S) {f : Formula} (h : DerivesSet₀ S f) : S f :=
  if hs : S f then hs else
    absurd (fun hInc => hMax.1 (derivesSet0_elim_impl (intro_impl' hInc) h)) (hMax.2 f hs)

theorem impl_iff' (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.impl A B) ↔ (S A → S B) := by
  refine ⟨fun hI hA => contains' hMax (derivesSet0_elim_impl (derivesSet0_hyp hI) (derivesSet0_hyp hA)),
    fun hFn => ?_⟩
  by_cases hI : S (Formula.impl A B)
  · exact hI
  · exfalso
    apply hMax.2 _ hI
    intro hInc
    have hN : DerivesSet₀ S (neg (Formula.impl A B)) := intro_impl' hInc
    have hA : S A := contains' hMax (derivesSet0_map (fun _ hd => neg_impl_left hd) hN)
    have hnB : DerivesSet₀ S (neg B) := derivesSet0_map (fun _ hd => neg_impl_right hd) hN
    exact hMax.1 (derivesSet0_elim_impl hnB (derivesSet0_hyp (hFn hA)))

theorem complete' (hMax : IsMaximalConsistent₀ S) : IsMemComplete S := fun f =>
  if hs : S f then Or.inl hs else Or.inr ((impl_iff' hMax).mpr (fun h => absurd h hs))

theorem or' (hMax : IsMaximalConsistent₀ S) {A B : Formula} :
    S (Formula.or A B) ↔ Or (S A) (S B) := by
  constructor
  · intro hOr
    by_cases hA : S A
    · exact Or.inl hA
    by_cases hB : S B
    · exact Or.inr hB
    exfalso
    apply hMax.2 A hA; intro hIA
    apply hMax.2 B hB; intro hIB
    have hnA := intro_impl' hIA
    have hnB := intro_impl' hIB
    refine hMax.1 (derivesSet0_map2 (fun Γ hd hn => ?_) (derivesSet0_hyp hOr)
      (derivesSet0_map2 (fun Γ h1 h2 => Derives₀.intro_and Γ (neg A) (neg B) h1 h2) hnA hnB))
    refine Derives₀.elim_or Γ A B Formula.bottom hd ?_ ?_
    · refine Derives₀.elim_impl _ A Formula.bottom ?_ (Derives₀.hyp _ _ (List.Mem.head _))
      exact Derives₀.elim_and_l _ (neg A) (neg B)
        (Derives₀.weakening _ _ _ hn (fun x hx => List.Mem.tail _ hx))
    · refine Derives₀.elim_impl _ B Formula.bottom ?_ (Derives₀.hyp _ _ (List.Mem.head _))
      exact Derives₀.elim_and_r _ (neg A) (neg B)
        (Derives₀.weakening _ _ _ hn (fun x hx => List.Mem.tail _ hx))
  · intro hOr
    cases hOr with
    | inl hA =>
      exact contains' hMax
        (derivesSet0_map (fun Γ hd => Derives₀.intro_or_l Γ A B hd) (derivesSet0_hyp hA))
    | inr hB =>
      exact contains' hMax
        (derivesSet0_map (fun Γ hd => Derives₀.intro_or_r Γ A B hd) (derivesSet0_hyp hB))

theorem forall' (hMax : IsMaximalConsistent₀ S) (hHenkin : IsHenkin S) {A : Formula} :
    S (Formula.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    refine contains' hMax ⟨[Formula.forall A], ?_, ?_⟩
    · intro g hg
      cases hg with
      | head => exact hAll
      | tail _ hT => exact absurd hT List.not_mem_nil
    · exact Derives₀.elim_forall _ A t (Derives₀.hyp _ _ (List.Mem.head _))
  · intro hAll
    by_cases hS : S (Formula.forall A)
    · exact hS
    exfalso
    apply hMax.2 _ hS; intro hInc
    have hNegForall := intro_impl' hInc
    have hExNeg : DerivesSet₀ S (Formula.ex (neg A)) :=
      derivesSet0_map (fun Γ hd =>
        Derives₀.elim_impl Γ (neg (Formula.forall A)) (Formula.ex (neg A))
          (Derives₀.forall_not_ex_not Γ A) hd) hNegForall
    obtain ⟨t, ht⟩ := hHenkin (neg A) (contains' hMax hExNeg)
    refine hMax.1 ⟨[neg (substFormula 0 t A), substFormula 0 t A], ?_, ?_⟩
    · intro g hg
      cases hg with
      | head => exact ht
      | tail _ hT =>
        cases hT with
        | head => exact hAll t
        | tail _ hT2 => exact absurd hT2 List.not_mem_nil
    · exact Derives₀.elim_impl _ (substFormula 0 t A) Formula.bottom
        (Derives₀.hyp _ _ (List.Mem.head _))
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

end Dec

end Exp

#print axioms Exp.T_consistent
#print axioms Exp.SP_max
#print axioms Exp.contains_stmt_implies_dne
#print axioms Exp.complete_stmt_implies_dne
#print axioms Exp.impl_iff_stmt_implies_dne
#print axioms Exp.or_stmt_implies_dne
#print axioms Exp.intro_impl'
#print axioms Exp.contains'
#print axioms Exp.impl_iff'
#print axioms Exp.complete'
#print axioms Exp.or'
#print axioms Exp.forall'
