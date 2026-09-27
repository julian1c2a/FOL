import FOL.Compacity0
import FOL.Inconsistencia
import FOL.Finitary0
/-! ESCEPTICO · Esencialidad de enunciados que la auditoria clasifica como «eliminable-MEDIDO»
(quotientOut), «esencial-hipótesis» (max_cons_forall, max_cons_neg, truth_lemma₀) o «semántico
sin clasificar / probablemente constructivo» (consistency_of_satisfiable₀). Cada teorema toma el
ENUNCIADO como hipótesis y deriva un principio no constructivo; un `example` de control comprueba
que el teorema real de FOL cumple la hipótesis (la hipótesis no es vacía). -/

open FOL.Metamath.Semantics

namespace ExpE

-- ═══ (1) quotientOut / quotientOut_eq: una sección de TODO cociente ⇒ tercio excluso ═══
theorem section_implies_em
    (out : ∀ {α : Type} {s : Setoid α}, Quotient s → α)
    (hout : ∀ {α : Type} {s : Setoid α} (q : Quotient s), Quotient.mk s (out q) = q) :
    ∀ P : Prop, Or P (Not P) := by
  intro P
  let s : Setoid Bool :=
    { r := fun a b => Or (a = b) P
      iseqv :=
        { refl := fun _ => Or.inl rfl
          symm := fun h => h.elim (fun e => Or.inl e.symm) Or.inr
          trans := fun h1 h2 =>
            h1.elim (fun e1 => h2.elim (fun e2 => Or.inl (e1.trans e2)) Or.inr) Or.inr } }
  have key : out (Quotient.mk s true) = out (Quotient.mk s false) → P := by
    intro h
    have hq : Quotient.mk s true = Quotient.mk s false :=
      (hout (Quotient.mk s true)).symm.trans
        ((congrArg (Quotient.mk s) h).trans (hout (Quotient.mk s false)))
    have hr : Or (true = false) P := Quotient.exact hq
    exact hr.elim (fun e => by cases e) id
  have key2 : P → out (Quotient.mk s true) = out (Quotient.mk s false) := by
    intro hP
    have hq : Quotient.mk s true = Quotient.mk s false := Quotient.sound (Or.inr hP)
    rw [hq]
  exact match decEq (out (Quotient.mk s true)) (out (Quotient.mk s false)) with
    | isTrue e => Or.inl (key e)
    | isFalse ne => Or.inr (fun hP => ne (key2 hP))

-- ═══ (2) La teoría del modelo de un punto (copiado de E3: sin choice) ═══
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

theorem stable_of_dec {D : Type} (M : Model D)
    (hdec : ∀ (v : Nat → D) (f : Formula), Decidable (evalFormula M v f)) :
    ∀ (v : Nat → D) (f : Formula), Not (Not (evalFormula M v f)) → evalFormula M v f :=
  fun v f hnn => match hdec v f with
    | isTrue h => h
    | isFalse h => absurd h hnn

open FOL.Henkin0 (DerivesSet₀ IsConsistent₀)
open FOL.Lindenbaum0 (IsMaximalConsistent₀ IsHenkin derivesSet0_weakening)
open FOL.Metamath.Soundness0 (Mtrue)

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

def T : Formula → Prop := fun x => evalFormula Mtrue (fun _ => ()) x

theorem T_consistent : IsConsistent₀ T := by
  intro ⟨Γ, hΓ, hD⟩
  exact sound_stable Mtrue (stable_of_dec Mtrue decTrue) hD (fun _ => ()) hΓ

theorem incons_pair {S : Formula → Prop} {g : Formula} (hng : S (neg g)) :
    Not (IsConsistent₀ (fun x => Or (S x) (x = g))) := by
  intro hcons
  apply hcons
  refine ⟨[neg g, g], ?_, ?_⟩
  · intro x hx
    cases hx with
    | head => exact Or.inl hng
    | tail _ hx' =>
      cases hx' with
      | head => exact Or.inr rfl
      | tail _ hx'' => exact absurd hx'' List.not_mem_nil
  · exact Derives₀.elim_impl _ g Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _))
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

-- ═══ (3) max_cons_neg ⇒ ¬¬P → P.  Testigo: T ∩ {x | x = neg ⊥ → P} ═══
def SN (P : Prop) : Formula → Prop := fun x => And (T x) (x = neg Formula.bottom → P)

theorem SN_max {P : Prop} (hnn : Not (Not P)) : IsMaximalConsistent₀ (SN P) := by
  refine ⟨fun hbot => T_consistent (derivesSet0_weakening hbot (fun x hx => hx.1)), ?_⟩
  intro g hng
  match decTrue (fun _ => ()) g with
  | isTrue hT => exact absurd (fun hP => hng ⟨hT, fun _ => hP⟩) hnn
  | isFalse hT =>
    cases g with
    | bottom =>
      intro hcons
      exact hcons ⟨[Formula.bottom], fun x hx => by
        cases hx with
        | head => exact Or.inr rfl
        | tail _ h => exact absurd h List.not_mem_nil, Derives₀.hyp _ _ (List.Mem.head _)⟩
    | atom p ts => exact incons_pair ⟨hT, fun h => by cases h⟩
    | eq t u => exact incons_pair ⟨hT, fun h => by cases h⟩
    | impl a b => exact incons_pair ⟨hT, fun h => by cases h⟩
    | «forall» a => exact incons_pair ⟨hT, fun h => by cases h⟩
    | and a b => exact incons_pair ⟨hT, fun h => by cases h⟩
    | or a b => exact incons_pair ⟨hT, fun h => by cases h⟩
    | ex a => exact incons_pair ⟨hT, fun h => by cases h⟩

theorem neg_stmt_implies_dne
    (hmn : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → ∀ {f : Formula},
      Iff (S (neg f)) (Not (S f))) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have h := (hmn (SN_max hnn) (f := Formula.bottom)).mpr (fun hb => hb.1)
  exact h.2 rfl

-- ═══ (4) max_cons_forall y truth_lemma₀ ⇒ ¬¬P → P.  Testigo HENKIN: T ∩ {x | x ∈ cadena → P},
--       cadena = ∀¬⊥, ∃∀¬⊥, ∃∃∀¬⊥, … (fórmulas sin términos) ═══
def tl : Formula → Prop
  | .bottom => True
  | .atom _ _ => False
  | .eq _ _ => False
  | .impl a b => And (tl a) (tl b)
  | .forall a => tl a
  | .and a b => And (tl a) (tl b)
  | .or a b => And (tl a) (tl b)
  | .ex a => tl a

theorem subst_tl : ∀ (A : Formula) (k : Nat) (t : Term), tl A → substFormula k t A = A := by
  intro A
  induction A with
  | bottom => intro _ _ _; rfl
  | atom _ _ => intro _ _ h; exact h.elim
  | eq _ _ => intro _ _ h; exact h.elim
  | impl a b iha ihb =>
    intro k t h
    show FormulaG.impl (substFormula k t a) (substFormula k t b) = _
    rw [iha k t h.1, ihb k t h.2]
  | «forall» a ih =>
    intro k t h
    show FormulaG.forall (substFormula (k + 1) (liftTerm 0 t) a) = _
    rw [ih (k + 1) _ h]
  | and a b iha ihb =>
    intro k t h
    show FormulaG.and (substFormula k t a) (substFormula k t b) = _
    rw [iha k t h.1, ihb k t h.2]
  | or a b iha ihb =>
    intro k t h
    show FormulaG.or (substFormula k t a) (substFormula k t b) = _
    rw [iha k t h.1, ihb k t h.2]
  | ex a ih =>
    intro k t h
    show FormulaG.ex (substFormula (k + 1) (liftTerm 0 t) a) = _
    rw [ih (k + 1) _ h]

theorem tl_subst : ∀ (A : Formula) (k : Nat) (t : Term), tl (substFormula k t A) → tl A := by
  intro A
  induction A with
  | bottom => intro _ _ _; trivial
  | atom _ _ => intro _ _ h; exact h
  | eq _ _ => intro _ _ h; exact h
  | impl a b iha ihb => intro k t h; exact ⟨iha k t h.1, ihb k t h.2⟩
  | «forall» a ih => intro k t h; exact ih (k + 1) _ h
  | and a b iha ihb => intro k t h; exact ⟨iha k t h.1, ihb k t h.2⟩
  | or a b iha ihb => intro k t h; exact ⟨iha k t h.1, ihb k t h.2⟩
  | ex a ih => intro k t h; exact ih (k + 1) _ h

def chain : Nat → Formula
  | 0 => Formula.forall (neg Formula.bottom)
  | n + 1 => Formula.ex (chain n)

theorem chain_tl : ∀ n, tl (chain n)
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => chain_tl n

def InChain (x : Formula) : Prop := ∃ n, x = chain n

theorem not_inChain_impl {a b : Formula} : Not (InChain (Formula.impl a b)) := by
  intro ⟨n, h⟩
  cases n with
  | zero => cases h
  | succ n => cases h

def SC (P : Prop) : Formula → Prop := fun x => And (T x) (InChain x → P)

theorem SC_max {P : Prop} (hnn : Not (Not P)) : IsMaximalConsistent₀ (SC P) := by
  refine ⟨fun hbot => T_consistent (derivesSet0_weakening hbot (fun x hx => hx.1)), ?_⟩
  intro g hng
  match decTrue (fun _ => ()) g with
  | isTrue hT => exact absurd (fun hP => hng ⟨hT, fun _ => hP⟩) hnn
  | isFalse hT => exact incons_pair ⟨hT, fun h => absurd h not_inChain_impl⟩

theorem T_subst_of_ex {A : Formula} (h : T (Formula.ex A)) (t : Term) : T (substFormula 0 t A) := by
  obtain ⟨d, hd⟩ := h
  exact (eval_substFormula_zero Mtrue (fun _ => ()) t A).mpr hd

theorem SC_henkin (P : Prop) : IsHenkin (SC P) := by
  intro A hEx
  refine ⟨Term.var 0, T_subst_of_ex hEx.1 _, ?_⟩
  intro ⟨n, hn⟩
  have htl : tl A := tl_subst A 0 (Term.var 0) (hn ▸ chain_tl n)
  have hA : A = chain n := (subst_tl A 0 (Term.var 0) htl).symm.trans hn
  exact hEx.2 ⟨n + 1, by rw [hA]; rfl⟩

theorem forall_stmt_implies_dne
    (hmf : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → IsHenkin S → ∀ {A : Formula},
      Iff (S (Formula.forall A)) (∀ t, S (substFormula 0 t A))) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  have h := (hmf (SC_max hnn) (SC_henkin P) (A := neg Formula.bottom)).mpr
    (fun t => ⟨fun hb => hb, fun hc => absurd hc not_inChain_impl⟩)
  exact h.2 ⟨0, rfl⟩

/-- Versión DÉBIL del lema de la verdad (existe ALGÚN modelo que lo cumple): la implica
`truth_lemma₀` y no menciona `canonicalModel` (cuya definición lleva choice). -/
theorem truth_stmt_implies_dne
    (htl : ∀ {S : Formula → Prop}, IsMaximalConsistent₀ S → IsHenkin S →
      ∃ (D : Type) (M : Model D) (v : Nat → D), ∀ f, Iff (evalFormula M v f) (S f)) :
    ∀ P : Prop, Not (Not P) → P := by
  intro P hnn
  obtain ⟨D, M, v, hM⟩ := htl (SC_max hnn) (SC_henkin P)
  have h := (hM (chain 0)).mp (fun _ hb => hb)
  exact h.2 ⟨0, rfl⟩

-- ═══ (5) consistency_of_satisfiable₀ ⇒ ∀ P : ℕ → Prop, ¬¬∀ n, P n ∨ ¬P n (DNS para EM) ═══
def MP (P : Nat → Prop) : Model Nat :=
  ⟨fun _ _ => 0, fun _ ds => match ds with
    | [d] => P d
    | _ => True⟩

def pA : Formula := Formula.atom "p" [Term.var 0]
def FEM : Formula := Formula.forall (Formula.or pA (neg pA))

theorem der_em (A : Formula) : [] ⊢₀ Formula.or A (neg A) := by
  refine Derives₀.dne_rule _ _ (Derives₀.intro_impl _ _ _ ?_)
  have hn : [neg (Formula.or A (neg A))] ⊢₀ neg A := by
    refine Derives₀.intro_impl _ _ _ ?_
    refine Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom ?_ ?_
    · exact Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    · exact Derives₀.intro_or_l _ A (neg A) (Derives₀.hyp _ _ (List.Mem.head _))
  exact Derives₀.elim_impl _ (Formula.or A (neg A)) Formula.bottom
    (Derives₀.hyp _ _ (List.Mem.head _))
    (Derives₀.intro_or_r _ A (neg A) hn)

theorem der_FEM : [neg FEM] ⊢₀ Formula.bottom := by
  have h0 : [] ⊢₀ FEM := Derives₀.intro_forall [] _ (der_em pA)
  exact Derives₀.elim_impl _ FEM Formula.bottom (Derives₀.hyp _ _ (List.Mem.head _))
    (Derives₀.weakening [] [neg FEM] FEM h0 (fun _ hx => absurd hx List.not_mem_nil))

theorem cons_sat_stmt_implies_dns
    (hcs : ∀ {S : Formula → Prop}, FOL.Canonical0.IsSatisfiable S → IsConsistent₀ S) :
    ∀ P : Nat → Prop, Not (Not (∀ n, Or (P n) (Not (P n)))) := by
  intro P h
  refine hcs (S := fun x => x = neg FEM) ⟨Nat, MP P, fun _ => 0, fun f hf => ?_⟩
    ⟨[neg FEM], fun g hg => ?_, der_FEM⟩
  · subst hf
    intro hall
    exact h (fun n => hall n)
  · cases hg with
    | head => rfl
    | tail _ h' => exact absurd h' List.not_mem_nil

end ExpE

-- ═══ Controles: los teoremas REALES de FOL cumplen cada hipótesis ═══
example : ∀ P : Prop, Or P (Not P) :=
  ExpE.section_implies_em (fun q => FOL.Canonical0.quotientOut q)
    (fun q => FOL.Canonical0.quotientOut_eq q)
example : ∀ P : Prop, Not (Not P) → P :=
  ExpE.neg_stmt_implies_dne (fun hMax => FOL.Canonical0.max_cons_neg hMax)
example : ∀ P : Prop, Not (Not P) → P :=
  ExpE.forall_stmt_implies_dne (fun hMax hH => FOL.Canonical0.max_cons_forall hMax hH)
example : ∀ P : Prop, Not (Not P) → P :=
  ExpE.truth_stmt_implies_dne (fun {S} hMax hH =>
    ⟨_, FOL.Canonical0.canonicalModel S hMax, FOL.Canonical0.canonicalEnv S hMax,
     FOL.Canonical0.truth_lemma₀ hMax hH⟩)
example : ∀ P : Nat → Prop, Not (Not (∀ n, Or (P n) (Not (P n)))) :=
  ExpE.cons_sat_stmt_implies_dns (fun h => FOL.Compacity0.consistency_of_satisfiable₀ h)

-- ═══ Mismo enunciado de los gemelos de Disj (exp-varios/Disj.lean), comprobado por tipo ═══
theorem ExpE.derives0_not_negP_fin : Not (([] : List Formula) ⊢₀ neg (Formula.atom "P" [])) := by
  intro h
  have hc := FOL.NDtoLK0.ndToLK (FOL.Derives2.derives0_iff_derives2.mp h)
  rcases FOL.Finitary0.lkc_tval hc true
    (by intro _ hx; exact absurd hx (List.not_mem_nil)) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [FOL.Finitary0.tval, neg])
  | tail _ hm => exact absurd hm (List.not_mem_nil)

theorem ExpE.derives0_not_complete_fin :
    ∃ A : Formula, And (Not (([] : List Formula) ⊢₀ A)) (Not (([] : List Formula) ⊢₀ neg A)) :=
  ⟨_, FOL.Finitary0.derives0_not_P_fin, ExpE.derives0_not_negP_fin⟩

theorem ExpE.derives0_no_disjunction_property : Not FOL.Inconsistencia.DisjunctionProperty₀ := by
  intro hdp
  obtain ⟨A, hA, hnA⟩ := ExpE.derives0_not_complete_fin
  rcases hdp A (neg A) (FOL.Propositional0.derives0_em_ctx [] A) with h | h
  · exact hA h
  · exact hnA h

example : @ExpE.derives0_not_complete_fin = @FOL.Metamath.Soundness0.derives0_not_complete := rfl
example : @ExpE.derives0_no_disjunction_property =
  @FOL.Inconsistencia.derives0_no_disjunction_property := rfl

#print axioms ExpE.section_implies_em
#print axioms ExpE.T_consistent
#print axioms ExpE.SN_max
#print axioms ExpE.neg_stmt_implies_dne
#print axioms ExpE.SC_max
#print axioms ExpE.SC_henkin
#print axioms ExpE.forall_stmt_implies_dne
#print axioms ExpE.truth_stmt_implies_dne
#print axioms ExpE.cons_sat_stmt_implies_dns
#print axioms ExpE.derives0_not_complete_fin
#print axioms ExpE.derives0_no_disjunction_property
#print axioms FOL.Canonical0.IsSatisfiable
