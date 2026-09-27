import FOL.HenkinLimit0

/-! Combinado: (a) bndC + (b2) locInv + anexo Fresh0 (cst_ne_shift', cst_inj'). -/

namespace ExpF

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0

theorem cst_size : ∀ n : Nat, (cst n).utf8ByteSize = n + 1
  | 0 => rfl
  | n + 1 => by
      show ("a" ++ cst n).utf8ByteSize = n + 1 + 1
      rw [String.utf8ByteSize_append, cst_size n]
      show 1 + (n + 1) = n + 1 + 1
      rw [Nat.add_comm]

/-- `cst_zero_ne` contando bytes (sin `String.instOrd`). -/
theorem cst_zero_ne' (n : Nat) : cst 0 ≠ cst (n + 1) := fun h =>
  absurd ((cst_size 0).symm.trans ((congrArg String.utf8ByteSize h).trans (cst_size (n + 1))))
    (fun h' => Nat.succ_ne_zero n (Nat.succ.inj h').symm)

/-- Dos cadenas de 1 byte distintas no pueden empezar igual. -/
theorem ne_of_head {a b x y : String} (ha : a.toByteArray.size = b.toByteArray.size)
    (hab : a ≠ b) : a ++ x ≠ b ++ y := fun h => by
  have hb : a.toByteArray ++ x.toByteArray = b.toByteArray ++ y.toByteArray := by
    rw [← String.toByteArray_append, ← String.toByteArray_append, h]
  exact hab (String.toByteArray_inj.mp (ByteArray.append_inj_left hb ha))

theorem g_eq : "g" = "g" ++ "" := by decide

/-- ⭐ `cst_ne_shift` sin `not_eq_of_beq_eq_false` (sin `String.instOrd`). -/
theorem cst_ne_shift' : ∀ (n : Nat) (s : String), cst n ≠ shift s
  | 0, s => by
      show "g" ≠ "f" ++ s
      rw [g_eq]
      exact ne_of_head rfl (by decide)
  | n + 1, s => by
      show "a" ++ cst n ≠ "f" ++ s
      exact ne_of_head rfl (by decide)

mutual
theorem not_occurs_shiftTerm' (n : Nat) : ∀ t : Term,
    Not (occursTerm (cst n) (renameTerm shift t))
  | .var _ => fun h => h
  | .func s ts => fun h => by
      cases h with
      | inl he => exact cst_ne_shift' n s he.symm
      | inr ht => exact not_occurs_shiftTerms' n ts ht

theorem not_occurs_shiftTerms' (n : Nat) : ∀ ts : List Term,
    Not (occursTerms (cst n) (renameTerms shift ts))
  | [] => fun h => h
  | t :: ts => fun h => by
      cases h with
      | inl ht => exact not_occurs_shiftTerm' n t ht
      | inr hts => exact not_occurs_shiftTerms' n ts hts
end

theorem not_occurs_shiftFormula' (n : Nat) : ∀ f : Formula,
    Not (occursFormula (cst n) (renameFormula shift f)) := by
  intro f
  induction f with
  | bottom => exact fun h => h
  | atom _ ts => exact not_occurs_shiftTerms' n ts
  | eq t u => exact fun h => h.elim (not_occurs_shiftTerm' n t) (not_occurs_shiftTerm' n u)
  | impl _ _ iha ihb => exact fun h => h.elim iha ihb
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun h => h.elim iha ihb
  | or _ _ iha ihb => exact fun h => h.elim iha ihb
  | ex _ ih => exact ih

theorem shiftTheory_fresh' {S : Formula → Prop} (n : Nat) :
    ∀ g, shiftTheory S g → Not (occursFormula (cst n) g) := by
  intro g hg hocc
  obtain ⟨h, _, he⟩ := hg
  exact not_occurs_shiftFormula' n h (he ▸ hocc)

end ExpF

namespace ExpAll

open FOL.Rename
open FOL.Eigenvariable
open FOL.Henkin0
open FOL.Fresh0
open FOL.HenkinLimit0
open FOL.Metamath.Enumeration

local notation:50 S " ⊢₀* " f => DerivesSet₀ S f

-- ============================================================
-- (a) · La cota, calculada
-- ============================================================

/-- ⭐ `cst n` ocupa exactamente `n + 1` bytes. -/
theorem cst_size : ∀ n : Nat, (cst n).utf8ByteSize = n + 1
  | 0 => rfl
  | n + 1 => by
      show ("a" ++ cst n).utf8ByteSize = n + 1 + 1
      rw [String.utf8ByteSize_append, cst_size n]
      show 1 + (n + 1) = n + 1 + 1
      rw [Nat.add_comm]

/-- Una cadena de `k` bytes no es `cst m` para ningún `m ≥ k`. Sin tercio excluso, sin
`cst_inj`: sólo contar bytes. -/
theorem cst_ne_of_size {s : String} {m : Nat} (hm : s.utf8ByteSize ≤ m) : cst m ≠ s := by
  intro h
  have h1 : m + 1 = s.utf8ByteSize := (cst_size m).symm.trans (congrArg String.utf8ByteSize h)
  exact Nat.not_succ_le_self m (Nat.le_trans (Nat.le_of_eq h1) hm)

mutual
def bT : Term → Nat
  | .var _ => 0
  | .func s ts => max s.utf8ByteSize (bTs ts)

def bTs : List Term → Nat
  | [] => 0
  | t :: ts => max (bT t) (bTs ts)
end

/-- ⭐ La cota de §2 de `HenkinLimit0`, **calculada**: el mayor tamaño en bytes de un símbolo de
función de la fórmula. -/
def bndC : Formula → Nat
  | .bottom => 0
  | .atom _ ts => bTs ts
  | .eq t u => max (bT t) (bT u)
  | .impl a b => max (bndC a) (bndC b)
  | .forall a => bndC a
  | .and a b => max (bndC a) (bndC b)
  | .or a b => max (bndC a) (bndC b)
  | .ex a => bndC a

mutual
theorem bT_spec : ∀ (t : Term) (m : Nat), bT t ≤ m → Not (occursTerm (cst m) t)
  | .var _, _, _ => fun h => h
  | .func s ts, m, hm => fun h => by
      cases h with
      | inl he => exact cst_ne_of_size (Nat.le_trans (Nat.le_max_left _ _) hm) he.symm
      | inr ht => exact bTs_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) ht

theorem bTs_spec : ∀ (ts : List Term) (m : Nat), bTs ts ≤ m → Not (occursTerms (cst m) ts)
  | [], _, _ => fun h => h
  | t :: ts, m, hm => fun h => by
      cases h with
      | inl ht => exact bT_spec t m (Nat.le_trans (Nat.le_max_left _ _) hm) ht
      | inr hts => exact bTs_spec ts m (Nat.le_trans (Nat.le_max_right _ _) hm) hts
end

private theorem pair {P Q : Prop} {a b m : Nat} (h1 : a ≤ m → Not P) (h2 : b ≤ m → Not Q)
    (hm : max a b ≤ m) : Not (Or P Q) := fun h =>
  h.elim (h1 (Nat.le_trans (Nat.le_max_left _ _) hm)) (h2 (Nat.le_trans (Nat.le_max_right _ _) hm))

/-- ⭐⭐ El sustituto de `bnd_spec`, con la cota calculada. -/
theorem bndC_spec : ∀ (f : Formula) (m : Nat), bndC f ≤ m → Not (occursFormula (cst m) f) := by
  intro f
  induction f with
  | bottom => exact fun _ _ h => h
  | atom _ ts => exact bTs_spec ts
  | eq t u => exact fun m hm => pair (bT_spec t m) (bT_spec u m) hm
  | impl _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | «forall» _ ih => exact ih
  | and _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | or _ _ iha ihb => exact fun m hm => pair (iha m) (ihb m) hm
  | ex _ ih => exact ih

/-- De regalo: `cst_bound_sym` (la entrada de `Fresh0`) sin `by_cases`: la cota es el tamaño. -/
theorem cst_bound_sym' (s : String) : ∃ N, ∀ m, N ≤ m → cst m ≠ s :=
  ⟨s.utf8ByteSize, fun _ hm => cst_ne_of_size hm⟩

/-- Y `cst_inj` sin `cst_zero_ne` (sin `String.instOrd`): contar bytes. -/
theorem cst_inj' (m n : Nat) (h : cst m = cst n) : m = n :=
  Nat.succ.inj ((cst_size m).symm.trans ((congrArg String.utf8ByteSize h).trans (cst_size n)))

/-- El índice del testigo, ahora **computable** (sin `noncomputable`). -/
def hidxC : Nat → Nat
  | 0 => bndC (natToFormula 0)
  | n + 1 => max (hidxC n + 1) (bndC (natToFormula (n + 1)))

-- Control de que es de verdad un programa: se evalúa.


-- ============================================================
-- (b2) · La inversa LOCAL de un renombrado inyectivo
-- ============================================================

mutual
def symsT : Term → List String
  | .var _ => []
  | .func s ts => s :: symsTs ts

def symsTs : List Term → List String
  | [] => []
  | t :: ts => symsT t ++ symsTs ts
end

def symsF : Formula → List String
  | .bottom => []
  | .atom _ ts => symsTs ts
  | .eq t u => symsT t ++ symsT u
  | .impl a b => symsF a ++ symsF b
  | .forall a => symsF a
  | .and a b => symsF a ++ symsF b
  | .or a b => symsF a ++ symsF b
  | .ex a => symsF a

def symsL : List Formula → List String
  | [] => []
  | g :: l => symsF g ++ symsL l

theorem symsL_mem : ∀ {l : List Formula} {g : Formula} {s : String},
    g ∈ l → s ∈ symsF g → s ∈ symsL l
  | _ :: _, _, _, .head _, hs => List.mem_append_left _ hs
  | _ :: _, _, _, .tail _ hg, hs => List.mem_append_right _ (symsL_mem hg hs)

/-- La inversa local: busca en la lista FINITA `L` una preimagen por `ρ`. Sólo usa la
igualdad decidible de `String`, que no depende de ningún axioma. -/
def locInv (ρ : String → String) : List String → String → String
  | [], x => x
  | t :: L, x => if ρ t = x then t else locInv ρ L x

theorem locInv_spec {ρ : String → String} (hinj : ∀ s t, ρ s = ρ t → s = t) :
    ∀ {L : List String} {s : String}, s ∈ L → locInv ρ L (ρ s) = s
  | t :: L, s, hs => by
      show (if ρ t = ρ s then t else locInv ρ L (ρ s)) = s
      by_cases h : ρ t = ρ s
      · rw [if_pos h]; exact hinj t s h
      · rw [if_neg h]
        cases hs with
        | head => exact absurd rfl h
        | tail _ hs' => exact locInv_spec hinj hs'

-- La cancelación, LOCAL: basta con que `σ ∘ ρ = id` sobre los símbolos que aparecen.
mutual
theorem rr_term {ρ σ : String → String} : ∀ t : Term,
    (∀ s, s ∈ symsT t → σ (ρ s) = s) → renameTerm σ (renameTerm ρ t) = t
  | .var _, _ => rfl
  | .func s ts, h => by
      show TermG.func (σ (ρ s)) (renameTerms σ (renameTerms ρ ts)) = TermG.func s ts
      rw [h s (List.Mem.head _), rr_terms ts (fun x hx => h x (List.Mem.tail _ hx))]

theorem rr_terms {ρ σ : String → String} : ∀ ts : List Term,
    (∀ s, s ∈ symsTs ts → σ (ρ s) = s) → renameTerms σ (renameTerms ρ ts) = ts
  | [], _ => rfl
  | t :: ts, h => by
      show renameTerm σ (renameTerm ρ t) :: renameTerms σ (renameTerms ρ ts) = t :: ts
      rw [rr_term t (fun x hx => h x (List.mem_append_left _ hx)),
        rr_terms ts (fun x hx => h x (List.mem_append_right _ hx))]
end

theorem rr_formula {ρ σ : String → String} : ∀ f : Formula,
    (∀ s, s ∈ symsF f → σ (ρ s) = s) → renameFormula σ (renameFormula ρ f) = f := by
  intro f
  induction f with
  | bottom => exact fun _ => rfl
  | atom p ts =>
      intro h
      show FormulaG.atom p (renameTerms σ (renameTerms ρ ts)) = FormulaG.atom p ts
      rw [rr_terms ts h]
  | eq t u =>
      intro h
      show FormulaG.eq (renameTerm σ (renameTerm ρ t)) (renameTerm σ (renameTerm ρ u)) = _
      rw [rr_term t (fun x hx => h x (List.mem_append_left _ hx)),
        rr_term u (fun x hx => h x (List.mem_append_right _ hx))]
  | impl a b iha ihb =>
      intro h
      show FormulaG.impl (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | «forall» a ih =>
      intro h
      show FormulaG.forall (renameFormula σ (renameFormula ρ a)) = _
      rw [ih h]
  | and a b iha ihb =>
      intro h
      show FormulaG.and (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | or a b iha ihb =>
      intro h
      show FormulaG.or (renameFormula σ (renameFormula ρ a)) (renameFormula σ (renameFormula ρ b)) = _
      rw [iha (fun x hx => h x (List.mem_append_left _ hx)),
        ihb (fun x hx => h x (List.mem_append_right _ hx))]
  | ex a ih =>
      intro h
      show FormulaG.ex (renameFormula σ (renameFormula ρ a)) = _
      rw [ih h]

theorem map_rr {ρ σ : String → String} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → renameFormula σ (renameFormula ρ g) = g) →
    (Γ.map (renameFormula ρ)).map (renameFormula σ) = Γ
  | [], _ => rfl
  | g :: Γ, h => by
      show renameFormula σ (renameFormula ρ g) :: (Γ.map (renameFormula ρ)).map (renameFormula σ)
        = g :: Γ
      rw [h g (List.Mem.head _), map_rr Γ (fun x hx => h x (List.Mem.tail _ hx))]

/-- ⭐⭐ `derives0_rename_conservative` **sin elección**: la inversa sólo tiene que valer sobre
los símbolos de `Γ` y `f`, que son finitos. -/
theorem derives0_rename_conservative' {ρ : String → String} (hinj : ∀ s t, ρ s = ρ t → s = t)
    {Γ : List Formula} {f : Formula}
    (h : (Γ.map (renameFormula ρ)) ⊢₀ renameFormula ρ f) : Γ ⊢₀ f := by
  have hc : ∀ g, g ∈ f :: Γ → renameFormula (locInv ρ (symsL (f :: Γ))) (renameFormula ρ g) = g :=
    fun g hg => rr_formula g (fun _ hs => locInv_spec hinj (symsL_mem hg hs))
  have h' := derives0_rename (locInv ρ (symsL (f :: Γ))) h
  rwa [map_rr Γ (fun g hg => hc g (List.Mem.tail _ hg)), hc f (List.Mem.head _)] at h'

/-- Las preimágenes de un contexto finito de `shiftTheory S` (eliminación de `∃` en `Prop`,
constructiva). -/
theorem shift_preimages {S : Formula → Prop} : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → shiftTheory S g) →
    ∃ Γ' : List Formula, And (∀ y, y ∈ Γ' → S y) (Γ = Γ'.map (renameFormula shift))
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | g :: Γ, h => by
      obtain ⟨y, hy, rfl⟩ := h g (List.Mem.head _)
      obtain ⟨Γ', h1, rfl⟩ := shift_preimages Γ (fun x hx => h x (List.Mem.tail _ hx))
      refine ⟨y :: Γ', fun z hz => ?_, rfl⟩
      cases hz with
      | head => exact hy
      | tail _ hz' => exact h1 z hz'

/-- ⭐⭐ `derivesSet0_shift_inv` **sin `invOf`**. -/
theorem derivesSet0_shift_inv' {S : Formula → Prop} {f : Formula}
    (h : shiftTheory S ⊢₀* renameFormula shift f) : S ⊢₀* f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  obtain ⟨Γ', hS, rfl⟩ := shift_preimages Γ hΓ
  exact ⟨Γ', hS, derives0_rename_conservative' shift_inj hD⟩

theorem shiftTheory_consistent₀' {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (shiftTheory S) := fun hbot => hCons (derivesSet0_shift_inv' hbot)

-- ============================================================
-- (a)+(b2) · La iteración ω con las dos variantes
-- ============================================================

theorem hidxC_ge : ∀ n, bndC (natToFormula n) ≤ hidxC n
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

theorem hidxC_step (n : Nat) : hidxC n < hidxC (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)

theorem hidxC_mono : ∀ {i n : Nat}, i < n → hidxC i < hidxC n
  | i, 0, h => absurd h (Nat.not_lt_zero i)
  | i, n + 1, h => by
      cases Nat.lt_or_ge i n with
      | inl hlt => exact Nat.lt_trans (hidxC_mono hlt) (hidxC_step n)
      | inr hge => exact (Nat.le_antisymm (Nat.le_of_lt_succ h) hge) ▸ hidxC_step n

theorem hidxC_ge_of_le {i n : Nat} (h : i ≤ n) : bndC (natToFormula i) ≤ hidxC n := by
  cases Nat.lt_or_ge i n with
  | inl hlt => exact Nat.le_trans (hidxC_ge i) (Nat.le_of_lt (hidxC_mono hlt))
  | inr hge => exact (Nat.le_antisymm h hge) ▸ hidxC_ge i

/-- La cadena, ya **sin `noncomputable`**. -/
def henC (S : Formula → Prop) : Nat → Formula → Prop
  | 0 => shiftTheory S
  | n + 1 => fun x => Or (henC S n x) (x = henkinAx (cst (hidxC n)) (natToFormula n))

theorem henC_mono (S : Formula → Prop) : ∀ {i n : Nat}, i ≤ n → ∀ x, henC S i x → henC S n x
  | _, 0, h, _, hx => (Nat.le_zero.mp h) ▸ hx
  | i, n + 1, h, x, hx => by
      cases Nat.lt_or_ge i (n + 1) with
      | inl hlt => exact Or.inl (henC_mono S (Nat.le_of_lt_succ hlt) x hx)
      | inr hge => exact (Nat.le_antisymm h hge) ▸ hx

theorem henC_fresh (S : Formula → Prop) (m : Nat) : ∀ (n : Nat),
    (∀ i, i < n → m ≠ hidxC i) →
    (∀ i, i < n → Not (occursFormula (cst m) (natToFormula i))) →
    ∀ g, henC S n g → Not (occursFormula (cst m) g)
  | 0, _, _, g, hg => ExpF.shiftTheory_fresh' m g hg
  | n + 1, hne, hfr, g, hg => by
      cases hg with
      | inl h =>
          exact henC_fresh S m n (fun i hi => hne i (Nat.lt_succ_of_lt hi))
            (fun i hi => hfr i (Nat.lt_succ_of_lt hi)) g h
      | inr he =>
          subst he
          refine not_occurs_henkinAx ?_ (hfr n (Nat.lt_succ_self n))
          intro hc
          exact hne n (Nat.lt_succ_self n) (cst_inj' m (hidxC n) hc)

theorem henC_fresh_at (S : Formula → Prop) (n : Nat) :
    ∀ g, henC S n g → Not (occursFormula (cst (hidxC n)) g) :=
  henC_fresh S (hidxC n) n
    (fun _ hi => Nat.ne_of_gt (hidxC_mono hi))
    (fun i hi => bndC_spec (natToFormula i) (hidxC n) (hidxC_ge_of_le (Nat.le_of_lt hi)))

theorem henC_consistent {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    ∀ n, IsConsistent₀ (henC S n)
  | 0 => shiftTheory_consistent₀' hCons
  | n + 1 =>
      henkin_step_consistent₀ (henC_consistent hCons n) (cst (hidxC n)) (natToFormula n)
        (henC_fresh_at S n) (bndC_spec (natToFormula n) (hidxC n) (hidxC_ge n))

def henLimitC (S : Formula → Prop) : Formula → Prop := fun x => ∃ n, henC S n x

theorem henLimitC_finite (S : Formula → Prop) : ∀ Γ : List Formula,
    (∀ g, g ∈ Γ → henLimitC S g) → ∃ N, ∀ g, g ∈ Γ → henC S N g
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | g :: Γ, hΓ => by
      obtain ⟨n, hn⟩ := hΓ g (List.Mem.head _)
      obtain ⟨N, hN⟩ := henLimitC_finite S Γ (fun x hx => hΓ x (List.Mem.tail _ hx))
      refine ⟨max n N, fun x hx => ?_⟩
      cases hx with
      | head => exact henC_mono S (Nat.le_max_left _ _) g hn
      | tail _ hx' => exact henC_mono S (Nat.le_max_right _ _) x (hN x hx')

theorem henLimitC_consistent₀ {S : Formula → Prop} (hCons : IsConsistent₀ S) :
    IsConsistent₀ (henLimitC S) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := hbot
  obtain ⟨N, hN⟩ := henLimitC_finite S Γ hΓ
  exact henC_consistent hCons N ⟨Γ, hN, hD⟩

theorem henLimitC_witness (S : Formula → Prop) (A : Formula) :
    ∃ c : String, henLimitC S (henkinAx c A) := by
  obtain ⟨n, hn⟩ := natToFormula_surj A
  exact ⟨cst (hidxC n), n + 1, Or.inr (by rw [hn])⟩

end ExpAll

#print axioms ExpAll.henC_fresh_at
#print axioms ExpAll.henC_consistent
#print axioms ExpAll.henLimitC_consistent₀
#print axioms ExpAll.henLimitC_witness
#print axioms ExpAll.shiftTheory_consistent₀'
