import FOL.Compacity0

/-!
# T71 · b1 — lo que AÑADE la numerabilidad de §3: un emparedado Σ⁰₁, y nada más allá de WLEM

El ENUNCIADO de `infinite_model_of_large_fresh` (luego también el de `infinite_model_of_large`)
da, para todo `P : Prop`, una sucesión `β` DECIDIBLE en `Prop` con

    P → (∃ n, β n) → ¬¬P        y        ¬P → ∀ n, ¬β n

(`sandwich_of_large_fresh`). Es lo que aquí se consigue sacar del modelo NUMERABLE: el `∃`
sobre el dominio pasa a un `∃` sobre `Nat` (por la enumeración) con cuerpo decidible (porque la
teoría obliga a `A` a ser decidible). Pero el cuerpo habla de un elemento ARBITRARIO `e n`, y lo
único que lo conecta con `P` son pertenencias NEGADAS: por eso la vuelta es `→ ¬¬P` y no `→ P`.

* Para el esquema de Kripke (KS: `P ↔ ∃ n, β n`), que con Markov da EM, faltaría `(∃ n, β n) → P`.
* Y el emparedado ENTERO ya sale de WLEM sola (`sandwich_of_wlem`, con `β n := ¬¬P`): la
  numerabilidad no añade fuerza por esta vía.

Testigo: `S_P := {∀x (A x ∨ ¬A x)} ∪ {∃x A x | P} ∪ {∀x ¬A x | ¬P}`, con modelos `Nat ⊕ PLift P`
(`A := está a la derecha`), sin símbolos de función (la frescura de las `cst` es gratis).
-/

set_option autoImplicit false

namespace T71Sem.B1.Sandwich

open FOL.Metamath.Semantics
open FOL.Compacity0 (CountableDom InfiniteDom HasLargeModels)
open FOL.Eigenvariable (occursFormula)
open FOL.Fresh0 (cst)

/-- El ENUNCIADO de `FOL.Compacity0.infinite_model_of_large_fresh`. -/
abbrev LHypFresh : Prop :=
  ∀ {S : Formula → Prop}, (∀ f, S f → ∀ m, Not (occursFormula (cst m) f)) → HasLargeModels S →
    ∃ (D : Type) (M : Model D) (v : Nat → D),
      And (And (CountableDom D) (InfiniteDom D)) (∀ f, S f → evalFormula M v f)

/-- El emparedado Σ⁰₁ (decidible en `Prop`). -/
abbrev Sandw : Prop :=
  ∀ P : Prop, ∃ β : Nat → Prop, And (∀ n, Or (β n) (Not (β n)))
    (And (P → ∃ n, β n) (And ((∃ n, β n) → Not (Not P)) (Not P → ∀ n, Not (β n))))

abbrev WLEM : Prop := ∀ P : Prop, Or (Not P) (Not (Not P))

def sA : List Char := ['A']
def At (t : Term) : Formula := FormulaG.atom sA [t]
def exA : Formula := FormulaG.ex (At (TermG.var 0))
def allNotA : Formula := FormulaG.forall (neg (At (TermG.var 0)))
def decA : Formula := FormulaG.forall (FormulaG.or (At (TermG.var 0)) (neg (At (TermG.var 0))))

def SP (P : Prop) : Formula → Prop := fun f =>
  Or (f = decA) (Or (And (f = exA) P) (And (f = allNotA) (Not P)))

def isR {P : Prop} : Sum Nat (PLift P) → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

def relS {P : Prop} : List (Sum Nat (PLift P)) → Prop
  | [d] => isR d
  | _ => False

def MS (P : Prop) : Model (Sum Nat (PLift P)) := ⟨fun _ _ => Sum.inl 0, fun _ ds => relS ds⟩

/-- Ninguna fórmula de `S_P` tiene símbolos de función. -/
theorem fresh_SP (P : Prop) : ∀ f, SP P f → ∀ m, Not (occursFormula (cst m) f) := by
  intro f hf m
  rcases hf with hf | ⟨hf, _⟩ | ⟨hf, _⟩ <;> subst hf
  · show Not (Or (Or False False) (Or (Or False False) False))
    intro h
    rcases h with (h | h) | ((h | h) | h) <;> exact h
  · show Not (Or False False)
    intro h
    rcases h with h | h <;> exact h
  · show Not (Or (Or False False) False)
    intro h
    rcases h with (h | h) | h <;> exact h

/-- `S_P` tiene modelos con tantos elementos distintos como se quiera: `Nat ⊕ PLift P`. -/
theorem large_SP (P : Prop) : HasLargeModels (SP P) := by
  intro _
  refine ⟨Sum Nat (PLift P), MS P, fun _ => Sum.inl 0, fun f hf => ?_, Sum.inl,
    fun i j _ _ h => Sum.inl.inj h⟩
  rcases hf with hf | ⟨hf, hP⟩ | ⟨hf, hnP⟩
  · subst hf
    intro d
    cases d with
    | inl _ => exact Or.inr (fun h => h)
    | inr _ => exact Or.inl trivial
  · subst hf
    exact ⟨Sum.inr ⟨hP⟩, trivial⟩
  · subst hf
    intro d hd
    cases d with
    | inl _ => exact hd
    | inr p => exact hnP p.down

/-- 🔑 El enunciado de §3 da el emparedado Σ⁰₁ (sin `Classical.choice`). -/
theorem sandwich_of_large_fresh (hL : LHypFresh) : Sandw := by
  intro P
  obtain ⟨D, M, v, ⟨⟨e, he⟩, _⟩, hM⟩ := hL (fresh_SP P) (large_SP P)
  refine ⟨fun n => M.rel sA [e n], fun n => ?_, fun hP => ?_, fun ⟨n, hn⟩ hnP => ?_,
    fun hnP n hn => ?_⟩
  · exact hM decA (Or.inl rfl) (e n)
  · obtain ⟨d, hd⟩ := hM exA (Or.inr (Or.inl ⟨rfl, hP⟩))
    obtain ⟨n, hn⟩ := he d
    refine ⟨n, ?_⟩
    show M.rel sA [e n]
    rw [hn]
    exact hd
  · exact hM allNotA (Or.inr (Or.inr ⟨rfl, hnP⟩)) (e n) hn
  · exact hM allNotA (Or.inr (Or.inr ⟨rfl, hnP⟩)) (e n) hn

/-- …y WLEM sola ya lo da (`β n := ¬¬P`): la numerabilidad no añade fuerza por aquí. -/
theorem sandwich_of_wlem (hW : WLEM) : Sandw := by
  intro P
  refine ⟨fun _ => Not (Not P), fun _ => ?_, fun hP => ⟨0, fun h => h hP⟩, fun ⟨_, h⟩ => h,
    fun hnP _ h => h hnP⟩
  cases hW P with
  | inl h => exact Or.inr (fun hnn => hnn h)
  | inr h => exact Or.inl h

/-- Control: el enunciado REAL (con frescura) cumple la hipótesis. -/
theorem ctrl_sandwich_fresh : Sandw :=
  sandwich_of_large_fresh (fun hF hL => FOL.Compacity0.infinite_model_of_large_fresh hF hL)

/-- Control: y el de `infinite_model_of_large` (sin frescura), que implica el de arriba. -/
theorem ctrl_sandwich : Sandw :=
  sandwich_of_large_fresh (fun _ hL => FOL.Compacity0.infinite_model_of_large hL)

end T71Sem.B1.Sandwich

#print axioms T71Sem.B1.Sandwich.fresh_SP
#print axioms T71Sem.B1.Sandwich.large_SP
#print axioms T71Sem.B1.Sandwich.sandwich_of_large_fresh
#print axioms T71Sem.B1.Sandwich.sandwich_of_wlem
#print axioms T71Sem.B1.Sandwich.ctrl_sandwich_fresh
#print axioms T71Sem.B1.Sandwich.ctrl_sandwich

-- ════════ s1 (escéptico): comprobaciones añadidas ════════
namespace T71Sem.S1B1

open T71Sem.B1.Sandwich

-- (1) `LHypFresh` ES, por definición, el tipo del teorema real
example : LHypFresh = type_of% @FOL.Compacity0.infinite_model_of_large_fresh := rfl

/-- WKS (forma del contexto). -/
abbrev WKS : Prop := ∀ P : Prop, ∃ β : Nat → Prop,
  And (∀ n, Or (β n) (Not (β n))) (Iff (Not P) (∀ n, Not (β n)))
/-- WLPOp (forma del contexto). -/
abbrev WLPOp : Prop := ∀ β : Nat → Prop, (∀ n, Or (β n) (Not (β n))) →
  Or (∀ n, Not (β n)) (Not (∀ n, Not (β n)))

-- (2) el emparedado NO es trivial: implica WKS (y WKS falla, p. ej., en Sh(ℝ))
theorem wks_of_sandw (h : Sandw) : WKS := by
  intro P
  obtain ⟨β, hdec, hPex, _, hnP⟩ := h P
  exact ⟨β, hdec, ⟨hnP, fun hall hP => by
    obtain ⟨n, hn⟩ := hPex hP
    exact hall n hn⟩⟩

-- (3) emparedado + WLPOp ⇒ WLEM (con `sandwich_of_wlem`: emparedado + WLPOp ⟺ WLEM)
theorem wlem_of_sandw_wlpop (h : Sandw) (hw : WLPOp) : WLEM := by
  intro P
  obtain ⟨β, hdec, hPex, hexnn, hnP⟩ := h P
  cases hw β hdec with
  | inl hall => exact Or.inl (fun hP => by obtain ⟨n, hn⟩ := hPex hP; exact hall n hn)
  | inr hn => exact Or.inr (fun hnP' => hn (hnP hnP'))

end T71Sem.S1B1

#print axioms T71Sem.S1B1.wks_of_sandw
#print axioms T71Sem.S1B1.wlem_of_sandw_wlpop
