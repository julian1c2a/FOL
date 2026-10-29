/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.BlockExtraction0
import FOL.Canonical0
import FOL.SymLit

/-!
# `FOL/Markov0.lean` — el ENUNCIADO de la completitud implica MARKOV para predicados con código (T71, ADR‑220 de RPP)

`Canonical0.completeness₀` lleva `Classical.choice`. ¿Es esencial? Su enunciado no implica el tercero excluido, pero sí
un principio que la lógica constructiva no demuestra: el de **Markov** para los predicados dados por un CÓDIGO
(Kreisel). Aquí, compilado y sin `Classical.choice`:

    markov_dioph_of_completeness :
      (∀ Γ f, satisfies Γ f → Γ ⊢₀ f) →
      ∀ p q : Poly, ¬¬ (∃ ν, p.eval ν = q.eval ν) → ∃ ν, p.eval ν = q.eval ν

con los códigos más sencillos que bastan: dos POLINOMIOS con coeficientes en ℕ (`Poly`), es decir, una ecuación
DIOFÁNTICA. Markov para ellas no lo demuestra la aritmética intuicionista (HA): por el teorema de Matiyasevich–Robinson–
Davis–Putnam equivale allí al de los predicados recursivos primitivos (no formalizado aquí).

## La prueba (el plan de ADR‑219 de RPP, sin la teoría como contexto)

1. **La fórmula.** `kreiselF p q := ∃y₀…y₅ ∃x̄ (Ax(ȳ) → p(x̄) = q(x̄))`, un bloque existencial sobre una matriz SIN
   cuantificadores: `Ax` son los cuatro axiomas de Robinson para `+` y `·` (`y+0=y`, `y+Sz=S(y+z)`, `y·0=0`,
   `y·Sz=y·z+y`), instanciados en variables del propio bloque.
2. **Su doble negación es VÁLIDA, sin lógica clásica** (`valid_nn_kreiselF`): si en un modelo no se cumpliera,
   toda instancia de los axiomas sería ¬¬‑verdadera y toda instancia de la ecuación, falsa; y con un `ν` que resuelve la
   ecuación (de `¬¬∃ν`, para refutar basta uno), el cálculo de `p(ν̄)` y `q(ν̄)` en el modelo —dentro de la mónada `¬¬`—
   da la ecuación en los numerales: contradicción.
3. **El enunciado de la completitud** da `[] ⊢₀ ¬¬kreiselF`, y `dne_schema`, `[] ⊢₀ kreiselF`.
4. **Herbrand de bloque** (`BlockExtraction0.herbrand_block₀`, sin choice) da un certificado: una disyunción finita de
   instancias, tautología proposicional módulo instancias de la igualdad.
5. **El modelo estándar decide** (`MN`): evaluando el certificado en ℕ, alguna instancia es verdadera, sus axiomas lo
   son siempre, y su ecuación da el `ν`.

## 📏 Footprint

`markov_dioph_of_completeness`: `[propext, Quot.sound]`. El control `markov_dioph_classical` —el mismo principio con la
completitud de verdad, `completeness₀`— lleva `Classical.choice`: el de `completeness₀`, que ahora se sabe que no se
puede quitar sin quitar Markov.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FOL.Markov0

open FOL.Metamath.Semantics
open FOL.Propositional0
open FOL.Herbrand0
open FOL.HerbrandBlock0

-- ============================================================
-- §1 · Los códigos: polinomios con coeficientes en ℕ
-- ============================================================

/-- Un polinomio en las variables `x₀, x₁, …` con coeficientes en ℕ. -/
inductive Poly : Type where
  | var : Nat → Poly
  | zero : Poly
  | succ : Poly → Poly
  | add : Poly → Poly → Poly
  | mul : Poly → Poly → Poly

/-- Su valor en `ν`. -/
def Poly.eval (ν : Nat → Nat) : Poly → Nat
  | .var i => ν i
  | .zero => 0
  | .succ p => p.eval ν + 1
  | .add p q => p.eval ν + q.eval ν
  | .mul p q => p.eval ν * q.eval ν

/-- Una cota de sus variables: todas son menores que `nvars`. -/
def Poly.nvars : Poly → Nat
  | .var i => i + 1
  | .zero => 0
  | .succ p => p.nvars
  | .add p q => Nat.max p.nvars q.nvars
  | .mul p q => Nat.max p.nvars q.nvars

-- ============================================================
-- §2 · La sintaxis: los símbolos de la aritmética y la fórmula de Kreisel
-- ============================================================

def sZ : List Char := sym!"0"
def sS : List Char := sym!"S"
def sA : List Char := sym!"+"
def sM : List Char := sym!"*"

def tZ : Term := TermG.func sZ []
def tS (t : Term) : Term := TermG.func sS [t]
def tA (t u : Term) : Term := TermG.func sA [t, u]
def tM (t u : Term) : Term := TermG.func sM [t, u]

/-- El polinomio como término, con la variable `xᵢ` en el índice `off + i`. -/
def Poly.toTerm (off : Nat) : Poly → Term
  | .var i => TermG.var (off + i)
  | .zero => tZ
  | .succ p => tS (p.toTerm off)
  | .add p q => tA (p.toTerm off) (q.toTerm off)
  | .mul p q => tM (p.toTerm off) (q.toTerm off)

/-- Los cuatro axiomas de Robinson para `+` y `·`, en las variables `#0 … #5`. -/
def axA1 : Formula := FormulaG.eq (tA (TermG.var 0) tZ) (TermG.var 0)
def axA2 : Formula := FormulaG.eq (tA (TermG.var 1) (tS (TermG.var 2))) (tS (tA (TermG.var 1) (TermG.var 2)))
def axM1 : Formula := FormulaG.eq (tM (TermG.var 3) tZ) tZ
def axM2 : Formula := FormulaG.eq (tM (TermG.var 4) (tS (TermG.var 5))) (tA (tM (TermG.var 4) (TermG.var 5)) (TermG.var 4))
def axQ : Formula := FormulaG.and axA1 (FormulaG.and axA2 (FormulaG.and axM1 axM2))

/-- La matriz: los axiomas implican la ecuación, con `xᵢ` en `#(6 + i)`. -/
def matrix (p q : Poly) : Formula := FormulaG.impl axQ (FormulaG.eq (p.toTerm 6) (q.toTerm 6))

/-- El tamaño del bloque: seis variables para los axiomas y las de los polinomios. -/
def blockSize (p q : Poly) : Nat := 6 + Nat.max p.nvars q.nvars

/-- ⭐ **La fórmula de Kreisel**: `∃ȳ ∃x̄ (Ax(ȳ) → p(x̄) = q(x̄))`. -/
def kreiselF (p q : Poly) : Formula := exBlock (blockSize p q) (matrix p q)

theorem quantFree_matrix (p q : Poly) : QuantFree (matrix p q) :=
  ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩

-- ============================================================
-- §3 · Bloques y entornos: evaluar `exBlock` e `instB`
-- ============================================================

/-- `E` es `v` con `n` valores delante: `E (i + n) = v i`. -/
def IsPre {D : Type} (n : Nat) (E v : Nat → D) : Prop := ∀ i, E (i + n) = v i

/-- El entorno con los valores `f i` en los índices `i < n` y `v` detrás. -/
def blk {D : Type} (f : Nat → D) (n : Nat) (v : Nat → D) : Nat → D := fun i => if i < n then f i else v (i - n)

theorem isPre_blk {D : Type} (f : Nat → D) (n : Nat) (v : Nat → D) : IsPre n (blk f n v) v := by
  intro i
  show (if i + n < n then f (i + n) else v (i + n - n)) = v i
  rw [ite_eq_right (Nat.not_lt.mpr (Nat.le_add_left n i)), Nat.add_sub_cancel]

theorem blk_lt {D : Type} (f : Nat → D) {n : Nat} (v : Nat → D) {i : Nat} (h : i < n) : blk f n v i = f i := by
  show (if i < n then f i else v (i - n)) = f i
  rw [ite_eq_left h]

theorem evalTerm_congr {D : Type} (M : Model D) {v w : Nat → D} (h : ∀ i, v i = w i) (t : Term) :
    evalTerm M v t = evalTerm M w t := by
  rw [funext h]

theorem evalFormula_congr {D : Type} (M : Model D) {v w : Nat → D} (h : ∀ i, v i = w i) (f : Formula) :
    Iff (evalFormula M v f) (evalFormula M w f) := by
  rw [funext h]

/-- Evaluar un bloque existencial: un entorno con `n` valores delante. (Sólo la vuelta hace falta aquí.) -/
theorem eval_exBlock_of {D : Type} (M : Model D) :
    ∀ (n : Nat) (φ : Formula) (v E : Nat → D), IsPre n E v → evalFormula M E φ → evalFormula M v (exBlock n φ)
  | 0, φ, v, E, hE, h => by
      show evalFormula M v φ
      exact (evalFormula_congr M (fun i => hE i) φ).mp h
  | n + 1, φ, v, E, hE, h => by
      show ∃ d : D, evalFormula M (shiftEnv v d) (exBlock n φ)
      refine ⟨E n, eval_exBlock_of M n φ (shiftEnv v (E n)) E (fun i => ?_) h⟩
      cases i with
      | zero => show E (0 + n) = E n; rw [Nat.zero_add]
      | succ j =>
          show E (j + 1 + n) = v j
          rw [Nat.add_assoc, Nat.add_comm 1 n]
          exact hE j

/-- `liftN n t`, evaluado con `n` valores delante, es `t`. -/
theorem eval_liftN {D : Type} (M : Model D) :
    ∀ (n : Nat) (t : Term) (E v : Nat → D), IsPre n E v → evalTerm M E (liftN n t) = evalTerm M v t
  | 0, t, E, v, hE => evalTerm_congr M (fun i => hE i) t
  | n + 1, t, E, v, hE => by
      show evalTerm M E (liftN n (liftTerm 0 t)) = evalTerm M v t
      rw [eval_liftN M n (liftTerm 0 t) E (fun i => E (i + n)) (fun _ => rfl)]
      have hsh : ∀ i, E (i + n) = updateEnv 0 v (E n) i := by
        intro i
        rw [updateEnv_zero]
        cases i with
        | zero => show E (0 + n) = E n; rw [Nat.zero_add]
        | succ j =>
            show E (j + 1 + n) = v j
            rw [Nat.add_assoc, Nat.add_comm 1 n]
            exact hE j
      rw [evalTerm_congr M hsh, eval_liftTerm_ext]

/-- Evaluar una instancia de bloque: un entorno con los valores de los términos delante. -/
theorem eval_instB {D : Type} (M : Model D) :
    ∀ (n : Nat) (ts : List Term) (φ : Formula) (v : Nat → D), ts.length = n →
      ∃ E, And (IsPre n E v) (Iff (evalFormula M v (instB n ts φ)) (evalFormula M E φ))
  | 0, _, φ, v, _ => ⟨v, fun i => rfl, Iff.rfl⟩
  | n + 1, [], _, _, h => absurd h (Nat.succ_ne_zero n).symm
  | n + 1, t :: ts, φ, v, h => by
      obtain ⟨E', hE', hiff⟩ := eval_instB M n ts (substFormula n (liftN n t) φ) v (Nat.succ.inj h)
      refine ⟨updateEnv n E' (evalTerm M v t), fun i => ?_, ?_⟩
      · show (if i + (n + 1) < n then E' (i + (n + 1))
              else if i + (n + 1) = n then evalTerm M v t else E' (i + (n + 1) - 1)) = v i
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [show i + (n + 1) - 1 = i + n by omega]
        exact hE' i
      · show Iff (evalFormula M v (instB n ts (substFormula n (liftN n t) φ))) _
        rw [hiff, eval_substFormula_ext, eval_liftN M n t E' v hE']

-- ============================================================
-- §4 · La doble negación de la fórmula es válida, sin lógica clásica
-- ============================================================

section Valid

variable {D : Type} (M : Model D)

/-- Los numerales en el modelo. -/
def numM : Nat → D
  | 0 => M.func sZ []
  | n + 1 => M.func sS [numM n]

theorem nn_map {P Q : Prop} (f : P → Q) (h : Not (Not P)) : Not (Not Q) := fun hq => h (fun hp => hq (f hp))

theorem nn_bind {P Q : Prop} (h : Not (Not P)) (f : P → Not (Not Q)) : Not (Not Q) :=
  fun hq => h (fun hp => f hp hq)

/-- Las instancias de los axiomas que el cálculo usa, ¬¬‑verdaderas. -/
structure AxFacts : Prop where
  a1 : ∀ a, Not (Not (M.func sA [a, M.func sZ []] = a))
  a2 : ∀ a b, Not (Not (M.func sA [a, M.func sS [b]] = M.func sS [M.func sA [a, b]]))
  m1 : ∀ a, Not (Not (M.func sM [a, M.func sZ []] = M.func sZ []))
  m2 : ∀ a b, Not (Not (M.func sM [a, M.func sS [b]] = M.func sA [M.func sM [a, b], a]))

variable {M}

theorem add_num (hx : AxFacts M) (a : Nat) :
    ∀ m, Not (Not (M.func sA [numM M a, numM M m] = numM M (a + m)))
  | 0 => hx.a1 (numM M a)
  | m + 1 => nn_bind (hx.a2 (numM M a) (numM M m)) fun h2 =>
      nn_map (fun ih => by
          show M.func sA [numM M a, M.func sS [numM M m]] = M.func sS [numM M (a + m)]
          rw [h2, ih]) (add_num hx a m)

theorem mul_num (hx : AxFacts M) (a : Nat) :
    ∀ m, Not (Not (M.func sM [numM M a, numM M m] = numM M (a * m)))
  | 0 => hx.m1 (numM M a)
  | m + 1 => nn_bind (hx.m2 (numM M a) (numM M m)) fun h2 =>
      nn_bind (mul_num hx a m) fun ih =>
        nn_map (fun hadd => by
            show M.func sM [numM M a, M.func sS [numM M m]] = numM M (a * m + a)
            rw [h2, ih, hadd]) (add_num hx (a * m) a)

/-- Una cota de las variables de un polinomio. -/
def VarsLt (k : Nat) : Poly → Prop
  | .var i => i < k
  | .zero => True
  | .succ p => VarsLt k p
  | .add p q => And (VarsLt k p) (VarsLt k q)
  | .mul p q => And (VarsLt k p) (VarsLt k q)

theorem varsLt_mono {k k' : Nat} (hk : k ≤ k') : ∀ p : Poly, VarsLt k p → VarsLt k' p
  | .var _, h => Nat.lt_of_lt_of_le h hk
  | .zero, _ => trivial
  | .succ p, h => varsLt_mono hk p h
  | .add p q, h => ⟨varsLt_mono hk p h.1, varsLt_mono hk q h.2⟩
  | .mul p q, h => ⟨varsLt_mono hk p h.1, varsLt_mono hk q h.2⟩

theorem varsLt_nvars : ∀ p : Poly, VarsLt p.nvars p
  | .var i => Nat.lt_succ_self i
  | .zero => trivial
  | .succ p => varsLt_nvars p
  | .add p q => ⟨varsLt_mono (Nat.le_max_left _ _) p (varsLt_nvars p),
                 varsLt_mono (Nat.le_max_right _ _) q (varsLt_nvars q)⟩
  | .mul p q => ⟨varsLt_mono (Nat.le_max_left _ _) p (varsLt_nvars p),
                 varsLt_mono (Nat.le_max_right _ _) q (varsLt_nvars q)⟩

/-- 🔑 **El cálculo de un polinomio en el modelo**, dentro de `¬¬`: si en `#(6 + i)` están los numerales de `ν i`,
el valor del término es el numeral de `p.eval ν`. -/
theorem eval_poly (hx : AxFacts M) (ν : Nat → Nat) (E : Nat → D) (k : Nat)
    (hE : ∀ i, i < k → E (6 + i) = numM M (ν i)) :
    ∀ p : Poly, VarsLt k p → Not (Not (evalTerm M E (p.toTerm 6) = numM M (p.eval ν)))
  | .var i, h => fun hn => hn (hE i h)
  | .zero, _ => fun hn => hn rfl
  | .succ p, h => nn_map (fun ih => by
        show M.func sS [evalTerm M E (p.toTerm 6)] = M.func sS [numM M (p.eval ν)]
        rw [ih]) (eval_poly hx ν E k hE p h)
  | .add p q, h => nn_bind (eval_poly hx ν E k hE p h.1) fun hp =>
      nn_bind (eval_poly hx ν E k hE q h.2) fun hq =>
        nn_map (fun hadd => by
            show M.func sA [evalTerm M E (p.toTerm 6), evalTerm M E (q.toTerm 6)] = numM M (p.eval ν + q.eval ν)
            rw [hp, hq, hadd]) (add_num hx (p.eval ν) (q.eval ν))
  | .mul p q, h => nn_bind (eval_poly hx ν E k hE p h.1) fun hp =>
      nn_bind (eval_poly hx ν E k hE q h.2) fun hq =>
        nn_map (fun hmul => by
            show M.func sM [evalTerm M E (p.toTerm 6), evalTerm M E (q.toTerm 6)] = numM M (p.eval ν * q.eval ν)
            rw [hp, hq, hmul]) (mul_num hx (p.eval ν) (q.eval ν))

/-- Seis valores para las variables de los axiomas. -/
def six (a0 a1 a2 a3 a4 a5 : D) : Nat → D := fun i => [a0, a1, a2, a3, a4, a5].getD i a0

/-- 🏁 **`¬¬kreiselF` es válida**, con `¬¬∃ν` como única hipótesis, y sin lógica clásica. -/
theorem valid_nn_kreiselF (p q : Poly) (hnn : Not (Not (∃ ν : Nat → Nat, p.eval ν = q.eval ν))) :
    satisfies [] (neg (neg (kreiselF p q))) := by
  intro D M v _ hnF
  apply hnn
  intro ⟨ν, hν⟩
  have hn6 : ∀ i, i < 6 → i < blockSize p q := fun i hi => Nat.lt_of_lt_of_le hi (Nat.le_add_right 6 _)
  -- Si `kreiselF` no vale, ningún entorno del bloque satisface la matriz.
  have H0 : ∀ E, IsPre (blockSize p q) E v → Not (evalFormula M E (matrix p q)) :=
    fun E hE h => hnF (eval_exBlock_of M _ _ v E hE h)
  -- Y entonces toda instancia de los axiomas es ¬¬‑verdadera.
  have hAx : ∀ f : Nat → D, Not (Not (evalFormula M (blk f (blockSize p q) v) axQ)) :=
    fun f hn => H0 _ (isPre_blk f _ v) (fun hA => absurd hA hn)
  have hx : AxFacts M := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a => ?_, fun a b => ?_⟩
    · refine nn_map (fun h => ?_) (hAx (six a a a a a a))
      have h1 := h.1
      change M.func sA [blk (six a a a a a a) _ v 0, M.func sZ []] = blk (six a a a a a a) _ v 0 at h1
      rw [blk_lt _ _ (hn6 0 (by decide))] at h1
      exact h1
    · refine nn_map (fun h => ?_) (hAx (six a a b a a a))
      have h2 := h.2.1
      change M.func sA [blk (six a a b a a a) _ v 1, M.func sS [blk (six a a b a a a) _ v 2]]
          = M.func sS [M.func sA [blk (six a a b a a a) _ v 1, blk (six a a b a a a) _ v 2]] at h2
      rw [blk_lt _ _ (hn6 1 (by decide)), blk_lt _ _ (hn6 2 (by decide))] at h2
      exact h2
    · refine nn_map (fun h => ?_) (hAx (six a a a a a a))
      have h3 := h.2.2.1
      change M.func sM [blk (six a a a a a a) _ v 3, M.func sZ []] = M.func sZ [] at h3
      rw [blk_lt _ _ (hn6 3 (by decide))] at h3
      exact h3
    · refine nn_map (fun h => ?_) (hAx (six a a a a a b))
      have h4 := h.2.2.2
      change M.func sM [blk (six a a a a a b) _ v 4, M.func sS [blk (six a a a a a b) _ v 5]]
          = M.func sA [M.func sM [blk (six a a a a a b) _ v 4, blk (six a a a a a b) _ v 5],
              blk (six a a a a a b) _ v 4] at h4
      rw [blk_lt _ _ (hn6 4 (by decide)), blk_lt _ _ (hn6 5 (by decide))] at h4
      exact h4
  -- El entorno con los numerales de `ν` en las variables de los polinomios.
  let g : Nat → D := fun i => numM M (ν (i - 6))
  let E := blk g (blockSize p q) v
  have hE : ∀ i, i < Nat.max p.nvars q.nvars → E (6 + i) = numM M (ν i) := by
    intro i hi
    show blk g (blockSize p q) v (6 + i) = numM M (ν i)
    rw [blk_lt (n := blockSize p q) _ _ (Nat.add_lt_add_left hi 6)]
    show numM M (ν (6 + i - 6)) = numM M (ν i)
    rw [Nat.add_sub_cancel_left]
  have hT : Not (evalFormula M E (FormulaG.eq (p.toTerm 6) (q.toTerm 6))) :=
    fun hT => H0 E (isPre_blk g _ v) (fun _ => hT)
  have hp := eval_poly hx ν E _ hE p (varsLt_mono (Nat.le_max_left _ _) p (varsLt_nvars p))
  have hq := eval_poly hx ν E _ hE q (varsLt_mono (Nat.le_max_right _ _) q (varsLt_nvars q))
  exact hp fun hp' => hq fun hq' => hT (by
    show evalTerm M E (p.toTerm 6) = evalTerm M E (q.toTerm 6)
    rw [hp', hq', hν])

end Valid

-- ============================================================
-- §5 · El modelo estándar decide el certificado
-- ============================================================

/-- ⭐ **El modelo estándar** de la aritmética: `0`, `S`, `+` y `·` sobre ℕ; ninguna relación. -/
def MN : Model Nat where
  func s ds := match s, ds with
    | ['0'], [] => 0
    | ['S'], [a] => a + 1
    | ['+'], [a, b] => a + b
    | ['*'], [a, b] => a * b
    | _, _ => 0
  rel _ _ := False

/-- La valoración proposicional que da el modelo estándar en `ρ`: las ecuaciones, decididas en ℕ. -/
def vMN (ρ : Nat → Nat) : PVal := fun f => match f with
  | .eq t u => decide (evalTerm MN ρ t = evalTerm MN ρ u)
  | _ => false

/-- Sin cuantificadores, la valoración y la evaluación en ℕ coinciden. -/
theorem peval_vMN (ρ : Nat → Nat) :
    ∀ f : Formula, QuantFree f → Iff (peval (vMN ρ) f = true) (evalFormula MN ρ f)
  | .bottom, _ => Iff.intro (fun h => Bool.noConfusion h) (fun h => h.elim)
  | .atom _ _, _ => Iff.intro (fun h => Bool.noConfusion h) (fun h => h.elim)
  | .eq t u, _ => Iff.intro (fun h => show evalTerm MN ρ t = evalTerm MN ρ u from of_decide_eq_true h)
      (fun h => decide_eq_true (p := evalTerm MN ρ t = evalTerm MN ρ u) h)
  | .impl a b, h => by
      have ia := peval_vMN ρ a h.1
      have ib := peval_vMN ρ b h.2
      show Iff ((!(peval (vMN ρ) a) || peval (vMN ρ) b) = true) (evalFormula MN ρ a → evalFormula MN ρ b)
      cases ha : peval (vMN ρ) a with
      | false => exact Iff.intro (fun _ hA => absurd (ia.mpr hA) (by rw [ha]; exact Bool.false_ne_true))
                   (fun _ => rfl)
      | true =>
          cases hb : peval (vMN ρ) b with
          | false => exact Iff.intro (fun h => Bool.noConfusion h)
                       (fun h => absurd (ib.mpr (h (ia.mp ha))) (by rw [hb]; exact Bool.false_ne_true))
          | true => exact Iff.intro (fun _ _ => ib.mp hb) (fun _ => rfl)
  | .and a b, h => by
      have ia := peval_vMN ρ a h.1
      have ib := peval_vMN ρ b h.2
      show Iff ((peval (vMN ρ) a && peval (vMN ρ) b) = true) (And (evalFormula MN ρ a) (evalFormula MN ρ b))
      rw [Bool.and_eq_true, ia, ib]
  | .or a b, h => by
      have ia := peval_vMN ρ a h.1
      have ib := peval_vMN ρ b h.2
      show Iff ((peval (vMN ρ) a || peval (vMN ρ) b) = true) (Or (evalFormula MN ρ a) (evalFormula MN ρ b))
      rw [Bool.or_eq_true, ia, ib]
  | .forall _, h => h.elim
  | .ex _, h => h.elim

theorem evalTerms_append {D : Type} (M : Model D) (ρ : Nat → D) :
    ∀ (l₁ l₂ : List Term), evalTerms M ρ (l₁ ++ l₂) = evalTerms M ρ l₁ ++ evalTerms M ρ l₂
  | [], _ => rfl
  | t :: l₁, l₂ => by
      show evalTerm M ρ t :: evalTerms M ρ (l₁ ++ l₂) = evalTerm M ρ t :: (evalTerms M ρ l₁ ++ evalTerms M ρ l₂)
      rw [evalTerms_append M ρ l₁ l₂]

/-- Las instancias de la igualdad son verdaderas en todo modelo. -/
theorem eqInstance_true {D : Type} (M : Model D) (ρ : Nat → D) {g : Formula} (h : EqInstance g) :
    evalFormula M ρ g := by
  cases h with
  | refl t => exact (rfl : evalTerm M ρ t = evalTerm M ρ t)
  | symm t u => exact fun h => h.symm
  | trans t u w => exact fun h1 h2 => h1.trans h2
  | func f pre post a b =>
      intro hab
      show M.func f (evalTerms M ρ (pre ++ a :: post)) = M.func f (evalTerms M ρ (pre ++ b :: post))
      rw [evalTerms_append, evalTerms_append]
      show M.func f (evalTerms M ρ pre ++ evalTerm M ρ a :: evalTerms M ρ post)
          = M.func f (evalTerms M ρ pre ++ evalTerm M ρ b :: evalTerms M ρ post)
      rw [show evalTerm M ρ a = evalTerm M ρ b from hab]
  | atom p pre post a b =>
      intro hab
      show M.rel p (evalTerms M ρ (pre ++ a :: post)) → M.rel p (evalTerms M ρ (pre ++ b :: post))
      rw [evalTerms_append, evalTerms_append]
      show M.rel p (evalTerms M ρ pre ++ evalTerm M ρ a :: evalTerms M ρ post)
          → M.rel p (evalTerms M ρ pre ++ evalTerm M ρ b :: evalTerms M ρ post)
      rw [show evalTerm M ρ a = evalTerm M ρ b from hab]
      exact id

theorem mem_of_peval_disjOf (v : PVal) :
    ∀ fs : List Formula, peval v (disjOf fs) = true → ∃ f, And (f ∈ fs) (peval v f = true)
  | [], h => Bool.noConfusion h
  | f :: fs, h => by
      have h' : (peval v f || peval v (disjOf fs)) = true := h
      rcases Bool.or_eq_true _ _ |>.mp h' with hf | hr
      · exact ⟨f, List.mem_cons_self, hf⟩
      · obtain ⟨g, hg, hgv⟩ := mem_of_peval_disjOf v fs hr
        exact ⟨g, List.mem_cons_of_mem f hg, hgv⟩

/-- En el modelo estándar los axiomas valen siempre. -/
theorem axQ_MN (E : Nat → Nat) : evalFormula MN E axQ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- El valor de un polinomio en el modelo estándar. -/
theorem evalTerm_MN_poly (E : Nat → Nat) : ∀ p : Poly, evalTerm MN E (p.toTerm 6) = p.eval (fun i => E (6 + i))
  | .var _ => rfl
  | .zero => rfl
  | .succ p => by
      show evalTerm MN E (p.toTerm 6) + 1 = p.eval (fun i => E (6 + i)) + 1
      rw [evalTerm_MN_poly E p]
  | .add p q => by
      show evalTerm MN E (p.toTerm 6) + evalTerm MN E (q.toTerm 6) = _
      rw [evalTerm_MN_poly E p, evalTerm_MN_poly E q]; rfl
  | .mul p q => by
      show evalTerm MN E (p.toTerm 6) * evalTerm MN E (q.toTerm 6) = _
      rw [evalTerm_MN_poly E p, evalTerm_MN_poly E q]; rfl

/-- 🔑 **Del certificado de Herbrand, una solución**: evaluado en ℕ, alguna instancia es verdadera, y su ecuación
da el `ν`. -/
theorem solution_of_cert {p q : Poly} {tss : List (List Term)} {E : List Formula}
    (hc : HerbrandCertBlock (blockSize p q) (matrix p q) tss E) : ∃ ν : Nat → Nat, p.eval ν = q.eval ν := by
  let ρ : Nat → Nat := fun _ => 0
  have hE : ∀ g, g ∈ E → peval (vMN ρ) g = true := fun g hg =>
    (peval_vMN ρ g (FOL.Sequent0.quantFree_of_eqInstance (hc.2.1 g hg))).mpr (eqInstance_true MN ρ (hc.2.1 g hg))
  obtain ⟨f, hf, hfv⟩ := mem_of_peval_disjOf (vMN ρ) _ (hc.2.2 (vMN ρ) hE)
  obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hf
  have hlen := hc.1 ts hts
  have hqf := quantFree_instB _ ts _ hlen (quantFree_matrix p q)
  obtain ⟨Env, _, hiff⟩ := eval_instB MN _ ts (matrix p q) ρ hlen
  have hm : evalFormula MN Env (matrix p q) := hiff.mp ((peval_vMN ρ _ hqf).mp hfv)
  have heq : evalTerm MN Env (p.toTerm 6) = evalTerm MN Env (q.toTerm 6) := hm (axQ_MN Env)
  exact ⟨fun i => Env (6 + i), by rw [← evalTerm_MN_poly, ← evalTerm_MN_poly]; exact heq⟩

-- ============================================================
-- §6 · El teorema
-- ============================================================

/-- El ENUNCIADO de la completitud de `Derives₀` para contextos finitos. -/
def CompletenessStmt : Prop := ∀ (Γ : List Formula) (f : Formula), satisfies Γ f → Γ ⊢₀ f

/-- 🏁 **El enunciado de la completitud implica Markov para las ecuaciones diofánticas**, sin `Classical.choice`. -/
theorem markov_dioph_of_completeness (H : CompletenessStmt) (p q : Poly)
    (hnn : Not (Not (∃ ν : Nat → Nat, p.eval ν = q.eval ν))) : ∃ ν : Nat → Nat, p.eval ν = q.eval ν := by
  have hd : [] ⊢₀ neg (neg (kreiselF p q)) := H [] _ (valid_nn_kreiselF p q hnn)
  have hF : [] ⊢₀ kreiselF p q := Derives₀.elim_impl [] _ _ (Derives₀.dne_schema [] (kreiselF p q)) hd
  obtain ⟨tss, E, hc⟩ := (FOL.BlockExtraction0.herbrand_block₀ (quantFree_matrix p q)).mp hF
  exact solution_of_cert hc

/-- 🔍 **El control**: con la completitud de verdad, el principio de Markov para las ecuaciones diofánticas sale (con
el `Classical.choice` de `completeness₀`). La hipótesis del teorema no es vacía. -/
theorem markov_dioph_classical (p q : Poly) (hnn : Not (Not (∃ ν : Nat → Nat, p.eval ν = q.eval ν))) :
    ∃ ν : Nat → Nat, p.eval ν = q.eval ν :=
  markov_dioph_of_completeness (fun _ _ h => FOL.Canonical0.completeness₀ h) p q hnn

end FOL.Markov0

#print axioms FOL.Markov0.valid_nn_kreiselF
#print axioms FOL.Markov0.solution_of_cert
#print axioms FOL.Markov0.markov_dioph_of_completeness
#print axioms FOL.Markov0.markov_dioph_classical
