/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Propositional0, FOL.Eq0
-- @axiom_system: constructive
-- @importance: high

import FOL.Propositional0
import FOL.Eq0

/-!
# `FOL.Herbrand0` — **H4**: el CERTIFICADO de Herbrand, construido y VERIFICABLE

Hito **H4** de `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.2, y el objetivo **H** de §0: *«de una prueba
de `∃x φ(x)` con `φ` sin cuantificadores, extraer términos `t₁…tₙ` tales que
`φ(t₁) ∨ … ∨ φ(tₙ)` sea tautología»*.

    derives0_ex_of_cert : HerbrandCert φ ts E → [] ⊢₀ ∃x φ(x)

⭐⭐ **Y el certificado es DATO SINTÁCTICO y se verifica por cómputo**: `HerbrandCert` es una lista
de términos, una lista de instancias de los axiomas de la igualdad, y una **tautología
proposicional comprobable con `ptautCheck` — que reduce, así que sale `by rfl`**. Ver §7.

Footprint: `[propext, Quot.sound]`. **Ni un `Classical.choice`**, en todo el módulo.

## Lo que está y lo que falta — dicho antes que nada

| | dirección | estado |
|---|---|---|
| ⟸ | **certificado ⇒ demostración** | 🏁 **DEMOSTRADA aquí**, incondicional y finitaria |
| ⟹ | **demostración ⇒ certificado** (H3) | ⬜ **DEUDA**, enunciada como `Prop`, no postulada |

⛔ **La ⟹ es H3 —la eliminación de cortes— y NO está.** Aquí se **enuncia** como
`HerbrandExtraction`, y se escribe **el consumidor**: `herbrand_iff`, que con ella convierte
Herbrand en un `↔`. *Una deuda se enuncia como `Prop`, nunca se postula* — y el consumidor va
antes, para que la guarda salga de él y no del molde.

## ⚠️ Por qué el certificado lleva una lista `E`, y no sólo términos

Porque **hay igualdad** (§5.3 del plan). Sin `=`, la disyunción de Herbrand acaba en tautología
**proposicional**. Con `=`, acaba en tautología **del esqueleto módulo la teoría ecuacional**:
`∃x (x ≐ c)` tiene certificado `ts = [c]`, y su disyunción es `c ≐ c`, que **no** es tautología
proposicional —es un átomo— pero sí es un axioma de la igualdad.

⭐ La solución finitaria no es «clausura de congruencia» como procedimiento, sino **listar las
instancias que el certificado usa**: `E`. Cada una es una `EqInstance` —refl, simetría,
transitividad, congruencia de función, congruencia de relación— y **todas son derivables**
(`derives0_of_eqInstance`), así que el certificado no añade fuerza: sólo la organiza.

🔑 *La clausura de congruencia se convierte en un dato del certificado, y la decidibilidad que hacía
falta es la de la tautología proposicional, que ya está (`ptautCheck`).*

## ⭐ Y una pieza que conviene mirar: el CUT sobre premisas derivables

`derives0_discharge : (E ⊢₀ ψ) → (∀ g ∈ E, [] ⊢₀ g) → [] ⊢₀ ψ` es **un corte**, y aquí es
**admisible gratis** porque `intro_impl` es un **constructor** de `Derives₀`. ⚠️ Esto **no** es
H3: eliminar el corte es transformar la *derivación* para que no lo use; esto sólo lo *contrae*.
Pero es la mitad fácil, y es lo que permite que el certificado descargue su propia `E`.

## Ámbito

⚠️ **Un solo cuantificador.** `∃x φ(x)`, no `∃x̄`. La versión n‑aria es iteración rutinaria pero
la aritmética de De Bruijn bajo binders anidados (`substFormula 0 t (∃ψ) = ∃ (substFormula 1 (lift t) ψ)`)
pide su propia capa de lemas. ⬜ No hecho, y dicho.
-/

namespace FOL.Herbrand0

open FOL.DecEq
open FOL.Propositional0
open FOL.Eq0

-- ============================================================
-- §1 · El verificador de tautologías, que REDUCE
-- ============================================================

-- ⚠️ Vive aquí y no en `FOL.Propositional0` a propósito: existe **para** el certificado, y así
-- aquel módulo —ya publicado y medido— no se toca.

/-- `peval` sólo mira los átomos de la fórmula. -/
theorem peval_congr {v w : PVal} : ∀ (φ : Formula),
    (∀ a, a ∈ patoms φ → v a = w a) → peval v φ = peval w φ := by
  intro φ
  induction φ with
  | bottom => intro _; rfl
  | atom p ts => intro h; exact h _ (List.Mem.head _)
  | eq t u => intro h; exact h _ (List.Mem.head _)
  | «forall» a => intro h; exact h _ (List.Mem.head _)
  | ex a => intro h; exact h _ (List.Mem.head _)
  | impl A B ihA ihB =>
      intro h
      show ((!(peval v A)) || peval v B) = ((!(peval w A)) || peval w B)
      rw [ihA (fun a ha => h a (List.mem_append.mpr (Or.inl ha))),
          ihB (fun a ha => h a (List.mem_append.mpr (Or.inr ha)))]
  | and A B ihA ihB =>
      intro h
      show (peval v A && peval v B) = (peval w A && peval w B)
      rw [ihA (fun a ha => h a (List.mem_append.mpr (Or.inl ha))),
          ihB (fun a ha => h a (List.mem_append.mpr (Or.inr ha)))]
  | or A B ihA ihB =>
      intro h
      show (peval v A || peval v B) = (peval w A || peval w B)
      rw [ihA (fun a ha => h a (List.mem_append.mpr (Or.inl ha))),
          ihB (fun a ha => h a (List.mem_append.mpr (Or.inr ha)))]

/-- Expansión de Shannon sobre la lista de átomos: la tabla de verdad, recorrida. -/
def pcheck : List Formula → PVal → Formula → Bool
  | [], v, φ => peval v φ
  | a :: L, v, φ => pcheck L (upd v a true) φ && pcheck L (upd v a false) φ

theorem pcheck_sound : ∀ (L : List Formula) (v : PVal) (φ : Formula),
    pcheck L v φ = true → ∀ w : PVal,
      (∀ a, a ∈ patoms φ → a ∉ L → w a = v a) → peval w φ = true
  | [], v, φ, h, w, hw =>
      (peval_congr (v := w) (w := v) φ (fun a ha => hw a ha (by simp))).trans h
  | a :: L, v, φ, h, w, hw => by
      have h2 := Bool.and_eq_true .. |>.mp h
      have hcase : pcheck L (upd v a (w a)) φ = true := by
        cases hb : w a with
        | true => exact h2.1
        | false => exact h2.2
      refine pcheck_sound L (upd v a (w a)) φ hcase w ?_
      intro x hx hxL
      by_cases hxa : x = a
      · subst hxa; rw [upd_self]
      · rw [upd_other v a (w a) hxa]
        exact hw x hx (fun hmem => (List.mem_cons.mp hmem).elim hxa hxL)

/-- ⭐⭐ **El verificador.** `ptautCheck φ` **reduce**, así que una tautología concreta se descarga
con `by rfl`. Es lo que hace que un certificado de Herbrand sea comprobable **a máquina**. -/
def ptautCheck (φ : Formula) : Bool := pcheck (patoms φ) (fun _ => false) φ

theorem ptaut_of_check {φ : Formula} (h : ptautCheck φ = true) : PTaut φ :=
  fun w => pcheck_sound (patoms φ) _ φ h w (fun _ ha hn => absurd ha hn)

-- ============================================================
-- §2 · El corte sobre premisas DERIVABLES — la mitad fácil
-- ============================================================

/-- ⭐ **Un corte, y es admisible gratis**: `intro_impl` es un **constructor** de `Derives₀`.
⚠️ Esto **no es H3**: eliminar el corte es transformar la derivación para que no lo use; esto
sólo lo contrae. Pero es lo que deja al certificado descargar su propia lista `E`. -/
theorem derives0_discharge : ∀ (E : List Formula) (ψ : Formula),
    (E ⊢₀ ψ) → (∀ g, g ∈ E → ([] ⊢₀ g)) → [] ⊢₀ ψ
  | [], _, h, _ => h
  | g :: E', ψ, h, hE => by
      refine derives0_discharge E' ψ ?_ (fun x hx => hE x (List.Mem.tail _ hx))
      refine Derives₀.elim_impl _ g ψ (Derives₀.intro_impl _ _ _ ?_) ?_
      · exact Derives₀.weakening _ _ _ h (fun x hx => hx)
      · exact Derives₀.weakening _ _ _ (hE g (List.Mem.head _))
          (fun x hx => absurd hx List.not_mem_nil)

-- ============================================================
-- §3 · La disyunción finita
-- ============================================================

def disjOf : List Formula → Formula
  | [] => Formula.bottom
  | f :: fs => Formula.or f (disjOf fs)

/-- La **disyunción de Herbrand**: las instancias de `φ` en los términos del certificado. -/
def herbrandDisj (φ : Formula) (ts : List Term) : Formula :=
  disjOf (ts.map (fun t => substFormula 0 t φ))

/-- ⭐ De la disyunción finita al existencial: un `intro_ex` por término, bajo `elim_or`. -/
theorem derives0_ex_of_disj {φ : Formula} : ∀ (ts : List Term) (Γ : List Formula),
    (Γ ⊢₀ herbrandDisj φ ts) → Γ ⊢₀ Formula.ex φ
  | [], _, h => Derives₀.bot_elim _ _ h
  | t :: ts, Γ, h => by
      refine Derives₀.elim_or Γ (substFormula 0 t φ) (herbrandDisj φ ts) (Formula.ex φ) h ?_ ?_
      · exact Derives₀.intro_ex _ φ t (Derives₀.hyp _ _ (List.Mem.head _))
      · exact derives0_ex_of_disj ts _ (Derives₀.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §4 · Las instancias de la igualdad que el certificado puede usar
-- ============================================================

def eqReflAx (t : Term) : Formula := Formula.eq t t

def eqSymmAx (t u : Term) : Formula := Formula.impl (Formula.eq t u) (Formula.eq u t)

def eqTransAx (t u w : Term) : Formula :=
  Formula.impl (Formula.eq t u) (Formula.impl (Formula.eq u w) (Formula.eq t w))

def eqFuncAx (f : String) (pre post : List Term) (a b : Term) : Formula :=
  Formula.impl (Formula.eq a b)
    (Formula.eq (Term.func f (pre ++ a :: post)) (Term.func f (pre ++ b :: post)))

def eqAtomAx (p : String) (pre post : List Term) (a b : Term) : Formula :=
  Formula.impl (Formula.eq a b)
    (Formula.impl (Formula.atom p (pre ++ a :: post)) (Formula.atom p (pre ++ b :: post)))

/-- Lo que el certificado tiene derecho a poner en `E`. ⭐ Cerrado: sólo axiomas de la igualdad,
así que el certificado **no añade fuerza**, sólo la organiza. -/
inductive EqInstance : Formula → Prop where
  | refl (t : Term) : EqInstance (eqReflAx t)
  | symm (t u : Term) : EqInstance (eqSymmAx t u)
  | trans (t u w : Term) : EqInstance (eqTransAx t u w)
  | func (f : String) (pre post : List Term) (a b : Term) : EqInstance (eqFuncAx f pre post a b)
  | atom (p : String) (pre post : List Term) (a b : Term) : EqInstance (eqAtomAx p pre post a b)

/-- ⭐⭐ **Toda instancia admisible es DERIVABLE.** Aquí pagan `FOL.Eq0` y los dos constructores
`refl`/`subst` de `Derives₀`. -/
theorem derives0_of_eqInstance {g : Formula} (h : EqInstance g) : [] ⊢₀ g := by
  cases h with
  | refl t => exact Derives₀.refl _ t
  | symm t u =>
      exact Derives₀.intro_impl _ _ _ (derives0_eq_symm (Derives₀.hyp _ _ (List.Mem.head _)))
  | trans t u w =>
      refine Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ ?_)
      exact derives0_eq_trans
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))
  | func f pre post a b =>
      exact Derives₀.intro_impl _ _ _
        (derives0_eq_func_congr f pre post (Derives₀.hyp _ _ (List.Mem.head _)))
  | atom p pre post a b =>
      refine Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ ?_)
      exact derives0_atom_congr p pre post
        (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §5 · ⭐⭐⭐ EL CERTIFICADO, Y QUE SIRVE
-- ============================================================

/-- **El certificado de Herbrand para `∃x φ(x)`**: una lista de términos, una lista de instancias
de la igualdad, y la constancia de que la disyunción se sigue **proposicionalmente** de ellas.

⭐ Es **dato sintáctico**, y su segunda componente se comprueba con `ptautCheck` (§7). -/
def HerbrandCert (φ : Formula) (ts : List Term) (E : List Formula) : Prop :=
  And (∀ g, g ∈ E → EqInstance g)
      (∀ v : PVal, (∀ g, g ∈ E → peval v g = true) → peval v (herbrandDisj φ ts) = true)

/-- ⭐⭐⭐ **EL CERTIFICADO SIRVE**: de él sale la demostración, incondicionalmente y sin
`Classical.choice`.

La cadena es: `derives0_of_ptaut_ctx` (H2) da `E ⊢₀ disyunción`; `derives0_discharge` (§2) quita
`E` porque cada instancia es derivable (§4); `derives0_ex_of_disj` (§3) cierra el existencial. -/
theorem derives0_ex_of_cert {φ : Formula} {ts : List Term} {E : List Formula}
    (h : HerbrandCert φ ts E) : [] ⊢₀ Formula.ex φ := by
  refine derives0_ex_of_disj ts [] ?_
  refine derives0_discharge E _ (derives0_of_ptaut_ctx h.2) ?_
  exact fun g hg => derives0_of_eqInstance (h.1 g hg)

-- ============================================================
-- §6 · ⬜ H3, ENUNCIADA — y su CONSUMIDOR
-- ============================================================

/-- Fórmulas sin cuantificadores: la hipótesis sin la cual **Herbrand es falso**. -/
def QuantFree : Formula → Prop
  | .bottom => True
  | .atom _ _ => True
  | .eq _ _ => True
  | .impl a b => And (QuantFree a) (QuantFree b)
  | .and a b => And (QuantFree a) (QuantFree b)
  | .or a b => And (QuantFree a) (QuantFree b)
  | .forall _ => False
  | .ex _ => False

/-- ⬜⬜ **LA DEUDA H3 — la extracción del certificado.** Se **enuncia**, no se postula.

Es la mitad que necesita **eliminación de cortes**: de una derivación de `∃x φ(x)` hay que
*leer* los testigos, y eso exige que la derivación no use cortes —o transformarla para que no los
use—. ⛔ **No está hecha.** Ver `doc/PLAN-COMPLETITUD-FINITISTA.md` §5.4.

⚠️ `QuantFree φ` **no es decoración**: para `φ` con cuantificadores el enunciado es **falso**. -/
def HerbrandExtraction : Prop :=
  ∀ φ : Formula, QuantFree φ → ([] ⊢₀ Formula.ex φ) → ∃ ts E, HerbrandCert φ ts E

/-- ⭐ **El CONSUMIDOR, escrito antes que nada**: con H3, Herbrand es un **si y sólo si**.

🔑 La mitad `←` es incondicional (`derives0_ex_of_cert`); la hipótesis `h3` sólo paga la `→`.
*Una deuda se enuncia con su consumidor delante, para que la guarda salga del consumidor y no del
molde.* -/
theorem herbrand_iff (h3 : HerbrandExtraction) {φ : Formula} (hqf : QuantFree φ) :
    ([] ⊢₀ Formula.ex φ) ↔ ∃ ts E, HerbrandCert φ ts E :=
  ⟨fun h => h3 φ hqf h, fun ⟨_, _, hc⟩ => derives0_ex_of_cert hc⟩

-- ============================================================
-- §7 · ⚠️ CONTROL: certificados CONCRETOS, verificados por cómputo
-- ============================================================

-- ⚠️ Un teorema sobre certificados puede ser cierto y no tener ninguno. Estos dos los exhiben, y
-- la parte proposicional se comprueba **por `rfl`** — que es el punto de toda la vía H: *un
-- certificado finito y verificable*.

private def Px : Formula := Formula.atom "P" [Term.var 0]
private def c : Term := Term.func "c" []

/-- ⭐ **Caso puro**: `∃x (P(x) ∨ ¬P(x))`, con el testigo `c` y **sin** instancias ecuacionales. -/
theorem ex_tercio : [] ⊢₀ Formula.ex (Formula.or Px (neg Px)) := by
  refine derives0_ex_of_cert (ts := [c]) (E := []) ⟨fun _ hg => absurd hg List.not_mem_nil, ?_⟩
  intro v _
  exact ptaut_of_check (φ := herbrandDisj (Formula.or Px (neg Px)) [c]) (by rfl) v

/-- ⭐⭐ **Caso con IGUALDAD**, que es el que justifica la lista `E`: `∃x (x ≐ c)`. Su disyunción
de Herbrand es `c ≐ c`, que **no** es tautología proposicional —es un átomo— pero **sí** es un
axioma de la igualdad. *Ahí está, entera, la capa de §5.3 del plan.* -/
theorem ex_igualdad : [] ⊢₀ Formula.ex (Formula.eq (Term.var 0) c) := by
  refine derives0_ex_of_cert (ts := [c]) (E := [eqReflAx c]) ⟨?_, ?_⟩
  · intro g hg
    cases hg with
    | head => exact EqInstance.refl c
    | tail _ ht => exact absurd ht List.not_mem_nil
  · intro v hv
    have h1 : peval v (Formula.eq c c) = true := hv _ (List.Mem.head _)
    show (peval v (Formula.eq c c) || peval v (disjOf [])) = true
    simp [h1]

end FOL.Herbrand0

#print axioms FOL.Herbrand0.ptaut_of_check
#print axioms FOL.Herbrand0.derives0_discharge
#print axioms FOL.Herbrand0.derives0_of_eqInstance
#print axioms FOL.Herbrand0.derives0_ex_of_cert
#print axioms FOL.Herbrand0.herbrand_iff
#print axioms FOL.Herbrand0.ex_tercio
#print axioms FOL.Herbrand0.ex_igualdad
