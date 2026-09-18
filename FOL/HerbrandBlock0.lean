/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Sequent0
-- @axiom_system: classical
-- @importance: high

import FOL.Sequent0

/-!
# `FOL.HerbrandBlock0` — Herbrand para un BLOQUE de existenciales

El enunciado‑titular de la vía H, tal como el plan lo promete
(`doc/PLAN-COMPLETITUD-FINITISTA.md` §5.1), lleva **barras de tupla**:

    ⊢₀ ∃x̄ φ(x̄)  ⟺  ∃ t̄₁…t̄ₙ : ⊢ᵖʳᵒᵖ φ(t̄₁) ∨ … ∨ φ(t̄ₙ)      (φ sin cuantificadores)

⚠️ Y lo que hay hoy (`FOL.Hauptsatz0.herbrand`, ADR‑052) es el caso **n = 1**: un solo `∃`.
Este módulo pone las tuplas.

## ⭐ La mitad que se paga aquí: ⟸, la que CONSUME el certificado

    derives0_exBlock_of_cert : HerbrandCertBlock n φ tss E → [] ⊢₀ exBlock n φ

**incondicional**, sin hipótesis y sin el Hauptsatz. Es el calco exacto de `derives0_ex_of_cert`
(ADR‑043) con tuplas en vez de términos. 🔑 *Primero el consumidor, después el molde*: la guarda
del certificado (`∀ ts ∈ tss, ts.length = n`) **sale de aquí**, no se inventa.

## ⭐ La pieza de riesgo, y por qué el índice va `n + k` y no `k + n`

Todo depende de poder sustituir **a través** del bloque:

    substFormula k t (exBlock n φ) = exBlock n (substFormula (n + k) (liftN n t) φ)

⚠️ Escrito `k + n`, el caso `k = 0` obliga a reescribir con `Nat.zero_add` en cada uso, porque
`0 + n` **no** es `n` por definición (`Nat.add` recurre en el segundo argumento). Escrito `n + k`,
`n + 0` **sí** reduce y el consumidor no paga nada. *El orden de una suma en un enunciado no es
cosmético: decide si el consumidor reescribe o no.* Es el primo del §14 de las trampas de notación.

## 🏁 La mitad ⟹ — **PAGADA el 2026‑09‑18** en `FOL.BlockExtraction0` (ADR‑064)

⭐⭐ Y la obstrucción de abajo era correcta en el QUÉ y falsa en el CUÁNTO: sí había que llevar
la tupla parcial, pero **`instB` YA la lleva** — `instB n us φ` con `us` más corta que `n`
devuelve el bloque PENDIENTE (`instB 2 [t] φ = exBlock 1 (φ[1 := t])`). No hubo que definir
ninguna función nueva.
🔑 *Antes de construir el dato que falta, mirar si una función que ya existe lo devuelve en su
caso degenerado.*

✅ **Y la estimación de abajo ACERTÓ**: ~350–450 l. estimadas, **≈400 medidas**. Es la primera de
esta serie que cae dentro de su propio rango — lo que se abarató fue la PIEZA conceptual (no
hubo `peelB` que escribir), no el total.

### Lo que se midió en su momento, y se conserva porque acertó en la forma

`HerbrandExtractionBlock` se **enuncia** como `Prop` con su consumidor (`herbrand_block_iff`), y
**no se postula**. ⛔ No sale de `herbrand` (n = 1) por composición: el cuerpo de un bloque de
altura ≥ 2 **no es** una fórmula sin cuantificadores, luego `herbrand` no aplica a él.

⚠️ Lo que haría falta, medido leyendo `FOL.Sequent0.lk0_herbrand`: **rehacer su inducción de 14
casos con un invariante más rico**. Hoy el invariante es «todo `d ∈ Δ` es sin cuantificadores **o**
es exactamente `Formula.ex φ`» (`Sequent0.lean:203`), y la salida lleva `ts : List Term`. Para
bloques, el caso `exR` baja de `exBlock (m+1) ψ` a `exBlock m ψ'` —con `ψ'` sin cuantificadores por
`quantFree_instB`, luego **el invariante SÍ se cierra**—, pero hay que llevar además la **tupla
parcial** acumulada, y la salida pasa a `List (List Term)`. ⇒ es un rediseño del enunciado, no una
envoltura: **~350–450 l.**, riesgo alto. No es F ni H; es de su tamaño.

## 📏 Footprint

`[propext, Quot.sound]` en todo. **Ni un `Classical.choice`** — como toda la vía H.
-/

namespace FOL.HerbrandBlock0

open FOL.Herbrand0
open FOL.Propositional0

-- ============================================================
-- §1 · El bloque, su instanciación, y la conmutación que la sostiene
-- ============================================================

/-- Un bloque de `n` existenciales delante de `φ`. -/
def exBlock : Nat → Formula → Formula
  | 0, φ => φ
  | n + 1, φ => Formula.ex (exBlock n φ)

/-- `liftTerm 0` iterado `n` veces. -/
def liftN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => liftN n (liftTerm 0 t)

/-- ⭐ Sustituir **a través** de un bloque. El índice es `n + k` a propósito: ver la cabecera. -/
theorem subst_exBlock : ∀ (n : Nat) (φ : Formula) (k : Nat) (t : Term),
    substFormula k t (exBlock n φ) = exBlock n (substFormula (n + k) (liftN n t) φ)
  | 0, φ, k, t => by
      show substFormula k t φ = substFormula (0 + k) t φ
      rw [Nat.zero_add]
  | n + 1, φ, k, t => by
      show Formula.ex (substFormula (k + 1) (liftTerm 0 t) (exBlock n φ))
           = Formula.ex (exBlock n (substFormula (n + 1 + k) (liftN n (liftTerm 0 t)) φ))
      rw [subst_exBlock n φ (k + 1) (liftTerm 0 t),
          show n + (k + 1) = n + 1 + k from by omega]

/-- El bloque **instanciado** por una tupla: se pela de fuera adentro. -/
def instB : Nat → List Term → Formula → Formula
  | 0, _, φ => φ
  | n + 1, [], φ => exBlock (n + 1) φ
  | n + 1, t :: ts, φ => instB n ts (substFormula n (liftN n t) φ)

/-- Instanciar no introduce cuantificadores. -/
theorem quantFree_instB : ∀ (n : Nat) (ts : List Term) (φ : Formula),
    ts.length = n → QuantFree φ → QuantFree (instB n ts φ)
  | 0, _, _, _, h => h
  | n + 1, [], _, hl, _ => absurd hl.symm (Nat.succ_ne_zero n)
  | n + 1, t :: ts, φ, hl, hq =>
      quantFree_instB n ts _ (Nat.succ.inj hl)
        (FOL.Sequent0.quantFree_subst φ n (liftN n t) hq)

/-- ⭐⭐ **Del bloque INSTANCIADO al bloque existencial**: un `intro_ex` por componente. -/
theorem derives0_exBlock_of_inst : ∀ (n : Nat) (ts : List Term) (φ : Formula) (Γ : List Formula),
    ts.length = n → (Γ ⊢₀ instB n ts φ) → Γ ⊢₀ exBlock n φ
  | 0, _, _, _, _, h => h
  | n + 1, [], _, _, hl, _ => absurd hl.symm (Nat.succ_ne_zero n)
  | n + 1, t :: ts, φ, Γ, hl, h => by
      refine Derives₀.intro_ex Γ (exBlock n φ) t ?_
      rw [subst_exBlock n φ 0 t]
      exact derives0_exBlock_of_inst n ts (substFormula (n + 0) (liftN n t) φ) Γ
        (Nat.succ.inj hl) h

-- ============================================================
-- §2 · La disyunción de Herbrand, ahora sobre TUPLAS
-- ============================================================

def herbrandDisjBlock (n : Nat) (φ : Formula) (tss : List (List Term)) : Formula :=
  disjOf (tss.map (fun ts => instB n ts φ))

/-- ⭐ De la disyunción finita de instancias al bloque existencial. Calco de
`derives0_ex_of_disj` con tuplas. -/
theorem derives0_exBlock_of_disj (n : Nat) (φ : Formula) :
    ∀ (tss : List (List Term)) (Γ : List Formula),
      (∀ ts, ts ∈ tss → ts.length = n) →
      (Γ ⊢₀ herbrandDisjBlock n φ tss) → Γ ⊢₀ exBlock n φ
  | [], _, _, h => Derives₀.bot_elim _ _ h
  | ts :: rest, Γ, hlen, h => by
      refine Derives₀.elim_or Γ (instB n ts φ) (herbrandDisjBlock n φ rest) (exBlock n φ) h ?_ ?_
      · exact derives0_exBlock_of_inst n ts φ _ (hlen ts (List.Mem.head _))
          (Derives₀.hyp _ _ (List.Mem.head _))
      · exact derives0_exBlock_of_disj n φ rest _ (fun x hx => hlen x (List.Mem.tail _ hx))
          (Derives₀.hyp _ _ (List.Mem.head _))

-- ============================================================
-- §3 · El CERTIFICADO de bloque, y que SIRVE
-- ============================================================

/-- Lo que hay que exhibir: las tuplas (todas de longitud `n`), las instancias de igualdad que se
usan, y que la disyunción es **tautología proposicional módulo `E`**. -/
def HerbrandCertBlock (n : Nat) (φ : Formula) (tss : List (List Term)) (E : List Formula) : Prop :=
  And (∀ ts, ts ∈ tss → ts.length = n)
    (And (∀ g, g ∈ E → EqInstance g)
      (∀ v : PVal, (∀ g, g ∈ E → peval v g = true) →
        peval v (herbrandDisjBlock n φ tss) = true))

/-- ⭐⭐⭐ **EL CERTIFICADO DE BLOQUE SIRVE**: de él sale la demostración, incondicionalmente y
sin el Hauptsatz. -/
theorem derives0_exBlock_of_cert {n : Nat} {φ : Formula} {tss : List (List Term)}
    {E : List Formula} (h : HerbrandCertBlock n φ tss E) : [] ⊢₀ exBlock n φ := by
  refine derives0_exBlock_of_disj n φ tss [] h.1 ?_
  refine derives0_discharge E _ (derives0_of_ptaut_ctx h.2.2) ?_
  exact fun g hg => derives0_of_eqInstance (h.2.1 g hg)

-- ============================================================
-- §4 · La mitad ⟹, ENUNCIADA como deuda y con su consumidor delante
-- ============================================================

/-- 🏁 La extracción para bloques. **PAGADA el 2026-09-18** (ADR-064). Testigo incondicional:
**`FOL.BlockExtraction0.herbrand_extraction_block`**.

Se sigue **enunciando** como `Prop` porque su consumidor (`herbrand_block_iff`) la toma como
hipótesis. ⚠️ La cabecera del módulo ya decía «PAGADA» mientras esta línea seguía diciendo ⬜:
**el mismo fichero se contradecía a sí mismo**, y lo cazó [G.1] (ADR-072). -/
def HerbrandExtractionBlock : Prop :=
  ∀ (n : Nat) (φ : Formula), QuantFree φ → ([] ⊢₀ exBlock n φ) →
    ∃ tss E, HerbrandCertBlock n φ tss E

/-- ⭐ **El CONSUMIDOR, escrito antes que el molde**: con la extracción, Herbrand de bloque es un
**si y sólo si**. 🔑 La mitad `←` es incondicional; la hipótesis sólo paga la `→`. -/
theorem herbrand_block_iff (h : HerbrandExtractionBlock) {n : Nat} {φ : Formula}
    (hqf : QuantFree φ) :
    Iff ([] ⊢₀ exBlock n φ) (∃ tss E, HerbrandCertBlock n φ tss E) :=
  ⟨fun hd => h n φ hqf hd, fun ⟨_, _, hc⟩ => derives0_exBlock_of_cert hc⟩

-- ============================================================
-- §5 · ⚠️ CONTROL: un certificado de BLOQUE concreto, y de los que llevan igualdad
-- ============================================================

private def c : Term := Term.func "c" []

/-- ⭐⭐ `∃x ∃y (x ≐ y)`, con la tupla `[c, c]`. Su instancia es `c ≐ c`, que **no** es tautología
proposicional —es un átomo— pero **sí** es un axioma de la igualdad: por eso el certificado lleva
`E`. Es el control de que el bloque funciona con `n = 2` y con igualdad a la vez. -/
theorem ex_bloque_igualdad :
    [] ⊢₀ exBlock 2 (Formula.eq (Term.var 1) (Term.var 0)) := by
  refine derives0_exBlock_of_cert (n := 2) (tss := [[c, c]]) (E := [eqReflAx c]) ⟨?_, ?_, ?_⟩
  · intro ts hts
    cases hts with
    | head => rfl
    | tail _ ht => exact absurd ht (List.not_mem_nil)
  · intro g hg
    cases hg with
    | head => exact EqInstance.refl c
    | tail _ ht => exact absurd ht (List.not_mem_nil)
  · intro v hv
    have hc : peval v (eqReflAx c) = true := hv _ (List.Mem.head _)
    show peval v (Formula.or (Formula.eq c c) Formula.bottom) = true
    show (peval v (Formula.eq c c) || peval v Formula.bottom) = true
    simp only [eqReflAx] at hc
    simp [hc]

end FOL.HerbrandBlock0

#print axioms FOL.HerbrandBlock0.subst_exBlock
#print axioms FOL.HerbrandBlock0.derives0_exBlock_of_inst
#print axioms FOL.HerbrandBlock0.derives0_exBlock_of_disj
#print axioms FOL.HerbrandBlock0.derives0_exBlock_of_cert
#print axioms FOL.HerbrandBlock0.ex_bloque_igualdad
