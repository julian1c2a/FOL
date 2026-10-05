/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Canonical0
-- @axiom_system: classical
-- @importance: high

import FOL.Canonical0

/-!
# `FOL.Skolem0` — 🏁 el axioma de SKOLEM es **CONSERVATIVO**, con término de argumentos fijos

    skolem_conservative₀ : c fresco para Γ, A y φ →
                          (skolemAxT c t̄ A :: Γ) ⊢₀ φ  →  Γ ⊢₀ φ
    henkin_conservative₀ : el caso `t̄ = []`, por la vía SINTÁCTICA y sin `Classical.choice`

⭐ **2026‑09‑27 (decisión del propietario tras la auditoría de constructividad):**
`henkin_conservative₀` deja de ser el corolario `t̄ = []` de `skolem_conservative₀` y se prueba
dentro del cálculo, con el paso de Henkin en positivo (`Henkin0.henkin_step_derives`), `ctx_split`
y `dne_rule`: `[propext, Quot.sound]`. `skolem_conservative₀` conserva la ruta semántica (abajo).

## ⭐ Y `t̄` NO necesita ser fresco — ésa es la medición que abarata todo

Con argumentos **fijos**, la interpretación del símbolo nuevo puede ser **constante**
(`updateFunc M c (fun _ => w)`), y entonces `c(t̄)` vale lo mismo **sean cuales sean los
argumentos** — incluso si mencionan `c`. ⇒ no hace falta ninguna correspondencia entre la lista de
argumentos y el entorno De Bruijn, que es lo caro del caso general.
🔑 *Cuando la interpretación que se construye es constante, los argumentos dejan de ser un problema.*

## ⛔ Y un bloqueo que yo había declarado y NO existe

ADR‑056 §5 dijo que faltaba «suministro de símbolos frescos **n‑arios**». **Falso, y medido**: en
este árbol `Term.func` toma un símbolo (`List Char`; hasta D7, 2026‑10‑05, un `String`) y una lista
de **cualquier** longitud, así que **la aridad no está en el tipo**; y `occursFormula c f` mira el
**nombre**, no la aridad. ⇒ `cst : Nat → List Char` (`FOL/Fresh0.lean`) ya da infinitos símbolos de
Skolem de cualquier aridad.
⚠️ Van **cuatro** obstrucciones mías declaradas y luego refutadas en dos días (cuenta del
2026‑09‑17, ADR‑059).

## ⭐⭐ El puente que NO existía, y era el bloqueo medido

Una medición externa señaló el bloqueo de Skolem, y acertó: **no había ningún lema que conectara
`occursFormula` (sintáctico, `FOL/Eigenvariable.lean`) con `evalFormula` (semántico,
`FOL/Semantics.lean`)**. Sin él, la frescura de un símbolo no dice **nada** semánticamente: se
puede decir «`c` no aparece en `f`» y no poder concluir que reinterpretar `c` no cambia el valor
de `f`. Ésa es la pieza:

    evalFormula_updateFunc : ¬ occursFormula c f →
      (evalFormula (updateFunc M c F) v f ↔ evalFormula M v f)

📏 **No depende de ningún axioma.** Setenta líneas, net‑0, y es reutilizable por cualquier
argumento de frescura que quiera decir algo semántico — no sólo por Skolem.

## ⭐ Y el axioma de Skolem YA ESTABA ESCRITO: es `henkinAx`

    henkinAx c A = (∃A) ⇒ A[c]            -- FOL.Henkin0.henkinAx

Es literalmente el axioma de Skolem para un existencial cuyo cuerpo no tiene más variables libres.
⇒ no hay que definir nada nuevo: *antes de construir, buscar*.
⚠️ Lo que el proyecto tenía sobre él era `henkin_step_consistent₀` (ADR‑037): que el paso **preserva
la CONSISTENCIA**. La conservatividad es **estrictamente más fuerte** y es lo que hace falta para
decir que skolemizar no inventa teoremas.
⭐ **Precisión del 2026‑09‑27**: más fuerte es el ENUNCIADO, no la maquinaria. Escrito en
POSITIVO, el paso de Henkin (`Henkin0.henkin_step_derives`) transforma derivaciones de `⊥` desde
`S ∪ {H}` en derivaciones de `⊥` desde `S`; con `¬φ` dentro de `S` da la conservatividad del caso
constante sin pasar por la semántica, y así se prueba hoy `henkin_conservative₀`
(`henkin_step_consistent₀` es ahora corolario de `henkin_step_derives`).

## ⭐ La ruta, y dónde paga cada pieza

    (henkinAx c A :: Γ) ⊢₀ φ
      --[ derives0_soundness ]-->  vale en TODO modelo del contexto ampliado
      --[ se EXPANDE M en `c` con un testigo ]-->  ese modelo existe
      --[ evalFormula_updateFunc, dos veces ]-->  Γ ⊨ φ         (c fresco para Γ y para φ)
      --[ completeness₀ ]-->  Γ ⊢₀ φ

⚠️ El testigo se elige con `by_cases` sobre si `∃A` vale en `M`, y en la rama negativa el axioma se
cumple **vacuamente** — por el propio lema de coincidencia. *La frescura se usa tres veces y cada
una hace un trabajo distinto: en Γ para transportar el contexto, en A para elegir el testigo, y en
φ para traer la conclusión de vuelta.*

⚠️ Es la ruta de `skolem_conservative₀` (el diagrama la escribe con `henkinAx`, su caso `t̄ = []`).
Desde el 2026‑09‑27 `henkin_conservative₀` **no** la toma: va por `henkin_step_derives` (ver la
cabecera).

## 📏 Footprint (al día el 2026‑09‑27)

`updateFunc`, `evalTerm_updateFunc`, `evalFormula_updateFunc`, `evalTerm_new` y `evalTerm_newT`
**sin ningún axioma**.
⭐ `henkin_conservative₀`: **`[propext, Quot.sound]`**, sin `Classical.choice` (vía sintáctica).
`skolem_conservative₀`: `[propext, Classical.choice, Quot.sound]`. El `Classical.choice` tiene tres
procedencias, y las tres son de la ruta SEMÁNTICA:

* la elección del testigo aquí mismo (`by_cases` sobre `∃d`, `Exists.choose`): es la forma
  semántica del axioma, y en esta ruta es esencial: el enunciado semántico que usa —todo modelo se
  expande con UN testigo `w` que valida `(∃A) → A[w]`, el «bebedor dual»— implica el tercio excluso
  (medido: `auditoria/constructividad-2026-09-27/experimentos/exp-esencial/E6b_Henkin.lean`; con
  prefijo, la expansión implica AC y AC el tercio excluso, `E6_Skolem.lean`, sobre `SkolemN0.skF`);
* `derives0_soundness` (`FOL.Soundness0`): la semántica de Tarski en `Prop`;
* `completeness₀` (`FOL.Canonical0`): el lema de la verdad sobre un maximal ARBITRARIO y su
  `byContradiction` final.

⚠️ **Rectificado el 2026‑09‑27.** Este párrafo decía que el de `completeness₀` era «el **WKL** de
siempre», con la tesis de `PLAN-COMPLETITUD-FINITISTA.md` §6.3 (el `if IsConsistent₀` de
Lindenbaum). En Lean es falso: `lindenbaum_lemma₀` y `henkin_completion₀` son `[propext, Quot.sound]`
(`auditoria/constructividad-2026-09-27/`). El WKL nombra la FUERZA lógica de la completitud
(⇔ WKL₀ sobre RCA₀), no el sitio del `choice`. Y le atribuía el mismo footprint a
`henkin_conservative₀`, que ya no lleva `Classical.choice`.
⛔ Vía W, no vía H, salvo el caso Henkin. ⚠️ El enunciado es sintáctico: que el caso `t̄ ≠ []` tenga
prueba sin `Classical.choice` (Herbrand, o el segundo teorema ε) es HIPÓTESIS.

## 🏁 El axioma bajo un PREFIJO de universales — **HECHO en `FOL.SkolemN0`**

🏁 `FOL.SkolemN0.skolem_conservative_n₀` lo cierra, y la pieza que aquí se dio por inexistente
—reconstruir el entorno desde una lista— resultó no hacer falta: `envPush` se **construye** con
`shiftEnv` y las dos ecuaciones del paso inductivo salen `rfl`.
⚠️ Lo de abajo decía «**MEDIDO** que no existe nada de eso», y la falsedad iba etiquetada
**MEDIDO**. Se deja como historial.

## ⬜~~Lo que falta: el axioma bajo un PREFIJO de universales~~ (refutado)

    ∀y₁…∀y_k ( (∃x A) → A[x := c(y₁,…,y_k)] )

Ahí el testigo **depende de la tupla**, luego `F : List D → D` ya no puede ser constante y hay que
relacionar la lista de argumentos con el entorno De Bruijn bajo `k` `shiftEnv` anidados.
⬜ **MEDIDO que no existe nada de eso**: `FOL/Semantics.lean` tiene `shiftEnv`/`updateEnv` y sus
conmutaciones, pero **nada iterado `k` veces** ni que reconstruya un entorno desde una lista.
⬜ ~200 l., riesgo **medio**, y el riesgo está entero en esa pieza. El prefijo `∀ⁿ` en sí es copia
de `exBlock`/`subst_exBlock` (`FOL/HerbrandBlock0.lean`), ~40 l.
-/

namespace FOL.Skolem0

open FOL.Metamath.Semantics
open FOL.Eigenvariable
open FOL.Henkin0

/-- Reinterpretar UN símbolo de función, dejando todo lo demás igual.
⚠️ El `if f = c` usa la igualdad decidible de `List Char`, que **no** trae `Classical.choice`
(`evalTerm_updateFunc` y `evalFormula_updateFunc` no dependen de ningún axioma). Hasta D7
(2026‑10‑05, ADR‑129 de RPP) usaba `String.decEq`, que tampoco lo traía: lo que lo traía era
DESCOMPONER un `String`, no compararlo
(`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §7). Precisado el 2026‑09‑27 (auditoría
de constructividad): en v4.31 lo trae DECODIFICAR el UTF‑8 (`String.toList` y afines), no el tipo;
comparar y recorrer los bytes no lo trae. -/
def updateFunc {D : Type} (M : Model D) (c : List Char) (F : List D → D) : Model D where
  func := fun f ds => if f = c then F ds else M.func f ds
  rel := M.rel

-- ── ⭐⭐ EL LEMA DE COINCIDENCIA ─────────────────────────────────────────────
mutual
theorem evalTerm_updateFunc {D : Type} (M : Model D) (c : List Char) (F : List D → D) :
    ∀ (t : Term) (v : Nat → D), Not (occursTerm c t) →
      evalTerm (updateFunc M c F) v t = evalTerm M v t
  | .var _, _, _ => rfl
  | .func s ts, v, h => by
      have hs : Not (s = c) := fun he => h (Or.inl he)
      show (if s = c then F (evalTerms (updateFunc M c F) v ts)
            else M.func s (evalTerms (updateFunc M c F) v ts)) = M.func s (evalTerms M v ts)
      rw [if_neg hs, evalTerms_updateFunc M c F ts v (fun ht => h (Or.inr ht))]

theorem evalTerms_updateFunc {D : Type} (M : Model D) (c : List Char) (F : List D → D) :
    ∀ (ts : List Term) (v : Nat → D), Not (occursTerms c ts) →
      evalTerms (updateFunc M c F) v ts = evalTerms M v ts
  | [], _, _ => rfl
  | t :: ts, v, h => by
      show evalTerm (updateFunc M c F) v t :: evalTerms (updateFunc M c F) v ts
           = evalTerm M v t :: evalTerms M v ts
      rw [evalTerm_updateFunc M c F t v (fun ht => h (Or.inl ht)),
          evalTerms_updateFunc M c F ts v (fun ht => h (Or.inr ht))]
end

theorem evalFormula_updateFunc {D : Type} (M : Model D) (c : List Char) (F : List D → D) :
    ∀ (f : Formula) (v : Nat → D), Not (occursFormula c f) →
      Iff (evalFormula (updateFunc M c F) v f) (evalFormula M v f) := by
  intro f
  induction f with
  | bottom => intro _ _; exact Iff.rfl
  | atom p ts =>
      intro v h
      show Iff (M.rel p (evalTerms (updateFunc M c F) v ts)) (M.rel p (evalTerms M v ts))
      rw [evalTerms_updateFunc M c F ts v h]
  | eq t u =>
      intro v h
      show Iff (evalTerm (updateFunc M c F) v t = evalTerm (updateFunc M c F) v u)
               (evalTerm M v t = evalTerm M v u)
      rw [evalTerm_updateFunc M c F t v (fun ht => h (Or.inl ht)),
          evalTerm_updateFunc M c F u v (fun ht => h (Or.inr ht))]
  | impl a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx hy => (ihb v (fun ht => h (Or.inr ht))).mp
          (hx ((iha v (fun ht => h (Or.inl ht))).mpr hy)))
        (fun hx hy => (ihb v (fun ht => h (Or.inr ht))).mpr
          (hx ((iha v (fun ht => h (Or.inl ht))).mp hy)))
  | and a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx => ⟨(iha v (fun ht => h (Or.inl ht))).mp hx.1,
                    (ihb v (fun ht => h (Or.inr ht))).mp hx.2⟩)
        (fun hx => ⟨(iha v (fun ht => h (Or.inl ht))).mpr hx.1,
                    (ihb v (fun ht => h (Or.inr ht))).mpr hx.2⟩)
  | or a b iha ihb =>
      intro v h
      exact Iff.intro
        (fun hx => hx.imp (iha v (fun ht => h (Or.inl ht))).mp
                          (ihb v (fun ht => h (Or.inr ht))).mp)
        (fun hx => hx.imp (iha v (fun ht => h (Or.inl ht))).mpr
                          (ihb v (fun ht => h (Or.inr ht))).mpr)
  | «forall» a ih =>
      intro v h
      exact Iff.intro
        (fun hx d => (ih (shiftEnv v d) h).mp (hx d))
        (fun hx d => (ih (shiftEnv v d) h).mpr (hx d))
  | ex a ih =>
      intro v h
      exact Iff.intro
        (fun hx => hx.elim (fun d hd => ⟨d, (ih (shiftEnv v d) h).mp hd⟩))
        (fun hx => hx.elim (fun d hd => ⟨d, (ih (shiftEnv v d) h).mpr hd⟩))

/-- El símbolo nuevo se interpreta como el testigo elegido. -/
theorem evalTerm_new {D : Type} (M : Model D) (c : List Char) (w : D) (v : Nat → D) :
    evalTerm (updateFunc M c (fun _ => w)) v (Term.func c []) = w := by
  show (if c = c then w else M.func c (evalTerms (updateFunc M c (fun _ => w)) v [])) = w
  rw [if_pos rfl]

-- ── 🏁 LA CONSERVATIVIDAD ───────────────────────────────────────────────────

/-- El axioma de Skolem con un término de argumentos **fijos**: `(∃A) ⇒ A[c(t̄)]`.
Con `t̄ = []` es exactamente `henkinAx`. -/
def skolemAxT (c : List Char) (ts : List Term) (A : Formula) : Formula :=
  Formula.impl (Formula.ex A) (substFormula 0 (Term.func c ts) A)

/-- ⭐ Con argumentos FIJOS, la interpretación del símbolo nuevo puede ser **constante**, y por eso
el valor no depende de `ts`. Es lo que hace que no haga falta ninguna correspondencia entre la
lista de argumentos y el entorno De Bruijn. -/
theorem evalTerm_newT {D : Type} (M : Model D) (c : List Char) (w : D) (v : Nat → D)
    (ts : List Term) : evalTerm (updateFunc M c (fun _ => w)) v (Term.func c ts) = w := by
  show (if c = c then w
        else M.func c (evalTerms (updateFunc M c (fun _ => w)) v ts)) = w
  rw [if_pos rfl]

/-- 🏁🏁 **El axioma de Skolem no inventa teoremas** — con el término de Skolem aplicado a
argumentos **cualesquiera**. Si `c` es fresco para el contexto, el cuerpo y la conclusión, todo lo
que se demuestra con él se demuestra sin él.

⭐ `ts` **no** necesita ser fresco: como la interpretación de `c` es constante, `c(t̄)` vale lo
mismo sean cuales sean los argumentos — incluso si mencionan `c`. -/
theorem skolem_conservative₀ {c : List Char} {A φ : Formula} {Γ : List Formula} {ts : List Term}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (skolemAxT c ts A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ := by
  refine FOL.Canonical0.completeness₀ ?_
  intro D M v hctx
  -- ⭐ el núcleo: con CUALQUIER testigo que haga válido el axioma, la conclusión vuelve
  have step : ∀ (w : D), evalFormula (updateFunc M c (fun _ => w)) v (skolemAxT c ts A) →
      evalFormula M v φ := by
    intro w hax
    have hM' : ∀ g, g ∈ (skolemAxT c ts A :: Γ) →
        evalFormula (updateFunc M c (fun _ => w)) v g := by
      intro g hg
      cases hg with
      | head => exact hax
      | tail _ hm => exact (evalFormula_updateFunc M c _ g v (hΓ g hm)).mpr (hctx g hm)
    exact (evalFormula_updateFunc M c _ φ v hφ).mp
      (FOL.Metamath.Soundness0.derives0_soundness h D (updateFunc M c (fun _ => w)) v hM')
  by_cases hEx : ∃ d, evalFormula M (shiftEnv v d) A
  · -- hay testigo en `M`: se elige, y el axioma vale
    refine step hEx.choose ?_
    intro _
    refine (eval_substFormula_zero _ v (Term.func c ts) A).mpr ?_
    rw [evalTerm_newT M c hEx.choose v ts]
    exact (evalFormula_updateFunc M c _ A (shiftEnv v hEx.choose) hA).mpr hEx.choose_spec
  · -- no hay testigo: el axioma vale VACUAMENTE, y eso también lo da la coincidencia
    refine step (v 0) ?_
    intro hex
    exact absurd
      (hex.elim (fun d hd => ⟨d, (evalFormula_updateFunc M c _ A (shiftEnv v d) hA).mp hd⟩)) hEx

/-- 🏁 El caso de ADR‑056 (constante, `henkinAx c A = skolemAxT c [] A`), **por la vía SINTÁCTICA
y sin `Classical.choice`** (2026‑09‑27, decisión del propietario tras la auditoría de
constructividad): `(H :: Γ) ⊢₀ φ` da `(H :: ¬φ :: Γ) ⊢₀ ⊥`; el paso de Henkin en positivo
(`Henkin0.henkin_step_derives`) quita `H` porque `c` es fresca en `Γ`, `A` y `φ`; y `ctx_split` más
`dne_rule` quitan `¬φ`. Hasta entonces era el corolario `t̄ = []` de `skolem_conservative₀`, que
pasa por la completitud y por elegir el testigo en un modelo. -/
theorem henkin_conservative₀ {c : List Char} {A φ : Formula} {Γ : List Formula}
    (hΓ : ∀ g, g ∈ Γ → Not (occursFormula c g))
    (hA : Not (occursFormula c A))
    (hφ : Not (occursFormula c φ))
    (h : (henkinAx c A :: Γ) ⊢₀ φ) : Γ ⊢₀ φ := by
  -- (H :: ¬φ :: Γ) ⊢₀ ⊥
  have hbot : (henkinAx c A :: neg φ :: Γ) ⊢₀ Formula.bottom := by
    refine Derives₀.elim_impl _ φ Formula.bottom
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) ?_
    refine Derives₀.weakening _ _ _ h ?_
    intro x hx
    cases hx with
    | head => exact List.Mem.head _
    | tail _ hx' => exact List.Mem.tail _ (List.Mem.tail _ hx')
  -- quitar H: `c` es fresca en Γ ∪ {¬φ}
  have hS : DerivesSet₀ (fun x => Or (x ∈ Γ) (x = neg φ)) Formula.bottom := by
    refine henkin_step_derives c A ?_ hA ⟨_, ?_, hbot⟩
    · intro g hg
      cases hg with
      | inl hm => exact hΓ g hm
      | inr he => subst he; exact fun ho => ho.elim hφ (fun h => h)
    · intro x hx
      cases hx with
      | head => exact Or.inr rfl
      | tail _ hx' =>
        cases hx' with
        | head => exact Or.inl (Or.inr rfl)
        | tail _ hx'' => exact Or.inl (Or.inl hx'')
  -- quitar ¬φ del contexto finito, sin decidir la igualdad, y cerrar con `dne_rule`
  obtain ⟨Δ, hΔ, hD⟩ := hS
  obtain ⟨Δ', hΔ', hsub⟩ := ctx_split (H := neg φ) Δ hΔ
  have hnn : Δ' ⊢₀ neg (neg φ) := Derives₀.intro_impl _ _ _ (Derives₀.weakening _ _ _ hD hsub)
  exact Derives₀.weakening _ _ _ (Derives₀.dne_rule _ _ hnn) hΔ'

end FOL.Skolem0

#print axioms FOL.Skolem0.evalTerm_updateFunc
#print axioms FOL.Skolem0.evalFormula_updateFunc
#print axioms FOL.Skolem0.evalTerm_new
#print axioms FOL.Skolem0.skolem_conservative₀
#print axioms FOL.Skolem0.henkin_conservative₀
