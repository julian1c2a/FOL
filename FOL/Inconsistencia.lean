/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

> ## 🗑️ 2026‑10‑02 · REESCRITO: `FOL/MetaRules.lean` RETIRADO, y el diagnóstico de este módulo, al revés
>
> Este módulo vivía en `cuarentena/` y subió al build el 2026‑09‑23 (decisión E3 del cierre: «congelar un
> repositorio con su pieza de evidencia sin compilar es congelar una afirmación, no un hecho»). Su §1 era
> `inconsistencia_de_cualquier_solidez`: con el `axiom raa` en el entorno, **cualquier** teorema de solidez
> para `Derives` daba `False`. Se leyó como «la solidez de `Derives` es FALSA». **Era al revés: lo falso era
> `raa`.** Los 22 constructores de `Derives` son sólidos (§1 de abajo), así que los ENUNCIADOS de las cuatro
> meta‑reglas se refutan sin usarlas (§3). El propietario decidió retirarlas —«no hacemos uso de herramientas
> que no sean verdaderas»— y con ellas se fue aquel teorema, cuyo enunciado era falso: sólo se «demostraba»
> con `raa`. Registro de lo que decía y de su footprint, al final del fichero.
-/
import FOL.FOL
import FOL.Semantics
import FOL.Propositional0
import FOL.Soundness0
import FOL.Finitary0
import FOL.Fresh0

/-!
# Lo que `Derives` SÍ cumple, y los enunciados que NO tienen testigo

| § | qué | teorema |
|---|---|---|
| 1 | sin meta‑reglas, `Derives` **ES** `Derives₀`: `gen_rule` es admisible con una constante fresca | `derives_to_derives0` |
| 1 | y por tanto es **sólido** para Tarski | `derives_soundness` |
| 2 | ⛔ la propiedad de disyunción es FALSA para `Derives₀` (en el build desde el 2026‑09‑23, sin `Classical.choice` desde el 2026‑09‑27; la reescritura de hoy no la toca) | `derives0_no_disjunction_property` |
| 3 | ⛔ los ENUNCIADOS de `imp_intro`, `raa`, `or_elim` y `ex_elim`, refutados SIN usarlos | `imp_intro_refutable`, `raa_refutable`, `or_elim_refutable`, `ex_elim_refutable` |

⭐ Los cuatro de §3 y el de §2 dicen lo mismo con distinta forma: **un enunciado no tiene testigo**. Las tres
primeras refutaciones van por la vía FINITARIA (`derives_to_derives0` + `Finitary0`, sin `Classical.choice`);
`ex_elim` necesita un modelo de dos puntos, porque su premisa habla de TODO término y una valuación booleana no
distingue términos.

🔑 *La regla M‑11 —«un `axiom` que habita un inductivo prohíbe inducir sobre él»— se quedaba corta. El recursor
cubre por definición a TODO habitante: si una inducción demuestra que el inductivo es sólido, el axioma que lo
contradice es FALSO, y lo que hay que retirar es el axioma, no la inducción.*

**Ámbito**: esto habla de `Derives`, el cálculo de 22 constructores de `FOL/FOL.lean`. El sujeto de FOL sigue
siendo `Derives₀`; `Derives` queda como lo que es: `Derives₀` más `gen_rule`, que es admisible.
-/

open FOL.Metamath.Semantics

namespace FOL.Inconsistencia

-- ============================================================
-- §1 · Sin meta‑reglas, `Derives` ES `Derives₀`, y es sólido
-- ============================================================

section DerivesEsDerives0

open FOL.Eigenvariable FOL.Lift0 FOL.Fresh0

/-- El núcleo de `Henkin0.abs_neg_witness` sin el `neg`: abstraer una constante fresca recién
    sustituida devuelve la fórmula. -/
theorem abs_witness (c : String) (A : Formula) (hcA : Not (occursFormula c A)) :
    absFormula c 0 (substFormula 0 (Term.func c []) A) = A := by
  rw [absFormula_subst c A 0 0 (Nat.le_refl 0), absFormula_eq_lift c A 1 hcA]
  have hc : absTerm c 0 (Term.func c []) = Term.var 0 := by simp [absTerm]
  rw [hc, substFormula_lift_var A 0]

/-- 🏁 **Los 22 constructores de `Derives` se traducen a `Derives₀`.** Veintiuno son el mismo
    constructor; `gen_rule` —cuya premisa recorre TODO término— es **admisible**: basta su premisa en
    UNA constante fresca y `derives0_gen_fresh`. Medido en `ROBINSON_PlusPlus/sondeos/`
    `MetaReglasRefutables.lean` §4 antes de subirlo aquí (2026‑10‑02). -/
theorem derives_to_derives0 {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) : Γ ⊢₀ f := by
  induction h with
  | hyp Γ f hm => exact Derives₀.hyp Γ f hm
  | intro_impl Γ A B _ ih => exact Derives₀.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₀.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₀.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₀.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₀.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₀.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₀.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₀.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₀.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₀.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₀.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₀.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₀.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₀.weakening Γ Γ' f ih hsub
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact Derives₀.rewrite_at Γ f f' p sub sub' ih hget hrule heq
  | gen_rule Γ A _ ih =>
      obtain ⟨N1, h1⟩ := cst_bound_list Γ
      obtain ⟨N2, h2⟩ := cst_bound_formula A
      have hΓ := h1 (max N1 N2) (Nat.le_max_left _ _)
      have hA := h2 (max N1 N2) (Nat.le_max_right _ _)
      have h := derives0_gen_fresh (cst (max N1 N2)) hΓ (ih (Term.func (cst (max N1 N2)) []))
      rwa [abs_witness _ A hA] at h
  | dne_rule Γ A _ ih => exact Derives₀.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₀.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₀.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₀.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives₀.subst Γ t₁ t₂ f ih1 ih2

end DerivesEsDerives0

/-- 🏁 **La solidez de TARSKI de `Derives`.** Hasta el 2026‑10‑02 este fichero «demostraba» que este
    enunciado no tenía testigo; lo que no lo tenía era `raa`. -/
theorem derives_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) : satisfies Γ f :=
  derives0_soundness (derives_to_derives0 h)


-- ============================================================
-- §2 · ⛔⛔ La PROPIEDAD DE DISYUNCIÓN es FALSA para `Derives₀`
-- ============================================================

/-! ## ⛔⛔ Un enunciado que NO tiene testigo

⭐⭐ **Añadido el 2026‑09‑23, y la historia vale más que el teorema.** El propietario decidió ir a
por la **propiedad de disyunción** como último resultado de FOL. Se verificó el objetivo antes de
construir nada, y **no sobrevivió**: `Derives₀` es deducción natural **CLÁSICA** (`FOL/Derives0.lean`,
con `dne_rule`, `dne_schema` y `forall_not_ex_not` como constructores), y la propiedad de
disyunción es la marca de lo **INTUICIONISTA**.

⭐ **El contraejemplo estaba partido en dos mitades del propio árbol**, a dos módulos de
distancia, y nadie las había puesto juntas:

| pieza | dónde | qué da |
|---|---|---|
| `derives0_em_ctx` | `FOL/Propositional0.lean` | `Δ ⊢₀ A ∨ ¬A`, finitario, por `dne_rule` |
| `derives0_not_complete` | `FOL/Soundness0.lean` | `∃A, ⊬₀ A ∧ ⊬₀ ¬A`, dos modelos sobre `Unit` |

🔑 *No era un objetivo difícil: era un objetivo imposible.* Y la refutación costaba cinco
líneas con piezas que ya estaban compiladas — se habría encontrado **después** de abrir el frente.

⭐ **2026‑09‑27 (decisión del propietario tras la auditoría de constructividad):** la mitad de la
incompletitud ya no se toma de `Soundness0.derives0_not_complete` (modelos de Tarski en `Prop`, con
`Classical.choice`), sino de su gemelo FINITARIO `derives0_not_complete_fin`, de este módulo:
`Finitary0.derives0_not_P_fin` (valuación booleana `false`) y `derives0_not_negP_fin` (valuación
`true`). ⇒ `derives0_no_disjunction_property` pasa a `[propext, Quot.sound]`. La de `Soundness0`
se conserva (módulo congelado) como corolario de su ruta.

⭐ **Lo que SÍ es cierto** está probado en otro árbol: `PeanoRF/Calculus/Slash.lean`, por la barra
de Kleene, sobre `Derivesᵢ` = `Derives₀` **menos los tres constructores clásicos** y sobre esta
misma `Formula`. ⛔ No es importable desde aquí: su cadena baja a `ROBINSON_PlusPlus` y a `Peano`. -/

/-- La **propiedad de disyunción**, enunciada como `Prop` — el idioma del proyecto: una
obligación se enuncia, nunca se postula. -/
def DisjunctionProperty₀ : Prop :=
  ∀ A B : Formula, (([] : List Formula) ⊢₀ Formula.or A B) →
    Or (([] : List Formula) ⊢₀ A) (([] : List Formula) ⊢₀ B)

/-- `⊬₀ ¬P`, por la valuación BOOLEANA de `FOL.Finitary0` (`derives0_iff_derives2`, `ndToLK` y
`lkc_tval` con la valuación `true`; **sin** el Hauptsatz, que `Finitary0` no importa), no por un
modelo de Tarski: sin `Classical.choice`. -/
theorem derives0_not_negP_fin : Not (([] : List Formula) ⊢₀ neg (Formula.atom "P" [])) := by
  intro h
  have hc := FOL.NDtoLK0.ndToLK (FOL.Derives2.derives0_iff_derives2.mp h)
  rcases FOL.Finitary0.lkc_tval hc true
    (by intro _ hx; exact absurd hx (List.not_mem_nil)) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [FOL.Finitary0.tval, neg])
  | tail _ hm => exact absurd hm (List.not_mem_nil)

/-- `Derives₀` no decide `P`: el gemelo FINITARIO de `Soundness0.derives0_not_complete`. -/
theorem derives0_not_complete_fin :
    ∃ A : Formula, And (Not (([] : List Formula) ⊢₀ A)) (Not (([] : List Formula) ⊢₀ neg A)) :=
  ⟨_, FOL.Finitary0.derives0_not_P_fin, derives0_not_negP_fin⟩

/-- ⛔⛔ **Y es FALSA**, con el tercio excluso como contraejemplo. ⭐ Sin `Classical.choice` desde
el 2026‑09‑27 (decisión del propietario): la incompletitud se toma de la vía finitaria
(`derives0_not_complete_fin`) y no de la semántica de Tarski en `Prop`. -/
theorem derives0_no_disjunction_property : Not DisjunctionProperty₀ := by
  intro hdp
  obtain ⟨A, hA, hnA⟩ := derives0_not_complete_fin
  rcases hdp A (neg A) (FOL.Propositional0.derives0_em_ctx [] A) with h | h
  · exact hA h
  · exact hnA h


-- ============================================================
-- §3 · ⛔⛔ Los ENUNCIADOS de las cuatro meta‑reglas, refutados SIN usarlas
-- ============================================================

/-! ## ⛔⛔ Las cuatro meta‑reglas de `FOL/MetaRules.lean` eran FALSAS

Eran `axiom` porque su premisa es una **función de Lean** (`Γ ⊢ A → Γ ⊢ B`), una ocurrencia no positiva
que el kernel rechaza en un `inductive`. Ese mismo rasgo las hace falsas: si `Γ ⊬ A`, la función existe
**vacuamente**, y la regla fabrica una conclusión que la solidez de §1 prohíbe. Se enuncian aquí como `Prop`
y se refutan **sin postularlas**: valen para siempre, y dicen que no se pueden volver a postular sin hacer
inconsistente a Lean. Primera medición: `ROBINSON_PlusPlus/sondeos/MetaReglasRefutables.lean` (2026‑10‑02,
auditoría de la base, L1‑3 y R2‑4‑1). -/

/-- El enunciado de `imp_intro`: de una función `Γ ⊢ A → Γ ⊢ B`, la implicación objeto. -/
def ImpIntro : Prop := ∀ {Γ : List Formula} {A B : Formula}, (Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)

/-- El enunciado de `raa`: de una función `Γ ⊢ A → Γ ⊢ ⊥`, la negación. -/
def Raa : Prop := ∀ {Γ : List Formula} {A : Formula}, (Γ ⊢ A → Γ ⊢ Formula.bottom) → Γ ⊢ neg A

/-- El enunciado de `or_elim`, con las dos ramas como funciones de Lean. -/
def OrElim : Prop := ∀ {Γ : List Formula} {A B C : Formula}, (Γ ⊢ Formula.or A B) →
    (Γ ⊢ A → Γ ⊢ C) → (Γ ⊢ B → Γ ⊢ C) → Γ ⊢ C

/-- El enunciado de `ex_elim`, con la continuación como función de Lean sobre TODO término. -/
def ExElim : Prop := ∀ {Γ : List Formula} {A C : Formula}, (Γ ⊢ Formula.ex A) →
    (∀ t : Term, Γ ⊢ substFormula 0 t A → Γ ⊢ C) → Γ ⊢ C

/-- `⊬ P`, por la vía finitaria: lo que `Derives` prueba, `Derives₀` lo prueba. -/
theorem derives_not_P : Not (([] : List Formula) ⊢ Formula.atom "P" []) := fun h =>
  FOL.Finitary0.derives0_not_P_fin (derives_to_derives0 h)

/-- `⊬ ¬P`, ídem. -/
theorem derives_not_negP : Not (([] : List Formula) ⊢ neg (Formula.atom "P" [])) := fun h =>
  derives0_not_negP_fin (derives_to_derives0 h)

/-- 🏁 **`imp_intro` es FALSO**: como `⊬ P`, la premisa `⊢ P → ⊢ ⊥` vale vacuamente, y daría `⊢ ¬P`. -/
theorem imp_intro_refutable : Not ImpIntro := fun H =>
  derives_not_negP (H (Γ := []) (A := Formula.atom "P" []) (B := Formula.bottom)
    (fun h => absurd h derives_not_P))

/-- 🏁 **`raa` es FALSO**, por la misma razón. Es el detonador que este fichero usaba al revés. -/
theorem raa_refutable : Not Raa := fun H =>
  derives_not_negP (H (Γ := []) (A := Formula.atom "P" []) (fun h => absurd h derives_not_P))

/-- 🏁 **`or_elim` es FALSO**: `⊢ P ∨ ¬P` (tercio excluso), y como `⊬ P` y `⊬ ¬P`, las dos ramas valen
    vacuamente hacia `⊥` — que `Derives₀` no prueba. -/
theorem or_elim_refutable : Not OrElim := fun H =>
  FOL.Finitary0.derives0_consistent_fin (derives_to_derives0
    (H (Γ := []) (A := Formula.atom "P" []) (B := neg (Formula.atom "P" [])) (C := Formula.bottom)
      (derives0_to_derives (FOL.Propositional0.derives0_em_ctx [] (Formula.atom "P" [])))
      (fun h => absurd h derives_not_P) (fun h => absurd h derives_not_negP)))

/-- El modelo de dos puntos para `ex_elim`: `P` sólo vale en `true`, y todo término vale `false`. -/
private def MB : Model Bool := ⟨fun _ _ => false, fun _ ds => ds = [true]⟩
private def vB : Nat → Bool := fun _ => false
private def PA : Formula := Formula.atom "P" [Term.var 0]

/-- 🏁 **`ex_elim` es FALSO**: en `MB`, `∃x P(x)` es verdadera pero ningún TÉRMINO la testimonia
    (todos valen `false`), así que desde `[∃x P(x)]` no se deriva ningún `P(t)`, la continuación vale
    vacuamente hacia `⊥`, y `MB` refuta `⊥`. Una valuación booleana no distingue términos: aquí hace falta
    un modelo, y con él `Classical.choice`. -/
theorem ex_elim_refutable : Not ExElim := by
  intro hex
  have hΓ : contextSatisfies MB vB [Formula.ex PA] := by
    intro g hg
    cases hg with
    | head => simp [PA, MB, evalFormula, evalTerms, evalTerm, shiftEnv]
    | tail _ h => exact absurd h List.not_mem_nil
  have hterm : ∀ t : Term, evalTerm MB vB t = false := by
    intro t; cases t <;> simp [evalTerm, MB, vB]
  have hno : ∀ t : Term, Not ([Formula.ex PA] ⊢ substFormula 0 t PA) := by
    intro t ht
    have := derives_soundness ht Bool MB vB hΓ
    simp [PA, MB, substFormula, substTerms, substTerm, evalFormula, evalTerms] at this
    exact absurd this (by simpa [MB] using hterm t)
  exact derives_soundness
    (hex (Γ := [Formula.ex PA]) (A := PA) (C := Formula.bottom)
      (Derives.hyp _ _ (List.Mem.head _)) (fun t ht => absurd ht (hno t)))
    Bool MB vB hΓ

end FOL.Inconsistencia

/-! ## 🗑️ REGISTRO — lo que este fichero demostraba hasta el 2026‑10‑02

    inconsistencia_de_cualquier_solidez
        (solidez : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢ f) → satisfies Γ f) : False
      -- (1) `⊬ P`, por solidez con `Mfalse`;  (2) `raa` (premisa vacua) da `⊢ ¬P`;
      -- (3) solidez con `Mtrue` lo contradice.

(se cita sin la palabra clave a propósito: los controles cuentan declaraciones por texto), con footprint
`[propext, FOL.MetaRules.raa]`. Su enunciado es **FALSO**, y lo era también entonces: `derives_soundness`
es un testigo de su hipótesis, y la inducción que lo prueba no ve los axiomas. Lo que medía no era que `Derives` no fuera sólido, sino que `raa` no lo era. -/

/-! ## FOOTPRINT (medido el 2026‑10‑02) — `derives_to_derives0`, `derives0_no_disjunction_property`,
`imp_intro_refutable`, `raa_refutable` y `or_elim_refutable`: `[propext, Quot.sound]`, la vía finitaria,
sin `Classical.choice`. `derives_soundness` y `ex_elim_refutable`: `[propext, Classical.choice,
Quot.sound]`, porque pasan por los modelos de Tarski en `Prop`. Ningún axioma del proyecto: no queda
ninguno. Los vigila `../ROBINSON_PlusPlus/check-footprints.bash`. -/
#print axioms FOL.Inconsistencia.derives_to_derives0
#print axioms FOL.Inconsistencia.derives_soundness
#print axioms FOL.Inconsistencia.derives0_no_disjunction_property
#print axioms FOL.Inconsistencia.imp_intro_refutable
#print axioms FOL.Inconsistencia.raa_refutable
#print axioms FOL.Inconsistencia.or_elim_refutable
#print axioms FOL.Inconsistencia.ex_elim_refutable
