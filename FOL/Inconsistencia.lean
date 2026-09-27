/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

> ## ⭐⭐ 2026‑09‑23 · ESTE MÓDULO SUBE AL BUILD (decisión E3 del cierre)
>
> Vivía en `cuarentena/`, que **no se compila**. Y `cuarentena/README.md` —en su nota de cabecera,
> que atribuye la lección a su §7— dice, casi con esas
> palabras, que un directorio no compilado es **cómo un `axiom` falso sobrevivió ochenta días**.
> ⇒ la **evidencia** de que la solidez de `Derives` es falsa **no la verificaba ningún build**.
>
> 🔑 *Congelar un repositorio con su pieza de evidencia sin compilar es congelar una
> afirmación, no un hecho.*
>
> ⚠️ **Y es seguro tenerlo en la librería principal**: el teorema es **CONDICIONAL**
> —`(solidez : …) → False`—, no afirma `False`. Lo que dice es que **ese enunciado no tiene
> testigo**, y por eso no hay nada que aislar.
-/
import FOL.FOL
import FOL.MetaRules
import FOL.Semantics
import FOL.Propositional0
import FOL.Soundness0
import FOL.Finitary0

/-!
# ⛔⛔ La EVIDENCIA COMPILADA: `Derives` no admite teorema de solidez

Medido el **2026‑09‑11**, cuando vivía en `cuarentena/`. Desde el 2026‑09‑23 está **en la
librería** (`FOL.lean` lo importa y el build lo compila; ver la nota de arriba), y no contamina
nada porque el teorema es **condicional**. Su footprint lo vigila
`../ROBINSON_PlusPlus/check-footprints.bash`.

## Qué se demuestra aquí

No es «la prueba de `cuarentena/Soundness.lean` (borrado el 2026‑09‑23, `62dc2d5`) tenía un
fallo». Es más fuerte:

> **CUALQUIER función de tipo `∀ {Γ f}, (Γ ⊢ f) → satisfies Γ f` demuestra `False`.**

Es decir: el enunciado de solidez para `Derives` **no es demostrable porque es FALSO**, y ninguna
prueba más cuidadosa lo arreglaría.

## Por qué

`Derives` es un `inductive` de **22 constructores**; los 21 que comparte con `Derives₀` son
semánticamente válidos (`derives0_soundness`). Pero `FOL/MetaRules.lean` declara **cuatro `axiom`s
que lo HABITAN** (`imp_intro`, `raa`, `or_elim`, `ex_elim`; censo en `AXIOMS.md`) — y tienen que
ser axiomas, porque sus premisas son **funciones de Lean**, es
decir ocurrencias negativas que Lean rechazaría en un `inductive`.

⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**. Un teorema probado por
`induction` cubre los 22 casos, pero **se aplica a todos los habitantes**. Es el fallo clásico de
`axiom foo : UnInductivo`: rompe la garantía de «no hay basura».

El detonador concreto es `raa`: si `Γ ⊬ A`, la función `Γ ⊢ A → Γ ⊢ ⊥` existe **vacuamente**, luego
`raa` da `Γ ⊢ ¬A`. Con solidez eso obliga a `Γ ⊨ ¬A`, que es falso en cuanto `A` sea verdadera en
algún modelo de `Γ`. Y con `Γ = []` bastan **dos modelos triviales sobre `Unit`**.

## Qué NO dice

* ⚠️ **No dice que `ROBINSON_PlusPlus` sea inconsistente.** Medido el 2026‑09‑27: la librería de
  RPP **no importa** este módulo (el `FOL.Soundness` que aquí se citaba ya no existe)
  ni el barrel raíz `FOL`; sólo `FOL.FOL`, `FOL.MetaRules`, `FOL.Tactics`, `FOL.Deduction` y
  `FOL.Theorems.*`. Su árbol entero y la cadena de Gödel no están en contexto inconsistente.
* ⚠️ **No dice que `FOL/Semantics.lean` esté mal.** Está bien, y es útil: es lo que permitió probar
  `prfI_soundness` en `../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean` (un sondeo, fuera del
  build de RPP).
* ⚠️ **No dice que las meta‑reglas estén mal.** Dicen lo que dicen: `⊢` es una noción metateórica de
  verdad, no una relación de derivabilidad.
  `../ROBINSON_PlusPlus/ROBINSON_PlusPlus/Meta/OmegaStrength.lean` mide la otra cara —`⊢` decide
  toda sentencia— y de ahí que **no sea r.e.**

## La salida buena

Enunciar la solidez sobre un cálculo **sin axiomas habitándolo**. `ROBINSON_PlusPlus` tiene uno:
`Prfᵢ` (17 constructores, **cero** axiomas). `prfI_soundness` está probado, con footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open FOL.Metamath.Semantics

namespace FOL.Inconsistencia

-- Los dos modelos triviales sobre `Unit` (`Mfalse`: toda relación falsa; `Mtrue`: toda verdadera) y
-- el átomo `P` son los de `FOL.Soundness0`. Aquí había copias literales, retiradas el 2026‑09‑27
-- (N4, RPP‑109).
open FOL.Metamath.Soundness0 (Mfalse Mtrue P)

/-- Con contexto vacío, `contextSatisfies` es trivial. -/
theorem ctx_nil {D : Type} (M : Model D) (v : Nat → D) : contextSatisfies M v [] := by
  intro f hf; cases hf

/-- ⛔⛔ **El resultado.** Cualquier testigo del enunciado de solidez para `Derives` da `False`,
    sin ninguna otra hipótesis. El argumento usa sólo `raa` y dos modelos sobre `Unit`. -/
theorem inconsistencia_de_cualquier_solidez
    (solidez : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢ f) → satisfies Γ f) : False := by
  -- (1) `P` no es derivable del contexto vacío: lo refuta el modelo con relaciones falsas.
  have hnd : ¬ ([] ⊢ P) := fun h => solidez h Unit Mfalse (fun _ => ()) (ctx_nil _ _)
  -- (2) Luego `raa` — cuya premisa es una función de Lean — refuta `P`.
  have hneg : [] ⊢ neg P := FOL.MetaRules.raa (fun h => absurd h hnd)
  -- (3) Pero `P` es verdadera en el modelo con relaciones verdaderas.
  have h := solidez hneg Unit Mtrue (fun _ => ()) (ctx_nil _ _)
  simp only [evalFormula, neg] at h
  exact h trivial


-- ============================================================
-- §2 · ⛔⛔ Y la PROPIEDAD DE DISYUNCIÓN es FALSA para `Derives₀`
-- ============================================================

/-! ## ⛔⛔ El segundo enunciado que NO tiene testigo

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
misma `Formula`. ⛔ No es importable desde aquí: su cadena baja a `ROBINSON_PlusPlus` y a `Peano`.

⚠️ **Este teorema y el de §1 son hermanos**, y por eso viven juntos: los dos dicen que un
enunciado **no tiene testigo**, y los dos lo dicen del cálculo que el proyecto usa. -/

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

end FOL.Inconsistencia

/-! ## FOOTPRINT (2026‑09‑27) — §1, `[propext, FOL.MetaRules.raa]`; §2, `[propext, Quot.sound]`.
Ni `Classical.choice` ni otro axioma del proyecto. (Decía «sólo `raa` y los tres de Lean»: §1 no
usa `Quot.sound`, y §2 llevó `Classical.choice` hasta el 2026‑09‑27.) -/
#print axioms FOL.Inconsistencia.inconsistencia_de_cualquier_solidez
#print axioms FOL.Inconsistencia.derives0_no_disjunction_property
