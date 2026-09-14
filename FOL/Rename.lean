/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.Derives0
-- @axiom_system: none
-- @importance: high

import FOL.Derives0

/-!
# `FOL.Rename` — renombrado de símbolos de función, y que `Derives₀` lo respeta

⭐⭐ **Pieza del Paso 2** de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2.

    derives0_rename (ρ : String → String) :
        Γ ⊢₀ f  →  Γ.map (renameFormula ρ) ⊢₀ renameFormula ρ f

## Por qué hace falta

Es **la pieza que la extensión de Henkin necesita** y que hasta ahora estaba prohibida. La
construcción clásica añade testigos `(∃A) → A[c]` con `c` **fresca**, y la consistencia de cada
paso se prueba por contraposición: de una derivación que usa `c` hay que fabricar otra que no la
use. Eso es **transformar una derivación**, o sea **inducción sobre el cálculo**.

⛔ Sobre `Derives` es **ilegítimo** (M‑11: cuatro axiomas lo habitan).
✅ Sobre `Derives₀` es trabajo ordinario — y aquí está, con los **21** casos.

## ⚠️ Qué renombra, exactamente

**Sólo símbolos de FUNCIÓN.** Los de relación (`Formula.atom p ts`) se dejan intactos.

En esta firma los dos son `String`, pero son **dos espacios de nombres distintos** (`Model.func` y
`Model.rel` en `FOL/Semantics.lean`), y lo que Henkin necesita mover son las **constantes**, que
son símbolos de función de aridad cero. Renombrar también los relacionales confundiría los dos.

⚠️ **No se pide que `ρ` sea inyectiva.** Para esta dirección no hace falta: un renombrado
cualquiera transporta derivaciones. La inyectividad hará falta para la **recíproca** (la
conservatividad), que es otra pieza.

## Lo que hubo que probar antes

| lema | por qué |
|---|---|
| `rename_liftTerm` / `rename_liftTerms` / `rename_liftFormula` | el caso `intro_forall` levanta el contexto |
| `rename_substTerm` / `rename_substTerms` / `rename_substFormula` | los casos `elim_forall`, `intro_ex`, `subst` |
| `rename_getAt?` · `rename_replaceAt` · `rename_localRule` | el caso `rewrite_at` ⭐ **barato: `LocalRule` tiene UN constructor** |
| `map_rename_lift` | `(Γ.map lift).map ρ = (Γ.map ρ).map lift`, para `intro_forall` y `elim_ex` |

🔑 Y el patrón de siempre: **el renombrado conmuta con todo porque no toca las variables**. Es lo
que lo hace mucho más barato que una sustitución.
-/

namespace FOL.Rename

-- ============================================================
-- La operación
-- ============================================================

mutual
/-- Renombra los símbolos de FUNCIÓN de un término. Las variables no se tocan. -/
def renameTerm (ρ : String → String) : Term → Term
  | .var n => .var n
  | .func s ts => .func (ρ s) (renameTerms ρ ts)

def renameTerms (ρ : String → String) : List Term → List Term
  | [] => []
  | t :: ts => renameTerm ρ t :: renameTerms ρ ts
end

/-- Renombra los símbolos de función de una fórmula. ⚠️ El símbolo de RELACIÓN de un `atom`
**no** se toca: es otro espacio de nombres. -/
def renameFormula (ρ : String → String) : Formula → Formula
  | .bottom => .bottom
  | .atom p ts => .atom p (renameTerms ρ ts)
  | .eq t u => .eq (renameTerm ρ t) (renameTerm ρ u)
  | .impl a b => .impl (renameFormula ρ a) (renameFormula ρ b)
  | .forall a => .forall (renameFormula ρ a)
  | .and a b => .and (renameFormula ρ a) (renameFormula ρ b)
  | .or a b => .or (renameFormula ρ a) (renameFormula ρ b)
  | .ex a => .ex (renameFormula ρ a)

/-- `neg` es `impl _ ⊥`, así que el renombrado pasa por dentro **por `rfl`**. -/
theorem rename_neg (ρ : String → String) (A : Formula) :
    renameFormula ρ (neg A) = neg (renameFormula ρ A) := rfl

-- ============================================================
-- Conmuta con el LIFT
-- ============================================================

mutual
theorem rename_liftTerm (ρ : String → String) (c : Nat) (t : Term) :
    renameTerm ρ (liftTerm c t) = liftTerm c (renameTerm ρ t) := by
  cases t with
  | var n =>
      by_cases h : n < c
      · simp [liftTerm, renameTerm, h]
      · simp [liftTerm, renameTerm, h]
  | func s ts =>
      simp only [liftTerm, renameTerm]
      congr 1
      exact rename_liftTerms ρ c ts

theorem rename_liftTerms (ρ : String → String) (c : Nat) (ts : List Term) :
    renameTerms ρ (liftTerms c ts) = liftTerms c (renameTerms ρ ts) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, renameTerms, List.cons.injEq]
      exact ⟨rename_liftTerm ρ c t, rename_liftTerms ρ c ts'⟩
end

theorem rename_liftFormula (ρ : String → String) : ∀ (c : Nat) (f : Formula),
    renameFormula ρ (liftFormula c f) = liftFormula c (renameFormula ρ f) := by
  intro c f
  induction f generalizing c with
  | bottom => rfl
  | atom p ts => simp only [liftFormula, renameFormula, rename_liftTerms]
  | eq t u => simp only [liftFormula, renameFormula, rename_liftTerm]
  | impl a b iha ihb => simp only [liftFormula, renameFormula, iha, ihb]
  | «forall» a ih => simp only [liftFormula, renameFormula, ih]
  | and a b iha ihb => simp only [liftFormula, renameFormula, iha, ihb]
  | or a b iha ihb => simp only [liftFormula, renameFormula, iha, ihb]
  | ex a ih => simp only [liftFormula, renameFormula, ih]

-- ============================================================
-- Conmuta con la SUSTITUCIÓN
-- ============================================================

mutual
theorem rename_substTerm (ρ : String → String) (v : Nat) (s : Term) (t : Term) :
    renameTerm ρ (substTerm v s t) = substTerm v (renameTerm ρ s) (renameTerm ρ t) := by
  cases t with
  | var n =>
      by_cases h1 : n = v
      · simp [substTerm, renameTerm, h1]
      · by_cases h2 : n > v
        · simp [substTerm, renameTerm, h1, h2]
        · simp [substTerm, renameTerm, h1, h2]
  | func g ts =>
      simp only [substTerm, renameTerm]
      congr 1
      exact rename_substTerms ρ v s ts

theorem rename_substTerms (ρ : String → String) (v : Nat) (s : Term) (ts : List Term) :
    renameTerms ρ (substTerms v s ts) = substTerms v (renameTerm ρ s) (renameTerms ρ ts) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTerms, renameTerms, List.cons.injEq]
      exact ⟨rename_substTerm ρ v s t, rename_substTerms ρ v s ts'⟩
end

theorem rename_substFormula (ρ : String → String) : ∀ (f : Formula) (v : Nat) (s : Term),
    renameFormula ρ (substFormula v s f) = substFormula v (renameTerm ρ s) (renameFormula ρ f) := by
  intro f
  induction f with
  | bottom => intro v s; rfl
  | atom p ts => intro v s; simp only [substFormula, renameFormula, rename_substTerms]
  | eq t u => intro v s; simp only [substFormula, renameFormula, rename_substTerm]
  | impl a b iha ihb => intro v s; simp only [substFormula, renameFormula, iha, ihb]
  | «forall» a ih =>
      intro v s
      simp only [substFormula, renameFormula, ih, rename_liftTerm]
  | and a b iha ihb => intro v s; simp only [substFormula, renameFormula, iha, ihb]
  | or a b iha ihb => intro v s; simp only [substFormula, renameFormula, iha, ihb]
  | ex a ih =>
      intro v s
      simp only [substFormula, renameFormula, ih, rename_liftTerm]

-- ============================================================
-- Conmuta con la NAVEGACIÓN por posiciones (para `rewrite_at`)
-- ============================================================

theorem rename_getAt? (ρ : String → String) : ∀ (p : Pos) (f : Formula),
    getAt? (renameFormula ρ f) p = (getAt? f p).map (renameFormula ρ) := by
  intro p
  induction p with
  | root => intro f; simp [getAt?]
  | left p' ih => intro f; cases f <;> simp only [getAt?, renameFormula, ih] <;> rfl
  | right p' ih => intro f; cases f <;> simp only [getAt?, renameFormula, ih] <;> rfl
  | body p' ih => intro f; cases f <;> simp only [getAt?, renameFormula, ih] <;> rfl

theorem rename_replaceAt (ρ : String → String) : ∀ (p : Pos) (f newSub : Formula),
    replaceAt (renameFormula ρ f) p (renameFormula ρ newSub)
      = renameFormula ρ (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro f n; simp [replaceAt]
  | left p' ih => intro f n; cases f <;> simp only [replaceAt, renameFormula, ih]
  | right p' ih => intro f n; cases f <;> simp only [replaceAt, renameFormula, ih]
  | body p' ih => intro f n; cases f <;> simp only [replaceAt, renameFormula, ih]

/-- ⭐ Barato: `LocalRule` tiene **un solo constructor**. -/
theorem rename_localRule (ρ : String → String) {A B : Formula} (h : LocalRule A B) :
    LocalRule (renameFormula ρ A) (renameFormula ρ B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (renameFormula ρ A) (renameFormula ρ B) (renameFormula ρ C)

-- ============================================================
-- El contexto: renombrar y levantar conmutan
-- ============================================================

theorem map_rename_lift (ρ : String → String) (Γ : List Formula) :
    (Γ.map (liftFormula 0)).map (renameFormula ρ)
      = (Γ.map (renameFormula ρ)).map (liftFormula 0) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, rename_liftFormula, ih]

-- ============================================================
-- ⭐⭐ EL LEMA
-- ============================================================

/-- **`Derives₀` respeta el renombrado de símbolos de función.**

⭐ Inducción sobre los 21 constructores — legítima porque `Derives₀` **no tiene
habitantes‑axioma** (ADR‑033). Sobre `Derives` esto sería M‑11 en estado puro.

Es la pieza que la extensión de Henkin necesitaba (plan §6.2). -/
theorem derives0_rename (ρ : String → String) {Γ : List Formula} {f : Formula} (h : Γ ⊢₀ f) :
    (Γ.map (renameFormula ρ)) ⊢₀ renameFormula ρ f := by
  induction h with
  | hyp Γ' f' hIn => exact Derives₀.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih =>
      exact Derives₀.intro_impl _ _ _ ih
  | elim_impl Γ' A B _ _ ih1 ih2 => exact Derives₀.elim_impl _ _ _ ih1 ih2
  | intro_and Γ' A B _ _ ih1 ih2 => exact Derives₀.intro_and _ _ _ ih1 ih2
  | elim_and_l Γ' A B _ ih => exact Derives₀.elim_and_l _ _ _ ih
  | elim_and_r Γ' A B _ ih => exact Derives₀.elim_and_r _ _ _ ih
  | intro_or_l Γ' A B _ ih => exact Derives₀.intro_or_l _ _ _ ih
  | intro_or_r Γ' A B _ ih => exact Derives₀.intro_or_r _ _ _ ih
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 => exact Derives₀.elim_or _ _ _ _ ih1 ih2 ih3
  | intro_forall Γ' A _ ih =>
      refine Derives₀.intro_forall _ _ ?_
      rw [← map_rename_lift]
      exact ih
  | elim_forall Γ' A t _ ih =>
      have := Derives₀.elim_forall (Γ'.map (renameFormula ρ)) (renameFormula ρ A)
                (renameTerm ρ t) ih
      rw [rename_substFormula]
      exact this
  | intro_ex Γ' A t _ ih =>
      refine Derives₀.intro_ex _ _ (renameTerm ρ t) ?_
      rw [← rename_substFormula]
      exact ih
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      refine Derives₀.elim_ex _ (renameFormula ρ A) _ ih1 ?_
      rw [← rename_liftFormula, ← map_rename_lift]
      exact ih2
  | bot_elim Γ' A _ ih => exact Derives₀.bot_elim _ _ ih
  | weakening Γ' Γ'' f' _ hSub ih =>
      refine Derives₀.weakening _ _ _ ih ?_
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hSub y hy)
  | rewrite_at Γ' f' f'' p sub sub' _ hget hrule heq ih =>
      refine Derives₀.rewrite_at _ _ _ p (renameFormula ρ sub) (renameFormula ρ sub') ih ?_ ?_ ?_
      · rw [rename_getAt?, hget]; rfl
      · exact rename_localRule ρ hrule
      · rw [heq, ← rename_replaceAt]
  | dne_rule Γ' A _ ih => exact Derives₀.dne_rule _ _ ih
  | dne_schema Γ' A => exact Derives₀.dne_schema _ _
  | forall_not_ex_not Γ' A => exact Derives₀.forall_not_ex_not _ _
  | refl Γ' t => exact Derives₀.refl _ _
  | subst Γ' t₁ t₂ f' _ _ ih1 ih2 =>
      have := Derives₀.subst (Γ'.map (renameFormula ρ)) (renameTerm ρ t₁) (renameTerm ρ t₂)
                (renameFormula ρ f') ih1 (by rw [← rename_substFormula]; exact ih2)
      rw [rename_substFormula]
      exact this

end FOL.Rename

#print axioms FOL.Rename.derives0_rename
