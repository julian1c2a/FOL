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
# `FOL.Eigenvariable` — de una constante FRESCA a un `∀`

⭐⭐ **La otra mitad del Paso 2** de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.2.

    derives0_gen_fresh (c) (hfresh : ∀ g ∈ Γ, ¬ occursFormula c g) :
        Γ ⊢₀ φ  →  Γ ⊢₀ ∀ (absFormula c 0 φ)

Es **el paso de eigenvariable**: si algo se deriva usando una constante `c` que **no aparece en el
contexto**, entonces se deriva su generalización. Es lo que hace funcionar la extensión de Henkin:
de `S ⊢₀ ¬A[c]` con `c` fresca se pasa a `S ⊢₀ ∀x ¬A(x)`, y con eso cae la consistencia del paso.

## ⚠️ Por qué NO era un renombrado

`FOL.Rename` manda símbolos a símbolos y **no toca las variables**, y por eso conmutaba con todo
gratis. Aquí la operación manda una **constante** a una **variable**, así que **sí** toca los
índices de De Bruijn: al entrar en un binder, el índice de la variable nueva sube.

⇒ Las conmutaciones llevan **hipótesis de nivel**, y ésa es toda la diferencia de precio:

| lema | hipótesis |
|---|---|
| `absTerm_lift` / `absFormula_lift` | `j ≤ k` |
| `absTerm_subst` / `absFormula_subst` | `v ≤ k` |

🔑 Las dos se usan con `j = 0` y `v = 0`, donde la hipótesis es trivial; pero la **inducción bajo
binders** las necesita generales, porque ahí `j` y `v` suben con `k`.

## La estructura de la prueba

1. `absFormula c k φ` — sustituye `c` (como **constante**, o sea `func c []`) por `var k`, y
   **levanta** las variables libres `≥ k`. Bajo un binder, `k` sube a `k+1`.
2. `absDerives` — transporte por los **21** constructores, **generalizado sobre `k`**. ⚠️ El `k`
   tiene que estar en el motivo de la inducción: en `intro_forall` la hipótesis inductiva se usa a
   nivel `k+1`, no `k`.
3. `occursFormula` y `abs_eq_lift_of_not_occurs` — si `c` **no aparece**, `absFormula c k` es
   exactamente `liftFormula k`.
4. ⇒ con `c` fresca en `Γ`, el contexto transportado **es** `Γ.map (liftFormula 0)`, y
   `Derives₀.intro_forall` —que es un **constructor**— cierra.

⭐ **El paso 4 es el que explica por qué esto encaja tan bien en este cálculo**: `intro_forall` ya
ES la regla de la eigenvariable en forma de De Bruijn. Lo único que faltaba era llevar la
derivación desde «constante fresca» hasta «contexto levantado».
-/

namespace FOL.Eigenvariable

-- ============================================================
-- §1 · La abstracción de una constante
-- ============================================================

mutual
/-- Sustituye la **constante** `c` (es decir `Term.func c []`) por `Term.var k`, y levanta las
variables libres `≥ k` para dejarle sitio. -/
def absTerm (c : String) (k : Nat) : Term → Term
  | .var n => if n < k then .var n else .var (n + 1)
  | .func s [] => if s = c then .var k else .func s []
  | .func s (t :: ts) => .func s (absTerms c k (t :: ts))

def absTerms (c : String) (k : Nat) : List Term → List Term
  | [] => []
  | t :: ts => absTerm c k t :: absTerms c k ts
end

/-- ⚠️ Bajo un binder el índice de la variable nueva **sube**: `k` pasa a `k + 1`. Es la única
diferencia real con `renameFormula`, y de ahí sale todo el coste extra. -/
def absFormula (c : String) (k : Nat) : Formula → Formula
  | .bottom => .bottom
  | .atom p ts => .atom p (absTerms c k ts)
  | .eq t u => .eq (absTerm c k t) (absTerm c k u)
  | .impl a b => .impl (absFormula c k a) (absFormula c k b)
  | .forall a => .forall (absFormula c (k + 1) a)
  | .and a b => .and (absFormula c k a) (absFormula c k b)
  | .or a b => .or (absFormula c k a) (absFormula c k b)
  | .ex a => .ex (absFormula c (k + 1) a)

theorem abs_neg (c : String) (k : Nat) (A : Formula) :
    absFormula c k (neg A) = neg (absFormula c k A) := rfl

-- ============================================================
-- §2 · Conmuta con el LIFT, con `j ≤ k`
-- ============================================================

mutual
theorem absTerm_lift (c : String) : ∀ (j k : Nat) (_ : j ≤ k) (t : Term),
    liftTerm j (absTerm c k t) = absTerm c (k + 1) (liftTerm j t) := by
  intro j k hjk t
  cases t with
  | var n =>
      by_cases h1 : n < k
      · by_cases h2 : n < j
        · simp [absTerm, liftTerm, h1, h2, show n < k + 1 by omega]
        · simp [absTerm, liftTerm, h1, h2, show n + 1 < k + 1 by omega]
      · have h2 : ¬ n < j := by omega
        simp [absTerm, liftTerm, h1, h2, show ¬ n + 1 < j by omega,
          show ¬ n + 1 < k + 1 by omega]
  | func s ts =>
      cases ts with
      | nil =>
          by_cases hs : s = c
          · simp [absTerm, liftTerm, liftTerms, hs, show ¬ k < j by omega]
          · simp [absTerm, liftTerm, liftTerms, hs]
      | cons u us =>
          simp only [absTerm, liftTerm, liftTerms]
          congr 1
          exact absTerms_lift c j k hjk (u :: us)

theorem absTerms_lift (c : String) : ∀ (j k : Nat) (_ : j ≤ k) (ts : List Term),
    liftTerms j (absTerms c k ts) = absTerms c (k + 1) (liftTerms j ts) := by
  intro j k hjk ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [absTerms, liftTerms, List.cons.injEq]
      exact ⟨absTerm_lift c j k hjk t, absTerms_lift c j k hjk ts'⟩
end

theorem absFormula_lift (c : String) : ∀ (f : Formula) (j k : Nat), j ≤ k →
    liftFormula j (absFormula c k f) = absFormula c (k + 1) (liftFormula j f) := by
  intro f
  induction f with
  | bottom => intro j k _; rfl
  | atom p ts => intro j k h; simp only [absFormula, liftFormula, absTerms_lift c j k h]
  | eq t u => intro j k h; simp only [absFormula, liftFormula, absTerm_lift c j k h]
  | impl a b iha ihb => intro j k h; simp only [absFormula, liftFormula, iha j k h, ihb j k h]
  | «forall» a ih =>
      intro j k h
      simp only [absFormula, liftFormula, ih (j + 1) (k + 1) (by omega)]
  | and a b iha ihb => intro j k h; simp only [absFormula, liftFormula, iha j k h, ihb j k h]
  | or a b iha ihb => intro j k h; simp only [absFormula, liftFormula, iha j k h, ihb j k h]
  | ex a ih =>
      intro j k h
      simp only [absFormula, liftFormula, ih (j + 1) (k + 1) (by omega)]

-- ============================================================
-- §3 · Conmuta con la SUSTITUCIÓN, con `v ≤ k`
-- ============================================================

mutual
theorem absTerm_subst (c : String) : ∀ (v k : Nat) (_ : v ≤ k) (s : Term) (t : Term),
    absTerm c k (substTerm v s t) = substTerm v (absTerm c k s) (absTerm c (k + 1) t) := by
  intro v k hvk s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · subst h1
        simp [absTerm, substTerm, show n < k + 1 by omega]
      · by_cases h2 : n > v
        · by_cases h3 : n < k + 1
          · have e1 : n - 1 < k := by omega
            simp [absTerm, substTerm, h1, h2, h3, e1]
          · have e1 : ¬ n - 1 < k := by omega
            have e2 : n + 1 ≠ v := by omega
            have e3 : n + 1 > v := by omega
            simp [absTerm, substTerm, h1, h2, h3, e1, e2, e3]
            omega
        · have e0 : n < k + 1 := by omega
          have e1 : n < k := by omega
          simp [absTerm, substTerm, h1, h2, e0, e1]
  | func g ts =>
      cases ts with
      | nil =>
          by_cases hg : g = c
          · have e : ¬ k + 1 = v := by omega
            have e2 : k + 1 > v := by omega
            simp [absTerm, substTerm, substTerms, hg, e, e2]
          · simp [absTerm, substTerm, substTerms, hg]
      | cons u us =>
          simp only [absTerm, substTerm, substTerms]
          congr 1
          exact absTerms_subst c v k hvk s (u :: us)

theorem absTerms_subst (c : String) : ∀ (v k : Nat) (_ : v ≤ k) (s : Term) (ts : List Term),
    absTerms c k (substTerms v s ts) = substTerms v (absTerm c k s) (absTerms c (k + 1) ts) := by
  intro v k hvk s ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [absTerms, substTerms, List.cons.injEq]
      exact ⟨absTerm_subst c v k hvk s t, absTerms_subst c v k hvk s ts'⟩
end

theorem absFormula_subst (c : String) : ∀ (f : Formula) (v k : Nat), v ≤ k → ∀ (s : Term),
    absFormula c k (substFormula v s f)
      = substFormula v (absTerm c k s) (absFormula c (k + 1) f) := by
  intro f
  induction f with
  | bottom => intro v k _ s; rfl
  | atom p ts => intro v k h s; simp only [absFormula, substFormula, absTerms_subst c v k h s]
  | eq t u => intro v k h s; simp only [absFormula, substFormula, absTerm_subst c v k h s]
  | impl a b iha ihb =>
      intro v k h s; simp only [absFormula, substFormula, iha v k h s, ihb v k h s]
  | «forall» a ih =>
      intro v k h s
      simp only [absFormula, substFormula, ih (v + 1) (k + 1) (by omega) (liftTerm 0 s),
        absTerm_lift c 0 k (by omega)]
  | and a b iha ihb =>
      intro v k h s; simp only [absFormula, substFormula, iha v k h s, ihb v k h s]
  | or a b iha ihb =>
      intro v k h s; simp only [absFormula, substFormula, iha v k h s, ihb v k h s]
  | ex a ih =>
      intro v k h s
      simp only [absFormula, substFormula, ih (v + 1) (k + 1) (by omega) (liftTerm 0 s),
        absTerm_lift c 0 k (by omega)]

-- ============================================================
-- §4 · Conmuta con la navegación (para `rewrite_at`)
-- ============================================================

/-- ⚠️⚠️ **Aquí está la diferencia con `FOL.Rename`, y la vi al compilar.** `getAt?`/`replaceAt`
ATRAVIESAN binders (`Pos.body`), y `absFormula` **cambia de nivel** al entrar en uno. Así que los
dos lemas son **FALSOS** si se enuncian a nivel constante: hay que llevar la cuenta de cuántos
binders tiene el camino. Eso es `posDepth`.

🔑 *Cuando una operación depende de la profundidad, todo lo que navegue el árbol tiene que
llevarla en el enunciado.* -/
def posDepth : Pos → Nat
  | .root => 0
  | .left p => posDepth p
  | .right p => posDepth p
  | .body p => posDepth p + 1

theorem abs_getAt? (c : String) : ∀ (p : Pos) (k : Nat) (f : Formula),
    getAt? (absFormula c k f) p = (getAt? f p).map (absFormula c (k + posDepth p)) := by
  intro p
  induction p with
  | root => intro k f; simp [getAt?, posDepth]
  | left p' ih => intro k f; cases f <;> simp only [getAt?, absFormula, ih, posDepth] <;> rfl
  | right p' ih => intro k f; cases f <;> simp only [getAt?, absFormula, ih, posDepth] <;> rfl
  | body p' ih =>
      intro k f
      cases f <;>
        simp only [getAt?, absFormula, ih, posDepth, Nat.add_assoc, Nat.add_comm 1] <;> rfl

theorem abs_replaceAt (c : String) : ∀ (p : Pos) (k : Nat) (f newSub : Formula),
    replaceAt (absFormula c k f) p (absFormula c (k + posDepth p) newSub)
      = absFormula c k (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro k f n; simp [replaceAt, posDepth]
  | left p' ih => intro k f n; cases f <;> simp only [replaceAt, absFormula, ih, posDepth]
  | right p' ih => intro k f n; cases f <;> simp only [replaceAt, absFormula, ih, posDepth]
  | body p' ih =>
      intro k f n
      -- ⚠️ `k + (posDepth p' + 1)` y `(k + 1) + posDepth p'` son el mismo número pero no el
      -- mismo TÉRMINO: hay que reasociar antes de que `ih` case.
      have e : k + (posDepth p' + 1) = (k + 1) + posDepth p' := by omega
      cases f <;> simp only [replaceAt, absFormula, posDepth, e, ih]

theorem abs_localRule (c : String) (k : Nat) {A B : Formula} (h : LocalRule A B) :
    LocalRule (absFormula c k A) (absFormula c k B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (absFormula c k A) (absFormula c k B) (absFormula c k C)

-- ============================================================
-- §5 · El contexto
-- ============================================================

theorem map_abs_lift (c : String) (k : Nat) (Γ : List Formula) :
    (Γ.map (absFormula c k)).map (liftFormula 0)
      = (Γ.map (liftFormula 0)).map (absFormula c (k + 1)) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih =>
      simp only [List.map_cons, absFormula_lift c g 0 k (Nat.zero_le _), ih]

-- ============================================================
-- §6 · ⭐ EL TRANSPORTE, generalizado sobre el nivel
-- ============================================================

/-- **`Derives₀` transporta la abstracción de una constante.**

⚠️ El `∀ k` está **dentro** a propósito: en `intro_forall` y `elim_ex` la hipótesis inductiva se
usa a nivel `k + 1`, no a nivel `k`. Si el `k` se fija fuera, la inducción no cierra. -/
theorem absDerives (c : String) {Γ : List Formula} {φ : Formula} (h : Γ ⊢₀ φ) :
    ∀ k : Nat, (Γ.map (absFormula c k)) ⊢₀ absFormula c k φ := by
  induction h with
  | hyp Γ' f' hIn => intro k; exact Derives₀.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih => intro k; exact Derives₀.intro_impl _ _ _ (ih k)
  | elim_impl Γ' A B _ _ ih1 ih2 => intro k; exact Derives₀.elim_impl _ _ _ (ih1 k) (ih2 k)
  | intro_and Γ' A B _ _ ih1 ih2 => intro k; exact Derives₀.intro_and _ _ _ (ih1 k) (ih2 k)
  | elim_and_l Γ' A B _ ih => intro k; exact Derives₀.elim_and_l _ _ _ (ih k)
  | elim_and_r Γ' A B _ ih => intro k; exact Derives₀.elim_and_r _ _ _ (ih k)
  | intro_or_l Γ' A B _ ih => intro k; exact Derives₀.intro_or_l _ _ _ (ih k)
  | intro_or_r Γ' A B _ ih => intro k; exact Derives₀.intro_or_r _ _ _ (ih k)
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 =>
      intro k; exact Derives₀.elim_or _ _ _ _ (ih1 k) (ih2 k) (ih3 k)
  | intro_forall Γ' A _ ih =>
      intro k
      refine Derives₀.intro_forall _ _ ?_
      rw [map_abs_lift]
      exact ih (k + 1)
  | elim_forall Γ' A t _ ih =>
      intro k
      have := Derives₀.elim_forall (Γ'.map (absFormula c k)) (absFormula c (k + 1) A)
                (absTerm c k t) (ih k)
      rw [absFormula_subst c A 0 k (Nat.zero_le _)]
      exact this
  | intro_ex Γ' A t _ ih =>
      intro k
      refine Derives₀.intro_ex _ _ (absTerm c k t) ?_
      rw [← absFormula_subst c A 0 k (Nat.zero_le _)]
      exact ih k
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      intro k
      refine Derives₀.elim_ex _ (absFormula c (k + 1) A) _ (ih1 k) ?_
      rw [absFormula_lift c B 0 k (Nat.zero_le _), map_abs_lift]
      exact ih2 (k + 1)
  | bot_elim Γ' A _ ih => intro k; exact Derives₀.bot_elim _ _ (ih k)
  | weakening Γ' Γ'' f' _ hSub ih =>
      intro k
      refine Derives₀.weakening _ _ _ (ih k) ?_
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hSub y hy)
  | rewrite_at Γ' f' f'' p sub sub' _ hget hrule heq ih =>
      intro k
      refine Derives₀.rewrite_at _ _ _ p (absFormula c (k + posDepth p) sub)
        (absFormula c (k + posDepth p) sub') (ih k) ?_ ?_ ?_
      · rw [abs_getAt?, hget]; rfl
      · exact abs_localRule c _ hrule
      · rw [heq, ← abs_replaceAt]
  | dne_rule Γ' A _ ih => intro k; exact Derives₀.dne_rule _ _ (ih k)
  | dne_schema Γ' A => intro k; exact Derives₀.dne_schema _ _
  | forall_not_ex_not Γ' A => intro k; exact Derives₀.forall_not_ex_not _ _
  | refl Γ' t => intro k; exact Derives₀.refl _ _
  | subst Γ' t₁ t₂ f' _ _ ih1 ih2 =>
      intro k
      have := Derives₀.subst (Γ'.map (absFormula c k)) (absTerm c k t₁) (absTerm c k t₂)
                (absFormula c (k + 1) f') (ih1 k)
                (by rw [← absFormula_subst c f' 0 k (Nat.zero_le _)]; exact ih2 k)
      rw [absFormula_subst c f' 0 k (Nat.zero_le _)]
      exact this

-- ============================================================
-- §7 · Frescura, y el paso de eigenvariable
-- ============================================================

mutual
def occursTerm (c : String) : Term → Prop
  | .var _ => False
  | .func s ts => Or (s = c) (occursTerms c ts)

def occursTerms (c : String) : List Term → Prop
  | [] => False
  | t :: ts => Or (occursTerm c t) (occursTerms c ts)
end

def occursFormula (c : String) : Formula → Prop
  | .bottom => False
  | .atom _ ts => occursTerms c ts
  | .eq t u => Or (occursTerm c t) (occursTerm c u)
  | .impl a b => Or (occursFormula c a) (occursFormula c b)
  | .forall a => occursFormula c a
  | .and a b => Or (occursFormula c a) (occursFormula c b)
  | .or a b => Or (occursFormula c a) (occursFormula c b)
  | .ex a => occursFormula c a

mutual
theorem absTerm_eq_lift (c : String) : ∀ (k : Nat) (t : Term), Not (occursTerm c t) →
    absTerm c k t = liftTerm k t := by
  intro k t hocc
  cases t with
  | var n => by_cases h : n < k <;> simp [absTerm, liftTerm, h]
  | func s ts =>
      cases ts with
      | nil =>
          have hs : Not (s = c) := fun h => hocc (Or.inl h)
          simp [absTerm, liftTerm, liftTerms, hs]
      | cons u us =>
          simp only [absTerm, liftTerm]
          congr 1
          exact absTerms_eq_lift c k (u :: us) (fun h => hocc (Or.inr h))

theorem absTerms_eq_lift (c : String) : ∀ (k : Nat) (ts : List Term), Not (occursTerms c ts) →
    absTerms c k ts = liftTerms k ts := by
  intro k ts hocc
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [absTerms, liftTerms, List.cons.injEq]
      exact ⟨absTerm_eq_lift c k t (fun h => hocc (Or.inl h)),
             absTerms_eq_lift c k ts' (fun h => hocc (Or.inr h))⟩
end

/-- ⭐ **Si `c` no aparece, abstraerla es exactamente LEVANTAR.** Es el puente entre §6 y
`Derives₀.intro_forall`. -/
theorem absFormula_eq_lift (c : String) : ∀ (f : Formula) (k : Nat), Not (occursFormula c f) →
    absFormula c k f = liftFormula k f := by
  intro f
  induction f with
  | bottom => intro k _; rfl
  | atom p ts => intro k h; simp only [absFormula, liftFormula, absTerms_eq_lift c k ts h]
  | eq t u =>
      intro k h
      simp only [absFormula, liftFormula, absTerm_eq_lift c k t (fun x => h (Or.inl x)),
        absTerm_eq_lift c k u (fun x => h (Or.inr x))]
  | impl a b iha ihb =>
      intro k h
      simp only [absFormula, liftFormula, iha k (fun x => h (Or.inl x)),
        ihb k (fun x => h (Or.inr x))]
  | «forall» a ih => intro k h; simp only [absFormula, liftFormula, ih (k + 1) h]
  | and a b iha ihb =>
      intro k h
      simp only [absFormula, liftFormula, iha k (fun x => h (Or.inl x)),
        ihb k (fun x => h (Or.inr x))]
  | or a b iha ihb =>
      intro k h
      simp only [absFormula, liftFormula, iha k (fun x => h (Or.inl x)),
        ihb k (fun x => h (Or.inr x))]
  | ex a ih => intro k h; simp only [absFormula, liftFormula, ih (k + 1) h]

theorem map_abs_eq_map_lift (c : String) {Γ : List Formula}
    (hfresh : ∀ g, g ∈ Γ → Not (occursFormula c g)) :
    Γ.map (absFormula c 0) = Γ.map (liftFormula 0) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨absFormula_eq_lift c g 0 (hfresh g (List.Mem.head _)),
             ih (fun x hx => hfresh x (List.Mem.tail _ hx))⟩

/-- ⭐⭐ **EL PASO DE EIGENVARIABLE.**

Si `Γ ⊢₀ φ` y la constante `c` **no aparece en el contexto**, entonces se deriva la
generalización. Es lo que la extensión de Henkin necesita para probar que añadir el testigo
preserva la consistencia.

⚠️ Nótese que **no se pide** que `c` no aparezca en `φ` — al revés: la gracia es justamente que
`φ` la usa, y `absFormula c 0 φ` es «`φ` con `c` convertida en la variable ligada». -/
theorem derives0_gen_fresh (c : String) {Γ : List Formula} {φ : Formula}
    (hfresh : ∀ g, g ∈ Γ → Not (occursFormula c g)) (h : Γ ⊢₀ φ) :
    Γ ⊢₀ Formula.forall (absFormula c 0 φ) := by
  refine Derives₀.intro_forall _ _ ?_
  rw [← map_abs_eq_map_lift c hfresh]
  exact absDerives c h 0

/-- Corolario en la forma que consume Henkin: con `c` fresca en el contexto, de `Γ ⊢₀ φ` se obtiene
**cualquier instancia** `Γ ⊢₀ (absFormula c 0 φ)[t]`. -/
theorem derives0_inst_fresh (c : String) {Γ : List Formula} {φ : Formula}
    (hfresh : ∀ g, g ∈ Γ → Not (occursFormula c g)) (h : Γ ⊢₀ φ) (t : Term) :
    Γ ⊢₀ substFormula 0 t (absFormula c 0 φ) :=
  Derives₀.elim_forall _ _ t (derives0_gen_fresh c hfresh h)

end FOL.Eigenvariable

#print axioms FOL.Eigenvariable.absDerives
#print axioms FOL.Eigenvariable.derives0_gen_fresh
#print axioms FOL.Eigenvariable.derives0_inst_fresh
