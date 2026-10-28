/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOLModels.lean
-- FOL⁼ en el marco, con sus MODELOS: la semántica, la compacidad, la completitud fuerte, la existencia de modelo y
-- la conservatividad relativa a un lenguaje (T58, ADR‑217 de RPP).

import TheoryFramework.Instances.FOL
import TheoryFramework.Conservativity
import FOL.Compacity0

/-!
# FOL⁼ con sus modelos (T58, ADR‑217 de RPP)

`TheoryFramework/Instances/FOL.lean` (congelado) declara `Derives₀` como `LogicSystem`, con su solidez y su
completitud para premisas FINITAS. Aquí, lo que el marco no podía decir sin modelos:

    fol0Semantics                  : ModelSemantics Formula   -- Interp0 = dominio + estructura + valuación
    fol0Compact                    : CompactLogic Formula     -- de FOL.Compacity0.compactness
    fol0_proves_iff_entails        : T.proves f ↔ T.entails f        -- 🏁 la COMPLETITUD FUERTE, en el marco
    fol0_consistent_iff_hasModel   : IsConsistent T ↔ T.HasModel     -- 🏁 la existencia de modelo
    fol0_conservativeOver_of_expansion                                -- el criterio, con EXPANSIONES
    fol0_extDef_conservative       : una extensión por DEFINICIÓN es conservativa sobre el lenguaje de T
    fol0_extDef_not_conservative   : …y la frescura del símbolo es necesaria (el control)

## El lenguaje

`LangFormula L φ`: todo símbolo de `φ` —de función y de RELACIÓN— está en `L`. (`occursFormula` de
`FOL/Eigenvariable.lean` sólo mira los de función.) `AgreeOn L M M'`: dos estructuras sobre el mismo dominio que
coinciden en los símbolos de `L`; y `evalFormula_agreeOn`, el lema de coincidencia: una fórmula de `L` vale lo
mismo en las dos. Con eso, la conservatividad de libro: `T₂` no prueba ninguna fórmula NUEVA de `L`.

## 📏 Footprint

`fol0Semantics` y las piezas del lenguaje (`evalFormula_agreeOn`, `expandRel_agreeOn`, `expandRel_defAx`): sin
`Classical.choice`. Todo lo que pasa por la compacidad o por la completitud (`fol0Compact` y lo que la usa):
`[propext, Classical.choice, Quot.sound]`, el de `FOL.Compacity0.compactness` y `completeness₀`.
-/

namespace TheoryFramework.Instances

open FOL.Metamath.Semantics
open TheoryFramework.ModelSemantics

-- ============================================================
-- §1 · La semántica de modelos y la compacidad
-- ============================================================

/-- Una interpretación de FOL⁼: un dominio, una estructura sobre él y una valuación de las variables. -/
structure Interp0 : Type 1 where
  D : Type
  M : Model D
  v : Nat → D

/-- ⭐ **Los modelos de FOL⁼**: satisfacer es `evalFormula`, y `satisfies Γ f` es «todo modelo de `Γ` satisface `f`». -/
instance fol0Semantics : ModelSemantics Formula where
  Interp := Interp0
  sat I f := evalFormula I.M I.v f
  entails_iff _ _ := Iff.intro (fun h I hI => h I.D I.M I.v hI) (fun h D M v hΓ => h ⟨D, M, v⟩ hΓ)

/-- `Sat` del marco es `IsSatisfiable` de FOL. -/
theorem fol0_sat_iff (S : Formula → Prop) : Iff (Sat S) (FOL.Canonical0.IsSatisfiable S) :=
  Iff.intro (fun ⟨I, hI⟩ => ⟨I.D, I.M, I.v, hI⟩) (fun ⟨D, M, v, h⟩ => ⟨⟨D, M, v⟩, h⟩)

/-- La compacidad de libro de FOL⁼, leída en el marco. -/
theorem fol0_satCompact : SatCompact Formula := fun S h =>
  (fol0_sat_iff S).mpr ((FOL.Compacity0.compactness S).mpr fun Γ hΓ => (fol0_sat_iff _).mp (h Γ hΓ))

/-- ⭐ **FOL⁼ es compacta** (en la forma de consecuencia): la negación de FOL es la clásica (`neg f = f ⇒ ⊥`, y
su valor es la negación del de `f`, por definición). -/
instance fol0Compact : CompactLogic Formula :=
  compact_of_satCompact (fun _ _ => Iff.rfl) fol0_satCompact

/-- 🏁 **LA COMPLETITUD FUERTE DE FOL⁼, en el marco**: una teoría prueba `f` si y sólo si `f` es consecuencia
semántica de sus axiomas —de todos—. (`fol0_proves_iff_models`, en el fichero congelado, es la versión FINITA.) -/
theorem fol0_proves_iff_entails (T : Theory Formula) (f : Formula) : Iff (T.proves f) (T.entails f) :=
  Theory.proves_iff_entails T f

/-- Y para FOL⁼ la consecuencia finita de `Theory.models` es la de verdad. -/
theorem fol0_models_iff_entails (T : Theory Formula) (f : Formula) : Iff (T.models f) (T.entails f) :=
  Theory.models_iff_entails T f

/-- 🏁 **EXISTENCIA DE MODELO**, derivada en el marco: una teoría de FOL⁼ es consistente si y sólo si tiene
modelo. (Es `FOL.Compacity0.model_existence_iff₀`, que aquí sale de la completitud finita y la compacidad.) -/
theorem fol0_consistent_iff_hasModel (T : Theory Formula) : Iff (IsConsistent T) T.HasModel :=
  consistent_iff_hasModel (fun _ h => h) T

-- ============================================================
-- §2 · El lenguaje de una fórmula y el lema de coincidencia
-- ============================================================

mutual
/-- Todo símbolo de función del término está en `L`. -/
def LangTerm (L : List Char → Prop) : Term → Prop
  | .var _ => True
  | .func s ts => And (L s) (LangTerms L ts)

/-- Todo símbolo de función de los términos está en `L`. -/
def LangTerms (L : List Char → Prop) : List Term → Prop
  | [] => True
  | t :: ts => And (LangTerm L t) (LangTerms L ts)
end

/-- ⭐ Las fórmulas del LENGUAJE `L`: todo símbolo —de función y de relación— está en `L`. -/
def LangFormula (L : List Char → Prop) : Formula → Prop
  | .bottom => True
  | .atom p ts => And (L p) (LangTerms L ts)
  | .eq t u => And (LangTerm L t) (LangTerm L u)
  | .impl a b => And (LangFormula L a) (LangFormula L b)
  | .forall a => LangFormula L a
  | .and a b => And (LangFormula L a) (LangFormula L b)
  | .or a b => And (LangFormula L a) (LangFormula L b)
  | .ex a => LangFormula L a

/-- Dos estructuras sobre el mismo dominio que COINCIDEN en los símbolos de `L`. -/
def AgreeOn (L : List Char → Prop) {D : Type} (M M' : Model D) : Prop :=
  ∀ s, L s → And (∀ ds, M.func s ds = M'.func s ds) (∀ ds, Iff (M.rel s ds) (M'.rel s ds))

mutual
theorem evalTerm_agreeOn {L : List Char → Prop} {D : Type} {M M' : Model D} (h : AgreeOn L M M') :
    ∀ (t : Term) (v : Nat → D), LangTerm L t → evalTerm M v t = evalTerm M' v t
  | .var _, _, _ => rfl
  | .func s ts, v, ht => by
      unfold LangTerm at ht
      unfold evalTerm
      rw [evalTerms_agreeOn h ts v ht.2]
      exact (h s ht.1).1 _

theorem evalTerms_agreeOn {L : List Char → Prop} {D : Type} {M M' : Model D} (h : AgreeOn L M M') :
    ∀ (ts : List Term) (v : Nat → D), LangTerms L ts → evalTerms M v ts = evalTerms M' v ts
  | [], _, _ => rfl
  | t :: ts, v, ht => by
      unfold LangTerms at ht
      unfold evalTerms
      rw [evalTerm_agreeOn h t v ht.1, evalTerms_agreeOn h ts v ht.2]
end

/-- ⭐ **EL LEMA DE COINCIDENCIA**: una fórmula de `L` vale lo mismo en dos estructuras que coinciden en `L`. -/
theorem evalFormula_agreeOn {L : List Char → Prop} {D : Type} {M M' : Model D} (h : AgreeOn L M M') :
    ∀ (f : Formula) (v : Nat → D), LangFormula L f → Iff (evalFormula M v f) (evalFormula M' v f) := by
  intro f
  induction f with
  | bottom => intro _ _; exact Iff.rfl
  | atom p ts =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      rw [evalTerms_agreeOn h ts v hf.2]
      exact (h p hf.1).2 _
  | eq t u =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      rw [evalTerm_agreeOn h t v hf.1, evalTerm_agreeOn h u v hf.2]
  | impl a b iha ihb =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      exact Iff.intro (fun hx hy => (ihb v hf.2).mp (hx ((iha v hf.1).mpr hy)))
        (fun hx hy => (ihb v hf.2).mpr (hx ((iha v hf.1).mp hy)))
  | «forall» a ih =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      exact Iff.intro (fun hx d => (ih (shiftEnv v d) hf).mp (hx d))
        (fun hx d => (ih (shiftEnv v d) hf).mpr (hx d))
  | and a b iha ihb =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      exact Iff.intro (fun hx => ⟨(iha v hf.1).mp hx.1, (ihb v hf.2).mp hx.2⟩)
        (fun hx => ⟨(iha v hf.1).mpr hx.1, (ihb v hf.2).mpr hx.2⟩)
  | or a b iha ihb =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      exact Iff.intro (fun hx => hx.imp (iha v hf.1).mp (ihb v hf.2).mp)
        (fun hx => hx.imp (iha v hf.1).mpr (ihb v hf.2).mpr)
  | ex a ih =>
      intro v hf
      unfold LangFormula at hf
      unfold evalFormula
      exact Iff.intro (fun ⟨d, hd⟩ => ⟨d, (ih (shiftEnv v d) hf).mp hd⟩)
        (fun ⟨d, hd⟩ => ⟨d, (ih (shiftEnv v d) hf).mpr hd⟩)

-- ============================================================
-- §3 · Conservatividad relativa a un lenguaje, en FOL⁼
-- ============================================================

/-- 🏁 **El criterio, con EXPANSIONES**: si todo modelo de `T₁` se expande —el mismo dominio, la misma valuación, los
símbolos de `L` sin tocar— a un modelo de `T₂`, entonces `T₂` es conservativa sobre `T₁` en las fórmulas de `L`. -/
theorem fol0_conservativeOver_of_expansion {L : List Char → Prop} {T₁ T₂ : Theory Formula} (hle : T₁ ≤ T₂)
    (hexp : ∀ (D : Type) (M : Model D) (v : Nat → D), (∀ g, T₁.axioms g → evalFormula M v g) →
      Exists fun M' : Model D => And (AgreeOn L M M') (∀ g, T₂.axioms g → evalFormula M' v g)) :
    IsConservativeOver (LangFormula L) T₁ T₂ := by
  refine conservativeOver_of_expansion hle fun I hI => ?_
  obtain ⟨M', hag, h2⟩ := hexp I.D I.M I.v hI
  exact ⟨⟨I.D, M', I.v⟩, h2, fun f hf hJ => (evalFormula_agreeOn hag f I.v hf).mpr hJ⟩

/-- El axioma que DEFINE el símbolo de relación unario `P` por la fórmula `φ` (de variable libre `#0`):
`∀x (P(x) ⇔ φ(x))`. -/
def defAx (P : List Char) (φ : Formula) : Formula :=
  FormulaG.forall (iff (FormulaG.atom P [TermG.var 0]) φ)

/-- `T` más la definición de `P` por `φ`. -/
def extDef (T : Theory Formula) (P : List Char) (φ : Formula) : Theory Formula where
  axioms g := Or (T.axioms g) (g = defAx P φ)

/-- La EXPANSIÓN que interpreta `P` como el conjunto que `φ` define (con la valuación `v` para las demás variables
libres de `φ`); el resto, sin tocar. -/
def expandRel {D : Type} (M : Model D) (v : Nat → D) (P : List Char) (φ : Formula) : Model D where
  func := M.func
  rel s ds := if s = P then
      (match ds with
       | [d] => evalFormula M (shiftEnv v d) φ
       | _ => M.rel s ds)
    else M.rel s ds

/-- Si `P` no está en `L`, la expansión coincide con `M` en `L`. -/
theorem expandRel_agreeOn {L : List Char → Prop} {D : Type} (M : Model D) (v : Nat → D) {P : List Char}
    (φ : Formula) (hP : Not (L P)) : AgreeOn L M (expandRel M v P φ) := by
  intro s hs
  have hsP : Not (s = P) := fun he => hP (he ▸ hs)
  refine ⟨fun _ => rfl, fun ds => ?_⟩
  show Iff (M.rel s ds) (if s = P then _ else M.rel s ds)
  rw [ite_eq_right hsP]

/-- La expansión satisface la definición, si `φ` es del lenguaje y `P` no. -/
theorem expandRel_defAx {L : List Char → Prop} {D : Type} (M : Model D) (v : Nat → D) {P : List Char}
    {φ : Formula} (hP : Not (L P)) (hφ : LangFormula L φ) : evalFormula (expandRel M v P φ) v (defAx P φ) := by
  intro d
  have hrel : (expandRel M v P φ).rel P [d] = evalFormula M (shiftEnv v d) φ := by
    show (if P = P then _ else _) = _
    rw [ite_eq_left rfl]
  have hφ' := evalFormula_agreeOn (expandRel_agreeOn M v φ hP) φ (shiftEnv v d) hφ
  exact ⟨fun h => hφ'.mp (Eq.mp hrel h), fun h => Eq.mpr hrel (hφ'.mpr h)⟩

/-- 🏁 **UNA EXTENSIÓN POR DEFINICIÓN ES CONSERVATIVA**: si el símbolo nuevo `P` no está en `L` y `φ` y los
axiomas de `T` sí, `T + ∀x (P(x) ⇔ φ)` no prueba ninguna fórmula de `L` que `T` no probara. (`T` puede ser
infinita: la prueba pasa por la completitud FUERTE.) -/
theorem fol0_extDef_conservative {L : List Char → Prop} {T : Theory Formula} {P : List Char} {φ : Formula}
    (hP : Not (L P)) (hφ : LangFormula L φ) (hT : ∀ g, T.axioms g → LangFormula L g) :
    IsConservativeOver (LangFormula L) T (extDef T P φ) := by
  refine fol0_conservativeOver_of_expansion (fun _ h => Or.inl h) fun D M v hM => ?_
  refine ⟨expandRel M v P φ, expandRel_agreeOn M v φ hP, fun g hg => ?_⟩
  rcases hg with h | h
  · exact (evalFormula_agreeOn (expandRel_agreeOn M v φ hP) g v (hT g h)).mp (hM g h)
  · rw [h]
    exact expandRel_defAx M v hP hφ

/-- 🔍 **El control: la frescura de `P` es NECESARIA.** Con `P` en el lenguaje, definirlo por `⊥` en la teoría
vacía NO es conservativo: la extensión prueba `∀x (P(x) ⇒ ⊥)`, que es del lenguaje y que la teoría vacía no
prueba (un modelo en que `P` vale en todo lo refuta). Las dos mitades salen del marco: la completitud fuerte y la
solidez. -/
theorem fol0_extDef_not_conservative (P : List Char) :
    Not (IsConservativeOver (LangFormula fun _ => True) Theory.empty (extDef Theory.empty P FormulaG.bottom)) := by
  intro h
  let ψ : Formula := FormulaG.forall (FormulaG.impl (FormulaG.atom P [TermG.var 0]) FormulaG.bottom)
  have hψ : LangFormula (fun _ => True) ψ := ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  -- La extensión prueba `ψ`: todo modelo de la definición hace `P` vacío.
  have hprueba : (extDef Theory.empty P FormulaG.bottom).proves ψ := by
    refine (fol0_proves_iff_entails _ ψ).mpr fun I hI d hd => ?_
    exact ((hI (defAx P FormulaG.bottom) (Or.inr rfl)) d).1 hd
  -- La teoría vacía no lo prueba: en `Unit`, con `P` verdadero en todo, `ψ` es falsa.
  have hno : Not (Theory.empty.proves ψ) := by
    intro hp
    let I : Interp0 := ⟨Unit, ⟨fun _ _ => (), fun _ _ => True⟩, fun _ => ()⟩
    exact Theory.entails_of_proves hp I (fun _ h => h.elim) () trivial
  exact hno (h.2 ψ hψ hprueba)

end TheoryFramework.Instances

#print axioms TheoryFramework.Instances.fol0Semantics
#print axioms TheoryFramework.Instances.fol0Compact
#print axioms TheoryFramework.Instances.fol0_proves_iff_entails
#print axioms TheoryFramework.Instances.fol0_models_iff_entails
#print axioms TheoryFramework.Instances.fol0_consistent_iff_hasModel
#print axioms TheoryFramework.Instances.evalFormula_agreeOn
#print axioms TheoryFramework.Instances.fol0_conservativeOver_of_expansion
#print axioms TheoryFramework.Instances.expandRel_defAx
#print axioms TheoryFramework.Instances.fol0_extDef_conservative
#print axioms TheoryFramework.Instances.fol0_extDef_not_conservative
