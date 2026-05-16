/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: (none)
-- @axiom_system: none
-- @importance: high
--
-- PropLogic: Propositional Logic — subset of FOLPure without quantifiers or terms.
-- Atoms are propositional variables identified by a String name.

namespace PropLogic

-- ============================================================
-- Fase 1: Sintaxis Proposicional
-- ============================================================

inductive Formula : Type where
  | bottom : Formula
  | atom   (p : String) : Formula
  | impl   (f1 f2 : Formula) : Formula
  | and    (f1 f2 : Formula) : Formula
  | or     (f1 f2 : Formula) : Formula
  deriving DecidableEq, Repr

-- Notaciones
notation:65 "#" p => Formula.atom p
notation:max "⊥" => Formula.bottom

-- Macro para propositions
macro_rules
  | `(⊥) => `(PropLogic.Formula.bottom)

-- ============================================================
-- Fase 2: Posiciones en el Árbol de Fórmulas
-- ============================================================

inductive Pos : Type where
  | root  : Pos
  | left  : Pos → Pos
  | right : Pos → Pos
  deriving DecidableEq, Repr

def getAt? (f : Formula) (p : Pos) : Option Formula :=
  match p with
  | .root => some f
  | .left p' =>
    match f with
    | .impl f1 _ => getAt? f1 p'
    | .and  f1 _ => getAt? f1 p'
    | .or   f1 _ => getAt? f1 p'
    | _ => none
  | .right p' =>
    match f with
    | .impl _ f2 => getAt? f2 p'
    | .and  _ f2 => getAt? f2 p'
    | .or   _ f2 => getAt? f2 p'
    | _ => none

def replaceAt (f : Formula) (p : Pos) (sub : Formula) : Formula :=
  match p with
  | .root => sub
  | .left p' =>
    match f with
    | .impl f1 f2 => .impl (replaceAt f1 p' sub) f2
    | .and  f1 f2 => .and  (replaceAt f1 p' sub) f2
    | .or   f1 f2 => .or   (replaceAt f1 p' sub) f2
    | other => other
  | .right p' =>
    match f with
    | .impl f1 f2 => .impl f1 (replaceAt f2 p' sub)
    | .and  f1 f2 => .and  f1 (replaceAt f2 p' sub)
    | .or   f1 f2 => .or   f1 (replaceAt f2 p' sub)
    | other => other

-- ============================================================
-- Fase 3: Reglas Locales de Reescritura
-- ============================================================

inductive LocalRule : Formula → Formula → Type where
  | commuteImpl (A B C : Formula) :
      LocalRule (.impl A (.impl B C)) (.impl B (.impl A C))

-- ============================================================
-- Fase 4: Sistema de Derivación (Deducción Natural)
-- ============================================================

inductive Derives : List Formula → Formula → Prop where
  | hyp        (Γ : List Formula) (f : Formula) (h : f ∈ Γ) : Derives Γ f
  | intro_impl (Γ : List Formula) (A B : Formula) (h : Derives (A :: Γ) B) : Derives Γ (.impl A B)
  | elim_impl  (Γ : List Formula) (A B : Formula) (h1 : Derives Γ (.impl A B)) (h2 : Derives Γ A) : Derives Γ B
  | intro_and  (Γ : List Formula) (A B : Formula) (h1 : Derives Γ A) (h2 : Derives Γ B) : Derives Γ (.and A B)
  | elim_and_l (Γ : List Formula) (A B : Formula) (h : Derives Γ (.and A B)) : Derives Γ A
  | elim_and_r (Γ : List Formula) (A B : Formula) (h : Derives Γ (.and A B)) : Derives Γ B
  | intro_or_l (Γ : List Formula) (A B : Formula) (h : Derives Γ A) : Derives Γ (.or A B)
  | intro_or_r (Γ : List Formula) (A B : Formula) (h : Derives Γ B) : Derives Γ (.or A B)
  | elim_or    (Γ : List Formula) (A B C : Formula)
      (h_or : Derives Γ (.or A B))
      (h_A  : Derives (A :: Γ) C)
      (h_B  : Derives (B :: Γ) C) : Derives Γ C
  | bot_elim   (Γ : List Formula) (A : Formula) (h : Derives Γ .bottom) : Derives Γ A
  | weakening  (Γ Γ' : List Formula) (f : Formula)
      (h : Derives Γ f) (hSub : ∀ x, x ∈ Γ → x ∈ Γ') : Derives Γ' f
  | rewrite_at (Γ : List Formula) (f f' : Formula) (p : Pos) (sub sub' : Formula)
      (h : Derives Γ f)
      (h_get : getAt? f p = some sub)
      (h_rule : LocalRule sub sub')
      (h_replace : replaceAt f p sub' = f') : Derives Γ f'

scoped notation:50 Γ " ⊢ " f => Derives Γ f

-- Abreviaturas derivadas
def neg (f : Formula) : Formula := .impl f .bottom
def iff (f1 f2 : Formula) : Formula := .and (.impl f1 f2) (.impl f2 f1)

end PropLogic
