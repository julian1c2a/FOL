/-
  Formalización de Lógica de Primer Orden (FOL) en Lean 4.
  Este archivo define la sintaxis, un sistema de navegación por posiciones
  y un sistema de derivación que permite aplicar reglas en subexpresiones exactas.
-/

-- 1. SINTAXIS: Términos y Fórmulas
-- Usamos índices de De Bruijn para las variables (Nat) para evitar colisiones de nombres.

inductive Term where
  | var  : Nat → Term
  | func : String → List Term → Term
  deriving Repr, BEq

inductive Formula where
  | bottom : Formula
  | atom   : String → List Term → Formula
  | impl   : Formula → Formula → Formula
  | forall : Formula → Formula
  deriving Repr, BEq

-- Definición de negación como (A → ⊥)
def neg (f : Formula) : Formula := Formula.impl f Formula.bottom

-- 2. NAVEGACIÓN: Posiciones en el árbol (AST)
-- Una posición es un camino desde la raíz hasta una subfórmula.

inductive Pos where
  | root  : Pos
  | left  : Pos → Pos   -- Lado izquierdo de una implicación
  | right : Pos → Pos   -- Lado derecho de una implicación
  | body  : Pos → Pos   -- Dentro de un cuantificador universal
  deriving Repr

-- Función para obtener la subfórmula en una posición dada
def getAt? (f : Formula) : Pos → Option Formula
  | .root => some f
  | .left p =>
      match f with
      | .impl f1 _ => getAt? f1 p
      | _ => none
  | .right p =>
      match f with
      | .impl _ f2 => getAt? f2 p
      | _ => none
  | .body p =>
      match f with
      | .forall f1 => getAt? f1 p
      | _ => none

-- Función para reemplazar una subfórmula en una posición exacta
def replaceAt (f : Formula) (p : Pos) (newSub : Formula) : Formula :=
  match p with
  | .root => newSub
  | .left p' =>
      match f with
      | .impl f1 f2 => .impl (replaceAt f1 p' newSub) f2
      | _ => f
  | .right p' =>
      match f with
      | .impl f1 f2 => .impl f1 (replaceAt f2 p' newSub)
      | _ => f
  | .body p' =>
      match f with
      | .forall f1 => .forall (replaceAt f1 p' newSub)
      | _ => f

-- 3. REGLAS DE TRANSFORMACIÓN
-- Definimos reglas de reescritura lógica que pueden aplicarse localmente.

inductive LocalRule : Formula → Formula → Prop where
  | doubleNegElim : ∀ A, LocalRule (neg (neg A)) A
  | commuteImpl   : ∀ A B C, LocalRule (.impl A (.impl B C)) (.impl B (.impl A C))
  -- Se pueden añadir más reglas como De Morgan, etc.

-- 4. SISTEMA DE DERIVACIÓN (Deducción Natural + Reescritura Local)
-- Este predicado 'Derives' certifica que una fórmula es válida bajo un contexto Γ.

inductive Derives : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives Γ f

  -- Reglas estándar de Deducción Natural
  | intro_impl : ∀ Γ A B, Derives (A :: Γ) B → Derives Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives Γ (.impl A B) → Derives Γ A → Derives Γ B
  | intro_forall : ∀ Γ A, Derives Γ A → Derives Γ (.forall A) -- Simplificado (sin manejo de scope)

  -- REGLA MAESTRA: Aplicación de regla en subexpresión exacta
  -- Permite transformar 'f' en 'f'' si existe una posición 'p' donde 'sub' se transforma en 'sub''
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derives Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derives Γ f'

-- 5. EJEMPLO DE USO
-- Vamos a ver cómo se vería la estructura de una fórmula y su manipulación.

def formula_ejemplo : Formula :=
  .impl (.atom "P" []) (neg (neg (.atom "Q" [])))

-- Queremos aplicar Doble Negación sólo al átomo Q, que está en la posición:
-- Raíz -> Derecha (lado derecho de la implicación)
def posicion_Q : Pos := .right .root

-- La fórmula resultante tras aplicar la regla en esa posición exacta sería:
def formula_simplificada : Formula :=
  replaceAt formula_ejemplo posicion_Q (.atom "Q" [])

-- Comprobación:
-- formula_simplificada es P → Q
