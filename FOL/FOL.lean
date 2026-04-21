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

-- Definición de conectores lógicos derivados
def neg (f : Formula) : Formula := Formula.impl f Formula.bottom

def top : Formula := neg Formula.bottom

def lor (f1 f2 : Formula) : Formula := Formula.impl (neg f1) f2

def land (f1 f2 : Formula) : Formula := neg (Formula.impl f1 (neg f2))

def iff (f1 f2 : Formula) : Formula := land (Formula.impl f1 f2) (Formula.impl f2 f1)

def ex (f : Formula) : Formula := neg (Formula.forall (neg f))

-- Notaciones para hacer las fórmulas legibles
notation "⊥" => Formula.bottom
notation "⊤" => top
prefix:75 "¬ " => neg
infixr:70 " ∧ " => land
infixr:65 " ∨ " => lor
infixr:60 " ⇒ " => Formula.impl
infix:55 " ⇔ " => iff
prefix:80 "∀. " => Formula.forall
prefix:80 "∃. " => ex

-- Coerción para escribir átomos proposicionales más fácilmente (ej. "P" en lugar de .atom "P" [])
instance : Coe String Formula where
  coe s := Formula.atom s []

-- Notación para variables de De Bruijn
prefix:max "#" => Term.var

-- 1.5. LIFT Y SUSTITUCIÓN (De Bruijn)

-- LIFT (Desplazamiento de índices libres)
-- Aumenta en 1 las variables libres a partir de la profundidad 'c'
mutual
def liftTerm (c : Nat) (t : Term) : Term :=
  match t with
  | .var n => if n < c then .var n else .var (n + 1)
  | .func f ts => .func f (liftTerms c ts)

def liftTerms (c : Nat) (ts : List Term) : List Term :=
  match ts with
  | [] => []
  | t :: ts' => liftTerm c t :: liftTerms c ts'
end

def liftFormula (c : Nat) (f : Formula) : Formula :=
  match f with
  | .bottom => .bottom
  | .atom p ts => .atom p (liftTerms c ts)
  | .impl f1 f2 => .impl (liftFormula c f1) (liftFormula c f2)
  | .forall f1 => .forall (liftFormula (c + 1) f1)

-- SUSTITUCIÓN
-- Reemplaza la variable libre 'v' con el término 's'
mutual
def substTerm (v : Nat) (s : Term) (t : Term) : Term :=
  match t with
  | .var n => 
      if n = v then s
      else if n > v then .var (n - 1)
      else .var n
  | .func f ts => .func f (substTerms v s ts)

def substTerms (v : Nat) (s : Term) (ts : List Term) : List Term :=
  match ts with
  | [] => []
  | t :: ts' => substTerm v s t :: substTerms v s ts'
end

def substFormula (v : Nat) (s : Term) (f : Formula) : Formula :=
  match f with
  | .bottom => .bottom
  | .atom p ts => .atom p (substTerms v s ts)
  | .impl f1 f2 => .impl (substFormula v s f1) (substFormula v s f2)
  | .forall f1 => .forall (substFormula (v + 1) (liftTerm 0 s) f1)

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
  
  -- Reglas de Cuantificadores
  | intro_forall : ∀ Γ A, Derives (Γ.map (liftFormula 0)) A → Derives Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives Γ (.forall A) → Derives Γ (substFormula 0 t A)

  -- Lógica Clásica (Reductio ad Absurdum)
  | raa : ∀ Γ A, Derives (neg A :: Γ) ⊥ → Derives Γ A

  -- Debilitamiento (Weakening)
  | weakening : ∀ Γ Γ' f, Derives Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives Γ' f

  -- REGLA MAESTRA: Aplicación de regla en subexpresión exacta
  -- Permite transformar 'f' en 'f'' si existe una posición 'p' donde 'sub' se transforma en 'sub''
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derives Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derives Γ f'

infix:50 " ⊢ " => Derives

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
