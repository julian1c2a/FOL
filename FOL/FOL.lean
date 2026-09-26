/-
  Formalización de Lógica de Primer Orden (FOL) en Lean 4.
  Este archivo define la sintaxis, un sistema de navegación por posiciones
  y un sistema de derivación que permite aplicar reglas en subexpresiones exactas.
-/

-- 1. SINTAXIS: Términos y Fórmulas
-- Usamos índices de De Bruijn para las variables (Nat) para evitar colisiones de nombres.

/-!
### El tipo de los SÍMBOLOS es un PARÁMETRO (ADR-068, paso 4 del plan)

`TermG S` / `FormulaG S` son el núcleo genérico; `Term`/`Formula` son los `abbrev` de hoy,
`S := String`. ⚠️ El árbol entero sigue diciendo `Term`/`Formula` y **no cambió ni una
línea**: meter el PARÁMETRO costó TRES ficheros (éste, `FOL/DecEq.lean` y
`ROBINSON_PlusPlus/Meta/HilbertSeq.lean`) y los 147 footprints de entonces salieron idénticos (ADR-068).
⛔ Eso **no** es la migración `String`→`List Char` (plan §7.3 de RPP): los `abbrev` siguen en
`String`, y la instanciación en `List Char` queda ABANDONADA en FOL (D7): no mueve ningún
footprint titular de FOL (su `Classical.choice` es el WKL) y su dividendo es de RPP (`strCode`).

⛔⛔ **La razón que aquí se daba para el parámetro era FALSA, y se midió el 2026‑09‑23.**
Decía: *«`List Char` es numerable y sirve para Gödel, pero si Löwenheim-Skolem **ascendente**
entra en la hoja de ruta haría falta migrar otra vez»*. **El parámetro no es lo que bloquea
LS↑**: la cadena de completitud está indexada por `Nat` **por construcción**
(`LindenbaumStep : Nat → …`, `FreshSym.cst : Nat → Sym`), y `EnumSym` —la clase que esto
presentaba como la habilitadora— lo reconoce en su propio docstring: *«con `Sym` genérico esto
no es demostrable —hay tipos no numerables—»* (`SymClasses.lean`). ⇒ **la clase que habilitaría
LS↑ es justo la que es FALSA para los lenguajes que LS↑ necesita.** Un LS↑ a cardinal
arbitrario pide un Lindenbaum **transfinito**, y sin Mathlib no hay Zorn.

⛔ **Y la 2ª entrega —`Canonical0` genérico en el símbolo— queda CERRADA**, por decisión del
propietario del 2026‑09‑23: nadie la consume (RPP y PeanoRF sólo instancian `String`) y su única
justificación escrita era la de arriba.

⭐ **El parámetro se queda**, y no es un error: costó tres ficheros, no rompió nada, y la sintaxis,
`Derives₀`, `LocalRule` y la semántica (`ModelG`) ya son genéricos. Lo que se cierra es seguir
empujándolo por la cadena de completitud.

⛔ **Y el cierre es DEFINITIVO** (decisión del propietario del 2026-09-26): no hay receta para
reabrirla. `Fresh0`, `Henkin0`, `HenkinLimit0`, `Lindenbaum0`, `Canonical0` y `Enumeration` son
`String` por dentro y así se quedan; las clases de `SymClasses.lean` se quedan como MEDIDA de lo
que esa cadena le pediría al tipo de símbolos, y **ningún** módulo las consume. Enhebrarlas
tampoco daría LS↑ (ver arriba).

⭐ Y el **modelo infinito numerable** (`Compacity0.infinite_model_of_large`, que **no** es LS↑)
**no la necesita**: basta con ℵ₀ constantes frescas, y `Fresh0.cst : Nat → String` las da.
-/
inductive TermG (S : Type) where
  | var  : Nat → TermG S
  | func : S → List (TermG S) → TermG S
  deriving Repr, BEq

inductive FormulaG (S : Type) where
  | bottom : FormulaG S
  | atom   : S → List (TermG S) → FormulaG S
  | eq     : TermG S → TermG S → FormulaG S
  | impl   : FormulaG S → FormulaG S → FormulaG S
  | forall : FormulaG S → FormulaG S
  | and    : FormulaG S → FormulaG S → FormulaG S
  | or     : FormulaG S → FormulaG S → FormulaG S
  | ex     : FormulaG S → FormulaG S
  deriving Repr, BEq

abbrev Term := TermG String
abbrev Formula := FormulaG String

namespace Term
  export TermG (var func var.injEq func.injEq rec recOn casesOn)

/-- ⚠️ **El ÚNICO sitio donde parametrizar cuesta algo.** Para un inductivo CON parámetro
Lean genera el `noConfusion` **heterogéneo** (`S = S' → t ≈ t'`), no el homogéneo. Este shim
recupera la forma de siempre, y con él los 13 sitios de llamada del árbol no cambian. -/
theorem noConfusion {P : Prop} {t t' : Term} (h : t = t') :
    TermG.noConfusionType P t t' :=
  TermG.noConfusion (S := String) (S' := String) rfl (heq_of_eq h)
end Term

namespace Formula
  export FormulaG (bottom atom eq impl «forall» and or ex
    atom.injEq eq.injEq impl.injEq «forall».injEq and.injEq or.injEq ex.injEq
    rec recOn casesOn)

/-- ⚠️ El mismo shim que en `Term`. -/
theorem noConfusion {P : Prop} {t t' : Formula} (h : t = t') :
    FormulaG.noConfusionType P t t' :=
  FormulaG.noConfusion (S := String) (S' := String) rfl (heq_of_eq h)

/-- ⚠️ Y la otra: para un inductivo con parámetro Lean genera `.injEq` pero **no** `.inj`. -/
theorem ex.inj {a b : Formula} (h : FormulaG.ex a = FormulaG.ex b) : a = b := by
  rw [FormulaG.ex.injEq] at h; exact h
end Formula

-- Definición de conectores lógicos derivados
-- ⭐ PASO 0-a de la migración `String → Sym` (ADR-069): genéricos en el tipo de los símbolos.
-- ⚠️ El parámetro se llama `Sym` y NO `S`: `S` está ocupado por la TEORÍA (`Formula → Prop`)
-- en `Henkin0`, `Fresh0`, `HenkinLimit0`, `Lindenbaum0` y `Canonical0`, donde además es el
-- binder de la `local notation … ⊢₀* …`.
def neg {Sym : Type} (f : FormulaG Sym) : FormulaG Sym := FormulaG.impl f FormulaG.bottom

def top {Sym : Type} : FormulaG Sym := neg FormulaG.bottom

def iff {Sym : Type} (f1 f2 : FormulaG Sym) : FormulaG Sym :=
  FormulaG.and (FormulaG.impl f1 f2) (FormulaG.impl f2 f1)

-- Notaciones para hacer las fórmulas legibles
notation "⊥" => Formula.bottom
notation "⊤" => top
prefix:75 "¬ " => neg
infixr:70 " ∧ " => Formula.and
infixr:65 " ∨ " => Formula.or
infix:50 " ≐ " => Formula.eq
infixr:60 " ⇒ " => Formula.impl
infix:55 " ⇔ " => iff
prefix:80 "∀. " => Formula.forall
prefix:80 "∃. " => Formula.ex

-- Coerción para escribir átomos proposicionales más fácilmente (ej. "P" en lugar de .atom "P" [])
instance : Coe String Formula where
  coe s := Formula.atom s []

-- Notación para variables de De Bruijn
prefix:max "#" => Term.var

-- 1.5. LIFT Y SUSTITUCIÓN (De Bruijn)
-- ⭐ PASO 0-b de la migración (ADR-069). Esta es la capa que EXPONE el árbol: 32 ficheros de
-- `FOL/` la tocan, 29 de ellos bloqueados, y 107 de RPP. Si el `rfl` sigue cerrando aquí,
-- sigue cerrando en todas partes.

-- LIFT (Desplazamiento de índices libres)
-- Aumenta en 1 las variables libres a partir de la profundidad 'c'
mutual
def liftTerm {Sym : Type} (c : Nat) (t : TermG Sym) : TermG Sym :=
  match t with
  | .var n => if n < c then .var n else .var (n + 1)
  | .func f ts => .func f (liftTerms c ts)

def liftTerms {Sym : Type} (c : Nat) (ts : List (TermG Sym)) : List (TermG Sym) :=
  match ts with
  | [] => []
  | t :: ts' => liftTerm c t :: liftTerms c ts'
end

def liftFormula {Sym : Type} (c : Nat) (f : FormulaG Sym) : FormulaG Sym :=
  match f with
  | .bottom => .bottom
  | .atom p ts => .atom p (liftTerms c ts)
  | .eq t1 t2 => .eq (liftTerm c t1) (liftTerm c t2)
  | .impl f1 f2 => .impl (liftFormula c f1) (liftFormula c f2)
  | .forall f1 => .forall (liftFormula (c + 1) f1)
  | .and f1 f2 => .and (liftFormula c f1) (liftFormula c f2)
  | .or f1 f2 => .or (liftFormula c f1) (liftFormula c f2)
  | .ex f1 => .ex (liftFormula (c + 1) f1)

-- SUSTITUCIÓN
-- Reemplaza la variable libre 'v' con el término 's'
mutual
def substTerm {Sym : Type} (v : Nat) (s : TermG Sym) (t : TermG Sym) : TermG Sym :=
  match t with
  | .var n =>
      if n = v then s
      else if n > v then .var (n - 1)
      else .var n
  | .func f ts => .func f (substTerms v s ts)

def substTerms {Sym : Type} (v : Nat) (s : TermG Sym) (ts : List (TermG Sym)) : List (TermG Sym) :=
  match ts with
  | [] => []
  | t :: ts' => substTerm v s t :: substTerms v s ts'
end

def substFormula {Sym : Type} (v : Nat) (s : TermG Sym) (f : FormulaG Sym) : FormulaG Sym :=
  match f with
  | .bottom => .bottom
  | .atom p ts => .atom p (substTerms v s ts)
  | .eq t1 t2 => .eq (substTerm v s t1) (substTerm v s t2)
  | .impl f1 f2 => .impl (substFormula v s f1) (substFormula v s f2)
  | .forall f1 => .forall (substFormula (v + 1) (liftTerm 0 s) f1)
  | .and f1 f2 => .and (substFormula v s f1) (substFormula v s f2)
  | .or f1 f2 => .or (substFormula v s f1) (substFormula v s f2)
  | .ex f1 => .ex (substFormula (v + 1) (liftTerm 0 s) f1)

-- 2. NAVEGACIÓN: Posiciones en el árbol (AST)
-- Una posición es un camino desde la raíz hasta una subfórmula.

inductive Pos where
  | root  : Pos
  | left  : Pos → Pos   -- Lado izquierdo de op binaria
  | right : Pos → Pos   -- Lado derecho de op binaria
  | body  : Pos → Pos   -- Dentro de un cuantificador
  deriving Repr

-- Función para obtener la subfórmula en una posición dada
def getAt? {Sym : Type} (f : FormulaG Sym) : Pos → Option (FormulaG Sym)
  | .root => some f
  | .left p =>
      match f with
      | .impl f1 _ | .and f1 _ | .or f1 _ => getAt? f1 p
      | _ => none
  | .right p =>
      match f with
      | .impl _ f2 | .and _ f2 | .or _ f2 => getAt? f2 p
      | _ => none
  | .body p =>
      match f with
      | .forall f1 | .ex f1 => getAt? f1 p
      | _ => none

-- Función para reemplazar una subfórmula en una posición exacta
def replaceAt {Sym : Type} (f : FormulaG Sym) (p : Pos) (newSub : FormulaG Sym) : FormulaG Sym :=
  match p with
  | .root => newSub
  | .left p' =>
      match f with
      | .impl f1 f2 => .impl (replaceAt f1 p' newSub) f2
      | .and f1 f2 => .and (replaceAt f1 p' newSub) f2
      | .or f1 f2 => .or (replaceAt f1 p' newSub) f2
      | _ => f
  | .right p' =>
      match f with
      | .impl f1 f2 => .impl f1 (replaceAt f2 p' newSub)
      | .and f1 f2 => .and f1 (replaceAt f2 p' newSub)
      | .or f1 f2 => .or f1 (replaceAt f2 p' newSub)
      | _ => f
  | .body p' =>
      match f with
      | .forall f1 => .forall (replaceAt f1 p' newSub)
      | .ex f1 => .ex (replaceAt f1 p' newSub)
      | _ => f

-- 3. REGLAS DE TRANSFORMACIÓN
-- Definimos reglas de reescritura lógica que pueden aplicarse localmente.

-- ⛔⛔ `LocalRule` y `Derives` SE QUEDAN EN `String`, y es una decisión, no un olvido (ADR-069):
--  1. `Derives` es el cálculo CONTAMINADO: `raa`/`imp_intro` toman funciones de Lean, luego es
--     sintácticamente completo, y ADR-029 prohibe inducir sobre él de forma PERMANENTE (M-11).
--     Es la herramienta de RPP, no el sujeto de la metateoría.
--  2. MEDIDO: RPP lo cita **192** veces y no cita `Derives₀` ni una. Parametrizarlo tocaría esas
--     192 citas y reabriría el coste de ADR-068 (noConfusion heterogéneo, ausencia de `.inj`)
--     con 22 constructores, a cambio de nada: la metateoría de FOL⁼ va sobre `Derives₀`.
--  3. ⛔ **RECTIFICADO (ADR-071)**: ADR-069 dijo aquí «`LocalRule` es su premisa y le
--     sigue», y era FALSO. `LocalRule` es premisa de `rewrite_at`, que está en **`Derives₀`**
--     también ⇒ sigue a `Derives₀` y **sí** se generifica. `Derives` la usa instanciada en
--     `String`, que es exactamente lo que necesita.
--     🔑 *Una premisa compartida sigue al consumidor MÁS GENÉRICO, no al primero que se mire.*
-- ⇒ la generificación se CORTA aquí, y `derives0_to_derives` (Derives0.lean) queda como
--    especialización sólo-String. *Cuando un tipo está contaminado, se declara al lado el que sí
--    sirve* — la misma razón por la que `Derives₀` existe.

inductive LocalRule {Sym : Type} : FormulaG Sym → FormulaG Sym → Prop where
  | commuteImpl   : ∀ A B C, LocalRule (.impl A (.impl B C)) (.impl B (.impl A C))
  -- Se pueden añadir más reglas como De Morgan, etc.

-- 4. SISTEMA DE DERIVACIÓN (Deducción Natural + Reescritura Local)
-- Este predicado 'Derives' certifica que una fórmula es válida bajo un contexto Γ.

inductive Derives : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives Γ f

  -- Reglas estándar de Deducción Natural
  | intro_impl : ∀ Γ A B, Derives (A :: Γ) B → Derives Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives Γ (.impl A B) → Derives Γ A → Derives Γ B

  -- Reglas de conjunción
  | intro_and  : ∀ Γ A B, Derives Γ A → Derives Γ B → Derives Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives Γ (.and A B) → Derives Γ A
  | elim_and_r : ∀ Γ A B, Derives Γ (.and A B) → Derives Γ B

  -- Reglas de disyunción
  | intro_or_l : ∀ Γ A B, Derives Γ A → Derives Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives Γ B → Derives Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives Γ (.or A B) → Derives (A :: Γ) C → Derives (B :: Γ) C → Derives Γ C

  -- Reglas de Cuantificadores
  | intro_forall : ∀ Γ A, Derives (Γ.map (liftFormula 0)) A → Derives Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives Γ (.forall A) → Derives Γ (substFormula 0 t A)

  | intro_ex : ∀ Γ A t, Derives Γ (substFormula 0 t A) → Derives Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives Γ (.ex A) → Derives (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives Γ B

  -- Lógica Intuicionista (Ex Falso Quodlibet)
  | bot_elim : ∀ Γ A, Derives Γ ⊥ → Derives Γ A

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

  -- ════════════════════════════════════════════════════════════════════════
  -- Reglas CLÁSICAS y de GENERALIZACIÓN — constructores desde el 2026‑09‑12
  --
  -- ⭐ D-2 (ADR-028): estos cuatro eran `axiom` (tres en `MetaRules.lean`, uno en
  -- `Theorems/Neg.lean`, uno en `Theorems/Quantifiers.lean`) y **NO tenían por qué serlo**:
  -- sus premisas son ocurrencias POSITIVAS, así que el kernel los acepta aquí. Sólo los que
  -- tienen premisa-FUNCIÓN (`Γ ⊢ A → Γ ⊢ B`) están obligados a ser axiomas — ver M-11.
  --
  -- 🔑 Y esto no es contabilidad: un `axiom` que habita un inductivo **afirma una falsedad
  -- sobre el punto fijo**; un constructor **lo extiende**. Con estos cuatro dentro, `Derives`
  -- tiene cuatro habitantes-basura menos.
  | gen_rule : ∀ Γ A, (∀ n : Term, Derives Γ (substFormula 0 n A)) → Derives Γ (.forall A)
  | dne_rule : ∀ Γ A, Derives Γ (neg (neg A)) → Derives Γ A
  | dne_schema : ∀ Γ A, Derives Γ (.impl (neg (neg A)) A)
  | forall_not_ex_not : ∀ Γ A, Derives Γ (.impl (neg (.forall A)) (.ex (neg A)))

  -- Reglas de Igualdad
  | refl  : ∀ Γ t, Derives Γ (.eq t t)
  | subst : ∀ Γ t₁ t₂ f, Derives Γ (.eq t₁ t₂) → Derives Γ (substFormula 0 t₁ f) → Derives Γ (substFormula 0 t₂ f)

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
