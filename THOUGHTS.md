# Thoughts — ProjectName

**Last updated:** 2026-11-09 — revisado como HISTÓRICO (ADR‑262 de RPP): la cabecera y las notas posteriores a la marca anterior, comprobadas contra el árbol; el cuerpo es registro de su fecha y no se ha re‑medido. Antes, 2026-04-20 00:00
**Author**: Julián Calderón Almendros

> 🗄️ **PLANTILLA** (✏️ 2026‑11‑09, ADR‑262 de RPP): es el THOUGHTS.md de la plantilla lean4-project-template —el
> título «ProjectName», los huecos entre corchetes y las «Lessons Learned» son suyos—, con la fecha y el autor que le
> puso el arranque de FOL (`3cc59fa`, 2026‑04‑20) y UNA nota del proyecto, la del 2026‑04‑21 (las tácticas, que están
> hoy en `FOL/Tactics.lean`). Después nadie ha escrito en él: sólo cambiaron sus finales de línea (`800261b`). Lo de
> abajo es registro; lo vigente, [DECISIONS.md](DECISIONS.md) y [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md).

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

[Record the core design philosophy of the project here. Examples:

- Why no Mathlib dependency?
- What mathematical system is being formalized?
- What pedagogical or research goals does this serve?]

---

## Ideas and Alternatives

### 2026-04-21 — Automatización de Tácticas (Fase 4)

**Identidad y Debilitamiento**:
- Se ha implementado con éxito la táctica `derive_hyp` (basada en recursión sobre `List.Mem.head` y `List.Mem.tail` mediante `MetaM`) para cerrar automáticamente cualquier objetivo de la forma `Γ ⊢ f` siempre que `f ∈ Γ`. Esto cubre completamente la regla de identidad.
- Para el debilitamiento (`weakening`), un enfoque similar con una macro/táctica `derive_weaken T` puede tomar un teorema `T : Γ ⊢ f`, aplicar `Derives.weakening`, y luego descargar la submeta de inclusión de listas iterando sobre los elementos de `Γ` (usando `prove_mem` internamente para cada uno). Debido a que las listas `Γ` en nuestras pruebas suelen ser concretas (ej. `[A, B]`), este enfoque sintáctico funcionará bien.

**Automatización de `rewrite_at`**:
- El problema central de `rewrite_at` es que aplicar una regla local en Deducción Natural (`LocalRule`) en una posición `p` arbitraria requiere especificar explícitamente esa posición y las subfórmulas exactas (`sub` y `sub'`), lo que hace que las pruebas sean largas y propensas a errores de índice.
- *Investigación de enfoque*: En lugar de forzar al usuario a proporcionar la posición `p`, podemos crear una táctica en Lean 4 (`derive_rewrite`) que haga lo siguiente:
  1. Tome como argumento la fórmula original (o busque en `Γ` si se aplica hacia adelante) y la regla a aplicar (ej. `LocalRule.doubleNegElim`).
  2. Implemente una función `MetaM` que recorra el AST de la fórmula (`Formula`) construyendo la lista de todas las posiciones válidas (`getAllPositions`).
  3. En cada posición `p`, extraiga la subfórmula con `getAt?` e intente unificarla con el lado izquierdo de la regla dada.
  4. Si unifica, aplique `Derives.rewrite_at` con esa `p` y verifique si el resultado (`replaceAt`) coincide con el objetivo esperado.
- *Desafío*: `LocalRule` en Lean está definido como un `Prop`, lo que significa que no podemos "ejecutarlo" para extraer el patrón directamente en código de nivel de término fácilmente sin usar `Expr` unificators de `Lean.Meta`. 
- *Alternativa más simple*: En lugar de recibir un `LocalRule`, la táctica podría recibir la subfórmula a buscar y la subfórmula de reemplazo explícitamente, y la táctica simplemente encuentra la posición `p` donde ocurre esa subfórmula por primera vez y delega al usuario la prueba de que `LocalRule sub sub'` es válida.

---

## Open Questions

- [ ] [Question 1 — e.g., "Should we use hierarchical partition keys?"]
- [ ] [Question 2 — e.g., "Is the current axiom ordering optimal?"]

---

## Lessons Learned

### Naming Conventions

- Mathlib naming conventions (NAMING-CONVENTIONS.md) significantly improve searchability
- The `mem_X_iff` pattern is more discoverable than `X_is_specified`
- Predicates as prefix (`isNat_zero`) are more consistent than suffix (`zero_is_nat`)

### Module Organization

- Subdirectories should mirror sub-namespaces
- Each subdirectory benefits from a `Basic.lean` for foundational definitions
- Extension modules (`FooExt.lean`) are preferable to modifying frozen modules

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift
- Annotations (`@importance`, `@axiom_system`) help AI prioritize context loading

---

## Future Directions

[Record long-term goals and aspirations for the project.]
