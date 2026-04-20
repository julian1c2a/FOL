# Thoughts — ProjectName

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

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

### [Date] — [Topic]

[Record ideas, alternatives you considered, and why you chose a particular approach.]

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
