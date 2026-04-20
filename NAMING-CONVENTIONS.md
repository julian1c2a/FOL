# Naming Conventions — Mathlib Style

> Permanent reference document for this project.
> All rules are based on the
> [Mathlib Naming Conventions](https://leanprover-community.github.io/contribute/naming.html),
> adapted to the project's specific domain.

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

---

## 1. Capitalization Rules

| Declaration type | Convention | Example |
|------------------|------------|---------|
| Theorems, lemmas (Prop terms) | `snake_case` | `union_comm`, `mem_powerset_iff` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `IsFunction`, `IsNat`, `BoolAlg.Basic` |
| Functions returning `Type` | by return type | `powerset` (→ U → `snake`), `IsNat` (→ Prop → `Upper`) |
| Other `Type` terms | `lowerCamelCase` | `successor`, `fromPeano`, `binUnion` |
| Acronyms | as group upper/lower | `ZFC` (namespace), `zfc` (in snake_case) |

---

## 2. Symbol-to-Word Dictionary

| Symbol | In names | Notes |
|--------|----------|-------|
| ∈ | `mem` | `x ∈ A` → `mem` |
| ∉ | `not_mem` | |
| ∪ | `union` | binary |
| ∩ | `inter` | binary |
| ⋃ | `sUnion` | `s` = "set of sets" |
| ⋂ | `sInter` | idem |
| ⊆ | `subset` | non-strict |
| ⊂ | `ssubset` | strict (extra `s`) |
| 𝒫 | `powerset` | |
| σ | `succ` | |
| ∅ | `empty` | |
| △ | `symmDiff` | |
| ᶜ | `compl` | complement |
| \ | `sdiff` | set difference |
| ×ₛ | `prod` | cartesian product |
| ⟂ | `disjoint` | |
| = | `eq` | often omitted |
| ≠ | `ne` | |
| → | `of` / implicit | conclusion goes first |
| ↔ | `iff` | suffix |
| ¬ | `not` | |
| ∃ | `exists` | |
| ∀ | `forall` | |
| ∘ | `comp` | composition |
| ⁻¹ | `inv` | inverse |
| + | `add` | |
| \* / · | `mul` | |
| − | `sub` (binary) / `neg` (unary) | |
| ^ | `pow` | |
| / | `div` | |
| ∣ | `dvd` | divides |
| ≤ | `le` | |
| < | `lt` | |
| ≥ | `ge` | only for argument swap |
| > | `gt` | only for argument swap |
| 0 | `zero` | |
| 1 | `one` | |

---

## 3. Name Formation Rules (12 rules)

### RULE 1 — Conclusion first, hypotheses with `_of_`

The name describes **what is proved**, not how. Hypotheses are added with `_of_`:

```
-- Pattern: A → B → C
-- Name:    c_of_a_of_b
-- Order:   conclusion_of_hypothesis1_of_hypothesis2

-- Example:
-- Theorem: isNat n → isNat (σ n)
-- Name:    isNat_succ_of_isNat
--          ^^^^^^^^^ ^^^^^^^^^^
--          conclusion hypothesis
```

### RULE 2 — Biconditionals carry suffix `_iff`

```
-- Theorem: x ∈ (𝒫 A) ↔ x ⊆ A
-- Name:    mem_powerset_iff
--          ^^^ ^^^^^^^^ ^^^
--          ∈    𝒫        ↔
```

### RULE 3 — Eliminate `_wc` — Use `.mp` / `.mpr` or `_of_`

The `_wc` suffix (if used historically) is replaced by Mathlib convention:

```
-- For forward direction of an iff:
--    inter_eq_empty_iff_disjoint.mp
-- For backward direction:
--    inter_eq_empty_iff_disjoint.mpr
-- As standalone theorem:
--    disjoint_of_inter_eq_empty    (conclusion_of_hypothesis)
```

### RULE 4 — Algebraic properties → short axiomatic name

```
-- commutativity:   union_comm, inter_comm
-- associativity:   inter_assoc, union_assoc
-- absorption:      union_inter_self
-- distributivity:  union_inter_distrib_left
```

**Standard axiomatic suffixes (Mathlib):**

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_comm` | commutativity | `union_comm` |
| `_assoc` | associativity | `inter_assoc` |
| `_refl` | reflexivity | `subset_refl` |
| `_irrefl` | irreflexivity | `ssubset_irrefl` |
| `_symm` | symmetry | `disjoint_symm` |
| `_trans` | transitivity | `subset_trans` |
| `_antisymm` | antisymmetry | `subset_antisymm` |
| `_asymm` | asymmetry | `ssubset_asymm` |
| `_inj` | injectivity (iff) | `succ_inj` (σ a = σ b ↔ a = b) |
| `_injective` | injectivity (pred) | `succ_injective` |
| `_self` | operation with itself | `union_self` (A ∪ A = A) |
| `_left` / `_right` | lateral variant | `union_subset_left` |
| `_cancel` | cancellation | `add_left_cancel` |
| `_mono` | monotonicity | `powerset_mono` |

### RULE 5 — Predicates as prefix, operations in infix order

```
-- Predicate as prefix:   isNat_zero (not zero_is_nat)
-- Exception:             succ_injective (_injective, _surjective are always suffix)
```

### RULE 6 — Standard abbreviations for frequent conditions

| Instead of | Use | Meaning |
|-----------|-----|---------|
| `zero_lt_x` | `pos` | x > 0 |
| `x_lt_zero` | `neg` | x < 0 |
| `x_le_zero` | `nonpos` | x ≤ 0 |
| `zero_le_x` | `nonneg` | x ≥ 0 |

### RULE 7 — Definitions with `Is` for Prop predicates

```
-- Definition (Prop): def IsNat (n : U) : Prop := ...     (UpperCamelCase)
-- In theorem names:  isNat_zero, isNat_succ, isNat_of_mem (lowerCamelCase in snake_case)
```

### RULE 8 — Functions/constructors non-Prop: `lowerCamelCase`

```
-- powerset (not PowerSetOf)  — lowerCamelCase, remove "Of"
-- union (not BinUnion)       — "Bin" removed (binary by arity)
-- sep (not SpecSet)          — "sep" = Mathlib standard for separation
-- comp (not FunctionComposition)
-- image (not ImageSet)
```

### RULE 9 — Specifications: `_iff` and `mem_X_iff`

The pattern `X_is_specified` is replaced by `mem_X_iff`:

```
-- mem_succ_iff      (was: successor_is_specified)
-- mem_inter_iff     (was: BinInter_is_specified)
-- mem_union_iff     (was: BinUnion_is_specified)
-- mem_sep_iff       (was: SpecSet_is_specified)
-- mem_sdiff_iff     (was: Difference_is_specified)
```

### RULE 10 — Uniqueness and existence

```
-- inter_unique      (was: BinInterUniqueSet)
-- powerset_unique   (was: PowerSetExistsUnique)
-- sUnion_unique     (was: UnionExistsUnique)
```

### RULE 11 — Names with `_left` / `_right`

```
-- subset_union_left    — A ⊆ (A ∪ B), subset is left argument
-- subset_union_right   — B ⊆ (A ∪ B), subset is right argument
```

### RULE 12 — Named theorems (proper names)

```
-- cantor_no_surjection          — proper name + description (OK in Mathlib)
-- cantor_schroeder_bernstein    — proper name (kept as-is)
```

> **NOTE:** Mathematical proper names are kept as-is in Mathlib.
> Only operational words are normalized (`mem`, `union`, etc.).

---

## 4. Quick Reference Tables

### 4.1 Definitions — common renamings

| Before | After | Rationale |
|--------|-------|-----------|
| `BinInter` | `inter` | remove "Bin" |
| `BinUnion` | `union` | remove "Bin" |
| `PowerSetOf` | `powerset` | lowerCamelCase, remove "Of" |
| `UnionSet` | `sUnion` | "s" = set-of-sets |
| `SpecSet` | `sep` | Mathlib standard |
| `successor` | `succ` | standard abbreviation |
| `FunctionComposition` | `comp` | standard abbreviation |
| `IdFunction` | `id` | standard abbreviation |
| `InverseFunction` | `inv` | standard abbreviation |
| `ImageSet` | `image` | simplification |
| `PreimageSet` | `preimage` | simplification |
| `Restriction` | `restrict` | simplification |
| `isNat` | `IsNat` | UpperCamelCase (Prop) |
| `isSingleValued` | `IsSingleValued` | UpperCamelCase (Prop) |
| `isInductive` | `IsInductive` | UpperCamelCase |

### 4.2 Theorems — `_is_specified` → `mem_X_iff`

| Before | After | Breakdown |
|--------|-------|-----------|
| `PowerSet_is_specified` | `mem_powerset_iff` | mem + 𝒫 + ↔ |
| `successor_is_specified` | `mem_succ_iff` | mem + σ + ↔ |
| `BinInter_is_specified` | `mem_inter_iff` | mem + ∩ + ↔ |
| `BinUnion_is_specified` | `mem_union_iff` | mem + ∪ + ↔ |
| `SpecSet_is_specified` | `mem_sep_iff` | mem + sep + ↔ |

### 4.3 Theorems — algebraic properties

| Before | After | Breakdown |
|--------|-------|-----------|
| `BinUnion_commutative` | `union_comm` | ∪ + commutativity |
| `BinInter_commutative` | `inter_comm` | ∩ + commutativity |
| `BinInter_associative` | `inter_assoc` | ∩ + associativity |
| `subseteq_reflexive` | `subset_refl` | ⊆ + reflexivity |
| `subseteq_transitive` | `subset_trans` | ⊆ + transitivity |
| `subseteq_antisymmetric` | `subset_antisymm` | ⊆ + antisymmetry |

---

## 5. Migration Note

During development, names are renamed progressively following these conventions.
Priority order for migration:

1. Base modules (axioms): `Extension`, `Specification`, `Union`, `PowerSet`
2. Natural numbers: `Nat.Basic` + arithmetic modules
3. Functions and relations: `Functions`, `Relations`
4. Derived structures: Boolean algebras, cardinality, etc.

Each rename is verified with full compilation before proceeding.
