# -*- coding: utf-8 -*-
import io, sys, json, os
sys.stdout.reconfigure(encoding='utf-8')
R = 'E:/dropbox/github/lean4/FOL/'
D = 'C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/exp-juez/'
def rd(f): return io.open(R + f, encoding='utf-8').read()
def lines(f, a, b): return '\n'.join(rd(f).split('\n')[a - 1:b])
E = []
def add(f, buscar, reemplazar, motivo): E.append(dict(fichero=f, buscar=buscar, reemplazar=reemplazar, motivo=motivo))

AUD = 'auditoría 2026‑09‑27'
# ── 1-3 · docs de estado ─────────────────────────────────────────────────────────
WKL = "y ese `Classical.choice` es el WKL de `Lindenbaum0` (ADR-041)."
WKLr = ("y ese `Classical.choice` **no** es el `if` de `Lindenbaum0`, como decía ADR-041: la auditoría del "
        "2026-09-27 midió `lindenbaum_lemma₀` y `henkin_completion₀`, con los mismos enunciados, en `[propext, Quot.sound]` "
        "(etapa impredicativa, más las rutas de `String`, `open Classical`, `bnd` e `invOf` corregidas). Lo que queda es clásico "
        "de verdad: el lema de la verdad sobre un maximal ARBITRARIO (`max_cons_*`, cuyos enunciados implican ¬¬P→P, medido), "
        "el `byContradiction` final (forma de Markov, hipótesis) y la semántica en `Prop` (`derives0_soundness` implica ¬¬P→P, "
        "medido). La equivalencia con WKL₀ es de matemática inversa, sobre RCA₀, y no dice dónde está el choice en Lean.")
for f in ['CURRENT-STATUS-PROJECT.md', 'NEXT-STEPS.md', 'README.md']:
    add(f, WKL, WKLr, "Afirmación de LOCALIZACIÓN refutada: exp-esencial/E4_Lindenbaum.lean (lindenbaum_nochoice [propext]) y "
        "exp-juez/Comb.lean (lindenbaum_lemma_nc y henkin_completion_nc [propext, Quot.sound], mismo tipo comprobado); esencialidad "
        "de max_cons_* y de derives0_soundness en exp-esencial/E3 y E1.")
# ── 4-5 · FOL.lean y SymClasses ─────────────────────────────────────────────────
add('FOL/FOL.lean',
    "footprint titular de FOL (su `Classical.choice` es el WKL) y su dividendo es de RPP (`strCode`).",
    "footprint titular de FOL (lo que `String` aporta al `Classical.choice` es de RUTA y se quita sin salir de\n"
    "`String`: " + AUD + ", medido) y su dividendo es de RPP (`strCode`).",
    "«su Classical.choice es el WKL» es la misma localización refutada; y el aporte de String es de ruta (exp-string/E4: "
    "FreshSym/EnumSym String en [propext, Quot.sound]).")
add('FOL/SymClasses.lean',
    "footprint titular de FOL (su `Classical.choice` es el WKL).",
    "footprint titular de FOL (y lo que `String` añadía al `Classical.choice` era de RUTA, no del tipo: con\n"
    "`instLawfulBEqString` y `String.exists_eq_ofList`, `FreshSym String` y `EnumSym String` miden\n"
    "`[propext, Quot.sound]`; " + AUD + ").",
    "Misma localización refutada; exp-inv/Fresh.lean (Exp.freshString) y exp-inv/Enum.lean (Exp.enumString) [propext, Quot.sound].")
# ── 6 · Fresh0 §Footprint ───────────────────────────────────────────────────────
add('FOL/Fresh0.lean', lines('FOL/Fresh0.lean', 57, 69),
    "`Classical.choice` entra por tres vías, y la " + AUD + " midió que **ninguna es necesaria**\n"
    "para estos enunciados:\n\n"
    "* `Rename.invOf` (la inversa GLOBAL de `shift`, fabricada con elección) en `derivesSet0_shift_inv`:\n"
    "  basta una inversa LOCAL sobre los símbolos del contexto finito, con `DecidableEq String`; con ella\n"
    "  `derivesSet0_shift_inv` y `shiftTheory_consistent₀` miden `[propext, Quot.sound]`;\n"
    "* el tercio excluso de `cst_bound_sym` sobre `∃ k, cst k = s` (§4): con la cota `s.utf8ByteSize`\n"
    "  (`(cst m).utf8ByteSize = m + 1`) el mismo enunciado mide `[propext, Quot.sound]`;\n"
    "* `String`, pero al COMPARAR, no al descomponer: `not_eq_of_beq_eq_false rfl` pide `ReflBEq String`, y\n"
    "  la síntesis la saca de `String.instOrd`/`instLawfulEqOrd`/`instTransOrd`, que llevan choice; con\n"
    "  `of_decide_eq_false rfl` (o pasando `instLawfulBEqString`) `cst_zero_ne`/`cst_ne_shift` miden\n"
    "  `[propext]`. No es el muro de `../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §7:\n"
    "  `String.decEq`, `String.append_right_inj` y `shift_inj` nunca llevaron choice.\n\n"
    "⚠️ Y el `Classical.choice` de la completitud tampoco es el `if IsConsistent …` de Lindenbaum: ver\n"
    "`FOL.Lindenbaum0`, «Dónde está la no‑finitud».",
    "§Footprint da las tres vías por necesarias («la matemática», «deuda del núcleo») y localiza la completitud en el if: "
    "las tres medidas evitables (exp-bnd-invOf/Exp.lean derivesSet0_shift_inv'; exp-string/E3,E8; exp-inv/Fresh.lean; exp-string/E9 "
    "trampa de instancias) y el if refutado (E4, Comb).")
# ── 7 · Henkin0 cabecera ────────────────────────────────────────────────────────
add('FOL/Henkin0.lean',
    "`Classical.choice` que aparece viene de ahí, de `Exists.choose`, del tercio excluso de\n"
    "`cst_bound_sym` y de los lemas de `String` del núcleo tras `shift_inj`/`cst_inj`\n"
    "(`String.append_right_inj`; `FOL.Fresh0` §Footprint, ADR",
    "`Classical.choice` que aparece viene de ahí, de `Exists.choose`, del tercio excluso de\n"
    "`cst_bound_sym`, de la `ReflBEq String` que la síntesis saca de `String.instOrd` en\n"
    "`cst_zero_ne`/`cst_ne_shift` (⚠️ `String.append_right_inj` y `shift_inj` miden `[propext, Quot.sound]`)\n"
    "y, aquí mismo, del `open Classical` que decide `x = henkinAx c A` en `henkin_step_consistent₀`.\n"
    "Todas son evitables (" + AUD + ", medido; la inversa GLOBAL `invOf` sólo hace falta en\n"
    "`Compacity0.hasLargeModels_shift`): partiendo el contexto con la disyunción que ya da la hipótesis\n"
    "(sin decidir nada), `henkin_step_consistent₀` mide `[propext, Quot.sound]` (`FOL.Fresh0` §Footprint, ADR",
    "Atribuye choice a String.append_right_inj (medido [propext, Quot.sound], exp-string/E1) y omite el propDecidable propio "
    "(exp-deceq/E1 con DecEq y E4 con ctx_split: [propext, Quot.sound]).")
# ── 8 · DecEq ───────────────────────────────────────────────────────────────────
add('FOL/DecEq.lean', lines('FOL/DecEq.lean', 59, 62),
    "sus `Decidable` siguen resolviéndose por `Classical.propDecidable`. Cambiarlo movería el footprint\n"
    "de teoremas ya publicados y medidos. ⚠️ Lo que aquí se decía después era FALSO (" + AUD + ",\n"
    "medido): ni «no se ganaría nada» —con este módulo importado, la misma prueba de\n"
    "`Henkin0.henkin_step_consistent₀` mide `[propext, Quot.sound]` y la de\n"
    "`Lindenbaum0.derivesSet0_intro_impl`, `[propext]`— ni el `if IsConsistent₀ …` de `FOL.Lindenbaum0`\n"
    "«tiene que seguir ahí»: con una etapa impredicativa, `lindenbaum_lemma₀` no lo necesita. Retrofitarlo\n"
    "es decisión del propietario: mueve filas de footprint.",
    "exp-deceq/E1,E2,E3 (con DecEq) y exp-esencial/E4 + exp-juez/Comb (Lindenbaum sin if).")
# ── 9 · Compacity0 §Footprint ───────────────────────────────────────────────────
add('FOL/Compacity0.lean', lines('FOL/Compacity0.lean', 87, 100),
    "Los titulares, `[propext, Classical.choice, Quot.sound]`. ⚠️ **El `Classical.choice` viene de\n"
    "`model_existence_lemma₀` y de `derives0_soundness`** (la semántica es clásica: `FOL.Soundness0`), con\n"
    "varias procedencias (las enumeran `FOL.Canonical0` y `FOL.Lindenbaum0`). ⚠️ Lo que se decía aquí,\n"
    "que la que da la fuerza es el `if IsConsistent₀` de `FOL.Lindenbaum0` (el WKL), es FALSO en Lean\n"
    "(" + AUD + ", medido): ese `if` se quita y `henkin_completion₀` mide `[propext, Quot.sound]`. Lo\n"
    "irreducible es el lema de la verdad sobre un maximal arbitrario y la semántica en `Prop` (el enunciado\n"
    "de `model_existence_lemma₀` implica ¬P ∨ ¬¬P, y el de `derives0_soundness`, ¬¬P → P). ⛔ Esto **no** es\n"
    "finitario, al revés que `FOL.Finitary0`: es vía W, no vía H.\n"
    "⚠️ **En §3 el `Classical.choice` NO viene sólo de la completitud**: `infTheory_finSat` y\n"
    "`evalTerm_updateCsts` lo llevan SIN pasar por `model_existence_lemma₀`. Es el de `FOL.Fresh0`\n"
    "(`cst_bound_list`, `cst_inj`): el tercio excluso de `cst_bound_sym` y la `ReflBEq String` que\n"
    "`cst_zero_ne` saca de `String.instOrd` —comparar, no descomponer—; las dos, evitables (medido: con\n"
    "ellas corregidas, los dos titulares miden `[propext, Quot.sound]`).\n"
    "`infinite_model_of_large` pasa por `Rename.invOf` también fuera de `model_existence_lemma₀` (vía\n"
    "`hasLargeModels_shift`, que necesita la inversa GLOBAL de `shift`). El conjunto de axiomas es el\n"
    "mismo; las procedencias son varias.",
    "Localiza la fuerza en el if (refutado: E4, Comb) y describe el choice de §3 como «descomponer» String (es comparar: "
    "exp-string/E9; evalTerm_updateCsts e infTheory_finSat en [propext, Quot.sound] en exp-string/E4). Esencialidad: "
    "exp-esencial/E7 (WLEM) y E1 (DNE).")
# ── 10-11 · Skolem0 ─────────────────────────────────────────────────────────────
add('FOL/Skolem0.lean', lines('FOL/Skolem0.lean', 113, 115),
    "⚠️ El `if f = c` usa `String.decEq`, que **no** trae `Classical.choice` (`#print axioms String.decEq`:\n"
    "vacío). Lo que lo trae no es `String` sino RUTAS concretas del núcleo (" + AUD + ", medido):\n"
    "decodificar (`String.toList`/`String.ofList_toList`; `String.exists_eq_ofList` no lo trae) y el ORDEN\n"
    "(la `ReflBEq String` derivada de `String.instOrd` al usar `not_eq_of_beq_eq_false`;\n"
    "`instLawfulBEqString` no lo trae). -/",
    "«lo trae DESCOMPONER un String, no compararlo»: exp-string/E9 (not_eq_of_beq_eq_false sobre String lleva choice; "
    "beq_iff_eq no) y exp-inv/Enum.lean (String.exists_eq_ofList [propext]).")
add('FOL/Skolem0.lean', lines('FOL/Skolem0.lean', 81, 84),
    "`skolem_conservative₀` y `henkin_conservative₀`, `[propext, Classical.choice, Quot.sound]` — el\n"
    "`Classical.choice` es el de `completeness₀` (⚠️ que NO es el `if` de Lindenbaum: ver `FOL.Lindenbaum0`),\n"
    "más la elección del testigo y el de `derives0_soundness` (`FOL.Soundness0`: la semántica es clásica).\n"
    "⛔ Vía W, no vía H. ⚠️ Pero el enunciado es SINTÁCTICO y la ruta semántica no es obligada: el caso\n"
    "Henkin (`henkin_conservative₀`) tiene prueba sintáctica con `[propext, Quot.sound]` (" + AUD + ",\n"
    "medido); el caso con prefijo, hipótesis (Herbrand/ε).",
    "«el WKL de siempre» (localización refutada) y omite que henkin_conservative₀ sale sintáctico sin choice "
    "(exp-esencial/E8_HenkinSintactico.lean, mismo enunciado).")
# ── 12-13 · HenkinLimit0 (bnd y §Footprint) ─────────────────────────────────────
add('FOL/HenkinLimit0.lean', lines('FOL/HenkinLimit0.lean', 182, 184),
    "/-- La cota de `cst_bound_formula`, elegida. ⚠️ `noncomputable`: es `Exists.choose`, y ahí entra\n"
    "`Classical.choice`. ⚠️ **Sí** es evitable con este mismo enunciado (" + AUD + ", medido): la\n"
    "cota calculada «mayor `utf8ByteSize` de los símbolos de función», con `(cst n).utf8ByteSize = n + 1`,\n"
    "cumple `bnd_spec` con `[propext, Quot.sound]`, no lleva ningún axioma y deja `bnd`, `hidx` y `hen`\n"
    "computables. Si se deja así es porque lo que se construye es una **teoría**, no un programa. -/",
    "«No es evitable con este enunciado»: exp-bnd-invOf/Exp.lean (bndC sin axiomas, bndC_spec [propext, Quot.sound], "
    "hidxC computable con #eval) y exp-inv/Bnd.lean.")
add('FOL/HenkinLimit0.lean', lines('FOL/HenkinLimit0.lean', 73, 76),
    "`[propext, Classical.choice, Quot.sound]` y **cero axiomas del proyecto**. El `Classical.choice`\n"
    "entra por `Exists.choose` en `bnd` (§2), por `String` (§7 del plan) y por lo que ya traen\n"
    "`shiftTheory_consistent₀` (`Rename.invOf`) y `henkin_step_consistent₀`. ⚠️ Las cuatro son evitables\n"
    "(" + AUD + ", medido): con ellas corregidas, `hen_consistent`, `henLimit_consistent₀` y\n"
    "`henLimit_witness` miden `[propext, Quot.sound]`. Y el de la completitud no es el\n"
    "`if IsConsistent …` de Lindenbaum: ver `FOL.Lindenbaum0`.",
    "Da por buenas las procedencias y localiza la completitud en el if. exp-juez/Comb.lean: henC_consistent, "
    "henLimitC_consistent₀, henLimitC_witness [propext, Quot.sound].")
# ── 14 · Enumeration §Footprint ─────────────────────────────────────────────────
add('FOL/Enumeration.lean', lines('FOL/Enumeration.lean', 65, 66),
    lines('FOL/Enumeration.lean', 65, 66) + " ⚠️ Y `String.toList`/`String.ofList_toList` llevan\n"
    "`Classical.choice` (v4.31, medido: el decodificador UTF‑8): por ellos `natToString_surj`,\n"
    "`natToTerm_surj`, `natToTerms_surj`, `natToFormula_surj` y la instancia `EnumSym String` miden\n"
    "`[propext, Classical.choice, Quot.sound]`. Es de RUTA: con `String.exists_eq_ofList` (`[propext]`)\n"
    "`natToString_surj` y `natToFormula_surj` miden `[propext, Quot.sound]` (" + AUD + ").\n"
    "`natToFormula` y las demás funciones: `[propext, Quot.sound]`.",
    "«Cero axiomas… núcleo de Lean»: 7 constantes con choice en decls.tsv; exp-string/E3,E4,E8 y exp-inv/Enum.lean.")
# ── 15 · Theorems/Eq ────────────────────────────────────────────────────────────
add('FOL/Theorems/Eq.lean', lines('FOL/Theorems/Eq.lean', 27, 27),
    lines('FOL/Theorems/Eq.lean', 27, 27) + "\n--\n"
    "-- ⚠️ 2026-09-27 (auditoría, medido): el módulo NO quedó limpio del todo. `substTerm_subst_comm_succ`,\n"
    "-- `substTerms_subst_comm_succ` y `subst_subst_comm_succ` (RPP lo usa en `Meta/Hilbert.lean`) llevan\n"
    "-- `[propext, Classical.choice, Quot.sound]`: tres `simp` del caso `var` reescriben con\n"
    "-- `Nat.left_eq_add`/`Nat.add_eq_left`, que en v4.31 llevan choice. Con\n"
    "-- `simp [..., -Nat.left_eq_add, -Nat.add_eq_left]` la misma prueba mide `[propext, Quot.sound]`.",
    "La cabecera da el módulo por limpio: decls.tsv y exp-varios/Eq0orig (control) / Eq4min [propext, Quot.sound].")
# ── 16-17 · Lindenbaum0 ─────────────────────────────────────────────────────────
add('FOL/Lindenbaum0.lean', lines('FOL/Lindenbaum0.lean', 44, 56),
    "Aquí se decía que en una línea:\n\n"
    "    if IsConsistent₀ (Sₙ ∪ {φₙ}) then … else …\n\n"
    "Esa condición es **Π⁰₁** y se decide con `Classical.propDecidable`, y se afirmaba que **ahí cabe\n"
    "toda la no‑finitud del teorema de completitud** (el WKL de\n"
    "`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md` §6.3).\n\n"
    "⛔ **Eso es FALSO en Lean** (" + AUD + ", medido). La etapa no necesita decidir nada: con\n\n"
    "    Step (n+1) x := Step n x ∨ (x = φₙ ∧ IsConsistent₀ (Step n ∪ {φₙ}))\n\n"
    "(posible porque `Prop` es impredicativo; la consistencia es negativa y basta ¬¬(C ∨ ¬C)), el mismo\n"
    "`lindenbaum_lemma₀` mide `[propext]` para cualquier enumeración sobreyectiva, y el límite queda\n"
    "CERRADO por deducción sin tercio excluso, así que `henkin_completion₀` también sale, con el mismo\n"
    "enunciado, en `[propext, Quot.sound]` (corrigiendo además las rutas de `String`, `bnd`, `invOf` y el\n"
    "`filter` de `derivesSet0_intro_impl`). Lo clásico de verdad está al USAR la teoría: el tercio excluso\n"
    "sobre la pertenencia a un maximal ARBITRARIO (`max_cons_contains`, y en `FOL.Canonical0`\n"
    "`max_cons_impl_iff`, `max_cons_or`, `max_cons_complete`: sus enunciados implican ¬¬P → P, medido) y\n"
    "el `byContradiction` final de `completeness₀`. La equivalencia completitud ≡ WKL₀ vale sobre RCA₀,\n"
    "donde la teoría completa tiene que existir como conjunto; en Lean existe gratis como predicado.\n\n"
    "⚠️ Los demás `Classical.choice` que llegan aquí (`Exists.choose` de `bnd`, el tercio excluso de\n"
    "`cst_bound_sym`, `Rename.invOf`, `henkin_step_consistent₀`, `String`) son también evitables.",
    "La tesis de localización (ADR-040 §2) está refutada: exp-esencial/E4_Lindenbaum.lean y exp-juez/Comb.lean "
    "(limit_max, limit_closed [propext]; lindenbaum_lemma_nc y henkin_completion_nc [propext, Quot.sound], tipos iguales). "
    "Esencialidad de max_cons_*: exp-esencial/E3_MaxCons.lean.")
add('FOL/Lindenbaum0.lean', lines('FOL/Lindenbaum0.lean', 131, 132),
    "/-- La condición del `if` es **Π⁰₁** y se decide con `Classical.propDecidable`. ⚠️ No es «toda la\n"
    "no‑finitud del teorema», como se decía: la etapa impredicativa la evita (ver la cabecera). -/",
    "Docstring «⛔ Aquí está toda la no‑finitud del teorema»: refutado por E4 y Comb.")
# ── 18-19 · Canonical0 ──────────────────────────────────────────────────────────
add('FOL/Canonical0.lean', lines('FOL/Canonical0.lean', 57, 64),
    "Todo este módulo es constructivo salvo el uso de `Classical.choose` en `quotientOut` y el tercio\n"
    "excluso (`byContradiction`, `by_cases`, `em`, `byCases`). ⚠️ Aquí se decía que la no‑finitud del\n"
    "teorema está **una capa más abajo**, en el `if IsConsistent₀ (Sₙ ∪ {φₙ})` de `FOL.Lindenbaum0`\n"
    "(ADR‑040 §2), y que «ese `Classical.choice` es el WKL». ⛔ **Es al revés** (" + AUD + ", medido):\n"
    "`henkin_completion₀` tiene prueba con `[propext, Quot.sound]`, y el `Classical.choice` irreducible\n"
    "está AQUÍ: en `max_cons_contains`/`max_cons_impl_iff`/`max_cons_or`/`max_cons_complete`, cuyos\n"
    "enunciados (sobre un maximal ARBITRARIO) implican ¬¬P → P; en `model_existence_lemma₀`, cuyo enunciado\n"
    "implica ¬P ∨ ¬¬P; y en el `byContradiction` final de `completeness₀` (forma de Markov; hipótesis).\n"
    "`quotientOut` es evitable: con `Quot.lift` sobre listas el modelo canónico sale computable. La\n"
    "completitud para lenguajes numerables es **≡ WKL₀** sobre RCA₀ (Simpson IV.3.3), y WKL₀ es\n"
    "**Π⁰₂‑conservativo sobre PRA** (Friedman); pero eso es matemática inversa y no localiza el\n"
    "`Classical.choice` de Lean.",
    "Localización refutada (E4, Comb) y la del choice irreducible, medida: exp-esencial/E3 (DNE), E7 (WLEM), E5 (cociente "
    "por listas, canonicalModel' sin noncomputable).")
add('FOL/Canonical0.lean', lines('FOL/Canonical0.lean', 577, 579),
    "⛔ Aquí se decía que lo que su `Classical.choice` tiene de no finitario es el `if IsConsistent₀ …` de\n"
    "`FOL.Lindenbaum0` (el WKL). ⚠️ FALSO en Lean (" + AUD + ", medido): viene del lema de la verdad\n"
    "sobre un maximal arbitrario (`max_cons_*`) y del `byContradiction` de abajo. Ver la cabecera. -/",
    "Mismo error de localización en el docstring del titular.")
# ── 20-23 · menciones «el WKL» como localización en candidatos ───────────────────
add('FOL/SkolemN0.lean',
    "⚠️ El `Classical.choice` del footprint **no es nuevo**: `completeness₀` ya lo trae (es el WKL). Lo",
    "⚠️ El `Classical.choice` del footprint **no es nuevo**: `completeness₀` ya lo trae (⚠️ no es el `if`\n"
    "de Lindenbaum: ver `FOL.Lindenbaum0`). Lo",
    "«(es el WKL)»: localización refutada (E4, Comb).")
add('FOL/SkolemHerbrand0.lean',
    "(`skolem_conservative_nf₀`) pasa por la completitud (el WKL). Por la estructura de la prueba entra",
    "(`skolem_conservative_nf₀`) pasa por la completitud semántica (`completeness₀`). Por la estructura de la prueba entra",
    "«(el WKL)»: localización refutada (E4, Comb).")
add('FOL/Interpolation0.lean',
    "`completeness₀` (el WKL, `Classical.choice`). `lk0_refute` la da SINTÁCTICAMENTE, leyendo `Γ ⟹ Δ`",
    "`completeness₀` (`Classical.choice`). `lk0_refute` la da SINTÁCTICAMENTE, leyendo `Γ ⟹ Δ`",
    "«(el WKL, …)»: localización refutada (E4, Comb).")
add('FOL/SkolemNF0.lean',
    "normal son **interderivables**. 📏 Y las dos mitades **sin `Classical.choice`** — el WKL entra",
    "normal son **interderivables**. 📏 Y las dos mitades **sin `Classical.choice`** — el choice entra",
    "«el WKL entra»: localización refutada (E4, Comb).")
# ── 24-28 · REFERENCE.md ────────────────────────────────────────────────────────
add('REFERENCE.md',
    "`natToFormula` y su sobreyectividad, **computables**, cero axiomas",
    "`natToFormula` (**computable**, `[propext, Quot.sound]`) y su sobreyectividad —⚠️ `natToFormula_surj` lleva "
    "`Classical.choice` (vía `String.toList`/`ofList_toList`), evitable con `String.exists_eq_ofList` (" + AUD + ", "
    "medido)—, cero axiomas **del proyecto**",
    "decls.tsv: natToFormula_surj [propext, Classical.choice, Quot.sound].")
add('REFERENCE.md',
    "| `Enumeration.lean` | `natToFormula` y su sobreyectividad, **computables** | `net‑0` | 030 |",
    "| `Enumeration.lean` | `natToFormula` y su sobreyectividad (⚠️ `natToFormula_surj` lleva `Classical.choice` por `String.toList`; evitable, " + AUD + ") | ``propext, Classical.choice, Quot.sound`` | 030 |",
    "La tabla de footprints por módulo da `net‑0` a un módulo con 7 constantes con choice (decls.tsv).")
add('REFERENCE.md',
    "⛔ Aquí vive la no‑finitud del teorema (`if IsConsistent₀ …`, Π⁰₁).",
    "⚠️ Se decía que aquí vive la no‑finitud del teorema (`if IsConsistent₀ …`); FALSO en Lean: `henkin_completion₀` sale con `[propext, Quot.sound]` (" + AUD + ", medido).",
    "Localización refutada (Comb).")
add('REFERENCE.md',
    "⛔ Aquí vive la no‑finitud (Π⁰₁) |",
    "⚠️ la «no‑finitud» NO vive aquí: `henkin_completion₀` sale con `[propext, Quot.sound]` (" + AUD + ") |",
    "Localización refutada (Comb).")
add('REFERENCE.md',
    "triple en `EnumSym`—, porque no descompone ninguna cadena.",
    "triple en `EnumSym`—. ⚠️ Pero la diferencia es de RUTA, no del tipo (" + AUD + ", medido): la de "
    "`FreshSym String` sale de COMPARAR (`not_eq_of_beq_eq_false` con una `ReflBEq String` derivada de `String.instOrd`) "
    "y la de `EnumSym String` de `String.toList`/`ofList_toList`; con `instLawfulBEqString` y `String.exists_eq_ofList` "
    "las dos instancias de `String` miden `[propext, Quot.sound]`.",
    "exp-inv/Fresh.lean, exp-inv/Enum.lean, exp-string/E9.")
# ── 29-30 · AXIOMS.md ───────────────────────────────────────────────────────────
add('AXIOMS.md', lines('AXIOMS.md', 225, 225),
    "* ⚠️ **No cuenta `Classical.choice`**, que no es un `axiom` del proyecto: lo llevan 157 de las 2978\n"
    "  constantes de FOL y `TheoryFramework`, en 17 módulos (" + AUD + ", `collectAxioms` sobre el\n"
    "  entorno compilado). Según el grafo, 60 lo pierden con cambios locales de prueba medidos (`String`,\n"
    "  `open Classical`, `simp` aritmético, `bnd`) y 91 con todo lo medido evitable (más la inversa local\n"
    "  de `shift`, la etapa impredicativa de Lindenbaum, el cociente por listas y las pruebas alternativas\n"
    "  medidas de los corolarios que hoy pasan por la completitud o la solidez).\n"
    "  Lo irreducible (enunciados que implican ¬¬P → P, ¬P ∨ ¬¬P o AC, medido) es la semántica en `Prop`\n"
    "  (`derives0_soundness`, `lkc_sound`, `lk0_sound`), el lema de la verdad sobre un maximal arbitrario\n"
    "  (`max_cons_*`, `model_existence_lemma₀`) y las funciones de Skolem semánticas (`skF`).\n" + lines('AXIOMS.md', 225, 225),
    "El censo sólo cuenta axiom; decls.tsv + exp-juez/scen.py (S1: 157→97; S6: 157→66).")
add('AXIOMS.md', lines('AXIOMS.md', 159, 161),
    "y se midió antes de construir: el núcleo de Lean da `Char.ofNat_toNat` y `String.ofList_toList`,\n"
    "que es exactamente lo que hace falta. ⚠️ `String` ya **no** es `structure String where data : List Char`\n"
    "en v4.31 —es UTF‑8 opaco— así que `String.mk s.data = s` **no** vale por `rfl`; el lema sí. ⚠️ Pero el\n"
    "lema lleva `Classical.choice` (el decodificador UTF‑8 del núcleo): `String.exists_eq_ofList`\n"
    "(`[propext]`) hace el mismo trabajo sin él (" + AUD + ", medido).",
    "String.ofList_toList [propext, Classical.choice, Quot.sound] (exp-esencial/E4b, exp-string/E1).")
# ── 31-32 · TheoryFramework (falsedades no de constructividad, del inventario) ───
add('TheoryFramework/Logic.lean',
    "`LK₀`/`LKc` (`SequentSound0`) y `Prf₀`\n(`../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`). -/",
    "`LK₀`/`LKc` (`SequentSound0`) y `Prfᵢ`\n(`prfI_soundness`, `../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`). -/",
    "Nombre muerto: D6 renombró Prf₀ → Prfᵢ (inventario; RPP sondeos/AnclaSoundness.lean).")
add('TheoryFramework.lean', lines('TheoryFramework.lean', 15, 20),
    "-- `Instances/` no se importa aquí. Sólo queda `TheoryFramework/Instances/FOL.lean`, y SIN\n"
    "-- declaraciones (`folSystem` retirada el 2026-09-23): explica por qué no hay instancia.\n"
    "-- `PropLogic` y `FOLPure` se retiraron el 2026-09-12 (`cuarentena/librerias-retiradas/`).",
    "Cita instancias PropLogic/FOLPure que ya no existen (inventario).")

ok = True
for e in E:
    s = rd(e['fichero']); n = s.count(e['buscar'])
    if n != 1: ok = False
    print(n, e['fichero'], '|', e['buscar'][:80].replace('\n', '⏎'))
print('TODAS UNICAS' if ok else 'HAY NO-UNICAS', len(E))
by = {}
for e in E: by.setdefault(e['fichero'], []).append(e)
for f, es in by.items():
    s = rd(f)
    for e in es: s = s.replace(e['buscar'], e['reemplazar'], 1)
    out = D + 'check/' + f
    os.makedirs(os.path.dirname(out), exist_ok=True)
    io.open(out, 'w', encoding='utf-8', newline='\n').write(s)
json.dump(E, io.open(D + 'edits_juez.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
print('ficheros:', sorted(by))
