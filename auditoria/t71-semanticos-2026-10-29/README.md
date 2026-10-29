# T71, la mitad semántica — el registro de la exploración (2026‑10‑29)

**Last updated:** 2026-10-29 — creado con T71 (ADR‑221 de RPP).

**Sobre:** FOL `fa0b1f1` (el de antes de `FOL/EsencialidadSem0.lean`) · Lean v4.35.0 ·
**Autor:** Julián Calderón Almendros, con un flujo de siete agentes (tres implementadores, dos exploradores y dos
escépticos) ·
**Decisión:** ADR‑221 de `../../../ROBINSON_PlusPlus/DECISIONS.md` ·
**Clasificación vigente:** `../../AXIOMS.md` §4.3 · **La medida, en el build:** `../../FOL/EsencialidadSem0.lean`

## Qué es esta carpeta

T71 (la auditoría de RPP) preguntaba si el `Classical.choice` de los cinco teoremas semánticos de
`FOL/Compacity0.lean` es ESENCIAL: si su ENUNCIADO, tomado como hipótesis, implica sin choice un principio que la
lógica constructiva no demuestra. Lo medido entró en el build (`FOL.EsencialidadSem0`, E8–E10):

| enunciado | implica, sin ningún axioma | en `FOL.EsencialidadSem0` |
|---|---|---|
| `compactness` (basta la vuelta) | WLEM, `¬P ∨ ¬¬P` | E8 |
| `loewenheim_skolem_down`, `countable_infinite_of_infinite` | KSst (el esquema de Kripke para las proposiciones ¬¬‑estables) y, de él, WKS | E9 |
| `infinite_model_of_large`, `infinite_model_of_large_fresh` | WLPO para sucesiones decidibles y WKS; juntos, WLEM | E10 |

Aquí queda lo demás: qué MÁS podrían implicar esos enunciados, con lo que se compiló fuera del build y lo que sólo
está argumentado. Nada de esta carpeta lo importa nadie, y no la compila el build.

## Los ficheros

Cada uno se compila suelto, desde la raíz de RPP y con FOL construido: `lake env lean <fichero>`.
`medidas-2026-10-29.txt` guarda la salida literal de cada uno, re‑ejecutados el 2026‑10‑29 contra FOL `fa0b1f1`.
Los teoremas, como mucho `[propext, Quot.sound]`; los controles (que aplican los teoremas reales), con
`Classical.choice`, como se espera.

| fichero | autor | qué mide |
|---|---|---|
| `b1-Colapso.lean` | el explorador b1, ampliado por el escéptico s1 | Lo único que un modelo dice de una teoría es NEGATIVO («info_negativa»). Con el artilugio disyuntivo `T c d := {Q ∨ R} ∪ {¬Q | c} ∪ {¬R | d}`, la compacidad da EXACTAMENTE De Morgan, `¬(c ∧ d) → ¬c ∨ ¬d`, que equivale a WLEM («sat_T_iff», «finSat_T_iff», «deMorgan_of_compactness_mpr»). El testigo de Kreisel–Markov `SM α` tiene un modelo numerable e infinito para TODO `α` y sin hipótesis («colapso_MP»: el dominio es el cociente de `Option ℕ` que identifica el testigo con el menor índice verdadero), así que la compacidad, LS↓ y §3 no dan nada sobre él; nombrar el testigo ES Markov («nombrado_iff», «testigo_nombrado»). La teoría pensada para LPO da sólo WLPO («sat_SL_iff_wlpo») |
| `b1-Sandwich.lean` | b1 y s1 | El «emparedado» Σ⁰₁ desde §3 con la frescura («sandwich_of_large_fresh») y desde WLEM («sandwich_of_wlem»); con WLPOp da WLEM («wlem_of_sandw_wlpop») |
| `b2-Reticulo.lean` | el explorador b2 | Dónde caen los principios, en lógica pura: WLEM ⟹ KSneg ⟹ WKS, KS ⟹ KSneg, KSneg ⟺ KSst, WKS es KS salvo doble negación («wks_iff_nn»). Bajo WKS colapsan WLEM, LLPOp y WLPOp («wks_llpop_implies_wlem», «wks_collapse»). BKS⁻ + Markov ⟹ DNE (Moschovakis 1980, en forma p) y KS + LPOp ⟹ EM. Las formas p implican las de `Bool` |
| `a2-LSWKS.lean` | el implementador a2, ampliado por s2 | La primera derivación de LS↓ ⟹ WKS; la forma «KSdn», equivalente a KSst, y la UNIFORME «KSdnSeq» (una sola sucesión para toda una familia `P : Nat → Prop`); de ella, KS para `∃k P k` con cada `P k` ¬¬‑estable («ksdnSeq_ksSigma», `[propext]`) |
| `s2-Trampas.lean` | el escéptico s2 | Trampas de footprint, medidas: un `match` con patrones SOLAPADOS mete `propext` en la definición; `List.length_replicate` y `Nat.mod_eq_of_lt` llevan `propext`; `List.Nodup.length_le_of_subset` lleva `Classical.choice` |
| `s1-MutTypeOf.lean` | el escéptico s1 | ⚠️ DEBE FALLAR, con tres errores: los mutantes de la comprobación «la hipótesis ES el enunciado» (`→` en lugar de `Iff`; §3 sin `InfiniteDom`; §3 sin la frescura). El enunciado correcto pasa. Prueba que la comprobación de `EsencialidadSem0` discrimina |

## Lo ARGUMENTADO, sin compilar

Son argumentos de modelos, revisados por los escépticos. El hueco común: se supone, sin comprobarlo, que Lean sin
`Classical.choice` (`Prop` impredicativa, `propext`, cocientes, universos) es correcto en los modelos de prehaces y
de haces usados. Es estándar, pero no está formalizado aquí.

* **Que los principios medidos no se demuestren sin choice.** En el modelo de Kripke sobre el poset
  `V = {0<1, 0<2}`, WLEM falla en la raíz con `P = {1}`. En todo modelo de Kripke, una sucesión que se fuerza
  decidible es constante en cada cono, y por eso WKS ⟺ WLEM allí: WKS falla también, y con él KSst. Lo mismo sale
  del topos efectivo, porque un realizador de `∀ P` es uniforme en `P`. Es la evidencia de E7: el mismo contramodelo.
  ✅ Confirmado por s2, que comprobó además que LS↓ falla directamente en `V`.
* **Ninguno de los cinco implica EM.** En el modelo de Kripke sobre `{0<1}` valen los cinco (el nodo 1 es clásico:
  la compacidad clásica y LS↓ dan allí un modelo numerable `N`, y el prehaz constante `N` fuerza la teoría en 0) y
  falla EM; valen WLEM, MP y LPO. 🟡 Revisado por s1 sin encontrarle fallo.
* **LS↓ y `countable_infinite_of_infinite` no implican KS, BKS⁻, EM ni DNE** (el topos de Sierpinski: valen los dos
  enunciados, con un prehaz constante tomado de una subestructura elemental numerable del mundo clásico, y fallan KS
  con `P = {1}` y EM). ✅ Confirmado por s2 como argumento.
* **LS↓ y `countable_infinite_of_infinite` no implican WLEM, WLPO, LLPO ni MP** (haces sobre el espacio de Cantor:
  LS↓ por Löwenheim–Skolem en `L_{ω₁,ω}` sobre las secciones; los contraejemplos, con los clopens «el primer 1 está en
  la posición n» y el punto `0^ω`). 🟡 Plausible: el paso central no está verificado.
* **La compacidad y §3 no implican MP, LPO ni KS** (haces sobre `βℕ`, extremadamente disconexo, donde vale WLEM y
  falla MP con la indicadora de `{n}`). 🟡 Plausible, revisado por s1.

## Lo que queda abierto

* DNS (`∀n ¬¬P n → ¬¬∀n P n`) y ¬¬EM: ninguno de los modelos usados los separa de los cinco enunciados.
* Si la compacidad implica Markov para las ecuaciones diofánticas, como la completitud (`../../FOL/Markov0.lean`).
* Si KSst es estrictamente más fuerte que WKS sin Markov (con Markov coinciden: «wks_mpp_implies_ksdn»).
* La cota por arriba: según un esbozo de s1, no compilado, WLEM + ¬¬EM bastarían para los cinco enunciados.
