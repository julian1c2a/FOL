# `cuarentena/` — ⛔ **tres módulos apartados el 2026‑09‑11**

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros

> ## `soundness : Γ ⊢ f → Γ ⊨ f` es **FALSO**, y junto con `raa` demostraba **`False` sin hipótesis**
>
> No es un fallo en la prueba. El **enunciado** no es demostrable, porque no es verdad.
> Evidencia compilada: **`cuarentena/Inconsistencia.lean`**.

---

## 1 · Qué se apartó, y por qué

| módulo | venía de | por qué |
|---|---|---|
| `Soundness.lean` | `FOL/Soundness.lean` | contiene el teorema falso |
| `Compacity.lean` | `FOL/Compacity.lean` | `compactness_theorem` se apoya en él |
| `Theorems_Soundness.lean` | `FOL/Theorems/Soundness.lean` | reexportaba `soundness` |

Y `FOL.lean` —el barrel raíz— importaba `FOL.MetaRules` **y** `FOL.Soundness` a la vez:
⇒ **`import FOL` era un módulo inconsistente.** Ya no los importa.

## 2 · La causa, exacta

`Derives` (`FOL/FOL.lean:165`) es un `inductive` de **18 constructores**, todos semánticamente
válidos — es deducción natural intuicionista. La solidez para ellos es cierta y su prueba era
correcta caso por caso.

⚠️ **CENSO CORREGIDO el 2026‑09‑12**: esta página decía «cinco» y son **OCHO en la librería FOL**
(**doce** contando el lado de ROBINSON_PlusPlus). Los que faltaban estaban **fuera** de
`MetaRules.lean`, que es justo donde nadie miró:

| dónde | cuáles | n |
|---|---|---|
| `FOL/MetaRules.lean` | `imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim` | 6 |
| `FOL/Theorems/Neg.lean:57` | **un SEGUNDO `dne`**, en forma de esquema (`Γ ⊢ (¬¬A ⇒ A)`), distinto del de `MetaRules` (que es regla). Lo consume `Completeness.lean:680` | 1 |
| `FOL/Theorems/Quantifiers.lean:115` | `forall_not_impl_exists_not` | 1 |
| *(RPP)* | `ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`, `ax_p_tfa` | +4 |

Los seis de `MetaRules.lean` son:

    axiom imp_intro (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)
    axiom gen       (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) : Γ ⊢ ∀A
    axiom raa       (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A
    axiom or_elim   …
    axiom ex_elim   …

⚠️ **Y tienen que ser axiomas**: sus premisas son **funciones de Lean**, o sea ocurrencias negativas
de `Derives` en su propio constructor. Lean rechaza ese `inductive`. No es un descuido: no hay
alternativa dentro del tipo.

⇒ `Derives` tiene habitantes que **no son aplicaciones de constructor**, y entonces:

> ⛔ **Ningún teorema sobre `Derives` puede demostrarse por `induction`.** La inducción cubre los
> 18 constructores; el enunciado cuantifica sobre **todos** los habitantes.

Es el fallo clásico de `axiom foo : UnInductivo`: rompe la garantía de «no hay basura» del tipo.

**Medido**: `soundness` era **el único** teorema de todo `FOL/` probado por inducción sobre
`Derives` (`grep -rn "induction h with" FOL/` → una sola línea). El radio del daño es ése.

## 3 · El detonador, en tres pasos

Con contexto **vacío** y dos modelos triviales sobre `Unit`:

1. `P` no es derivable de `[]` — lo refuta el modelo con todas las relaciones **falsas**, vía la
   propia solidez.
2. Luego `raa`, cuya premisa `[] ⊢ P → [] ⊢ ⊥` existe **vacuamente**, da `[] ⊢ ¬P`.
3. Pero `P` es verdadera en el modelo con todas las relaciones **verdaderas**. Solidez ⇒ `[] ⊨ ¬P`
   ⇒ contradicción.

Footprint medido: **`[propext, FOL.MetaRules.raa]`**. Ni `Classical.choice` hace falta.

## 4 · Qué NO significa

* ⚠️ **`ROBINSON_PlusPlus` NO está afectado.** Medido: no importa `FOL.Soundness` ni el barrel raíz
  `FOL` — sólo `FOL.FOL`, `FOL.MetaRules`, `FOL.Tactics`, `FOL.Deduction` y `FOL.Theorems.*`.
  Sus 131 módulos y la cadena de Gödel no están en contexto inconsistente.
* ⚠️ **`FOL/Semantics.lean` está BIEN** y se queda en la librería. Es sólido y es útil: es
  exactamente lo que permitió demostrar `prf0_soundness` (§6).
* ⚠️ **Las meta‑reglas no están «mal»**. Dicen lo que dicen: `⊢` es una noción metateórica de
  verdad, no una relación de derivabilidad. La otra cara está medida en
  `ROBINSON_PlusPlus/Meta/OmegaStrength.lean`: con `raa`, `⊢` **decide toda sentencia** (lo que no
  prueba, lo refuta) ⇒ **no es r.e.** Eso ya era sabido; lo nuevo es que **también impide la
  solidez**, y las dos cosas son la misma: un cálculo completo y sólido sobre una teoría con
  modelos no elementalmente equivalentes no existe.

## 5 · Lo que se perdió, y lo que no

`compactness_theorem` (`Compacity.lean`) era **vacuo**: su prueba pasaba por `soundness`.
`Completeness.lean` **no** está afectado —no importa ni `Soundness` ni `MetaRules`— y se queda.

## 6 · La salida buena, y ya está hecha

Enunciar la solidez sobre un cálculo **sin axiomas habitándolo**. `ROBINSON_PlusPlus` tiene uno:

    Prf₀ — 17 constructores, CERO axiomas habitándolo (medido)

`prf0_soundness : Prf₀ φ → satisfies axioms φ` está **demostrado**, por inducción sobre los 17
constructores, con footprint **`[propext, Classical.choice, Quot.sound]`** — net‑0 puro.
Está en `ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.

## 6bis · ⛔ **ESTA CUARENTENA NO FUE EFECTIVA EL PRIMER DÍA** (2026‑09‑12)

Se movió el fuente, se quitó del barrel, se reconstruyó el árbol y dio **verde**. Pero `lake` **no
recoge la basura**: `.lake/build/lib/lean/FOL/Soundness.olean` se quedó, `import FOL.Soundness`
**seguía resolviendo desde él**, y `False` se demostraba al día siguiente exactamente igual —
verificado compilando, footprint `[propext, Classical.choice, Quot.sound, FOL.MetaRules.raa]`.

🔑 **Retirar el FUENTE no retira el MÓDULO.** Un `.olean` sin `.lean` es un **módulo fantasma**:
importable, invisible al build, y sin fuente que auditar.

**Arreglado**: borrados `Soundness.olean`/`Compacity.olean` y sus artefactos hermanos, y verificado
que el import **falla** («object file … does not exist»).

**Control**: bloque **`[F]` de `ROBINSON_PlusPlus/check-doc-sync.bash`** — ROMPE si hay algún
`.olean` sin fuente, aquí o en `../FOL`. Probado en los dos sentidos. ⭐ Al estrenarlo aparecieron
**cuatro fantasmas más en RPP**, uno de ellos `Meta/Incompleteness` —la capa Gödel LEGACY retirada—
que reexponía **`axiom D2` y `axiom D3`**, las dos condiciones que el proyecto **demostró** después.

⚠️ Y ojo al reverso: `FOLPure`, `PropLogic` y `FOL_poli` tienen sus **propios** `Soundness.lean`
**vivos** con el mismo defecto estructural. No son fantasmas —tienen fuente— pero **no están en
cuarentena**. Ver §7.

## 7 · ⬜ Lo que esta cuarentena NO cubre

Auditoría del 2026‑09‑11/12, medido y **reproducido compilando** por dos agentes independientes:

* ⛔⛔ **`FOLPure` y `FOL_poli` son INCONSISTENTES** por una causa **distinta** a ésta: declaran como
  `axiom` la ecuación `substFormula v t (liftFormula (v+1) f) = f`, que **el propio `FOL` documenta
  como FALSA desde 2026‑06‑23 con contraejemplo** y corrigió… sólo en `FOL/`. Se compiló `False` en
  las dos, footprint `[subst_lift_cancel_formula]`.
  🔶 **Contenido por desuso**: ninguna tiene consumidores ni artefactos, y RPP no las toca.
* `FOLPure`, `PropLogic` y `FOL_poli` tienen además su propio `soundness` por inducción sobre su
  propio `Derives`, con el mismo hueco. Sin cuarentena.
* `FOL_poli/FOL.lean` es **byte‑idéntico** a `FOL/FOL.lean`: un clon muerto.
* De las cinco `lean_lib`, **sólo `FOL` está viva** (único `@[default_target]`, único con `.olean`,
  única que consume RPP).

⇒ **Decisión pendiente del propietario**: retirar las tres librerías muertas, o ponerlas en
cuarentena también.

## 8 · La reparación de fondo, que NO se ha hecho

Lo de arriba **contiene**, no repara. La reparación real es que las meta‑reglas **no habiten
`Derives`**: declararlas sobre una relación aparte `DerivesW` con `Derives Γ f → DerivesW Γ f`, y
dejar `Derives` limpio para que su solidez sea un teorema de verdad.

⛔⛔ **Y con el censo corregido, esa reparación NO BASTARÍA** (2026‑09‑12): mover sólo `MetaRules`
dejaría **seis** habitantes — los dos de `FOL/Theorems/` y los cuatro de RPP.

⚠️ Y uno de ellos lo **fabrica RPP** con la forma mala: `ax_list_induction`
(`../ROBINSON_PlusPlus/ROBINSON_PlusPlus/Full/Lists.lean:55`) tiene una **premisa‑FUNCIÓN**
`Γ ⊢ φ t → Γ ⊢ φ (cons h t)`. ⇒ el problema no es de quién es el fichero, es de la **FORMA de la
premisa**. Una reparación que deja habitantes **no repara nada**.

⚠️ **Coste medido**: `ROBINSON_PlusPlus` usa constructores `Derives.*` **164 veces**
(`Derives.subst` 58, `Derives.refl` 40, `Derives.hyp` 18, `Derives.weakening` 13,
`Derives.intro_impl` 13, …), más toda la notación `⊢`. No es una tarde. **Queda como decisión del
propietario.**

---

**Véase también:** `cuarentena/Inconsistencia.lean` (la evidencia, compilable),
`FOL/MetaRules.lean` (el aviso en cabecera),
`ROBINSON_PlusPlus/Meta/OmegaStrength.lean` y `ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`.
