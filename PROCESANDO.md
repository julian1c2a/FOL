# Procesando: Teorema de Completitud y Modelo Cociente

1. **Relación de equivalencia sintáctica:** Definida como `termEqv S t1 t2 := S (.eq t1 t2)`.
2. **Demostración de que es relación de equivalencia:** Hemos añadido `substTerm_liftTerm`, `derive_eq_symm` y `derive_eq_trans` en un nuevo fichero `Theorems/Eq.lean`, y utilizado estos teoremas para demostrar `termEqv_refl`, `termEqv_symm`, y `termEqv_trans` en `Completeness.lean`. Además, se ha instanciado `termSetoid`.

Siguientes pasos:
3. **(Hecho)** Definir el nuevo dominio (el cociente del setoide).
4. Hacer el lift hacia el conjunto cociente de las funciones y predicados.
5. Redefinir el modelo canónico y refactorizar.
