#!/bin/bash
# guarda-toolchain.bash — FOL y RPP, en el MISMO toolchain (M-1 de DECISIONS.md; la M-3 de RPP, reescrita en su
# ADR-205, T16). La llaman las entradas que ejecutan `lake` desde FOL (`Makefile`, `check-axioms.bash`).
#
# Con RPP al lado (`../ROBINSON_PlusPlus`, o `RPP_DIR`) y otro `lean-toolchain`, se NIEGA (código 1): construir FOL
# desde aquí con otro toolchain escribiría `.olean` incompatibles en el `.lake` que RPP usa. Con el mismo, da igual
# construir desde aquí o desde la raíz de RPP (MEDIDO en un par clonado: doc/registro/2026-10-28-t16/ de RPP).
# Sin RPP al lado, lo DICE y deja seguir: un control tiene tres resultados, y el tercero se anuncia.
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

RPP="${RPP_DIR:-../ROBINSON_PlusPlus}"
if [ ! -f lean-toolchain ]; then
  echo "⛔ guarda-toolchain: no hay lean-toolchain en FOL" >&2
  exit 1
fi
if [ ! -f "$RPP/lean-toolchain" ]; then
  echo "⚠️  guarda-toolchain: sin $RPP/lean-toolchain no comparo el toolchain (alcance REDUCIDO)" >&2
  exit 0
fi
A=$(tr -d '\r' < lean-toolchain)
B=$(tr -d '\r' < "$RPP/lean-toolchain")
if [ "$A" != "$B" ]; then
  echo "⛔ guarda-toolchain: FOL en $A y RPP en $B. Con toolchains distintos, construir FOL desde aquí mezcla el .lake que usa RPP (M-1): un bump mueve el par a la vez (desde RPP: bash update-toolchain.bash)." >&2
  exit 1
fi
echo "✓ guarda-toolchain: FOL y RPP en $A"
