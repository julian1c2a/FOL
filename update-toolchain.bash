#!/bin/bash
# update-toolchain.bash — ⛔ RETIRADO aquí el 2026‑10‑20 (T42, ADR‑176 de RPP).
#
# Compilaba FOL desde ESTE directorio (`lake build`, que usa el toolchain de FOL: lo prohíbe M‑3) y, si compilaba,
# COMMITEABA él solo el `lean-toolchain`. El par (RPP, FOL) se prueba junto, con la misma versión, desde la raíz de
# ROBINSON_PlusPlus y en árboles aparte, sin commit:
#
#     cd ../ROBINSON_PlusPlus && bash update-toolchain.bash [vX.Y.Z]
#
# El bump, si se decide, lo hace un ADR, a mano, en los dos repos (M‑12: FOL primero).
export PATH="/usr/bin:$PATH"
echo "⛔ update-toolchain.bash está retirado en FOL (T42, ADR-176 de RPP)." >&2
echo "   El par se prueba desde ROBINSON_PlusPlus: cd ../ROBINSON_PlusPlus && bash update-toolchain.bash ${1:-}" >&2
exit 2
