#!/usr/bin/env bash
# cierre-imports.bash — el CIERRE de imports de las raíces del build: el universo de los módulos (T15 y ADR‑163 de RPP).
#
# Uso:  bash cierre-imports.bash              las rutas del cierre, una por línea, ordenadas (LC_ALL=C)
#       bash cierre-imports.bash --autotest   compila un árbol de prueba y comprueba el cierre; sale con 0 si cuadra
#
# Desde las RAÍCES (abajo), sigue los `import` de la CABECERA de cada fichero —leída sin comentarios, con
# `strip-lean.awk`: un `import` dentro de un comentario no cuenta, ni uno después de la primera orden— y sólo los
# módulos de los PREFIJOS (los de este repo). Sale con 2 si uno de esos `import` nombra un fichero que no existe.
#
# 🔑 Es el universo de los controles: `[L]` de `check-doc-sync.bash` lo compara con `git ls-files` y con el disco (lo
# que compilan los `globs` del lakefile), y `[A]` y `[C]` cuentan y recorren sobre él. Antes cada control tenía su
# lista de `ls` (`TheoryFramework/**/*.lean` sin `globstar` es un nivel, y un subdirectorio nuevo no lo veía nadie).
#
# ⛔ Una definición delicada vive en UN sitio: las raíces de FOL están AQUÍ y en ningún otro fichero. El código es
# el mismo que el de `../ROBINSON_PlusPlus/cierre-imports.bash`, salvo `RAICES` y `PREFIJOS` (RPP lo comprueba). La
# tercera raíz, `TheoryFramework.Instances.FOL`, la compila el `globs` y el barril `TheoryFramework.lean` NO la importa
# a propósito (arrastraría toda la capa clásica de FOL; ver su comentario).

export PATH="/usr/bin:$PATH"
RAICES="FOL TheoryFramework TheoryFramework.Instances.FOL"
PREFIJOS="FOL TheoryFramework"

cd "$(dirname "$0")" || exit 2
STRIP="$PWD/strip-lean.awk"

# Los módulos que importa la cabecera del fichero $1, uno por línea. La cabecera acaba en la primera línea (sin
# comentarios) que no empieza por una de sus palabras: `prelude`, `module`, `public`, `meta`, `import`.
importa() {
  LC_ALL=C awk -f "$STRIP" "$1" | LC_ALL=C awk '
    { n = split($0, t, /[ \t]+/); k = 1
      while (k <= n && t[k] == "") k++
      if (k > n) next
      if (t[k] != "import" && t[k] != "prelude" && t[k] != "module" && t[k] != "public" && t[k] != "meta") exit
      for (; k <= n; k++)
        if (t[k] == "import") {
          k++
          while (k <= n && t[k] == "all") k++
          if (k <= n) print t[k]
        }
    }'
}

# cierre DIR "RAICES" "PREFIJOS": las rutas (relativas a DIR) del cierre, ordenadas; devuelve 2 si falta un fichero.
cierre() {
  local dir=$1 raices=$2 prefijos=$3 m f i p falta=0
  local -A visto=()
  local -a cola salida=()
  read -r -a cola <<< "$raices"
  while [ ${#cola[@]} -gt 0 ]; do
    m=${cola[0]}; cola=("${cola[@]:1}")
    [ -n "${visto[$m]+x}" ] && continue
    visto[$m]=1
    f="${m//.//}.lean"
    if [ ! -f "$dir/$f" ]; then
      echo "  ✗ el cierre importa $m, y $f NO existe" >&2
      falta=2
      continue
    fi
    salida+=("$f")
    while IFS= read -r i; do
      for p in $prefijos; do
        case "$i" in "$p"|"$p".*) cola+=("$i"); break ;; esac
      done
    done < <(importa "$dir/$f")
  done
  [ ${#salida[@]} -gt 0 ] && printf '%s\n' "${salida[@]}" | LC_ALL=C sort
  return $falta
}

# El árbol de prueba: dos ficheros alcanzables, cinco que no lo son por razones distintas (un `import` en un
# comentario de bloque, otro en uno de línea, otro tras la primera orden, uno suelto que importa a otro, y un nombre
# que sólo COMIENZA por el prefijo), y una segunda raíz con un `import` a un fichero que no existe.
autotest() {
  local d got rc
  d=$(mktemp -d) || return 2
  mkdir -p "$d/Lib/Sub"
  printf '%s\n' '/- import Lib.Fantasma -/' 'import Lib.A  -- import Lib.Otro' '/- abre' 'import Lib.Fantasma -/' \
    'import Lean' 'import Library.X' '' '/-! doc del módulo -/' 'def x := 1' 'import Lib.Tarde' > "$d/Lib.lean"
  printf '%s\n' 'prelude' 'import Lib.Sub.B' 'namespace Lib' 'end Lib' > "$d/Lib/A.lean"
  printf '%s\n' '-- hoja' 'def y := 2' > "$d/Lib/Sub/B.lean"
  printf '%s\n' 'import Lib.A' > "$d/Lib/Suelto.lean"
  for m in Fantasma Otro Tarde; do printf 'def z := 0\n' > "$d/Lib/$m.lean"; done
  printf '%s\n' 'import Lib.NoExiste' > "$d/Mal.lean"
  got=$(cierre "$d" "Lib" "Lib" 2>/dev/null); rc=$?
  got=$(printf '%s' "$got" | tr '\n' ' ')
  [ $rc -eq 0 ] || { echo "  autotest: el cierre de Lib devuelve $rc (¿sigue a Library.X?)" >&2; rc=1; }
  [ "$got" = "Lib.lean Lib/A.lean Lib/Sub/B.lean" ] || { echo "  autotest: el cierre de Lib es «$got»" >&2; rc=1; }
  cierre "$d" "Lib Mal" "Lib" > /dev/null 2>&1
  [ $? -eq 2 ] || { echo "  autotest: un import a un fichero que no existe NO devuelve 2" >&2; rc=1; }
  rm -rf "$d"
  return $rc
}

case "${1:-}" in
  --autotest) autotest ;;
  "") cierre . "$RAICES" "$PREFIJOS" ;;
  *) echo "uso: bash cierre-imports.bash [--autotest]" >&2; exit 2 ;;
esac
