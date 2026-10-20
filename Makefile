# Makefile for Lean 4 projects
# Usage: make <target>
# Requires: bash, lake, git

.PHONY: build build-all clean rebuild sorry axioms status lock unlock list init help

## Build the project (los DOS `@[default_target]`: FOL y TheoryFramework)
build:
	lake build

## Build TODAS las librerías del lakefile, explícitamente.
## ⚠️ 2026-09-12 (A-2): antes sólo `FOL` era `@[default_target]`, así que CUATRO de las
## cinco librerías NO SE COMPILABAN NUNCA — y ahí sobrevivió 80 días un `axiom` que el
## propio proyecto había declarado FALSO. Tres de ellas se retiraron (D-1); la cuarta,
## `TheoryFramework`, entró al build y su `Instances/FOL.lean` resultó estar roto.
## ⇒ Si se añade una `lean_lib`, AÑADIRLA AQUÍ.
build-all:
	lake build FOL TheoryFramework

## Censo de `axiom` de Lean (A-1)
axioms:
	@bash check-axioms.bash

## Clean build artifacts
clean:
	lake clean

## Clean and rebuild
rebuild: clean build

## Check for sorry statements
sorry:
	@bash check-sorry.bash

## Show project status: locked files + sorry count
status:
	@echo "=== Lock Status ==="
	@bash git-lock.bash list
	@echo ""
	@echo "=== Sorry Status ==="
	@bash check-sorry.bash || true
	@echo ""
	@echo "=== Axiom Status ==="
	@bash check-axioms.bash || true

## Lock a file: make lock FILE=ProjectName/Module.lean
lock:
	@[ -n "$(FILE)" ] || (echo "Usage: make lock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash lock $(FILE)

## Unlock a file: make unlock FILE=ProjectName/Module.lean
unlock:
	@[ -n "$(FILE)" ] || (echo "Usage: make unlock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash unlock $(FILE)

## List all locked files
list:
	@bash git-lock.bash list

## Initialize lock system (install git hook)
init:
	@bash git-lock.bash init

# (2026-10-18, T15 y ADR-163 de RPP: `make new` y `make root` se retiraron con new-module.bash y gen-root.bash, que
#  estaba PROHIBIDO desde A-7. Un modulo nuevo se crea a mano y se importa desde su barril; [L] de
#  check-doc-sync.bash dice si un fichero no esta en el cierre de imports.)

## Toolchain: ⛔ retirado aquí (T42, ADR-176 de RPP); el par se prueba desde ROBINSON_PlusPlus
update-toolchain:
	@bash update-toolchain.bash $(VERSION)

## Show this help
help:
	@echo "Available targets:"
	@grep -E '^## ' Makefile | sed 's/^## /  /'
