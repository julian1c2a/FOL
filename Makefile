# Makefile for Lean 4 projects
# Usage: make <target>
# Requires: bash, lake, git

.PHONY: build build-all clean rebuild sorry axioms status lock unlock list init new help

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

## Create a new module: make new NAME=Algebra/Ring
new:
	@[ -n "$(NAME)" ] || (echo "Usage: make new NAME=ModuleName" && exit 1)
	@bash new-module.bash $(NAME)

## ⛔ PROHIBIDO (2026-09-12, A-7): sobrescribe el barrel, borra el aviso de cuarentena
## y mete tres modulos huerfanos con declaraciones DUPLICADAS. Ver gen-root.bash.
root:
	@echo "⛔ 'make root' esta PROHIBIDO en este repo — ver la cabecera de gen-root.bash (A-7)."
	@exit 2

## Update Lean toolchain: make update-toolchain VERSION=v4.29.0
update-toolchain:
	@[ -n "$(VERSION)" ] || (echo "Usage: make update-toolchain VERSION=v4.29.0" && exit 1)
	@bash update-toolchain.bash $(VERSION)

## Show this help
help:
	@echo "Available targets:"
	@grep -E '^## ' Makefile | sed 's/^## /  /'
