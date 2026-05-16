#!/bin/bash
# guarda_y_bloquea.bash
# Secuencia para guardar y bloquear un archivo .lean

if [ -z "$1" ]; then
    echo "Uso: bash guarda_y_bloquea.bash <archivo.lean> [mensaje de commit]"
    exit 1
fi

FILE="$1"
MSG="${2:-"Actualización de $FILE"}"

echo "Desbloqueando la lista..."
bash git-lock.bash unlock

echo "Desbloqueando $FILE..."
bash git-lock.bash unlock "$FILE"

echo "Añadiendo a git..."
git add .

echo "Haciendo commit..."
git commit -m "$MSG"

echo "Haciendo push..."
git push

echo "Bloqueando $FILE..."
bash git-lock.bash lock "$FILE"

echo "Bloqueando la lista..."
bash git-lock.bash lock

echo "Completado."
