#!/bin/bash

# Vérifie si le programme dpll existe
if [ ! -f ./dpll ]; then
  echo "Le programme ./dpll n'existe pas. Veuillez le compiler d'abord."
  exit 1
fi

# Vérifie si le répertoire SAT existe
if [ ! -d ./SAT ]; then
  echo "Le répertoire ./SAT n'existe pas."
  exit 1
fi

# Boucle sur tous les fichiers dans le répertoire SAT
for file in ./SAT/*; do
  if [ -f "$file" ]; then
   # Exclure le fichier ii8a2.cnf
    if [ "$(basename "$file")" = "ii8a2.cnf" ]; then
      echo "Skipping file: $file"
      continue
    fi
    
    echo "Traitement du fichier: $file"
    ./dpll "$file"
  fi
done