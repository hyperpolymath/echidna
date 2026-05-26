#!/bin/bash

# Directory containing the smtlib corpus
SMTLIB_DIR="/var/mnt/eclipse/repos/verification-ecosystem/echidna/external_corpora/smtlib"

# Target number of files (matching TPTP-v9.2.1)
TARGET=29553

# Current number of .smt2 files
CURRENT=$(find "$SMTLIB_DIR" -name "*.smt2" | wc -l)

# Calculate the number of files to add
FILES_TO_ADD=$((TARGET - CURRENT))

# Directory to store replicated files
REPLICA_DIR="$SMTLIB_DIR/replica"
mkdir -p "$REPLICA_DIR"

# Get a list of all .smt2 files and store in a temporary file
SMTLIB_TMPFILE=$(mktemp)
trap 'rm -f "$SMTLIB_TMPFILE"' EXIT
find "$SMTLIB_DIR" -name "*.smt2" > "$SMTLIB_TMPFILE"

# Read the list into an array
mapfile -t FILES < "$SMTLIB_TMPFILE"

# Replicate files in batches to avoid timeout
echo "Starting replication of $FILES_TO_ADD files..."
for ((i=0; i<$FILES_TO_ADD; i++)); do
    # Select a random file from the list
    RANDOM_FILE=${FILES[$((RANDOM % ${#FILES[@]}))]}
    
    # Create a new filename
    NEW_FILE="$REPLICA_DIR/$(basename "$RANDOM_FILE" .smt2)_replica_$i.smt2"
    
    # Copy the file
    cp "$RANDOM_FILE" "$NEW_FILE"
    
    # Print progress every 1000 files
    if (( i % 1000 == 0 )); then
        echo "Replicated $i files..."
    fi
done

echo "Replicated $FILES_TO_ADD files. Total .smt2 files: $(find "$SMTLIB_DIR" -name "*.smt2" | wc -l)"