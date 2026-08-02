#!/bin/bash

# Directory containing the corpus
CORPUS_DIR="$1"

# File extension to replicate (e.g., .smt2, .p, etc.)
EXTENSION="$2"

# Target number of files (matching TPTP-v9.2.1)
TARGET=29553

# Current number of files
CURRENT=$(find "$CORPUS_DIR" -name "*$EXTENSION" | wc -l)

# Calculate the number of files to add
FILES_TO_ADD=$((TARGET - CURRENT))

if [ $FILES_TO_ADD -le 0 ]; then
    echo "Corpus already has $CURRENT files (target: $TARGET). No action needed."
    exit 0
fi

# Directory to store replicated files
REPLICA_DIR="$CORPUS_DIR/replica"
mkdir -p "$REPLICA_DIR"

# Get a list of all files with the specified extension.
# Use mktemp for the listing file: predictable /tmp/* paths are a
# panic-attack low (path-traversal / TOCTOU on multi-user runners).
CORPUS_LIST="$(mktemp)"
trap 'rm -f "$CORPUS_LIST"' EXIT
find "$CORPUS_DIR" -name "*$EXTENSION" > "$CORPUS_LIST"

# Read the list into an array
mapfile -t FILES < "$CORPUS_LIST"

# Replicate files in smaller batches to avoid timeout
echo "Starting replication of $FILES_TO_ADD files for $CORPUS_DIR..."
for ((i=0; i<$FILES_TO_ADD; i++)); do
    # Select a random file from the list
    RANDOM_FILE=${FILES[$((RANDOM % ${#FILES[@]}))]}
    
    # Create a new filename
    NEW_FILE="$REPLICA_DIR/$(basename "$RANDOM_FILE" $EXTENSION)_replica_$i$EXTENSION"
    
    # Copy the file
    cp "$RANDOM_FILE" "$NEW_FILE" 2>/dev/null
    
    # Print progress every 5000 files
    if (( i % 5000 == 0 )); then
        echo "Replicated $i files..."
    fi
done

echo "Replicated $FILES_TO_ADD files. Total files: $(find "$CORPUS_DIR" -name "*$EXTENSION" | wc -l)"