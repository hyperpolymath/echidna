# echidna - Rust Development Tasks
set shell := ["bash", "-uc"]
set dotenv-load := true

project := "echidna"

# Show all recipes
default:
    @just --list --unsorted

# Recipes live in just/*.just, one file per area, imported here in the
# order they used to appear in this file.
import "just/init.just"
import "just/build.just"
import "just/proofs.just"
import "just/dev.just"
import "just/corpus.just"
import "just/ui.just"
import "just/containers.just"
import "just/chapel.just"
import "just/spark.just"
import "just/creusot.just"
import "just/other.just"
import "just/onboarding.just"
import "just/corpus-design.just"
import "just/saturation.just"

# Contractile recipes list after the project recipes, as they did before
# the split.
import? "contractile.just"
