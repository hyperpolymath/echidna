# Melange Route

This shows how to use Melange (AffineScript → OCaml → JS or native).

## Setup

```bash
# Install opam (OCaml package manager)
opam init
opam switch create . 5.1.0

# Install Melange
opam install melange dune

# Build
dune build
```

## Key Difference from AffineScript

- **AffineScript**: npm-based, JS output only
- **Melange**: opam-based, can also compile to native

## Native Binary Option

Change dune file to use `(executable ...)` instead of `(melange.emit ...)`
to get a standalone binary that generates HTML without any runtime.
