# YatimaStdLib.lean

An auxiliary Std lib for Lean 4 that aims to support the development of other packages for Yatima Inc.

## Nix

Nix is a declarative and deterministic package manager and build tool which ensures reproducibility.

### Developing

Enable auto loading dependencies into the shell with `direnv allow` or manually with `nix develop`.

### Building

Build with `nix build .`

### Tests

Run tests with `nix run .#test`
