# YatimaStdLib.lean

An auxiliary Std lib for Lean 4 that aims to support the development of other packages for Yatima Inc.

## Develop

1. Install `elan`. It will then automatically ensure that the correct version of `lean` is enabled.
2. Install a reasonably modern `cargo` (but apparently not too modern, we're working on clarifying the supported versions of `cargo`/`rustc`).
3. Run `lake build` to build everything, then run `lake exe lspec` to run tests. If you're lucky, you'll see something [like this](https://github.com/yatima-inc/YatimaStdLib.lean/actions/runs/3941938405/jobs/6744983278) in your terminal.

## Nix support

Since the project has external dependencies aside from `lean`, we ship a complementary nix flake.
Currently the versions it installs are wrong, but we're working hard on making all the external dependencies reproducibly work to ensure smooth building and usage of the project.
