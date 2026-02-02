# Getting Started

This document covers how to set up, build, and extend the Gibbs project. For an overview of the project structure, see [Gibbs Overview](00-overview.md).

## Prerequisites

Gibbs requires Lean 4 (v4.26.0), managed through elan. The project uses nix and direnv for environment setup, and just as a task runner. Install elan from the Lean 4 documentation if you do not already have it.

## Building

Run the following commands to initialize and build:

```bash
direnv allow
just build
```

The first command loads the nix environment, which provides elan, just, and other tools. The second runs `lake build` with `LEAN_NUM_THREADS=3`. There is no separate test suite. The build itself is the verification. If `lake build` succeeds, all proofs are valid.

To type-check a single file during development:

```bash
lake env lean Gibbs/Path/To/File.lean
```

This is faster than a full build when iterating on one module. Use `just clean` to remove `.lake` build artifacts and `just update` to refresh Lake dependencies.

## Dependencies

Gibbs depends on two local path dependencies:

- Mathlib from `../lean_common/mathlib4` (shared installation with pre-built artifacts)
- Telltale from `../telltale/lean` (effects and session-type spatial system)

Both must be checked out at the expected relative paths before building. The `lakefile.lean` declares them as `require mathlib` and `require telltale`.

## Using Gibbs as a Dependency

To use Gibbs in your own Lean project, add it as a dependency in your `lakefile.lean`:

```lean
require gibbs from .."../gibbs"
```

Then import the modules you need:

```lean
import Gibbs.Hamiltonian
import Gibbs.MeanField
import Gibbs.ContinuumField
import Gibbs.Consensus
```

Each of these is a facade file that re-exports all submodules within that directory. You can also import individual files for finer-grained control, for example `import Gibbs.Hamiltonian.Stability`.
