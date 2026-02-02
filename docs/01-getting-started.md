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

## Adding a New Module

Each layer has a facade file that re-exports its submodules. For example, `Gibbs/Hamiltonian.lean` imports all files under `Gibbs/Hamiltonian/`. When adding a new file, import it from the appropriate facade.

New files should follow these conventions:

1. Start with a prose problem statement after imports explaining what the file proves, what makes it hard, and the solution structure.
2. Use `/-! ## Section Name -/` headers to break the file into logical groups.
3. No code block may exceed 30 lines. Extract helper lemmas when proofs grow.
4. Every theorem gets a docstring. Complex proofs get a strategy comment.
5. Files must stay under 500 lines. Split into submodules when larger.

Use type abbreviations for readability. The project uses `Config n` for `EuclideanSpace ℝ (Fin n)` and `PhasePoint n` for the position-momentum pair.

## Common Proof Tactics

| Tactic | Typical Use |
|--------|-------------|
| `rfl` | Definitional equality, operator exactness |
| `simp` | Unfolding definitions, arithmetic simplification |
| `linarith` / `nlinarith` | Linear and nonlinear arithmetic inequalities |
| `positivity` | Nonnegativity of energy, norms, exponentials |
| `ring` / `field_simp` | Algebraic identities, normalization |
| `omega` | Natural number arithmetic |
| `ext` | Function extensionality |

These tactics appear throughout the codebase. Convexity arguments typically use `nlinarith` after unfolding definitions. Energy nonnegativity proofs use `positivity`. Algebraic cancellations in thermodynamic identities use `ring`.
