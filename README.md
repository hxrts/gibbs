# Gibbs

Structure defines a *set of possible executions*, causality selects a *member* of that set.

* MPST projection preserves intensional structure while erasing extensional detail.
* Mean-field abstraction preserves macroscopic intensional structure while erasing extensional individuality and history.

Both frameworks perform erasure at the extensional level:

* Projection forgets *how* an executed protocol is interleaved or scheduled, keeping only what each role must do.
* Mean-field abstraction forgets *which* agent did what, when, keeping only how many agents are in each intensional state.

## Setup

```bash
direnv allow   # loads nix environment
just build     # builds lean library
```
