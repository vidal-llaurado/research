# Lean proofs

| Paper | Formalized components |
| --- | --- |
| I1 | Reconstruction, identification algebra and inverse bounds under explicit analytic assumptions. |
| I2 | Two-asset projection and finite date-budget optimization. |
| I3 | Global protection, capital foundations, conditional symmetry reduction and the exact reduced optimization. |

The 199 statements check parts of the proofs; the main theorems are not fully formalized.
Assumptions are explicit in each statement. Lean and mathlib versions are pinned.

With Lean installed, run from the repository root:

```sh
cd lean
lake build
lake env lean Audit.lean
```

`lake build` checks the proofs; the last command lists their axiom dependencies.
