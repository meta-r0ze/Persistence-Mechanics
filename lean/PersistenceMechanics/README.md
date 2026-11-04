# PersistenceMechanics — PM framework

Lean 4 proofs for the survival/hazard, Gibbs and selection framework used by
Papers I–VI.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — module map and results.
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) — inputs and open items.

Build: Lean 4.34.1 with Mathlib pinned in `lake-manifest.json`.

```sh
lake exe cache get
./check.sh
```
