# Third-party notices

This package is released under the MIT license (see `LICENSE`). It contains no
source code copied from the projects below; it requires them as Lake dependencies,
which are fetched from their own repositories at build time and remain under
their own licenses.

| Project | License | Repository | Use |
|---|---|---|---|
| VCV-io | Apache-2.0 | <https://github.com/Verified-zkEVM/VCV-io> | `ProbComp`, `OracleComp`, `SPMF`, `simulateQ` and the probability notation that the bridge relates to CatCrypt |
| Mathlib | Apache-2.0 | <https://github.com/leanprover-community/mathlib4> | mathematical library (`PMF`, `ℝ≥0∞`) |
| CatCrypt Core | MIT | <https://github.com/spitters/CatCrypt-core> | `SDistr`, `SPComp`, `Advantage` |

The transitive dependencies of these projects are listed in `lake-manifest.json`;
each carries the license stated in its repository.
