# Third-party notices

This package is released under the MIT license (see `LICENSE`). It requires the
projects below as Lake dependencies, which are fetched from their own repositories at
build time and remain under their own licenses; the two Apache-2.0 files listed after
the table are the only source code in this package from another project or staged for one.

| Project | License | Repository | Use |
|---|---|---|---|
| VCV-io | Apache-2.0 | <https://github.com/Verified-zkEVM/VCV-io> | `ProbComp`, `OracleComp`, `SPMF`, `simulateQ` and the probability notation that the bridge relates to CatCrypt |
| Mathlib | Apache-2.0 | <https://github.com/leanprover-community/mathlib4> | mathematical library (`PMF`, `ℝ≥0∞`) |
| CatCrypt Core | MIT | <https://github.com/spitters/CatCrypt-core> | `SDistr`, `SPComp`, `Advantage` |

Two files are under Apache-2.0 and carry their license headers:
`CatCryptVCVio/OracleComp/MapLens.lean` is staged for contribution to VCV-io, and
`CatCryptVCVio/Rust/OracleComp.lean` is a copy of VCV-io's `Interop/Rust/Common.lean` and
`Interop/Rust/Run.lean` (Copyright 2026 Quang Dao), in its own namespace.

The transitive dependencies of these projects are listed in `lake-manifest.json`;
each carries the license stated in its repository.
