# CatCrypt VCVio

Interoperability between [CatCrypt Core](https://github.com/spitters/CatCrypt-core)
and [VCV-io](https://github.com/Verified-zkEVM/VCV-io) in Lean 4. The package relates
VCV-io's `ProbComp` / `OracleComp` computations and `SPMF` distributions to
CatCrypt's `SDistr` sub-distributions and `SPComp` stateful-probabilistic programs,
so that a probability bound proved in VCV-io becomes an `Advantage` bound in
CatCrypt.

**Documentation:** [API reference](https://spitters.github.io/catcrypt-vcvio/)

Module names live under the `CatCryptVCVio.*` root (single entry point:
`import CatCryptVCVio`). Declarations live in the namespace
`CatCrypt.Crypto.VCVioBridge`. Paths in the table below are relative to
`CatCryptVCVio/`.

## Contents

| Module | Main definitions | Main theorems |
|---|---|---|
| `Monad` | `toSDistr`, `fromSDistr` (VCV-io's `SPMF α` and CatCrypt's `SDistr α` are both `PMF (Option α)`); `ProbComp.toSDistr` (through `evalSPMF`); `probCompLift : ProbComp α → SPComp α` | `toSDistr_fromSDistr`, `fromSDistr_toSDistr`; `probCompLift_pure`, `probCompLift_bind` (monad-morphism laws); `probCompLift_isPure` (the lift does not read or write the heap) |
| `State` | `HeapOp`, `heapStateSpec` (typed heap reads and writes as an oracle spec); `heapHandler`; `runState : OracleComp heapStateSpec α → SPComp α` | `runState_pure`, `runState_bind` |
| `Linking` | `PkgImpl I E` (a package with imports `I` and exports `E`, as `QueryImpl E (OracleComp I)`); `PkgImpl.id'`; `PkgImpl.link` (linking by `simulateQ`); `PkgImpl.toSPComp` | `link_id_left`, `link_id_right`, `simulateQ_simulateQ`, `link_assoc`; `toSPComp_link` (a definitional unfolding) |
| `Relational` | — | `probCompLift_apply`; `prTrue_probCompLift`: `prTrue (probCompLift mx) Heap.empty = Pr[= true \| mx]`; `advantage_probCompLift_le_of_probOutput_diff`; `advantage_probCompLift_eq_zero_of_evalDist_eq` |
| `Examples/Coin` | `returnTrue` | `returnTrue_self_zero_advantage` |
| `Examples/OneTimePad` | — | `zero_advantage_of_evalDist_eq`, `zero_advantage_of_eq` (zero advantage from equal `evalDist`; the file contains no one-time pad) |
| `Examples/AdvantageTransfer` | — | one `example` applying `advantage_probCompLift_le_of_probOutput_diff` |

The package declares no axioms and uses no `native_decide`.

## What is not included

- An equivalence between VCV-io's relational program logic (built on
  `SPMF.Coupling`) and CatCrypt's `rHoare` (built on `CatCrypt.Prob.Coupling`).
  The transfer results here are quantitative.
- A theorem relating `PkgImpl.link` to CatCrypt-core's deep-embedding linking
  `CatCrypt.Deep.DeepPackage.link`.
- Transfer of universal-composability statements, and re-exports of VCV-io's
  forking lemma. CatCrypt-core carries its own forking lemmas.
- Security reductions for concrete schemes. The examples apply the transfer
  lemmas to generic games.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [CatCrypt Core](https://github.com/spitters/CatCrypt-core) at commit `2adfac7`
- [VCV-io](https://github.com/Verified-zkEVM/VCV-io) at commit `f9dc47d9da`
- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.33.1`

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).

## Build

`lake build` builds the default target, the `CatCryptVCVio` library. See
[BUILDING.md](BUILDING.md).

## Documentation

- **API reference:** [doc-gen4](https://spitters.github.io/catcrypt-vcvio/)
- **Changelog:** [CHANGELOG.md](CHANGELOG.md) ·
  **Contributing:** [CONTRIBUTING.md](CONTRIBUTING.md) ·
  **Third-party notices:** [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)

## Related projects

- [CatCrypt Core](https://github.com/spitters/CatCrypt-core) — the game-based
  proof framework this package connects to.
- [VCV-io](https://github.com/Verified-zkEVM/VCV-io) — a Lean 4 framework for
  oracle computations and their probabilistic semantics.

## Citing

See `CITATION.cff`. The accompanying paper:

> B. Spitters. *CatCrypt: From Rust to Cryptographic Security in Lean.*
> Cryptology ePrint Archive, Paper 2026/604.
> <https://eprint.iacr.org/2026/604.pdf>

## License

MIT. See `LICENSE`. Dependencies carry their own licenses; see
`THIRD_PARTY_NOTICES.md`.
