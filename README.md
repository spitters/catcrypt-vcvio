# CatCrypt VCVio

Interoperability between [CatCrypt Core](https://github.com/spitters/CatCrypt-core)
and [VCV-io](https://github.com/Verified-zkEVM/VCV-io) in Lean 4. The package relates
VCV-io's `ProbComp` / `OracleComp` computations and their measure semantics `𝒟[·]`
to CatCrypt's `SDistr` sub-distributions and `SPComp` stateful-probabilistic
programs, so that a probability bound proved in VCV-io becomes an `Advantage` bound
in CatCrypt.

**Documentation:** [API reference](https://spitters.github.io/catcrypt-vcvio/)

Module names live under the `CatCryptVCVio.*` root (single entry point:
`import CatCryptVCVio`). Declarations live in the namespace
`CatCrypt.Crypto.VCVioBridge`. Paths in the table below are relative to
`CatCryptVCVio/`.

## Contents

| Module | Main definitions | Main theorems |
|---|---|---|
| `Monad` | `sdistrMeasure` and the instance `EvalDistSemantics SDistr` (a sub-distribution as the sum of its point masses, so `𝒟[d]` is defined for every `SDistr`); `unifImpl : QueryImpl unifSpec SDistr`; `ProbComp.toSDistr := simulateQ unifImpl`; `probCompLift : ProbComp α → SPComp α` | the pure and bind laws of the instance (`LawfulEvalDistSemantics SDistr`); `evalDist_sdistr_singleton`: `𝒟[d] {x} = d (some x)`; `evalDist_sdistr_injective` (with measurable singletons, `d ↦ 𝒟[d]` is injective: the sub-distribution monad embeds in the Giry monad); `evalDist_toSDistr`: `𝒟[mx] = 𝒟[ProbComp.toSDistr mx]`; `probCompLift_pure`, `probCompLift_bind` (monad-morphism laws); `probCompLift_isPure` (the lift does not read or write the heap) |
| `State` | `HeapOp`, `heapStateSpec` (typed heap reads and writes as an oracle spec); `heapHandler`; `runState : OracleComp heapStateSpec α → SPComp α` | `runState_pure`, `runState_bind` |
| `Linking` | `PkgImpl I E` (a package with imports `I` and exports `E`, as `QueryImpl E (OracleComp I)`); `PkgImpl.id'`; `PkgImpl.link` (linking by `simulateQ`); `PkgImpl.toSPComp` | `link_id_left`, `link_id_right`, `simulateQ_simulateQ`, `link_assoc`; `toSPComp_link` (a definitional unfolding) |
| `Relational` | — | `probCompLift_apply`; `prTrue_probCompLift`: `prTrue (probCompLift mx) Heap.empty = 𝒟[mx] {true}`, and `prTrue_probCompLift_eq_prEvent` with the event `Pr{let b ← mx}[b = true]`; `advantage_probCompLift_le_of_probOutput_diff` (from bounds on `𝒟[mx₀] {true} - 𝒟[mx₁] {true}` in both directions); `advantage_probCompLift_eq_zero_of_evalDist_eq` (from `𝒟[mx₀] = 𝒟[mx₁]`) |
| `Examples/Coin` | `returnTrue` | `returnTrue_self_zero_advantage` |
| `Examples/OneTimePad` | — | `zero_advantage_of_evalDist_eq`, `zero_advantage_of_eq` (zero advantage from equal `evalDist`; the file contains no one-time pad) |
| `Examples/AdvantageTransfer` | — | one `example` applying `advantage_probCompLift_le_of_probOutput_diff` |
| `PolyFun/ExactWP` | `XCoreWP.ofMAlgOrdered`, `XCoreWP.ofOpSpec` (PolyFun's ordered monad algebras and per-operation specifications as XDijkstra observations) | `lawfulXCoreWP_ofExactWPMonad` (every exact `WPMonad` is a lawful XDijkstra observation); `lawfulXCoreWP_ofMAlgOrdered`, `ofMAlgOrdered_wp` (the weakest precondition is `μ (x >>= pure ∘ post)`), `ofMAlgOrdered_triple_iff`; `lawfulXCoreWP_ofOpSpec`, `ofOpSpec_wp` (the weakest precondition is `FreeM.wpFold`) |
| `PolyFun/Pullback` | — | `isMonadMorphism_monadHom` (a PolyFun monad homomorphism preserves `pure` and `bind`); `lawful_pullback_monadHom` (an XDijkstra observation pulled back along it is lawful); `lawful_pullback_freeM` (free-monad syntax observed through a handler is lawful); `freeM_lift_triple_iff` (a generator has the triples of its handler) |
| `PolyFun/Relational` | the instance `instMAlgRelOrderedExact : MAlgRelOrdered T T Prop` (exact couplings `RelQ0.liftR 0` as a relational monad algebra, defined as the grade-`0` part of `instMAlgRelGradedRelQ0`) | `triple_iff` (PolyFun's relational triple is `pre → RelQ0.liftR 0 post x y`) |
| `PolyFun/RelationalGraded` | `MAlgRelGraded G m₁ m₂ l` (a relational weakest precondition indexed by grades in an ordered additive monoid `G`: grade `0` on `pure` is the postcondition, the precondition is monotone in the grade, and grades add under `bind`); `GTriple`; `atZero`, `ofMAlgRelOrdered`; `RelQ0MonadCompat`; the instance `instMAlgRelGradedRelQ0 : MAlgRelGraded ℝ≥0∞ T T Prop` (approximate couplings `RelQ0.liftR ε`) | `gtriple_pure`, `gtriple_conseq`, `gtriple_mono_grade`, `gtriple_bind`, `gtriple_bind_le` (the graded triple rules); `atZero_ofMAlgRelOrdered`, `unitEquiv` (graded algebras over the trivial monoid `Unit` are PolyFun's `MAlgRelOrdered` algebras); `grwp_adequate` (the graded precondition at grade `ε` gives an `ε`-approximate sub-coupling of the denotations from every initial heap); `liftRApprox_pure_inv_of_lt_one`, `RelQ0.liftR_pure_inv_of_lt_one` (a coupling of two point masses at an error below `1` relates the points) |
| `PolyFun/StatefulFrame` | `runPT` (the XDijkstra observation of a free program run through a `Stateful` handler); `sepFst`, `sepSnd` | `runPT_localAlong_of_embed` (locality along a state embedding that commutes with the requests); `runPT_sum_inl_frame`, `runPT_sum_inr_frame`, `triple_sum_inl_frame`, `triple_sum_inr_frame` (the frame rule of `Stateful.sum`: a program on one summand preserves every predicate on the other summand's state) |

The `PolyFun/*` modules declare in the namespace
`CatCrypt.Crypto.VCVioBridge.XDijkstra` and use PolyFun at the revision VCV-io pins
(`ef4c157`).

The package declares no axioms and uses no `native_decide`.

## What is not included

- An equivalence between VCV-io's relational program logic and CatCrypt's
  `rHoare` (built on `CatCrypt.Prob.Coupling`).
  The transfer results here are quantitative.
- A theorem relating `PkgImpl.link` to CatCrypt-core's deep-embedding linking
  `CatCrypt.Deep.DeepPackage.link`.
- Transfer of universal-composability statements, and re-exports of VCV-io's
  forking lemma. CatCrypt-core carries its own forking lemmas.
- Security reductions for concrete schemes. The examples apply the transfer
  lemmas to generic games.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [CatCrypt Core](https://github.com/spitters/CatCrypt-core) at branch `main`
- [VCV-io](https://github.com/Verified-zkEVM/VCV-io) at commit `88efe971` (tag `v4.35.0`)
- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.35.0`

Toolchain: `leanprover/lean4:v4.35.0` (see `lean-toolchain`).

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
