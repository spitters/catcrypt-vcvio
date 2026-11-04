# Changelog

## Unreleased

- `OracleComp/MapLens`: oracle computations along lenses of oracle specs, and the transport of
  `IsQueryBound`, `IsTotalQueryBound`, `IsQueryBoundP`, `AllQueriesSatisfy` and
  `IsPerIndexQueryBound` along lenses.
- `ResponderSys`: VCV-io's stateful responders as CatCrypt reactive systems, with runs, views
  and advantages.
- `OracleAdvOracleComp`: bridges of `IsPerIndexQueryBound` and `AllQueriesSatisfy` to
  CatCrypt's per-oracle charges and call restriction.
- `Monad`: `toSDistr_map`, `probCompLift_map`, `map_probCompLift`.
- Lean v4.35.0; VCV-io `6214f907`, PolyFun `4181c822`.

Initial release of the VCV-io interoperability package for CatCrypt Core
(Lean 4.33.1, Mathlib `v4.33.1`, VCV-io `f9dc47d9da`).

- `Monad`: `toSDistr` / `fromSDistr` between VCV-io's `SPMF` and CatCrypt's
  `SDistr`; `ProbComp.toSDistr`; the monad morphism `probCompLift : ProbComp → SPComp`
  with `probCompLift_pure`, `probCompLift_bind` and `probCompLift_isPure`.
- `State`: the typed heap as the oracle spec `heapStateSpec`, the handler
  `heapHandler`, and the morphism `runState : OracleComp heapStateSpec → SPComp`
  with `runState_pure` and `runState_bind`.
- `Linking`: packages as `PkgImpl I E := QueryImpl E (OracleComp I)`, linking by
  `simulateQ`, the unit laws `link_id_left` / `link_id_right`, associativity
  `link_assoc`, and the lowering `PkgImpl.toSPComp`.
- `Relational`: `prTrue_probCompLift` (`prTrue (probCompLift mx) Heap.empty =
  Pr[= true | mx]`), `advantage_probCompLift_le_of_probOutput_diff` and
  `advantage_probCompLift_eq_zero_of_evalDist_eq`.
- `Examples/{Coin, OneTimePad, AdvantageTransfer}`: applications of the transfer
  lemmas to generic games.
- Documents: README, BUILDING, CONTRIBUTING, CITATION.cff, LICENSE (MIT),
  THIRD_PARTY_NOTICES; CI build with sorry and `native_decide` guards; doc-gen4
  workflow publishing to GitHub Pages.
