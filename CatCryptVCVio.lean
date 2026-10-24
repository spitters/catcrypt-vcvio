/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Monad
public import CatCryptVCVio.State
public import CatCryptVCVio.Linking
public import CatCryptVCVio.Relational
public import CatCryptVCVio.Examples.Coin
public import CatCryptVCVio.Examples.OneTimePad
public import CatCryptVCVio.Examples.AdvantageTransfer

/-!
# VCVio Bridge

Umbrella module of the VCVio–CatCrypt interoperability bridge. It imports every
module of the package; the declarations live in the namespace
`CatCrypt.Crypto.VCVioBridge`.

## Modules

* `Monad` — the measure semantics `EvalDistSemantics SDistr` (the embedding of the
  sub-PMF monad into the Giry monad), the interpretation `ProbComp.toSDistr` with
  `𝒟[mx] = 𝒟[ProbComp.toSDistr mx]`, and the `probCompLift : ProbComp → SPComp`
  monad morphism
* `State` — the typed heap as an oracle spec, and the `runState` morphism
  `OracleComp heapStateSpec → SPComp`
* `Linking` — packages as VCVio query implementations, linking by `simulateQ`,
  and its unit and associativity laws
* `Relational` — `prTrue (probCompLift mx) Heap.empty = 𝒟[mx] {true}` and the
  transfer of probability bounds to `Advantage` bounds
* `Examples/*` — applications of the transfer lemmas (`Coin`, `OneTimePad`,
  `AdvantageTransfer`)
-/

@[expose] public section
