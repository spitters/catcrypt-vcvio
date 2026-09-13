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

* `Monad` — the definitional identification of VCVio's `SPMF` with CatCrypt's
  `SDistr`, and the `probCompLift : ProbComp → SPComp` monad morphism
* `State` — the typed heap as an oracle spec, and the `runState` morphism
  `OracleComp heapStateSpec → SPComp`
* `Linking` — packages as VCVio query implementations, linking by `simulateQ`,
  and its unit and associativity laws
* `Relational` — `prTrue (probCompLift mx) Heap.empty = Pr[= true | mx]` and the
  transfer of probability bounds to `Advantage` bounds
* `Examples/*` — applications of the transfer lemmas (`Coin`, `OneTimePad`,
  `AdvantageTransfer`)
-/

@[expose] public section
