/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Relational

/-!
# Bridge Example — Constant game

The `ProbComp Bool` game `returnTrue := pure true`, lifted by `probCompLift` to
`SPComp`. The one theorem, `returnTrue_self_zero_advantage`, states that the
lifted game has zero `Advantage` against itself; it is an instance of
`advantage_probCompLift_eq_zero_of_evalDist_eq` with `rfl` as the `evalDist`
equality. No probability of the game is computed.
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- The `ProbComp Bool` computation that returns `true`. -/
def returnTrue : ProbComp Bool := pure true

/-- The lift of `returnTrue` has zero `Advantage` against itself. -/
theorem returnTrue_self_zero_advantage :
    Advantage (probCompLift returnTrue) (probCompLift returnTrue) = 0 :=
  advantage_probCompLift_eq_zero_of_evalDist_eq _ _ rfl

end CatCrypt.Crypto.VCVioBridge.Examples
