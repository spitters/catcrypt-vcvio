/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Relational

/-!
# Bridge Example — Zero advantage from `evalDist` equality

Two `ProbComp Bool` games with equal `evalDist` have zero `Advantage` between
their `probCompLift`s (`zero_advantage_of_evalDist_eq`), and a game has zero
`Advantage` against itself (`zero_advantage_of_eq`). The file contains no
one-time pad. VCVio's own one-time-pad example (`oneTimePad.cipherGivenMsg_equiv`
in VCVio's `Examples/OneTimePad/Basic.lean`, outside VCVio's main library) proves
that the ciphertext distributions for two messages are equal; mapping both
games through the same Boolean distinguisher gives an `evalDist` equality of the
form this file consumes.
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- An `evalDist` equality between two `ProbComp Bool` games gives zero
    `Advantage` between their lifts. This restates
    `advantage_probCompLift_eq_zero_of_evalDist_eq`. -/
theorem zero_advantage_of_evalDist_eq
    (game₀ game₁ : ProbComp Bool) (h : evalDist game₀ = evalDist game₁) :
    Advantage (probCompLift game₀) (probCompLift game₁) = 0 :=
  advantage_probCompLift_eq_zero_of_evalDist_eq game₀ game₁ h

/-- The lift of a `ProbComp Bool` game has zero `Advantage` against itself. -/
theorem zero_advantage_of_eq (game : ProbComp Bool) :
    Advantage (probCompLift game) (probCompLift game) = 0 :=
  zero_advantage_of_evalDist_eq game game rfl

end CatCrypt.Crypto.VCVioBridge.Examples
