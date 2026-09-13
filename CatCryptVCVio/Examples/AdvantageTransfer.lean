/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Relational

/-!
# Bridge Example — Advantage transfer

An application of `advantage_probCompLift_le_of_probOutput_diff`: bounds on
`Pr[= true | game₀] - Pr[= true | game₁]` in both directions give an `Advantage`
bound on the lifted `SPComp` games. A computational reduction proved over
`ProbComp` in VCVio is transferred to CatCrypt in the same way.
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- Two games whose output probabilities differ by at most `1 / 2` at every
    `b : Bool`, in both directions, have `Advantage` at most `1 / 2` between
    their lifts. -/
example (game₀ game₁ : ProbComp Bool)
    (hbound : ∀ b : Bool,
      (Pr[= b | game₀]) - (Pr[= b | game₁]) ≤ (1 / 2 : ℝ≥0∞) ∧
      (Pr[= b | game₁]) - (Pr[= b | game₀]) ≤ (1 / 2 : ℝ≥0∞)) :
    Advantage (probCompLift game₀) (probCompLift game₁) ≤ (1 / 2 : ℝ≥0∞) :=
  advantage_probCompLift_le_of_probOutput_diff game₀ game₁ (hbound true).1 (hbound true).2

end CatCrypt.Crypto.VCVioBridge.Examples
