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
equality. `prTrue_returnTrue` computes the probability that the lifted game
returns `true` from the empty heap through `prTrue_probCompLift`.
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

/-- The lift of `returnTrue` returns `true` from the empty heap with probability `1`. -/
theorem prTrue_returnTrue :
    prTrue (probCompLift returnTrue) CatCrypt.Core.Heap.empty = 1 := by
  rw [prTrue_probCompLift, returnTrue, evalDist_pure,
    MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton true)]

end CatCrypt.Crypto.VCVioBridge.Examples
