/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Monad
public import CatCryptCore.Crypto.Advantage

/-!
# VCVio Bridge — Relational / Advantage transfer

Bridges VCVio's measure semantics (`𝒟[mx]`, events `Pr{…}[…]`) to CatCrypt's
relational and advantage-level reasoning (`Advantage`, `prTrue`) via `probCompLift`.

The main content is the **probability-preservation lemma**: the probability that
`probCompLift mx` returns `true` from the empty heap is the mass `𝒟[mx] {true}`.
This is what makes VCVio's quantitative reductions transfer into CatCrypt
`Advantage` bounds.

## Main results

* `probCompLift_apply` — pointwise evaluation of `probCompLift mx h`
* `prTrue_probCompLift` — `prTrue (probCompLift mx) CatCrypt.Core.Heap.empty = 𝒟[mx] {true}`,
  and `prTrue_probCompLift_eq_prEvent` in the event form `Pr{let b ← mx}[b = true]`
* `advantage_probCompLift_le_of_probOutput_diff` — VCVio probability bounds
  transfer to CatCrypt advantage bounds
* `advantage_probCompLift_eq_zero_of_evalDist_eq` — equal measures give zero advantage

## Relation between the relational program logics

VCVio's relational program logic (`VCVio.ProgramLogic.Relational`) is built on
couplings of its measure semantics; CatCrypt's `rHoare`
(`CatCryptCore/Relational/Judgment.lean`) is built on `CatCrypt.Prob.Coupling`.
No equivalence between VCVio's relational triples and `rHoare` is proved here; the
results of this file are quantitative, and transfer probability bounds to
`Advantage` bounds.
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SDistrLift
open MeasureTheory
open scoped ENNReal

/-! ## Pointwise evaluation of `probCompLift` -/

/-- Evaluating `probCompLift mx` at an output `(a, h')` starting from heap `h`:
    the heap must be unchanged (`h = h'`) and the probability is that of
    `ProbComp.toSDistr mx` returning `a`. For any other final heap, the probability is `0`. -/
theorem probCompLift_apply_toSDistr {α : Type} (mx : ProbComp α) (h h' : CatCrypt.Core.Heap)
    (a : α) :
    (probCompLift mx h) (some (a, h')) =
      if h = h' then ProbComp.toSDistr mx (some a) else 0 := by
  unfold probCompLift sdistrToSPComp
  show (SDistr.bind (ProbComp.toSDistr mx) (fun a' => SDistr.pure (a', h))) _ = _
  unfold SDistr.bind SDistr.pure SDistr.fail
  rw [PMF.bind_apply]
  rw [tsum_option_split]
  simp only [PMF.pure_apply, reduceCtorEq, ite_false, mul_zero, zero_add]
  by_cases hh : h = h'
  · subst hh
    simp only [ite_true]
    rw [tsum_eq_single a]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  · simp only [hh, ite_false]
    apply ENNReal.tsum_eq_zero.mpr
    intro a'
    rcases eq_or_ne a' a with rfl | hne_a
    · simp [Ne.symm hh]
    · simp [Ne.symm hne_a]

/-- Evaluating `probCompLift mx` at an output `(a, h')` starting from heap `h`:
    the heap must be unchanged (`h = h'`) and the probability is the mass `𝒟[mx] {a}`
    of VCVio's measure semantics. For any other final heap, the probability is `0`. -/
theorem probCompLift_apply {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : ProbComp α) (h h' : CatCrypt.Core.Heap) (a : α) :
    (probCompLift mx h) (some (a, h')) = if h = h' then 𝒟[mx] {a} else 0 := by
  rw [probCompLift_apply_toSDistr, evalDist_toSDistr, evalDist_sdistr_singleton]

/-! ## Probability preservation -/

/-- The key compatibility lemma: the probability that `probCompLift mx` returns
    `true` (starting from the empty heap) is the mass `𝒟[mx] {true}` of VCVio's
    measure semantics.

    This is the identity that lets VCVio's probability bounds transfer to
    CatCrypt's `Advantage` statements. -/
theorem prTrue_probCompLift (mx : ProbComp Bool) :
    prTrue (probCompLift mx) CatCrypt.Core.Heap.empty = 𝒟[mx] {true} := by
  unfold prTrue
  rw [tsum_congr fun h => probCompLift_apply mx CatCrypt.Core.Heap.empty h true]
  rw [tsum_eq_single CatCrypt.Core.Heap.empty]
  · simp
  · intro h hne
    simp [Ne.symm hne]

/-- `prTrue_probCompLift` in VCVio's event notation. -/
theorem prTrue_probCompLift_eq_prEvent (mx : ProbComp Bool) :
    prTrue (probCompLift mx) CatCrypt.Core.Heap.empty = Pr{let b ← mx}[b = true] := by
  rw [prTrue_probCompLift, prEvent_eq_evalDist_singleton]

/-! ## Advantage transfer -/

/-- VCVio probability bounds transfer to CatCrypt advantage bounds. If two
    `ProbComp Bool` games have masses `𝒟[·] {true}` differing by at most `ε`, then
    their `probCompLift`s have `Advantage` at most `ε`. -/
theorem advantage_probCompLift_le_of_probOutput_diff
    (mx₀ mx₁ : ProbComp Bool) {ε : ℝ≥0∞}
    (h₀ : 𝒟[mx₀] {true} - 𝒟[mx₁] {true} ≤ ε)
    (h₁ : 𝒟[mx₁] {true} - 𝒟[mx₀] {true} ≤ ε) :
    Advantage (probCompLift mx₀) (probCompLift mx₁) ≤ ε := by
  unfold Advantage
  simp only [prTrue_probCompLift]
  exact max_le h₀ h₁

/-- Perfect-indistinguishability transfer: equal measure semantics `𝒟[·]` implies zero
    `Advantage` on the lifts. -/
theorem advantage_probCompLift_eq_zero_of_evalDist_eq
    (mx₀ mx₁ : ProbComp Bool) (h : 𝒟[mx₀] = 𝒟[mx₁]) :
    Advantage (probCompLift mx₀) (probCompLift mx₁) = 0 := by
  unfold Advantage
  rw [prTrue_probCompLift, prTrue_probCompLift, h]; simp

end CatCrypt.Crypto.VCVioBridge
