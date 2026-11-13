/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.OracleAdvOracleComp
public import CatCryptCore.Complexity.TimeBoundCharge

/-!
# Time certificates of oracle adversaries as query bounds of VCVio computations

A time certificate of a reduction whose output is an oracle adversary is a costed adversary
`A : OracleAdv.Timed D R α` (or a step-prefixed one `x : ℕ × OracleAdv.Timed D R α`) with a
time bound `A.TimeBound n`; by `OracleAdv.Timed.timeBound_iff_isChargeBound` this is the charge
bound `n` of its tick tree `toFreeMT A` under the charge `tickCost`. Every `rand` and `query` node
costs one unit, and step costs are nonnegative, so the number of nodes on every path of the
erased adversary `A.erase` is at most `n`. For a VCVio computation
`oc : OracleComp (advSpec D R) α` whose tree `ofOracleComp oc` is the erased adversary, this is
VCVio's total query bound `oc.IsTotalQueryBound n`, which counts the uniform queries `inl m`
(the sampling nodes) and the oracle queries `inr d`; restricted to the oracle queries it is the
bound `oc.IsQueryBoundP (fun t => t.isRight = true) n`.

## Main results

* `OracleAdv.Timed.isRollBound_toFreeM_erase_of_timeBound` — a time bound `n` bounds the nodes
  of the erased tree by `n`
* `isTotalQueryBound_of_timeBound`, `isTotalQueryBound_of_isChargeBound` — the time bound, or
  the charge bound of the tick tree, is a total query bound of the VCVio computation
* `isTotalQueryBound_of_stepTimeBound`, `isTotalQueryBound_of_isChargeBound_stepToFreeMT` — the
  step-prefixed forms, with budget `n - x.1`
* `isQueryBoundP_of_timeBound` — the bound `n` on the oracle queries `inr d`
* `isTotalQueryBound_toOracleComp_of_timeBound`,
  `isTotalQueryBound_toOracleComp_of_stepTimeBound` — the forms for an erased adversary of the
  uniform fragment and its computation `toOracleComp`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

open PFunctor

variable {D R α : Type}

/-- A time bound `n` of a costed adversary bounds the number of `rand` and `query` nodes on every
path of its erasure by every `m ≥ n`. -/
theorem isRollBound_toFreeM_erase_of_timeBound {A : Timed D R α} {n : ℕ} (h : A.TimeBound n)
    (m : ℕ) (hm : n ≤ m) :
    (OracleAdv.toFreeM A.erase).IsRollBound m (fun _ b => 0 < b) (fun _ b => b - 1) := by
  induction A generalizing n m with
  | ret a => trivial
  | rand p c k ih =>
    simp only [erase, OracleAdv.toFreeM, FreeM.isRollBound_liftBind_iff]
    exact ⟨by have := h.1; omega, fun b => ih b (h.2 b).2 (m - 1) (by omega)⟩
  | query d c k ih =>
    simp only [erase, OracleAdv.toFreeM, FreeM.isRollBound_liftBind_iff]
    exact ⟨by have := h.1; omega, fun r => ih r (h.2 r).2 (m - 1) (by omega)⟩

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Crypto.VCVioBridge

open PFunctor OracleSpec OracleComp

variable {D R α : Type}

/-- A time bound `n` of a costed adversary is the total query bound `n` of a VCVio computation
whose tree is its erasure. -/
theorem isTotalQueryBound_of_timeBound {A : OracleAdv.Timed D R α}
    {oc : OracleComp (advSpec D R) α} (hoc : ofOracleComp oc = OracleAdv.toFreeM A.erase)
    {n : ℕ} (h : A.TimeBound n) : oc.IsTotalQueryBound n := by
  have hb := OracleAdv.Timed.isRollBound_toFreeM_erase_of_timeBound h n le_rfl
  rw [← hoc, isRollBound_ofOracleComp] at hb
  exact hb

/-- The charge bound `n` of the tick tree of a costed adversary is the total query bound `n` of a
VCVio computation whose tree is its erasure. -/
theorem isTotalQueryBound_of_isChargeBound {A : OracleAdv.Timed D R α}
    {oc : OracleComp (advSpec D R) α} (hoc : ofOracleComp oc = OracleAdv.toFreeM A.erase)
    {n : ℕ} (h : (OracleAdv.Timed.toFreeMT A).IsChargeBound OracleAdv.Timed.tickCost n) :
    oc.IsTotalQueryBound n :=
  isTotalQueryBound_of_timeBound hoc ((OracleAdv.Timed.timeBound_iff_isChargeBound A n).2 h)

/-- A step time bound `n` of a step-prefixed costed adversary `x` is the total query bound
`n - x.1` of a VCVio computation whose tree is the erasure of `x.2`. -/
theorem isTotalQueryBound_of_stepTimeBound {x : ℕ × OracleAdv.Timed D R α}
    {oc : OracleComp (advSpec D R) α} (hoc : ofOracleComp oc = OracleAdv.toFreeM x.2.erase)
    {n : ℕ} (h : OracleAdv.Timed.StepTimeBound x n) : oc.IsTotalQueryBound (n - x.1) :=
  isTotalQueryBound_of_timeBound hoc h.2

/-- The charge bound `n` of the step-prefixed tick tree of `x` is the total query bound `n - x.1`
of a VCVio computation whose tree is the erasure of `x.2`. -/
theorem isTotalQueryBound_of_isChargeBound_stepToFreeMT {x : ℕ × OracleAdv.Timed D R α}
    {oc : OracleComp (advSpec D R) α} (hoc : ofOracleComp oc = OracleAdv.toFreeM x.2.erase)
    {n : ℕ}
    (h : (OracleAdv.Timed.stepToFreeMT x).IsChargeBound OracleAdv.Timed.tickCost n) :
    oc.IsTotalQueryBound (n - x.1) :=
  isTotalQueryBound_of_stepTimeBound hoc
    ((OracleAdv.Timed.stepTimeBound_iff_isChargeBound x n).2 h)

/-- A time bound `n` of a costed adversary bounds the oracle queries `inr d` of a VCVio
computation whose tree is its erasure by `n`. -/
theorem isQueryBoundP_of_timeBound {A : OracleAdv.Timed D R α}
    {oc : OracleComp (advSpec D R) α} (hoc : ofOracleComp oc = OracleAdv.toFreeM A.erase)
    {n : ℕ} (h : A.TimeBound n) : oc.IsQueryBoundP (fun t => t.isRight = true) n := by
  rw [← isQueryBound_ofOracleComp, hoc, OracleAdv.ofFreeM_toFreeM]
  exact OracleAdv.Timed.isQueryBound_of_timeBound h

/-- A time bound `n` of a costed adversary whose erasure is in the uniform fragment is the total
query bound `n` of the VCVio computation of the erasure. -/
theorem isTotalQueryBound_toOracleComp_of_timeBound {A : OracleAdv.Timed D R α}
    (hu : IsUnifRand (OracleAdv.toFreeM A.erase)) {n : ℕ} (h : A.TimeBound n) :
    (toOracleComp _ hu).IsTotalQueryBound n :=
  isTotalQueryBound_of_timeBound (ofOracleComp_toOracleComp _ hu) h

/-- A step time bound `n` of `x` whose erased tree is in the uniform fragment is the total query
bound `n - x.1` of the VCVio computation of the erasure. -/
theorem isTotalQueryBound_toOracleComp_of_stepTimeBound {x : ℕ × OracleAdv.Timed D R α}
    (hu : IsUnifRand (OracleAdv.toFreeM x.2.erase)) {n : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x n) :
    (toOracleComp _ hu).IsTotalQueryBound (n - x.1) :=
  isTotalQueryBound_of_stepTimeBound (ofOracleComp_toOracleComp _ hu) h

end CatCrypt.Crypto.VCVioBridge
