/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.TimeCharge
public import CatCryptCore.Examples.PRFMACTimed

/-!
# The time certificate of the PRF-to-MAC reduction as a VCVio query bound

The costed form `prfMacRed.timed` of the PRF-to-MAC reduction of `CatCryptCore.Examples.PRFMAC`
has the time theorem `prfMacRed.timeBound_timed`: a forger of time `n` gives a distinguisher of
time at most `8 n + 7`. Through `CatCryptVCVio.TimeCharge`, a VCVio computation whose tree is the
erased distinguisher makes at most `8 n + 7` queries, uniform and oracle queries together.

## Main results

* `prfMacRed_isTotalQueryBound` — the total query bound `8 n + 7` of the VCVio computation of
  the distinguisher
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Examples.PRFMAC OracleComp

/-- A forger of time `n` gives a PRF distinguisher whose VCVio computation makes at most
`8 n + 7` queries. -/
theorem prfMacRed_isTotalQueryBound {D T : Type} [DecidableEq D] [DecidableEq T]
    {A : OracleAdv.Timed D T (D × T)} {n : ℕ} (hA : A.TimeBound n)
    {oc : OracleComp (advSpec D T) Bool}
    (hoc : ofOracleComp oc = OracleAdv.toFreeM (prfMacRed.timed A).2.erase) :
    oc.IsTotalQueryBound (8 * n + 7) :=
  (isTotalQueryBound_of_stepTimeBound hoc (prfMacRed.timeBound_timed hA)).mono (Nat.sub_le _ _)

end CatCrypt.Crypto.VCVioBridge
