/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatchCore
public import VCVio.ProgramLogic.Tactics
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# `catcrypt_auto` shapes and arms for VCVio goals

Registrations with the registry of `CatCryptCore.Tactics.AutoDispatchCore` for goals about
VCVio's `OracleComp`. Every shape is read in the direct stage, on the goal as stated. The
arms are the tactics and simp sets of VCVio (`vcgen`, `rvcgen`, `by_equiv`, `handler_step`,
`prEvent_norm`, `handler_nf`, `handler_simp`) and the roll-bound lemmas of PolyFun
(`PFunctor.FreeM.isRollBound_*`), of which `OracleComp.IsQueryBound` is the specialisation.

| Shape | Detected goal | Arms, in order |
|---|---|---|
| VCVio relational triple | `RelTriple`, `RelWP`, `_ =ᵈ _` | `rvcgen`; `by_equiv` then `rvcgen` |
| VCVio unary triple | `Triple _ _ _` | `vcgen`; `vcgen` then `grind` or `simp` |
| VCVio query bound | see below | `simp`; roll-bound unfolding; `grind`; `simp` then `decide` |
| VCVio simulateQ equation | see below | `simp`; `grind`; `handler_step` then `simp` |
| VCVio probability | see below | `simp`; `grind`; `prEvent_norm`; `Pi.single_apply`; `vcgen` |

* A query bound is an application of `IsQueryBound`, `IsTotalQueryBound`, `IsQueryBoundP`,
  `IsPerIndexQueryBound` or `PFunctor.FreeM.IsRollBound`. Its second arm unfolds the bound
  to `IsRollBound` and runs `simp` with PolyFun's `isRollBound_pure`,
  `isRollBound_lift_bind_iff` and `isRollBound_map_iff`; its third arm runs `grind` with the
  unfolding of the total and predicate bounds and `isTotalQueryBound_query_bind_iff`.
* A `simulateQ` equation is an equation with a side `simulateQ _ _` or
  `(simulateQ _ _).run _`.
* A probability goal is an `=`, `≠`, `≤` or `<` that mentions `evalDist` (`𝒟[_]`),
  `prEvent` (`Pr{_}[_]`) or `prFail`. Its third arm runs `simp only [prEvent_norm]` then
  `simp`, its fourth `simp [Pi.single_apply, eq_comm]`, its fifth `vcgen` and its last
  `by_equiv` then `rvcgen`.

The arm texts take the arguments of `catcrypt_auto [t₁, …]` through `%GRIND` and
`%GRIND_TAIL`. The registrations are active where this module is imported.
-/

public section

/-! ## Shapes -/

catcrypt_auto_shape "VCVio relational triple" direct priority 100 :=
  any [app OracleComp.ProgramLogic.Relational.RelTriple,
    app OracleComp.ProgramLogic.Relational.RelWP, app EvalDistEq]

catcrypt_auto_shape "VCVio unary triple" direct priority 100 :=
  app OracleComp.ProgramLogic.Triple

catcrypt_auto_shape "VCVio query bound" direct priority 95 :=
  any [app OracleComp.IsQueryBound, app OracleComp.IsTotalQueryBound,
    app OracleComp.IsQueryBoundP, app OracleComp.IsPerIndexQueryBound,
    app PFunctor.FreeM.IsRollBound]

catcrypt_auto_shape "VCVio simulateQ equation" direct priority 90 :=
  any [arg Eq/3 at 1 (app simulateQ), arg Eq/3 at 2 (app simulateQ),
    arg Eq/3 at 1 (arg StateT.run/5 at 3 (app simulateQ)),
    arg Eq/3 at 2 (arg StateT.run/5 at 3 (app simulateQ))]

catcrypt_auto_shape "VCVio probability" direct priority 80 :=
  all [any [app Eq, app Ne, app LE.le, app LT.lt],
    mentions [evalDist, prEvent, prFail]]

/-! ## Arms -/

catcrypt_auto_arm "VCVio relational triple" order 10 := "rvcgen"
catcrypt_auto_arm "VCVio relational triple" order 20 := "(by_equiv <;> rvcgen)"

catcrypt_auto_arm "VCVio unary triple" order 10 := "vcgen"
catcrypt_auto_arm "VCVio unary triple" order 20 :=
  "(vcgen <;> first | grind%GRIND | simp%GRIND)"

catcrypt_auto_arm "VCVio query bound" order 10 := "simp%GRIND"
catcrypt_auto_arm "VCVio query bound" order 20
    needs [OracleComp.isQueryBound_iff_isRollBound, PFunctor.FreeM.isRollBound_pure,
      PFunctor.FreeM.isRollBound_lift_bind_iff, PFunctor.FreeM.isRollBound_map_iff] :=
  "set_option linter.unusedSimpArgs false in \
    (simp only [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP, \
    OracleComp.IsPerIndexQueryBound, OracleComp.isQueryBound_iff_isRollBound]; \
    simp [PFunctor.FreeM.isRollBound_pure, PFunctor.FreeM.isRollBound_lift_bind_iff, \
    PFunctor.FreeM.isRollBound_map_iff%GRIND_TAIL])"
catcrypt_auto_arm "VCVio query bound" order 30
    needs [OracleComp.isTotalQueryBound_query_bind_iff] :=
  "grind [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP, \
    OracleComp.isTotalQueryBound_query_bind_iff%GRIND_TAIL]"
catcrypt_auto_arm "VCVio query bound" order 40 := "(simp%GRIND <;> decide)"

catcrypt_auto_arm "VCVio simulateQ equation" order 10 := "simp%GRIND"
catcrypt_auto_arm "VCVio simulateQ equation" order 20 := "grind%GRIND"
catcrypt_auto_arm "VCVio simulateQ equation" order 30 := "(handler_step; simp%GRIND)"

catcrypt_auto_arm "VCVio probability" order 10 := "simp%GRIND"
catcrypt_auto_arm "VCVio probability" order 20 := "grind%GRIND"
catcrypt_auto_arm "VCVio probability" order 30 := "(simp only [prEvent_norm]; simp%GRIND)"
catcrypt_auto_arm "VCVio probability" order 40 := "simp [Pi.single_apply, eq_comm%GRIND_TAIL]"
catcrypt_auto_arm "VCVio probability" order 50 := "vcgen"
catcrypt_auto_arm "VCVio probability" order 60 := "(by_equiv <;> rvcgen)"

end

/-! ## Tests -/

section Tests

open MeasureTheory OracleComp OracleSpec OracleComp.ProgramLogic
  OracleComp.ProgramLogic.Relational
open scoped ENNReal

/-! ### Probability -/

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} ≠ 0 := by catcrypt_auto
example (x : Bool) : Pr{let y ← (pure x : ProbComp Bool)}[y = x] = 1 := by catcrypt_auto
example (x y : Bool) : 𝒟[(pure y : ProbComp Bool)] {x} = if x = y then 1 else 0 := by
  catcrypt_auto
example (x : Bool) : prFail (pure x : ProbComp Bool) = 0 := by catcrypt_auto
example (mx : ProbComp Bool) : Pr{let _ ← mx}[True] ≤ 1 := by catcrypt_auto

/-! ### Query bounds -/

example {ι : Type} {spec : OracleSpec ι} {α : Type} (x : α) :
    IsTotalQueryBound (pure x : OracleComp spec α) 0 := by catcrypt_auto
example {ι : Type} {spec : OracleSpec ι} {α : Type} (t : ι) (x : α) :
    IsTotalQueryBound (liftM (spec.query t) >>= fun _ => (pure x : OracleComp spec α)) 1 := by
  catcrypt_auto

/-! ### `simulateQ` equations -/

example {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (impl : QueryImpl spec m) (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := by catcrypt_auto
example {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (impl : QueryImpl spec m) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    simulateQ impl (oa >>= f) = simulateQ impl oa >>= fun a => simulateQ impl (f a) := by
  catcrypt_auto

/-! ### Relational and unary triples -/

example (a : Bool) :
    RelTriple (pure a : ProbComp Bool) (pure a : ProbComp Bool) (EqRel Bool) := by
  catcrypt_auto
example (mx : ProbComp Bool) : mx =ᵈ mx := by catcrypt_auto
example (x : Bool) : Triple 1 (pure x : ProbComp Bool) (fun _ => 1) := by catcrypt_auto

/-! ### Reported arms -/

/--
info: Try this:
  [apply] simp
-/
#guard_msgs in
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} ≠ 0 := by catcrypt_auto?

/--
info: Try this:
  [apply] set_option linter.unusedSimpArgs false in
    (simp only [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP, OracleComp.IsPerIndexQueryBound,
        OracleComp.isQueryBound_iff_isRollBound];
      simp [PFunctor.FreeM.isRollBound_pure, PFunctor.FreeM.isRollBound_lift_bind_iff,
        PFunctor.FreeM.isRollBound_map_iff])
-/
#guard_msgs in
example {ι : Type} {spec : OracleSpec ι} {α : Type} (x : α) :
    IsTotalQueryBound (pure x : OracleComp spec α) 0 := by catcrypt_auto?

/--
info: Try this:
  [apply] simp
-/
#guard_msgs in
example {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (impl : QueryImpl spec m) (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := by catcrypt_auto?

/--
info: Try this:
  [apply] rvcgen
-/
#guard_msgs in
example (a : Bool) :
    RelTriple (pure a : ProbComp Bool) (pure a : ProbComp Bool) (EqRel Bool) := by
  catcrypt_auto?

end Tests
