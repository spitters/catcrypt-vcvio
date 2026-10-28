/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.PolyFun.RelationalGraded

/-!
# Exact couplings as a PolyFun relational monad algebra

PolyFun's `MAlgRelOrdered m₁ m₂ l` is the predicate-transformer form of the simple
framework of relational program logics of Maillard, Hriţcu, Rivas and Van Muylder: a
relational weakest precondition `rwp x y post : l` with a pure law, monotonicity in the
postcondition and a bind inequality. For a relational Q₀-monad `T` (`RelQ0`) whose monad
structure is the one of its lifting (`RelQ0MonadCompat`), exact couplings form such an
algebra over `Prop`: it is the grade-`0` restriction (`MAlgRelGraded.atZero`) of the
graded algebra of approximate couplings `instMAlgRelGradedRelQ0`, so `rwp x y post` is
`RelQ0.liftR 0 post x y`. PolyFun's relational `Triple pre x y post` is then
`pre → RelQ0.liftR 0 post x y`.

## Main results

* `instMAlgRelOrderedExact`: exact couplings form an `MAlgRelOrdered T T Prop`.
* `triple_iff`: PolyFun's relational triple is `pre → RelQ0.liftR 0 post x y`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob CatCrypt.Relational

/-- **Exact couplings as a PolyFun relational monad algebra.** It is the grade-`0`
restriction of the graded algebra of approximate couplings: the relational weakest
precondition of `x` and `y` at `post` is the exact coupling `RelQ0.liftR 0 post x y`. -/
instance instMAlgRelOrderedExact {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T] :
    MAlgRelOrdered T T Prop :=
  MAlgRelGraded.atZero ℝ≥0∞

/-- PolyFun's relational triple of exact couplings: `Triple pre x y post` holds iff `pre`
implies the exact coupling `RelQ0.liftR 0 post x y`. It is the unfolding lemma of
`MAlgRelOrdered.Triple` at `instMAlgRelOrderedExact`. -/
theorem triple_iff {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T] {α β : Type}
    (pre : Prop) (x : T α) (y : T β) (post : α → β → Prop) :
    MAlgRelOrdered.Triple pre x y post ↔ (pre → RelQ0.liftR 0 post x y) :=
  Iff.rfl

end CatCrypt.Crypto.VCVioBridge.XDijkstra
