/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad
public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Exact couplings as a PolyFun relational monad algebra

PolyFun's `MAlgRelOrdered m₁ m₂ l` is the predicate-transformer form of the simple
framework of relational program logics of Maillard, Hriţcu, Rivas and Van Muylder: a
relational weakest precondition `rwp x y post : l` with a pure law, monotonicity in the
postcondition and a bind inequality. For a relational Q₀-monad `T` (`RelQ0`) whose monad
structure is the one of its lifting (`RelQ0MonadCompat`), exact couplings form such an
algebra over `Prop`: `rwp x y post` is `RelQ0.liftR 0 post x y`. Its pure law is the
coupling pure rule together with its converse, which adequacy gives: a coupling of two
point masses at an error below `1` relates the two points. Its bind law is
`RelQ0.liftR_bind` at grades `0 + 0`. PolyFun's relational `Triple pre x y post` is then
`pre → RelQ0.liftR 0 post x y`.

## Main results

* `liftRApprox_pure_inv_of_lt_one`: an approximate sub-coupling of two point masses at an
  error below `1` relates the two points.
* `RelQ0.liftR_pure_inv_of_lt_one`: the same for the lifting of every `RelQ0`.
* `RelQ0MonadCompat`: the monad structure of `T` is the one of its lifting; `SDistr` is an
  instance.
* `instMAlgRelOrderedExact`: exact couplings form an `MAlgRelOrdered T T Prop`.
* `triple_iff`: PolyFun's relational triple is `pre → RelQ0.liftR 0 post x y`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob CatCrypt.Relational

/-- An approximate sub-coupling of two point masses at an error below `1` relates the two
points. -/
theorem liftRApprox_pure_inv_of_lt_one {α β : Type} {ε : ℝ≥0∞} {R : α → β → Prop}
    {a : α} {b : β} (hε : ε < 1) (h : liftRApprox ε R (SDistr.pure a) (SDistr.pure b)) :
    R a b := by
  classical
  obtain ⟨c, hc⟩ := h
  by_contra hn
  have hz : ∀ a' b', c.joint (some (a', b')) = 0 := by
    intro a' b'
    by_contra hne
    have ha : a' = a := by
      by_contra hx
      have h1 := c.left_le a'
      have h2 : c.joint (some (a', b')) ≤ ∑' b'', c.joint (some (a', b'')) :=
        ENNReal.le_tsum (f := fun b'' => c.joint (some (a', b''))) b'
      simp [SDistr.pure_apply_some, Ne.symm hx] at h1
      grind
    have hb : b' = b := by
      by_contra hx
      have h1 := c.right_le b'
      have h2 : c.joint (some (a', b')) ≤ ∑' a'', c.joint (some (a'', b')) :=
        ENNReal.le_tsum (f := fun a'' => c.joint (some (a'', b'))) a'
      simp [SDistr.pure_apply_some, Ne.symm hx] at h1
      grind
    subst ha hb
    exact hn (hc _ _ hne)
  have hdef := c.left_deficit
  simp only [hz, tsum_zero, tsub_zero] at hdef
  have h1 : (∑' a', (SDistr.pure a : SDistr α) (some a')) = 1 :=
    SDistr.tsum_some_eq_one_of_none_zero (SDistr.pure_apply_none _)
  rw [h1] at hdef
  exact absurd (lt_of_le_of_lt hdef hε) (lt_irrefl _)

/-- In every `RelQ0`, a lifting of a relation to two point masses at an error below `1`
relates the two points. -/
theorem RelQ0.liftR_pure_inv_of_lt_one {T : Type → Type} [RelQ0 T] {α β : Type}
    {ε : ℝ≥0∞} {R : α → β → Prop} {a : α} {b : β} (hε : ε < 1)
    (h : RelQ0.liftR ε R (RelQ0.pure' (T := T) a) (RelQ0.pure' (T := T) b)) : R a b := by
  have hA := RelQ0.liftR_adequate h CatCrypt.Core.Heap.empty
  rw [RelQ0.denote_pure, RelQ0.denote_pure] at hA
  exact (liftRApprox_pure_inv_of_lt_one hε hA).1

/-- The monad structure of `T` is the one of its graded relational lifting: `pure` is
`RelQ0.pure'` and `bind` is `RelQ0.bind'`. -/
class RelQ0MonadCompat (T : Type → Type) [Monad T] [RelQ0Lift T] : Prop where
  /-- `pure` is the unit of the lifting. -/
  pure_eq : ∀ {α : Type} (a : α), (pure a : T α) = RelQ0.pure' a
  /-- `bind` is the bind of the lifting. -/
  bind_eq : ∀ {α β : Type} (x : T α) (f : α → T β), x >>= f = RelQ0.bind' x f

/-- The monad structure of `SDistr` is the one of its sub-coupling lifting. -/
instance : RelQ0MonadCompat SDistr where
  pure_eq _ := rfl
  bind_eq _ _ := rfl

/-- **Exact couplings as a PolyFun relational monad algebra.** The relational weakest
precondition of `x` and `y` at `post` is the exact coupling `RelQ0.liftR 0 post x y`. The
pure law holds as an equation of propositions by `propext`, from `RelQ0.liftR_pure` and its
converse `RelQ0.liftR_pure_inv_of_lt_one`. -/
instance instMAlgRelOrderedExact {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T] :
    MAlgRelOrdered T T Prop where
  rwp x y post := RelQ0.liftR 0 post x y
  rwp_pure a b post := by
    rw [RelQ0MonadCompat.pure_eq, RelQ0MonadCompat.pure_eq]
    exact propext ⟨RelQ0.liftR_pure_inv_of_lt_one zero_lt_one, RelQ0.liftR_pure⟩
  rwp_mono hpost := RelQ0.liftR_mono_rel hpost
  rwp_bind_le x y f g post := by
    intro h
    rw [RelQ0MonadCompat.bind_eq, RelQ0MonadCompat.bind_eq]
    simpa using RelQ0.liftR_bind (δ := 0) h (fun _ _ hab => hab)

/-- PolyFun's relational triple of exact couplings: `Triple pre x y post` holds iff `pre`
implies the exact coupling `RelQ0.liftR 0 post x y`. It is the unfolding lemma of
`MAlgRelOrdered.Triple` at `instMAlgRelOrderedExact`. -/
theorem triple_iff {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T] {α β : Type}
    (pre : Prop) (x : T α) (y : T β) (post : α → β → Prop) :
    MAlgRelOrdered.Triple pre x y post ↔ (pre → RelQ0.liftR 0 post x y) :=
  Iff.rfl

end CatCrypt.Crypto.VCVioBridge.XDijkstra
